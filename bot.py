#!/usr/bin/env python3
"""Автоканал про вузы, поступление и науку.

Workflow запускает этот скрипт каждые 10 минут, но публикует он только когда
подошло время (next_post_at в posted.json). Днём пост примерно раз в 30 минут,
ночью примерно раз в 90, с разбросом. Время следующего поста каждый раз
выбирается случайно.

Когда пора публиковать:
  1. Бот читает ВСЕ ленты из sources.json и находит новые новости.
  2. Дешёвая модель ставит каждой три оценки: важность, польза абитуриенту и
     срочность. Из них считается рейтинг 0-10.
  3. Срочные и важные (рейтинг >= TOP_MIN) идут в очередь top и публикуются
     первыми, лучшие вперёд. Общие, но важные и средние (рейтинг >= RESERVE_MIN)
     откладываются в запас reserve и выходят, только когда хороших новостей нет.
     Слабые отбрасываются.
  4. Каждый FACT_EVERY-й пост, а также когда новостей нет, это факт о вузе по
     статье Википедии, с фото, если лицензия свободная.
  5. К новости берётся картинка: из ленты, а если там нет, то og:image со страницы.
     Пост пишется по-русски ТОЛЬКО по тексту источника. Любое число, которого
     нет в источнике, считается выдумкой и пост отклоняется. Внизу ссылка.
Только стандартная библиотека Python.
"""
import datetime as dt
import hashlib
import json
import os
import random
import re
import struct
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from email.utils import parsedate_to_datetime
from html import unescape
from html.entities import name2codepoint
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).parent
STATE_FILE = ROOT / "posted.json"
SOURCES = json.loads((ROOT / "sources.json").read_text(encoding="utf-8"))


def _env(name, default):
    """Пустые значения из GitHub (переменная не задана) считаются незаданными."""
    return os.environ.get(name) or default


# ---------- настройки ----------

# ИИ. Бесплатный вариант: любой OpenAI-совместимый API, по умолчанию Groq.
LLM_KEY = (os.environ.get("LLM_API_KEY") or "").strip()
LLM_URL = _env("LLM_BASE_URL", "https://api.groq.com/openai/v1").rstrip("/")
LLM_PAUSE = float(_env("LLM_PAUSE", 20))  # пауза между запросами: лимит токенов в минуту
MODEL = _env("LLM_MODEL", "" if LLM_KEY else _env("CLAUDE_MODEL", "claude-haiku-5-5"))
RANK_MODEL = _env("LLM_RANK_MODEL", MODEL)
# Если модель не задана, бот спрашивает у Groq список доступных и берёт первую из этих.
PREFER_MAIN = ["openai/gpt-oss-120b", "llama-3.3-70b-versatile", "openai/gpt-oss-20b", "llama-3.1-8b-instant"]
PREFER_RANK = ["llama-3.1-8b-instant", "openai/gpt-oss-20b", "openai/gpt-oss-120b", "llama-3.3-70b-versatile"]
NOT_TEXT_MODELS = ("whisper", "orpheus", "guard", "tts", "safeguard", "embed")

DRY = os.environ.get("DRY_RUN") == "1"
FORCE = DRY or _env("FORCE", "").lower() in ("1", "true")  # ручной запуск: публиковать сразу
UA = "Mozilla/5.0 (compatible; unifacts-bot/1.0)"
MAX_CHARS = 5000 if LLM_KEY else 15000  # у бесплатных API мал лимит токенов в минуту
CONTENT_NS = "{http://purl.org/rss/1.0/modules/content/}encoded"

# Расписание (Маврикий = UTC+4). Всё можно менять переменными репозитория на GitHub.
DAY_MINUTES = float(_env("DAY_MINUTES", 30))
NIGHT_MINUTES = float(_env("NIGHT_MINUTES", 90))
JITTER = float(_env("JITTER", 0.25))          # разброс: 0.25 = плюс-минус 25%
NIGHT_START = int(_env("NIGHT_START", 23))    # ночь с 23:00 до 07:00 по местному времени
NIGHT_END = int(_env("NIGHT_END", 7))
TZ = dt.timezone(dt.timedelta(hours=float(_env("TZ_OFFSET", 4))))
RETRY_MINUTES = 15          # если публиковать нечего
ERROR_BACKOFF_MINUTES = 30  # если запуск упал

# Рейтинг
TOP_MIN = float(_env("TOP_MIN", 7.0))
RESERVE_MIN = float(_env("RESERVE_MIN", 5.0))
TOP_MAX_AGE_DAYS = 3        # срочная новость старше этого уходит в запас
RESERVE_MAX_AGE_DAYS = 30   # запас старше этого забывается
FEED_MAX_AGE_DAYS = 7
PER_FEED_LIMIT = 15
SCORE_BATCH = 10
SCORE_MAX_PER_RUN = 40
SAME_KIND_PENALTY = 0.7     # небольшой штраф, если тип такой же, как у прошлого поста
FACT_EVERY = int(_env("FACT_EVERY", 6))
MAX_ATTEMPTS = 3            # сколько кандидатов пробуем превратить в пост за запуск
REFILL_BELOW = 10

TRANSLATE = ("Источник на английском: пиши пост по-русски (это перевод и пересказ). "
             "Названия вузов и программ при первом упоминании давай по-русски, "
             "оригинал можно добавить в скобках.")

FACT_PROMPT = """Ты ведёшь русскоязычный Telegram-канал для школьников, которые думают о поступлении в зарубежные вузы.
Ниже текст статьи из Википедии про: {name}.
Выбери из него ОДИН неожиданный, конкретный факт (история, традиции, известные выпускники, научные достижения, необычные цифры) и напиши пост.

Правила:
- """ + TRANSLATE + """
- Используй только то, что прямо написано в тексте. Ничего не добавляй из своих знаний.
- Числа, годы и имена бери в точности как в тексте. Не округляй, не считай, не выводи новые числа.
- Не пиши про рейтинги, стоимость обучения и шансы поступления.
- 350-650 символов, живой русский язык, без воды, без хэштегов, без разметки (звёздочек и решёток).
- В заголовке есть название вуза.
- Оформление: первая строка - цепляющий заголовок, в начале него эмодзи по теме. Дальше 3-4 коротких абзаца по 1-2 предложения, между абзацами пустая строка. Всего 3-5 эмодзи по смыслу (в заголовке и в начале или конце абзацев), не больше одного на абзац, эмодзи-цифры не используй.
- Выведи только текст поста, без вступлений.
- Если в тексте нет подходящего факта, ответь одним словом: SKIP.

Текст статьи:
{text}"""

NEWS_PROMPT = """Ты ведёшь русскоязычный Telegram-канал для школьников, которые думают о поступлении в зарубежные вузы.
Ниже текст новости. Издание: {outlet}. Заголовок: {name}.
Перескажи новость коротким постом.

Правила:
- """ + TRANSLATE + """
- Только факты из текста. Не добавляй ничего от себя, не делай прогнозов и выводов, которых в тексте нет.
- Числа, годы и названия бери в точности как в тексте. Не округляй, не считай, не выводи новые числа.
- Пересказывай своими словами, не копируй предложения, прямые цитаты не используй.
- 350-700 символов, живой русский язык, без хэштегов, без разметки (звёздочек и решёток).
- Оформление: первая строка - цепляющий заголовок, в начале него эмодзи по теме. Дальше 3-4 коротких абзаца по 1-2 предложения, между абзацами пустая строка. Всего 3-5 эмодзи по смыслу (в заголовке и в начале или конце абзацев), не больше одного на абзац, эмодзи-цифры не используй.
- Выведи только текст поста, без вступлений.
- Если в тексте мало содержания или это реклама, ответь одним словом: SKIP.

Текст новости:
{text}"""

SCORE_PROMPT = """Ты редактор Telegram-канала для школьников 14-18 лет, которые хотят поступать в зарубежные вузы (олимпиады, SAT, летние школы, стипендии, наука).
Оцени каждую новость по трём признакам:
important - насколько новость значима, от 0 до 10. 9-10: крупные изменения правил поступления, виз, стипендий, крупные научные открытия, события мирового уровня. 5-8: заметные новости. 0-4: мелочи, локальные истории, реклама, внутренние дела одного вуза.
relevant - насколько новость полезна или интересна абитуриенту, который хочет учиться за рубежом, от 0 до 10.
timely - 1, если новость привязана ко времени и устареет за несколько дней. 0, если это общая тема, которая останется актуальной (обзор, тренд, объяснение).
Ответь только JSON-массивом объектов, по одному на каждую новость, в том же порядке. Пример для двух новостей: [{"important": 8, "relevant": 9, "timely": 1}, {"important": 5, "relevant": 4, "timely": 0}]

Новости:
{items}"""

REFILL_PROMPT = """Назови {n} разных университетов мира, известных абитуриентам (разные страны и континенты, не только США и Великобритания).
Для каждого дай точное название статьи в английской Википедии.
Не повторяй эти: {known}
Ответь только JSON-массивом строк, без пояснений."""


# ---------- время ----------

def utcnow():
    return dt.datetime.now(dt.timezone.utc)


def iso(t):
    return t.isoformat(timespec="seconds")


def is_night(now):
    h = now.astimezone(TZ).hour
    if NIGHT_START > NIGHT_END:  # ночь через полночь: 23-7
        return h >= NIGHT_START or h < NIGHT_END
    return NIGHT_START <= h < NIGHT_END


def next_delay(now):
    base = NIGHT_MINUTES if is_night(now) else DAY_MINUTES
    return dt.timedelta(minutes=base * random.uniform(1 - JITTER, 1 + JITTER))


# ---------- сеть ----------

def http_get(url, data=None, headers=None):
    req = urllib.request.Request(url, data=data, headers={"User-Agent": UA, **(headers or {})})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()


def init_models():
    """Если модель не задана вручную, берём первую доступную этому ключу."""
    global MODEL, RANK_MODEL
    if not LLM_KEY or (MODEL and os.environ.get("LLM_MODEL")):
        return
    try:
        data = json.loads(http_get(f"{LLM_URL}/models", headers={"Authorization": f"Bearer {LLM_KEY}"}))
        avail = {m["id"] for m in data["data"]}
    except Exception as e:
        print("список моделей не получен:", e)
        avail = set()
    usable = sorted(m for m in avail if not any(x in m for x in NOT_TEXT_MODELS))
    pick = lambda prefs: next((m for m in prefs if m in avail), usable[0] if usable else None)
    MODEL = MODEL if os.environ.get("LLM_MODEL") else (pick(PREFER_MAIN) or "llama-3.3-70b-versatile")
    RANK_MODEL = os.environ.get("LLM_RANK_MODEL") or pick(PREFER_RANK) or MODEL
    print(f"модели: основная {MODEL}, для оценок {RANK_MODEL}")


def _retry_after(e, attempt):
    try:
        return min(float(e.headers.get("retry-after")), 90)
    except (TypeError, ValueError):
        return 20 * (attempt + 1)


_last_llm = 0.0


def ask_llm(prompt, max_tokens=800, model=None):
    """Один запрос к модели. Если задан LLM_API_KEY, идёт в OpenAI-совместимый API
    (Groq, Gemini и т.п.), иначе в Claude по ANTHROPIC_API_KEY."""
    global _last_llm
    model = model or MODEL
    if LLM_KEY:
        wait = LLM_PAUSE - (time.time() - _last_llm)  # бесплатные тарифы ограничивают токены в минуту
        if wait > 0:
            time.sleep(wait)
        body = {"model": model, "max_tokens": max_tokens, "temperature": 0.4,
                "messages": [{"role": "user", "content": prompt}]}
        if "gpt-oss" in model:  # рассуждающая модель: меньше рассуждений, больше места для ответа
            body["reasoning_effort"] = "low"
            body["max_tokens"] = max_tokens + 1000
        url = f"{LLM_URL}/chat/completions"
        headers = {"Authorization": f"Bearer {LLM_KEY}", "content-type": "application/json"}
    else:
        url = "https://api.anthropic.com/v1/messages"
        body = {"model": model, "max_tokens": max_tokens,
                "messages": [{"role": "user", "content": prompt}]}
        headers = {"x-api-key": os.environ["ANTHROPIC_API_KEY"],
                   "anthropic-version": "2023-06-01", "content-type": "application/json"}
    data = json.dumps(body).encode()
    for attempt in range(5):
        try:
            raw = http_get(url, data, headers)
            _last_llm = time.time()
            break
        except urllib.error.HTTPError as e:
            _last_llm = time.time()
            detail = e.read().decode(errors="replace")
            if e.code in (429, 500, 502, 503) and attempt < 4:
                wait = _retry_after(e, attempt)
                print(f"  ИИ вернул {e.code}, жду {wait:.0f} с и повторяю")
                time.sleep(wait)
                continue
            sys.exit(f"ИИ-API ({model}): {e.code} {detail}")
    out = json.loads(raw)
    if LLM_KEY:
        return (out["choices"][0]["message"].get("content") or "").strip()
    return "".join(b.get("text", "") for b in out["content"]).strip()


def tg(method, fields, photo=None):
    url = f"https://api.telegram.org/bot{os.environ['TELEGRAM_BOT_TOKEN']}/{method}"
    if photo:
        boundary = "----unifacts" + os.urandom(8).hex()
        parts = [
            f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode()
            for k, v in fields.items()
        ]
        ext, ctype = ("png", "image/png") if photo[:4] == b"\x89PNG" else ("jpg", "image/jpeg")
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="photo"; filename="photo.{ext}"\r\n'
            f'Content-Type: {ctype}\r\n\r\n'.encode() + photo + b"\r\n")
        parts.append(f"--{boundary}--\r\n".encode())
        data, headers = b"".join(parts), {"Content-Type": f"multipart/form-data; boundary={boundary}"}
    else:
        data, headers = urllib.parse.urlencode(fields).encode(), {}
    try:
        raw = http_get(url, data, headers)
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"Telegram {method}: {e.code} {e.read().decode(errors='replace')}")
    if not json.loads(raw).get("ok"):
        raise RuntimeError(f"Telegram {method}: {raw!r}")


def publish(post):
    text, photo = post["text"], post.get("photo")
    if DRY:
        print("----- DRY RUN -----")
        print(text)
        print("[фото]", photo["credit"] if photo else "нет")
        print("-------------------")
        return
    chat = os.environ["TELEGRAM_CHAT_ID"]
    sent_photo = False
    if photo:
        caption = text + "\n" + photo["credit"]
        try:
            if len(caption) <= 1024:  # лимит подписи к фото в Telegram
                tg("sendPhoto", {"chat_id": chat, "caption": caption}, photo["bytes"])
                return
            tg("sendPhoto", {"chat_id": chat, "caption": photo["credit"]}, photo["bytes"])
            sent_photo = True
        except RuntimeError as e:
            print("фото не отправилось, шлю только текст:", e)
    tg("sendMessage", {
        "chat_id": chat, "text": text,
        # картинка уже ушла: второе превью ссылки не нужно
        "link_preview_options": json.dumps({"is_disabled": sent_photo or not post["preview"]}),
    })


# ---------- текст ----------

class _Text(HTMLParser):
    SKIP = {"script", "style", "noscript", "nav", "footer", "header", "form"}
    BREAK = {"p", "div", "br", "li", "h1", "h2", "h3", "h4"}

    def __init__(self):
        super().__init__()
        self.out, self.skip = [], 0

    def handle_starttag(self, tag, attrs):
        if tag in self.SKIP:
            self.skip += 1

    def handle_endtag(self, tag):
        if tag in self.SKIP and self.skip:
            self.skip -= 1
        if tag in self.BREAK:
            self.out.append("\n")

    def handle_data(self, data):
        if not self.skip:
            self.out.append(data)


def html_to_text(html):
    p = _Text()
    p.feed(html)
    t = re.sub(r"[ \t\xa0]+", " ", "".join(p.out))
    return re.sub(r"\n\s*\n+", "\n", t).strip()


# Числа: 1636, 21,000, 21 000, 3.5. Пост не должен содержать числа, которого нет в источнике.
NUM = re.compile(r"\d+(?:[,  ]\d{3}(?!\d))*(?:\.\d+)?")


def joined_numbers(text):
    return {re.sub(r"\D", "", m) for m in NUM.findall(text)}


def known_numbers(text):
    return set(re.findall(r"\d+", text)) | joined_numbers(text)


EMOJI = re.compile("[\U0001F300-\U0001FAFF\u2600-\u27BF\u2B50\u2B06\u2B07\u2934\u2935\u2B05\u2B1B\u2B1C\u2B55]")
DEFAULT_EMOJI = {"fact": "🏛", "admissions": "🎓", "science": "🔬"}


def pretty(text, kind):
    """Оформление: без разметки, абзацы через пустую строку, эмодзи в заголовке."""
    t = re.sub(r"[*#`]+", "", text).strip()
    paras = [p.strip() for p in re.split(r"\n+", t) if p.strip()]
    if not paras:
        return text
    if len(paras) < 3:  # модель выдала сплошной текст: режем по предложениям, по два в абзац
        title, rest = paras[0], " ".join(paras[1:])
        sents = re.split(r"(?<=[.!?…])\s+(?=[A-ZА-ЯЁ0-9«\"(])", rest)
        paras = [title] + [" ".join(sents[i:i + 2]) for i in range(0, len(sents), 2) if sents[i:i + 2]]
    if not EMOJI.search(paras[0]):
        paras[0] = DEFAULT_EMOJI.get(kind, "📌") + " " + paras[0]
    return "\n\n".join(paras)


def make_post(prompt_tpl, source_text, kind="fact", **fields):
    known = known_numbers(source_text)
    prompt = prompt_tpl.format(text=source_text, **fields)
    for attempt in range(3):
        out = ask_llm(prompt).strip()
        if out.upper().startswith("SKIP"):
            return None
        bad = sorted(n for n in joined_numbers(out) if n not in known)
        if bad:
            print(f"  отклонено, чисел нет в источнике: {bad} (попытка {attempt + 1})")
            continue
        if not 200 <= len(out) <= 1800:
            print(f"  отклонено, длина {len(out)}")
            continue
        return pretty(out, kind)
    return None


# ---------- Википедия: факты и фото ----------

def wiki_page(title):
    q = urllib.parse.urlencode({
        "action": "query", "prop": "extracts|pageimages", "explaintext": 1,
        "exsectionformat": "plain", "piprop": "thumbnail|name", "pithumbsize": 1280,
        "redirects": 1, "titles": title, "format": "json",
    })
    page = next(iter(json.loads(http_get(f"https://en.wikipedia.org/w/api.php?{q}"))["query"]["pages"].values()))
    return {
        "name": page.get("title", title),
        "text": page.get("extract", ""),
        "image_file": page.get("pageimage"),
        "image_url": page.get("thumbnail", {}).get("source"),
    }


def wiki_photo(page):
    """Фото статьи, только если оно свободное (CC или общественное достояние). Иначе None."""
    f, url = page.get("image_file"), page.get("image_url")
    if not f or not url or not f.lower().endswith((".jpg", ".jpeg")):  # png/svg обычно логотипы и схемы
        return None
    try:
        q = urllib.parse.urlencode({
            "action": "query", "titles": "File:" + f, "prop": "imageinfo",
            "iiprop": "extmetadata", "format": "json",
        })
        info = next(iter(json.loads(http_get(f"https://en.wikipedia.org/w/api.php?{q}"))["query"]["pages"].values()))
        meta = info["imageinfo"][0]["extmetadata"]
        if str(meta.get("NonFree", {}).get("value", "")).lower() in ("true", "1"):
            return None
        lic = meta.get("LicenseShortName", {}).get("value", "")
        if not re.match(r"(?i)(cc[ -]|cc0|public domain|pd)", lic):
            return None
        artist = html_to_text(meta.get("Artist", {}).get("value", ""))[:60] or "автор не указан"
        return {"bytes": http_get(url), "credit": f"Фото: {artist}, {lic}, Wikimedia Commons"}
    except Exception as e:
        print("  фото пропущено:", e)
        return None


def all_universities(state):
    return SOURCES["universities"] + [u for u in state["extra_universities"] if u not in SOURCES["universities"]]


def refill_universities(state):
    """Пополняет список вузов: модель предлагает названия, бот оставляет только те,
    что реально нашлись в Википедии и достаточно длинные. Работает без участия человека."""
    known = all_universities(state)
    try:
        out = ask_llm(REFILL_PROMPT.format(n=30, known="; ".join(known)), max_tokens=1200)
        titles = json.loads(re.search(r"\[.*\]", out, re.S).group(0))
    except Exception as e:
        print("пополнение списка вузов не удалось:", e)
        return
    added = 0
    for t in titles:
        if not isinstance(t, str) or t in known or t in state["extra_universities"]:
            continue
        try:
            page = wiki_page(t)
        except Exception:
            continue
        if len(page["text"]) >= 3000 and re.search(r"(?i)universit|college|institute|school|polytechnic|academy", page["name"]):
            state["extra_universities"].append(t)
            added += 1
    print(f"в список вузов добавлено: {added}")


def build_fact_post(state):
    left = [u for u in all_universities(state) if u not in state["posted"]]
    if len(left) < REFILL_BELOW:
        refill_universities(state)
        left = [u for u in all_universities(state) if u not in state["posted"]]
    random.shuffle(left)
    for title in left[:3]:
        print("факт:", title)
        try:
            page = wiki_page(title)
        except Exception as e:
            print("  Википедия недоступна:", e)
            continue
        if len(page["text"]) < 1500:
            state["posted"].append(title)  # статья слишком короткая, больше не пробуем
            continue
        post = make_post(FACT_PROMPT, page["text"][:MAX_CHARS], kind="fact", name=page["name"])
        if post:
            url = "https://en.wikipedia.org/wiki/" + urllib.parse.quote(page["name"].replace(" ", "_"))
            return {"text": f"{post}\n\nИсточник: Википедия, {url}", "preview": False,
                    "photo": wiki_photo(page), "kind": "fact", "key": title}
    return None


# ---------- новости (RSS) ----------

def _fix_entities(xml):
    """В лентах бывают HTML-сущности вроде &nbsp;, которых нет в XML: заменяем на числовые."""
    xml = re.sub(r"^\s*<\?xml[^>]*\?>", "", xml)

    def sub(m):
        cp = name2codepoint.get(m.group(1))
        return f"&#{cp};" if cp else ""
    return re.sub(r"&(?!(?:amp|lt|gt|quot|apos);)([A-Za-z][A-Za-z0-9]*);", sub, xml)


MEDIA = "{http://search.yahoo.com/mrss/}"
IMG_BAD = re.compile(r"(?i)logo|icon|avatar|sprite|pixel|tracking|placeholder|badge|favicon|\.svg|\.gif|\.webp|1x1")
NEWS_PHOTOS = _env("NEWS_PHOTOS", "1") != "0"  # NEWS_PHOTOS=0 выключает картинки у новостей


def feed_image(it, body):
    """Адрес картинки из элемента ленты: media:content, media:thumbnail, enclosure, первый <img>."""
    for tag in ("content", "thumbnail"):
        for el in it.iter(MEDIA + tag):
            url, typ = el.get("url"), el.get("type", "")
            if url and (tag == "thumbnail" or el.get("medium") == "image" or typ.startswith("image")
                        or re.search(r"\.(jpe?g|png)(\?|$)", url, re.I)):
                return url
    for el in it.iter("enclosure"):
        if el.get("url") and el.get("type", "").startswith("image"):
            return el.get("url")
    for m in re.finditer(r"""<img\b[^>]*?\bsrc=["']([^"']+)""", body, re.I):
        if not IMG_BAD.search(m.group(1)):
            return m.group(1)
    return None


def page_image(page_html):
    """og:image или twitter:image со страницы статьи."""
    for tag in re.findall(r"<meta\b[^>]*>", page_html[:200000], re.I):
        if re.search(r"""(?:property|name)=["'](?:og:image(?::url)?|twitter:image)["']""", tag, re.I):
            m = re.search(r"""content=["']([^"']+)""", tag, re.I)
            if m:
                return m.group(1)
    return None


def image_size(b):
    """Ширина и высота JPEG или PNG по заголовку, без сторонних библиотек."""
    if b[:8] == b"\x89PNG\r\n\x1a\n" and len(b) > 24:
        return struct.unpack(">II", b[16:24])
    if b[:2] == b"\xff\xd8":
        i = 2
        while i + 9 < len(b):
            if b[i] != 0xFF:
                i += 1
                continue
            m = b[i + 1]
            if m == 0xFF:
                i += 1
            elif m in (0x01, 0xD8) or 0xD0 <= m <= 0xD7:
                i += 2
            elif 0xC0 <= m <= 0xCF and m not in (0xC4, 0xC8, 0xCC):
                h, w = struct.unpack(">HH", b[i + 5:i + 9])
                return w, h
            else:
                i += 2 + struct.unpack(">H", b[i + 2:i + 4])[0]
    return None


def fetch_image(url, base):
    """Скачивает картинку и проверяет, что это не логотип, не баннер и Telegram её примет."""
    url = urllib.parse.urljoin(base, unescape(url).strip())
    if not url.startswith("http") or IMG_BAD.search(url.split("?")[0]):
        return None
    try:
        data = http_get(url, headers={"Referer": base, "Accept": "image/jpeg,image/png,*/*;q=0.5"})
    except Exception as e:
        print("  картинка не скачалась:", e)
        return None
    size = image_size(data)
    if not size:
        return None
    w, h = size
    if w < 500 or h < 250 or len(data) < 15000 or len(data) > 8_000_000 or max(w, h) > 3 * min(w, h) or w + h > 10000:
        print(f"  картинка не подошла: {w}x{h}, {len(data) // 1000} КБ")
        return None
    return data


def read_feed(feed):
    root = ET.fromstring(_fix_entities(http_get(feed["url"]).decode("utf-8", errors="replace")))
    items = []
    for it in root.iter("item"):
        try:
            date = parsedate_to_datetime(it.findtext("pubDate"))
        except Exception:
            date = utcnow()
        if date.tzinfo is None:
            date = date.replace(tzinfo=dt.timezone.utc)
        body = it.findtext(CONTENT_NS) or it.findtext("description") or ""
        items.append({
            "outlet": feed["name"], "kind": feed["category"],
            "title": (it.findtext("title") or "").strip(),
            "link": (it.findtext("link") or "").strip(),
            "body": body, "image": feed_image(it, body),
            "date": date,
        })
    return items


def item_id(link):
    return hashlib.sha1(link.encode()).hexdigest()[:12]


def _clamp(x):
    return max(0.0, min(10.0, float(x)))


def score_batch(batch):
    """Оценки важности, пользы и срочности для пачки новостей. None, если не получилось."""
    lines = [f"{i}. [{b['outlet']}] {b['title']}. {html_to_text(b['body'])[:350]}"
             for i, b in enumerate(batch, 1)]
    try:
        out = ask_llm(SCORE_PROMPT.replace("{items}", "\n".join(lines)),
                      max_tokens=60 * len(batch) + 100, model=RANK_MODEL)
        arr = json.loads(re.search(r"\[.*\]", out, re.S).group(0))
        res = [{"important": _clamp(o["important"]), "relevant": _clamp(o["relevant"]),
                "timely": 1 if int(o.get("timely", 1)) else 0} for o in arr]
        return res if len(res) == len(batch) else None
    except Exception as e:
        print("  оценка не удалась:", e)
        return None


def rating(s):
    return round(0.55 * s["important"] + 0.45 * s["relevant"], 1)


def tier_of(r, timely):
    if r >= TOP_MIN:
        return "top" if timely else "reserve"  # важная, но общая: в запас
    if r >= RESERVE_MIN:
        return "reserve"
    return "drop"


BODIES = {}  # link -> текст из ленты, только в этом запуске
IMAGES = {}  # link -> адрес картинки из ленты, только в этом запуске


def refresh_pool(state, now):
    # 1. старение очереди
    keep = []
    for p in state["pool"]:
        age = (now - dt.datetime.fromisoformat(p["date"])).days
        if p["tier"] == "top" and age > TOP_MAX_AGE_DAYS:
            p["tier"] = "reserve"
        if age <= RESERVE_MAX_AGE_DAYS:
            keep.append(p)
    state["pool"] = keep

    # 2. все ленты: что нового
    known = set(state["seen"]) | {p["id"] for p in state["pool"]}
    cutoff = now - dt.timedelta(days=FEED_MAX_AGE_DAYS)
    fresh = []
    for feed in SOURCES["feeds"]:
        try:
            items = read_feed(feed)
        except Exception as e:
            print(f"  лента {feed['name']} не открылась: {e}")
            continue
        n = 0
        for it in sorted(items, key=lambda i: i["date"], reverse=True):
            if not it["link"]:
                continue
            BODIES[it["link"]] = it["body"]
            IMAGES[it["link"]] = it.get("image")
            if item_id(it["link"]) in known or it["date"] < cutoff or n >= PER_FEED_LIMIT:
                continue
            fresh.append(it)
            n += 1
    fresh.sort(key=lambda i: i["date"], reverse=True)
    fresh = fresh[:SCORE_MAX_PER_RUN]
    print(f"новых новостей: {len(fresh)}, в очереди: {len(state['pool'])}")

    # 3. оценка пачками
    for i in range(0, len(fresh), SCORE_BATCH):
        batch = fresh[i:i + SCORE_BATCH]
        scores = score_batch(batch)
        if not scores:
            continue  # вернёмся к этим новостям в следующий раз
        for it, s in zip(batch, scores):
            r = rating(s)
            tier = tier_of(r, s["timely"])
            state["seen"].append(item_id(it["link"]))
            print(f"  {r:>4} {tier:<7} {'срочно' if s['timely'] else 'общее ':<6} {it['title'][:60]}")
            if tier != "drop":
                state["pool"].append({
                    "id": item_id(it["link"]), "link": it["link"], "outlet": it["outlet"],
                    "kind": it["kind"], "title": it["title"], "date": iso(it["date"]),
                    "rating": r, "timely": s["timely"], "tier": tier})


def build_news_post(item):
    print(f"новость [{item['tier']}] {item['rating']}: {item['title'][:70]}")
    link = item["link"]
    text = html_to_text(BODIES.get(link, ""))
    page_html = None

    def page():
        nonlocal page_html
        if page_html is None:
            try:
                page_html = http_get(link).decode("utf-8", errors="replace")
            except Exception as e:
                print("  страница не открылась:", e)
                page_html = ""
        return page_html

    if len(text) < 1500:  # в ленте только анонс: пробуем взять страницу целиком
        full = html_to_text(page())
        if len(full) > len(text):
            text = full
    text = text[:MAX_CHARS]
    if len(text) < 400:
        print("  мало текста, пропускаю")
        return None
    post = make_post(NEWS_PROMPT, text, kind=item["kind"], name=item["title"], outlet=item["outlet"])
    if not post:
        return None
    photo = None
    if NEWS_PHOTOS:  # сначала картинка из ленты, потом og:image со страницы
        for get_url in (lambda: IMAGES.get(link), lambda: page_image(page())):
            url = get_url()
            data = fetch_image(url, link) if url else None
            if data:
                photo = {"bytes": data, "credit": f"Фото: {item['outlet']}"}
                break
    return {"text": f"{post}\n\nИсточник: {item['outlet']}, {link}", "preview": True,
            "photo": photo, "kind": item["kind"], "key": item["id"]}


# ---------- выбор поста ----------

def pick_post(state, now):
    def eff(p):  # срочные: рейтинг минус возраст, чуть реже повторяем тип прошлого поста
        age = (now - dt.datetime.fromisoformat(p["date"])).total_seconds() / 86400
        return p["rating"] - 0.5 * age - (SAME_KIND_PENALTY if p["kind"] == state["last_kind"] else 0)

    top = sorted((p for p in state["pool"] if p["tier"] == "top"), key=eff, reverse=True)
    reserve = sorted((p for p in state["pool"] if p["tier"] == "reserve"), key=lambda p: p["rating"], reverse=True)
    order = []
    if state["since_fact"] >= FACT_EVERY:
        order.append(None)  # None = факт о вузе
    order += top + reserve
    order.append(None)

    attempts, fact_tried = 0, False
    for item in order:
        if attempts >= MAX_ATTEMPTS:
            break
        if item is None:
            if fact_tried:
                continue
            fact_tried = True
            attempts += 1
            post = build_fact_post(state)
        else:
            attempts += 1
            post = build_news_post(item)
            if not post:  # не подошла: убираем из очереди насовсем
                state["pool"] = [p for p in state["pool"] if p["id"] != item["id"]]
        if post:
            return post
    return None


def apply_post(state, post):
    if post["kind"] == "fact":
        state["posted"].append(post["key"])
        state["since_fact"] = 0
    else:
        state["pool"] = [p for p in state["pool"] if p["id"] != post["key"]]
        state["since_fact"] += 1
    state["last_kind"] = post["kind"]


# ---------- запуск ----------

def load_state():
    s = json.loads(STATE_FILE.read_text(encoding="utf-8")) if STATE_FILE.exists() else {}
    for k, v in {"posted": [], "extra_universities": [], "seen": [], "pool": [],
                 "since_fact": 0, "last_kind": None, "next_post_at": None}.items():
        s.setdefault(k, v)
    return s


def save_state(state):
    if DRY:
        return
    state["seen"] = state["seen"][-4000:]
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")


def main():
    state = load_state()
    now = utcnow()
    due = state["next_post_at"]
    if not FORCE and due and now < dt.datetime.fromisoformat(due):
        print(f"рано: следующий пост после {due} (сейчас {iso(now)})")
        return
    try:
        init_models()
        refresh_pool(state, now)
        post = pick_post(state, now)
        if not post:
            state["next_post_at"] = iso(now + dt.timedelta(minutes=RETRY_MINUTES))
            print(f"публиковать нечего, повторю через {RETRY_MINUTES} минут")
            return
        publish(post)
        apply_post(state, post)
        delay = next_delay(now)
        state["next_post_at"] = iso(now + delay)
        print(f"опубликовано ({post['kind']}), следующий пост через {delay.total_seconds() / 60:.0f} мин")
    except BaseException:
        state["next_post_at"] = iso(now + dt.timedelta(minutes=ERROR_BACKOFF_MINUTES))
        raise
    finally:
        save_state(state)


if __name__ == "__main__":
    main()

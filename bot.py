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
     Если нет, ИИ предлагает запросы и выбирает свободное фото на Wikimedia Commons;
     потом нейросетевая иллюстрация (по желанию), потом своя карточка.
     Пост пишется по-русски ТОЛЬКО по тексту источника. Любое число, которого
     нет в источнике, считается выдумкой и пост отклоняется. Внизу ссылка.
Только стандартная библиотека Python.
"""
import datetime as dt
import hashlib
import io
import json
import math
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
import zlib
from email.utils import parsedate_to_datetime
from html import escape as html_escape, unescape
from html.entities import name2codepoint
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).parent
STATE_FILE = ROOT / "posted.json"
SOURCES = json.loads((ROOT / "sources.json").read_text(encoding="utf-8"))


try:  # все переменные репозитория одним куском (если workflow их передаёт)
    _VARS = json.loads(os.environ.get("VARS_JSON") or "{}")
except ValueError:
    _VARS = {}


def _env(name, default):
    """Пустые значения из GitHub (переменная не задана) считаются незаданными."""
    return os.environ.get(name) or _VARS.get(name) or default


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
RESERVE_MIN = float(_env("RESERVE_MIN", 6.0))   # ниже: выбрасываем, средние новости не публикуем
TOP_MAX_AGE_DAYS = 3        # срочная новость старше этого уходит в запас
RESERVE_MAX_AGE_DAYS = 30   # запас старше этого забывается
FEED_MAX_AGE_DAYS = 7
PER_FEED_LIMIT = 15
SCORE_BATCH = 10
SCORE_MAX_PER_RUN = 40
SAME_KIND_PENALTY = 0.7     # небольшой штраф, если тип такой же, как у прошлого поста
OUTLET_PENALTY = 1.0        # штраф, если издание то же, что у прошлого поста (половина, если у позапрошлого)
RECENT_KEEP = 150           # сколько заголовков опубликованных новостей помним для поиска дублей
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
- Формат ответа: только JSON-объект, без пояснений и без markdown-разметки. Пример схемы:
{{"title": "заголовок", "title_emoji": "🎓", "paragraphs": [{{"emoji": "📌", "text": "первый абзац"}}, {{"emoji": "🔎", "text": "второй абзац"}}], "takeaway": "главное одной фразой", "sad": false}}
- title: цепляющий заголовок без эмодзи. paragraphs: 3-4 коротких абзаца по 1-2 предложения, в тексте абзацев эмодзи нет.
- takeaway: одна короткая фраза (до 110 символов) с главным выводом для абитуриента. Только то, что есть в тексте, без новых чисел и без эмодзи.
- title_emoji и emoji каждого абзаца: ровно один эмодзи, который по СМЫСЛУ подходит именно этому заголовку или абзацу (визы и документы 🛂, деньги и стипендии 💰, наука 🔬, рейтинг 🏆, дата или срок 📅, место 📍, студенты 🎓, правила и законы ⚖️, технологии 💻, здоровье и биология 🧬, космос 🚀, исследование 🔎, предупреждение ⚠️). Эмодзи не повторяются, эмодзи-цифры не используй.
- sad: true, если новость про смерть, трагедию, насилие или преступление, иначе false.
- Выведи только JSON, без вступлений.
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
- Формат ответа: только JSON-объект, без пояснений и без markdown-разметки. Пример схемы:
{{"title": "заголовок", "title_emoji": "🎓", "paragraphs": [{{"emoji": "📌", "text": "первый абзац"}}, {{"emoji": "🔎", "text": "второй абзац"}}], "takeaway": "главное одной фразой", "sad": false}}
- title: цепляющий заголовок без эмодзи. paragraphs: 3-4 коротких абзаца по 1-2 предложения, в тексте абзацев эмодзи нет.
- takeaway: одна короткая фраза (до 110 символов) с главным выводом для абитуриента. Только то, что есть в тексте, без новых чисел и без эмодзи.
- title_emoji и emoji каждого абзаца: ровно один эмодзи, который по СМЫСЛУ подходит именно этому заголовку или абзацу (визы и документы 🛂, деньги и стипендии 💰, наука 🔬, рейтинг 🏆, дата или срок 📅, место 📍, студенты 🎓, правила и законы ⚖️, технологии 💻, здоровье и биология 🧬, космос 🚀, исследование 🔎, предупреждение ⚠️). Эмодзи не повторяются, эмодзи-цифры не используй.
- sad: true, если новость про смерть, трагедию, насилие или преступление, иначе false.
- Выведи только JSON, без вступлений.
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
    if not LLM_KEY or (MODEL and _env("LLM_MODEL", "")):
        return
    try:
        data = json.loads(http_get(f"{LLM_URL}/models", headers={"Authorization": f"Bearer {LLM_KEY}"}))
        avail = {m["id"] for m in data["data"]}
    except Exception as e:
        print("список моделей не получен:", e)
        avail = set()
    usable = sorted(m for m in avail if not any(x in m for x in NOT_TEXT_MODELS))
    pick = lambda prefs: next((m for m in prefs if m in avail), usable[0] if usable else None)
    MODEL = MODEL if _env("LLM_MODEL", "") else (pick(PREFER_MAIN) or "llama-3.3-70b-versatile")
    RANK_MODEL = _env("LLM_RANK_MODEL", "") or pick(PREFER_RANK) or MODEL
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


TOPIC_TAGS = {"campus": "#поступление", "policy": "#визы #правила", "money": "#стипендии", "ranking": "#рейтинги",
              "tech": "#технологии", "space": "#космос", "bio": "#медицина", "science": "#наука", "fact": "#вузы"}


def render(post, credit=""):
    """Текст для Telegram (HTML) и такой же простой текст для подсчёта длины подписи.
    Заголовок жирным, источник ссылкой-названием, подпись фото и хэштег темы курсивом/в конце."""
    body, src, tags = post["text"], post.get("source"), post.get("tags")
    esc = lambda t: html_escape(t, quote=False)
    head, _, rest = body.partition("\n\n")
    def one(p):
        if p.startswith("💡 Главное:"):
            return f"<blockquote>{esc(p)}</blockquote>"
        if post.get("bold_headings") and "\n" in p:  # у статей первая строка раздела: заголовок
            first, second = p.split("\n", 1)
            return f"<b>{esc(first)}</b>\n{esc(second)}"
        return esc(p)
    paras = [one(p) for p in rest.split("\n\n")] if rest else []
    html_t = f"<b>{esc(head)}</b>" + ("\n\n" + "\n\n".join(paras) if paras else "")
    plain = body
    foot_html, foot_plain = [], []
    if src:
        label, url = src
        foot_html.append(f'<i>Источник:</i> <a href="{html_escape(url, quote=True)}">{esc(label)}</a>')
        foot_plain.append(f"Источник: {label}")
    for label, url in post.get("extra_links") or []:
        foot_html.append(f'<i>{esc(label)}:</i> <a href="{html_escape(url, quote=True)}">{esc(urllib.parse.urlparse(url).netloc)}</a>')
        foot_plain.append(f"{label}: {urllib.parse.urlparse(url).netloc}")
    if credit:
        foot_html.append(f"<i>{esc(credit)}</i>")
        foot_plain.append(credit)
    if tags:
        foot_html.append(esc(tags))
        foot_plain.append(tags)
    if foot_html:
        html_t += "\n\n" + "\n".join(foot_html)
        plain += "\n\n" + "\n".join(foot_plain)
    return html_t, plain


def publish(post):
    photo = post.get("photo")
    html_t, plain = render(post)
    if DRY:
        print("----- DRY RUN -----")
        print(plain)
        print("[ссылка]", post["source"][1] if post.get("source") else "нет")
        print("[фото]", (photo["credit"] or "карточка") if photo else "нет")
        print("-------------------")
        return
    chat = os.environ["TELEGRAM_CHAT_ID"]
    sent_photo = False
    if photo:
        cap_html, cap_plain = render(post, photo["credit"])
        try:
            if len(cap_plain) <= 1024:  # лимит подписи к фото в Telegram (считается без тегов)
                tg("sendPhoto", {"chat_id": chat, "caption": cap_html, "parse_mode": "HTML"}, photo["bytes"])
                return
            tg("sendPhoto", {"chat_id": chat, **({"caption": "<i>" + html_escape(photo["credit"], quote=False) + "</i>"} if photo["credit"] else {}),
                             **({"parse_mode": "HTML"} if photo["credit"] else {})}, photo["bytes"])
            sent_photo = True
        except RuntimeError as e:
            print("фото не отправилось, шлю только текст:", e)
    tg("sendMessage", {
        "chat_id": chat, "text": html_t, "parse_mode": "HTML",
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
# один эмодзи целиком: флаг, символ с вариантом или составная последовательность
EMOJI_SEQ = re.compile("(?:[\U0001F1E6-\U0001F1FF]{2}|[\U0001F300-\U0001FAFF\u2600-\u27BF\u2B50\u2B55\u2B05-\u2B07\u2934\u2935\u2B1B\u2B1C]"
                       "[\ufe0f\U0001F3FB-\U0001F3FF]?(?:\u200d[\U0001F300-\U0001FAFF\u2600-\u27BF]\ufe0f?)*)")


def spread_emoji(paras):
    """Если модель собрала эмодзи в кучу (подряд или в конце поста), раскладывает их по началам абзацев:
    заголовок, потом абзацы, равномерно. Если эмодзи уже стоят по тексту, ничего не трогает."""
    seq = EMOJI_SEQ.pattern
    per = [EMOJI_SEQ.findall(p) for p in paras]
    total = sum(map(len, per))
    adjacent = any(re.search(f"(?:{seq})\\s*(?:{seq})", p) for p in paras)
    last_heavy = len(per[-1]) >= 2 and len(per[-1]) * 2 >= total
    if total < 2 or not (adjacent or last_heavy):
        return paras
    emojis = [e for group in per for e in group]
    clean = []
    for p in paras:
        p = EMOJI_SEQ.sub("", p)
        p = re.sub(r"[ \t]{2,}", " ", re.sub(r"\s+([.,!?;:…])", r"\1", p)).strip()
        clean.append(p)
    n = len(clean)
    k = min(len(emojis), n)
    slots = [0] if k == 1 else sorted({round(i * (n - 1) / (k - 1)) for i in range(k)})
    for slot, e in zip(slots, emojis):
        clean[slot] = e + " " + clean[slot]
    for i, e in enumerate(emojis[len(slots):]):  # лишние: после первого предложения абзаца
        j = 1 + i % max(1, n - 1)
        m = re.search(r"[.!?…]", clean[j])
        clean[j] = clean[j][:m.end()] + " " + e + clean[j][m.end():] if m else clean[j] + " " + e
    return clean


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
    paras = spread_emoji(paras)
    if not EMOJI.search(paras[0]):
        paras[0] = DEFAULT_EMOJI.get(kind, "📌") + " " + paras[0]
    return "\n\n".join(paras)


def clean_text(t):
    """Текст без эмодзи и разметки: эмодзи расставляет код."""
    t = re.sub("[\ufe0f\u200d]", "", EMOJI_SEQ.sub("", str(t)))
    return re.sub(r"[ \t]{2,}", " ", re.sub(r"[*#`]+", "", t)).strip()


def compose(obj, kind, n):
    """Собирает пост из JSON модели. Эмодзи подобраны моделью под каждый абзац, а код решает,
    сколько их оставить (n) и куда: заголовок всегда, остальные на начала случайных абзацев."""
    title = clean_text(obj["title"])
    paras = [(clean_text(p["text"]), p.get("emoji")) for p in obj["paragraphs"] if isinstance(p, dict) and clean_text(p["text"])]
    if not title or len(paras) < 2:
        raise ValueError("нет заголовка или мало абзацев")

    def valid(e):
        e = str(e or "").strip()
        return e if EMOJI_SEQ.fullmatch(e) else None

    if obj.get("sad"):
        n = min(n, 2)  # про печальное: смайликов поменьше
    head = valid(obj.get("title_emoji")) or DEFAULT_EMOJI.get(kind, "📌")
    used = {head}
    free = []
    for i, (_, e) in enumerate(paras):
        e = valid(e)
        if e and e not in used:
            used.add(e)
            free.append((i, e))
    chosen = dict(sorted(random.sample(free, min(len(free), max(0, n - 1)))))
    body = [(chosen[i] + " " if i in chosen else "") + t for i, (t, _) in enumerate(paras)]
    gist = clean_text(str(obj.get("takeaway") or ""))
    if 15 <= len(gist) <= 160 and not EMOJI.search(gist):  # строка «Главное» в конце поста
        body.append("💡 Главное: " + gist.rstrip(" ."))
    return "\n\n".join([f"{head} {title}"] + body)


def make_post(prompt_tpl, source_text, kind="fact", **fields):
    known = known_numbers(source_text)
    prompt = prompt_tpl.format(text=source_text, **fields)
    for attempt in range(3):
        out = ask_llm(prompt, max_tokens=1000).strip()
        if out.upper().startswith("SKIP"):
            return None
        m = re.search(r"\{.*\}", out, re.S)
        if m:
            try:
                n = random.choice([1, 2, 2, 3, 3, 4, 4, 5])  # у разных постов разное число смайликов
                text = compose(json.loads(m.group(0), strict=False), kind, n)
            except (ValueError, KeyError, TypeError, AttributeError) as e:
                print(f"  ответ не по схеме: {e} (попытка {attempt + 1})")
                continue
        else:
            text = pretty(out, kind)  # модель ответила обычным текстом
        bad = sorted(n for n in joined_numbers(text) if n not in known)
        if bad:
            print(f"  отклонено, чисел нет в источнике: {bad} (попытка {attempt + 1})")
            continue
        if not 200 <= len(text) <= 1800:
            print(f"  отклонено, длина {len(text)}")
            continue
        return text
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
            photo = wiki_photo(page)
            if not photo and IMAGE_SEARCH:
                photo = commons_photo(page["name"], page["text"], queries=[page["name"]])
            if not photo and AI_IMAGES:
                photo = ai_image("fact", page["name"])
            if not photo and CARD_ON:
                photo = make_card(post, "fact", "Википедия: " + page["name"])
            return {"text": post, "source": ("Википедия", url), "preview": False,
                    "photo": photo, "kind": "fact", "key": title, "tags": TOPIC_TAGS["fact"]}
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


FONT_PATHS = [str(ROOT / "font.ttf"), "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf"]
CARD_ON = _env("CARD", "1") != "0"        # CARD=0 выключает собственные картинки-карточки
AI_IMAGES = _env("IMAGE_AI", "0") == "1"  # IMAGE_AI=1: сначала пробовать нейросетевую иллюстрацию

# Стиль карточки зависит от темы новости: цвета, подпись и рисунок справа.
STYLES = {
    "campus":  dict(label="ПОСТУПЛЕНИЕ", bg="#0F1B3D", line="#1D3067", acc="#F2B84B", txt="#FFF1CF", sub="#8FA3D9"),
    "policy":  dict(label="ПРАВИЛА И ВИЗЫ", bg="#3A1020", line="#6A2A40", acc="#FF8A65", txt="#FFEFE8", sub="#E0A3A8"),
    "money":   dict(label="ДЕНЬГИ И СТИПЕНДИИ", bg="#14281D", line="#24503A", acc="#E6C65C", txt="#FFF8DC", sub="#9BC4A5"),
    "ranking": dict(label="РЕЙТИНГИ", bg="#1B1B2F", line="#33335C", acc="#FFD166", txt="#FFF6D8", sub="#A5A5D6"),
    "tech":    dict(label="ТЕХНОЛОГИИ", bg="#08131F", line="#14405F", acc="#4CC9F0", txt="#E6FAFF", sub="#7FB4CC"),
    "space":   dict(label="КОСМОС И ФИЗИКА", bg="#06060F", line="#26266B", acc="#B388FF", txt="#F0E9FF", sub="#9C93CC"),
    "bio":     dict(label="БИОЛОГИЯ И МЕДИЦИНА", bg="#0C2F3C", line="#17667A", acc="#5EEAD4", txt="#E8FFFA", sub="#7FC4C0"),
    "science": dict(label="НАУКА", bg="#1E1245", line="#3B2A8A", acc="#FF7AB6", txt="#FFF0F8", sub="#B8A5E6"),
    "fact":    dict(label="ФАКТ О ВУЗЕ", bg="#2B1A12", line="#5A3A2A", acc="#F2B84B", txt="#FFF1CF", sub="#C9A58C"),
}
SCIENCE_TOPICS = [
    ("tech", r"\bai\b|artificial intelligence|machine learning|robot|quantum|software|algorithm|computer|semiconductor|\bchips?\b"),
    ("space", r"\bspace\b|planet|galax|telescope|nasa|\bstars?\b|cosmic|\bmars\b|\bmoon\b|black hole|physic|particle|asteroid"),
    ("bio", r"\bgenes?\b|\bdna\b|\bcells?\b|brain|cancer|vaccine|medic|bacteri|virus|biolog|species|disease|protein|health"),
]
ADMISSION_TOPICS = [
    ("policy", r"visa|immigra|work permit|border|regulation|legislat|\bban\b|\blaw\b|policy|crackdown|deport|tariff|\bcap\b"),
    ("money", r"scholarship|funding|\bgrants?\b|tuition|\bfees?\b|\bloans?\b|financial aid|endowment|budget"),
    ("ranking", r"ranking|\branks?\b|league table|\bindex\b|\btop \d+|best universit"),
] + SCIENCE_TOPICS
AI_STYLE = {  # описание стиля для нейросети (только абстракция: без людей, текста и логотипов)
    "campus": "isometric illustration of a university campus and a globe, navy and gold",
    "policy": "flat illustration of documents, passport stamps and a map, burgundy and coral",
    "money": "flat illustration of coins and a graduation cap, dark green and gold",
    "ranking": "flat illustration of a podium and ascending bars, indigo and yellow",
    "tech": "futuristic neural network of glowing nodes, dark blue and cyan",
    "space": "deep space with a ringed planet and stars, black and violet",
    "bio": "abstract DNA helix and cells, deep teal and mint",
    "science": "abstract atom with orbiting electrons, indigo and pink",
    "fact": "classical university building with columns, warm brown and gold",
}


def topic_of(kind, title, body=""):
    if kind == "fact":
        return "fact"
    rules, default = (ADMISSION_TOPICS, "campus") if kind == "admissions" else (SCIENCE_TOPICS, "science")
    for scope in (title.lower(), (title + " " + body[:1500]).lower()):  # заголовок важнее текста
        for name, pat in rules:
            if re.search(pat, scope):
                return name
    return default


def _ell(d, cx, cy, a, b, deg, fill, width):
    th, pts = math.radians(deg), []
    for i in range(121):
        t = 2 * math.pi * i / 120
        x, y = a * math.cos(t), b * math.sin(t)
        pts.append((cx + x * math.cos(th) - y * math.sin(th), cy + x * math.sin(th) + y * math.cos(th)))
    d.line(pts, fill=fill, width=width, joint="curve")


def _rect(d, cx, cy, w, h, deg, outline, width):
    th = math.radians(deg)
    pts = [(cx + x * math.cos(th) - y * math.sin(th), cy + x * math.sin(th) + y * math.cos(th))
           for x, y in ((-w / 2, -h / 2), (w / 2, -h / 2), (w / 2, h / 2), (-w / 2, h / 2))]
    d.line(pts + [pts[0]], fill=outline, width=width, joint="curve")


def _dot(d, x, y, r, fill):
    d.ellipse((x - r, y - r, x + r, y + r), fill=fill)


def motif(d, name, cx, cy, r, rng, line, acc, W, H):
    w = 5
    if name == "campus":  # глобус
        d.ellipse((cx - r, cy - r, cx + r, cy + r), outline=line, width=w)
        d.ellipse((cx - 150, cy - r, cx + 150, cy + r), outline=line, width=w)
        for dy in (-r * 0.5, 0, r * 0.5):
            half = (r * r - dy * dy) ** 0.5
            d.line((cx - half, cy + dy, cx + half, cy + dy), fill=line, width=w)
    elif name == "science":  # атом
        for deg in (0, 60, 120):
            _ell(d, cx, cy, r * 0.85, r * 0.33, deg, line, w)
        _dot(d, cx, cy, 38, acc)
        for deg, t in ((0, 0.4), (60, 2.4), (120, 4.4)):
            th = math.radians(deg)
            x, y = r * 0.85 * math.cos(t), r * 0.33 * math.sin(t)
            _dot(d, cx + x * math.cos(th) - y * math.sin(th), cy + x * math.sin(th) + y * math.cos(th), 14, acc)
    elif name == "space":  # звёзды и планета с кольцом
        for _ in range(140):
            _dot(d, rng.randint(0, W), rng.randint(0, H), rng.choice((1, 1, 2, 3)), line if rng.random() < 0.7 else acc)
        d.ellipse((cx - r * 0.55, cy - r * 0.55, cx + r * 0.55, cy + r * 0.55), fill=line)
        _ell(d, cx, cy, r * 0.95, r * 0.25, -22, acc, 7)
    elif name == "tech":  # сеть узлов
        pts = []
        while len(pts) < 16:
            x, y = rng.uniform(-r, r), rng.uniform(-r, r)
            if x * x + y * y <= r * r:
                pts.append((cx + x, cy + y))
        for i, (x, y) in enumerate(pts):
            near = sorted(range(len(pts)), key=lambda j: (pts[j][0] - x) ** 2 + (pts[j][1] - y) ** 2)[1:3]
            for j in near:
                d.line((x, y, pts[j][0], pts[j][1]), fill=line, width=4)
        for i, (x, y) in enumerate(pts):
            _dot(d, x, y, 16 if i % 5 == 0 else 9, acc if i % 5 == 0 else line)
    elif name == "bio":  # спираль ДНК
        top, bottom, amp = cy - r, cy + r, r * 0.42
        s1, s2 = [], []
        for i in range(0, 101):
            y = top + (bottom - top) * i / 100
            ph = i / 100 * 4 * math.pi
            s1.append((cx + amp * math.sin(ph), y))
            s2.append((cx - amp * math.sin(ph), y))
        for i in range(4, 100, 6):
            d.line((s1[i], s2[i]), fill=line, width=5)
            _dot(d, s1[i][0], s1[i][1], 8, acc)
            _dot(d, s2[i][0], s2[i][1], 8, acc)
        d.line(s1, fill=acc, width=7, joint="curve")
        d.line(s2, fill=line, width=7, joint="curve")
    elif name == "ranking":  # столбцы рейтинга
        base, bw, gap = cy + r * 0.8, 84, 26
        x0 = cx - 70 - (5 * bw + 4 * gap) / 2
        for i, hgt in enumerate((0.35, 0.55, 0.45, 0.8, 1.1)):
            x = x0 + i * (bw + gap)
            d.rectangle((x, base - hgt * r, x + bw, base), fill=acc if i == 4 else line)
        d.line((x0 - 20, base + 6, x0 + 5 * bw + 4 * gap + 20, base + 6), fill=line, width=w)
    elif name == "money":  # монеты
        for k, (dx, dy, rr) in enumerate(((-110, 110, 110), (60, 150, 90), (-20, -70, 120), (160, -90, 80))):
            d.ellipse((cx + dx - rr, cy + dy - rr, cx + dx + rr, cy + dy + rr), fill=line, outline=acc, width=6)
            d.ellipse((cx + dx - rr * 0.7, cy + dy - rr * 0.7, cx + dx + rr * 0.7, cy + dy + rr * 0.7), outline=acc, width=4)
    elif name == "policy":  # документы и печать
        for deg, off in ((-12, -40), (0, 0), (10, 40)):
            _rect(d, cx + off, cy, 360, 470, deg, line, w)
        for k in range(6):
            y = cy - 150 + k * 46
            d.line((cx - 120, y, cx + (80 if k % 2 else 130), y), fill=line, width=5)
        d.ellipse((cx + 0, cy + 70, cx + 190, cy + 260), outline=acc, width=9)
        d.ellipse((cx + 28, cy + 98, cx + 162, cy + 232), outline=acc, width=5)
    elif name == "fact":  # здание с колоннами
        bx0, bx1 = cx - r * 0.85, cx + r * 0.85
        base = cy + r * 0.75
        d.polygon([(bx0 - 20, base - 400), (cx, base - 560), (bx1 + 20, base - 400)], outline=line, width=w)
        d.line((bx0 - 20, base - 400, bx1 + 20, base - 400), fill=line, width=w)
        for i in range(5):
            x = bx0 + 20 + i * (bx1 - bx0 - 40) / 4
            d.rectangle((x - 30, base - 380, x + 30, base - 40), outline=line, width=w)
        for k in range(3):
            d.rectangle((bx0 - 20 - k * 25, base - 40 + k * 28, bx1 + 20 + k * 25, base - 12 + k * 28), outline=line, width=w)


def _pillow():
    """Pillow на раннере GitHub может не стоять: доустанавливаем один раз прямо из бота."""
    try:
        from PIL import Image, ImageDraw, ImageFont
    except ImportError:
        import subprocess, site, importlib
        print("  ставлю Pillow")
        for extra in (["--user"], []):
            r = subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", *extra,
                                "--break-system-packages", "pillow"], capture_output=True, text=True)
            if r.returncode == 0:
                break
            print("  pip не справился:", (r.stderr or r.stdout).strip()[-300:])
        # папка пользовательских пакетов могла появиться только что: без этого import её не видит
        try:
            p = site.getusersitepackages()
            if p not in sys.path:
                sys.path.append(p)
        except Exception:
            pass
        importlib.invalidate_caches()
        try:
            from PIL import Image, ImageDraw, ImageFont
        except ImportError as e:
            print("  Pillow так и не появился:", e)
            return None
    return Image, ImageDraw, ImageFont


def make_card(post_text, kind, outlet, source=""):
    """Собственная картинка 1280x720: стиль зависит от темы новости. Чужих прав нет и она всегда есть."""
    try:
        mods = _pillow()
        font_path = next((f for f in FONT_PATHS if os.path.exists(f)), None)
        if not mods or not font_path:
            return None
        Image, ImageDraw, ImageFont = mods
        title = re.sub(r"\s+", " ", re.sub("[\ufe0f\u200d]", "", EMOJI.sub("", post_text.strip().split("\n")[0]))).strip()
        st = STYLES[topic_of(kind, title, source)]
        rng = random.Random(zlib.crc32(title.encode()))  # у каждого поста свой рисунок, но стабильный
        W, H = 1280, 720
        img = Image.new("RGB", (W, H), st["bg"])
        d = ImageDraw.Draw(img)
        motif(d, next(k for k, v in STYLES.items() if v is st), 1070, 360, 290, rng, st["line"], st["acc"], W, H)
        d.rectangle((80, 78, 160, 86), fill=st["acc"])
        font = lambda size: ImageFont.truetype(font_path, size)
        d.text((80, 104), "МИРОВОЙ КАМПУС  ·  " + st["label"], font=font(30), fill=st["acc"])

        def wrap(size, width):
            f, lines, cur = font(size), [], ""
            for w in title.split():
                t = (cur + " " + w).strip()
                if d.textlength(t, font=f) <= width or not cur:
                    cur = t
                else:
                    lines.append(cur)
                    cur = w
            return lines + [cur], f

        for size in (76, 68, 60, 54, 48, 42):
            lines, f = wrap(size, 760)
            if len(lines) * size * 1.2 <= 440:
                break
        else:
            lines = lines[:6]
            lines[-1] = lines[-1].rstrip(" ,.;:") + "…"
        y = 170
        for ln in lines:
            d.text((80, y), ln, font=f, fill=st["txt"])
            y += int(size * 1.2)
        d.text((80, H - 90), outlet, font=font(30), fill=st["sub"])
        buf = io.BytesIO()
        img.save(buf, "JPEG", quality=90)
        return {"bytes": buf.getvalue(), "credit": ""}
    except Exception as e:
        print("  карточка не вышла:", e)
        return None


def ai_image(kind, title, source=""):
    """Необязательно (IMAGE_AI=1): абстрактная иллюстрация от бесплатного генератора Pollinations.
    Любая ошибка или странный ответ: None, тогда бот рисует карточку."""
    try:
        name = topic_of(kind, title, source)
        prompt = (AI_STYLE[name] + ", abstract editorial illustration, clean vector style, no text, no letters, "
                  "no people, no faces, no logos")
        url = ("https://image.pollinations.ai/prompt/" + urllib.parse.quote(prompt) +
               f"?width=1280&height=720&nologo=true&seed={random.randint(1, 10**6)}")
        data = http_get(url)
        size = image_size(data)
        if size and size[0] >= 500 and 20000 <= len(data) <= 8_000_000:
            return {"bytes": data, "credit": "Иллюстрация: ИИ"}
    except Exception as e:
        print("  ИИ-иллюстрация не вышла:", e)
    return None


# ---------- поиск свободных фото (Wikimedia Commons) с проверкой ИИ ----------

COMMONS_API = "https://commons.wikimedia.org/w/api.php"
IMAGE_SEARCH = _env("IMAGE_SEARCH", "1") != "0"  # IMAGE_SEARCH=0 выключает поиск фото

QUERY_PROMPT = """Нужна свободная фотография к новости (поиск по Wikimedia Commons, запросы на английском).
Заголовок: {title}
Текст: {text}
Назови до 3 коротких поисковых запросов на английском для фотографии КОНКРЕТНОГО места, здания или организации из новости: название университета, кампуса, города, лаборатории, обсерватории. Бери только названия, которые есть в тексте.
Если в новости нет конкретного места или организации, которое можно сфотографировать (общая тема, закон, исследование, рейтинг, человек), ответь []. Не придумывай названия.
Ответь только JSON-массивом строк."""

PICK_PROMPT = """Редактор выбирает фотографию к новости.
Новость: {title}. {text}
Кандидаты (номер. название файла | описание | категории):
{items}
Выбери номер фотографии, которая показывает ТО ЖЕ САМОЕ конкретное место, здание или организацию, о которых новость. Если ни одна явно не подходит (другое место, общий вид, старое событие, портрет, схема), ответь -1. Лучше -1, чем неточная фотография.
Ответь только JSON-объектом вида {"best": номер или -1}"""


def commons_candidates(query):
    """Свободные JPEG с Commons по запросу: лицензия CC или общественное достояние."""
    q = urllib.parse.urlencode({
        "action": "query", "generator": "search", "gsrnamespace": 6, "gsrlimit": 8,
        "gsrsearch": query + " filetype:bitmap", "prop": "imageinfo",
        "iiprop": "url|size|mime|extmetadata", "iiurlwidth": 1280, "format": "json"})
    pages = json.loads(http_get(f"{COMMONS_API}?{q}")).get("query", {}).get("pages", {})
    out = []
    for pg in pages.values():
        ii = (pg.get("imageinfo") or [None])[0]
        if not ii or ii.get("mime") != "image/jpeg" or ii.get("width", 0) < 1000 or ii.get("height", 0) < 500:
            continue
        meta = ii.get("extmetadata", {})
        val = lambda k: meta.get(k, {}).get("value", "")
        lic = val("LicenseShortName")
        if str(val("NonFree")).lower() in ("true", "1") or not re.match(r"(?i)(cc[ -]|cc0|public domain|pd)", lic):
            continue
        out.append({"title": pg.get("title", "").removeprefix("File:"), "url": ii.get("thumburl") or ii["url"],
                    "desc": html_to_text(val("ImageDescription"))[:200], "cats": val("Categories")[:150],
                    "artist": html_to_text(val("Artist"))[:60] or "автор не указан", "lic": lic,
                    "order": pg.get("index", 99)})
    return sorted(out, key=lambda c: c["order"])


def commons_photo(title, text, queries=None):
    """Ищет свободное фото на Commons и просит ИИ выбрать подходящее по названию, описанию и категориям
    файла. Саму картинку ИИ не видит. Если ничего явно не подошло, возвращает None."""
    try:
        if queries is None:
            out = ask_llm(QUERY_PROMPT.replace("{title}", title).replace("{text}", text[:700]),
                          max_tokens=150, model=RANK_MODEL)
            queries = json.loads(re.search(r"\[.*\]", out, re.S).group(0))
        cands, urls = [], set()
        for q in [q for q in queries if isinstance(q, str) and q.strip()][:3]:
            for c in commons_candidates(q):
                if c["url"] not in urls:
                    urls.add(c["url"])
                    cands.append(c)
        cands = cands[:8]
        if not cands:
            print("  фото на Commons: кандидатов нет")
            return None
        lines = "\n".join(f"{i}. {c['title']} | {c['desc']} | {c['cats']}" for i, c in enumerate(cands))
        out = ask_llm(PICK_PROMPT.replace("{title}", title).replace("{text}", text[:500]).replace("{items}", lines),
                      max_tokens=60, model=RANK_MODEL)
        best = int(json.loads(re.search(r"\{.*\}", out, re.S).group(0))["best"])
        if not 0 <= best < len(cands):
            print(f"  фото на Commons: ИИ отклонил всех кандидатов ({len(cands)})")
            return None
        c = cands[best]
        data = fetch_image(c["url"], "https://commons.wikimedia.org/")
        if not data:
            return None
        print("  фото на Commons:", c["title"])
        return {"bytes": data, "credit": f"Фото: {c['artist']}, {c['lic']}, Wikimedia Commons"}
    except (Exception, SystemExit) as e:  # поиск фото не должен ронять запуск
        print("  поиск фото не удался:", e)
        return None


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


STOP = set("this that with from have will into over after about their what when which while more than also been were your says said "
           "university universities college colleges students student higher education school schools international global world study studies".split())


# Страны и известные вузы: если в заголовках названы РАЗНЫЕ, это разные новости ("UK visa fees rise" и "Canada visa fees rise").
ENTITIES = set(("australia canada china india japan korea uk us britain ireland scotland germany france netherlands sweden denmark norway "
                "finland spain italy russia ukraine singapore malaysia indonesia thailand vietnam turkey uae dubai qatar saudi pakistan "
                "bangladesh nigeria ghana kenya africa brazil mexico argentina chile zealand europe asia texas california hong kong "
                "harvard oxford cambridge mit stanford yale princeton columbia caltech berkeley ucl imperial eth toronto mcgill "
                "melbourne sydney tsinghua peking nus cornell duke brown penn dartmouth").split())
SYNONYMS = [(r"\bu\.s\.a?\b|\busa\b|\bunited states\b|\bamerican?\b", "us"),
            (r"\bu\.k\.|\bunited kingdom\b|\bbritish\b|\bengland\b|\bbritain\b", "uk"),
            (r"\bnew zealand\b", "zealand"), (r"\bchinese\b", "china"), (r"\bindian\b", "india"),
            (r"\baustralian\b", "australia"), (r"\bcanadian\b", "canada"), (r"\bjapanese\b", "japan")]


def entities(title):
    t = title.lower()
    for pat, rep_ in SYNONYMS:
        t = re.sub(pat, rep_, t)
    return {w for w in re.findall(r"[a-z]+", t) if w in ENTITIES}


def stems(title):
    """Значимые слова заголовка, обрезанные до 6 букв: так 'tightens' и 'tightened' совпадают."""
    return {w[:6] for w in re.findall(r"[a-zа-яё]{4,}", title.lower()) if w not in STOP}


def similar(a, b):
    """Один и тот же сюжет у разных изданий: у заголовков сильно пересекаются значимые слова."""
    A, B = stems(a), stems(b)
    if not A or not B:
        return False
    EA, EB = entities(a), entities(b)
    if EA and EB and not (EA & EB):  # названы разные страны или вузы
        return False
    inter, small = len(A & B), min(len(A), len(B))
    return (inter >= 3 and inter / small >= 0.6) or (inter >= 4 and inter / small >= 0.45)


def dedupe_fresh(fresh, state):
    """Убирает из новых статей те, что повторяют уже опубликованное, лежащее в очереди, или друг друга
    (из нескольких версий одного сюжета берётся самая подробная). Это экономит и запросы к ИИ."""
    have = [r["title"] for r in state["recent"]] + [p["title"] for p in state["pool"]]
    kept = []
    for it in sorted(fresh, key=lambda i: -len(BODIES.get(i["link"], ""))):
        if any(similar(it["title"], t) for t in have) or any(similar(it["title"], k["title"]) for k in kept):
            state["seen"].append(item_id(it["link"]))
            print(f"  дубль, пропускаю: {it['title'][:70]}")
            continue
        kept.append(it)
    return sorted(kept, key=lambda i: i["date"], reverse=True)


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


BOOST_RE = {  # то, что абитуриенту особенно нужно: чуть повышаем пользу
    "admissions": re.compile(r"(?i)scholarship|olympiad|\bsat\b|admission|financial aid|tuition|international student|\bvisa\b|"
                             r"acceptance rate|early decision|common app|summer program|fellowship|application deadline|"
                             r"\bact\b|\bap exams?\b|toefl|ielts|duolingo|test-optional|test optional|admissions? test|entrance exam|"
                             r"standardi[sz]ed test|a-levels?|\bgre\b|\bgmat\b|baccalaureate|exam (?:change|reform|format)"),
    "science": re.compile(r"(?i)breakthrough|first time|first-ever|nobel|record|discover|new study finds|cure|solves"),
}
DEMOTE_RE = re.compile(r"(?i)^\W*(opinion|column|op-ed|editorial|podcast|webinar|sponsored|partner content|the download)\b|"
                       r"\b(football|basketball|athletic director|head coach)\b")


def adjust(s, title, kind):
    """Модель оценивает по заголовку и паре предложений и ошибается. Добавляем простые правила:
    полезные ключевые слова чуть повышают пользу, мнения, подкасты и спорт понижают."""
    s = dict(s)
    b = BOOST_RE.get(kind)
    if b and b.search(title):
        s["relevant"] = min(10.0, s["relevant"] + 1.0)
    if DEMOTE_RE.search(title):
        s["important"] = max(0.0, s["important"] - 2.5)
        s["relevant"] = max(0.0, s["relevant"] - 1.5)
    return s


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
    fresh = dedupe_fresh(fresh, state)[:SCORE_MAX_PER_RUN]
    print(f"новых новостей: {len(fresh)}, в очереди: {len(state['pool'])}")

    # 3. оценка пачками
    for i in range(0, len(fresh), SCORE_BATCH):
        batch = fresh[i:i + SCORE_BATCH]
        scores = score_batch(batch)
        if not scores:
            continue  # вернёмся к этим новостям в следующий раз
        for it, s in zip(batch, scores):
            s = adjust(s, it["title"], it["kind"])
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
    if not photo and IMAGE_SEARCH:  # поиск свободного фото на Commons, выбор делает ИИ
        photo = commons_photo(item["title"], text)
    if not photo and AI_IMAGES:
        photo = ai_image(item["kind"], item["title"], text)
    if not photo and CARD_ON:  # своей картинки у источника нет или она не подошла
        photo = make_card(post, item["kind"], item["outlet"], item["title"] + " " + text)
    return {"text": post, "source": (item["outlet"], link), "preview": True,
            "photo": photo, "kind": item["kind"], "key": item["id"],
            "title": item["title"], "outlet": item["outlet"],
            "tags": TOPIC_TAGS[topic_of(item["kind"], item["title"], text)]}


# ---------- выбор поста ----------

def outlet_penalty(state, outlet):
    last = state["last_outlets"]
    return (OUTLET_PENALTY if last and last[-1] == outlet else 0) + \
           (OUTLET_PENALTY / 2 if len(last) > 1 and last[-2] == outlet else 0)


def pick_post(state, now):
    # очередь могла получить сюжет, который только что вышел у другого издания: убираем такие
    recent = [r["title"] for r in state["recent"]]
    state["pool"] = [p for p in state["pool"] if not any(similar(p["title"], t) for t in recent)]

    def eff(p):  # срочные: рейтинг минус возраст, штрафы за тот же тип и то же издание подряд
        age = (now - dt.datetime.fromisoformat(p["date"])).total_seconds() / 86400
        return p["rating"] - 0.5 * age - (SAME_KIND_PENALTY if p["kind"] == state["last_kind"] else 0) \
            - outlet_penalty(state, p["outlet"])

    top = sorted((p for p in state["pool"] if p["tier"] == "top"), key=eff, reverse=True)
    reserve = sorted((p for p in state["pool"] if p["tier"] == "reserve"),
                     key=lambda p: p["rating"] - outlet_penalty(state, p["outlet"]), reverse=True)
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
        state["last_outlets"].append("Википедия")
    else:
        state["pool"] = [p for p in state["pool"] if p["id"] != post["key"]]
        state["since_fact"] += 1
        state["recent"].append({"title": post["title"], "outlet": post["outlet"]})
        state["last_outlets"].append(post["outlet"])
    state["recent"] = state["recent"][-RECENT_KEEP:]
    state["last_outlets"] = state["last_outlets"][-5:]
    state["last_kind"] = post["kind"]


# ---------- рейтинги вузов: раз в день топ-10 с картинкой-списком ----------

RANKING_ON = _env("RANKING", "1") != "0"             # RANKING=0 выключает посты с рейтингами
RANKING_HOUR = int(_env("RANKING_HOUR", 19))         # не раньше этого часа по местному времени
RANKING_DYNAMIC = _env("RANKING_DYNAMIC", "1") != "0"   # RANKING_DYNAMIC=0: только списки из rankings.json
RANKING_FORCE = _env("RANKING_FORCE", "") in ("1", "true")  # для проверки: опубликовать рейтинг сейчас


def load_rankings():
    p = ROOT / "rankings.json"
    if not p.exists():
        return []
    return json.loads(p.read_text(encoding="utf-8")).get("lists", [])


def ranking_due(state, now):
    local = now.astimezone(TZ)
    return state.get("ranking_day") != local.date().isoformat() and local.hour >= RANKING_HOUR


def pick_ranking(state):
    """Берём список, который не публиковали дольше всех (ни разу не было: идём по порядку файла)."""
    lists = load_rankings()
    hist = state.get("rank_hist", [])
    last = {l["id"]: max((i for i, h in enumerate(hist) if h == l["id"]), default=-1) for l in lists}
    return min(lists, key=lambda l: last[l["id"]], default=None)


def make_ranking_card(lst):
    """Картинка 1080x1350: заголовок и список вузов с местами. Всегда своя, чужих прав нет."""
    try:
        mods = _pillow()
        font_path = next((f for f in FONT_PATHS if os.path.exists(f)), None)
        if not mods or not font_path:
            print("  нет Pillow или шрифта font.ttf:", bool(mods), font_path)
            return None
        Image, ImageDraw, ImageFont = mods
        W, H = 1080, 1350
        BG1, BG2 = (17, 31, 70), (9, 16, 40)
        GOLD, CREAM, WHITE, MUTED, ROW = (242, 184, 75), (255, 241, 207), (255, 255, 255), (143, 163, 217), (26, 43, 93)
        SILVER, BRONZE, GRID = (205, 212, 226), (205, 140, 90), (42, 65, 127)
        img = Image.new("RGB", (W, H), BG1)
        d = ImageDraw.Draw(img)
        for y in range(H):
            k = y / (H - 1)
            d.line((0, y, W, y), fill=tuple(int(BG1[i] * (1 - k) + BG2[i] * k) for i in range(3)))
        font = lambda s: ImageFont.truetype(font_path, s)
        d.rectangle((70, 64, 150, 72), fill=GOLD)
        d.text((70, 88), "МИРОВОЙ КАМПУС  ·  " + lst.get("label", "РЕЙТИНГИ"), font=font(28), fill=GOLD)

        def wrap(text, f, width):
            lines, cur = [], ""
            for w in text.split():
                t = (cur + " " + w).strip()
                if d.textlength(t, font=f) <= width or not cur:
                    cur = t
                else:
                    lines.append(cur)
                    cur = w
            return lines + [cur]

        for size in (68, 60, 54, 48, 44):
            f = font(size)
            lines = wrap(lst["title"], f, 940)
            if len(lines) <= 2:
                break
        y = 150
        for ln in lines:
            d.text((70, y), ln, font=f, fill=WHITE)
            y += int(size * 1.18)
        d.text((70, y + 8), lst.get("subtitle", ""), font=font(28), fill=MUTED)
        top, bottom = y + 62, H - 105
        rows = lst["rows"]
        n, gap = len(rows), 12
        rh = min(96, (bottom - top - gap * (n - 1)) // n)
        for i, r in enumerate(rows):
            y0 = top + i * (rh + gap)
            d.rounded_rectangle((70, y0, W - 70, y0 + rh), radius=20, fill=ROW)
            rank = str(r.get("rank") or (i + 1))
            col = {"1": GOLD, "2": SILVER, "3": BRONZE}.get(rank, GRID)
            cx, cy, cr = 70 + 14 + rh // 2 - 4, y0 + rh // 2, rh // 2 - 8
            d.ellipse((cx - cr, cy - cr, cx + cr, cy + cr), fill=col)
            fr = font(int(cr * (1.0 if len(rank) < 3 else 0.78)))
            d.text((cx, cy), rank, font=fr, fill=(15, 27, 61) if col != GRID else WHITE, anchor="mm")
            right = W - 70 - 24
            extra, prev = r.get("extra"), r.get("prev")
            if prev and not extra:
                try:
                    diff = int(prev) - int(rank)
                except ValueError:
                    diff = 0
                extra = f"▲ {diff}" if diff > 0 else (f"▼ {-diff}" if diff < 0 else "=")
                ecol = GOLD if diff > 0 else ((240, 120, 120) if diff < 0 else MUTED)
            else:
                ecol = CREAM
            ef = font(max(24, int(rh * 0.34)))
            ew = d.textlength(extra, font=ef) if extra else 0
            if extra:
                d.text((right, cy), extra, font=ef, fill=ecol, anchor="rm")
            x = cx + cr + 24
            maxw = right - ew - 20 - x
            nsize = int(rh * 0.44)
            while d.textlength(r["name"], font=font(nsize)) > maxw and nsize > 22:
                nsize -= 2
            two = rh >= 54 and r.get("sub")
            d.text((x, cy - (int(rh * 0.16) if two else 0)), r["name"], font=font(nsize), fill=WHITE, anchor="lm")
            if two:
                ssize = max(20, int(rh * 0.27))
                while d.textlength(r["sub"], font=font(ssize)) > maxw and ssize > 16:
                    ssize -= 1
                d.text((x, cy + int(rh * 0.27)), r["sub"], font=font(ssize), fill=MUTED, anchor="lm")
        d.text((70, H - 80), "t.me/world_campus_ru", font=font(30), fill=GOLD)
        d.text((W - 70, H - 80), "данные: " + re.split(r"[:(]| и ", lst["source"][0])[0].strip(), font=font(24), fill=MUTED, anchor="ra")
        buf = io.BytesIO()
        img.save(buf, "JPEG", quality=92)
        return {"bytes": buf.getvalue(), "credit": ""}
    except Exception as e:
        print("  картинка рейтинга не вышла:", e)
        return None


# ---------- бесконечные рейтинги: открытые данные ShanghaiRanking (ARWU и рейтинг по 55 предметам) ----------

ARWU_API = "https://www.shanghairanking.com/api/pub/v1/"
ARWU_DEFAULT_YEAR = 2026
SUBJECTS = {  # код: (английское название, русское, эмодзи)
    "AS0101": ("Mathematics", "Математика", "➗"), "AS0102": ("Physics", "Физика", "⚛️"),
    "AS0103": ("Chemistry", "Химия", "🧪"), "AS0104": ("Earth Sciences", "Науки о Земле", "🌋"),
    "AS0105": ("Geography", "География", "🗺"), "AS0106": ("Ecology", "Экология", "🌿"),
    "AS0107": ("Oceanography", "Океанография", "🌊"), "AS0108": ("Atmospheric Science", "Наука об атмосфере", "⛅"),
    "AS0201": ("Mechanical Engineering", "Машиностроение", "⚙️"),
    "AS0202": ("Electrical & Electronic Engineering", "Электротехника и электроника", "🔌"),
    "AS0205": ("Automation & Control", "Автоматика и управление", "🎛"),
    "AS0206": ("Telecommunication Engineering", "Телекоммуникации", "📡"),
    "AS0207": ("Instruments Science & Technology", "Приборостроение", "🔭"),
    "AS0208": ("Biomedical Engineering", "Биомедицинская инженерия", "🫀"),
    "AS0210": ("Computer Science & Engineering", "Информатика", "💻"),
    "AS0211": ("Civil Engineering", "Строительство и архитектура", "🏗"),
    "AS0212": ("Chemical Engineering", "Химическая технология", "⚗️"),
    "AS0213": ("Materials Science & Engineering", "Материаловедение", "🔩"),
    "AS0214": ("Nanoscience & Nanotechnology", "Нанотехнологии", "🔬"),
    "AS0215": ("Energy Science & Engineering", "Энергетика", "⚡"),
    "AS0216": ("Environmental Science & Engineering", "Экологическая инженерия", "♻️"),
    "AS0217": ("Water Resources", "Водные ресурсы", "💧"),
    "AS0219": ("Food Science & Technology", "Пищевые технологии", "🍎"),
    "AS0220": ("Biotechnology", "Биотехнологии", "🧫"),
    "AS0221": ("Aerospace Engineering", "Аэрокосмическая инженерия", "🚀"),
    "AS0222": ("Marine/Ocean Engineering", "Морская инженерия", "🚢"),
    "AS0223": ("Transportation Science & Technology", "Транспортные технологии", "🚆"),
    "AS0224": ("Remote Sensing", "Дистанционное зондирование", "🛰"),
    "AS0226": ("Mining & Mineral Engineering", "Горное дело", "⛏"),
    "AS0227": ("Metallurgical Engineering", "Металлургия", "🏭"),
    "AS0228": ("Textile Science & Engineering", "Текстильная инженерия", "🧵"),
    "AS0229": ("Artificial Intelligence", "Искусственный интеллект", "🤖"),
    "AS0230": ("Robotic Science & Engineering", "Робототехника", "🦾"),
    "AS0301": ("Biological Sciences", "Биология", "🧬"), "AS0302": ("Human Biological Sciences", "Биология человека", "🧬"),
    "AS0303": ("Agricultural Sciences", "Сельскохозяйственные науки", "🌾"), "AS0304": ("Veterinary Sciences", "Ветеринария", "🐾"),
    "AS0401": ("Clinical Medicine", "Клиническая медицина", "🩺"), "AS0402": ("Public Health", "Общественное здравоохранение", "🏥"),
    "AS0403": ("Dentistry & Oral Sciences", "Стоматология", "🦷"), "AS0404": ("Nursing", "Сестринское дело", "💉"),
    "AS0405": ("Medical Technology", "Медицинские технологии", "🩻"), "AS0406": ("Pharmacy & Pharmaceutical Sciences", "Фармация", "💊"),
    "AS0501": ("Economics", "Экономика", "💹"), "AS0502": ("Statistics", "Статистика", "📊"), "AS0503": ("Law", "Право", "⚖️"),
    "AS0504": ("Political Sciences", "Политология", "🏛"), "AS0505": ("Sociology", "Социология", "👥"),
    "AS0506": ("Education", "Педагогика и образование", "🍎"), "AS0507": ("Communication", "Коммуникации и медиа", "🎙"),
    "AS0508": ("Psychology", "Психология", "🧠"), "AS0509": ("Business Administration", "Бизнес-администрирование", "💼"),
    "AS0510": ("Finance", "Финансы", "💰"), "AS0511": ("Management", "Менеджмент", "📈"),
    "AS0512": ("Public Administration", "Государственное управление", "🏛"),
    "AS0513": ("Hospitality & Tourism Management", "Гостиничный и туристический менеджмент", "🏨"),
    "AS0515": ("Library & Information Science", "Библиотечное и информационное дело", "📚"),
}
REGIONS = {  # как называет страну ShanghaiRanking: (родительный падеж, именительный)
    "United States": ("США", "США"), "United Kingdom": ("Великобритании", "Великобритания"), "China": ("Китая", "Китай"),
    "Mainland China": ("Китая", "Китай"), "Australia": ("Австралии", "Австралия"), "Canada": ("Канады", "Канада"),
    "Germany": ("Германии", "Германия"), "France": ("Франции", "Франция"), "Japan": ("Японии", "Япония"),
    "Netherlands": ("Нидерландов", "Нидерланды"), "Switzerland": ("Швейцарии", "Швейцария"), "Italy": ("Италии", "Италия"),
    "Singapore": ("Сингапура", "Сингапур"), "South Korea": ("Южной Кореи", "Южная Корея"), "Korea": ("Южной Кореи", "Южная Корея"),
    "Spain": ("Испании", "Испания"), "Sweden": ("Швеции", "Швеция"), "Denmark": ("Дании", "Дания"), "Belgium": ("Бельгии", "Бельгия"),
    "Russia": ("России", "Россия"), "Hong Kong": ("Гонконга", "Гонконг"), "Israel": ("Израиля", "Израиль"),
    "Brazil": ("Бразилии", "Бразилия"), "India": ("Индии", "Индия"), "Saudi Arabia": ("Саудовской Аравии", "Саудовская Аравия"),
    "Finland": ("Финляндии", "Финляндия"), "Norway": ("Норвегии", "Норвегия"), "Austria": ("Австрии", "Австрия"),
    "Ireland": ("Ирландии", "Ирландия"), "New Zealand": ("Новой Зеландии", "Новая Зеландия"), "Taiwan": ("Тайваня", "Тайвань"),
    "Turkey": ("Турции", "Турция"), "Iran": ("Ирана", "Иран"), "Poland": ("Польши", "Польша"), "Portugal": ("Португалии", "Португалия"),
    "Czech Republic": ("Чехии", "Чехия"), "Egypt": ("Египта", "Египет"), "South Africa": ("ЮАР", "ЮАР"), "Malaysia": ("Малайзии", "Малайзия"),
    "Mexico": ("Мексики", "Мексика"), "Chile": ("Чили", "Чили"), "Argentina": ("Аргентины", "Аргентина"), "Greece": ("Греции", "Греция"),
    "Pakistan": ("Пакистана", "Пакистан"), "Thailand": ("Таиланда", "Таиланд"), "Estonia": ("Эстонии", "Эстония"),
}
SHORT_NAMES = {"Massachusetts Institute of Technology": "MIT", "California Institute of Technology": "Caltech",
               "University of California, Berkeley": "UC Berkeley", "University of California, Los Angeles": "UCLA",
               "University of California, San Diego": "UC San Diego", "Swiss Federal Institute of Technology Lausanne": "EPFL",
               "Swiss Federal Institute of Technology Zurich": "ETH Zurich", "Georgia Institute of Technology": "Georgia Tech"}
ARWU_NOTE = {"world": ("ℹ️", "ARWU считает научные достижения: Нобелевские премии и медали Филдса, цитируемость, статьи в Nature и Science. Качество преподавания он не оценивает."),
             "subject": ("ℹ️", "Это научный рейтинг: он оценивает публикации, цитирование, международное сотрудничество и награды, а не качество преподавания.")}


def arwu_get(kind, **params):
    j = json.loads(http_get(f"{ARWU_API}{kind}/rank?" + urllib.parse.urlencode(params)))
    if j.get("code") != 200:
        raise RuntimeError(f"ShanghaiRanking: {j.get('msg')}")
    return j["data"]


def arwu_entries(kind, year, code=None):
    params = {"version": year, **({"subj_code": code} if code else {})}
    out = [{"name": SHORT_NAMES.get(e["univNameEn"], e["univNameEn"]), "country": e.get("region") or "",
            "rank": str(e["ranking"]).strip()} for e in (arwu_get(kind, **params).get("rankings") or [])]
    if not out:
        raise RuntimeError("пустой список")
    return out


def arwu_year(state, now):
    """Свежий год берём из перечня предметов самого сайта, раз в неделю."""
    at = state.get("arwu_year_at")
    if state.get("arwu_year") and at and (now - dt.datetime.fromisoformat(at)).days < 7:
        return state["arwu_year"]
    try:
        cats = arwu_get("gras", version=2025, subj_code="RS0210")["subjCategory"]
        years = [int(y) for c in cats for d in c["detail"] for y in str(d["versions"]).split(",") if y.strip().isdigit()]
        state["arwu_year"], state["arwu_year_at"] = max(years), iso(now)
    except Exception as e:
        print("  год рейтинга не определился:", e)
    return state.get("arwu_year", ARWU_DEFAULT_YEAR)


def _nom(c):
    return REGIONS.get(c, (c, c))[1]


def _gen(c):
    return REGIONS.get(c, (c, c))[0]


def _leaders(rows):
    from collections import Counter
    c, n = Counter(r["country"] for r in rows).most_common(1)[0]
    return ("🌍", f"Больше всего вузов в списке у страны «{_nom(c)}»: {n} из {len(rows)}.") if n >= 3 else None


def dynamic_ranking(state, now):
    """Собирает новый список из данных ShanghaiRanking. Каждый вариант (предмет, страна, год) показываем один раз."""
    year = arwu_year(state, now)
    hist = set(state.get("rank_hist", []))
    cache = {}

    def get(kind, y, code=None):
        k = (kind, y, code)
        if k not in cache:
            cache[k] = arwu_entries(kind, y, code)
        return cache[k]

    base = {"tags": "#рейтинги #ARWU #университеты #наука"}
    gras_url = lambda code: f"https://www.shanghairanking.com/rankings/gras/{year}/{code}"
    arwu_src = ("ShanghaiRanking (ARWU)", f"https://www.shanghairanking.com/rankings/arwu/{year}")
    order = random.choices(["subj", "subjc", "risers", "arwuc", "slice"], weights=[30, 30, 20, 10, 10], k=5)
    for kind in dict.fromkeys(order):
        try:
            if kind == "subj":
                code = random.choice([c for c in SUBJECTS if f"gras:{year}:{c}" not in hist])
                en, ru, em = SUBJECTS[code]
                top = get("gras", year, code)[:10]
                notes = [("🥇", f"Лидер: {top[0]['name']}, {_nom(top[0]['country'])}.")]
                notes += [n for n in [_leaders(top)] if n] + [ARWU_NOTE["subject"]]
                return {**base, "id": f"gras:{year}:{code}", "emoji": em, "title": f"{ru}: топ-10 университетов мира",
                        "subtitle": f"ShanghaiRanking по предметам {year}",
                        "source": ("ShanghaiRanking: рейтинг по предметам", gras_url(code)),
                        "rows": [{"rank": r["rank"], "name": r["name"], "sub": _nom(r["country"])} for r in top], "notes": notes}
            if kind == "subjc":
                code = random.choice(list(SUBJECTS))
                en, ru, em = SUBJECTS[code]
                allr = get("gras", year, code)
                regs = {}
                for r in allr:
                    regs.setdefault(r["country"], []).append(r)
                ok = [c for c, v in regs.items() if len(v) >= 6 and c in REGIONS and f"grasc:{year}:{code}:{c}" not in hist]
                if not ok:
                    continue
                c = random.choice(ok)
                top = regs[c][:10]
                notes = [("🌍", f"Лучший вуз {_gen(c)} в этом предмете: {top[0]['name']}, {top[0]['rank']} место в мире."), ARWU_NOTE["subject"]]
                return {**base, "id": f"grasc:{year}:{code}:{c}", "emoji": em, "title": f"{ru}: топ-10 университетов {_gen(c)}",
                        "subtitle": f"место в списке · место в мире, ShanghaiRanking {year}",
                        "source": ("ShanghaiRanking: рейтинг по предметам", gras_url(code)),
                        "rows": [{"name": r["name"], "extra": f"в мире {r['rank']}"} for r in top], "notes": notes}
            if kind == "risers":
                code = random.choice([c for c in SUBJECTS if f"rise:{year}:{c}" not in hist])
                en, ru, em = SUBJECTS[code]
                old = {r["name"]: r["rank"] for r in get("gras", year - 1, code)}
                gains = []
                for r in get("gras", year, code):
                    if r["rank"].isdigit() and old.get(r["name"], "").isdigit() and int(old[r["name"]]) > int(r["rank"]):
                        gains.append((int(old[r["name"]]) - int(r["rank"]), r, int(old[r["name"]])))
                gains.sort(key=lambda g: (-g[0], int(g[1]["rank"])))
                if len(gains) < 4:
                    continue
                gains = gains[:8]
                g0 = gains[0]
                notes = [("🚀", f"{g0[1]['name']} поднялся на {g0[0]} мест: с {g0[2]} на {g0[1]['rank']}."), ARWU_NOTE["subject"]]
                return {**base, "id": f"rise:{year}:{code}", "emoji": "🚀", "title": f"{ru}: кто поднялся быстрее всех за год",
                        "subtitle": f"изменение места, ShanghaiRanking {year - 1} → {year}",
                        "source": ("ShanghaiRanking: рейтинг по предметам", gras_url(code)),
                        "rows": [{"rank": r["rank"], "name": r["name"], "sub": f"{_nom(r['country'])} · было {o}", "prev": o}
                                 for _, r, o in gains], "notes": notes}
            if kind == "arwuc":
                regs = {}
                for r in get("arwu", year):
                    regs.setdefault(r["country"], []).append(r)
                ok = [c for c, v in regs.items() if len(v) >= 8 and c in REGIONS and f"arwuc:{year}:{c}" not in hist]
                if not ok:
                    continue
                c = random.choice(ok)
                top = regs[c][:10]
                notes = [("🌍", f"Лучший вуз {_gen(c)}: {top[0]['name']}, {top[0]['rank']} место в мире."), ARWU_NOTE["world"]]
                return {**base, "id": f"arwuc:{year}:{c}", "emoji": "🎓", "title": f"Топ-10 университетов {_gen(c)} по ARWU {year}",
                        "subtitle": f"место в списке · место в мире, ARWU {year}", "source": arwu_src,
                        "rows": [{"name": r["name"], "extra": f"в мире {r['rank']}"} for r in top], "notes": notes}
            if kind == "slice":
                start = random.choice([s for s in range(0, 100, 10) if f"arwus:{year}:{s}" not in hist])
                part = get("arwu", year)[start:start + 10]
                notes = [_leaders(part), ARWU_NOTE["world"]]
                return {**base, "id": f"arwus:{year}:{start}", "emoji": "🏆",
                        "title": f"ARWU {year}: места {start + 1}–{start + 10}" if start else f"Топ-10 университетов мира по ARWU {year}",
                        "subtitle": "Academic Ranking of World Universities (Шанхайский рейтинг)", "source": arwu_src,
                        "rows": [{"rank": r["rank"], "name": r["name"], "sub": _nom(r["country"])} for r in part],
                        "notes": [n for n in notes if n]}
        except IndexError:  # все варианты этого типа уже показаны
            continue
        except Exception as e:
            print(f"  динамический рейтинг ({kind}) не вышел: {e}")
    return None


def build_ranking_post(state, now=None):
    lst = None
    if RANKING_DYNAMIC and random.random() < 0.8:  # 80% новых списков из открытых данных, 20% подборка из rankings.json
        lst = dynamic_ranking(state, now or utcnow())
    lst = lst or pick_ranking(state)
    if not lst:
        return None
    print("рейтинг:", lst["id"])
    paras = [f"{e} {t}" for e, t in lst.get("notes", [])]
    photo = make_ranking_card(lst)
    if not photo:  # без картинки список идёт текстом
        paras.insert(0, "\n".join(f"{r.get('rank') or i + 1}. {r['name']}" for i, r in enumerate(lst["rows"])))
    text = "\n\n".join([f"{lst['emoji']} {lst['title']}"] + paras)
    return {"text": text, "source": tuple(lst["source"]), "preview": False, "photo": photo,
            "kind": "ranking", "key": lst["id"], "tags": lst.get("tags", TOPIC_TAGS["ranking"])}


def apply_ranking(state, post, now):
    state["ranking_day"] = now.astimezone(TZ).date().isoformat()
    state["rank_hist"] = (state.get("rank_hist", []) + [post["key"]])[-3000:]


# ---------- опросы (раз в день) и шпаргалки (раз в два дня) ----------

POLL_ON = _env("POLLS", "1") != "0"                  # POLLS=0 выключает опросы
POLL_HOUR = int(_env("POLL_HOUR", 12))               # не раньше этого часа по местному времени
POLL_FORCE = _env("POLL_FORCE", "") in ("1", "true")
TIPS_ON = _env("TIPS", "1") != "0"                   # TIPS=0 выключает шпаргалки
TIPS_HOUR = int(_env("TIPS_HOUR", 15))
TIPS_EVERY_DAYS = int(_env("TIPS_EVERY_DAYS", 2))
TIPS_FORCE = _env("TIPS_FORCE", "") in ("1", "true")


def _local_day(now):
    return now.astimezone(TZ).date()


def poll_due(state, now):
    return state.get("poll_day") != _local_day(now).isoformat() and now.astimezone(TZ).hour >= POLL_HOUR


def tips_due(state, now):
    last = state.get("tips_day")
    gap = (_local_day(now) - dt.date.fromisoformat(last)).days if last else 99
    return gap >= TIPS_EVERY_DAYS and now.astimezone(TZ).hour >= TIPS_HOUR


def _lru(items, hist):
    last = {i["id"]: max((n for n, h in enumerate(hist) if h == i["id"]), default=-1) for i in items}
    return min(items, key=lambda i: last[i["id"]], default=None)


def arwu_quiz(state, now):
    """Вопрос «какой вуз выше в рейтинге»: два-три вуза из топ-100 ARWU, правильный ответ вычисляется по данным."""
    year = arwu_year(state, now)
    top = [e for e in arwu_entries("arwu", year)[:100] if e["rank"].isdigit()]
    for _ in range(30):
        trio = sorted(random.sample(top, 3), key=lambda e: int(e["rank"]))
        if int(trio[1]["rank"]) - int(trio[0]["rank"]) >= 10 and int(trio[2]["rank"]) - int(trio[1]["rank"]) >= 10:
            break
    else:
        return None
    names = [e["name"] for e in trio]
    key = "quiz:" + "|".join(sorted(names))
    if key in state.get("poll_hist", []):
        return None
    options = names[:]
    random.shuffle(options)
    expl = f"Места в ARWU {year}: " + ", ".join(f"{e['name']} {e['rank']}" for e in trio)
    return {"kind": "poll", "key": key, "question": f"Какой университет выше в рейтинге ARWU {year}?", "options": options,
            "quiz": True, "correct": options.index(names[0]), "explanation": expl[:200]}


def build_poll(state, now):
    p = None
    if RANKING_DYNAMIC and random.random() < 0.5:
        try:
            p = arwu_quiz(state, now)
        except Exception as e:
            print("  опрос из ARWU не вышел:", e)
    if not p:
        polls = json.loads((ROOT / "polls.json").read_text(encoding="utf-8"))["polls"]
        q = _lru(polls, state.get("poll_hist", []))
        if not q:
            return None
        opts = q["o"][:]
        if "a" in q:  # у викторины порядок вариантов перемешиваем, правильный ответ отслеживаем
            right = opts[q["a"]]
            random.shuffle(opts)
            p = {"kind": "poll", "key": q["id"], "question": q["q"], "options": opts, "quiz": True,
                 "correct": opts.index(right), "explanation": q["e"]}
        else:
            p = {"kind": "poll", "key": q["id"], "question": q["q"], "options": opts, "quiz": False}
    print("опрос:", p["key"])
    return p


def publish_poll(p):
    if DRY:
        print("----- DRY RUN (опрос) -----")
        print(p["question"], p["options"], p.get("correct"))
        return
    fields = {"chat_id": os.environ["TELEGRAM_CHAT_ID"], "question": p["question"], "is_anonymous": "true",
              "options": json.dumps([{"text": o} for o in p["options"]], ensure_ascii=False)}
    if p["quiz"]:
        fields.update({"type": "quiz", "correct_option_id": p["correct"], "explanation": p["explanation"]})
    tg("sendPoll", fields)


def apply_poll(state, p, now):
    state["poll_day"] = _local_day(now).isoformat()
    state["poll_hist"] = (state.get("poll_hist", []) + [p["key"]])[-300:]


def build_tips_post(state):
    tips = json.loads((ROOT / "tips.json").read_text(encoding="utf-8"))["tips"]
    t = _lru(tips, state.get("tips_hist", []))
    if not t:
        return None
    print("шпаргалка:", t["id"])
    text = "\n\n".join([f"{t['emoji']} {t['title']}"] + [f"{e} {x}" for e, x in t["paras"]])
    photo = make_card(text, "admissions", "Шпаргалка абитуриента", t["title"]) if CARD_ON else None
    return {"text": text, "source": None, "preview": False, "photo": photo, "kind": "tips", "key": t["id"],
            "tags": t.get("tags", "#шпаргалка")}


def apply_tips(state, post, now):
    state["tips_day"] = _local_day(now).isoformat()
    state["tips_hist"] = (state.get("tips_hist", []) + [post["key"]])[-100:]


# ---------- календарь дедлайнов (раз в неделю) ----------

DEADLINES_ON = _env("DEADLINES", "1") != "0"        # DEADLINES=0 выключает календарь
DEADLINES_HOUR = int(_env("DEADLINES_HOUR", 10))
DEADLINES_FORCE = _env("DEADLINES_FORCE", "") in ("1", "true")
DEADLINES_WINDOW_DAYS = int(_env("DEADLINES_WINDOW", 50))
RU_MONTHS = ["января", "февраля", "марта", "апреля", "мая", "июня", "июля", "августа", "сентября", "октября", "ноября", "декабря"]


def upcoming_deadlines(now, window=DEADLINES_WINDOW_DAYS):
    """Сроки из deadlines.json на ближайшие дни. Даты хранятся как месяц-день и каждый год переносятся сами;
    если сезон не тот, в котором их сверяли, к дате добавляется «около»."""
    data = json.loads((ROOT / "deadlines.json").read_text(encoding="utf-8"))
    today = _local_day(now)
    out = []
    for it in data["items"]:
        m, d = map(int, it["md"].split("-"))
        date = dt.date(today.year, m, d)
        if date < today:
            date = dt.date(today.year + 1, m, d)
        days = (date - today).days
        if days <= window:
            out.append({**it, "date": date, "days": days, "approx": date.year != it.get("verified", date.year)})
    return sorted(out, key=lambda x: (x["date"], x["uni"])), data


def deadlines_due(state, now):
    wk = "%d-%02d" % now.astimezone(TZ).isocalendar()[:2]
    return state.get("deadlines_week") != wk and now.astimezone(TZ).hour >= DEADLINES_HOUR


def build_deadlines_post(state, now):
    items, data = upcoming_deadlines(now)
    if len(items) < 3:
        return None
    items = items[:11]
    rows = []
    for it in items:
        when = f"{'около ' if it['approx'] else ''}{it['date'].day} {RU_MONTHS[it['date'].month - 1]}"
        left = "сегодня" if it["days"] == 0 else ("завтра" if it["days"] == 1 else f"через {it['days']} дн.")
        rows.append({"rank": str(it["days"]), "name": f"{it['uni']}: {it['round']}", "sub": when + (" · " + it["note"] if it.get("note") else ""), "extra": left})
    lst = {"title": "Ближайшие дедлайны в лучшие университеты", "subtitle": "число в кружке: сколько дней осталось", "rows": rows,
           "source": tuple(data["source"]), "emoji": "📅", "label": "ДЕДЛАЙНЫ"}
    notes = [("🔒", "Early Decision обязывает пойти в вуз, если приняли. Restrictive и Single-Choice Early Action не обязывают, но ограничивают подачу в другие ранние программы."),
             ("⚠️", "Даты могут сдвигаться на день-два от сезона к сезону. Проверяй их на странице приёма самого вуза.")]
    photo = make_ranking_card(lst)
    paras = [f"{e} {t}" for e, t in notes]
    if not photo:
        paras.insert(0, "\n".join(f"{r['sub']}: {r['name']}" for r in rows))
    return {"text": "\n\n".join([f"📅 {lst['title']}"] + paras), "source": lst["source"], "preview": False, "photo": photo,
            "kind": "deadlines", "key": "deadlines", "tags": "#дедлайны #поступление"}


def apply_deadlines(state, now):
    state["deadlines_week"] = "%d-%02d" % now.astimezone(TZ).isocalendar()[:2]


# ---------- статья про вуз из топ-100 (раз в день, утром) ----------

ARTICLE_ON = _env("ARTICLES", "1") != "0"           # ARTICLES=0 выключает статьи о вузах
ARTICLE_HOUR = int(_env("ARTICLE_HOUR", 8))
ARTICLE_FORCE = _env("ARTICLE_FORCE", "") in ("1", "true")
ARTICLE_CHARS = int(_env("ARTICLE_CHARS", 10000))
SEC_RE = re.compile(r"(?i)academ|admission|financ|aid|scholar|tuition|cost|student|campus|research|school|college|facult|program|department|athlet|alumni|history|organi[sz]ation|international")
SEC_SKIP = re.compile(r"(?i)see also|references|external links|further reading|notes|footnotes|bibliography|gallery|in popular culture|controversy|controversies")
OFFICIAL_KEYS = ["scholarship", "financial aid", "financial-aid", "international", "admission", "tuition", "cost", "apply"]

ARTICLE_PROMPT = """Ты ведёшь русскоязычный Telegram-канал для школьников, которые думают о поступлении в зарубежные вузы.
Ниже материалы про университет: {name}. Это статья Википедии и, возможно, страницы официального сайта вуза.
Напиши обзорную статью для абитуриента.

Правила:
- """ + TRANSLATE + """
- Используй только то, что прямо написано в материалах. Ничего не добавляй из своих знаний и не угадывай.
- Числа, годы и названия бери в точности как в материалах. Не округляй, не считай, не выводи новые числа.
- Про рейтинги не пиши: они добавляются отдельно.
- Если в материалах нет данных для раздела (например, про стипендии или требования), раздел НЕ пиши. Лучше меньше разделов, чем выдумка.
- Разделы выбирай только из тех, по которым есть данные: «О вузе», «Сильные направления», «Поступление и требования», «Стоимость и стипендии», «Студенческая жизнь», «Известные выпускники и достижения».
- От 3 до 6 разделов, в каждом 2-4 коротких предложения. Весь текст 1800-3200 символов, без хэштегов, без разметки (звёздочек и решёток).
- Формат ответа: только JSON-объект без пояснений. Схема:
{{"title": "заголовок с названием вуза", "title_emoji": "🎓", "intro": "1-2 предложения о вузе", "sections": [{{"emoji": "🔬", "heading": "Сильные направления", "text": "текст раздела"}}], "takeaway": "главное одной фразой до 110 символов"}}
- emoji каждого раздела: один эмодзи по смыслу раздела, эмодзи не повторяются, в текстах эмодзи нет.
- Если материалов недостаточно для статьи, ответь одним словом: SKIP.

Материалы:
{text}"""


def wiki_sections(title):
    """Статья Википедии с заголовками разделов: введение плюс разделы про учёбу, поступление, деньги, жизнь."""
    q = urllib.parse.urlencode({"action": "query", "prop": "extracts|pageimages|pageprops", "explaintext": 1, "exsectionformat": "wiki",
                                "piprop": "thumbnail|name", "pithumbsize": 1280, "ppprop": "wikibase_item", "redirects": 1,
                                "titles": title, "format": "json"})
    page = next(iter(json.loads(http_get(f"https://en.wikipedia.org/w/api.php?{q}"))["query"]["pages"].values()))
    text = page.get("extract", "")
    parts = re.split(r"\n(=+) (.+?) \1\n", text)
    lead, secs = parts[0].strip(), []
    for i in range(1, len(parts) - 2, 3):
        title_, body = parts[i + 1].strip(), parts[i + 2].strip()
        if body and SEC_RE.search(title_) and not SEC_SKIP.search(title_):
            secs.append((title_, body))
    out, total = [lead[:2500]], 2500
    for t_, b in secs:
        if total >= ARTICLE_CHARS * 0.65:
            break
        chunk = f"== {t_} ==\n{b[:1800]}"
        out.append(chunk)
        total += len(chunk)
    return {"name": page.get("title", title), "text": "\n\n".join(out), "full_len": len(text), "image_file": page.get("pageimage"),
            "image_url": page.get("thumbnail", {}).get("source"), "item": page.get("pageprops", {}).get("wikibase_item")}


def official_pages(item):
    """Официальный сайт вуза из Викиданных и до трёх его страниц про поступление и стипендии. Любая ошибка: пусто."""
    try:
        j = json.loads(http_get("https://www.wikidata.org/w/api.php?" + urllib.parse.urlencode(
            {"action": "wbgetclaims", "entity": item, "property": "P856", "format": "json"})))
        home = j["claims"]["P856"][0]["mainsnak"]["datavalue"]["value"]
    except Exception as e:
        print("  официальный сайт не найден:", e)
        return None, []
    try:
        html = http_get(home).decode("utf-8", errors="replace")
    except Exception as e:
        print("  сайт вуза не открылся:", e)
        return home, []
    host = urllib.parse.urlparse(home).netloc.lower()
    root = ".".join(host.split(".")[-2:]) if not re.search(r"\.(ac|co|edu)\.[a-z]{2}$", host) else ".".join(host.split(".")[-3:])
    found = {}
    for m in re.finditer(r'(?is)<a\s[^>]*href=["\']([^"\'#]+)["\'][^>]*>(.*?)</a>', html):
        href, label = urllib.parse.urljoin(home, m.group(1)), re.sub(r"<[^>]+>|\s+", " ", m.group(2)).strip().lower()
        h = urllib.parse.urlparse(href)
        if h.scheme not in ("http", "https") or not h.netloc.lower().endswith(root) or re.search(r"(?i)\.(pdf|jpg|png|zip)$", h.path):
            continue
        for rank, k in enumerate(OFFICIAL_KEYS):
            if k in label or k in h.path.lower():
                found.setdefault(href, rank)
                break
    pages = []
    for href in sorted(found, key=found.get)[:3]:
        try:
            txt = html_to_text(http_get(href).decode("utf-8", errors="replace"))
            if len(txt) > 600:
                pages.append((href, txt[:2500]))
        except Exception as e:
            print("  страница вуза не открылась:", href[:60], e)
    return home, pages


def strong_subjects(name, year):
    """Лучшие предметы вуза по ARWU: просматриваем все предметы параллельно, берём пять с лучшими местами."""
    from concurrent.futures import ThreadPoolExecutor

    def one(code):
        try:
            for e in arwu_entries("gras", year, code):
                if e["name"] == name:
                    return (int(e["rank"]), SUBJECTS[code][1]) if e["rank"].isdigit() else None
        except Exception:
            return None
    with ThreadPoolExecutor(8) as ex:
        res = [r for r in ex.map(one, list(SUBJECTS)) if r]
    return sorted(res)[:5]


def compose_article(obj, rank_line):
    title = clean_text(obj["title"])
    intro = clean_text(obj.get("intro") or "")
    secs = []
    for s in obj.get("sections") or []:
        if isinstance(s, dict) and clean_text(s.get("text") or "") and clean_text(s.get("heading") or ""):
            e = str(s.get("emoji") or "").strip()
            secs.append(((e if EMOJI_SEQ.fullmatch(e) else "📌"), clean_text(s["heading"]), clean_text(s["text"])))
    if not title or not intro or len(secs) < 3:
        raise ValueError("мало разделов")
    head = str(obj.get("title_emoji") or "").strip()
    head = head if EMOJI_SEQ.fullmatch(head) else "🎓"
    gist = clean_text(str(obj.get("takeaway") or ""))
    blocks = [f"{e} {h}\n{t}" for e, h, t in secs]
    return head, title, intro, blocks, (gist.rstrip(" .") if 15 <= len(gist) <= 160 and not EMOJI.search(gist) else "")


def article_for(name, year, ranked):
    """Собирает статью о вузе. None, если материалов мало или модель ответила не по правилам."""
    page = wiki_sections(name)
    if page["full_len"] < 4000:
        print("  статья Википедии короткая, пропускаю")
        return None
    home, pages = official_pages(page["item"]) if page.get("item") else (None, [])
    text = page["text"]
    for href, t in pages:
        text += f"\n\n=== Официальный сайт вуза ({href}) ===\n{t}"
    text = text[:ARTICLE_CHARS]
    known = known_numbers(text)
    prompt = ARTICLE_PROMPT.format(text=text, name=page["name"])
    for attempt in range(3):
        out = ask_llm(prompt, max_tokens=2200).strip()
        if out.upper().startswith("SKIP"):
            return None
        m = re.search(r"\{.*\}", out, re.S)
        if not m:
            continue
        try:
            head, title, intro, blocks, gist = compose_article(json.loads(m.group(0), strict=False), "")
        except (ValueError, KeyError, TypeError, AttributeError) as e:
            print(f"  ответ не по схеме: {e} (попытка {attempt + 1})")
            continue
        bad = sorted(n for n in joined_numbers("\n".join([title, intro] + blocks + [gist])) if n not in known)
        if bad:
            print(f"  отклонено, чисел нет в источнике: {bad} (попытка {attempt + 1})")
            continue
        extra = []
        if ranked:
            rank, subjects = ranked() if callable(ranked) else ranked
            line = f"🏆 Рейтинг ShanghaiRanking (ARWU) {year}: {rank} место в мире."
            if subjects:
                line += " Лучшие направления по этому рейтингу: " + ", ".join(f"{s} ({r})" for r, s in subjects) + "."
            extra.append(line)
        body_text = "\n".join(blocks)
        if not re.search(r"(?i)поступлен|стипенд|стоимост|требован", body_text):
            extra.append("ℹ️ Условия поступления и стипендии лучше проверить на официальном сайте вуза: они меняются каждый год.")
        if gist:
            extra.append("💡 Главное: " + gist)
        parts = [f"{head} {title}", intro] + blocks
        while len("\n\n".join(parts + extra)) > 3500 and len(parts) > 5:
            parts.pop()
        return {"text": "\n\n".join(parts + extra), "page": page, "home": home}
    return None


def build_article_post(state, now):
    init_models()
    year = arwu_year(state, now)
    done = set(state.get("profiled", []))
    world = []
    try:
        world = [e for e in arwu_entries("arwu", year)[:100] if e["rank"].isdigit()]
    except Exception as e:
        print("  список ARWU недоступен, беру вуз из своего списка:", e)
    cands = [(e["name"], e) for e in world if e["name"] not in done] or [(u, None) for u in all_universities(state) if u not in done]
    random.shuffle(cands)
    for name, e in cands[:3]:
        print("статья о вузе:", name)
        state.setdefault("profiled", []).append(name)  # неудачные тоже помечаем, чтобы не биться об один и тот же
        try:
            ranked = (lambda: (e["rank"], strong_subjects(name, year))) if e else None
            art = article_for(name, year, ranked)
        except Exception as ex:
            print("  статья не вышла:", ex)
            continue
        if not art:
            continue
        page = art["page"]
        photo = wiki_photo(page)
        if not photo and IMAGE_SEARCH:
            photo = commons_photo(page["name"], page["text"], queries=[page["name"], page["name"] + " campus"])
        if not photo and CARD_ON:
            photo = make_card(art["text"], "fact", "Обзор вуза: " + page["name"])
        wiki_url = "https://en.wikipedia.org/wiki/" + urllib.parse.quote(page["name"].replace(" ", "_"))
        post = {"text": art["text"], "source": ("Википедия", wiki_url), "preview": False, "photo": photo, "kind": "article",
                "key": name, "tags": "#вузы #обзор #университеты", "bold_headings": True}
        if art["home"]:
            post["extra_links"] = [("Официальный сайт", art["home"])]
        return post
    return None


def apply_article(state, now):
    state["article_day"] = _local_day(now).isoformat()
    state["profiled"] = state.get("profiled", [])[-400:]


def article_due(state, now):
    return state.get("article_day") != _local_day(now).isoformat() and now.astimezone(TZ).hour >= ARTICLE_HOUR


# ---------- запуск ----------

def load_state():
    s = json.loads(STATE_FILE.read_text(encoding="utf-8")) if STATE_FILE.exists() else {}
    for k, v in {"posted": [], "extra_universities": [], "seen": [], "pool": [],
                 "since_fact": 0, "last_kind": None, "next_post_at": None,
                 "recent": [], "last_outlets": []}.items():
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
        if RANKING_ON and (RANKING_FORCE or ranking_due(state, now)):  # раз в день рейтинг вузов, ИИ для него не нужен
            rp = build_ranking_post(state, now)
            if rp:
                publish(rp)
                apply_ranking(state, rp, now)
                delay = next_delay(now)
                state["next_post_at"] = iso(now + delay)
                print(f"опубликован рейтинг ({rp['key']}), следующий пост через {delay.total_seconds() / 60:.0f} мин")
                return
        if ARTICLE_ON and (ARTICLE_FORCE or article_due(state, now)):  # утром статья про один вуз из топ-100
            ap = build_article_post(state, now)
            if ap:
                publish(ap)
                apply_article(state, now)
                state["next_post_at"] = iso(now + next_delay(now))
                print(f"опубликована статья о вузе ({ap['key']})")
                return
        if DEADLINES_ON and (DEADLINES_FORCE or deadlines_due(state, now)):  # раз в неделю календарь дедлайнов
            dp = build_deadlines_post(state, now)
            if dp:
                publish(dp)
                apply_deadlines(state, now)
                state["next_post_at"] = iso(now + next_delay(now))
                print("опубликован календарь дедлайнов")
                return
            apply_deadlines(state, now)  # ближайших дедлайнов нет: до следующей недели не проверяем
        if POLL_ON and (POLL_FORCE or poll_due(state, now)):  # раз в день опрос или викторина
            p = build_poll(state, now)
            if p:
                publish_poll(p)
                apply_poll(state, p, now)
                state["next_post_at"] = iso(now + next_delay(now))
                print("опубликован опрос")
                return
        if TIPS_ON and (TIPS_FORCE or tips_due(state, now)):  # раз в два дня шпаргалка
            tp = build_tips_post(state)
            if tp:
                publish(tp)
                apply_tips(state, tp, now)
                state["next_post_at"] = iso(now + next_delay(now))
                print(f"опубликована шпаргалка ({tp['key']})")
                return
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

#!/usr/bin/env python3
"""Ежедневный пост в Telegram-канал про вузы, поступление и науку.

Каждый день бот собирает кандидатов:
  fact       - вуз из списка, факт по статье Википедии (с фото, если лицензия свободная)
  admissions - новости про поступление и международное образование (RSS)
  science    - научные новости (RSS)
ИИ-модель (Claude или бесплатная, см. LLM_API_KEY) оценивает кандидатов по шкале 1-10 (насколько зацепит школьника, который
хочет учиться за рубежом), берёт лучшего и пишет по-русски пересказ ТОЛЬКО по
тексту источника (англоязычный источник переводится и пересказывается).
Любое число в посте, которого нет в источнике, считается выдумкой: пост
отклоняется. В конце всегда ссылка на оригинал.
Только стандартная библиотека Python.
"""
import datetime as dt
import json
import os
import random
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).parent
STATE_FILE = ROOT / "posted.json"
SOURCES = json.loads((ROOT / "sources.json").read_text(encoding="utf-8"))

# Бесплатный вариант: любой OpenAI-совместимый API. По умолчанию Groq.
# Пустые значения из GitHub (секрет не задан) считаются незаданными.
LLM_KEY = (os.environ.get("LLM_API_KEY") or "").strip()
LLM_URL = (os.environ.get("LLM_BASE_URL") or "https://api.groq.com/openai/v1").rstrip("/")
LLM_PAUSE = float(os.environ.get("LLM_PAUSE") or 20)
MODEL = os.environ.get("LLM_MODEL") or (
    "llama-3.3-70b-versatile" if LLM_KEY else os.environ.get("CLAUDE_MODEL", "claude-haiku-5-5"))
DRY = os.environ.get("DRY_RUN") == "1"
UA = "Mozilla/5.0 (compatible; unifacts-bot/1.0)"
MAX_CHARS = 7000 if LLM_KEY else 15000  # у бесплатных API мал лимит токенов в минуту
CONTENT_NS = "{http://purl.org/rss/1.0/modules/content/}encoded"
FACT_CANDIDATES = 3     # сколько вузов участвует в ежедневном отборе
TRIES = 3               # сколько лучших кандидатов пробуем превратить в пост
SAME_KIND_PENALTY = 1.5 # штраф, если тип поста такой же, как вчера

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
- 400-700 символов, живой русский язык, без воды, максимум 1 эмодзи в начале, без хэштегов.
- Первая строка - цепляющий заголовок с названием вуза, дальше 2-4 коротких абзаца.
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
- 400-800 символов, живой русский язык, максимум 1 эмодзи в начале, без хэштегов.
- Первая строка - заголовок, дальше 2-4 коротких абзаца. Выведи только текст поста, без вступлений.
- Если новость не будет интересна школьнику, который планирует учиться за рубежом (локальные скандалы, внутренняя политика вуза, узкие административные темы), или в тексте мало содержания, ответь одним словом: SKIP.

Текст новости:
{text}"""

RANK_PROMPT = """Ты редактор Telegram-канала для школьников 14-18 лет, которые хотят поступать в зарубежные вузы (олимпиады, SAT, летние школы, стипендии, наука).
Ниже кандидаты для сегодняшнего поста. Оцени каждого по шкале от 1 до 10: насколько он зацепит такую аудиторию, удивит или принесёт пользу.
Высоко: неожиданные факты, заметные научные открытия, реальные изменения правил поступления, виз, стипендий.
Низко: локальные скандалы, реклама, узкие административные новости, банальности.
Для типа fact оценивай, насколько вуз знаменит и интересен абитуриентам.
Ответь только JSON-массивом чисел в том же порядке, без пояснений. Пример для трёх кандидатов: [7, 3, 9]

{items}"""


# ---------- сеть ----------

def http_get(url, data=None, headers=None):
    req = urllib.request.Request(url, data=data, headers={"User-Agent": UA, **(headers or {})})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()


def _retry_after(e, attempt):
    try:
        return min(float(e.headers.get("retry-after")), 90)
    except (TypeError, ValueError):
        return 20 * (attempt + 1)


def ask_llm(prompt, max_tokens=800):
    """Один запрос к модели. Если задан LLM_API_KEY, идёт в OpenAI-совместимый API
    (Groq, Gemini и т.п., есть бесплатные тарифы), иначе в Claude по ANTHROPIC_API_KEY."""
    if LLM_KEY:
        time.sleep(LLM_PAUSE)  # бесплатные тарифы ограничивают токены в минуту
        url = f"{LLM_URL}/chat/completions"
        body = {"model": MODEL, "max_tokens": max_tokens, "temperature": 0.4,
                "messages": [{"role": "user", "content": prompt}]}
        headers = {"Authorization": f"Bearer {LLM_KEY}", "content-type": "application/json"}
    else:
        url = "https://api.anthropic.com/v1/messages"
        body = {"model": MODEL, "max_tokens": max_tokens,
                "messages": [{"role": "user", "content": prompt}]}
        headers = {"x-api-key": os.environ["ANTHROPIC_API_KEY"],
                   "anthropic-version": "2023-06-01", "content-type": "application/json"}
    data = json.dumps(body).encode()
    for attempt in range(5):
        try:
            raw = http_get(url, data, headers)
            break
        except urllib.error.HTTPError as e:
            detail = e.read().decode(errors="replace")
            if e.code in (429, 500, 502, 503) and attempt < 4:
                wait = _retry_after(e, attempt)
                print(f"  ИИ вернул {e.code}, жду {wait:.0f} с и повторяю")
                time.sleep(wait)
                continue
            sys.exit(f"ИИ-API: {e.code} {detail}")
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
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="photo"; filename="photo.jpg"\r\n'
            f'Content-Type: image/jpeg\r\n\r\n'.encode() + photo + b"\r\n")
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
    if photo:
        caption = text + "\n" + photo["credit"]
        try:
            if len(caption) <= 1024:  # лимит подписи к фото в Telegram
                tg("sendPhoto", {"chat_id": chat, "caption": caption}, photo["bytes"])
                return
            tg("sendPhoto", {"chat_id": chat, "caption": photo["credit"]}, photo["bytes"])
        except RuntimeError as e:
            print("фото не отправилось, шлю только текст:", e)
    tg("sendMessage", {
        "chat_id": chat, "text": text,
        "link_preview_options": json.dumps({"is_disabled": not post["preview"]}),
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


def make_post(prompt_tpl, source_text, **fields):
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
        return out
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


REFILL_BELOW = 10   # когда непоказанных вузов меньше, бот сам придумывает новые


REFILL_PROMPT = """Назови {n} разных университетов мира, известных абитуриентам (разные страны и континенты, не только США и Великобритания).
Для каждого дай точное название статьи в английской Википедии.
Не повторяй эти: {known}
Ответь только JSON-массивом строк, без пояснений."""


def all_universities(state):
    return SOURCES["universities"] + [u for u in state["extra_universities"] if u not in SOURCES["universities"]]


def refill_universities(state):
    """Пополняет список вузов: Claude предлагает названия, бот оставляет только те,
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


def fact_candidates(state):
    if len([u for u in all_universities(state) if u not in state["posted"]]) < REFILL_BELOW:
        refill_universities(state)
    left = [u for u in all_universities(state) if u not in state["posted"]]
    if not left:
        print("Список вузов закончился, пополнить не удалось")
    random.shuffle(left)
    out = []
    for title in left[:FACT_CANDIDATES]:
        try:
            page = wiki_page(title)
        except Exception as e:
            print("  Википедия недоступна:", e)
            continue
        if len(page["text"]) < 1500:
            continue
        out.append({"kind": "fact", "title": page["name"], "snippet": "факты по статье Википедии",
                    "page": page, "key": title})
    return out


# ---------- новости (RSS) ----------

def read_feed(feed):
    root = ET.fromstring(http_get(feed["url"]))
    items = []
    for it in root.iter("item"):
        try:
            date = parsedate_to_datetime(it.findtext("pubDate"))
        except Exception:
            date = dt.datetime.now(dt.timezone.utc)
        if date.tzinfo is None:
            date = date.replace(tzinfo=dt.timezone.utc)
        items.append({
            "outlet": feed["name"], "kind": feed["category"],
            "title": (it.findtext("title") or "").strip(),
            "link": (it.findtext("link") or "").strip(),
            "body": it.findtext(CONTENT_NS) or it.findtext("description") or "",
            "date": date,
        })
    return items


def news_candidates(state, category):
    cutoff = dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=7)
    out = []
    for feed in SOURCES["feeds"]:
        if category and feed["category"] != category:
            continue
        try:
            items = read_feed(feed)
        except Exception as e:
            print(f"  лента {feed['name']} не открылась: {e}")
            continue
        items = [i for i in items if i["link"] and i["link"] not in state["seen"] and i["date"] >= cutoff]
        items.sort(key=lambda i: i["date"], reverse=True)
        for i in items[:6]:
            i["snippet"] = html_to_text(i["body"])[:300]
            out.append(i)
    return out


# ---------- отбор лучшего ----------

def rank(cands, last_kind):
    lines = [f"{i}. [{c['kind']}] {c['title']}. {c['snippet']}" for i, c in enumerate(cands, 1)]
    scores = [5.0] * len(cands)
    try:
        out = ask_llm(RANK_PROMPT.format(items="\n".join(lines)), max_tokens=300)
        parsed = [float(s) for s in json.loads(re.search(r"\[[^\]]*\]", out).group(0))]
        if len(parsed) == len(cands):
            scores = parsed
        else:
            print("ранжирование: неверная длина ответа, все оценки равны")
    except Exception as e:
        print("ранжирование не удалось, все оценки равны:", e)
    for c, s in zip(cands, scores):
        c["ai_score"] = s
        c["score"] = s - (SAME_KIND_PENALTY if c["kind"] == last_kind else 0) + random.random() * 0.1
    cands.sort(key=lambda c: c["score"], reverse=True)
    for c in cands:
        print(f"  {c['score']:.1f} (ИИ {c['ai_score']:.0f}) [{c['kind']}] {c['title'][:70]}")


def build_post(c, state):
    if c["kind"] == "fact":
        page = c["page"]
        post = make_post(FACT_PROMPT, page["text"][:MAX_CHARS], name=page["name"])
        if not post:
            return None
        url = "https://en.wikipedia.org/wiki/" + urllib.parse.quote(page["name"].replace(" ", "_"))
        return {"text": f"{post}\n\nИсточник: Википедия, {url}", "preview": False,
                "photo": wiki_photo(page), "kind": "fact", "record": ("posted", c["key"])}
    state["seen"].append(c["link"])  # к этой новости больше не возвращаемся
    text = html_to_text(c["body"])
    if len(text) < 1500:  # в ленте только анонс: пробуем взять страницу целиком
        try:
            page = html_to_text(http_get(c["link"]).decode("utf-8", errors="replace"))
            if len(page) > len(text):
                text = page
        except Exception as e:
            print("  страница не открылась:", e)
    text = text[:MAX_CHARS]
    if len(text) < 400:
        print("  мало текста, пропускаю")
        return None
    post = make_post(NEWS_PROMPT, text, name=c["title"], outlet=c["outlet"])
    if not post:
        return None
    return {"text": f"{post}\n\nИсточник: {c['outlet']}, {c['link']}", "preview": True,
            "photo": None, "kind": c["kind"], "record": None}


# ---------- запуск ----------

def load_state():
    s = json.loads(STATE_FILE.read_text(encoding="utf-8")) if STATE_FILE.exists() else {}
    s.setdefault("posted", [])
    s.setdefault("seen", [])
    s.setdefault("last_kind", None)
    s.setdefault("extra_universities", [])
    return s


def save_state(state):
    if DRY:
        return
    state["seen"] = state["seen"][-500:]
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")


def main():
    state = load_state()
    kind = os.environ.get("KIND", "").strip()  # fact / admissions / science / пусто = все
    cands = []
    if kind in ("", "fact"):
        cands += fact_candidates(state)
    if kind != "fact":
        cands += news_candidates(state, kind or None)
    if not cands:
        sys.exit("Нет кандидатов: проверь ленты и список вузов")
    try:
        print(f"кандидатов: {len(cands)}")
        rank(cands, state["last_kind"])
        for c in cands[:TRIES]:
            print("пробую:", c["title"][:70])
            post = build_post(c, state)
            if post:
                publish(post)
                if post["record"]:
                    state[post["record"][0]].append(post["record"][1])
                state["last_kind"] = post["kind"]
                print("опубликовано:", post["kind"])
                return
        sys.exit("Ни один из лучших кандидатов не прошёл проверку, завтра попробуем снова")
    finally:
        save_state(state)


if __name__ == "__main__":
    main()

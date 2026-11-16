#!/usr/bin/env python3
"""
Lean Telegram bot-hosting panel (Railway friendly).

What it does (and nothing more):
  * users upload a .py / .zip  -> panel stores it and runs it as a child process
  * Start / Stop / Restart / Logs / Env vars / Update files / Delete
  * ONE supervisor thread: auto-restart with back-off, RAM limit per bot,
    container-wide memory guard, staggered boot (no thundering herd)
  * state lives in DATA_DIR (put a Railway Volume there!)

Required env vars : BOT_TOKEN, OWNER_ID
Optional env vars : DATA_DIR / RAILWAY_VOLUME_MOUNT_PATH, MAX_BOTS_PER_USER (3),
                    BOT_RAM_MB (300), MAX_CRASHES (8), BOOT_DELAY (15),
                    MEM_LIMIT_MB (auto-detected from cgroup)
"""
from __future__ import annotations

import hashlib
import html
import json
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import zipfile
from collections import deque
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import psutil
import telebot
from telebot import types
from telebot.apihelper import ApiTelegramException

# ═════════════════════════════════════════════════════════════════
#  CONFIG
# ═════════════════════════════════════════════════════════════════

def _int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, default))
    except (TypeError, ValueError):
        return default


TOKEN = (os.environ.get("BOT_TOKEN") or "").strip()
OWNER_ID = _int("OWNER_ID", 0)
MAX_BOTS_PER_USER = _int("MAX_BOTS_PER_USER", 3)
BOT_RAM_MB = _int("BOT_RAM_MB", 300)
MAX_CRASHES = _int("MAX_CRASHES", 8)
BOOT_DELAY = _int("BOOT_DELAY", 15)
MAX_UPLOAD_MB = 20
MAX_UNZIP_MB = 100
MAX_ENV_VARS = 30
TICK = 5            # supervisor interval (seconds)
LAUNCHES_PER_TICK = 2
MB = 1024 * 1024

BASE_DIR = Path(__file__).resolve().parent
_vol = os.environ.get("DATA_DIR") or os.environ.get("RAILWAY_VOLUME_MOUNT_PATH")
PERSISTENT = bool(_vol)
DATA_DIR = Path(_vol) if _vol else BASE_DIR / "storage"
BOTS_DIR = DATA_DIR / "bots"
DB_FILE = DATA_DIR / "db.json"
BOTS_DIR.mkdir(parents=True, exist_ok=True)

ENTRY_NAMES = ["main.py", "bot.py", "app.py", "index.py", "run.py", "start.py"]
SKIP_PARTS = {".deps", "__pycache__", ".tmp", "__MACOSX", ".git", "venv", ".venv"}
BLOCKED_ENV = {"PATH", "HOME", "PYTHONPATH", "PYTHONHOME", "LD_PRELOAD",
               "LD_LIBRARY_PATH", "TMPDIR", "PYTHONSTARTUP"}

# import name -> pip name (only the ones that differ)
PIP_ALIAS = {
    "telegram": "python-telegram-bot", "PIL": "Pillow", "cv2": "opencv-python-headless",
    "bs4": "beautifulsoup4", "yaml": "PyYAML", "dotenv": "python-dotenv",
    "Crypto": "pycryptodome", "sklearn": "scikit-learn", "dateutil": "python-dateutil",
    "jwt": "PyJWT", "telebot": "pyTelegramBotAPI", "nacl": "PyNaCl",
    "serial": "pyserial", "psycopg2": "psycopg2-binary", "discord": "discord.py",
}

try:  # optional external scanner (security_scanner_free.py next to this file)
    sys.path.insert(0, str(BASE_DIR))
    from security_scanner_free import scan_file as _scan_file  # type: ignore
except Exception:  # pragma: no cover
    _scan_file = None

bot = telebot.TeleBot(TOKEN or "123456:TEST", parse_mode="HTML",
                      threaded=True, num_threads=8)

# ═════════════════════════════════════════════════════════════════
#  DATABASE  (one small JSON file, atomic writes)
# ═════════════════════════════════════════════════════════════════

_lock = threading.RLock()
DB: Dict[str, Any] = {"users": {}, "bots": {}, "banned": []}


def db_load() -> None:
    global DB
    try:
        d = json.loads(DB_FILE.read_text("utf-8"))
    except FileNotFoundError:
        return
    except Exception:
        try:
            shutil.copy(DB_FILE, DB_FILE.with_suffix(".corrupt"))
        except Exception:
            pass
        print("[db] db.json unreadable — starting fresh (copy kept as db.corrupt)")
        return
    d.setdefault("users", {})
    d.setdefault("bots", {})
    d.setdefault("banned", [])
    DB = d


def db_save() -> None:
    with _lock:
        tmp = DB_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(DB, ensure_ascii=False), "utf-8")
        os.replace(tmp, DB_FILE)


# ═════════════════════════════════════════════════════════════════
#  RUNTIME STATE
# ═════════════════════════════════════════════════════════════════

class St:
    """In-memory runtime state of one hosted bot."""
    def __init__(self) -> None:
        self.proc: Optional[subprocess.Popen] = None
        self.log: deque = deque(maxlen=300)
        self.fails = 0
        self.autofix = 0
        self.next_try = 0.0
        self.started = 0.0
        self.launching = False
        self.exit_seen = True


ST: Dict[str, St] = {}


def st(bid: str) -> St:
    with _lock:
        return ST.setdefault(bid, St())


def alive(s: St) -> bool:
    return s.proc is not None and s.proc.poll() is None


# ═════════════════════════════════════════════════════════════════
#  SMALL HELPERS
# ═════════════════════════════════════════════════════════════════

def esc(x: Any) -> str:
    return html.escape(str(x), quote=False)


def is_admin(uid: int) -> bool:
    return bool(OWNER_ID) and uid == OWNER_ID


def blocked(uid: int) -> bool:
    return uid in DB["banned"]


def user_bots(uid: int) -> List[Dict[str, Any]]:
    return [b for b in DB["bots"].values() if b["owner"] == uid]


def can_access(uid: int, b: Optional[Dict[str, Any]]) -> bool:
    return bool(b) and (b["owner"] == uid or is_admin(uid))


def notify(uid: int, text: str) -> None:
    try:
        bot.send_message(uid, text)
    except Exception:
        pass


def fmt_dur(sec: float) -> str:
    sec = int(sec)
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    m, _ = divmod(r, 60)
    if d:
        return f"{d}d {h}h"
    if h:
        return f"{h}h {m}m"
    return f"{m}m"


def tree_rss(pid: int) -> int:
    try:
        p = psutil.Process(pid)
        total = p.memory_info().rss
        for c in p.children(recursive=True):
            try:
                total += c.memory_info().rss
            except psutil.Error:
                pass
        return total
    except psutil.Error:
        return 0


def mem_limit() -> int:
    env_mb = _int("MEM_LIMIT_MB", 0)
    if env_mb > 0:
        return env_mb * MB
    total = psutil.virtual_memory().total
    for p in ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"):
        try:
            v = Path(p).read_text().strip()
            if v != "max" and int(v) < total:
                return int(v)
        except Exception:
            pass
    return total


def mem_usage() -> Tuple[int, int]:
    """(panel + all child bots RSS, container limit)"""
    used = psutil.Process().memory_info().rss
    for s in list(ST.values()):
        if alive(s):
            used += tree_rss(s.proc.pid)  # type: ignore[union-attr]
    return used, mem_limit()


def kill_tree(proc: subprocess.Popen) -> None:
    for sig, wait in ((signal.SIGTERM, 5), (signal.SIGKILL, 3)):
        try:
            os.killpg(proc.pid, sig)          # child runs in its own session
        except ProcessLookupError:
            pass
        except Exception:
            try:
                proc.send_signal(sig)
            except Exception:
                pass
        try:
            proc.wait(timeout=wait)
            return
        except subprocess.TimeoutExpired:
            continue


# ═════════════════════════════════════════════════════════════════
#  RUNNING CHILD BOTS
# ═════════════════════════════════════════════════════════════════

_pip_sem = threading.Semaphore(1)        # never run two pip installs at once


def _clean_env(bdir: Path) -> Dict[str, str]:
    """Minimal env — the panel's own secrets are NOT passed on."""
    (bdir / ".tmp").mkdir(exist_ok=True)
    return {
        "PATH": os.environ.get("PATH", "/usr/local/bin:/usr/bin:/bin"),
        "HOME": str(bdir),
        "TMPDIR": str(bdir / ".tmp"),
        "PYTHONPATH": str(bdir / ".deps"),
        "PYTHONUNBUFFERED": "1",
        "LANG": "C.UTF-8",
    }


def pip_install(bdir: Path, args: List[str], s: St, timeout: int = 300) -> bool:
    deps = bdir / ".deps"
    deps.mkdir(exist_ok=True)
    cmd = [sys.executable, "-m", "pip", "install", "--target", str(deps),
           "--no-input", "--disable-pip-version-check", "--quiet", *args]
    env = _clean_env(bdir)
    env["PIP_ROOT_USER_ACTION"] = "ignore"
    with _pip_sem:
        s.log.append("[panel] pip install " + " ".join(args)[:200])
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
                               env=env, cwd=str(bdir))
        except subprocess.TimeoutExpired:
            s.log.append("[panel] pip timed out")
            return False
        except Exception as e:
            s.log.append(f"[panel] pip error: {e}")
            return False
    for ln in (r.stderr or r.stdout or "").splitlines()[-6:]:
        s.log.append(ln[:300])
    return r.returncode == 0


def install_requirements(bdir: Path, s: St) -> None:
    """Only when requirements.txt exists AND changed since the last install."""
    req = bdir / "requirements.txt"
    if not req.exists():
        return
    h = hashlib.md5(req.read_bytes()).hexdigest()
    marker = bdir / ".deps" / ".req_hash"
    try:
        if marker.exists() and marker.read_text() == h:
            return
    except Exception:
        pass
    if pip_install(bdir, ["-r", str(req)], s):
        marker.parent.mkdir(exist_ok=True)
        marker.write_text(h)


def _reader(proc: subprocess.Popen, s: St) -> None:
    try:
        for raw in iter(proc.stdout.readline, b""):  # type: ignore[union-attr]
            s.log.append(raw.decode("utf-8", "replace").rstrip()[:500])
    except Exception:
        pass


def register_failure(b: Dict[str, Any], s: St, reason: str) -> None:
    s.fails += 1
    b["restarts"] = b.get("restarts", 0) + 1
    b["last_error"] = reason[-800:]
    if s.fails >= MAX_CRASHES:
        b["desired"] = False
        b["gave_up"] = True
        notify(b["owner"],
               f"⚠️ <b>{esc(b['name'])}</b> kept crashing and was stopped "
               f"after {s.fails} tries.\n<pre>{esc(reason[-500:])}</pre>")
    else:
        s.next_try = time.time() + min(300, 5 * 2 ** (s.fails - 1))   # 5,10,20,…300s
    db_save()


def launch(bid: str) -> None:
    """Runs in its own thread; always clears the 'launching' flag."""
    s = st(bid)
    b = DB["bots"].get(bid)
    try:
        if not b or not b.get("desired") or alive(s):
            return
        bdir = BOTS_DIR / bid
        entry = b.get("entry")
        if not entry or not (bdir / entry).is_file():
            register_failure(b, s, "entry file missing — upload the bot again")
            return
        used, limit = mem_usage()
        if used > 0.85 * limit:
            s.log.append("[panel] server memory is high — will retry in 60s")
            s.next_try = time.time() + 60
            return
        install_requirements(bdir, s)
        if not b.get("desired"):            # user pressed Stop during pip
            return
        env = _clean_env(bdir)
        env.update(b.get("env") or {})
        s.log.append(f"[panel] starting {entry}")
        proc = subprocess.Popen(
            [sys.executable, "-u", entry], cwd=str(bdir), env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, start_new_session=True)
        s.proc, s.started, s.exit_seen = proc, time.time(), False
        threading.Thread(target=_reader, args=(proc, s), daemon=True).start()
        b["status_note"] = ""
    except Exception as e:
        s.log.append(f"[panel] launch error: {e}")
        if b:
            register_failure(b, s, f"launch error: {e}")
    finally:
        s.launching = False


def _autofix(bid: str, pkg: str) -> None:
    s = st(bid)
    b = DB["bots"].get(bid)
    try:
        if pip_install(BOTS_DIR / bid, [pkg], s):
            s.next_try = 0
        elif b:
            register_failure(b, s, f"could not install missing module: {pkg}")
    finally:
        s.launching = False


def start_bot(b: Dict[str, Any]) -> None:
    s = st(b["id"])
    with _lock:
        b["desired"], b["gave_up"], b["last_error"] = True, False, ""
        s.fails, s.autofix, s.next_try = 0, 0, 0.0
        busy = alive(s) or s.launching
        if not busy:
            s.launching, s.exit_seen = True, True
    db_save()
    if not busy:
        threading.Thread(target=launch, args=(b["id"],), daemon=True).start()


def stop_bot(b: Dict[str, Any]) -> None:
    s = st(b["id"])
    b["desired"] = False
    db_save()
    if alive(s):
        kill_tree(s.proc)  # type: ignore[arg-type]
        s.exit_seen = True
        s.log.append("[panel] stopped")


def delete_bot(b: Dict[str, Any]) -> None:
    stop_bot(b)
    shutil.rmtree(BOTS_DIR / b["id"], ignore_errors=True)
    with _lock:
        DB["bots"].pop(b["id"], None)
        ST.pop(b["id"], None)
    db_save()


# ═════════════════════════════════════════════════════════════════
#  SUPERVISOR  (the single thread that keeps everything alive)
# ═════════════════════════════════════════════════════════════════

def tick() -> None:
    now = time.time()
    launches = 0
    running: List[Tuple[int, str]] = []

    for bid, b in list(DB["bots"].items()):
        s = st(bid)

        # 1) process just ended → classify
        if s.proc is not None and not alive(s) and not s.exit_seen:
            s.exit_seen = True
            rc = s.proc.returncode
            tail = "\n".join(list(s.log)[-12:])
            s.log.append(f"[panel] exited rc={rc}")
            if b.get("desired"):
                if rc == 0:
                    b["desired"] = False
                    b["last_error"] = "Bot finished normally (exit code 0)."
                    db_save()
                else:
                    m = re.search(r"No module named '([\w.]+)'", tail)
                    if m and s.autofix < 3:
                        s.autofix += 1
                        top = m.group(1).split(".")[0]
                        s.launching = True
                        threading.Thread(target=_autofix,
                                         args=(bid, PIP_ALIAS.get(top, top)),
                                         daemon=True).start()
                        continue
                    if now - s.started > 120:
                        s.fails = 0
                    register_failure(b, s, f"exit code {rc}\n{tail}")
            continue

        # 2) alive → RAM check, healthy-run reset
        if alive(s):
            rss = tree_rss(s.proc.pid)  # type: ignore[union-attr]
            running.append((rss, bid))
            if s.fails and now - s.started > 120:
                s.fails, s.autofix = 0, 0
            if rss > BOT_RAM_MB * MB and not is_admin(b["owner"]):
                s.log.append(f"[panel] RAM limit {BOT_RAM_MB} MB exceeded ({rss // MB} MB) — killed")
                kill_tree(s.proc)  # type: ignore[arg-type]
                s.exit_seen = True
                register_failure(b, s, f"RAM limit {BOT_RAM_MB} MB exceeded (used {rss // MB} MB)")
            continue

        # 3) should be running but is not → (re)launch, staggered
        if (b.get("desired") and not s.launching and s.exit_seen
                and now >= s.next_try and launches < LAUNCHES_PER_TICK):
            s.launching = True
            launches += 1
            threading.Thread(target=launch, args=(bid,), daemon=True).start()

    # 4) container-wide guard: stop the biggest bot before the OOM killer
    #    takes the whole panel (and every bot) down.
    if running:
        used, limit = mem_usage()
        if used > 0.92 * limit:
            rss, bid = max(running)
            b = DB["bots"].get(bid)
            s = st(bid)
            if b:
                kill_tree(s.proc)  # type: ignore[arg-type]
                s.exit_seen = True
                b["desired"], b["gave_up"] = False, True
                b["last_error"] = f"Stopped by memory guard (server RAM almost full, bot used {rss // MB} MB)."
                db_save()
                notify(b["owner"], f"⚠️ <b>{esc(b['name'])}</b> was stopped: server memory was almost full.")


def watchdog() -> None:
    time.sleep(BOOT_DELAY)      # let the old Railway instance die first
    print("[panel] supervisor running", flush=True)
    while True:
        try:
            tick()
        except Exception:
            traceback.print_exc()
        time.sleep(TICK)


# ═════════════════════════════════════════════════════════════════
#  UPLOAD HANDLING
# ═════════════════════════════════════════════════════════════════

def safe_extract(zpath: Path, dest: Path) -> None:
    with zipfile.ZipFile(zpath) as z:
        infos = z.infolist()
        if len(infos) > 2000:
            raise ValueError("zip has too many files")
        total = 0
        for i in infos:
            parts = Path(i.filename).parts
            if i.filename.startswith(("/", "\\")) or ".." in parts:
                raise ValueError("zip contains unsafe paths")
            total += i.file_size
            if total > MAX_UNZIP_MB * MB:
                raise ValueError(f"zip is larger than {MAX_UNZIP_MB} MB unpacked")
        z.extractall(dest)
    # flatten a single wrapper folder (MyBot/bot.py -> bot.py)
    items = [p for p in dest.iterdir() if p.name not in SKIP_PARTS]
    if len(items) == 1 and items[0].is_dir():
        inner = items[0]
        for p in list(inner.iterdir()):
            shutil.move(str(p), str(dest / p.name))
        shutil.rmtree(inner, ignore_errors=True)


def find_entry(bdir: Path) -> Optional[str]:
    files = [p for p in bdir.rglob("*.py")
             if not any(part in SKIP_PARTS for part in p.relative_to(bdir).parts)]
    if not files:
        return None
    rel = {str(p.relative_to(bdir)): p for p in files}
    for n in ENTRY_NAMES:
        if n in rel:
            return n
    files.sort(key=lambda p: (len(p.relative_to(bdir).parts), p.name))
    for p in files:                       # prefer a file that actually starts a bot
        try:
            t = p.read_text("utf-8", "ignore")
        except Exception:
            continue
        if re.search(r"polling\(|run_polling|__main__|app\.run\(", t):
            return str(p.relative_to(bdir))
    return str(files[0].relative_to(bdir))


def reg_user(u: types.User) -> None:
    k = str(u.id)
    if k not in DB["users"]:
        DB["users"][k] = {"name": (u.first_name or "")[:40], "username": u.username or "",
                          "joined": int(time.time())}
        db_save()


AWAIT: Dict[int, Tuple[str, str]] = {}      # uid -> ("env"|"update", bot_id)


def process_upload(m: types.Message, target: Optional[Dict[str, Any]]) -> None:
    uid = m.from_user.id
    doc = m.document
    fname = re.sub(r"[^\w.\-]", "_", os.path.basename(doc.file_name or "bot.py"))[:80]
    ext = fname.lower().rsplit(".", 1)[-1]
    wait = bot.reply_to(m, "⏳ Checking and saving…")
    tmpd = Path(tempfile.mkdtemp(prefix="up_"))
    new_dir: Optional[Path] = None
    try:
        src = tmpd / fname
        src.write_bytes(bot.download_file(bot.get_file(doc.file_id).file_path))

        if _scan_file:
            try:
                res = _scan_file(str(src))
            except Exception:
                res = {"recommendation": "APPROVE"}
            rec = res.get("recommendation")
            if rec == "REJECT":
                threats = "\n".join("• " + esc(t)[:120] for t in res.get("all_threats", [])[:5])
                bot.edit_message_text(f"🚫 <b>Rejected</b> — file looks malicious.\n{threats}",
                                      wait.chat.id, wait.message_id)
                if OWNER_ID:
                    notify(OWNER_ID, f"🚫 Rejected upload from <code>{uid}</code>: {esc(fname)}")
                return
            if rec == "MANUAL_REVIEW" and OWNER_ID and not is_admin(uid):
                notify(OWNER_ID, f"🔍 Suspicious upload from <code>{uid}</code>: {esc(fname)} "
                                 f"(risk {res.get('risk_score')}). It was allowed.")

        was_running = bool(target and target.get("desired"))
        if target:
            bid = target["id"]
            stop_bot(target)
            bdir = BOTS_DIR / bid
            for p in list(bdir.iterdir()) if bdir.exists() else []:
                if p.name in (".deps", ".tmp"):
                    continue
                shutil.rmtree(p, ignore_errors=True) if p.is_dir() else p.unlink(missing_ok=True)
            bdir.mkdir(exist_ok=True)
        else:
            bid = secrets.token_hex(4)
            bdir = new_dir = BOTS_DIR / bid
            bdir.mkdir(parents=True)

        if ext == "py":
            shutil.copy(src, bdir / fname)
        else:
            safe_extract(src, bdir)

        entry = find_entry(bdir)
        if not entry:
            raise ValueError("no .py file found in the upload")

        with _lock:
            if target:
                target["entry"] = entry
                b = target
            else:
                b = {"id": bid, "owner": uid, "name": Path(fname).stem[:30] or "bot",
                     "entry": entry, "env": {}, "desired": False, "gave_up": False,
                     "restarts": 0, "last_error": "", "created": int(time.time())}
                DB["bots"][bid] = b
            new_dir = None
        db_save()
        if was_running:
            start_bot(b)
        text, kb = bot_view(b)
        bot.edit_message_text("✅ Saved.\n\n" + text, wait.chat.id, wait.message_id, reply_markup=kb)
    except ValueError as e:
        bot.edit_message_text(f"❌ {esc(e)}", wait.chat.id, wait.message_id)
    except Exception as e:
        traceback.print_exc()
        try:
            bot.edit_message_text(f"❌ Upload failed: {esc(e)}", wait.chat.id, wait.message_id)
        except Exception:
            pass
    finally:
        if new_dir is not None:
            shutil.rmtree(new_dir, ignore_errors=True)
        shutil.rmtree(tmpd, ignore_errors=True)


# ═════════════════════════════════════════════════════════════════
#  TELEGRAM UI
# ═════════════════════════════════════════════════════════════════

def B(text: str, data: str) -> types.InlineKeyboardButton:
    return types.InlineKeyboardButton(text, callback_data=data)


def show(chat_id: int, msg_id: Optional[int], text: str,
         kb: Optional[types.InlineKeyboardMarkup] = None) -> None:
    if msg_id:
        try:
            bot.edit_message_text(text, chat_id, msg_id, reply_markup=kb,
                                  disable_web_page_preview=True)
            return
        except ApiTelegramException as e:
            if "message is not modified" in str(e):
                return
        except Exception:
            pass
    bot.send_message(chat_id, text, reply_markup=kb, disable_web_page_preview=True)


def main_kb(uid: int) -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(B("🤖 My bots", "ls"), B("📤 Upload bot", "up"))
    if is_admin(uid):
        kb.add(B("🛠 Admin", "adm"))
    return kb


WELCOME = ("👋 <b>Bot Hosting</b>\n\nSend me a <code>.py</code> or <code>.zip</code> file "
           "and I'll keep your bot running 24/7.\n\nUse the buttons below.")


def status_of(b: Dict[str, Any]) -> str:
    s = st(b["id"])
    if alive(s):
        return f"🟢 Running · {fmt_dur(time.time() - s.started)}"
    if b.get("desired"):
        return "🟡 Starting…" if s.fails == 0 else f"🟡 Restarting (try {s.fails}/{MAX_CRASHES})"
    if b.get("gave_up"):
        return "🔴 Crashed — auto-restart gave up"
    return "⚪ Stopped"


def bot_view(b: Dict[str, Any]) -> Tuple[str, types.InlineKeyboardMarkup]:
    s = st(b["id"])
    ram = f"{tree_rss(s.proc.pid) // MB} MB" if alive(s) else "—"  # type: ignore[union-attr]
    text = (f"🤖 <b>{esc(b['name'])}</b>\n"
            f"Status: {status_of(b)}\n"
            f"File: <code>{esc(b.get('entry'))}</code>\n"
            f"RAM: {ram} / {BOT_RAM_MB} MB · Restarts: {b.get('restarts', 0)}\n"
            f"Env vars: {len(b.get('env') or {})}")
    if b.get("last_error") and not alive(s):
        text += f"\n\n<b>Last error</b>\n<pre>{esc(b['last_error'][-500:])}</pre>"
    i = b["id"]
    kb = types.InlineKeyboardMarkup(row_width=2)
    if alive(s) or b.get("desired"):
        kb.add(B("⏹ Stop", f"x:{i}"), B("🔄 Restart", f"r:{i}"))
    else:
        kb.add(B("▶️ Start", f"s:{i}"))
    kb.add(B("📜 Logs", f"l:{i}"), B("⚙️ Env vars", f"e:{i}"))
    kb.add(B("📤 Update files", f"u:{i}"), B("🗑 Delete", f"d:{i}"))
    kb.add(B("🔃 Refresh", f"b:{i}"), B("⬅️ Back", "ls"))
    return text, kb


def list_view(uid: int) -> Tuple[str, types.InlineKeyboardMarkup]:
    bots = user_bots(uid)
    kb = types.InlineKeyboardMarkup(row_width=1)
    for b in bots:
        kb.add(B(f"{status_of(b).split(' ')[0]} {b['name']}", f"b:{b['id']}"))
    kb.add(B("📤 Upload bot", "up"), B("⬅️ Menu", "home"))
    limit = "∞" if is_admin(uid) else MAX_BOTS_PER_USER
    return f"🤖 <b>Your bots</b> ({len(bots)}/{limit})" + ("" if bots else "\n\nNothing here yet."), kb


def admin_text() -> str:
    used, limit = mem_usage()
    running = sum(1 for s in ST.values() if alive(s))
    kids = used - psutil.Process().memory_info().rss
    return (f"🛠 <b>Admin</b>\n"
            f"Users: {len(DB['users'])} · Bots: {len(DB['bots'])} · Running: {running}\n"
            f"Memory: {used // MB} / {limit // MB} MB (bots: {max(kids, 0) // MB} MB)\n"
            f"Storage: {'✅ persistent' if PERSISTENT else '⚠️ NOT persistent — add a Railway Volume!'}\n\n"
            f"/ban &lt;id&gt; · /unban &lt;id&gt;")


# ── commands ─────────────────────────────────────────────────────

@bot.message_handler(commands=["start", "menu"])
def h_start(m: types.Message) -> None:
    uid = m.from_user.id
    if blocked(uid):
        return
    AWAIT.pop(uid, None)
    reg_user(m.from_user)
    bot.send_message(m.chat.id, WELCOME, reply_markup=main_kb(uid))


@bot.message_handler(commands=["ban", "unban"])
def h_ban(m: types.Message) -> None:
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) != 2 or not parts[1].lstrip("-").isdigit():
        bot.reply_to(m, "Usage: /ban &lt;user_id&gt;  or  /unban &lt;user_id&gt;")
        return
    target = int(parts[1])
    if parts[0].startswith("/ban"):
        if target == OWNER_ID:
            return
        if target not in DB["banned"]:
            DB["banned"].append(target)
        for b in user_bots(target):
            stop_bot(b)
        bot.reply_to(m, f"🚫 Banned {target} and stopped their bots.")
    else:
        if target in DB["banned"]:
            DB["banned"].remove(target)
        bot.reply_to(m, f"✅ Unbanned {target}.")
    db_save()


# ── file upload ──────────────────────────────────────────────────

@bot.message_handler(content_types=["document"])
def h_doc(m: types.Message) -> None:
    uid = m.from_user.id
    if blocked(uid):
        return
    reg_user(m.from_user)
    action = AWAIT.pop(uid, None)
    target = None
    if action and action[0] == "update":
        t = DB["bots"].get(action[1])
        target = t if can_access(uid, t) else None

    doc = m.document
    name = (doc.file_name or "").lower()
    if not name.endswith((".py", ".zip")):
        bot.reply_to(m, "❌ Only <code>.py</code> or <code>.zip</code> files are supported.")
        return
    if doc.file_size and doc.file_size > MAX_UPLOAD_MB * MB:
        bot.reply_to(m, f"❌ File is bigger than {MAX_UPLOAD_MB} MB.")
        return
    if not target and not is_admin(uid) and len(user_bots(uid)) >= MAX_BOTS_PER_USER:
        bot.reply_to(m, f"❌ You already have {MAX_BOTS_PER_USER} bots (the limit). "
                        f"Delete one first, or update an existing bot.")
        return
    process_upload(m, target)


# ── env var input ────────────────────────────────────────────────

@bot.message_handler(content_types=["text"],
                     func=lambda m: AWAIT.get(m.from_user.id, ("",))[0] == "env")
def h_env_text(m: types.Message) -> None:
    uid = m.from_user.id
    _, bid = AWAIT.pop(uid)
    b = DB["bots"].get(bid)
    try:
        bot.delete_message(m.chat.id, m.message_id)      # don't leave tokens in chat
    except Exception:
        pass
    if not can_access(uid, b):
        return
    env = b.setdefault("env", {})
    changed, errors = [], []
    for line in (m.text or "").splitlines():
        line = line.strip()
        if not line or "=" not in line:
            continue
        k, v = line.split("=", 1)
        k, v = k.strip(), v.strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", k) or k in BLOCKED_ENV:
            errors.append(k[:30])
            continue
        if not v:
            env.pop(k, None)
        elif len(env) >= MAX_ENV_VARS and k not in env:
            errors.append(k)
            continue
        else:
            env[k] = v[:2000]
        changed.append(k)
    db_save()
    msg = "✅ Saved: " + (", ".join(f"<code>{esc(k)}</code>" for k in changed) or "nothing")
    if errors:
        msg += "\n⚠️ Skipped: " + ", ".join(esc(e) for e in errors)
    msg += "\nRestart the bot to apply."
    kb = types.InlineKeyboardMarkup()
    kb.add(B("⬅️ Back to bot", f"b:{bid}"))
    bot.send_message(m.chat.id, msg, reply_markup=kb)


# ── buttons ──────────────────────────────────────────────────────

@bot.callback_query_handler(func=lambda c: True)
def h_cb(c: types.CallbackQuery) -> None:
    uid, chat, mid = c.from_user.id, c.message.chat.id, c.message.message_id
    try:
        bot.answer_callback_query(c.id)
    except Exception:
        pass
    if blocked(uid):
        return
    act, _, arg = (c.data or "").partition(":")

    if act == "home":
        AWAIT.pop(uid, None)
        return show(chat, mid, WELCOME, main_kb(uid))
    if act == "up":
        kb = types.InlineKeyboardMarkup()
        kb.add(B("⬅️ Menu", "home"))
        return show(chat, mid, "📤 Send your bot as a <code>.py</code> or <code>.zip</code> file "
                               "(max 20 MB).\nIf it needs a token or API key, add it later "
                               "under <b>Env vars</b>.", kb)
    if act == "ls":
        AWAIT.pop(uid, None)
        t, kb = list_view(uid)
        return show(chat, mid, t, kb)

    if act == "adm" and is_admin(uid):
        kb = types.InlineKeyboardMarkup()
        kb.add(B("📋 All bots", "admb"), B("🔃 Refresh", "adm"))
        kb.add(B("⬅️ Menu", "home"))
        return show(chat, mid, admin_text(), kb)
    if act == "admb" and is_admin(uid):
        kb = types.InlineKeyboardMarkup(row_width=1)
        for b in list(DB["bots"].values())[:40]:
            kb.add(B(f"{status_of(b).split(' ')[0]} {b['name']} · {b['owner']}", f"b:{b['id']}"))
        kb.add(B("⬅️ Back", "adm"))
        return show(chat, mid, f"📋 <b>All bots</b> ({len(DB['bots'])})", kb)

    # everything below works on one bot
    b = DB["bots"].get(arg)
    if not can_access(uid, b):
        return show(chat, mid, "Bot not found.", main_kb(uid))
    assert b is not None
    s = st(b["id"])

    if act == "b":
        AWAIT.pop(uid, None)
        t, kb = bot_view(b)
        return show(chat, mid, t, kb)
    if act == "s":
        start_bot(b)
        time.sleep(1.5)
    elif act == "x":
        stop_bot(b)
    elif act == "r":
        stop_bot(b)
        start_bot(b)
        time.sleep(1.5)
    elif act == "l":
        lines = list(s.log)[-40:]
        body = "\n".join(lines)[-3000:] or "(no output yet)"
        kb = types.InlineKeyboardMarkup()
        kb.add(B("🔃 Refresh", f"l:{b['id']}"), B("⬅️ Back", f"b:{b['id']}"))
        return show(chat, mid, f"📜 <b>{esc(b['name'])}</b>\n<pre>{esc(body)}</pre>", kb)
    elif act == "e":
        AWAIT[uid] = ("env", b["id"])
        keys = ", ".join(f"<code>{esc(k)}</code>" for k in (b.get("env") or {})) or "none"
        kb = types.InlineKeyboardMarkup()
        kb.add(B("⬅️ Cancel", f"b:{b['id']}"))
        return show(chat, mid, f"⚙️ <b>Env vars</b>\nCurrent: {keys}\n\n"
                               f"Send one or more lines like:\n<code>BOT_TOKEN=123:ABC</code>\n"
                               f"<code>API_KEY=xyz</code>\nUse <code>KEY=</code> (empty) to remove. "
                               f"Your message is deleted after saving.", kb)
    elif act == "u":
        AWAIT[uid] = ("update", b["id"])
        kb = types.InlineKeyboardMarkup()
        kb.add(B("⬅️ Cancel", f"b:{b['id']}"))
        return show(chat, mid, "📤 Send the new <code>.py</code> / <code>.zip</code>. "
                               "It replaces the old files (env vars are kept).", kb)
    elif act == "d":
        kb = types.InlineKeyboardMarkup()
        kb.add(B("✅ Yes, delete", f"dd:{b['id']}"), B("Cancel", f"b:{b['id']}"))
        return show(chat, mid, f"🗑 Delete <b>{esc(b['name'])}</b> permanently?", kb)
    elif act == "dd":
        delete_bot(b)
        t, kb = list_view(uid)
        return show(chat, mid, "🗑 Deleted.\n\n" + t, kb)

    t, kb = bot_view(b)
    show(chat, mid, t, kb)


# ═════════════════════════════════════════════════════════════════
#  MAIN
# ═════════════════════════════════════════════════════════════════

def _shutdown(*_: Any) -> None:
    """Railway redeploy/stop: stop children cleanly. 'desired' flags stay set,
    so every bot that was running comes back by itself on the next boot."""
    print("[panel] shutting down…", flush=True)
    for s in list(ST.values()):
        if alive(s):
            try:
                os.killpg(s.proc.pid, signal.SIGTERM)  # type: ignore[union-attr]
            except Exception:
                pass
    time.sleep(2)
    for s in list(ST.values()):
        if alive(s):
            try:
                os.killpg(s.proc.pid, signal.SIGKILL)  # type: ignore[union-attr]
            except Exception:
                pass
    try:
        db_save()
    except Exception:
        pass
    os._exit(0)


def main() -> int:
    if not TOKEN:
        sys.exit("BOT_TOKEN is not set. Add it in Railway → Variables, then redeploy.")
    db_load()
    print(f"[panel] data dir: {DATA_DIR}  persistent={PERSISTENT}", flush=True)
    if not OWNER_ID:
        print("[panel] WARNING: OWNER_ID not set — admin panel disabled", flush=True)
    signal.signal(signal.SIGTERM, _shutdown)
    signal.signal(signal.SIGINT, _shutdown)

    try:
        bot.remove_webhook()
    except Exception:
        pass
    try:
        bot.set_my_commands([types.BotCommand("start", "open menu")])
    except Exception:
        pass

    threading.Thread(target=watchdog, daemon=True, name="supervisor").start()

    if OWNER_ID:
        to_restore = sum(1 for b in DB["bots"].values() if b.get("desired"))
        warn = "" if PERSISTENT else ("\n⚠️ <b>No Volume attached</b> — all bots/files are lost on "
                                       "every redeploy. Add a Railway Volume (mount path /data).")
        notify(OWNER_ID, f"✅ Panel online. Restoring {to_restore} bot(s) in {BOOT_DELAY}s.{warn}")

    while True:
        try:
            bot.infinity_polling(skip_pending=True, timeout=30, long_polling_timeout=25,
                                 allowed_updates=["message", "callback_query"])
        except Exception as e:
            print(f"[panel] polling error: {e}", flush=True)
            time.sleep(5)


if __name__ == "__main__":
    sys.exit(main())

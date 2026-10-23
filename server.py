#!/usr/bin/env python3
"""سيرفر بيت الهمس (أونلاين) - بايثون عادي من غير مكتبات إضافية.

التشغيل:   python server.py            (البورت 16613)
           python server.py 9000       (بورت تاني)

الغرف: كل غرفة ليها رقم ID من 5 أرقام، وفيها لحد 8 لاعبين.
القواعد:
  - لو لاعب مات: بيستنى صحابه.
  - لو كل اللاعبين ماتوا: الفريق كله بيعيد الشقة من الأول (wipe).
  - لو حد خرج بالمفتاح: الكل بيروح للشقة اللي بعدها (حتى اللي ماتوا).
"""
import asyncio
import json
import random
import sys
import time

MAX_PLAYERS = 8
MAX_LEVEL = 10
PORT = 16613
MAX_ROOMS = 500
IDLE_TIMEOUT = 120          # ثواني من غير أي رسالة = فصل
RATE = 150                  # أقصى عدد رسايل في الثانية للاعب الواحد

ROOMS = {}


def log(*a):
    try:
        print(*a, flush=True)
    except Exception:
        pass


def clean_name(n):
    n = ''.join(c for c in str(n or '') if c.isprintable()).strip()[:14]
    return n or "لاعب"


def num(v, lo=-1e6, hi=1e6, default=0.0):
    try:
        v = float(v)
    except (TypeError, ValueError):
        return default
    if v != v:
        return default
    return max(lo, min(hi, v))


class Room:
    def __init__(self, rid):
        self.id = rid
        self.seed = random.randint(1, 10 ** 6)
        self.level = 1
        self.started = False
        self.players = {}
        self.dead = set()
        self.next_pid = 0
        self.host = None
        self.shared = dict(done=set(), inv=set(), open=set())

    def snapshot(self):
        return {k: list(v) for k, v in self.shared.items()}

    def clear_progress(self):
        for v in self.shared.values():
            v.clear()
        self.dead.clear()

    def roster(self):
        return [[pid, c.name] for pid, c in sorted(self.players.items())]

    def broadcast(self, d, skip=None):
        for pid, c in list(self.players.items()):
            if pid != skip:
                c.send(d)

    def check_wipe(self):
        """كل اللاعبين ماتوا؟ يبقى الفريق كله يعيد الشقة"""
        if self.started and self.players and all(p in self.dead for p in self.players):
            self.clear_progress()
            self.broadcast(dict(t='wipe', level=self.level))


class Client:
    def __init__(self, writer):
        self.w = writer
        self.room = None
        self.pid = None
        self.name = ''
        self.tokens = RATE
        self.stamp = time.monotonic()
        self.last_chat = 0.0

    def send(self, d):
        try:
            if self.w.transport.get_write_buffer_size() > 2_000_000:     # لاعب بطيء جدًا: بنفصله
                self.w.close()
                return
            self.w.write((json.dumps(d, separators=(',', ':'), ensure_ascii=False) + "\n").encode('utf-8'))
        except Exception:
            pass

    def allow(self):
        now = time.monotonic()
        self.tokens = min(RATE, self.tokens + (now - self.stamp) * RATE)
        self.stamp = now
        if self.tokens < 1:
            return False
        self.tokens -= 1
        return True


def new_room_id():
    for _ in range(200):
        rid = str(random.randint(10000, 99999))
        if rid not in ROOMS:
            return rid
    return None


def join_room(c, room):
    pid = room.next_pid
    room.next_pid += 1
    c.room, c.pid = room, pid
    room.players[pid] = c
    if room.host is None:
        room.host = pid
    c.send(dict(t='room', room=room.id, you=pid, host=room.host, players=room.roster(),
                started=room.started, level=room.level, seed=room.seed, shared=room.snapshot(),
                dead=sorted(room.dead)))
    room.broadcast(dict(t='joined', id=pid, name=c.name), skip=pid)


def leave(c):
    room = c.room
    if not room:
        return
    c.room = None
    room.players.pop(c.pid, None)
    room.dead.discard(c.pid)
    if not room.players:
        ROOMS.pop(room.id, None)
        log("غرفة اتقفلت:", room.id)
        return
    if room.host == c.pid:
        room.host = min(room.players)
    room.broadcast(dict(t='left', id=c.pid, host=room.host))
    room.check_wipe()


def dispatch(c, m):
    t = m.get('t')
    room = c.room
    if t == 'create' and not room:
        if len(ROOMS) >= MAX_ROOMS:
            return c.send(dict(t='err', msg='busy'))
        rid = new_room_id()
        if not rid:
            return c.send(dict(t='err', msg='busy'))
        c.name = clean_name(m.get('name'))
        ROOMS[rid] = Room(rid)
        log("غرفة جديدة:", rid, c.name)
        join_room(c, ROOMS[rid])
    elif t == 'join' and not room:
        r = ROOMS.get(str(m.get('room', ''))[:8])
        if not r:
            return c.send(dict(t='err', msg='notfound'))
        if len(r.players) >= MAX_PLAYERS:
            return c.send(dict(t='err', msg='full'))
        c.name = clean_name(m.get('name'))
        join_room(c, r)
    elif not room:
        return
    elif t == 'chat':
        txt = ''.join(ch for ch in str(m.get('text', '')) if ch.isprintable()).strip()[:100]
        now = time.monotonic()
        if txt and now - c.last_chat > 0.4:
            c.last_chat = now
            room.broadcast(dict(t='chat', id=c.pid, text=txt), skip=c.pid)
    elif t == 'start':
        if c.pid == room.host and not room.started:
            room.started, room.level = True, 1
            room.clear_progress()
            room.broadcast(dict(t='start', seed=room.seed, level=1))
    elif t == 'pos' and room.started:
        d = dict(t='pos', id=c.pid, x=num(m.get('x')), y=num(m.get('y')), fx=num(m.get('fx'), -1, 1),
                 fy=num(m.get('fy'), -1, 1), mv=int(num(m.get('mv'), 0, 1)), fl=int(num(m.get('fl'), 0, 1)),
                 lv=int(num(m.get('lv'), 0, 99)), ls=1 if c.pid in room.dead else 0,
                 ex=str(m.get('ex', 'neutral'))[:10], fr=int(num(m.get('fr'), 0, 100)))
        gh = []
        for it in (m.get('gh') or [])[:4]:
            if isinstance(it, list) and len(it) == 4:
                gh.append([num(it[0]), num(it[1]), num(it[2], 0, 1), int(num(it[3], 0, 9))])
        d['gh'] = gh
        room.broadcast(d, skip=c.pid)
    elif t == 'ev' and room.started:
        k, v = m.get('k'), m.get('v')
        if k in ('done', 'inv', 'open') and isinstance(v, (str, int)) and len(str(v)) <= 64:
            room.shared[k].add(v)
            room.broadcast(dict(t='ev', id=c.pid, k=k, v=v), skip=c.pid)
    elif t == 'lose' and room.started:
        if c.pid not in room.dead:
            room.dead.add(c.pid)
            room.broadcast(dict(t='lose', id=c.pid), skip=c.pid)
            room.check_wipe()
    elif t == 'next' and room.started:
        if m.get('from') == room.level:
            room.clear_progress()
            if room.level >= MAX_LEVEL:
                room.started = False
                room.broadcast(dict(t='win'))
            else:
                room.level += 1
                room.broadcast(dict(t='next', level=room.level))
    # 'ping' وأي حاجة تانية: بس بتحدّث مؤقّت الخمول


async def handle(reader, writer):
    c = Client(writer)
    try:
        while True:
            line = await asyncio.wait_for(reader.readline(), IDLE_TIMEOUT)
            if not line:
                break
            if not c.allow():
                break
            try:
                m = json.loads(line)
            except ValueError:
                continue
            if isinstance(m, dict):
                dispatch(c, m)
    except (asyncio.TimeoutError, ConnectionError, ValueError, OSError):
        pass
    finally:
        leave(c)
        try:
            writer.close()
        except Exception:
            pass


async def serve(port=PORT):
    srv = await asyncio.start_server(handle, '0.0.0.0', port, limit=16384)
    log("سيرفر بيت الهمس شغّال على البورت", port)
    async with srv:
        await srv.serve_forever()


def run_in_thread(port=PORT):
    """بيشغّل السيرفر في Thread جوه اللعبة (للعب على نفس الشبكة). بيرمي OSError لو البورت مشغول"""
    import threading
    ready = threading.Event()
    box = {}

    def runner():
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        try:
            box['srv'] = loop.run_until_complete(asyncio.start_server(handle, '0.0.0.0', port, limit=16384))
        except OSError as ex:
            box['err'] = ex
            ready.set()
            return
        ready.set()
        loop.run_forever()

    threading.Thread(target=runner, daemon=True).start()
    ready.wait(5)
    if 'err' in box:
        raise box['err']
    return port


if __name__ == "__main__":
    p = int(sys.argv[1]) if len(sys.argv) > 1 else PORT
    try:
        asyncio.run(serve(p))
    except KeyboardInterrupt:
        pass

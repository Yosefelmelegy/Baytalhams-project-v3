import sys
import math
import random
import array
import json
import os
import datetime
import wave
import hashlib
import tempfile
import subprocess
import socket
import threading
import queue

try:
    import pygame
except ImportError:
    print("لازم تنزّل المكتبات:  pip install pygame arabic-reshaper python-bidi")
    sys.exit(1)
try:
    import arabic_reshaper
    try:
        from bidi import get_display
    except ImportError:
        from bidi.algorithm import get_display
except ImportError:
    print("لازم تنزّل المكتبات:  pip install pygame arabic-reshaper python-bidi")
    sys.exit(1)

import fp3d

VIEW3D = True                          # منظور أول (اضغط V عشان ترجع للمنظور من فوق)
MOUSE_SENS = 0.0026                    # حساسية الماوس

# ================================================================= إعدادات
SW, SH = 960, 640
T = 32
MAX_LEVEL = 10
# ---- الخوف: لو العداد اتملى بتخسر (والوحش لو لمسك بتخسر برضه)
FEAR_LOSE = 100.0
FEAR_GAIN = 0.85                       # كل زيادة خوف بتتضرب في الرقم ده (قلّله لو عايزها أسهل)
FEAR_DECAY = 1.6                       # سرعة هدوء الخوف في الثانية لما مفيش حاجة مخيفة
# ---- الأونلاين
MAX_PLAYERS = 8
NET_PORT = 16613
DEFAULT_SERVER = ""                    # اكتب هنا عنوان سيرفرك لو عايز يبقى جاهز عند صحابك (مثال "1.2.3.4:8765")
SERVER_ADDR = DEFAULT_SERVER
PLAYER_SC = 0.6                        # حجم الشخصية على الشاشة
CHAT_QUICK = ["تعالوا هنا!", "فيه وحش ورايا!", "ساعدوني!", "لقيت مفتاح", "استنوني", "مين معاه بطارية؟"]
GHOST_CHAT = ["{name}... أنا شايفك", "ماتبصّش وراك", "هو بيسمعكم من الحيطان", "محدش فيكم هيخرج",
              "مين اللي واقف جنبك؟", "{name}... ليه لوحدك؟", "ده مش {name}", "افتح الباب... افتحه"]
ONLINE_STATES = ('online', 'online_join', 'online_server', 'connecting', 'lobby')
FOOTSTEP_VOL = 0.10                    # صوت خطوات اللاعب (0 = بدون صوت)
BDAY_TEXT = "Happy New Year!"          # الجملة اللي الوحش بيقولها يوم الميلاد
# ---- المنصّة: أندرويد / ويندوز (EXE) / تشغيل عادي
ANDROID = 'ANDROID_ARGUMENT' in os.environ or 'ANDROID_PRIVATE' in os.environ
FROZEN = getattr(sys, 'frozen', False)
TOUCH = ANDROID or ('--touch' in sys.argv)           # وضع اللمس: موبايل، أو تجربة على الكمبيوتر بـ --touch
BASE_DIR = getattr(sys, '_MEIPASS', None) or os.path.dirname(os.path.abspath(__file__))   # ملفات اللعبة (assets)
if ANDROID:
    APP_DIR = os.environ.get('ANDROID_PRIVATE') or BASE_DIR        # مكان الحفظ على الموبايل
elif FROZEN:
    APP_DIR = os.path.dirname(sys.executable)                      # الحفظ جنب الـ EXE (مش الفولدر المؤقت)
else:
    APP_DIR = os.path.dirname(os.path.abspath(__file__))


def asset(name):
    return os.path.join(BASE_DIR, "assets", name)


SAVE_FILE = os.path.join(APP_DIR, "savegame.json")


LANG = 'ar'                       # اللغة الحالية: 'ar' أو 'en'  (زرار اللغة في القايمة أو حرف L)
EN = {}                           # القاموس: النص العربي -> الإنجليزي (في آخر الملف)


def tr(s):
    return EN.get(s, s) if LANG == 'en' else s


class S:
    """نص بيتترجم لوحده حسب اللغة الحالية"""

    def __init__(self, key, **kw):
        self.key, self.kw = key, kw

    def __str__(self):
        t = str(tr(self.key))
        if not self.kw:
            return t
        return t.format(**{k: (str(v) if isinstance(v, S) else tr(v) if isinstance(v, str) else v)
                           for k, v in self.kw.items()})


def diff(n):
    """الصعوبة بتزيد مع كل مرحلة"""
    return dict(cd=max(6.0, 20 - 1.6 * n),           # أقل فاصل بين خضّتين
                gmax=1 + (n >= 4) + (n >= 7) + (n >= 10),         # عدد الأشباح مع بعض
                gcd=max(8.0, 38 - 3.0 * n),          # وقت ظهور الشبح
                gspd=5 * n,                           # سرعة الشبح
                drain=0.6 * (1 + 0.05 * n),           # سرعة سحب بطارية الكشاف
                   amb=max(7.0, 24 - 2.2 * n))          # الأصوات العشوائية


# ================================================================= الأوض والأثاث
class Level:
    pass


class Obj:
    def __init__(self, oid, name, tx, ty, tw, th, color, solid=True, **kw):
        self.id, self.name = oid, name
        self.rect = pygame.Rect(tx * T, ty * T, tw * T, th * T)
        self.color, self.solid, self.can = color, solid, True
        self.kind = 'flavor'
        self.title = name
        self.text = ["مفيش حاجة هنا... بس حاسس إن حد بيبصلك."]
        self.give = self.need = self.scare = None
        self.finale = False
        self.lines = self.locked = []
        self.empty = "فاضي."
        self.toast = ""
        self.sp = None
        self.where = ""
        self.__dict__.update(kw)


GENERIC_FLAVOR = [
    ["مفيش حاجة هنا... بس حاسس إن حد بيبصلك."],
    ["الغبار هنا لسه مهزوز... حد لمس المكان من لحظة."],
    ["سمعت همس خفيف طالع من هنا."],
    ["ريحة رطوبة تقيلة... وحاجة تانية أوحش."],
    ["فيه بصمة إيد صغيرة على السطح."],
    ["فيه خربشة على الخشب: \"اخرج\"."],
    ["مفيش حاجة جوه... بس كان فيه حد هنا."],
    ["حاسس إن المكان ده اتحرّك ورايا... مش متأكد."],
]

# ---------------- المرحلة 1 (بيت مرسوم باليد) ----------------
ROOMS1 = [
    ("الصالة", (16, 16, 8, 8), (74, 52, 38)),
    ("أوضة المعيشة", (2, 16, 12, 8), (68, 50, 60)),
    ("المطبخ", (26, 16, 12, 8), (98, 98, 92)),
    ("أوضة النوم", (2, 2, 10, 7), (64, 44, 50)),
    ("المكتبة", (14, 2, 10, 7), (62, 46, 30)),
    ("المكتب", (26, 2, 12, 7), (40, 58, 54)),
    ("الممر", (2, 11, 36, 3), (54, 46, 42)),
]
DOORS1 = [(14, 19, 2, 2), (24, 19, 2, 2), (7, 14, 2, 2), (19, 14, 2, 2),
          (33, 14, 2, 2), (6, 9, 2, 2), (18, 9, 2, 2), (31, 9, 2, 2), (19, 24, 2, 1)]
RUGS1 = [(18, 18, 4, 3, (84, 28, 28)), (4, 5, 5, 3, (56, 34, 70)),
         (17, 4, 4, 3, (30, 60, 70)), (28, 5, 6, 3, (70, 40, 30)), (5, 18, 3, 2, (40, 60, 50))]
CANDLES1 = [(16, 17), (13, 17), (11, 8), (14, 8), (37, 8), (37, 23), (2, 12), (37, 12)]

TEXTS1 = {
    'hall_table': ("ورقة على الترابيزة", [
        "ورقة مكتوبة بخط مرتعش:",
        "\"الباب الكبير اتقفل لوحده... ومش هيتفتح غير بمفتاحه.",
        "المفتاح في المكتب اللي فوق، والمكتب مقفول.",
        "دوّر كويس... وماتبصّش ورا.\""]),
    'bookshelf_l': ("ورقة بين الكتب", [
        "لقيت ورقة قديمة:",
        "\"المفتاح النحاسي بتاع المكتب كنت دايمًا",
        "أخبّيه في دولاب أوضة النوم.\""]),
    'nightstand': ("مذكرات قديمة", [
        "\"كل ليلة بسمع خطوات قدام باب الأوضة.",
        "النهارده الخطوات وقفت... جوه الأوضة.\"",
        "آخر صفحة متبلّلة بحاجة حمرا..."]),
    'lib_desk': ("ورقة على المكتب", [
        "\"درج المكتب الكبير مفتاحه صغير.",
        "كنت بحطه في حتة باردة... في المطبخ.\""]),
    'bed': ("السرير", ["السرير متبهدل... والملاية لسه دافية!"]),
    'coffee_table': ("ترابيزة القهوة", ["كوباية شاي على الترابيزة... ولسه بتطلّع بخار."]),
    'stove': ("البوتجاز", ["البوتجاز بارد... بس سامع صوت غليان من جوه الحلّة!"]),
    'k_table': ("ترابيزة السفرة", ["حوالين الترابيزة أربع كراسي. الكرسي الرابع لسه بيهتز."]),
    'sink': ("الحوض", ["الحنفية بتنقّط... والميّه لونها مش طبيعي."]),
    'shelf_1': ("الكتب", ["كل الكتب دي عن الأرواح والأحلام المزعجة."]),
    'shelf_2': ("الكتب", ["كتاب مفتوح على صفحة مكتوب فيها: \"هو شايفك\"."]),
    'chair': ("الكرسي الهزّاز", ["الكرسي بيهتز لوحده... بعدت عنه بسرعة."]),
    'safe': ("الخزنة", ["خزنة محتاجة رقم سري، ومفيش حاجة هنا تفتحها."]),
}
BATTERY1 = {'sofa': "تحت وسادة الكنبة", 'drawer': "في الدرج", 'shelf_3': "ورا الكتب",
            'cabinet': "في الدولاب العلوي", 'study_shelf': "بين الكتب"}

SP1 = {
    'wardrobe': dict(kind='container', give='ka', scare='face', title="الدولاب",
                     lines=["جوه الدولاب لقيت مفتاح نحاسي تقيل.", "ده مفتاح المكتب."],
                     empty="الدولاب فاضي دلوقتي."),
    'fridge': dict(kind='container', give='small', scare='flicker', title="التلاجة",
                   lines=["التلاجة ريحتها وحشة...", "لقيت مفتاح صغير متلزّق في الباب من جوه."],
                   empty="التلاجة فاضية... وريحتها وحشة."),
    'desk': dict(kind='container', need='small', give='exit', finale=True, title="مكتب كبير",
                 locked=["الدرج الكبير مقفول بقفل صغير.", "محتاج مفتاح صغير."],
                 lines=["فتحت الدرج بالمفتاح الصغير...",
                        "لقيت مفتاح كبير صدّي: مفتاح الباب الأمامي!",
                        "يلا اجري على الباب!"],
                 empty="الدرج فاضي دلوقتي."),
    'study_door': dict(kind='door', need='ka', title="باب المكتب", toast="فتحت باب المكتب!",
                       locked=["الباب مقفول بمفتاح نحاسي.", "لازم تلاقيه."]),
    'front_door': dict(kind='exit', need='exit', title="الباب الأمامي",
                       locked=["الباب تقيل ومقفول بإحكام.", "محتاج مفتاحه... ومش معاك."]),
    'piano': dict(kind='special', sp='piano'),
    'portrait': dict(kind='special', sp='portrait'),
    'mirror': dict(kind='special', sp='mirror'),
    'doll': dict(kind='special', sp='doll'),
}


def build_objs1(seed=0):
    O = []

    def add(*a):
        O.append(Obj(*a))
    add('hall_table', "الترابيزة", 21, 17, 2, 1, (104, 66, 34))
    add('front_door', "الباب الأمامي", 19, 24, 2, 1, (110, 30, 30))
    add('bookshelf_l', "المكتبة الصغيرة", 2, 16, 3, 1, (80, 50, 28))
    add('sofa', "الكنبة", 3, 21, 4, 2, (110, 56, 90))
    add('coffee_table', "ترابيزة القهوة", 4, 19, 2, 1, (96, 62, 36))
    add('piano', "البيانو", 9, 21, 3, 2, (24, 24, 28))
    add('bed', "السرير", 3, 3, 3, 2, (130, 70, 70))
    add('nightstand', "الكومودينو", 6, 3, 1, 1, (100, 66, 40))
    add('wardrobe', "الدولاب", 9, 2, 2, 1, (88, 54, 30))
    add('drawer', "الدُرج", 2, 7, 2, 1, (96, 62, 36))
    add('shelf_1', "رف الكتب", 14, 2, 3, 1, (76, 48, 26))
    add('shelf_2', "رف الكتب", 17, 2, 3, 1, (76, 48, 26))
    add('shelf_3', "رف الكتب", 21, 2, 3, 1, (76, 48, 26))
    add('lib_desk', "مكتب المكتبة", 20, 6, 3, 2, (96, 62, 36))
    add('chair', "كرسي هزّاز", 15, 5, 2, 2, (120, 80, 50))
    add('stove', "البوتجاز", 27, 16, 3, 1, (74, 74, 80))
    add('fridge', "التلاجة", 30, 16, 2, 1, (196, 200, 206))
    add('cabinet', "الدولاب العلوي", 36, 16, 2, 1, (120, 84, 50))
    add('sink', "الحوض", 26, 22, 2, 1, (150, 156, 160))
    add('k_table', "ترابيزة السفرة", 30, 20, 3, 2, (110, 74, 44))
    add('study_door', "باب المكتب - مقفول", 31, 10, 2, 1, (112, 72, 30))
    add('desk', "مكتب كبير", 30, 3, 4, 2, (92, 58, 32))
    add('safe', "الخزنة", 26, 3, 1, 2, (60, 60, 66))
    add('portrait', "الصورة الكبيرة", 28, 2, 2, 1, (120, 100, 40))
    add('study_shelf', "رف الكتب", 35, 2, 3, 1, (76, 48, 26))
    add('mirror', "المراية الكبيرة", 22, 16, 2, 1, (170, 190, 200))
    add('doll', "الدُمية الكبيرة", 10, 7, 1, 1, (200, 150, 160))
    randomize_level1(O, seed)
    return O


KEY_SPOTS1 = ('wardrobe', 'drawer', 'nightstand', 'cabinet', 'fridge', 'bookshelf_l', 'lib_desk', 'hall_table',
              'shelf_1', 'shelf_2', 'shelf_3', 'sofa', 'k_table')
FIXED1 = ('desk', 'study_door', 'front_door', 'piano', 'portrait', 'mirror', 'doll')
HINT_NOTES1 = ('hall_table', 'bookshelf_l', 'lib_desk')


def room_name1(o):
    cx, cy = o.rect.centerx // T, o.rect.centery // T
    for nm, (x, y, w, h), _c in ROOMS1:
        if nm != "الممر" and x <= cx < x + w and y <= cy < y + h:
            return nm
    return "الممر"


def randomize_level1(O, seed):
    """المفتاح النحاسي والصغير والبطاريات والأوراق بتتحط في أماكن مختلفة في كل لعبة (والورق بيقول المكان الصح)"""
    rng = random.Random(seed * 13 + 1)
    by = {o.id: o for o in O}
    for oid in FIXED1:
        by[oid].__dict__.update(SP1[oid])
    for o in O:
        if o.id in TEXTS1 and o.id not in HINT_NOTES1:
            o.kind, (o.title, o.text) = 'note', TEXTS1[o.id]
    names1 = {'ka': "مفتاح المكتب النحاسي", 'small': "المفتاح الصغير"}
    study = {o.id for o in O if room_name1(o) == "المكتب"}
    spots = [o for o in O if o.id in KEY_SPOTS1 and o.id not in study]
    rng.shuffle(spots)
    cKa, cSm = spots.pop(), spots.pop()

    def mk(o, give):
        o.kind, o.give = 'container', give
        o.lines = [S("فتحت {f}...", f=o.name), S("ولقيت {k}!", k=names1[give])]
        o.empty = "فاضي دلوقتي."
        o.scare = rng.choice(['face', 'flicker', 'flicker', 'bang'])
    mk(cKa, 'ka')
    mk(cSm, 'small')

    def hint(o):
        return S("في {f} في {r}", f=o.name, r=room_name1(o))
    pool = [o for o in O if o.kind in ('flavor', 'note') and o.id not in study]
    rng.shuffle(pool)
    notes = [TEXTS1['hall_table'],
             ("ورقة بين الكتب", [S("ورقة قديمة...", ), S("مفتاح المكتب النحاسي مخبّي {h}.", h=hint(cKa))]),
             ("ورقة مطوية", [S("ورقة قديمة...", ), S("المفتاح الصغير بتاع الدُرج... {h}.", h=hint(cSm))])]
    for ttl, lines in notes:
        o = pool.pop()
        o.kind, o.title, o.text = 'note', ttl, list(lines)
    bp = pool + [by['study_shelf']]
    rng.shuffle(bp)
    for o in bp[:5]:
        o.kind, o.where = 'battery', S("جوه {f}", f=o.name)


# ================================================================= حكاية البيت (أوراق ودفاتر في الشقق)
STORY = {}
for _n, _t, _l, _te, _le in [(1, 'كارت قديم', ['د. عادل الحكيم - طبيب أطفال', 'الشقة 1 - عمارة الهمس - 1987'], 'Old business card', ['Dr. Adel El-Hakim - Pediatrician', 'Apartment 1 - Whispering Building - 1987']), (1, 'جواب ماتبعتش', ['حبيبتي سلمى، انتقلنا النهارده.', 'العمارة هادية أوي... هادية زيادة.'], 'A letter never sent', ['My dear Salma, we moved in today.', 'The building is so quiet... too quiet.']), (2, 'دفتر ليلى', ['صاحبي الجديد ساكن في الحيطة.', 'بيقول اسمه "اللي تحت". بيحب الاستغماية.'], "Layla's notebook", ['My new friend lives in the wall.', 'He says his name is "The One Below". He loves hide and seek.']), (2, 'تحذير', ['عم رضوان قال: "متنزلوش البدروم بالليل".', 'ومرضيش يقول ليه.'], 'A warning', ['Uncle Radwan said: "Never go down to the basement at night."', "He wouldn't say why."]), (3, 'ورقة صفرا', ['العمارة اتبنت فوق بير قديم.', 'كانوا بيرموا فيه كل اللي مش عايزينه... حتى ناس.'], 'Yellowed paper', ['The building was built over an old well.', "They threw in everything they didn't want... even people."]), (3, 'دفتر عادل', ['سلمى بتسمع همس بالليل.', 'قلتلها أعصاب. كنت غلطان.'], "Adel's notebook", ['Salma hears whispers at night.', 'I told her it was nerves. I was wrong.']), (4, 'رسمة بالشمع', ['ليلى رسمت بيتنا... وفي الأرض بير.', 'وحوالين البير ناس كتير واقفين.'], 'Crayon drawing', ['Layla drew our house... with a well in the ground.', 'And many people standing around it.']), (4, 'رسالة عم رضوان', ['أنا حاولت أقفل البير بالأسمنت سنين.', 'كل مرة يرجع يتفتح من تحت.'], "Uncle Radwan's message", ['I tried sealing the well with concrete for years.', 'Every time, it reopens from below.']), (5, 'دفتر عادل', ['سلمى اختفت امبارح. بابها مقفول من جوه.', 'والبوليس قال: "سافرت". هي مسافرتش.'], "Adel's notebook", ['Salma vanished yesterday. Her door is locked from inside.', 'The police said: "She left." She did not.']), (5, 'علبة موسيقى', ['مكتوب تحتها: "لسلمى... عشان تنامي".', 'واللحن بيشتغل لوحده من يومها.'], 'Music box', ['Written underneath: "For Salma... so you can sleep."', 'The tune has played by itself ever since.']), (6, 'ورقة مبلولة', ['سمعتها بتنادي عليا من تحت.', 'بس بتقول جملة واحدة: "ما تجيش".'], 'Damp paper', ['I heard her calling me from below.', 'But she only says one thing: "Don\'t come."']), (6, 'دفتر ليلى', ['ماما بتلعب معانا استغماية دلوقتي.', 'بس هي دايمًا اللي بتستخبى.'], "Layla's notebook", ['Mama plays hide and seek with us now.', 'But she is always the one hiding.']), (7, 'تقرير طبي', ['المريض: عادل الحكيم. بيسمع أصوات.', 'النوم: صفر. التوصية: يسيب العمارة فورًا.'], 'Medical report', ['Patient: Adel El-Hakim. Hears voices.', 'Sleep: none. Recommendation: leave the building at once.']), (7, 'ورقة بخط مرتعش', ['ليلى مش بتنام في سريرها.', 'بلاقيها واقفة قدام الحيطة... بتبتسم.'], 'Shaky handwriting', ["Layla doesn't sleep in her bed.", 'I find her standing before the wall... smiling.']), (8, 'دفتر عادل', ['نزلت البدروم. البير مفتوح.', 'وفيه سلم نازل لتحت... والتحت مضلّم.'], "Adel's notebook", ['I went down to the basement. The well is open.', 'There are stairs going down... and it is dark below.']), (8, 'نقش على الحيطة', ['"اللي بيفتح البير بيسكن العمارة للأبد".', 'وتحتها أسماء كتير... آخرها: عادل.'], 'Carving on the wall', ['"Whoever opens the well lives in the building forever."', 'Below it, many names... the last one: Adel.']), (9, 'ورقة من عادل', ['مش قادر أخرج. كل باب بيطلّعني شقة تانية.', 'كنت فاكر إني بدوّر على سلمى وليلى...'], 'A page from Adel', ["I can't get out. Every door leads to another apartment.", 'I thought I was searching for Salma and Layla...']), (9, 'اعتراف', ['الحقيقة: مفيش حد خطفهم.', 'أنا اللي فتحت البير... وهما دخلوا وراي.'], 'Confession', ['The truth: nobody kidnapped them.', 'I opened the well... and they followed me in.']), (10, 'الصفحة الأخيرة', ['كل واحد يدخل العمارة فاكر إنه بيهرب.', 'بس العمارة هي اللي بتختار مين يطلع.'], 'The last page', ['Everyone who enters thinks they are escaping.', 'But the building decides who gets out.']), (10, 'بخط ليلى', ['لو وصلت هنا... هو مش عايز يخرّجك.', 'عايزك تلعب معاه. افتح الباب واجري.'], "In Layla's handwriting", ["If you made it here... he doesn't want to let you out.", 'He wants you to play with him. Open the door and run.'])]:
    STORY.setdefault(_n, []).append((_t, _l))
CHAPTER = {n: t for n, t, _e in [(2, 'الفصل 2: صاحب ليلى اللي في الحيطة', "Chapter 2: Layla's friend in the wall"), (3, 'الفصل 3: البير', 'Chapter 3: The Well'), (4, 'الفصل 4: الرسمة', 'Chapter 4: The Drawing'), (5, 'الفصل 5: اختفاء سلمى', 'Chapter 5: Salma Vanishes'), (6, 'الفصل 6: اللي بينادي من تحت', 'Chapter 6: The Voice From Below'), (7, 'الفصل 7: ليلى مبتنامش', "Chapter 7: Layla Doesn't Sleep"), (8, 'الفصل 8: السلم', 'Chapter 8: The Stairs'), (9, 'الفصل 9: الحقيقة', 'Chapter 9: The Truth'), (10, 'الفصل 10: اللي بيختار', 'Chapter 10: The One Who Chooses')]}
STORY_END = 'وفي دفتر عادل القديم... اتكتب سطر جديد باسمك.'


def place_story(objs, n, seed):
    """بيحوّل كام قطعة أثاث عادية لأوراق من الحكاية (بعشوائية منفصلة، فنفس الشقة بتطلع نفس الأوراق عند كل اللاعبين)"""
    pool = [o for o in objs if o.kind == 'flavor']
    random.Random(seed * 7 + n).shuffle(pool)
    for o, (ttl, lines) in zip(pool, STORY.get(n, [])):
        o.kind, o.title, o.text = 'note', ttl, list(lines)


def build_level1(seed=0):
    lv = Level()
    lv.n, lv.W, lv.H = 1, 40, 26
    lv.title = "البيت القديم"
    lv.grid = [[1] * lv.W for _ in range(lv.H)]
    lv.floorc = [[(0, 0, 0)] * lv.W for _ in range(lv.H)]

    def carve(x, y, w, h, c):
        for j in range(y, y + h):
            for i in range(x, x + w):
                lv.grid[j][i] = 0
                lv.floorc[j][i] = c
    for _n, (x, y, w, h), c in ROOMS1:
        carve(x, y, w, h, c)
    for d in DOORS1:
        carve(*d, (58, 48, 40))
    lv.rooms = ROOMS1
    lv.rugs = RUGS1
    lv.candles = CANDLES1
    lv.objs = build_objs1(seed)
    lv.triggers = [dict(rect=pygame.Rect(a * T, b * T, c * T, d * T), kind=k, fired=False)
                   for a, b, c, d, k in [(10, 11, 3, 3, 'flicker'), (16, 4, 5, 2, 'bang'),
                                         (25, 11, 3, 3, 'face'), (27, 19, 5, 3, 'bang'),
                                         (4, 6, 4, 2, 'flicker'), (8, 18, 3, 2, 'face'),
                                         (17, 11, 3, 3, 'dash'), (4, 11, 3, 3, 'eyes'),
                                         (33, 11, 3, 3, 'watch'), (21, 19, 2, 2, 'knock'),
                                         (8, 4, 3, 2, 'name')]]
    lv.floors = [(i, j) for j in range(lv.H) for i in range(lv.W) if lv.grid[j][i] == 0]
    lv.start = (20 * T + 16, 21 * T + 16)
    lv.item_names = {'ka': "مفتاح المكتب النحاسي", 'small': "المفتاح الصغير", 'exit': "مفتاح الباب الأمامي"}

    def goal(g):
        if 'exit' in g.inv:
            return "اهرب من الباب الأمامي!"
        if 'study_door' in g.opened:
            return "افتح درج المكتب" if 'small' in g.inv else "دوّر على مفتاح صغير للدرج"
        if 'ka' in g.inv:
            return "افتح باب المكتب، فوق ناحية اليمين"
        return "دوّر على مفتاح المكتب النحاسي"
    lv.goal = goal
    return lv


# ---------------- المراحل 2..10 (بتتولّد تلقائي) ----------------
DIMS = {2: (3, 2), 3: (3, 3), 4: (4, 3), 5: (5, 3), 6: (4, 4), 7: (5, 4), 8: (6, 4), 9: (5, 5), 10: (6, 5)}
RW, RH = 9, 7
NAMES = ["أوضة النوم", "المكتبة", "المطبخ", "الصالة", "الحمّام", "أوضة الأطفال", "المخزن", "أوضة الضيوف",
         "السفرة", "البدروم", "العلّية", "المكتب", "أوضة الغسيل", "الشرفة", "أوضة الخياطة", "أوضة الموسيقى",
         "المرسم", "الطرقة الكبيرة", "أوضة الأجداد", "أوضة الصلاة", "غرفة الكتب القديمة", "أوضة الألعاب",
         "الأنتريه", "المخبأ", "غرفة المراية", "مخزن الخشب", "أوضة الساعة", "غرفة المرضى", "القبو",
         "أوضة الضوء الأحمر", "غرفة الدُمى", "أوضة السفرجي", "غرفة النجف"]
FURN = [("السرير", 3, 2, (130, 70, 70)), ("الدولاب", 2, 1, (88, 54, 30)), ("الكومودينو", 1, 1, (100, 66, 40)),
        ("المكتب", 3, 2, (96, 62, 36)), ("رف الكتب", 3, 1, (76, 48, 26)), ("الكنبة", 3, 1, (110, 56, 90)),
        ("الترابيزة", 2, 1, (104, 66, 34)), ("الصندوق الخشب", 1, 1, (110, 80, 40)),
        ("التلاجة", 1, 1, (196, 200, 206)), ("الخزانة", 2, 1, (80, 60, 40)), ("البيانو", 2, 2, (24, 24, 28)),
        ("الكرسي الهزّاز", 1, 1, (120, 80, 50)), ("الدُرج", 2, 1, (96, 62, 36)),
        ("المراية الكبيرة", 1, 1, (170, 190, 200)), ("الصورة", 2, 1, (120, 100, 40)),
        ("الدُمية الكبيرة", 1, 1, (200, 150, 160))]
PALETTE = [(74, 52, 38), (68, 50, 60), (98, 98, 92), (64, 44, 50), (62, 46, 30), (40, 58, 54),
           (60, 52, 70), (80, 60, 48), (52, 62, 52), (88, 70, 60)]
RUGCOL = [(84, 28, 28), (56, 34, 70), (30, 60, 70), (70, 40, 30), (40, 60, 50)]


def gen_level(n, seed):
    rng = random.Random(seed * 100 + n)
    srng = random.Random(seed * 31 + n)          # عشوائية منفصلة للخضّات (علشان شكل البيت ما يتغيّرش)
    cols, rows = DIMS[n]
    lv = Level()
    lv.n, lv.title = n, S("الشقة {n}", n=n)
    lv.W, lv.H = 2 + cols * (RW + 2), 2 + rows * (RH + 2)
    lv.grid = [[1] * lv.W for _ in range(lv.H)]
    lv.floorc = [[(0, 0, 0)] * lv.W for _ in range(lv.H)]
    dark_f = 1 - 0.04 * n

    def carve(x, y, w, h, c):
        for j in range(y, y + h):
            for i in range(x, x + w):
                lv.grid[j][i] = 0
                lv.floorc[j][i] = c

    def org(c, r):
        return 2 + c * (RW + 2), 2 + r * (RH + 2)

    names = NAMES[:]
    rng.shuffle(names)
    cells = [(c, r) for r in range(rows) for c in range(cols)]
    cell = {}
    for i, cr in enumerate(cells):
        x0, y0 = org(*cr)
        col = tuple(int(v * dark_f) for v in rng.choice(PALETTE))
        nm = names[i] if i < len(names) else S("أوضة {n}", n=i + 1)
        cell[cr] = dict(name=nm, x0=x0, y0=y0, col=col)
        carve(x0, y0, RW, RH, col)
    lv.rooms = [(v['name'], (v['x0'], v['y0'], RW, RH), v['col']) for v in cell.values()]

    # شجرة الأوض (متاهة)
    start = (cols // 2, rows - 1)
    seen, stack, edges = {start}, [start], []
    while stack:
        cur = stack[-1]
        nb = [(cur[0] + dc, cur[1] + dr) for dc, dr in ((1, 0), (-1, 0), (0, 1), (0, -1))
              if 0 <= cur[0] + dc < cols and 0 <= cur[1] + dr < rows and (cur[0] + dc, cur[1] + dr) not in seen]
        if nb:
            nx = rng.choice(nb)
            seen.add(nx)
            edges.append((cur, nx))
            stack.append(nx)
        else:
            stack.pop()
    deg = {c: 0 for c in cells}
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    leaves = [c for c in cells if deg[c] == 1 and c != start]
    rng.shuffle(leaves)
    locks = leaves[:2] if (n >= 7 and len(leaves) >= 2) else leaves[:1]
    A = locks[0]
    B = locks[1] if len(locks) > 1 else None

    # أبواب إضافية (لفّات)
    lockset = set(locks)
    pairs = []
    es = set(edges) | set((b, a) for a, b in edges)
    for (c, r) in cells:
        for dc, dr in ((1, 0), (0, 1)):
            o2 = (c + dc, r + dr)
            if o2 in cell and ((c, r), o2) not in es and (c, r) not in lockset and o2 not in lockset:
                pairs.append(((c, r), o2))
    rng.shuffle(pairs)
    all_edges = list(edges) + pairs[:len(cells) // 4]

    def gap(a, b):
        (c1, r1), (c2, r2) = a, b
        if r1 == r2:
            left = a if c1 < c2 else b
            lx, ly = org(*left)
            return (lx + RW, ly + 3, 2, 2)
        top = a if r1 < r2 else b
        tx, ty = org(*top)
        return (tx + 4, ty + RH, 2, 2)

    doorzones = {c: [] for c in cells}
    objs = []
    for a, b in all_edges:
        g = gap(a, b)
        carve(*g, (58, 48, 40))
        doorzones[a].append(pygame.Rect(g))
        doorzones[b].append(pygame.Rect(g))

    def lock_door(room, parent, oid, need, nm):
        g = gap(parent, room)
        gx, gy, gw, gh = g
        if parent[1] == room[1]:   # جنب بعض
            col_ = gx + 1 if room[0] > parent[0] else gx
            rect = (col_, gy, 1, 2)
        else:
            row_ = gy + 1 if room[1] > parent[1] else gy
            rect = (gx, row_, 2, 1)
        o = Obj(oid, S("باب {r} - مقفول", r=nm), *rect, (112, 72, 30), kind='door', need=need,
                title=S("باب {r}", r=nm), toast=S("فتحت باب {r}!", r=nm),
                locked=["الباب مقفول بقفل تقيل.", S("محتاج مفتاح {r}.", r=nm)])
        objs.append(o)
        return o

    def parent_of(c):
        for a, b in edges:
            if b == c:
                return a
            if a == c:
                return b

    dA = lock_door(A, parent_of(A), 'dA', 'ka', cell[A]['name'])
    if B:
        lock_door(B, parent_of(B), 'dB', 'kb', cell[B]['name'])

    # BFS للبعد عن البداية
    adj = {c: [] for c in cells}
    for a, b in all_edges:
        adj[a].append(b)
        adj[b].append(a)
    dist, q = {start: 0}, [start]
    for cur in q:
        for nx in adj[cur]:
            if nx not in dist:
                dist[nx] = dist[cur] + 1
                q.append(nx)
    border = [c for c in cells if c not in lockset and c != start and
              (c[0] in (0, cols - 1) or c[1] in (0, rows - 1))]
    border.sort(key=lambda c: -dist.get(c, 0))
    E = border[0]
    x0, y0 = cell[E]['x0'], cell[E]['y0']
    if E[1] == 0:
        er = (x0 + 4, y0 - 1, 2, 1)
    elif E[1] == rows - 1:
        er = (x0 + 4, y0 + RH, 2, 1)
    elif E[0] == 0:
        er = (x0 - 1, y0 + 3, 1, 2)
    else:
        er = (x0 + RW, y0 + 3, 1, 2)
    carve(*er, (58, 48, 40))
    doorzones[E].append(pygame.Rect(er))
    objs.append(Obj('exit', "باب الشقة", *er, (110, 30, 30), kind='exit', need='exit', title="باب الشقة",
                    locked=["الباب تقيل ومقفول بإحكام.", "محتاج مفتاح الشقة... ومش معاك."]))

    # أثاث
    furn = {c: [] for c in cells}
    cnt = [0]

    def place(cr, tries=60):
        v = cell[cr]
        x0, y0 = v['x0'], v['y0']
        nm, w, h, col = rng.choice(FURN)
        cands = []
        for (ww, hh) in ((w, h), (h, w)):
            if (ww, hh) == (w, h):
                for x in range(x0, x0 + RW - ww + 1):
                    cands += [(x, y0, ww, hh), (x, y0 + RH - hh, ww, hh)]
            else:
                for y in range(y0, y0 + RH - hh + 1):
                    cands += [(x0, y, ww, hh), (x0 + RW - ww, y, ww, hh)]
        rng.shuffle(cands)
        zones = [pygame.Rect(z.x - 2, z.y - 2, z.w + 4, z.h + 4) for z in doorzones[cr]]
        sp = pygame.Rect(x0 + RW // 2 - 1, y0 + RH // 2 - 1, 3, 3)
        for c in cands:
            r = pygame.Rect(c)
            if any(r.colliderect(z) for z in zones) or r.colliderect(sp):
                continue
            if any(r.inflate(2, 2).colliderect(pygame.Rect(o.rect.x // T, o.rect.y // T, o.rect.w // T, o.rect.h // T))
                   for o in furn[cr]):
                continue
            cnt[0] += 1
            o = Obj('g%d' % cnt[0], nm, c[0], c[1], c[2], c[3], col)
            o.text = rng.choice(GENERIC_FLAVOR)
            o.room = v['name']
            furn[cr].append(o)
            return o
        return None

    for cr in cells:
        for _ in range(rng.randint(3, 5)):
            place(cr)
    for lk in locks:
        while len(furn[lk]) < 2:
            if not place(lk):
                break
    if not furn[A]:
        o = place(A, 200)
    free_cells = [c for c in cells if c not in lockset]
    pool = [o for c in free_cells for o in furn[c]]
    rng.shuffle(pool)
    names_i = {'ka': S("مفتاح {r}", r=cell[A]['name']), 'exit': "مفتاح الشقة", 'small': "المفتاح الصغير"}
    if B:
        names_i['kb'] = S("مفتاح {r}", r=cell[B]['name'])

    def hint(o):
        return S("في {f} في {r}", f=o.name, r=o.room) if n < 5 else S("في {r}", r=o.room)

    def mk(o, give, need=None, finale=False):
        o.kind, o.give, o.need, o.finale = 'container', give, need, finale
        o.lines = [S("فتحت {f}...", f=o.name), S("ولقيت {k}!", k=names_i[give])]
        o.locked = [S("فيه قفل صغير على {f}.", f=o.name), "محتاج مفتاح صغير."]
        o.empty = "فاضي دلوقتي."
        if not finale and n >= 2:                     # خضّة وإنت بتاخد المفتاح
            o.scare = srng.choice(['face', 'flicker', 'flicker', 'bang', 'bang', 'dash', 'near'])

    nm_ = lv.item_names = names_i
    cE = rng.choice(furn[A]) if furn[A] else pool.pop()
    mk(cE, 'exit', finale=True)
    cKa = pool.pop()
    mk(cKa, 'ka', need='small' if n >= 4 else None)
    notes = []
    notes.append([S("المفتاح الكبير بتاع الشقة جوّه {r}.", r=cell[A]['name']), "والأوضة مقفولة، وعلى بابها قفل تقيل."])
    notes.append([S("مفتاح {r} مخبّي {h}.", r=cell[A]['name'], h=hint(cKa))])
    if n >= 4:
        if B and furn[B]:
            cS = rng.choice(furn[B])
            cKb = pool.pop()
            mk(cKb, 'kb')
            notes.append([S("مفتاح {r} {h}.", r=cell[B]['name'], h=hint(cKb))])
        else:
            cS = pool.pop()
        mk(cS, 'small')
        notes.append([S("المفتاح الصغير بتاع الدُرج... {h}.", h=hint(cS))])
    for nl in notes:
        if not pool:
            break
        o = pool.pop()
        o.kind, o.title, o.text = 'note', "ورقة مرمية", ["ورقة مكتوبة بخط مرتعش:"] + nl + (
            ["...ومكتوب في آخرها: \"{name}\""] if n >= 4 else [])
    nb = 3 + len(cells) // 3
    for o in pool[:nb]:
        o.kind, o.where = 'battery', S("جوه {f}", f=o.name)
    objs += [o for c in cells for o in furn[c]]
    for o in objs:                                # الأثاث اللي بيعمل رعب لوحده
        if o.kind == 'flavor':
            if o.name == "المراية الكبيرة":
                o.kind, o.sp = 'special', 'mirror'
            elif o.name == "الدُمية الكبيرة":
                o.kind, o.sp = 'special', 'doll'
            elif o.name == "البيانو":
                o.kind, o.sp = 'special', 'piano'
            elif o.name == "الصورة":
                o.kind, o.sp = 'special', 'portrait'
    lv.objs = objs

    # شموع
    cand_prob = max(0.3, 1 - 0.08 * n)
    lv.candles = []
    for cr in cells:
        v = cell[cr]
        if cr != start and rng.random() > cand_prob:
            continue
        corners = [(v['x0'], v['y0']), (v['x0'] + RW - 1, v['y0']),
                   (v['x0'], v['y0'] + RH - 1), (v['x0'] + RW - 1, v['y0'] + RH - 1)]
        rng.shuffle(corners)
        zones = doorzones[cr]
        for (cx_, cy_) in corners:
            r = pygame.Rect(cx_, cy_, 1, 1)
            if any(r.colliderect(pygame.Rect(o.rect.x // T, o.rect.y // T, o.rect.w // T, o.rect.h // T))
                   for o in furn[cr]):
                continue
            lv.candles.append((cx_, cy_))
            break
    # سجاد
    lv.rugs = []
    for cr in cells:
        if rng.random() < 0.6:
            v = cell[cr]
            lv.rugs.append((v['x0'] + 2, v['y0'] + 2, 5, 3, rng.choice(RUGCOL)))
    # خضّات
    others = [c for c in cells if c != start]
    rng.shuffle(others)
    cnt_t = min(len(others), 3 + n)
    kinds = (['face'] * (2 + n // 3) + ['bang'] * 3 + ['flicker'] * 3 +
             (['name'] * 2 if n >= 3 else []) + (['near'] * 2 if n >= 4 else []) +
             ['eyes'] * 2 + ['knock'] * 2 + (['dash'] * 2 if n >= 2 else []) +
             (['watch'] * 2 if n >= 3 else []))
    lv.triggers = []
    for i, cr in enumerate(others[:cnt_t]):
        v = cell[cr]
        k = rng.choice(kinds)
        if n == 5 and i == 0:
            k = 'name'
        lv.triggers.append(dict(rect=pygame.Rect((v['x0'] + 3) * T, (v['y0'] + 2) * T, 3 * T, 3 * T),
                                kind=k, fired=False))
    lv.floors = [(i, j) for j in range(lv.H) for i in range(lv.W) if lv.grid[j][i] == 0]
    sx, sy = cell[start]['x0'] + RW // 2, cell[start]['y0'] + RH // 2
    lv.start = (sx * T + 16, sy * T + 16)
    Aname = cell[A]['name']

    def goal(g):
        if 'exit' in g.inv:
            return "اهرب من باب الشقة!"
        if 'dA' in g.opened:
            return S("دوّر على مفتاح الشقة جوه {r}", r=Aname)
        if 'ka' in g.inv:
            return S("افتح باب {r}", r=Aname)
        return "اقرا الأوراق ودوّر على المفاتيح"
    lv.goal = goal
    return lv


# ================================================================= نص عربي
FONTS = {}
_cache = {}


def font_ok(f):
    try:
        return all(m is not None for m in f.metrics("\ufee3\ufefb\ufe8d\ufedf"))
    except Exception:
        return False


def load_font(size):
    for pth in (asset("font.ttf"), os.path.join(APP_DIR, "font.ttf"), os.path.join(APP_DIR, "font.otf")):
        if os.path.exists(pth):                         # الخط المرفق (IBM Plex Sans Arabic) أو أي خط حطيته جنب اللعبة
            return pygame.font.Font(pth, size)
    first = None
    for name in ("segoeui", "tahoma", "arial", "calibri", "dubai", "simplifiedarabic", "traditionalarabic",
                 "arabictypesetting", "sakkalmajalla", "notosansarabic", "notonaskharabic", "dejavusans",
                 "timesnewroman"):
        pth = pygame.font.match_font(name)
        if pth:
            f = pygame.font.Font(pth, size)
            if font_ok(f):
                return f
            first = first or f
    return first or pygame.font.Font(None, size)


def txt(text, size, color):
    text = str(text)
    key = (LANG, text, size, color)
    s = _cache.get(key)
    if s is None:
        if len(_cache) > 700:
            _cache.clear()
        f = FONTS.get(size) or FONTS.setdefault(size, load_font(size))
        shown = EN.get(text, text) if LANG == 'en' else text
        rs = arabic_reshaper.reshape(shown)
        try:
            vis = get_display(rs, base_dir='R') if (LANG == 'ar' and has_arabic(shown)) else get_display(rs)
        except TypeError:
            vis = get_display(rs)
        s = f.render(vis, True, color)
        _cache[key] = s
    return s


def txt_raw(text, size, color, lang):
    """نص بلغة ثابتة (عربي أو إنجليزي) من غير ترجمة، عشان شاشة التحكمات تعرض اللغتين مع بعض"""
    text = str(text)
    key = ('raw', lang, text, size, color)
    r = _cache.get(key)
    if r is None:
        if len(_cache) > 700:
            _cache.clear()
        f = FONTS.get(size) or FONTS.setdefault(size, load_font(size))
        if lang == 'ar':
            try:
                vis = get_display(arabic_reshaper.reshape(text), base_dir='R')
            except TypeError:
                vis = get_display(arabic_reshaper.reshape(text))
        else:
            vis = text
        r = f.render(vis, True, color)
        _cache[key] = r
    return r


def draw_raw(surf, text, size, color, x, y, align, lang):
    r = txt_raw(text, size, color, lang)
    if align == 'r':
        surf.blit(r, (x - r.get_width(), y))
    elif align == 'c':
        surf.blit(r, (x - r.get_width() // 2, y))
    else:
        surf.blit(r, (x, y))
    return r.get_height()


CREDITS_EN = "Produced by Youssef Elmelegy & Soliman Mohamed"
CREDITS_AR = "من إنتاج يوسف المليجي و سليمان محمد"
CONTROLS = [                                   # (الزرار، إنجليزي، عربي)
    ("W A S D", "Move / strafe", "حركة (قدّام وورا وجنب)"),
    ("Mouse / <  >", "Look around", "بصّ حواليك (ماوس أو الأسهم)"),
    ("Shift  /  K", "Run", "جري"),
    ("E / Space", "Interact (open, search)", "تفاعل (فتح وتقليب)"),
    ("F", "Flashlight - ghosts fear it", "الكشاف - الوحوش بتخاف منه"),
    ("Tab", "Map", "الخريطة"),
    ("F5", "Save game", "حفظ اللعبة"),
    ("T", "Chat (online)", "شات (أونلاين)"),
    ("L", "Switch language", "تغيير اللغة"),
    ("M", "Mute sound", "كتم الصوت"),
    ("-  /  +", "Volume", "مستوى الصوت"),
    ("F11", "Fullscreen", "ملء الشاشة"),
    ("V", "Switch view (3D / top-down)", "تغيير المنظور (3D / من فوق)"),
    ("Esc", "Pause menu", "قايمة اللعبة"),
]


def draw_text(surf, text, size, color, x, y, align='r'):
    s = txt(text, size, color)
    if align == 'r':
        surf.blit(s, (x - s.get_width(), y))
    elif align == 'c':
        surf.blit(s, (x - s.get_width() // 2, y))
    else:
        surf.blit(s, (x, y))
    return s.get_height()


# ================================================================= الصوت
SR = 44100
AUDIO = False
SND = {}


def _snd(samples):
    ch = pygame.mixer.get_init()[2]
    buf = array.array('h')
    for s in samples:
        v = int(max(-1.0, min(1.0, s)) * 30000)
        buf.append(v)
        if ch == 2:
            buf.append(v)
    return pygame.mixer.Sound(buffer=buf.tobytes())


def load_or_build_sounds(msg=None):
    """على الموبايل بيتخزّن الصوت أول مرة (بيتبني بالكود)، والمرات الجاية بيتحمّل في لحظة"""
    cache = os.path.join(APP_DIR, "cache", "snd_v5")
    marker = os.path.join(cache, "ok")
    if os.path.exists(marker):
        try:
            d = {}
            for fn in os.listdir(cache):
                if fn.endswith('.wav'):
                    d[fn[:-4]] = pygame.mixer.Sound(os.path.join(cache, fn))
            if 'drone' in d and 'roar' in d and 'chant' in d:
                return d
        except Exception:
            pass
    if msg:
        msg("جاري تجهيز الأصوات... (أول مرة بس)")
    d = build_sounds()
    if True:
        try:
            os.makedirs(cache, exist_ok=True)
            fmt = pygame.mixer.get_init()
            for k, snd in d.items():
                with wave.open(os.path.join(cache, k + ".wav"), 'wb') as w:
                    w.setnchannels(fmt[2])
                    w.setsampwidth(2)
                    w.setframerate(fmt[0])
                    w.writeframes(snd.get_raw())
            with open(marker, 'w') as f:
                f.write('ok')
        except Exception as ex:
            print("مقدرتش أخزّن الأصوات:", ex)
    return d


def build_sounds():
    rnd = random.random
    tp = 2 * math.pi
    S = {}
    out, ph, ph2 = [], 0.0, 0.0
    for i in range(int(SR * 1.5)):
        t = i / SR
        env = math.exp(-t * 2.0) if t > 0.01 else t / 0.01
        f = 1400 - 900 * t
        ph += tp * f / SR
        ph2 += tp * f * 1.41 / SR
        out.append(env * (0.45 * (rnd() * 2 - 1) + 0.3 * math.sin(ph) +
                          0.25 * math.sin(ph2) * (1 if int(t * 40) % 2 else -0.6)))
    S['scare'] = _snd(out)
    S['bang'] = _snd([math.exp(-i / SR * 8) * (0.8 * (rnd() * 2 - 1) + 0.8 * math.sin(tp * 55 * i / SR))
                      for i in range(int(SR * 0.7))])

    def thump(x):
        return math.sin(tp * 50 * x) * math.exp(-x * 16) if x >= 0 else 0.0
    S['heart'] = _snd([thump(i / SR) + 0.7 * thump(i / SR - 0.22) for i in range(int(SR * 0.8))])
    S['drone'] = _snd([(0.5 * math.sin(tp * 55 * i / SR) + 0.3 * math.sin(tp * 58 * i / SR) +
                        0.2 * math.sin(tp * 82.5 * i / SR)) * (0.7 + 0.3 * math.sin(tp * 0.5 * i / SR)) * 0.35
                       for i in range(SR * 4)])
    out, y = [], 0.0
    for i in range(int(SR * 1.8)):
        t = i / SR
        y = y * 0.85 + (rnd() * 2 - 1) * 0.15
        out.append(y * math.sin(math.pi * t / 1.8) ** 2 * (0.6 + 0.4 * math.sin(tp * 7 * t)) * 3)
    S['whisper'] = _snd(out)
    out, ph = [], 0.0
    for i in range(SR):
        t = i / SR
        ph += tp * (120 + 40 * math.sin(tp * 5 * t) + 60 * t) / SR
        out.append(((ph / tp) % 1 * 2 - 1) * 0.25 * math.sin(math.pi * t) + (rnd() - .5) * 0.04)
    S['creak'] = _snd(out)
    out, y = [], 0.0
    for i in range(int(SR * 0.18)):
        y = y * 0.8 + (rnd() * 2 - 1) * 0.2
        out.append(y * math.exp(-i / SR * 28) * 2.2)
    S['step'] = _snd(out)
    out = []
    for i in range(int(SR * 0.2)):
        t = i / SR
        out.append(0.3 * math.sin(tp * (660 if t < 0.1 else 880) * t) * math.exp(-(t % 0.1) * 20))
    S['pickup'] = _snd(out)
    for nm, f0 in (('foot1', 105), ('foot2', 88)):          # خطوات ناعمة وواطية
        out, y = [], 0.0
        for i in range(int(SR * 0.14)):
            t = i / SR
            y = y * 0.92 + (rnd() * 2 - 1) * 0.08
            out.append((0.8 * math.sin(tp * f0 * t) + 0.35 * y) * math.exp(-t * 34) * (1 if t > 0.004 else t / 0.004))
        S[nm] = _snd(out)
    S['unlock'] = _snd([(0.6 * (rnd() * 2 - 1) if i < SR * 0.04 else 0.4 * math.sin(tp * 300 * i / SR)) *
                        math.exp(-i / SR * 14) for i in range(int(SR * 0.3))])

    # ---------- أصوات رعب إضافية ----------
    out, y = [], 0.0                                        # خبط على الحيطة
    for i in range(int(SR * 1.0)):
        t = i / SR
        y = y * 0.9 + (rnd() * 2 - 1) * 0.1
        v = 0.0
        for h in (0.0, 0.3, 0.62):
            if t >= h:
                v += math.exp(-(t - h) * 36) * (0.9 * math.sin(tp * 95 * (t - h)) + 3.2 * y)
        out.append(v)
    S['knock'] = _snd(out)
    out, y = [], 0.0                                        # باب بيتقفل بقوة
    for i in range(int(SR * 1.0)):
        t = i / SR
        y = y * 0.86 + (rnd() * 2 - 1) * 0.14
        v = math.exp(-t * 6) * (5.0 * y + 0.9 * math.sin(tp * 42 * t))
        if t > 0.17:
            v += 0.45 * math.exp(-(t - 0.17) * 9) * (4.0 * y + 0.8 * math.sin(tp * 60 * t))
        out.append(v)
    S['slam'] = _snd(out)
    out, ph = [], 0.0                                       # عياط طفل بعيد
    for i in range(int(SR * 2.0)):
        t = i / SR
        f = 380 + 150 * math.sin(math.pi * t / 2.0) + 14 * math.sin(tp * 5.5 * t) - 40 * t
        ph += tp * f / SR
        env = math.sin(math.pi * t / 2.0) ** 0.8 * (0.75 + 0.25 * math.sin(tp * 4.5 * t))
        v = math.sin(ph) + 0.55 * math.sin(2 * ph + 0.6) + 0.35 * math.sin(3 * ph + 1.2) + 0.2 * math.sin(4 * ph)
        out.append(env * (0.28 * v + (rnd() - 0.5) * 0.05))
    S['cry'] = _snd(out)
    out = [0.0] * int(SR * 1.3)                             # ضحكة طفل
    for k, t0 in enumerate((0.0, 0.2, 0.4, 0.6, 0.86)):
        f0, dur, ph = 600 - k * 35, 0.13, 0.0
        for j in range(int(SR * dur)):
            t = j / SR
            ph += tp * (f0 - 160 * t / dur) / SR
            env = math.sin(math.pi * t / dur) ** 1.5
            v = env * (0.4 * math.sin(ph) + 0.22 * math.sin(2 * ph + 1) + 0.12 * math.sin(3 * ph))
            idx = int(SR * t0) + j
            out[idx] += v
            out[idx + int(SR * 0.11)] += v * 0.35
    S['laugh'] = _snd(out)
    out, y = [], 0.0                                        # نفس تقيل ورا رقبتك
    for i in range(int(SR * 1.8)):
        t = i / SR
        y = y * 0.78 + (rnd() * 2 - 1) * 0.22
        env = (math.sin(math.pi * t / 0.8) ** 2 if t < 0.8 else 0.0) + \
              (0.8 * math.sin(math.pi * (t - 0.9) / 0.8) ** 2 if 0.9 <= t < 1.7 else 0.0)
        out.append(y * env * 2.6)
    S['breath'] = _snd(out)
    out, ph = [], 0.0                                       # صرخة حادة
    for i in range(int(SR * 1.3)):
        t = i / SR
        f = 800 + 1700 * (t / 1.3) ** 1.5
        ph += tp * (f + 140 * math.sin(tp * 31 * t)) / SR
        env = (t / 0.01 if t < 0.01 else 1.0) * math.exp(-t * 1.6)
        out.append(env * (0.6 * math.tanh(2.6 * math.sin(ph)) + 0.35 * (rnd() * 2 - 1)))
    S['shriek'] = _snd(out)
    S['static'] = _snd([(rnd() * 2 - 1) * 0.8 * (1.0 if int(i / SR * 70) % 3 else 0.25) * math.exp(-i / SR * 4)
                        for i in range(int(SR * 0.5))])
    notes = (659.3, 784.0, 987.8, 784.0, 880.0, 659.3, 587.3)   # علبة موسيقى لحنها مش مظبوط
    out = [0.0] * int(SR * (0.4 * len(notes) + 0.9))
    for k, f in enumerate(notes):
        f *= 1 - 0.012 * k * (k > 3)                            # النغمات بتنزل شوية شوية
        st = int(SR * 0.4 * k)
        for j in range(int(SR * 0.9)):
            t = j / SR
            out[st + j] += math.exp(-t * 5.5) * 0.28 * (math.sin(tp * f * t) + 0.4 * math.sin(tp * f * 2.76 * t) +
                                                        0.2 * math.sin(tp * f * 5.4 * t))
    S['musicbox'] = _snd(out)
    out, y = [], 0.0                                        # شمعة بتطفي
    for i in range(int(SR * 0.45)):
        t = i / SR
        n_ = rnd() * 2 - 1
        y = y * 0.6 + n_ * 0.4
        out.append((n_ - y) * math.exp(-t * 9) * 1.1 * (t / 0.02 if t < 0.02 else 1.0))
    S['snuff'] = _snd(out)
    build_extra_sounds(S)
    build_extra_sounds2(S)
    return S


def build_extra_sounds(S):
    """أصوات رعب إضافية: زئير، زمجرة، صرخة، سلاسل، جرّ، خربشة، جرس، ريح، نقطة مياه، إزاز، راديو، ضحكة، كورال..."""
    rnd = random.random
    tp = 2 * math.pi

    out, ph, y = [], 0.0, 0.0                               # زمجرة وحش
    for i in range(int(SR * 1.6)):
        t = i / SR
        ph += tp * (62 + 16 * math.sin(tp * 2.5 * t) + 8 * math.sin(tp * 0.7 * t)) / SR
        saw = (ph / tp) % 1 * 2 - 1
        y = y * 0.88 + (rnd() * 2 - 1) * 0.12
        env = math.sin(math.pi * t / 1.6) ** 0.7
        out.append(env * (0.6 + 0.4 * math.sin(tp * 27 * t)) * math.tanh(1.8 * saw + 5 * y) * 0.75)
    S['growl'] = _snd(out)

    out, ph, y = [], 0.0, 0.0                               # زئير
    for i in range(int(SR * 1.9)):
        t = i / SR
        f = 80 + 150 * math.sin(math.pi * min(1.0, t / 1.2)) ** 1.3 - 20 * t + 12 * math.sin(tp * 9 * t)
        ph += tp * f / SR
        y = y * 0.7 + (rnd() * 2 - 1) * 0.3
        env = (t / 0.05 if t < 0.05 else 1.0) * math.exp(-max(0.0, t - 0.9) * 1.8)
        v = math.sin(ph) + 0.6 * math.sin(2 * ph + 0.4) + 0.5 * math.sin(3 * ph) + 0.35 * math.sin(5 * ph)
        out.append(env * math.tanh(1.2 * v + 2.0 * y) * 0.7)
    S['roar'] = _snd(out)

    out, ph, ph2 = [], 0.0, 0.0                             # صرخة ست
    for i in range(int(SR * 1.7)):
        t = i / SR
        f = 1100 + 700 * min(1.0, t / 0.25) - 400 * (t / 1.7) ** 2 + 45 * math.sin(tp * 8 * t)
        ph += tp * f / SR
        ph2 += tp * f * 1.012 / SR
        env = (t / 0.015 if t < 0.015 else 1.0) * math.exp(-t * 0.9) * (1.0 if t < 1.5 else (1.7 - t) / 0.2)
        v = math.sin(ph) + 0.5 * math.sin(2 * ph) + 0.7 * math.sin(ph2) + 0.25 * math.sin(3 * ph)
        out.append(env * (0.5 * math.tanh(2.2 * v) + (rnd() - 0.5) * 0.12))
    S['scream'] = _snd(out)

    n = int(SR * 1.6)                                       # سلاسل بتتجرّ
    out = [0.0] * n
    for t0 in (0.0, 0.11, 0.26, 0.31, 0.52, 0.6, 0.83, 0.97, 1.12):
        st, base = int(SR * t0), random.choice((1800, 2300, 2900, 3600))
        for j in range(int(SR * 0.28)):
            if st + j >= n:
                break
            t = j / SR
            out[st + j] += math.exp(-t * 30) * 0.3 * (math.sin(tp * base * t) + 0.6 * math.sin(tp * base * 1.47 * t) +
                                                        0.4 * math.sin(tp * base * 2.09 * t)) + (rnd() * 2 - 1) * 0.05 * math.exp(-t * 80)
    S['chains'] = _snd(out)

    out, y = [], 0.0                                        # حاجة تقيلة بتتسحب على الأرض
    for i in range(int(SR * 2.2)):
        t = i / SR
        y = y * 0.93 + (rnd() * 2 - 1) * 0.07
        env = math.sin(math.pi * t / 2.2) ** 1.2 * (0.55 + 0.45 * abs(math.sin(tp * 1.7 * t)))
        out.append(env * (y * 2.3 + 0.25 * math.sin(tp * 48 * t) * (0.5 + 0.5 * math.sin(tp * 3.4 * t))))
    S['dragging'] = _snd(out)

    out, y = [], 0.0                                        # ضوافر بتخربش الخشب
    for i in range(int(SR * 1.3)):
        t = i / SR
        nz = rnd() * 2 - 1
        y = y * 0.5 + nz * 0.5
        cyc = (t * 7) % 1
        env = (math.sin(math.pi * cyc / 0.55) if cyc < 0.55 else 0.0) * math.sin(math.pi * t / 1.3)
        out.append((nz - y) * env * 1.0)
    S['scratch'] = _snd(out)

    n = int(SR * 3.6)                                       # جرس كنيسة مش مظبوط
    out = [0.0] * n
    for t0, vol in ((0.0, 1.0), (1.5, 0.8)):
        st = int(SR * t0)
        for ratio, amp, dec in ((1.0, 1.0, 1.1), (2.0, 0.6, 1.5), (2.76, 0.5, 1.8), (5.4, 0.3, 2.6), (8.93, 0.15, 3.6)):
            f = 196 * ratio
            for j in range(int(SR * min(2.0, 4.5 / dec))):
                if st + j >= n:
                    break
                t = j / SR
                out[st + j] += vol * amp * 0.2 * math.exp(-t * dec) * math.sin(tp * f * t)
    S['bell'] = _snd(out)

    out, y, ph = [], 0.0, 0.0                               # ريح بتعوي
    for i in range(int(SR * 3.4)):
        t = i / SR
        y += (rnd() * 2 - 1 - y) * (0.04 + 0.05 * (0.5 + 0.5 * math.sin(tp * 0.4 * t)))
        ph += tp * (520 + 160 * math.sin(tp * 0.5 * t + 1) + 40 * math.sin(tp * 3 * t)) / SR
        env = math.sin(math.pi * t / 3.4) ** 1.3
        out.append(env * (y * 3.4 + 0.06 * math.sin(ph) * (0.5 + 0.5 * math.sin(tp * 0.7 * t))))
    S['wind'] = _snd(out)

    n = int(SR * 0.9)                                       # نقطة مياه في مكان فاضي
    out = [0.0] * n
    for t0, vol in ((0.0, 1.0), (0.42, 0.45)):
        st = int(SR * t0)
        for j in range(int(SR * 0.12)):
            t = j / SR
            out[st + j] += vol * 0.5 * math.exp(-t * 38) * math.sin(tp * (700 * t + 1500 * t * t))
    S['drip'] = _snd(out)

    n = int(SR * 1.0)                                       # إزاز بيتكسر
    out = [0.0] * n
    for i in range(int(SR * 0.12)):
        out[i] += (rnd() * 2 - 1) * math.exp(-i / SR * 40) * 0.9
    for _k in range(14):
        st, f = int(SR * random.uniform(0.03, 0.6)), random.uniform(2500, 6500)
        for j in range(int(SR * 0.2)):
            if st + j >= n:
                break
            t = j / SR
            out[st + j] += 0.16 * math.exp(-t * 28) * math.sin(tp * f * t)
    S['glass'] = _snd(out)

    out, y, ph = [], 0.0, 0.0                               # راديو بيتكلم لوحده
    for i in range(int(SR * 1.8)):
        t = i / SR
        y = y * 0.6 + (rnd() * 2 - 1) * 0.4
        seg = int(t * 9)
        ph += tp * (180 + 90 * ((seg * 37) % 7) / 7 + 40 * math.sin(tp * 6 * t)) / SR
        voice = (math.sin(ph) + 0.5 * math.sin(2 * ph) + 0.3 * math.sin(3 * ph)) * 0.18 if seg % 3 else 0.0
        out.append((voice * (0.6 + 0.4 * math.sin(tp * 13 * t)) + y * 0.35) * (0.4 + 0.6 * math.sin(math.pi * t / 1.8)))
    S['radio'] = _snd(out)

    n = int(SR * 1.8)                                       # ضحكة واطية بطيئة
    out = [0.0] * n
    for k, t0 in enumerate((0.0, 0.28, 0.56, 0.84, 1.2)):
        f0, dur, ph = 330 - k * 25, 0.2, 0.0
        for j in range(int(SR * dur)):
            t = j / SR
            ph += tp * (f0 - 90 * t / dur + 12 * math.sin(tp * 30 * t)) / SR
            env = math.sin(math.pi * t / dur) ** 1.2
            out[int(SR * t0) + j] += env * (0.4 * math.sin(ph) + 0.25 * math.sin(2 * ph + 1) + 0.15 * math.sin(3 * ph) +
                                            (rnd() - 0.5) * 0.08)
    S['giggle'] = _snd(out)

    n = int(SR * 2.8)                                       # كورال أصوات نشاز
    out = [0.0] * n
    for f in (196.0, 207.7, 293.7, 415.3):
        ph = random.random() * tp
        for i in range(n):
            t = i / SR
            ph += tp * f * (1 + 0.006 * math.sin(tp * (4.5 + f % 5) * t)) / SR
            out[i] += math.sin(math.pi * t / 2.8) ** 1.5 * 0.1 * (math.sin(ph) + 0.45 * math.sin(2 * ph) + 0.25 * math.sin(3 * ph))
    S['choir'] = _snd(out)

    out, y = [], 0.0                                        # فحيح
    for i in range(int(SR * 1.1)):
        t = i / SR
        nz = rnd() * 2 - 1
        y = y * 0.4 + nz * 0.6
        out.append((nz - y * 0.9) * math.sin(math.pi * t / 1.1) ** 0.8 * 0.9)
    S['hiss'] = _snd(out)

    out, y, y2 = [], 0.0, 0.0                               # رعد
    for i in range(int(SR * 2.8)):
        t = i / SR
        nz = rnd() * 2 - 1
        y += (nz - y) * 0.03
        y2 += (y - y2) * 0.05
        env = (1.0 if t < 0.03 else math.exp(-(t - 0.03) * 1.3)) * (0.7 + 0.3 * math.sin(tp * 7 * t))
        out.append(env * y2 * 15 + math.exp(-t * 30) * nz * 0.7)
    S['thunder'] = _snd(out)

    out, ph = [], 0.0                                       # أنين شبح
    for i in range(int(SR * 2.2)):
        t = i / SR
        ph += tp * (150 - 35 * (t / 2.2) + 6 * math.sin(tp * 5 * t)) / SR
        v = math.sin(ph) + 0.8 * math.sin(2 * ph) + 0.9 * math.sin(3 * ph + 0.3) + 0.5 * math.sin(5 * ph)
        out.append(math.sin(math.pi * t / 2.2) ** 1.4 * 0.22 * v + (rnd() - 0.5) * 0.03)
    S['moan'] = _snd(out)

    n = int(SR * 0.9)                                       # عضم بيتكسّر
    out, y = [0.0] * n, 0.0
    for t0 in (0.0, 0.13, 0.2, 0.41, 0.5, 0.66):
        st = int(SR * t0)
        for j in range(int(SR * 0.1)):
            t = j / SR
            y = y * 0.7 + (rnd() * 2 - 1) * 0.3
            out[st + j] += math.exp(-t * 45) * (y * 1.2 + 0.5 * math.sin(tp * 130 * t))
    S['crunch'] = _snd(out)


def build_extra_sounds2(S):
    """دفعة تانية من أصوات الرعب: بكا طفل، دبّان، جري، خبطات، صفير، تليفون، مقبض باب، ساعة، أرجوحة، عواء، غراب، ترتيل، ضربة رعب، حشرجة، همس معكوس"""
    rnd = random.random
    tp = 2 * math.pi

    n = int(SR * 2.1)                                       # بكا طفل
    out = [0.0] * n
    for t0, dur, f0 in ((0.0, 0.8, 520), (0.95, 0.75, 480), (1.8, 0.3, 430)):
        ph = 0.0
        for j in range(int(SR * dur)):
            t = j / SR
            ph += tp * (f0 + 150 * math.sin(math.pi * t / dur) + 14 * math.sin(tp * 9 * t)) / SR
            env = min(1.0, t / 0.04) * math.sin(math.pi * t / dur) ** 0.6
            out[int(SR * t0) + j] += env * 0.45 * math.tanh(1.3 * (math.sin(ph) + 0.6 * math.sin(2 * ph) +
                                                                  0.45 * math.sin(3 * ph) + (rnd() - 0.5) * 0.25))
    S['baby'] = _snd(out)

    out, y = [], 0.0                                        # سرب دبّان
    for i in range(int(SR * 2.5)):
        t = i / SR
        y = y * 0.8 + (rnd() * 2 - 1) * 0.2
        am = 0.5 + 0.5 * math.sin(tp * 7 * t) * math.sin(tp * 3.1 * t + 1)
        buzz = math.sin(tp * (190 + 25 * math.sin(tp * 11 * t)) * t) + 0.5 * math.sin(tp * 380 * t)
        out.append(math.sin(math.pi * t / 2.5) ** 0.6 * am * (0.22 * buzz + 0.5 * y))
    S['flies'] = _snd(out)

    n = int(SR * 1.6)                                       # جري سريع
    out = [0.0] * n
    for k in range(8):
        st = int(SR * (0.02 + k * 0.18))
        y = 0.0
        for j in range(int(SR * 0.12)):
            if st + j >= n:
                break
            t = j / SR
            y = y * 0.6 + (rnd() * 2 - 1) * 0.4
            out[st + j] += math.exp(-t * 38) * (0.6 * math.sin(tp * 85 * t) + 0.5 * y) * (0.7 + 0.04 * k)
    S['run'] = _snd(out)

    n = int(SR * 1.5)                                       # تلات خبطات تقيلة
    out = [0.0] * n
    for t0 in (0.0, 0.55, 1.1):
        st, y = int(SR * t0), 0.0
        for j in range(int(SR * 0.32)):
            t = j / SR
            y = y * 0.7 + (rnd() * 2 - 1) * 0.3
            out[st + j] += math.exp(-t * 13) * (0.9 * math.sin(tp * 105 * t) + 0.4 * math.sin(tp * 210 * t)) + math.exp(-t * 90) * y * 0.8
    S['knock3'] = _snd(out)

    out, ph = [], 0.0                                       # صفير مرعب بلحن بطيء
    notes = [880, 831, 740, 831, 659, 698, 740, 622]
    for i in range(int(SR * 2.6)):
        t = i / SR
        k = min(len(notes) - 1, int(t / 0.32))
        ph += tp * (notes[k] * 0.5 + 6 * math.sin(tp * 5.5 * t)) / SR
        c = (t % 0.32) / 0.32
        env = math.sin(math.pi * c) ** 0.5 * min(1.0, (2.6 - t) / 0.3)
        out.append(env * 0.35 * (math.sin(ph) + 0.12 * math.sin(2 * ph)) + (rnd() - 0.5) * 0.02 * env)
    S['whistle'] = _snd(out)

    n = int(SR * 2.4)                                       # تليفون قديم بيرن
    out = [0.0] * n
    for t0 in (0.0, 1.2):
        st = int(SR * t0)
        for j in range(int(SR * 0.8)):
            t = j / SR
            gate = 1.0 if (t * 22) % 1 < 0.55 else 0.0
            out[st + j] += gate * 0.3 * (math.sin(tp * 440 * t) + math.sin(tp * 480 * t)) * min(1.0, (0.8 - t) / 0.03)
    S['phone'] = _snd(out)

    n = int(SR * 1.3)                                       # حد بيهز مقبض الباب
    out = [0.0] * n
    for t0 in (0.0, 0.09, 0.21, 0.3, 0.52, 0.6, 0.83, 0.9):
        st, f = int(SR * t0), random.uniform(500, 1500)
        for j in range(int(SR * 0.16)):
            if st + j >= n:
                break
            t = j / SR
            out[st + j] += math.exp(-t * 36) * 0.35 * (math.sin(tp * f * t) + 0.7 * math.sin(tp * f * 1.62 * t) + (rnd() - 0.5) * 0.6)
    S['doorknob'] = _snd(out)

    n = int(SR * 3.2)                                       # ساعة: تك تك ودقّة تقيلة
    out = [0.0] * n
    for k in range(5):
        st, f = int(SR * (0.1 + k * 0.45)), (1500 if k % 2 == 0 else 1100)
        for j in range(int(SR * 0.05)):
            t = j / SR
            out[st + j] += math.exp(-t * 90) * 0.5 * math.sin(tp * f * t)
    st = int(SR * 2.4)
    for j in range(int(SR * 0.8)):
        t = j / SR
        out[st + j] += math.exp(-t * 3.5) * 0.4 * (math.sin(tp * 130 * t) + 0.5 * math.sin(tp * 262 * t + 1))
    S['clock'] = _snd(out)

    out, ph = [], 0.0                                       # أرجوحة بتزيّ لوحدها
    for i in range(int(SR * 2.6)):
        t = i / SR
        c = (t % 1.3) / 1.3
        ph += tp * (780 + 380 * math.sin(math.pi * c) + 30 * math.sin(tp * 40 * t)) / SR
        env = math.sin(math.pi * c) ** 1.4 * min(1.0, (2.6 - t) / 0.2)
        out.append(env * 0.3 * math.tanh(2.0 * (math.sin(ph) + 0.5 * math.sin(2 * ph) + 0.3 * math.sin(5 * ph))))
    S['swing'] = _snd(out)

    out, ph = [], 0.0                                       # عواء ديب بعيد
    for i in range(int(SR * 3.0)):
        t = i / SR
        f = 300 + 400 * math.sin(math.pi * min(1.0, t / 2.2)) ** 1.2 - 60 * max(0.0, t - 2.0) + 8 * math.sin(tp * 5.5 * t)
        ph += tp * f / SR
        env = min(1.0, t / 0.4) * min(1.0, (3.0 - t) / 0.6)
        out.append(env * 0.38 * (math.sin(ph) + 0.4 * math.sin(2 * ph) + 0.2 * math.sin(3 * ph)) + (rnd() - 0.5) * 0.03 * env)
    S['howl'] = _snd(out)

    n = int(SR * 1.3)                                       # غراب
    out = [0.0] * n
    for t0 in (0.0, 0.4, 0.8):
        ph = 0.0
        for j in range(int(SR * 0.24)):
            t = j / SR
            ph += tp * (520 - 220 * t / 0.24) / SR
            saw = (ph / tp) % 1 * 2 - 1
            out[int(SR * t0) + j] += math.sin(math.pi * t / 0.24) ** 0.5 * 0.45 * math.tanh(2.0 * saw + (rnd() - 0.5) * 0.9)
    S['crow'] = _snd(out)

    n = int(SR * 3.2)                                       # ترتيل واطي مخيف
    out = [0.0] * n
    for f in (98.0, 98.0 * 1.5, 147.0 * 1.06):
        ph = random.random() * tp
        for i in range(n):
            t = i / SR
            ph += tp * f * (1 + 0.004 * math.sin(tp * 4.2 * t)) / SR
            vow = 0.6 + 0.4 * math.sin(tp * 0.8 * t + f)
            out[i] += math.sin(math.pi * t / 3.2) ** 1.2 * 0.14 * (math.sin(ph) + 0.8 * vow * math.sin(3 * ph) + 0.5 * math.sin(5 * ph))
    S['chant'] = _snd(out)

    out, ph = [], 0.0                                       # ضربة رعب (stinger)
    for i in range(int(SR * 1.7)):
        t = i / SR
        ph += tp * (48 - 14 * min(1.0, t / 0.5)) / SR
        cluster = (math.sin(tp * 233 * t) + math.sin(tp * 247 * t) + math.sin(tp * 261 * t)) * math.exp(-t * 3.0) * 0.12
        out.append(math.tanh(1.8 * math.exp(-t * 2.4) * math.sin(ph)) * 0.9 + cluster + (rnd() * 2 - 1) * math.exp(-t * 45) * 0.7)
    S['boom'] = _snd(out)

    out, y, ph = [], 0.0, 0.0                               # حشرجة
    for i in range(int(SR * 1.9)):
        t = i / SR
        y += (rnd() * 2 - 1 - y) * 0.1
        ph += tp * (70 + 15 * math.sin(tp * 3 * t)) / SR
        flutter = 0.5 + 0.5 * math.sin(tp * 18 * t) * math.sin(tp * 1.3 * t + 2)
        out.append(math.sin(math.pi * t / 1.9) ** 1.1 * (flutter * (y * 3.0 + 0.25 * math.sin(ph))))
    S['rattle'] = _snd(out)

    out, y = [], 0.0                                        # همس معكوس
    for i in range(int(SR * 2.2)):
        t = i / SR
        nz = rnd() * 2 - 1
        y = y * 0.62 + nz * 0.38
        cyc = (t * 2.3) % 1
        env = (cyc / 0.8) ** 2 if cyc < 0.8 else 0.0
        out.append((y * 1.6 + 0.1 * math.sin(tp * (300 + 60 * math.sin(tp * 4 * t)) * t)) * env * 0.7)
    S['revwhisper'] = _snd(out)


MASTER = 1.0
SETTINGS_FILE = os.path.join(APP_DIR, "settings.json")


def save_settings():
    try:
        with open(SETTINGS_FILE, 'w', encoding='utf-8') as f:
            json.dump(dict(lang=LANG, volume=MASTER, server=SERVER_ADDR), f)
    except Exception:
        pass


def load_settings():
    global LANG, MASTER, SERVER_ADDR
    try:
        with open(SETTINGS_FILE, encoding='utf-8') as f:
            d = json.load(f)
        SERVER_ADDR = str(d.get('server', DEFAULT_SERVER) or DEFAULT_SERVER)[:60]
        LANG = d.get('lang', 'ar') if d.get('lang') in ('ar', 'en') else 'ar'
        MASTER = max(0.0, min(1.0, float(d.get('volume', 1.0))))
    except Exception:
        pass


def set_lang(l):
    global LANG
    LANG = l
    save_settings()


def set_server(v):
    global SERVER_ADDR
    SERVER_ADDR = (v or '').strip()[:60]
    save_settings()


def lan_ip():
    try:
        k = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        k.connect(("8.8.8.8", 80))
        ip = k.getsockname()[0]
        k.close()
        return ip
    except Exception:
        try:
            return socket.gethostbyname(socket.gethostname())
        except Exception:
            return "IP-جهازك"


def apply_volume():
    if AUDIO and 'drone' in SND:
        SND['drone'].set_volume(0.5 * MASTER)


def change_volume(delta=None, mute=False):
    global MASTER
    if mute:
        MASTER = 0.0 if MASTER > 0 else 1.0
    else:
        MASTER = max(0.0, min(1.0, round(MASTER + delta, 2)))
    apply_volume()
    save_settings()


def play(name, vol=1.0):
    if AUDIO and name in SND:
        SND[name].set_volume(max(0.0, min(1.0, vol * MASTER)))
        SND[name].play()


# ---------------- صوت الشبح وهو بينادي اسمك ----------------
_AR2L = dict(zip("ابتثجحخدذرزسشصضطظعغفقكلمنهةىءؤئأإآ",
                 ["a", "b", "t", "th", "j", "h", "kh", "d", "z", "r", "z", "s", "sh", "s", "d", "t", "z", "a",
                  "gh", "f", "k", "k", "l", "m", "n", "h", "a", "a", "", "o", "e", "a", "i", "aa"]))
_VOWELS = set("aeiou")


def has_arabic(t):
    return any('\u0600' <= c <= '\u06ff' for c in t)


def translit(name):
    """تحويل تقريبي للاسم العربي لحروف إنجليزي (لو مفيش صوت عربي في الجهاز)"""
    out = []
    for i, c in enumerate(name):
        if c == 'و':
            piece = 'oo' if (out and out[-1][-1:] not in _VOWELS) else 'w'
        elif c == 'ي':
            piece = 'ee' if (out and out[-1][-1:] not in _VOWELS) else 'y'
        else:
            piece = _AR2L.get(c, c if c.isascii() else "")
        if out and piece and out[-1][-1:] not in _VOWELS and piece[0] not in _VOWELS:
            out.append('a')
        if piece:
            out.append(piece)
    return ''.join(out) or name


def android_tts_to_wav(name, out):
    """نطق الاسم بمحرّك أندرويد (Google TTS) عن طريق pyjnius. لو مفيش صوت: الوحش هيهمس بس"""
    try:
        import time
        from jnius import autoclass, PythonJavaClass, java_method
        PythonActivity = autoclass('org.kivy.android.PythonActivity')
        TextToSpeech = autoclass('android.speech.tts.TextToSpeech')
        Locale = autoclass('java.util.Locale')
        File = autoclass('java.io.File')
        Bundle = autoclass('android.os.Bundle')
        state = {'ok': None}

        class InitListener(PythonJavaClass):
            __javainterfaces__ = ['android/speech/tts/TextToSpeech$OnInitListener']
            __javacontext__ = 'app'

            @java_method('(I)V')
            def onInit(self, status):
                state['ok'] = (status == 0)

        lst = InitListener()
        tts = TextToSpeech(PythonActivity.mActivity, lst)
        t0 = time.time()
        while state['ok'] is None and time.time() - t0 < 10:
            time.sleep(0.05)
        if not state['ok']:
            return False
        use_ar = tts.setLanguage(Locale('ar')) >= 0
        if not use_ar:
            tts.setLanguage(Locale.ENGLISH)
        tts.setSpeechRate(0.7)
        nm = name if (use_ar or not has_arabic(name)) else translit(name)
        if os.path.exists(out):
            os.remove(out)
        tts.synthesizeToFile("%s،  %s" % (nm, nm), Bundle(), File(out), "hh")
        last, t0 = -1, time.time()
        while time.time() - t0 < 20:                    # بنستنى الملف يتكتب ويثبت
            time.sleep(0.4)
            sz = os.path.getsize(out) if os.path.exists(out) else 0
            if sz > 1000 and sz == last:
                break
            last = sz
        tts.shutdown()
        return os.path.exists(out) and os.path.getsize(out) > 1000
    except Exception as ex:
        print("نطق أندرويد مش شغال:", ex)
        return False


import threading as _th
TTS_LOCK = _th.Lock()


def tts_to_wav(name, out):
    with TTS_LOCK:
        if os.path.exists(out) and os.path.getsize(out) > 1000:
            return True
        return _tts_to_wav_raw(name, out)


def _tts_to_wav_raw(name, out):
    """بيطلّع ملف wav فيه الاسم منطوق بصوت الجهاز (pyttsx3 أو PowerShell على ويندوز أو محرّك أندرويد)"""
    if ANDROID:
        return android_tts_to_wav(name, out)
    latin = translit(name) if has_arabic(name) else name
    phrase = lambda n: "%s،  %s" % (n, n)
    try:
        import pyttsx3
        eng = pyttsx3.init()
        chosen = None
        for v in eng.getProperty('voices'):
            info = (str(v.id) + ' ' + str(v.name) + ' ' + str(getattr(v, 'languages', ''))).lower()
            if any(k in info for k in ('arabic', 'hoda', 'naayf', 'areg', 'arsa', 'maged', 'majed', 'tarik', 'ar-', 'ar_')):
                chosen = v
                break
        if chosen:
            eng.setProperty('voice', chosen.id)
        eng.setProperty('rate', 105)
        eng.save_to_file(phrase(name if (chosen or not has_arabic(name)) else latin), out)
        eng.runAndWait()
        eng.stop()
        if os.path.exists(out) and os.path.getsize(out) > 1000:
            return True
    except Exception:
        pass
    if sys.platform.startswith('win'):
        ps = ("Add-Type -AssemblyName System.Speech;"
              "$s=New-Object System.Speech.Synthesis.SpeechSynthesizer;"
              "$v=$s.GetInstalledVoices()|?{$_.VoiceInfo.Culture.Name -like 'ar*'}|select -First 1;"
              "if($v){$s.SelectVoice($v.VoiceInfo.Name);$t=$env:GN_TEXT}else{$t=$env:GN_LATIN};"
              "$s.Rate=-4;$s.SetOutputToWaveFile($env:GN_OUT);$s.Speak($t);$s.Dispose()")
        env = dict(os.environ, GN_TEXT=phrase(name), GN_LATIN=phrase(latin), GN_OUT=out)
        try:
            subprocess.run(["powershell", "-NoProfile", "-Command", ps], env=env, timeout=40,
                           creationflags=0x08000000, capture_output=True)
        except Exception:
            pass
        if os.path.exists(out) and os.path.getsize(out) > 1000:
            return True
    return False


def scary_voice(path):
    """بيحوّل الصوت لصوت شيطاني: أوطى + تشويه + صدى + همس"""
    tp = 2 * math.pi
    with wave.open(path) as w:
        ch, sw, fr = w.getnchannels(), w.getsampwidth(), w.getframerate()
        raw = w.readframes(w.getnframes())
    if sw != 2:
        return None
    a = array.array('h')
    a.frombytes(raw)
    mono = [sum(a[i:i + ch]) / (ch * 32768.0) for i in range(0, len(a) - ch + 1, ch)]
    pk = max((abs(v) for v in mono), default=0)
    if pk < 0.01:
        return None
    idx = [i for i, v in enumerate(mono) if abs(v) > pk * 0.04]
    mono = mono[idx[0]:idx[-1] + 1]
    step, pos, dry, n = fr / SR * 0.62, 0.0, [], len(mono)       # تبطيئ + تغليظ
    while pos < n - 1:
        i = int(pos)
        f = pos - i
        dry.append(mono[i] * (1 - f) + mono[i + 1] * f)
        pos += step
    y, env, nz, out = 0.0, 0.0, 0.0, []
    for i, v in enumerate(dry):
        v = math.tanh(2.4 * v) * (0.72 + 0.28 * math.sin(tp * 42 * i / SR))   # تشويه + خشونة
        y += (v - y) * 0.45                                                   # فلتر
        env += (abs(y) - env) * 0.002
        nz = nz * 0.8 + (random.random() * 2 - 1) * 0.2
        out.append(y + nz * env * 1.3)                                        # همس فوق الصوت
    tail = int(SR * 1.1)
    res = [0.0] * (len(out) + tail)
    for d, g in ((0, 1.0), (0.13, 0.55), (0.29, 0.4), (0.5, 0.28), (0.8, 0.16)):
        k = int(SR * d)
        for i, v in enumerate(out):
            res[i + k] += v * g
    m = max(abs(v) for v in res) or 1.0
    res = [v / m * 0.95 for v in res]
    fade = int(SR * 0.05)
    for i in range(fade):
        res[i] *= i / fade
        res[-1 - i] *= i / fade
    return _snd(res)


VOICE_KINDS = ('v_whisper', 'v_child', 'v_rev', 'v_choir')


def _load_mono(path):
    with wave.open(path) as w:
        ch, sw, fr = w.getnchannels(), w.getsampwidth(), w.getframerate()
        raw = w.readframes(w.getnframes())
    if sw != 2:
        return None, fr
    a = array.array('h')
    a.frombytes(raw)
    mono = [sum(a[i:i + ch]) / (ch * 32768.0) for i in range(0, len(a) - ch + 1, ch)]
    pk = max((abs(v) for v in mono), default=0)
    if pk < 0.01:
        return None, fr
    idx = [i for i, v in enumerate(mono) if abs(v) > pk * 0.04]
    return mono[idx[0]:idx[-1] + 1], fr


def _resample(mono, fr, ratio):
    step, pos, out, n = fr / SR * ratio, 0.0, [], len(mono)
    while pos < n - 1:
        i = int(pos)
        f = pos - i
        out.append(mono[i] * (1 - f) + mono[i + 1] * f)
        pos += step
    return out


def _mix(layers, tail_s=1.2):
    """بيدمج طبقات (عينات، تأخير بالثواني، قوة) في صوت واحد فيه صدى"""
    n = max(int(SR * d) + len(x) for x, d, g in layers) + int(SR * tail_s)
    res = [0.0] * n
    for x, d, g in layers:
        k = int(SR * d)
        for i, v in enumerate(x):
            res[i + k] += v * g
    m = max(abs(v) for v in res) or 1.0
    res = [v / m * 0.95 for v in res]
    fade = int(SR * 0.05)
    for i in range(fade):
        res[i] *= i / fade
        res[-1 - i] *= i / fade
    return res


def _save_wav(path, res):
    buf = array.array('h', [int(max(-1.0, min(1.0, v)) * 30000) for v in res])
    with wave.open(path, 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes(buf.tobytes())


def make_voice_variants(path):
    """همس قريب من ودنك / طفل مشوّه / الاسم بالمقلوب / كورال شياطين"""
    mono, fr = _load_mono(path)
    if not mono:
        return {}
    tp = 2 * math.pi
    vs = {}
    dry = _resample(mono, fr, 0.9)                                    # همس في ودنك
    env, nz, out = 0.0, 0.0, []
    for v in dry:
        env += (abs(v) - env) * 0.004
        nz = nz * 0.55 + (random.random() * 2 - 1) * 0.45
        out.append(nz * min(1.0, env * 14) * 1.3 + v * 0.10)
    vs['v_whisper'] = _mix([(out, 0, 1.0), (out, 0.18, 0.5), (out, 0.4, 0.3), (out, 0.7, 0.15)])
    dry = _resample(mono, fr, 1.3)                                    # صوت طفل مشوّه
    out = [math.tanh(1.8 * v) * (0.75 + 0.25 * math.sin(tp * 28 * i / SR)) for i, v in enumerate(dry)]
    vs['v_child'] = _mix([(out, 0, 1.0), (out, 0.22, 0.45), (out, 0.46, 0.25)], 1.0)
    dry = _resample(mono, fr, 0.7)[::-1]                              # الاسم بالمقلوب
    out, y = [], 0.0
    for v in dry:
        y += (math.tanh(2.0 * v) - y) * 0.5
        out.append(y + (random.random() * 2 - 1) * 0.02)
    vs['v_rev'] = _mix([(out, 0, 1.0), (out, 0.3, 0.5), (out, 0.6, 0.35), (out, 1.0, 0.2)], 1.6)
    layers = []                                                       # كورال شياطين
    for ratio, d, g in ((0.5, 0.0, 1.0), (0.58, 0.04, 0.85), (0.72, 0.09, 0.7), (1.2, 0.13, 0.35)):
        x, y = [], 0.0
        for i, v in enumerate(_resample(mono, fr, ratio)):
            v = math.tanh(2.8 * v) * (0.7 + 0.3 * math.sin(tp * 38 * i / SR))
            y += (v - y) * 0.5
            x.append(y)
        layers.append((x, d, g))
    base = layers[0][0]
    layers += [(base, 0.35, 0.5), (base, 0.7, 0.35), (base, 1.2, 0.2)]
    vs['v_choir'] = _mix(layers, 1.8)
    return vs


# ================================================================= الوحوش بتنادي اللاعبين بأسمائهم بوضوح
CLEAR_KEYS = ('n', 'c', 'd')          # عادي / طفل / غليظ
NAME_BUSY = set()


def make_clear_voices(path):
    """نسخ واضحة من الاسم: من غير همس ولا تشويه، بس صدى خفيف وطبقة صوت مختلفة"""
    mono, fr = _load_mono(path)
    if not mono:
        return {}
    vs = {}
    for key, ratio in (('n', 0.92), ('c', 1.22), ('d', 0.78)):
        y, x = 0.0, []
        for v in _resample(mono, fr, ratio):
            y += (math.tanh(1.15 * v) - y) * 0.8
            x.append(y)
        vs[key] = _mix([(x, 0, 1.0), (x, 0.24, 0.26), (x, 0.52, 0.12)], 0.9)
    return vs


def prepare_name_voice(name):
    """بيجهّز نسخ واضحة من اسم لاعب. بتتحفظ في الكاش فمبتتعملش تاني"""
    if not AUDIO or not name or ('vn:%s:n' % name) in SND or name in NAME_BUSY:
        return False
    NAME_BUSY.add(name)
    try:
        vdir = os.path.join(APP_DIR, "cache") if ANDROID else tempfile.gettempdir()
        os.makedirs(vdir, exist_ok=True)
        base = os.path.join(vdir, "hh_voice_%s" % hashlib.md5(name.encode('utf-8')).hexdigest()[:10])
        paths = {k: base + "_clear_%s_v1.wav" % k for k in CLEAR_KEYS}
        if not all(os.path.exists(p) and os.path.getsize(p) > 1000 for p in paths.values()):
            if not tts_to_wav(name, base + ".wav"):
                return False
            for k, res in make_clear_voices(base + ".wav").items():
                _save_wav(paths[k], res)
        for k, p in paths.items():
            if os.path.exists(p):
                SND['vn:%s:%s' % (name, k)] = pygame.mixer.Sound(p)
        return ('vn:%s:n' % name) in SND
    except Exception as ex:
        print("مشكلة في صوت الاسم:", ex)
    finally:
        NAME_BUSY.discard(name)
    return False


def prepare_names_async(names):
    """بيجهّز أصوات أسماء كل اللاعبين في الخلفية واللعبة شغّالة"""
    names = [n for n in dict.fromkeys(names) if n]
    if not names or not AUDIO:
        return

    def run():
        for n in names:
            prepare_name_voice(n)
    _th.Thread(target=run, daemon=True).start()


def prepare_voice(name):
    """بيجهّز صوت الشبح باسمك. لو فشل: الشبح هيهمس وبس"""
    SND.pop('voice', None)
    for k in VOICE_KINDS:
        SND.pop(k, None)
    if not AUDIO or not name:
        return False
    vdir = os.path.join(APP_DIR, "cache") if ANDROID else tempfile.gettempdir()
    os.makedirs(vdir, exist_ok=True)
    path = os.path.join(vdir, "hh_voice_%s.wav" % hashlib.md5(name.encode('utf-8')).hexdigest()[:10])
    try:
        if not (os.path.exists(path) and os.path.getsize(path) > 1000):
            if not tts_to_wav(name, path):
                print("ملقيتش صوت ينطق الاسم. نزّل:  pip install pyttsx3  (الشبح هيهمس بس دلوقتي)")
                return False
        snd = scary_voice(path)
        if snd:
            SND['voice'] = snd
        vs = None
        for k in VOICE_KINDS:                       # النسخ المرعبة بتتحفظ علشان التشغيل الجاي يبقى أسرع
            cp = path[:-4] + "_%s_v2.wav" % k
            if not (os.path.exists(cp) and os.path.getsize(cp) > 1000):
                if vs is None:
                    vs = make_voice_variants(path)
                if k not in vs:
                    continue
                _save_wav(cp, vs[k])
            SND[k] = pygame.mixer.Sound(cp)
        prepare_names_async([name])
        return 'voice' in SND
    except Exception as ex:
        print("مشكلة في صوت الشبح:", ex)
    return False


def prepare_voice_async(name):
    """على الموبايل التجهيز بياخد وقت، فبيتعمل في الخلفية واللعبة شغّالة"""
    if not ANDROID:
        return prepare_voice(name)
    import threading
    threading.Thread(target=prepare_voice, args=(name,), daemon=True).start()
    return False


# ================================================================= رسومات
_rad = {}


def radial(R, amax=240):
    R = max(12, int(R // 6 * 6))
    s = _rad.get((R, amax))
    if s is None:
        s = pygame.Surface((2 * R, 2 * R), pygame.SRCALPHA)
        for r in range(R, 0, -2):
            pygame.draw.circle(s, (255, 255, 255, int(amax * (1 - r / R) ** 1.1)), (R, R), r)
        _rad[(R, amax)] = s
    return s


def light(dark, cx, cy, R, amax=240):
    s = radial(R, amax)
    r = s.get_width() // 2
    dark.blit(s, (cx - r, cy - r), special_flags=pygame.BLEND_RGBA_SUB)


_glow = {}


def glow(s, x, y, R, col, amax=180):
    key = (R, col, amax)
    g = _glow.get(key)
    if g is None:
        g = radial(R, amax).copy()
        g.fill(col + (255,), special_flags=pygame.BLEND_RGBA_MULT)
        _glow[key] = g
    s.blit(g, (x - g.get_width() // 2, y - g.get_height() // 2))


def make_face(seed, style=0):
    """الوحش بتاع الخضّة: 0 شيطان بقرون، 1 ملكة الصراخ، 2 سيد الجماجم"""
    random.seed(seed)
    w, h = 300, 380
    s = pygame.Surface((w, h), pygame.SRCALPHA)
    if style == 0:
        skin, rim, eye, mane = (112, 126, 108), (60, 72, 58), (255, 170, 20), (30, 10, 14)
    elif style == 1:
        skin, rim, eye, mane = (214, 216, 208), (130, 130, 124), (190, 230, 255), (6, 6, 10)
    else:
        skin, rim, eye, mane = (226, 220, 196), (120, 112, 90), (255, 40, 20), (20, 16, 20)
    for _ in range(80):                                   # شعر / عرف
        x0 = random.randint(40, 260)
        pts = [(x0, 60)]
        x, y = x0, 60
        for _k in range(9):
            x += random.randint(-10, 10) + (-6 if x0 < 150 else 6)
            y += random.randint(26, 40)
            pts.append((x, y))
        pygame.draw.lines(s, mane, False, pts, random.randint(3, 7))
    if style == 0:                                        # قرون
        for sg in (-1, 1):
            cx = 150 + sg * 70
            pts = [(cx, 90), (cx + sg * 30, 40), (cx + sg * 62, 12), (cx + sg * 80, 28),
                   (cx + sg * 46, 52), (cx + sg * 22, 100)]
            pygame.draw.polygon(s, (36, 30, 26), pts)
            pygame.draw.lines(s, (90, 80, 66), False, pts[:4], 3)
    elif style == 2:                                      # تاج عضم
        for k in range(7):
            bx = 80 + k * 23
            pygame.draw.polygon(s, (150, 140, 110), [(bx - 8, 74), (bx + 8, 74), (bx + random.randint(-6, 6), 74 - random.randint(30, 60))])
    box = (56, 58, 188, 290) if style != 2 else (62, 62, 176, 230)
    pygame.draw.ellipse(s, skin, box)
    if style == 2:
        pygame.draw.rect(s, skin, (96, 250, 108, 90), border_radius=18)
    pygame.draw.ellipse(s, rim, box, 6)
    for _ in range(14):                                   # شروخ وندوب
        x = random.randint(80, 220)
        y = random.randint(80, 200)
        pygame.draw.lines(s, rim, False, [(x, y), (x + random.randint(-20, 20), y + 20), (x + random.randint(-30, 30), y + random.randint(40, 70))], 2)
    for ex in (112, 188):                                 # العيون المتوهجة
        if style == 2:
            pygame.draw.ellipse(s, (0, 0, 0), (ex - 28, 112, 56, 70))
        elif style == 1:
            pygame.draw.ellipse(s, (0, 0, 0), (ex - 24, 104, 48, 96))
        else:
            pygame.draw.polygon(s, (0, 0, 0), [(ex - 34, 130), (ex + 34, 112), (ex + 28, 160), (ex - 26, 166)])
        glow(s, ex, 144, 40, eye, 230)
        pygame.draw.circle(s, (255, 255, 235), (ex, 144), 5)
    if style == 1:                                        # الفم والأنياب
        pygame.draw.ellipse(s, (0, 0, 0), (118, 214, 64, 130))
        for k in range(6):
            pygame.draw.polygon(s, (230, 230, 215), [(122 + k * 11, 224), (130 + k * 11, 224), (126 + k * 11, 244)])
    else:
        mh = 96 if style == 0 else 70
        pygame.draw.ellipse(s, (14, 0, 0), (86, 222, 128, mh + 34))
        for k in range(9):
            tx = 94 + k * 13
            ln = random.randint(18, 40) if k % 2 else random.randint(10, 22)
            pygame.draw.polygon(s, (236, 232, 210), [(tx, 234), (tx + 12, 234), (tx + 6, 234 + ln)])
            pygame.draw.polygon(s, (236, 232, 210), [(tx, 236 + mh + 10), (tx + 12, 236 + mh + 10), (tx + 6, 236 + mh - ln // 2)])
    random.seed()
    return s


def make_ghost():
    """شبح طويل بفستان ممزق، شعر أسود على وشه، وإيدين طويلة"""
    random.seed(11)
    s = pygame.Surface((96, 160), pygame.SRCALPHA)
    for k in range(16):                                   # أطراف الفستان الممزقة
        x0 = 20 + k * 4
        pygame.draw.polygon(s, (196 + random.randint(-14, 14), 200, 210, 235 - (k % 3) * 25),
                            [(x0, 62), (x0 + 8, 62), (x0 + 4 + random.randint(-4, 4), random.randint(112, 158))])
    pygame.draw.polygon(s, (208, 211, 218, 242), [(32, 54), (64, 54), (74, 122), (22, 122)])
    for sg in (-1, 1):                                    # دراعات طويلة وصوابع
        pts = [(48 + sg * 14, 60), (48 + sg * 26, 90), (48 + sg * 20, 118), (48 + sg * 28, 140)]
        pygame.draw.lines(s, (222, 222, 210), False, pts, 5)
        hx, hy = pts[-1]
        for f in range(5):
            pygame.draw.line(s, (222, 222, 210), (hx, hy), (hx + (f - 2) * 3 + sg * random.randint(0, 6), hy + random.randint(10, 20)), 2)
    pygame.draw.rect(s, (214, 214, 204), (45, 50, 6, 10))
    pygame.draw.ellipse(s, (226, 226, 214), (34, 12, 28, 40))
    for ex in (38, 51):
        pygame.draw.ellipse(s, (0, 0, 0), (ex, 26, 8, 13))
    pygame.draw.ellipse(s, (0, 0, 0), (43, 42, 10, 20))
    for _ in range(95):                                   # شعر طويل
        x0 = random.randint(32, 64)
        sd = -1 if x0 < 48 else 1
        x, y = x0, 12 + random.randint(0, 6)
        pts = [(x, y)]
        for _k in range(9):
            x += sd * random.randint(0, 4) + random.randint(-2, 2)
            y += random.randint(10, 16)
            pts.append((x, y))
        pygame.draw.lines(s, (6, 6, 8, 255), False, pts, random.randint(1, 3))
    for _ in range(6):
        x = random.randint(38, 58)
        pygame.draw.line(s, (6, 6, 8, 255), (x, 14), (x + random.randint(-4, 4), random.randint(36, 56)), 1)
    random.seed()
    return s


# ---------------- الوحوش (من الصورة): 0 زومبي، 1 شيطان، 2 قاتل بقناع، 3 عجوز
MON_META = [
    dict(file="mon_0.png", js="js_0.png", eyes=[(0.5964, 0.0893), (0.6906, 0.0937)], col=(200, 255, 170), pw=0.55),
    dict(file="mon_1.png", js="js_1.png", eyes=[(0.5178, 0.1065), (0.6650, 0.1106)], col=(255, 40, 30), pw=1.0),
    dict(file="mon_2.png", js="js_2.png", eyes=[(0.3518, 0.1097), (0.4422, 0.1160)], col=(255, 50, 40), pw=0.35),
    dict(file="mon_3.png", js="js_3.png", eyes=[(0.1858, 0.1014), (0.3169, 0.1014)], col=(255, 70, 60), pw=0.8),
]
EXPRS = ('neutral', 'happy', 'surprised', 'angry', 'sad', 'scared')


def rand_mk():
    """وحش عشوائي للخضّات: من غير اللي تحت (هو بيظهر في آخر شقة بس)"""
    ok = [i for i in range(nmon()) if mon_of(i).get('beh') != 'boss']
    return random.choice(ok or [0])


def nmon():
    return len(A['mons'])


def mon_of(mk):
    return A['mons'][mk % len(A['mons'])]


def mon_big(mk, face_right=True):
    """نسخة الوحش الكبيرة (للجري قدام الشاشة) بتتعمل مرة وتتخزّن"""
    key = (mk % nmon(), face_right)
    b = A['mon_big'].get(key)
    if b is None:
        spr = mon_of(mk)['img']
        w, h = spr.get_size()
        b = pygame.transform.smoothscale(spr, (int(w * 430 / h), 430))
        if not face_right:
            b = pygame.transform.flip(b, True, False)
        A['mon_big'][key] = b
    return b


def draw_ghost_pos(gx, gy, t, mk=0):
    w, h = mon_of(mk)['img'].get_size()
    return (int(gx - w / 2 + math.sin(t * 1.7 + gx * 0.01) * 5),
            int(gy - h + 36 + math.sin(t * 2.2 + gy * 0.01) * 4))


def draw_ghost(s, gx, gy, alpha, t, mk=0):
    spr = mon_of(mk)['img']
    w, h = spr.get_size()
    x, y = draw_ghost_pos(gx, gy, t, mk)
    spr.set_alpha(alpha)
    if random.random() < 0.12:                            # تشويش
        for k in range(0, h, 12):
            s.blit(spr, (x + (random.randint(-9, 9) if random.random() < 0.5 else 0), y + k), (0, k, w, 12))
    else:
        s.blit(spr, (x, y))
    return x, y


def ghost_eyes(s, x, y, a=1.0, mk=0):
    m = mon_of(mk)
    w, h = m['img'].get_size()
    amax = min(255, int(m['pw'] * 60 * (1 + int(min(a, 0.99) * 3))))
    for fx, fy in m['eyes']:
        ex, ey = x + int(fx * w), y + int(fy * h)
        glow(s, ex, ey, 14, m['col'], amax)
        pygame.draw.ellipse(s, (255, 235, 225), (ex - 3, ey - 2, 6, 4))


def load_art():
    """الوحوش والشخصية والتعبيرات من ملفات assets. لو حصلت مشكلة بنرجع للرسم القديم"""
    try:
        def img(n):
            return pygame.image.load(asset(n)).convert_alpha()

        def sm(surf, size):
            return pygame.transform.smoothscale(surf, size)

        sheet = img("char_dir.png")
        cw, ch = 51, 91
        dw, dh = int(cw * PLAYER_SC), int(ch * PLAYER_SC)
        A['pdir'] = [[sm(sheet.subsurface((c * cw, r * ch, cw, ch)).copy(), (dw, dh)) for c in range(4)] for r in range(4)]
        fx = img("char_fx.png")
        fw, fh = 75, 74
        A['pfx'] = [sm(fx.subsurface((c * fw, r * fh, fw, fh)).copy(), (int(fw * PLAYER_SC), int(fh * PLAYER_SC)))
                    for r in range(2) for c in range(4)]           # 0-3 إصابة، 4-7 موت
        faces = pygame.image.load(asset("faces.png")).convert()
        A['expr'] = {n: faces.subsurface((i * 106, 0, 106, 106)).copy() for i, n in enumerate(EXPRS)}
        A['expr_hud'] = {n: sm(f, (62, 62)) for n, f in A['expr'].items()}
        A['mons'], A['js'] = [], []
        for m in MON_META:
            spr = img(m['file'])
            h = 165
            A['mons'].append(dict(img=sm(spr, (int(spr.get_width() * h / spr.get_height()), h)),
                                  eyes=m['eyes'], col=m['col'], pw=m['pw']))
            A['js'].append(img(m['js']))
        A['pdir_t'] = {}
        A['pfx_t'] = {}
        A['mon_big'] = {}
        A['art'] = True
    except Exception as ex:
        print("art load failed:", ex)
        A['art'] = False
        A['mons'] = [dict(img=A['ghost'], eyes=[(0.44, 0.2), (0.57, 0.2)], col=(255, 40, 30), pw=1.0)]
        A['js'] = A['faces']
        A['mon_big'] = {}


# ================================================================= وحوش إضافية (بتترسم بالكود، وتقدر تستبدلها بصور من assets)
# كل وحش ليه رسمة جسم (بتمشي في الشقة) ووش كبير (للخضّة). لو حطيت في فولدر assets ملفات
#   mon_4.png / js_4.png  ... لحد  mon_9.png / js_9.png   هتتاخد هي بدل الرسم بالكود.
def _claws(s, x, y, sg, col=(222, 222, 210), n=5, ln=18):
    for f in range(n):
        pygame.draw.line(s, col, (x, y), (x + (f - n // 2) * 4 + sg * random.randint(0, 6), y + random.randint(ln - 6, ln + 8)), 2)


def _flames(s, cx, base_y, w, hgt, n=9):
    """ألسنة نار (3 طبقات: أحمر - برتقالي - أصفر)"""
    for k in range(n):
        x = cx - w // 2 + int(w * k / max(1, n - 1))
        hh = hgt * random.uniform(0.55, 1.0)
        for col, sc in (((210, 50, 8), 1.0), ((255, 140, 20), 0.72), ((255, 225, 110), 0.42)):
            pygame.draw.polygon(s, col, [(x - max(6, w // n), base_y), (x + max(6, w // n), base_y),
                                         (x + random.randint(-10, 10), base_y - int(hh * sc))])


def _sp_nun():
    """الراهبة: روب أسود، وش شاحب، عيون بتنزل دم"""
    random.seed(401)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    pygame.draw.polygon(s, (14, 14, 20), [(80, 120), (160, 120), (214, 326), (26, 326)])
    for k in range(9):
        x = 40 + k * 20
        pygame.draw.line(s, (32, 32, 42), (120 + (x - 120) * 0.3, 130), (x, 326), 2)
    pygame.draw.polygon(s, (8, 8, 12), [(84, 36), (156, 36), (188, 150), (52, 150)])
    pygame.draw.polygon(s, (232, 232, 226), [(70, 122), (170, 122), (150, 152), (90, 152)])
    pygame.draw.ellipse(s, (214, 214, 204), (92, 50, 56, 78))
    pygame.draw.rect(s, (236, 236, 230), (88, 42, 64, 16))
    for ex in (108, 132):
        pygame.draw.ellipse(s, (0, 0, 0), (ex - 9, 78, 18, 22))
        pygame.draw.line(s, (130, 0, 0), (ex, 98), (ex + random.randint(-3, 3), 130), 2)
    pygame.draw.ellipse(s, (20, 0, 0), (108, 108, 24, 16))
    for k in range(5):
        pygame.draw.line(s, (230, 230, 215), (111 + k * 4, 110), (111 + k * 4, 116), 1)
    pygame.draw.line(s, (170, 150, 60), (120, 160), (120, 198), 4)
    pygame.draw.line(s, (170, 150, 60), (108, 172), (132, 172), 4)
    for sg in (-1, 1):
        pts = [(120 + sg * 50, 140), (120 + sg * 66, 205), (120 + sg * 58, 262)]
        pygame.draw.lines(s, (12, 12, 18), False, pts, 18)
        pygame.draw.line(s, (210, 210, 200), pts[-1], (pts[-1][0], pts[-1][1] + 18), 6)
        _claws(s, pts[-1][0], pts[-1][1] + 14, sg)
    random.seed()
    return s, [(108, 90), (132, 90)]


def _sp_doll():
    """الدمية: راسها بورسلين مشروخ، عين زرار وعين فاضية"""
    random.seed(402)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    pygame.draw.polygon(s, (110, 18, 28), [(96, 150), (144, 150), (206, 312), (34, 312)])
    for k in range(8):
        pygame.draw.circle(s, (220, 205, 190), (46 + k * 21, 308), 9)
    for lx in (98, 134):
        pygame.draw.rect(s, (206, 196, 184), (lx, 306, 10, 22))
    pygame.draw.lines(s, (206, 196, 184), False, [(98, 162), (62, 200), (70, 246)], 9)
    pygame.draw.lines(s, (206, 196, 184), False, [(142, 162), (178, 200), (170, 246)], 9)
    pygame.draw.ellipse(s, (40, 22, 14), (44, 18, 152, 112))
    for sg in (-1, 1):
        for k in range(5):
            pygame.draw.circle(s, (40, 22, 14), (120 + sg * 70, 56 + k * 20), 17)
    pygame.draw.ellipse(s, (232, 224, 214), (64, 32, 112, 112))
    for _ in range(7):
        x, y = random.randint(80, 160), random.randint(46, 110)
        pygame.draw.lines(s, (90, 80, 70), False, [(x, y), (x + random.randint(-12, 12), y + 14), (x + random.randint(-16, 16), y + 30)], 1)
    pygame.draw.circle(s, (10, 10, 10), (98, 88), 15)
    pygame.draw.line(s, (230, 230, 230), (90, 80), (106, 96), 2)
    pygame.draw.line(s, (230, 230, 230), (106, 80), (90, 96), 2)
    pygame.draw.circle(s, (0, 0, 0), (142, 88), 16)
    for cx in (80, 160):
        pygame.draw.circle(s, (190, 70, 70), (cx, 118), 9)
    pygame.draw.line(s, (120, 10, 10), (92, 124), (148, 124), 3)
    for k in range(7):
        pygame.draw.line(s, (120, 10, 10), (94 + k * 9, 119), (94 + k * 9, 130), 1)
    random.seed()
    return s, [(98, 88), (142, 88)]


def _sp_tall():
    """الرجل الطويل: بدلة سودا، وش فاضي، دراعات طويلة وزوايد من ضهره"""
    random.seed(403)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    for k in range(5):                                       # زوايد من ضهره
        x, y = 120, 120
        pts = [(x, y)]
        sg = -1 if k % 2 else 1
        for _ in range(6):
            x += sg * random.randint(6, 18)
            y -= random.randint(2, 26) - (10 if k > 1 else 0)
            pts.append((x, y))
        pygame.draw.lines(s, (6, 6, 8), False, pts, 5)
    pygame.draw.rect(s, (10, 10, 14), (96, 230, 20, 96))
    pygame.draw.rect(s, (10, 10, 14), (124, 230, 20, 96))
    pygame.draw.polygon(s, (10, 10, 14), [(88, 94), (152, 94), (146, 244), (94, 244)])
    pygame.draw.polygon(s, (200, 200, 206), [(108, 94), (132, 94), (120, 150)])
    pygame.draw.line(s, (24, 24, 30), (120, 100), (120, 190), 5)
    for sg in (-1, 1):
        pts = [(120 + sg * 32, 100), (120 + sg * 54, 200), (120 + sg * 46, 312)]
        pygame.draw.lines(s, (10, 10, 14), False, pts, 8)
        hx, hy = pts[-1]
        for f in range(4):
            pygame.draw.line(s, (214, 214, 208), (hx, hy), (hx + (f - 2) * 3, hy + random.randint(12, 18)), 2)
    pygame.draw.rect(s, (214, 214, 208), (114, 80, 12, 16))
    pygame.draw.ellipse(s, (222, 222, 216), (98, 24, 44, 64))
    for ex in (110, 130):
        pygame.draw.ellipse(s, (30, 30, 34), (ex - 4, 54, 8, 8))
    random.seed()
    return s, [(110, 58), (130, 58)]


def _sp_clown():
    """المهرج: ابتسامة لحد ودانه وهدوم منقّطة"""
    random.seed(404)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    pygame.draw.polygon(s, (150, 30, 40), [(76, 140), (164, 140), (200, 312), (40, 312)])
    for _ in range(15):
        x, y = random.randint(70, 170), random.randint(160, 300)
        pygame.draw.circle(s, (205, 195, 80), (x, y), 7)
    for sg in (-1, 1):
        pygame.draw.lines(s, (150, 30, 40), False, [(120 + sg * 44, 152), (120 + sg * 78, 226), (120 + sg * 70, 262)], 16)
        pygame.draw.ellipse(s, (236, 236, 232), (120 + sg * 70 - 12, 256, 26, 30))
        _claws(s, 120 + sg * 70, 276, sg, (236, 236, 232), 4, 14)
    for k in range(9):
        pygame.draw.circle(s, (236, 236, 228), (76 + k * 11, 142), 10)
    for fx in (52, 128):
        pygame.draw.ellipse(s, (200, 40, 30), (fx, 302, 62, 26))
    for sg in (-1, 1):
        for k in range(5):
            pygame.draw.circle(s, (196, 56, 20), (120 + sg * (46 + (k % 2) * 6), 40 + k * 14), 18)
    pygame.draw.ellipse(s, (240, 236, 230), (80, 24, 80, 100))
    for ex in (104, 136):
        pygame.draw.polygon(s, (22, 10, 10), [(ex, 54), (ex + 11, 66), (ex, 78), (ex - 11, 66)])
    pygame.draw.circle(s, (210, 20, 20), (120, 86), 9)
    pygame.draw.ellipse(s, (150, 0, 10), (86, 94, 68, 28))
    pygame.draw.line(s, (150, 0, 10), (88, 104), (76, 88), 4)
    pygame.draw.line(s, (150, 0, 10), (152, 104), (164, 88), 4)
    for k in range(8):
        pygame.draw.polygon(s, (240, 236, 220), [(92 + k * 8, 104), (98 + k * 8, 104), (95 + k * 8, 112)])
    random.seed()
    return s, [(104, 66), (136, 66)]


def _sp_flesh():
    """الكتلة اللحمية: عيون كتير وخيوط وفم"""
    random.seed(405)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    for k in range(9):                                       # مجسّات
        sg = -1 if k % 2 else 1
        x, y = 120 + sg * random.randint(30, 70), random.randint(150, 290)
        pts = [(x, y)]
        for _ in range(6):
            x += sg * random.randint(6, 18)
            y += random.randint(-22, 14)
            pts.append((x, y))
        pygame.draw.lines(s, (120, 28, 44), False, pts, random.randint(4, 9))
    pygame.draw.ellipse(s, (146, 40, 54), (38, 60, 164, 266))
    for _ in range(14):
        x, y, r = random.randint(60, 180), random.randint(90, 300), random.randint(10, 26)
        c = random.randint(-22, 22)
        pygame.draw.ellipse(s, (146 + c, 40 + c // 2, 54 + c // 2), (x - r, y - r, 2 * r, int(r * 1.5)))
    pygame.draw.ellipse(s, (30, 0, 6), (78, 232, 84, 62))
    for k in range(7):
        pygame.draw.polygon(s, (236, 230, 205), [(84 + k * 11, 240), (94 + k * 11, 240), (89 + k * 11, 258)])
        pygame.draw.polygon(s, (236, 230, 205), [(84 + k * 11, 288), (94 + k * 11, 288), (89 + k * 11, 270)])
    eyes = [(92, 130, 20), (148, 126, 20), (120, 178, 11), (70, 190, 9), (170, 186, 9), (104, 96, 8), (140, 98, 8)]
    for ex, ey, r in eyes:
        pygame.draw.circle(s, (236, 230, 220), (ex, ey), r)
        pygame.draw.circle(s, (180, 20, 20), (ex, ey), max(3, int(r * 0.6)))
        pygame.draw.circle(s, (0, 0, 0), (ex, ey), max(2, int(r * 0.3)))
    random.seed()
    return s, [(92, 130), (148, 126)]


def _sp_skel():
    """الهيكل المحروق: عضم ولهب"""
    random.seed(406)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    bone = (226, 220, 196)
    glow(s, 120, 170, 100, (255, 110, 10), 150)
    pygame.draw.line(s, bone, (120, 100), (120, 236), 8)
    for k in range(6):
        pygame.draw.line(s, bone, (120, 116 + k * 16), (88 - k * 2, 130 + k * 16), 5)
        pygame.draw.line(s, bone, (120, 116 + k * 16), (152 + k * 2, 130 + k * 16), 5)
    pygame.draw.polygon(s, bone, [(96, 236), (144, 236), (136, 262), (104, 262)])
    for sg in (-1, 1):
        pygame.draw.lines(s, bone, False, [(120 + sg * 30, 112), (120 + sg * 54, 186), (120 + sg * 44, 250)], 6)
        _claws(s, 120 + sg * 44, 250, sg, bone, 5, 16)
        pygame.draw.lines(s, bone, False, [(120 + sg * 16, 262), (120 + sg * 22, 296), (120 + sg * 20, 326)], 7)
    pygame.draw.ellipse(s, bone, (88, 26, 64, 70))
    pygame.draw.rect(s, bone, (98, 86, 44, 22))
    for k in range(5):
        pygame.draw.line(s, (40, 36, 30), (102 + k * 9, 88), (102 + k * 9, 106), 1)
    for ex in (100, 124):
        pygame.draw.ellipse(s, (0, 0, 0), (ex, 52, 18, 24))
    _flames(s, 120, 46, 80, 62, 8)
    _flames(s, 120, 150, 110, 80, 9)
    random.seed()
    return s, [(109, 64), (133, 64)]


def _jf_nun():
    random.seed(501)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    pygame.draw.polygon(s, (6, 6, 10), [(26, 380), (58, 64), (150, 8), (242, 64), (274, 380)])
    pygame.draw.polygon(s, (232, 232, 226), [(70, 330), (230, 330), (262, 380), (38, 380)])
    pygame.draw.ellipse(s, (212, 212, 202), (80, 70, 140, 240))
    pygame.draw.rect(s, (236, 236, 230), (72, 62, 156, 40))
    for ex in (126, 174):
        pygame.draw.ellipse(s, (0, 0, 0), (ex - 18, 140, 36, 50))
        for _ in range(4):
            pygame.draw.line(s, (130, 0, 0), (ex, 186), (ex + random.randint(-10, 10), 300), 3)
        glow(s, ex, 164, 34, (255, 40, 40), 200)
        pygame.draw.circle(s, (255, 230, 220), (ex, 164), 4)
    pygame.draw.ellipse(s, (0, 0, 0), (118, 232, 64, 82))
    for k in range(6):
        pygame.draw.polygon(s, (232, 232, 216), [(122 + k * 10, 238), (130 + k * 10, 238), (126 + k * 10, 262)])
        pygame.draw.polygon(s, (232, 232, 216), [(122 + k * 10, 308), (130 + k * 10, 308), (126 + k * 10, 288)])
    random.seed()
    return s


def _jf_doll():
    random.seed(502)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    for sg in (-1, 1):
        for k in range(6):
            pygame.draw.circle(s, (40, 22, 14), (150 + sg * 118, 70 + k * 46), 34)
    pygame.draw.ellipse(s, (40, 22, 14), (30, 10, 240, 200))
    pygame.draw.ellipse(s, (234, 226, 216), (50, 46, 200, 300))
    for _ in range(11):
        x, y = random.randint(70, 230), random.randint(70, 250)
        pygame.draw.lines(s, (90, 80, 70), False, [(x, y), (x + random.randint(-20, 20), y + 24), (x + random.randint(-30, 30), y + random.randint(40, 70))], 2)
    pygame.draw.circle(s, (8, 8, 8), (106, 150), 30)
    pygame.draw.line(s, (230, 230, 230), (90, 134), (122, 166), 4)
    pygame.draw.line(s, (230, 230, 230), (122, 134), (90, 166), 4)
    pygame.draw.ellipse(s, (0, 0, 0), (168, 112, 58, 76))
    glow(s, 197, 150, 34, (255, 50, 40), 210)
    for cx in (80, 220):
        pygame.draw.circle(s, (196, 80, 80), (cx, 222), 20)
    pygame.draw.ellipse(s, (0, 0, 0), (92, 252, 116, 60))
    for k in range(10):
        pygame.draw.line(s, (234, 226, 216), (98 + k * 11, 252), (98 + k * 11, 270), 3)
        pygame.draw.line(s, (120, 10, 10), (96 + k * 11, 244), (96 + k * 11, 322), 1)
    random.seed()
    return s


def _jf_tall():
    random.seed(503)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    for _ in range(14):
        x, y = 150 + random.randint(-30, 30), 330
        pts = [(x, y)]
        for _k in range(7):
            x += random.randint(-30, 30)
            y -= random.randint(20, 46)
            pts.append((x, y))
        pygame.draw.lines(s, (6, 6, 8), False, pts, random.randint(3, 7))
    pygame.draw.polygon(s, (10, 10, 14), [(20, 380), (60, 300), (240, 300), (280, 380)])
    pygame.draw.polygon(s, (200, 200, 206), [(124, 300), (176, 300), (150, 380)])
    pygame.draw.ellipse(s, (222, 222, 216), (86, 24, 128, 290))
    for ex in (118, 182):
        pygame.draw.ellipse(s, (40, 40, 44), (ex - 14, 130, 28, 12))
        glow(s, ex, 136, 22, (255, 255, 255), 110)
    pygame.draw.ellipse(s, (0, 0, 0), (110, 200, 80, 120))
    for k in range(7):
        pygame.draw.line(s, (200, 200, 190), (116 + k * 11, 204), (116 + k * 11, 214 + (k % 2) * 8), 2)
    random.seed()
    return s


def _jf_clown():
    random.seed(504)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    for sg in (-1, 1):
        for k in range(6):
            pygame.draw.circle(s, (196, 56, 20), (150 + sg * (104 + (k % 2) * 12), 60 + k * 44), 38)
    pygame.draw.ellipse(s, (240, 236, 230), (56, 56, 188, 290))
    for ex in (112, 188):
        pygame.draw.polygon(s, (20, 8, 8), [(ex, 110), (ex + 28, 148), (ex, 186), (ex - 28, 148)])
        glow(s, ex, 148, 26, (255, 220, 40), 230)
        pygame.draw.line(s, (170, 0, 10), (ex - 30, 100), (ex + 24, 82), 5)
    pygame.draw.circle(s, (210, 20, 20), (150, 204), 24)
    pygame.draw.ellipse(s, (140, 0, 10), (60, 232, 180, 100))
    pygame.draw.line(s, (140, 0, 10), (66, 252), (44, 208), 8)
    pygame.draw.line(s, (140, 0, 10), (234, 252), (256, 208), 8)
    for k in range(13):
        pygame.draw.polygon(s, (240, 236, 220), [(74 + k * 12, 250), (86 + k * 12, 250), (80 + k * 12, 250 + random.randint(18, 34))])
        pygame.draw.polygon(s, (240, 236, 220), [(74 + k * 12, 320), (86 + k * 12, 320), (80 + k * 12, 320 - random.randint(12, 26))])
    random.seed()
    return s


def _jf_flesh():
    random.seed(505)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    pygame.draw.ellipse(s, (146, 40, 54), (14, 30, 272, 330))
    for _ in range(22):
        x, y, r = random.randint(40, 260), random.randint(60, 340), random.randint(14, 34)
        c = random.randint(-24, 24)
        pygame.draw.ellipse(s, (146 + c, 40 + c // 2, 54 + c // 2), (x - r, y - r, 2 * r, int(r * 1.4)))
    for _ in range(10):
        x, y = random.randint(60, 240), random.randint(70, 200)
        pygame.draw.lines(s, (90, 10, 24), False, [(x, y), (x + random.randint(-30, 30), y + 34), (x + random.randint(-40, 40), y + 70)], 3)
    placed = [(100, 130, 30), (206, 124, 30)]
    for _ in range(40):
        if len(placed) >= 13:
            break
        x, y, r = random.randint(50, 250), random.randint(70, 230), random.randint(11, 20)
        if all(math.hypot(x - px, y - py) > r + pr + 4 for px, py, pr in placed):
            placed.append((x, y, r))
    for ex, ey, r in placed:
        pygame.draw.circle(s, (236, 230, 220), (ex, ey), r)
        pygame.draw.circle(s, (180, 20, 20), (ex, ey), max(4, int(r * 0.62)))
        pygame.draw.circle(s, (0, 0, 0), (ex, ey), max(3, int(r * 0.32)))
        glow(s, ex, ey, r + 8, (255, 40, 30), 90)
    pygame.draw.ellipse(s, (26, 0, 6), (64, 248, 172, 100))
    for k in range(10):
        pygame.draw.polygon(s, (236, 230, 205), [(74 + k * 16, 256), (88 + k * 16, 256), (81 + k * 16, 282)])
        pygame.draw.polygon(s, (236, 230, 205), [(74 + k * 16, 340), (88 + k * 16, 340), (81 + k * 16, 314)])
    random.seed()
    return s


def _jf_skull():
    random.seed(506)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    glow(s, 150, 190, 170, (255, 100, 10), 210)
    _flames(s, 150, 320, 250, 250, 14)
    pygame.draw.ellipse(s, (226, 220, 196), (72, 56, 156, 216))
    pygame.draw.rect(s, (226, 220, 196), (104, 252, 92, 70), border_radius=10)
    for k in range(7):
        pygame.draw.line(s, (60, 50, 40), (110 + k * 13, 264), (110 + k * 13, 318), 2)
    pygame.draw.line(s, (60, 50, 40), (104, 288), (196, 288), 2)
    for ex in (122, 178):
        pygame.draw.ellipse(s, (0, 0, 0), (ex - 24, 126, 48, 66))
        glow(s, ex, 160, 36, (255, 170, 20), 240)
        pygame.draw.circle(s, (255, 240, 180), (ex, 160), 5)
    pygame.draw.polygon(s, (0, 0, 0), [(150, 206), (136, 238), (164, 238)])
    for _ in range(8):
        x, y = random.randint(90, 210), random.randint(70, 130)
        pygame.draw.lines(s, (90, 76, 56), False, [(x, y), (x + random.randint(-14, 14), y + 20), (x + random.randint(-20, 20), y + 44)], 2)
    _flames(s, 150, 76, 130, 84, 9)
    random.seed()
    return s


def _sp_below():
    """اللي تحت: كتلة سودا بدراعات طويلة ووش شاحب بعيون كتير"""
    random.seed(407)
    s = pygame.Surface((240, 330), pygame.SRCALPHA)
    glow(s, 120, 190, 112, (120, 0, 20), 120)
    for k in range(10):
        sg = -1 if k % 2 else 1
        x, y = 120 + sg * random.randint(30, 60), random.randint(110, 230)
        pts = [(x, y)]
        for _ in range(6):
            x += sg * random.randint(8, 20)
            y += random.randint(-30, 26)
            pts.append((x, y))
        pygame.draw.lines(s, (10, 6, 12), False, pts, random.randint(5, 10))
        hx, hy = pts[-1]
        for _f in range(4):
            pygame.draw.line(s, (200, 196, 188), (hx, hy), (hx + sg * random.randint(6, 16), hy + random.randint(-12, 12)), 2)
    pygame.draw.ellipse(s, (12, 8, 14), (46, 110, 148, 214))
    for _ in range(12):
        x, y = random.randint(60, 180), random.randint(200, 300)
        pygame.draw.line(s, (12, 8, 14), (x, y), (x, y + random.randint(14, 30)), 4)
    pygame.draw.ellipse(s, (206, 202, 190), (80, 20, 80, 120))
    for ex, ey, r in ((104, 62, 9), (136, 62, 9), (110, 88, 6), (130, 88, 6), (120, 42, 5)):
        pygame.draw.circle(s, (10, 0, 0), (ex, ey), r)
        pygame.draw.circle(s, (200, 20, 20), (ex, ey), max(2, r // 2))
    pygame.draw.ellipse(s, (20, 0, 6), (108, 102, 24, 38))
    for k in range(5):
        pygame.draw.line(s, (226, 222, 205), (111 + k * 4, 104), (111 + k * 4, 112), 1)
        pygame.draw.line(s, (226, 222, 205), (111 + k * 4, 138), (111 + k * 4, 130), 1)
    random.seed()
    return s, [(104, 62), (136, 62), (110, 88), (130, 88)]


def _jf_below():
    random.seed(507)
    s = pygame.Surface((300, 380), pygame.SRCALPHA)
    glow(s, 150, 200, 210, (130, 0, 24), 170)
    for k in range(16):
        sg = -1 if k % 2 else 1
        x, y = 150 + sg * random.randint(100, 150), random.randint(180, 380)
        pts = [(x, y)]
        for _ in range(6):
            x -= sg * random.randint(10, 24)
            y += random.randint(-40, 14)
            pts.append((x, y))
        pygame.draw.lines(s, (8, 4, 10), False, pts, random.randint(8, 14))
        hx, hy = pts[-1]
        for _f in range(5):
            pygame.draw.line(s, (210, 206, 194), (hx, hy), (hx - sg * random.randint(10, 26), hy + random.randint(-18, 18)), 3)
    pygame.draw.ellipse(s, (206, 202, 190), (62, 22, 176, 310))
    for _ in range(9):
        x, y = random.randint(90, 210), random.randint(40, 120)
        pygame.draw.lines(s, (70, 60, 56), False, [(x, y), (x + random.randint(-16, 16), y + 30), (x + random.randint(-24, 24), y + 70)], 2)
    for ex, ey, r in ((112, 118, 20), (188, 118, 20), (126, 170, 12), (174, 170, 12), (150, 82, 11), (150, 210, 8)):
        pygame.draw.circle(s, (10, 0, 0), (ex, ey), r)
        glow(s, ex, ey, r + 12, (255, 30, 30), 190)
        pygame.draw.circle(s, (210, 20, 20), (ex, ey), max(3, r // 2))
    pygame.draw.ellipse(s, (18, 0, 6), (112, 236, 76, 110))
    for k in range(8):
        pygame.draw.polygon(s, (230, 226, 208), [(116 + k * 9, 240), (124 + k * 9, 240), (120 + k * 9, 262)])
        pygame.draw.polygon(s, (230, 226, 208), [(116 + k * 9, 340), (124 + k * 9, 340), (120 + k * 9, 318)])
    random.seed()
    return s


# (الاسم، رسمة الجسم، رسمة الوش، لون العيون، قوّة التوهّج، السلوك، الطول)
EXTRA_MONS = [
    ("nun", _sp_nun, _jf_nun, (255, 40, 40), 0.9, "nun"),
    ("doll", _sp_doll, _jf_doll, (255, 60, 50), 0.8, "doll"),
    ("tall", _sp_tall, _jf_tall, (255, 255, 255), 0.45, "tall"),
    ("clown", _sp_clown, _jf_clown, (255, 220, 40), 0.9, "clown"),
    ("flesh", _sp_flesh, _jf_flesh, (255, 40, 30), 1.0, "flesh"),
    ("skel", _sp_skel, _jf_skull, (255, 160, 20), 1.0, "fire"),
    ("below", _sp_below, _jf_below, (255, 30, 30), 1.2, "boss", 250),
]
# صوت بيطلع مع كل وحش (بالترتيب: 0-3 الأصليين، 4-9 الجداد)
MON_SOUND = {0: 'moan', 1: 'growl', 2: 'breath', 3: 'cry', 4: 'bell', 5: 'giggle', 6: 'static', 7: 'laugh', 8: 'rattle', 9: 'crunch', 10: 'chant'}


def extra_amb(level):
    """أصوات أجواء إضافية بتتضاف على القديمة حسب الشقة"""
    k = ['wind', 'drip', 'scratch', 'clock', 'crow']
    if level >= 2:
        k += ['chains', 'dragging', 'moan', 'giggle', 'radio', 'knock3', 'doorknob', 'whistle', 'swing', 'flies']
    if level >= 3:
        k += ['growl', 'bell', 'glass', 'hiss', 'crunch', 'baby', 'phone', 'howl', 'chant', 'rattle', 'revwhisper', 'run']
    return k


def add_extra_monsters():
    """بيضيف الوحوش الجداد لقايمة الوحوش (A['mons']) والخضّة (A['js']). كل الكود التاني بيشتغل عليهم لوحده"""
    base = len(A['mons'])
    for i, m in enumerate(A['mons']):                      # سلوك الوحوش الأصليين (الزومبي والشيطان والقاتل والعجوز)
        m.setdefault('beh', ORIG_BEH[i] if (A.get('art') and i < len(ORIG_BEH)) else 'plain')
    if len(A['js']) > base:
        A['js'] = list(A['js'])[:base]
    for k, ent in enumerate(EXTRA_MONS):
        nm, spf, jff, col, pw, beh = ent[:6]
        hgt = ent[6] if len(ent) > 6 else 165
        try:
            big, eyes = spf()
            W, H = big.get_size()
            ef = [(ex / W, ey / H) for ex, ey in eyes]
            jface = jff()
            fn_m, fn_j = "mon_%d.png" % (4 + k), "js_%d.png" % (4 + k)
            if os.path.exists(asset(fn_m)):                    # صورة من عندك بتغلب الرسم بالكود
                big = pygame.image.load(asset(fn_m)).convert_alpha()
            if os.path.exists(asset(fn_j)):
                jface = pygame.image.load(asset(fn_j)).convert_alpha()
            h = hgt
            spr = pygame.transform.smoothscale(big, (max(1, int(big.get_width() * h / big.get_height())), h))
            A['mons'].append(dict(img=spr, eyes=ef, col=col, pw=pw, beh=beh))
            A['js'].append(jface)
        except Exception as ex:
            print("extra monster failed:", nm, ex)
    A['mon_big'] = {}


# ================================================================= سلوك كل وحش
ORIG_BEH = ['zombie', 'demon', 'killer', 'hag']
# أول شقة بيظهر فيها كل نوع (عشان الشقق الأولى تبقى أهدى)
BEH_LEVEL = {'zombie': 1, 'hag': 1, 'nun': 1, 'doll': 2, 'killer': 2, 'clown': 3, 'demon': 3, 'tall': 4, 'flesh': 5, 'fire': 6, 'boss': 99}
BEH_HINT = {'zombie': "بطيء... بس الكشاف مش بيأثر عليه!",
            'demon': "لما يزأر... اجري! هيهجم!",
            'killer': "بيسمع خطواتك... وقّف مكانك!",
            'hag': "بتختفي وتظهر أقرب منك!",
            'nun': "بتقوى كل ما تخاف... اهدا!",
            'doll': "بتنط ناحيتك... والكشاف بيجمّدها!",
            'tall': "كل ما تبصله بتخاف أكتر... وكل ما تبعد عينك بيقرّب!",
            'clown': "بيتلوّى وبيقف يضحك... استغل وقفته واجري!",
            'flesh': "بطيء... بس رعبه بيوصل لبعيد!",
            'fire': "سريع... بس بيحترق ويختفي بسرعة!"}


def pick_mon(level):
    """بيختار وحش مناسب للشقة (الأنواع الأخطر بتظهر في الشقق الأعلى)"""
    ok = [i for i in range(nmon()) if BEH_LEVEL.get(mon_of(i).get('beh', 'plain'), 1) <= level]
    return random.choice(ok or list(range(nmon())))


def make_vignette():
    s = pygame.Surface((SW, SH), pygame.SRCALPHA)
    for k in range(70):
        pygame.draw.rect(s, (90, 0, 0, int(230 * (1 - k / 70) ** 2.2)), (k * 4, k * 4, SW - k * 8, SH - k * 8), 4)
    return s


def draw_hand(s, x, y, ang):
    """بصمة إيد دم على الأرض"""
    col = (122, 10, 12)
    pygame.draw.ellipse(s, col, (x - 9, y - 5, 18, 20))
    for a in (-52, -26, 0, 26, 52):
        r = math.radians(a + ang)
        ln = 30 if a == 0 else 26
        pygame.draw.line(s, col, (x + math.sin(r) * 6, y - 2 - math.cos(r) * 6),
                         (x + math.sin(r) * ln, y - 2 - math.cos(r) * ln), 4)
    pygame.draw.line(s, col, (x - 4, y + 12), (x - 6, y + 34), 3)       # دم نازل



A = {}


# ================================================================= الحفظ
def load_save():
    try:
        with open(SAVE_FILE, encoding='utf-8') as f:
            d = json.load(f)
        if 'profile' in d:
            return d
    except Exception:
        pass
    return None


def write_save(d):
    try:
        with open(SAVE_FILE, 'w', encoding='utf-8') as f:
            json.dump(d, f, ensure_ascii=False)
        return True
    except Exception:
        return False


NAME_LINES = ["{n}... استنّى", "مش هتهرب يا {n}", "{n}.. ورااااك", "أنا شايفك يا {n}",
              "تعالى يا {n}... متخافش", "{n}... كنت مستنيك", "{n}... أنا واقف ورا الباب",
              "{n}.. بصّ ورا", "مش لوحدك يا {n}", "{n}... سامعك وإنت بتتنفّس",
              "فاضل خطوة واحدة يا {n}", "ليه سبتني لوحدي يا {n}؟"]

AMB_TEXT = {'creak': "سمعت صرير باب بيتفتح... في مكان ما.",
            'whisper': "مين اللي بيهمس؟!",
            'step': "خطوات... جاية من فوق.",
            'knock': "حد بيخبط... من جوه الحيطة!",
            'cry': "سمعت عياط طفل... بعيد.",
            'laugh': "ضحكة طفل... ورا الباب!",
            'musicbox': "علبة موسيقى بتشتغل لوحدها...",
            'breath': "حاسس بنفس بارد ورا رقبتك...",
            'slam': "باب اتقفل بقوة في مكان ما!"}
AMB_TEXT.update({'growl': "زمجرة... قريبة جداً!",
                 'chains': "سلاسل بتتجرّ في الضلمة...",
                 'dragging': "حاجة تقيلة بتتسحب على الأرض...",
                 'scratch': "حد بيخربش الحيطة بضوافره...",
                 'bell': "جرس بيدق... ومفيش جرس في البيت!",
                 'wind': "ريح بتعوي... والشبابيك مقفولة!",
                 'drip': "نقطة... نقطة... مياه بتنزل من فوق.",
                 'glass': "إزاز اتكسر في الأوضة اللي جنبك!",
                 'radio': "راديو بيتكلم لوحده... بصوت مش مفهوم.",
                 'giggle': "ضحكة واطية... جاية من تحت السرير.",
                 'moan': "أنين طويل... مش بشري.",
                 'hiss': "فحيح جنب ودنك!",
                 'crunch': "صوت عضم بيتكسّر..."})
AMB_TEXT.update({'baby': "طفل بيعيّط... ومفيش أطفال في العمارة.",
                 'flies': "دبّان كتير... جاي منين؟",
                 'run': "حد بيجري ناحيتك في الضلمة!",
                 'knock3': "تلات خبطات تقيلة على الباب...",
                 'whistle': "حد بيصفّر لحن قديم...",
                 'phone': "تليفون بيرن... والخط مقطوع من سنين.",
                 'doorknob': "مقبض الباب بيتهز... من بره!",
                 'clock': "ساعة بتدق... بس الساعات كلها واقفة.",
                 'swing': "أرجوحة بتزيّ لوحدها...",
                 'howl': "عواء بعيد... بيقرّب.",
                 'crow': "غراب بينعق... جوه الشقة!",
                 'chant': "ترتيل واطي... بلغة مش مفهومة.",
                 'boom': "ضربة مرعبة!",
                 'rattle': "حشرجة... جنبك مباشرة.",
                 'revwhisper': "همس معكوس... بيقول اسمك؟"})
LOUD_AMB = ('laugh', 'cry', 'musicbox', 'slam', 'knock', 'growl', 'giggle', 'moan', 'glass', 'bell', 'chains', 'hiss', 'crunch',
            'baby', 'phone', 'knock3', 'howl', 'chant', 'rattle', 'run', 'revwhisper', 'doorknob')
HALL_WORDS = ["وراك", "شايفك", "اطلع", "هو هنا"]
DECAL_WORDS = ["اطلع", "هو وراك", "شايفك", "مش هتخرج", "متبصّش"]


# ================================================================= اللعبة
AR_ROWS = ["ضصثقفغعهخحجد", "شسيبلاتنمكطذ", "ئءؤرىةوزظأإآ"]
EN_ROWS = ["qwertyuiop", "asdfghjkl", "zxcvbnm'"]


# ================================================================= الأونلاين (العميل)
def parse_addr(a):
    a = (a or '').strip()
    if not a:
        return None, NET_PORT
    if a.count(':') == 1:
        h, p = a.split(':')
        try:
            return h.strip(), int(p)
        except ValueError:
            return h.strip(), NET_PORT
    return a, NET_PORT


class Net:
    """اتصال TCP بالسيرفر. Thread للقراية وThread للكتابة، واللعبة بتسحب الرسايل كل فريم (مفيش تهنيج)"""

    def __init__(self):
        self.inq, self.outq = queue.Queue(), queue.Queue()
        self.sock, self.alive, self.gen = None, False, 0

    def connect(self, addr, first):
        self.close()
        self.inq, self.outq = queue.Queue(), queue.Queue()
        self.gen += 1
        host, port = parse_addr(addr)
        threading.Thread(target=self._run, args=(self.gen, host, port, first), daemon=True).start()

    def _run(self, gen, host, port, first):
        inq, outq = self.inq, self.outq
        try:
            sock = socket.create_connection((host, port), timeout=6)
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            sock.settimeout(None)
        except Exception:
            if gen == self.gen:
                inq.put({'t': '_err'})
            return
        if gen != self.gen:
            sock.close()
            return
        self.sock, self.alive = sock, True
        outq.put(first)
        threading.Thread(target=self._writer, args=(gen, sock, outq), daemon=True).start()
        buf = b''
        try:
            while gen == self.gen:
                data = sock.recv(8192)
                if not data:
                    break
                buf += data
                while b'\n' in buf:
                    line, buf = buf.split(b'\n', 1)
                    try:
                        m = json.loads(line.decode('utf-8'))
                    except ValueError:
                        continue
                    if isinstance(m, dict):
                        inq.put(m)
                if len(buf) > 65536:
                    break
        except Exception:
            pass
        if gen == self.gen:
            self.alive = False
            inq.put({'t': '_closed'})

    def _writer(self, gen, sock, outq):
        while gen == self.gen:
            try:
                d = outq.get(timeout=0.5)
            except queue.Empty:
                continue
            try:
                sock.sendall((json.dumps(d, separators=(',', ':'), ensure_ascii=False) + "\n").encode('utf-8'))
            except Exception:
                break

    def send(self, d):
        if self.alive:
            self.outq.put(d)

    def poll(self):
        out = []
        while True:
            try:
                out.append(self.inq.get_nowait())
            except queue.Empty:
                return out

    def close(self):
        self.gen += 1
        self.alive = False
        sk, self.sock = self.sock, None
        if sk:
            try:
                sk.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                sk.close()
            except Exception:
                pass


PEER_TINTS = [(0, 0, 0), (70, 0, 0), (0, 55, 0), (0, 25, 85), (70, 55, 0), (0, 55, 55), (80, 28, 0), (60, 60, 60)]
PEER_COLS = [(235, 235, 235), (255, 110, 110), (120, 235, 120), (130, 170, 255), (240, 220, 110), (110, 230, 230),
             (255, 170, 90), (200, 200, 200)]


class Game:
    _fear = 0.0
    fear_full = False          # اتملى العداد (بنفتكرها لحد ما update يشوفها، حتى لو الخوف هدي في نفس اللحظة)

    def __init__(self):
        self.state = 'title'
        self.help_prev = 'title'
        self.ang = -math.pi / 2           # اتجاه النظر (منظور أول)
        self.fp = fp3d.FP(SW, SH, TOUCH)
        self.fp_peek = {}
        self.running = False
        self.dark = pygame.Surface((SW, SH), pygame.SRCALPHA)
        self.t = 0.0
        self.sel = 0
        self.btns = []
        self.js_t, self.js_after, self.js_text, self.js_face = 0.0, None, "", None
        self.shake = 0.0
        self.toast_s, self.toast_t = "", 0.0
        self.dlg, self.dlg_title, self.dlg_close = None, "", None
        self.later = []
        self.app = None
        self.say = None
        self.bday_done = False
        self.field = 0
        self.form = {'name': '', 'day': '', 'month': ''}
        self.form_err = ""
        self.trans_t = 0.0
        self.next_n = 1
        self.win_t = 0.0
        self.lv = None
        self.level = 1
        self.objs = []
        self.opened = set()
        self.inv = set()
        self.done = set()
        self.ghosts = []
        self.spare, self.battery, self.fear = 0, 100.0, 0.0
        self.js_dur = 1.5
        self.eyes, self.decals, self.dash, self.hall = [], [], None, None
        self.out_c = set()
        self.glitch_t = 0.0
        self.was_moving = False
        self.eye_cd = self.snuff_cd = self.sc_cd = self.phantom_cd = 10.0
        self.joy, self.joy_run, self.kb_lang = (0.0, 0.0), False, 'ar'      # الجويستيك + لغة كيبورد الشاشة
        self._fear = 0.0
        self.emo = {}                                  # التعبيرات: اسم -> الوقت الباقي
        self.hurt_t = 0.0
        self.dying, self.lose_t, self.lose_why = False, 0.0, ""
        self.lvl_spare, self.lvl_battery = 0, 100.0
        # ---- أونلاين
        self.net, self.net_on = None, False
        self.room_id, self.my_id, self.host_id, self.room_seed = "", None, None, 0
        self.players, self.peers, self.pending_ev = {}, {}, []
        self.boss_on, self.pulse = False, 0.0
        self.inp, self.online_err, self.conn_t, self.ping_t, self.pos_t = "", "", 0.0, 0.0, 0.0
        self.after_profile, self.local_srv_msg = None, ""
        self.dead_ids, self.wipe_pending = set(), False
        self.chat, self.chat_open, self.chat_buf, self.chat_skip = [], False, "", False
        self.gchat_t = random.uniform(40, 80)
        self.mimic, self.mimic_t, self.step_cd = None, random.uniform(50, 90), random.uniform(15, 30)
        self.spec_i, self.cam = 0, (0.0, 0.0)
        self.profile = None
        self.saved = None
        d = load_save()
        if d:
            self.profile, self.saved = d['profile'], d.get('game')

    # ------------------------------------------------ أدوات
    def name(self):
        return (self.profile or {}).get('name', "يا غريب")

    def toast(self, s, sec=3.0):
        self.toast_s, self.toast_t = s, sec

    def dialog(self, title, lines, on_close=None):
        self.dlg = list(lines)
        self.dlg_title, self.dlg_close = title, on_close

    def close_dialog(self):
        fn = self.dlg_close
        self.dlg = self.dlg_close = None
        if fn:
            fn()

    def after(self, sec, fn):
        self.later.append([sec, fn])

    def flash_ok(self):
        return self.flash and self.battery > 0 and self.blackout <= 0

    def is_bday(self):
        p = self.profile
        d = datetime.date.today()
        return bool(p) and d.day == p['day'] and d.month == p['month']

    def maybe_birthday(self):
        if self.is_bday() and not self.bday_done:
            self.bday_done = True
            self.scare('face', text=BDAY_TEXT)

    def voice(self, vol=1.0, kind='voice'):
        if not AUDIO:
            return
        s = SND.get(kind) or SND.get('voice')
        if s is None:
            play('whisper', vol * 0.8)
        elif s.get_num_channels() == 0:
            s.set_volume(max(0.0, min(1.0, vol * MASTER)))
            s.play()

    def name_line(self, nm=None):
        return S(random.choice(NAME_LINES), n=nm or self.name())

    def target_name(self):
        """اللاعب اللي الوحش هينادي عليه (أونلاين: واحد من كل اللاعبين)"""
        names = [n for n in self.players.values() if n] if self.net_on else []
        return random.choice(names) if names else self.name()

    def say_name(self, vol, name, mk=None):
        """الوحش بينطق الاسم بوضوح، وطبقة الصوت بتختلف حسب نوع الوحش"""
        if not AUDIO:
            return
        beh = mon_of(mk).get('beh', 'plain') if mk is not None else 'plain'
        vt = {'doll': 'c', 'demon': 'd', 'flesh': 'd', 'tall': 'd', 'zombie': 'd', 'fire': 'd'}.get(beh, 'n')
        s = SND.get('vn:%s:%s' % (name, vt)) or SND.get('vn:%s:n' % name)
        if s is None:                                   # الصوت لسه مجهزش
            if name == self.name():
                self.voice(vol, 'voice')
            else:
                play('whisper', vol * 0.5)
        elif s.get_num_channels() == 0:
            s.set_volume(max(0.0, min(1.0, vol * MASTER)))
            s.play()

    @property
    def fear(self):
        return self._fear

    @fear.setter
    def fear(self, v):
        old = self._fear
        if v > old:
            v = old + (v - old) * FEAR_GAIN
        self._fear = max(0.0, min(100.0, v))
        if self._fear >= 100.0:
            self.fear_full = True

    # ------------------------------------------------ التعبيرات
    def emote(self, name, sec):
        if self.emo.get(name, 0) < sec:
            self.emo[name] = sec

    def expression(self):
        """الوش اللي بيظهر في الشاشة: بيتغير حسب اللي بيحصل"""
        if self.state == 'lose':
            return 'scared' if self.lose_t < 1.6 else 'sad'
        for n in ('surprised', 'scared', 'angry', 'sad', 'happy'):
            if self.emo.get(n, 0) > 0:
                return n
        return 'scared' if self.fear >= 50 else 'neutral'

    # ------------------------------------------------ جلسة ومراحل
    def new_session(self):
        self.spare, self.battery, self.fear = 0, 100.0, 0.0
        self.game_seed = random.randint(1, 10 ** 6)              # كل لعبة جديدة: شقق وأماكن مفاتيح مختلفة
        self.start_level(1)

    def start_level(self, n):
        self.level = n
        seed = self.room_seed if self.net_on else (getattr(self, 'game_seed', None) or self.profile['seed'])
        self.lv = build_level1(seed) if n == 1 else gen_level(n, seed)
        self.objs = self.lv.objs
        place_story(self.objs, n, seed)
        self.px, self.py = self.lv.start
        self.fx, self.fy = 0, -1
        self.ang = -math.pi / 2
        self.fp_peek = {}
        self.inv, self.done, self.opened = set(), set(), set()
        self.ghosts = []
        self.boss_on, self.pulse = False, 0.0
        D = diff(n)
        self.ghost_cd = D['gcd'] + 12
        self.cd = 10.0
        self.blackout = 0.0
        self.flash = True
        self.dead_warned = False
        self.later = []
        self.app = self.say = None
        self.amb = random.uniform(0.7, 1.2) * D['amb']
        self.step_t = self.heart_t = 0.0
        self.voice_cd = 6.0
        self.visited = set()
        self.show_map = False
        self.moving = False
        self.eyes, self.decals, self.dash, self.hall = [], [], None, None
        self.out_c = set()
        self.glitch_t = 0.0
        self.was_moving = False
        self.eye_cd = random.uniform(10, 20)
        self.snuff_cd = random.uniform(25, 40)
        self.sc_cd = 15.0
        self.phantom_cd = 20.0
        self.joy, self.joy_run = (0.0, 0.0), False
        apply_volume()
        if TOUCH and n == 1:
            self.toast("حرّك الجويستيك للمشي... وزر التفاعل لفتح الحاجات.", 6)
        self.fear = min(self.fear, 25.0)
        self.emo = {}
        self.hurt_t = 0.0
        self.dying = False
        self.fear_full = False
        self.lvl_spare, self.lvl_battery = self.spare, self.battery
        self.room = self.lv.rooms[0][0]
        self.dlg = None
        self.toast(S("{t} - عدد الأوض: {n}", t=self.lv.title, n=len(self.lv.rooms)), 4)

    def snapshot(self):
        return dict(profile=self.profile, game=dict(
            seed=getattr(self, 'game_seed', None), level=self.level, px=self.px, py=self.py, fx=self.fx, fy=self.fy, inv=sorted(self.inv),
            spare=self.spare, battery=self.battery, fear=self.fear, done=sorted(self.done),
            opened=sorted(self.opened), visited=sorted(self.visited),
            fired=[i for i, t in enumerate(self.lv.triggers) if t['fired']]))

    def save(self, silent=False):
        if self.net_on or self.state == 'lose':
            if not silent:
                self.toast("الحفظ مش متاح أونلاين", 2.5)
            return False
        ok = write_save(self.snapshot())
        if not silent:
            self.toast("تم حفظ اللعبة" if ok else "مقدرتش أحفظ الملف!", 2.5)
        return ok

    def load_game(self):
        g = self.saved
        self.spare, self.battery, self._fear = g['spare'], g['battery'], min(float(g['fear']), 60.0)
        self.game_seed = g.get('seed') or self.profile['seed']
        self.start_level(g['level'])
        self.px, self.py, self.fx, self.fy = g['px'], g['py'], g['fx'], g['fy']
        self.ang = math.atan2(self.fy, self.fx) if (self.fx or self.fy) else -math.pi / 2
        self.inv, self.done, self.opened = set(g['inv']), set(g['done']), set(g['opened'])
        for o in self.objs:
            if o.id in self.opened:
                o.solid = o.can = False
        self.visited = set(g.get('visited', []))
        for i in g['fired']:
            if i < len(self.lv.triggers):
                self.lv.triggers[i]['fired'] = True
        self.toast(S("أهلًا بيك تاني يا {n}...", n=self.name()), 3)

    def go_next(self):
        play('unlock')
        self.emote('happy', 4)
        if self.net_on:                                   # السيرفر هو اللي بيقول للكل يروحوا الشقة اللي بعدها
            self.net_send(dict(t='next', **{'from': self.level}))
            return
        if self.level >= MAX_LEVEL:
            self.state, self.win_t = 'win', 0.0
        else:
            self.state, self.trans_t, self.next_n = 'trans', 0.0, self.level + 1

    def update_trans(self, dt):
        self.trans_t += dt
        if self.trans_t > 3.4:
            self.start_level(self.next_n)
            self.state = 'play'
            if self.net_on:
                self.spread_start()
                for k, v in self.pending_ev:
                    self.apply_ev(k, v)
                self.pending_ev = []
            else:
                self.save(silent=True)

    # ------------------------------------------------ الخسارة
    def lose(self, why, mk=None):
        """الخوف اتملى أو وحش لمسك: خضّة بوحش، وبعدها شاشة الخسارة"""
        if self.dying or self.state not in ('play', 'pause'):
            return
        self.dying, self.lose_why = True, why
        self.fear_full = False
        mk = rand_mk() if mk is None else mk
        self.js_face = A['js'][mk % len(A['js'])]
        self.js_t = self.js_dur = 1.8
        self.js_after, self.js_text = self.lose_screen, ""
        self.dlg = None
        self.later = []
        self.shake = 1.0
        self._fear = 100.0
        play('shriek')
        play('scare')
        play('boom', 0.9)
        ms = MON_SOUND.get(mk % nmon())
        if ms:
            play(ms, 0.8)
        self.voice(1.0, 'v_choir')
        self.emote('surprised', 1.0)
        self.emote('scared', 3.0)
        if self.net_on:
            self.dead_ids.add(self.my_id)
            self.net_send(dict(t='lose'))

    def lose_screen(self):
        self.state, self.lose_t = 'lose', 0.0
        self.cam, self.spec_i = (self.px, self.py), 0
        self.js_after = None
        self.dlg = None

    def update_lose(self, dt):
        self.t += dt
        self.lose_t += dt
        self.shake = max(0.0, self.shake - dt)
        if self.toast_t > 0:
            self.toast_t -= dt
        if self.wipe_pending and self.lose_t > 2.8:
            self.do_wipe()
        elif not self.net_on and self.lose_t > 9.0:
            self.retry()

    def retry(self):
        """أوفلاين: نعيد الشقة من الأول بنفس البطاريات اللي دخلنا بيها"""
        self.dying = False
        self.spare, self.battery = self.lvl_spare, self.lvl_battery
        self._fear = 0.0
        self.start_level(self.level)
        self.state = 'play'

    def do_wipe(self):
        """أونلاين: كل اللاعبين ماتوا، الفريق كله بيعيد الشقة"""
        self.wipe_pending, self.dying = False, False
        self.dead_ids = set()
        self.js_t, self.js_after, self.dlg = 0.0, None, None
        self.spare, self.battery, self._fear = self.lvl_spare, self.lvl_battery, 0.0
        self.pending_ev = []
        self.start_level(self.level)
        self.spread_start()
        self.state = 'play'
        self.toast("كلكم خسرتوا... الشقة بتبدأ من الأول!", 4)

    def spread_start(self):
        """أونلاين: كل لاعب بيبدأ في مكان جنب التاني"""
        if not self.net_on:
            return
        ids = sorted(self.players)
        idx = ids.index(self.my_id) if self.my_id in ids else 0
        sx, sy = self.lv.start
        offs = [(0, 0), (22, 0), (-22, 0), (0, 22), (22, 22), (-22, 22), (0, -22), (44, 0)]
        for dx, dy in offs[idx % 8:] + offs[:idx % 8]:
            if not self.blocked(pygame.Rect(int(sx + dx) - 10, int(sy + dy) - 10, 20, 20)):
                self.px, self.py = sx + dx, sy + dy
                return

    # ------------------------------------------------ أونلاين
    def net_send(self, d):
        if self.net:
            self.net.send(d)

    def net_ev(self, k, v):
        if self.net_on:
            self.net_send(dict(t='ev', k=k, v=v))

    def apply_ev(self, k, v):
        if k == 'done':
            self.done.add(v)
        elif k == 'inv':
            self.inv.add(v)
        elif k == 'open':
            self.opened.add(v)
            for o in self.objs:
                if o.id == v:
                    o.solid = o.can = False

    def start_connect(self, first):
        if not parse_addr(SERVER_ADDR)[0]:
            self.online_err = "اكتب عنوان السيرفر الأول (أو شغّل سيرفر على جهازك)."
            return
        if not self.net:
            self.net = Net()
        self.online_err = ""
        self.net.connect(SERVER_ADDR, dict(first, name=self.name()))
        self.state, self.conn_t = 'connecting', 0.0

    def net_close(self):
        self.chat, self.chat_open = [], False
        if self.net:
            self.net.close()
        self.net_on = False
        self.peers, self.players, self.pending_ev = {}, {}, []
        self.dead_ids, self.wipe_pending = set(), False
        self.room_id = ""

    def leave_online(self, to='online'):
        self.net_close()
        self.dying = False
        self.js_t, self.js_after = 0.0, None
        self.state = to

    def begin_online(self, level, shared=None):
        self.net_on = True
        self.peers, self.pending_ev = {}, []
        self.dying, self.wipe_pending = False, False
        self.spare, self.battery, self._fear = 0, 100.0, 0.0
        self.fear_full = False
        self.start_level(level)
        for k, v in (shared or {}).items():
            for it in v:
                self.apply_ev(k, it)
        self.spread_start()
        self.state = 'play'
        self.toast(S("الغرفة {r}  -  بالتوفيق!", r=self.room_id), 4)

    def remote_next(self, level):
        self.dying, self.wipe_pending = False, False
        self.dead_ids = set()
        self.js_t, self.js_after, self.dlg = 0.0, None, None
        self.emote('happy', 4)
        self.state, self.trans_t, self.next_n = 'trans', 0.0, level

    def pname(self, pid):
        return self.players.get(pid, "لاعب")

    def net_msg(self, m):
        t = m.get('t')
        if t == 'room':
            self.net_on = True
            self.my_id, self.host_id, self.room_id = m.get('you'), m.get('host'), str(m.get('room'))
            self.players = {int(p[0]): str(p[1]) for p in m.get('players', [])}
            prepare_names_async(list(self.players.values()))
            self.room_seed = int(m.get('seed', 1))
            self.dead_ids = set(m.get('dead', []))
            if m.get('started'):
                self.begin_online(int(m.get('level', 1)), m.get('shared'))
            else:
                self.state = 'lobby'
        elif t == 'joined':
            self.players[m['id']] = str(m.get('name', ''))
            prepare_names_async([self.players[m['id']]])
            self.toast(S("{n} دخل الغرفة", n=self.pname(m['id'])), 2.5)
        elif t == 'left':
            nm = self.pname(m['id'])
            self.players.pop(m['id'], None)
            self.peers.pop(m['id'], None)
            self.dead_ids.discard(m['id'])
            self.host_id = m.get('host', self.host_id)
            self.toast(S("{n} خرج من الغرفة", n=nm), 2.5)
        elif t == 'start':
            self.begin_online(int(m.get('level', 1)))
        elif t == 'pos':
            pid = m['id']
            p = self.peers.get(pid)
            if p is None:
                p = self.peers[pid] = dict(id=pid, x=m['x'], y=m['y'])
            p.update(tx=m['x'], ty=m['y'], fx=m['fx'], fy=m['fy'], mv=m['mv'], fl=m['fl'], ex=m.get('ex', 'neutral'),
                     lv=m['lv'], ls=m.get('ls', 0), gh=m.get('gh', []))
            if p['lv'] != self.level:
                p['x'], p['y'] = m['x'], m['y']
        elif t == 'ev':
            if self.state == 'trans':
                self.pending_ev.append((m['k'], m['v']))
            else:
                self.apply_ev(m['k'], m['v'])
                if m['k'] == 'inv':
                    self.toast(S("{n} لقى حاجة مهمة!", n=self.pname(m['id'])), 3)
                    self.emote('happy', 2)
        elif t == 'chat':
            self.chat_add(self.pname(m['id']), str(m.get('text', ''))[:100], PEER_COLS[m['id'] % 8])
        elif t == 'lose':
            self.dead_ids.add(m['id'])
            self.toast(S("{n} خسر! لازم تكملوا من غيره...", n=self.pname(m['id'])), 3.5)
            if self.state == 'play' and self.js_t <= 0 and not self.dying:      # موت صاحبك بيرعبك
                play('whisper', 0.8)
                self.scare('flicker')
        elif t == 'wipe':
            if self.dying:
                self.wipe_pending = True
            else:
                self.do_wipe()
        elif t == 'next':
            self.remote_next(int(m['level']))
        elif t == 'win':
            self.dying = False
            self.state, self.win_t = 'win', 0.0
        elif t == 'err':
            self.online_err = {'notfound': "مفيش غرفة بالرقم ده.", 'full': "الغرفة مليانة (8 لاعبين).",
                               'busy': "السيرفر مشغول، جرّب كمان شوية."}.get(m.get('msg'), "حصل خطأ.")
            self.net_close()
            self.state = 'online'
        elif t == '_err':
            self.online_err = S("مقدرتش أوصل للسيرفر: {a}", a=SERVER_ADDR)
            self.net_close()
            self.state = 'online'
        elif t == '_closed':
            ingame = self.state in ('play', 'pause', 'trans', 'lose', 'win')
            self.online_err = "اتقطع الاتصال بالسيرفر."
            self.leave_online('title' if ingame else 'online')

    def net_tick(self, dt):
        if not self.net:
            return
        for m in self.net.poll():
            self.net_msg(m)
        if not self.net_on:
            if self.state == 'connecting':
                self.conn_t += dt
                if self.conn_t > 12:
                    self.online_err = S("مقدرتش أوصل للسيرفر: {a}", a=SERVER_ADDR)
                    self.net_close()
                    self.state = 'online'
            return
        self.pos_t -= dt
        if self.pos_t <= 0:
            self.pos_t = 0.08
            if self.state in ('play', 'pause', 'trans', 'lose'):
                self.net_send(dict(t='pos', x=round(self.px, 1), y=round(self.py, 1), fx=round(self.fx, 2),
                                   fy=round(self.fy, 2), mv=int(self.moving and self.state == 'play'),
                                   fl=int(self.flash_ok()), ex=self.expression(), lv=self.level,
                                   gh=[[round(g['x']), round(g['y']), round(max(0.0, min(1.0, g['a'])), 2), g.get('mk', 0)]
                                       for g in self.ghosts if g['a'] > 0.15][:3]))
            else:
                self.ping_t -= 0.08
                if self.ping_t <= 0:
                    self.ping_t = 8.0
                    self.net_send(dict(t='ping'))
        k = min(1.0, dt * 12)
        for p in self.peers.values():
            p['x'] += (p['tx'] - p['x']) * k
            p['y'] += (p['ty'] - p['y']) * k

    # ------------------------------------------------ الشات
    def open_chat(self):
        if not self.net_on or self.chat_open:
            return
        self.chat_open, self.chat_buf, self.chat_skip = True, "", True
        if not TOUCH:
            pygame.key.start_text_input()

    def close_chat(self):
        self.chat_open = False
        if not TOUCH:
            pygame.key.stop_text_input()

    def chat_add(self, name, text, col=(235, 235, 235), ghost=False):
        self.chat.append(dict(n=name, x=text, t=self.t, c=col, g=ghost))
        del self.chat[:-30]

    def send_chat(self, text):
        text = text.strip()[:100]
        if not text or not self.net_on:
            return
        self.chat_add(self.name(), text, PEER_COLS[(self.my_id or 0) % 8])
        self.net_send(dict(t='chat', text=text))

    def chat_event(self, e):
        """وهو الشات مفتوح: الكيبورد كله بيروح له. بيرجّع True لو الحدث اتاكل"""
        if e.type == pygame.TEXTINPUT:
            if self.chat_skip:                       # الحرف T اللي فتح الشات نفسه
                self.chat_skip = False
                if e.text in ('t', 'T', 'ف'):
                    return True
            self.chat_buf = (self.chat_buf + e.text.replace("\n", ""))[:100]
            return True
        if e.type == pygame.KEYDOWN:
            k = e.key
            if k == pygame.K_ESCAPE:
                self.close_chat()
            elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.send_chat(self.chat_buf)
                self.close_chat()
            elif k == pygame.K_BACKSPACE:
                self.chat_buf = self.chat_buf[:-1]
            return True
        return None

    def update_mimic(self, dt):
        """فخ: "صاحبك" واقف في الضلمة مستنيك... لو قربت منه يطلع وحش"""
        m = self.mimic
        if m:
            m['age'] += dt
            dx, dy = self.px - m['x'], self.py - m['y']
            d = math.hypot(dx, dy) or 1.0
            m['fx'], m['fy'] = dx / d, dy / d
            if d < 120:
                self.mimic = None
                self.scare('face')
                self.chat_add("؟؟؟", "قلتلك... ده مش " + self.pname(m['pid']), (210, 30, 30), ghost=True)
            elif m['age'] > 30 or d > 1100:
                self.mimic = None
            return
        self.mimic_t -= dt
        if self.mimic_t > 0 or self.level < 2 or self.dying:
            return
        self.mimic_t = random.uniform(70, 130)
        al = self.alive_peers()
        if not al:
            return
        for _ in range(60):
            tx, ty = random.choice(self.lv.floors)
            x, y = tx * T + 16, ty * T + 16
            if 380 < math.hypot(x - self.px, y - self.py) < 650:
                self.mimic = dict(x=x, y=y, pid=random.choice(al)['id'], age=0.0, fx=0.0, fy=1.0)
                return

    def ghost_chat(self):
        """رسالة في الشات من "؟؟؟": البيت بيكلّمكم"""
        names = list(self.players.values()) or [self.name()]
        line = random.choice(GHOST_CHAT).replace("{name}", random.choice(names))
        self.chat_add("؟؟؟", line, (210, 30, 30), ghost=True)
        play('whisper', 0.6)
        self.fear = self.fear + 4
        self.glitch_t = max(self.glitch_t, 0.25)

    def glitched(self, text, i):
        """الخوف عالي: الرسايل بتبوظ حروفها"""
        if self.fear < 60:
            return text
        rr = random.Random(int(self.t * 6) * 7919 + i)
        k = (self.fear - 50) / 400.0
        return ''.join(rr.choice("█▓؟#") if (c != ' ' and rr.random() < k) else c for c in text)

    def draw_chat(self, s):
        shown = [m for m in self.chat if self.chat_open or self.t - m['t'] < 14]
        shown = shown[-8:]
        base = SH - 78 - (44 if self.chat_open and not TOUCH else 0)
        for i, m in enumerate(reversed(shown)):
            age = self.t - m['t']
            k = 1.0 if (self.chat_open or age < 10) else max(0.25, 1 - (age - 10) / 4)
            col = tuple(int(c * k) for c in m['c'])
            line = "%s: %s" % (m['n'], m['x'] if m['g'] else self.glitched(m['x'], i))
            if m['g'] and random.random() < 0.06:
                line = self.glitched(line, i + 99)
            draw_text(s, line, 18, col, 16, base - i * 22, 'l')
        if self.chat_open:
            if TOUCH:
                for i, ph in enumerate(CHAT_QUICK):
                    r = pygame.Rect(SW // 2 - 260 + (i % 2) * 270, 150 + (i // 2) * 58, 250, 50)
                    self.draw_button(s, ph, r, False, 20)
                    self.btns.append((r, 'q:%d' % i))
                r = pygame.Rect(SW // 2 - 125, 330, 250, 46)
                self.draw_button(s, "إغلاق", r, False, 20)
                self.btns.append((r, 'qx'))
            else:
                box = pygame.Rect(12, SH - 52, 600, 34)
                pygame.draw.rect(s, (14, 10, 12), box, border_radius=6)
                pygame.draw.rect(s, (200, 150, 80), box, 2, border_radius=6)
                caret = "|" if int(self.t * 2) % 2 == 0 else ""
                draw_text(s, self.chat_buf + caret, 20, (255, 240, 210), 20, SH - 49, 'l')
                draw_text(s, "Enter: إرسال   |   Esc: إلغاء", 14, (140, 140, 140), 16, SH - 70, 'l')

    def extra_ghosts(self):
        """أونلاين: كل 3 لاعبين زيادة = وحش زيادة"""
        return (len(self.players) - 1) // 3 if self.net_on else 0

    def alive_peers(self):
        return [p for p in self.peers.values() if p['id'] not in self.dead_ids and p['lv'] == self.level]

    def spec_list(self):
        return sorted(self.alive_peers(), key=lambda p: p['id'])

    def cam_pos(self):
        """اللاعب الميت بيتفرّج على صحابه (وبيبدّل بينهم)"""
        if self.state == 'lose' and self.net_on:
            sl = self.spec_list()
            if sl:
                p = sl[self.spec_i % len(sl)]
                cx, cy = self.cam
                self.cam = (cx + (p['x'] - cx) * 0.12, cy + (p['y'] - cy) * 0.12)
                return self.cam
        return self.px, self.py

    # ------------------------------------------------ خضّات
    def scare(self, kind, after=None, text=""):
        D = diff(getattr(self, 'level', 1))
        self.cd = max(self.cd if hasattr(self, 'cd') else 0, D['cd'])
        self.emote('surprised', 1.8 if kind == 'face' else 1.0)
        self.emote('scared', 5.0 if kind == 'face' else 3.5)
        if kind in ('face', 'flash'):
            dur = 1.5 if kind == 'face' else 0.32
            self.js_t = self.js_dur = dur
            self.js_after, self.js_text = after, text
            self.js_face = A['js'][random.randrange(len(A['js']))]
            self.fear = (self.fear + (22 if kind == 'face' else 8))
            self.shake = 0.6
            play(random.choice(('scare', 'shriek')) if kind == 'face' else 'static')
            if kind == 'face' and text and text == self.name():
                self.voice(1.0, 'v_choir')
            if kind == 'face':
                self.after(dur + 0.4, lambda: play('breath', 0.7))
                self.after(dur, lambda: setattr(self, 'hurt_t', 0.9))
                if self.level >= 3 and random.random() < 0.2:          # خضّة تانية بعد ما تهدا
                    self.after(dur + 3.2, lambda: self.scare('flash'))
        elif kind == 'bang':
            play('bang')
            self.shake = 0.5
            self.fear = (self.fear + 14)
            self.toast("حاجة وقعت وراك!!", 2.5)
            self.app = [self.px - self.fx * 150, self.py - self.fy * 150, 0.45, rand_mk()]
            if self.level >= 2 and random.random() < 0.4:
                self.after(1.2, lambda: play('laugh', 0.6))
        elif kind == 'flicker':
            self.blackout = 3.0
            self.fear = (self.fear + 10)
            play('whisper', 0.9)
            self.toast("كل الأنوار طفت!...", 3)
            self.after(1.4, lambda: play('step', 0.6))
            self.after(2.0, lambda: play('creak', 0.6))
            self.after(2.5, lambda: play('breath', 0.7))
            if self.level >= 4 and random.random() < 0.5:
                self.after(3.1, lambda: self.spawn_ghost(near=True, force=True))
        elif kind == 'name':
            self.name_sequence()
        elif kind == 'near':
            self.fear = (self.fear + 8)
            play('whisper', 0.8)
            self.spawn_ghost(near=True, force=True)
        elif kind == 'dash':                       # ضلّ بيجري قدامك بسرعة
            self.dash = dict(t=0.0, dur=0.55, dir=random.choice((-1, 1)), mk=rand_mk())
            play('shriek', 0.8)
            play('bang', 0.5)
            self.shake = 0.5
            self.fear = (self.fear + 14)
        elif kind == 'knock':                      # خبط من جوه الحيطة
            play('knock', 1.0)
            self.shake = 0.3
            self.fear = (self.fear + 8)
            self.toast("حد بيخبط... من جوه الحيطة!", 3)
            if self.level >= 3 and random.random() < 0.4:
                self.after(2.0, lambda: self.scare('name'))
        elif kind == 'eyes':                       # عيون في الضلمة
            self.fear = (self.fear + 6)
            self.spawn_eyes(random.choice((2, 3)), 160, 380)
            self.toast("حاسس إن في عيون بتبصلك من الضلمة...", 3)
        elif kind == 'roar':                       # زئير ووحش بيجري قدامك
            self.dash = dict(t=0.0, dur=0.7, dir=random.choice((-1, 1)), mk=rand_mk())
            play(random.choice(('roar', 'growl')), 1.0)
            play('thunder', 0.5)
            play('boom', 0.7)
            self.shake = 0.7
            self.fear = (self.fear + 16)
            self.toast("سمعت زئير مرعب!!", 2.5)
        elif kind == 'scream':                     # صرخة ست قريبة وبعدها وش
            play('scream', 1.0)
            self.shake = 0.4
            self.fear = (self.fear + 12)
            self.toast("صرخة... قريبة جداً!", 2.5)
            self.after(0.9, lambda: self.scare('flash') if (self.state == 'play' and self.js_t <= 0) else None)
        elif kind == 'chorus':                     # ضلمة وكورال شياطين ووحش ورا ضهرك
            self.blackout = 3.5
            self.fear = (self.fear + 12)
            play('choir', 0.9)
            play('chant', 0.6)
            play('wind', 0.6)
            self.toast("أصوات كتير بتهمس في ودنك...", 3)
            self.after(2.0, lambda: self.spawn_ghost(near=True, force=True))
        elif kind == 'crawl':                      # حاجة بتزحف وراك
            play('scratch', 0.9)
            self.after(0.6, lambda: play('dragging', 0.8))
            self.after(1.4, lambda: play('hiss', 0.9))
            self.fear = (self.fear + 12)
            self.shake = 0.3
            self.toast("حاجة بتزحف ورا ضهرك...", 3)
            self.app = [self.px - self.fx * 110, self.py - self.fy * 110, 0.9, rand_mk()]
        elif kind == 'watch':                      # شبح بيتحرك لما تدير ضهرك
            if self.spawn_watcher():
                self.fear = (self.fear + 6)
            else:
                self.scare('near')

    def name_sequence(self):
        """أرعب نداء: صمت تام... نفس... اسمك بالمقلوب... همس في ودنك... الاسم بيتكتب حرف حرف...
        وبعدين كورال شياطين من ورا ضهرك... وآخرها وش بيصرخ باسمك"""
        nm = self.name()
        self.cd = max(self.cd, 45)
        self.fear = (self.fear + 15)
        self.blackout = 6.0                                   # ضلمة تامة
        self.heart_t = 5.0
        if AUDIO and 'drone' in SND:
            SND['drone'].set_volume(0)                        # الصمت قبل العاصفة
        self.after(0.6, lambda: play('breath', 0.9))
        self.after(1.8, lambda: self.voice(0.55, 'v_rev'))    # الاسم بالمقلوب
        self.after(3.2, lambda: (self.voice(0.85, 'v_whisper'), play('creak', 0.5)))
        gap = min(0.22, 1.8 / max(1, len(nm)))
        for i in range(1, len(nm) + 1):                       # الاسم بيتكتب قدامك حرف حرف
            self.after(3.4 + gap * i, lambda i=i: setattr(self, 'say', [nm[:i], 2.2]))

        def behind():
            self.shake = 1.0
            self.fear = (self.fear + 25)
            self.voice(1.0, 'v_choir')
            play('bang', 0.6)
            play('heart', 1.0)
            self.after(0.45, lambda: play('heart', 1.0))
            self.app = [self.px - self.fx * 70, self.py - self.fy * 70, 1.6, rand_mk()]
            self.say = [nm, 2.4]
        self.after(5.4, behind)
        self.after(7.6, lambda: apply_volume())
        self.after(8.4, lambda: self.voice(0.9, 'v_child'))   # من ناحية تانية
        self.after(10.2, lambda: self.scare('face', text=nm))  # وش بيصرخ باسمك

    def roll_scare(self):
        """احتمال خضّة وإنت بتقلّب في حاجة (بتزيد مع المراحل)"""
        if self.cd > 0 or random.random() > min(0.35, 0.08 + 0.025 * self.level):
            return None
        pool = ['face', 'face', 'bang', 'bang', 'flicker', 'flicker', 'dash', 'knock', 'eyes']
        if self.level >= 2:
            pool += ['scream', 'crawl']
        if self.level >= 3:
            pool += ['roar', 'chorus']
        return random.choice(pool)

    def ambient(self, kind):
        play(kind, 0.6 if kind in ('creak', 'whisper', 'step') else 0.8)
        if kind in ('slam', 'knock'):
            self.shake = max(self.shake, 0.3)
        self.toast(AMB_TEXT[kind], 3)
        self.fear = (self.fear + (5 if kind in LOUD_AMB else 3))

    def first_visit(self):
        """أول مرة تدخل أوضة: ساعات حاجة بتحصل"""
        if self.sc_cd > 0 or self.cd > 3:
            return
        if random.random() < (0.22 if self.level == 1 else 0.38):
            self.sc_cd = random.uniform(20, 35)
            kinds = ['slam', 'slam', 'knock', 'breath'] + extra_amb(self.level)
            if self.level >= 2:
                kinds += ['laugh', 'cry']
            if self.level >= 3:
                kinds.append('musicbox')
            k = random.choice(kinds)
            if k == 'slam':
                play('slam', 0.9)
                self.shake = 0.35
                self.toast("الباب اتقفل وراك بقوة!", 3)
                self.fear = (self.fear + 6)
            else:
                self.ambient(k)

    def dark_company(self):
        """الكشاف مات... والضلمة مش فاضية"""
        if self.flash_ok():
            return
        play('breath', 0.9)
        self.toast("في الضلمة... حد بيتنفّس جنبك.", 3)
        self.fear = (self.fear + 8)
        self.emote('sad', 4)
        self.after(2.2, lambda: None if self.flash_ok() else self.scare('near'))

    def wall_at(self, x, y):
        tx, ty = int(x // T), int(y // T)
        lv = self.lv
        return tx < 0 or ty < 0 or tx >= lv.W or ty >= lv.H or lv.grid[ty][tx] == 1

    def spawn_eyes(self, n=2, dmin=170, dmax=420):
        if len(self.eyes) >= 4:
            return
        tx, ty = int(self.px // T), int(self.py // T)
        rect = None
        for _nm, (x, y, w, h), _c in self.lv.rooms:
            if x <= tx < x + w and y <= ty < y + h:
                rect = (x, y, w, h)
                break
        if not rect:
            return
        x0, y0, w, h = rect
        for _ in range(n):
            for _t in range(40):
                ex = (x0 + random.randrange(w)) * T + 16
                ey = (y0 + random.randrange(h)) * T + 16
                d = math.hypot(ex - self.px, ey - self.py)
                if dmin <= d <= dmax and not self.blocked(pygame.Rect(ex - 8, ey - 8, 16, 16)):
                    self.eyes.append(dict(x=float(ex), y=float(ey), t=0.0, life=random.uniform(6, 11),
                                          ph=random.random() * 4))
                    break
        if self.eyes:
            play('whisper', 0.35)

    def spawn_watcher(self):
        """شبح واقف في الضلمة: مش بيتحرك طول ما إنت بتبصله... أول ما تدير ضهرك بيقرّب"""
        if len(self.ghosts) >= 3:
            return False
        for sgn in (1, -1):
            best = 0
            for dist in range(80, 361, 20):
                r = pygame.Rect(int(self.px + self.fx * sgn * dist) - 10, int(self.py + self.fy * sgn * dist) - 10, 20, 20)
                if self.blocked(r):
                    break
                best = dist
            if best >= 160:
                self.ghosts.append(dict(x=self.px + self.fx * sgn * best, y=self.py + self.fy * sgn * best,
                                        a=0.0, life=20.0, say=None, kind='watch', t=1.2, mk=rand_mk()))
                play('whisper', 0.6)
                self.toast("فيه حاجة واقفة في الضلمة... متدّيش ضهرك!", 3.5)
                return True
        return False

    def update_watcher(self, g, dt, d, gx, gy, facing):
        g['life'] -= dt
        looking = facing > 0.5
        lit = self.flash_ok() and looking and d < 330
        if g['life'] > 0:
            g['a'] = min(0.9, g['a'] + dt * 0.9)
        else:
            g['a'] -= dt * 0.8
        if lit:
            g['life'] -= dt * 3
            g['scare_t'] = 0.45
            g['sc_cd'] = g.get('sc_cd', 0.0) - dt
            if g['sc_cd'] <= 0 and g['a'] > 0.25:
                g['sc_cd'] = random.uniform(2.2, 3.6)
                play(random.choice(('hiss', 'scream')), 0.5)
                self.glitch_t = max(self.glitch_t, 0.12)
            nx, ny = g['x'] - gx / d * 70 * dt, g['y'] - gy / d * 70 * dt
            if not self.wall_at(nx, ny):
                g['x'], g['y'] = nx, ny
        else:
            g['scare_t'] = max(0.0, g.get('scare_t', 0.0) - dt)
        if g['a'] <= 0 and g['life'] <= 0:
            self.ghosts.remove(g)
            return False
        if not looking:                              # ضهرك ليه = بيقرّب
            g['t'] -= dt
            if g['t'] <= 0:
                g['t'] = random.uniform(0.8, 1.5)
                nx, ny = g['x'] + gx / d * 85, g['y'] + gy / d * 85
                if not self.wall_at(nx, ny):
                    g['x'], g['y'] = nx, ny
                    play('step', 0.45)
                    self.fear = (self.fear + 3)
        if d < 320:
            self.fear = (self.fear + 5 * dt)
        if d < 95 and g['a'] > 0.4:
            self.lose('monster', g.get('mk'))
            return True
        return False

    def ghost_move(self, g, dt, d, facing, D):
        """سلوك الوحش حسب نوعه. بيرجّع (سرعة، الكشاف بيطرده؟، مضاعف الخوف، حركة جانبية)"""
        beh = mon_of(g.get('mk', 0)).get('beh', 'plain')
        base = 62 + D['gspd'] + self.fear * 0.2
        lit = self.flash_ok() and d < 240 and facing > 0.6          # الكشاف عليه
        sp, rep, aura, lat = base, lit, 1.0, 0.0
        if beh == 'zombie':                       # بطيء وعنيد: الكشاف مش بيطرده
            sp, rep = base * (0.33 if lit else 0.55), False
            g['life'] += dt * 0.4
            if random.random() < dt * 0.2 and d < 450:
                play('moan', 0.5 * (1 - d / 450))
        elif beh == 'demon':                      # بيستنى... بيزأر... وبعدين بيهجم
            g['bt'] = g.get('bt', random.uniform(3, 5)) - dt
            rep = False
            if g.get('charge', 0.0) > 0:
                g['charge'] -= dt
                sp = base * 3.0
            elif g.get('warn', 0.0) > 0:
                g['warn'] -= dt
                sp = 0.0
                if g['warn'] <= 0:
                    g['charge'] = 1.3
            else:
                sp, rep = base * 0.5, lit
                if g['bt'] <= 0 and d < 420 and g['a'] > 0.3:
                    g['bt'] = random.uniform(6, 9)
                    g['warn'] = 0.9
                    play('roar', 0.8)
                    self.shake = max(self.shake, 0.4)
                    self.fear = (self.fear + 6)
        elif beh == 'killer':                     # بيسمع خطواتك: ساكن لو وقفت، وبيتجمّد في الكشاف
            rep = False
            if lit:
                sp = 0.0
            elif self.moving:
                sp = base * 1.8
            else:
                sp = base * 0.3
        elif beh == 'hag':                        # بتختفي وتظهر أقرب
            sp = base * 0.3 if not lit else -45
            g['bl'] = g.get('bl', random.uniform(3, 5)) - dt
            if g['bl'] <= 0 and d > 150:
                g['bl'] = random.uniform(4, 7)
                k = random.uniform(0.35, 0.55)
                g['x'] += (self.px - g['x']) * k
                g['y'] += (self.py - g['y']) * k
                g['a'] = 0.1
                play('cry', 0.5)
                self.fear = (self.fear + 4)
        elif beh == 'nun':                        # بتتغذّى على خوفك
            sp = base * min(2.1, 0.4 + self.fear / 55.0)
            if random.random() < dt * 0.15 and d < 420:
                play('bell', 0.45)
        elif beh == 'doll':                       # نطّات متقطعة وضحك، والكشاف بيجمّدها
            rep, sp = False, 0.0
            g['stun'] = 1.6 if lit else g.get('stun', 0.0) - dt
            g['hop'] = g.get('hop', random.uniform(0.3, 0.8)) - dt
            if g['hop'] <= 0 and g['stun'] <= 0 and g['a'] > 0.2:
                g['hop'] = random.uniform(0.7, 1.1)
                stp = 70 + D['gspd'] * 0.6
                g['x'] += (self.px - g['x']) / d * stp
                g['y'] += (self.py - g['y']) / d * stp
                if random.random() < 0.5:
                    play('giggle', 0.4)
        elif beh == 'tall':                       # كل ما تبصله بتخاف... وكل ما تبعد عينك بيقرّب
            rep = False
            if facing > 0.6 and d < 420:
                sp = base * 0.4
                self.fear = (self.fear + 9 * dt)
                if random.random() < dt * 0.4:
                    self.glitch_t = max(self.glitch_t, 0.1)
                    play('static', 0.4)
            else:
                sp = base * 1.2
        elif beh == 'clown':                      # بيتلوّى وبيقف يضحك
            rep = False
            g['pz'] = g.get('pz', random.uniform(2, 4)) - dt
            if g['pz'] <= 0:
                if g.get('stop', 0.0) <= 0:
                    g['stop'] = 1.0
                    play('laugh', 0.6)
                    self.fear = (self.fear + 3)
                g['stop'] -= dt
                if g['stop'] <= 0:
                    g['pz'] = random.uniform(3, 5)
                sp = 0.0
            else:
                sp = base * 1.15
                lat = base * 0.9 * math.cos(self.t * 3.2 + g.get('ph', 0.0))
        elif beh == 'flesh':                      # بطيء بس رعبه واسع
            sp, rep, aura = base * (0.15 if lit else 0.3), False, 2.2
            g['life'] += dt * 0.5
            if random.random() < dt * 0.15 and d < 450:
                play('dragging', 0.4)
        elif beh == 'fire':                       # سريع بس بيحترق
            sp, rep = base * 1.5, False
            g['life'] -= dt * 0.8
            if random.random() < dt * 0.6 and d < 450:
                play('crunch', 0.35)
        elif beh == 'boss':                       # اللي تحت: 3 مراحل (زحف، زئير وهجوم، جري)
            g['age'] = g.get('age', 0.0) + dt
            g['life'] = 99.0
            ph = 1 if g['age'] < 25 else (2 if g['age'] < 55 else 3)
            if ph != g.get('phase'):
                g['phase'] = ph
                self.boss_phase(ph)
            rep, aura = False, 1.3
            self.voice_cd = min(self.voice_cd, 5.0)               # بينادي الأسماء كتير
            slow = 0.45 if lit else 1.0                           # الكشاف بيبطّئه
            if ph == 1:
                sp = base * 0.95 * slow
            elif ph == 2:
                g['bt'] = g.get('bt', 4.0) - dt
                if g.get('charge', 0.0) > 0:
                    g['charge'] -= dt
                    sp = base * 3.0
                elif g.get('warn', 0.0) > 0:
                    g['warn'] -= dt
                    sp = 0.0
                    if g['warn'] <= 0:
                        g['charge'] = 1.3
                else:
                    sp = base * 0.9 * slow
                    if g['bt'] <= 0:
                        g['bt'] = random.uniform(6, 8)
                        g['warn'] = 0.9
                        play('roar', 1.0)
                        self.shake = max(self.shake, 0.5)
            else:
                sp = base * 1.3 * slow
                if random.random() < dt * 0.35:
                    self.glitch_t = max(self.glitch_t, 0.15)
        return sp, rep, aura, lat

    def boss_phase(self, ph):
        if ph == 1:
            self.toast("اللي تحت صحي... اجري على الباب!", 4)
            play('chant', 0.8)
        elif ph == 2:
            self.toast("بيزأر!... استعد!", 3)
            play('roar', 1.0)
            play('boom', 0.8)
            self.blackout = max(self.blackout, 1.5)
            self.shake = 0.7
            self.fear = (self.fear + 10)
        else:
            self.toast("مفيش وقت... بيجري ناحيتك!", 3)
            play('scream', 0.8)
            play('boom', 0.9)
            self.blackout = max(self.blackout, 1.2)
            self.shake = 0.8
            self.fear = (self.fear + 12)

    def start_boss(self):
        """الشقة 10: أول ما تفتح الدرج الأخير... اللي تحت بيصحى"""
        if self.boss_on or self.level != MAX_LEVEL or self.state != 'play':
            return
        mk = next((i for i in range(nmon()) if mon_of(i).get('beh') == 'boss'), None)
        if mk is None:
            return
        self.boss_on = True
        self.ghosts = []
        pos = None
        for _ in range(80):
            tx, ty = random.choice(self.lv.floors)
            x, y = tx * T + 16, ty * T + 16
            if 450 < math.hypot(x - self.px, y - self.py) < 900:
                pos = (x, y)
                break
        x, y = pos or (self.px - self.fx * 500, self.py - self.fy * 500)
        self.ghosts.append(dict(x=x, y=y, a=0.2, life=99.0, say=None, mk=mk, ph=0.0, boss=True))
        self.blackout = 2.0
        self.shake = 0.6
        play('thunder')
        play('boom')
        self.fear = (self.fear + 8)

    def add_decals(self):
        """بعد ما النور يرجع: كتابة بالدم وبصمات إيد ظهرت"""
        new = []
        px, py = self.px + self.fx * 120, self.py + self.fy * 120
        if not self.blocked(pygame.Rect(int(px) - 40, int(py) - 14, 80, 28)):
            word = self.name() if (self.level >= 3 and random.random() < 0.4) else random.choice(DECAL_WORDS)
            new.append(dict(kind='text', x=px, y=py, text=word, size=34, ang=random.randint(-12, 12)))
        for _ in range(random.randint(1, 2)):
            hx, hy = self.px + random.randint(-110, 110), self.py + random.randint(-90, 90)
            if not self.blocked(pygame.Rect(int(hx) - 10, int(hy) - 10, 20, 20)):
                new.append(dict(kind='hand', x=hx, y=hy, ang=random.randint(-40, 40)))
        self.decals = (self.decals + new)[-12:]
        if new:
            play('whisper', 0.5)

    def snuff_candle(self):
        lit = [i for i, (cx, cy) in enumerate(self.lv.candles)
               if i not in self.out_c and 80 < math.hypot(cx * T + 16 - self.px, cy * T + 16 - self.py) < 380]
        if not lit or len(self.out_c) >= max(1, len(self.lv.candles) // 2):
            return
        self.out_c.add(random.choice(lit))
        play('snuff', 0.8)
        self.toast("الشمعة طفت لوحدها!", 3)
        self.fear = (self.fear + 4)
        if random.random() < 0.5:
            self.after(1.0, lambda: play('whisper', 0.6))

    def spawn_ghost(self, near=False, force=False):
        if self.boss_on:
            return
        D = diff(self.level)
        if not force and len(self.ghosts) >= D['gmax'] + self.extra_ghosts():
            return
        if not near and self.level >= 2 and random.random() < 0.35 and self.spawn_watcher():
            self.ghost_cd = random.uniform(0.7, 1.2) * D['gcd']
            return
        if near:
            x, y = self.px - self.fx * 230, self.py - self.fy * 230
        else:
            for _ in range(60):
                tx, ty = random.choice(self.lv.floors)
                x, y = tx * T + 16, ty * T + 16
                if 380 < math.hypot(x - self.px, y - self.py) < 700:
                    break
        g = dict(x=x, y=y, a=0.3 if near else 0.0, life=14.0, say=None, mk=pick_mon(self.level), ph=random.random() * 6.28)
        if self.level >= 2 and random.random() < 0.6:
            nm = self.target_name()
            g['say'] = [self.name_line(nm), 5.0]
            self.after(0.8, lambda nm=nm, mk=g['mk']: self.say_name(0.85, nm, mk))
        self.ghosts.append(g)
        self.ghost_cd = random.uniform(0.7, 1.2) * D['gcd']
        if not near:
            self.toast("حاسس إن في حد بيراقبك...", 3)
        play('whisper', 0.7)
        ms = MON_SOUND.get(g['mk'] % nmon())
        if ms:
            self.after(0.6, lambda ms=ms: play(ms, 0.55))
        bh = mon_of(g['mk']).get('beh')
        seen = self.__dict__.setdefault('seen_beh', set())
        if bh in BEH_HINT and bh not in seen:               # أول مرة تقابل النوع ده: تلميح عن طريقته
            seen.add(bh)
            self.after(3.4, lambda t=BEH_HINT[bh]: self.toast(t, 4.0) if self.state == 'play' else None)

    # ------------------------------------------------ تفاعل
    def fp_on(self):
        return VIEW3D and getattr(self, 'lv', None) is not None

    def rand_choice(self, seq):
        return random.choice(seq)

    def fp_event(self, o, kind):
        if kind == 'open' and self.state in ('play', 'pause'):
            play('creak', 0.3)

    def nearest(self):
        if self.fp_on():                                           # القطعة اللي بتبصلها
            o = self.fp.pick(self)
            if o:
                return o
            best, bd = None, 1e9
            ca, sa = math.cos(self.ang), math.sin(self.ang)
            for o in self.objs:
                if o.can and o.rect.inflate(44, 44).collidepoint(self.px, self.py):
                    vx, vy = o.rect.centerx - self.px, o.rect.centery - self.py
                    d = math.hypot(vx, vy)
                    if d > 0 and (vx * ca + vy * sa) / d > 0.45 and d < bd:
                        best, bd = o, d
            return best
        best, bd = None, 1e9
        for o in self.objs:
            if o.can and o.rect.inflate(44, 44).collidepoint(self.px, self.py):
                d = math.hypot(o.rect.centerx - self.px, o.rect.centery - self.py)
                if d < bd:
                    best, bd = o, d
        return best

    def interact(self):
        o = self.nearest()
        if not o:
            return
        if self.fp_on() and fp3d.style_of(o) in fp3d.OPENABLE:
            self.fp_peek[o.id] = self.t + 2.8              # الدُرج/الضلفة بتتفتح وانت بتدوّر
        k = o.kind
        if k in ('flavor', 'note'):
            sc = self.roll_scare()
            self.dialog(o.title, o.text, on_close=(lambda: self.scare(sc)) if sc else None)
        elif k == 'battery':
            if o.id in self.done:
                self.toast("دوّرت تاني... مفيش حاجة.")
            else:
                self.done.add(o.id)
                self.net_ev('done', o.id)
                self.spare += 1
                self.emote('happy', 3)
                play('pickup')
                self.toast(S("لقيت بطارية للكشاف {w}!", w=o.where), 3.5)
                sc = self.roll_scare()
                if sc:
                    self.after(1.2, lambda: self.scare(sc))
        elif k == 'special':
            self.interact_special(o)
        elif k == 'container':
            self.open_container(o)
        elif k == 'door':
            if o.need in self.inv:
                o.solid = o.can = False
                self.opened.add(o.id)
                self.net_ev('open', o.id)
                self.emote('happy', 3)
                play('unlock')
                self.toast(o.toast, 3)
                if self.level >= 2 and random.random() < 0.14 + 0.02 * self.level:       # وحش ورا الباب
                    self.after(0.35, lambda: self.scare('face') if (self.state == 'play' and self.js_t <= 0) else None)
            else:
                self.emote('angry', 2.5)
                self.dialog(o.title, o.locked)
        elif k == 'exit':
            if o.need in self.inv:
                if self.level >= 3 and random.random() < 0.5:      # آخر لحظة: حاجة بتطلعلك قدام الباب
                    self.scare('face', after=self.go_next)
                else:
                    self.go_next()
            else:
                self.emote('angry', 2.5)
                self.dialog(o.title, o.locked)

    def interact_special(self, o):
        self.fear = (self.fear + 6)
        if o.sp == 'piano':
            play('creak', 0.8)
            self.toast("النغمة طلعت من البيانو... وإيدك لسه ما لمستوش!", 3.5)
        elif o.sp == 'mirror':
            if o.id in self.done:
                play('whisper', 0.6)
                self.toast("المراية ساكتة... بس حاسس إنها مستنية.", 3)
            else:
                self.done.add(o.id)
                self.net_ev('done', o.id)
                self.dialog("المراية الكبيرة", ["بصّيت في المراية... مفيش غير انعكاسك.",
                                                "لحظة... ليه انعكاسك بيبتسم؟"],
                            on_close=lambda: self.scare('face'))
        elif o.sp == 'doll':
            if o.id in self.done:
                play('laugh', 0.7)
                self.toast("الدُمية بتبصلك... ومكانها اتغيّر!", 3)
            else:
                self.done.add(o.id)
                self.net_ev('done', o.id)

                def doll_end():
                    play('laugh', 0.9)
                    self.shake = 0.4
                    self.after(1.1, lambda: self.scare('bang'))
                self.dialog("الدُمية الكبيرة", ["دُمية قديمة وعنيها زجاج لامع.",
                                                 "رقبتها مايلة ناحيتك... مكانتش كده من شوية."],
                            on_close=doll_end)
        else:
            play('whisper', 0.8)
            self.dialog("الصورة", ["راجل عينيه بتتابعك في كل مكان...", "ويمكن عينيه اتحركت فعلًا."])

    def open_container(self, o):
        if o.id in self.done:
            self.toast(o.empty)
            return
        if o.need and o.need not in self.inv:
            self.emote('angry', 2.5)
            self.dialog(o.title, o.locked)
            return
        self.done.add(o.id)
        self.net_ev('done', o.id)
        if self.level >= 2 and random.random() < 0.10 + 0.01 * self.level:
            self.after(0.5, lambda: self.scare('bang') if (self.state == 'play' and self.js_t <= 0) else None)
        if o.give:
            self.inv.add(o.give)
            self.net_ev('inv', o.give)
            self.emote('happy', 3)
            play('pickup')

        def show():
            on = None
            if o.finale:
                on = lambda: (self.scare('flicker'), self.after(2.0, lambda: self.scare('face')),
                              self.after(4.5, self.start_boss) if self.level == MAX_LEVEL else None)
            self.dialog(o.title, o.lines, on_close=on)
        if o.scare == 'face':
            self.scare('face', after=show)
        else:
            if o.scare:
                self.scare(o.scare)
            show()

    # ------------------------------------------------ تحديث
    def blocked(self, r):
        lv = self.lv
        for ty in range(r.top // T, (r.bottom - 1) // T + 1):
            for tx in range(r.left // T, (r.right - 1) // T + 1):
                if tx < 0 or ty < 0 or tx >= lv.W or ty >= lv.H or lv.grid[ty][tx] == 1:
                    return True
        return any(o.solid and r.colliderect(o.rect) for o in self.objs)

    def tick_js(self, dt):
        if self.js_t > 0:
            self.js_t -= dt
            if self.js_t <= 0 and self.js_after:
                fn, self.js_after = self.js_after, None
                fn()

    def update(self, dt):
        self.t += dt
        D = diff(self.level)
        self.shake = max(0.0, self.shake - dt)
        self.hurt_t = max(0.0, self.hurt_t - dt)
        for en in list(self.emo):
            self.emo[en] -= dt
            if self.emo[en] <= 0:
                del self.emo[en]
        if self.toast_t > 0:
            self.toast_t -= dt
        if self.state in ('pause', 'help') and not self.net_on:   # أونلاين: اللعبة مبتقفش لما تفتح القايمة
            return
        if self.say:
            self.say[1] -= dt
            if self.say[1] <= 0:
                self.say = None
        for it in self.later[:]:
            it[0] -= dt
            if it[0] <= 0:
                self.later.remove(it)
                it[1]()
        if self.app:
            self.app[2] -= dt
            if self.app[2] <= 0:
                self.app = None
        if self.dash:
            self.dash['t'] += dt
            if self.dash['t'] >= self.dash['dur']:
                self.dash = None
        if self.hall:
            self.hall[0] -= dt
            if self.hall[0] <= 0:
                self.hall = None
        if self.glitch_t > 0:
            self.glitch_t -= dt
        if self.js_t > 0 or self.dlg or self.state not in ('play', 'pause'):
            self.moving = False
            return

        if self.level >= 2 and self.fear > 20:                          # خطوات ورا ضهرك
            self.step_cd -= dt
            if self.step_cd <= 0:
                self.step_cd = random.uniform(18, 36)
                for i in range(5):
                    self.after(0.42 * i, lambda i=i: play('step', 0.55 - 0.08 * i))
        if self.net_on:
            self.update_mimic(dt)
            self.gchat_t -= dt
            if self.gchat_t <= 0:
                self.gchat_t = random.uniform(50, 110)
                if self.level >= 2:
                    self.ghost_chat()
        if self.blackout > 0:
            self.blackout -= dt
            if self.blackout <= 0:
                self.toast("النور رجع...", 2)
                self.add_decals()
        self.cd -= dt
        self.voice_cd -= dt
        self.sc_cd -= dt
        self.phantom_cd -= dt

        k = pygame.key.get_pressed()
        fp = self.fp_on()
        if fp:                                                        # منظور أول: W/S قدّام ورا، A/D جنب، الأسهم يمين وشمال بتلف
            if self.state == 'play' and not self.chat_open:
                self.ang += ((k[pygame.K_RIGHT] - k[pygame.K_LEFT]) * 2.3) * dt
            self.fx, self.fy = math.cos(self.ang), math.sin(self.ang)
            fwd = (k[pygame.K_w] or k[pygame.K_UP]) - (k[pygame.K_s] or k[pygame.K_DOWN])
            strf = k[pygame.K_d] - k[pygame.K_a]
            if self.joy[0] or self.joy[1]:
                strf, fwd = self.joy[0], -self.joy[1]
            if self.state != 'play' or self.chat_open:
                fwd = strf = 0
            dx = fwd * self.fx + strf * (-self.fy)
            dy = fwd * self.fy + strf * self.fx
        else:
            dx = (k[pygame.K_d] or k[pygame.K_RIGHT]) - (k[pygame.K_a] or k[pygame.K_LEFT])
            dy = (k[pygame.K_s] or k[pygame.K_DOWN]) - (k[pygame.K_w] or k[pygame.K_UP])
            if self.joy[0] or self.joy[1]:                            # جويستيك اللمس
                dx, dy = self.joy
            if self.state != 'play' or self.chat_open:
                dx = dy = 0
        self.moving = bool(dx or dy)
        if (self.was_moving and not self.moving and self.level >= 2 and self.fear > 20
                and self.phantom_cd <= 0 and random.random() < 0.35):
            self.phantom_cd = random.uniform(25, 45)              # وقفت؟ فيه خطوات لسه جاية ناحيتك
            for i, dl in enumerate((0.45, 0.9, 1.35)):
                self.after(dl, lambda i=i: play('foot1' if i % 2 == 0 else 'foot2', 0.38 - 0.08 * i))
            self.after(1.9, lambda: play('breath', 0.5))
        self.was_moving = self.moving
        if dx or dy:
            n = math.hypot(dx, dy)
            dx, dy = dx / n, dy / n
            if not fp:
                self.fx, self.fy = dx, dy
            run = k[pygame.K_LSHIFT] or k[pygame.K_RSHIFT] or k[pygame.K_k] or self.joy_run
            self.running = bool(run)
            sp = 190 if run else 125
            nx = self.px + dx * sp * dt
            if not self.blocked(pygame.Rect(int(nx) - 10, int(self.py) - 10, 20, 20)):
                self.px = nx
            ny = self.py + dy * sp * dt
            if not self.blocked(pygame.Rect(int(self.px) - 10, int(ny) - 10, 20, 20)):
                self.py = ny
            self.step_t -= dt
            if self.step_t <= 0:
                self.foot = not getattr(self, 'foot', False)
                play('foot1' if self.foot else 'foot2', FOOTSTEP_VOL * (1.5 if run else 1.0))
                self.step_t = 0.38 if run else 0.55
                if self.level >= 2 and random.random() < 0.08 + self.fear / 700:
                    self.after(0.3, lambda: play('foot2', 0.3))          # صدى خطوة ورا ضهرك

        if self.battery <= 0 and self.spare > 0:
            self.spare -= 1
            self.battery = 100.0
            self.dead_warned = False
            self.toast("غيّرت بطارية الكشاف.", 2)
        if self.flash_ok():
            self.battery = max(0.0, self.battery - D['drain'] * dt)
            if self.battery <= 0 and not self.dead_warned:
                self.dead_warned = True
                self.toast("الكشاف فصل! دوّر على بطاريات.", 3)
                self.emote('sad', 4)
                if self.spare <= 0:
                    self.after(2.6, self.dark_company)

        tx, ty = int(self.px // T), int(self.py // T)
        for ri, (nm, (x, y, w, h), _c) in enumerate(self.lv.rooms):
            if x <= tx < x + w and y <= ty < y + h:
                self.room = nm
                if ri not in self.visited:
                    self.visited.add(ri)
                    if len(self.visited) > 1:
                        self.first_visit()

        pr = pygame.Rect(int(self.px) - 10, int(self.py) - 10, 20, 20)
        for tr in self.lv.triggers:
            if not tr['fired'] and self.cd <= 0 and pr.colliderect(tr['rect']):
                tr['fired'] = True
                self.scare(tr['kind'])
                break

        # عيون في الضلمة
        self.eye_cd -= dt
        if self.eye_cd <= 0:
            self.eye_cd = random.uniform(16, 30)
            if not self.eyes and self.blackout <= 0:
                self.spawn_eyes(random.choice((1, 2)))
        for e in self.eyes[:]:
            e['t'] += dt
            e['life'] -= dt
            ex, ey = e['x'] - self.px, e['y'] - self.py
            d = math.hypot(ex, ey) or 1
            e['x'] -= ex / d * 9 * dt
            e['y'] -= ey / d * 9 * dt
            lit = self.flash_ok() and d < 260 and (ex / d * self.fx + ey / d * self.fy) > 0.75
            if e['life'] <= 0 or lit or d < 70:
                self.eyes.remove(e)
                if lit or d < 70:
                    play('whisper', 0.5)
                    self.fear = (self.fear + 5)
                    if random.random() < 0.4:
                        self.after(0.8, lambda: self.spawn_eyes(1, 110, 190))

        # الأشباح
        if len(self.ghosts) < D['gmax'] + self.extra_ghosts() and not self.boss_on:
            self.ghost_cd -= dt
            if self.ghost_cd <= 0:
                self.spawn_ghost()
        for g in self.ghosts[:]:
            gx, gy = self.px - g['x'], self.py - g['y']
            d = math.hypot(gx, gy) or 1
            facing = (-gx / d) * self.fx + (-gy / d) * self.fy
            if g.get('kind') == 'watch':
                if self.update_watcher(g, dt, d, gx, gy, facing):
                    break
                continue
            g['life'] -= dt
            g['a'] = min(1.0, g['a'] + dt * 0.5) if g['life'] > 0 else g['a'] - dt * 0.8
            if g['say']:
                g['say'][1] -= dt
                if g['say'][1] <= 0:
                    g['say'] = None
            if g['a'] <= 0 and g['life'] <= 0:
                self.ghosts.remove(g)
                continue
            sp, rep, aura, lat = self.ghost_move(g, dt, d, facing, D)
            beh_ = mon_of(g.get('mk', 0)).get('beh', 'plain')
            g['scare_t'] = max(0.0, g.get('scare_t', 0.0) - dt)
            g['sc_cd'] = g.get('sc_cd', 0.0) - dt
            if self.flash_ok() and d < 260 and facing > 0.55:        # الكشاف عليه: كل الوحوش بتخاف منه
                rep = True
                g['scare_t'] = 0.45
                g['charge'] = 0.0
                if beh_ in ('demon', 'boss'):
                    g['warn'] = 0.0
                if g['sc_cd'] <= 0 and g['a'] > 0.25:                # صرخة رعب وهو بيهرب
                    g['sc_cd'] = random.uniform(2.2, 3.6)
                    play(random.choice(('hiss', 'scream', 'roar')), 0.35 + 0.4 * (1 - d / 260))
                    self.glitch_t = max(self.glitch_t, 0.12)
                    self.shake = max(self.shake, 0.18)
            if rep:
                self.emote('angry', 0.6)
                sp = -45.0 if beh_ == 'plain' else -max(45.0, min(130.0, abs(sp) * 0.8))
                if beh_ != 'boss':
                    g['life'] -= dt * (2.5 if beh_ == 'plain' else 1.0)
            g['x'] += gx / d * sp * dt - gy / d * lat * dt
            g['y'] += gy / d * sp * dt + gx / d * lat * dt
            if d < (420 if aura > 1 else 320):
                self.fear = (self.fear + 7 * aura * dt)
                if random.random() < dt * 0.4:
                    play('whisper', 0.6 * (1 - d / 320))
                if d < 220 and random.random() < dt * 0.15:
                    play('breath', 0.5 * (1 - d / 220))
            if d < 300 and g['a'] > 0.4 and self.voice_cd <= 0:
                self.voice_cd = random.uniform(7, 12)
                nm = self.target_name()
                g['say'] = [self.name_line(nm), 3.5]
                self.say_name(max(0.6, min(1.0, 1.3 - d / 300)), nm, g.get('mk'))
            if d < (44 if g.get('boss') else 26) and g['a'] > 0.5:
                self.lose('monster', g.get('mk'))
                break

        near_candle = any(ci not in self.out_c and
                          math.hypot(cx * T + 16 - self.px, cy * T + 16 - self.py) < 110
                          for ci, (cx, cy) in enumerate(self.lv.candles))
        seen = any(g['a'] > 0.2 for g in self.ghosts)
        if near_candle and self.blackout <= 0:
            self.fear = max(0, self.fear - 6 * dt)
        elif not self.flash_ok() and self.fear < 45:
            self.fear += 2.5 * dt
        elif self.fear > 0 and not seen:
            self.fear = max(0, self.fear - FEAR_DECAY * dt)
        if self.fear_full or self.fear >= FEAR_LOSE - 0.01:      # العداد اتملى = خسرت
            self.lose('fear')
            return
        near = min([math.hypot(g['x'] - self.px, g['y'] - self.py) for g in self.ghosts if g.get('a', 1.0) > 0.25] or [9999.0])
        inten = max(self.fear / 100.0, max(0.0, 1 - near / 520.0))        # قلبك بيدق أسرع كل ما الوحش يقرّب
        self.pulse = max(0.0, self.pulse - dt * 2.5)
        if inten > 0.3:
            self.heart_t -= dt
            if self.heart_t <= 0:
                play('heart', 0.25 + 0.75 * inten)
                self.heart_t = 1.3 - 0.85 * inten
                self.pulse = inten

        # الشموع بتطفي لوحدها
        self.snuff_cd -= dt
        if self.snuff_cd <= 0:
            self.snuff_cd = random.uniform(22, 40)
            if self.level >= 2:
                self.snuff_candle()

        # هلوسة: حاجة بتلمع في طرف عينك لحظة
        if self.fear > 55 and self.hall is None and random.random() < dt * (self.fear - 50) / 220:
            self.hall = [random.uniform(0.15, 0.3), random.choice(['ghost', 'word', 'eyes']),
                         random.randint(80, SW - 80), random.randint(220, SH - 150),
                         random.choice(HALL_WORDS + [self.name()])]
        if self.fear > 65 and self.glitch_t <= 0 and random.random() < dt * 0.8 * (self.fear - 60) / 40:
            self.glitch_t = 0.12

        self.amb -= dt
        if self.amb <= 0:
            self.amb = random.uniform(0.7, 1.2) * D['amb']
            kinds = ['creak', 'whisper', 'step', 'knock', 'breath'] + extra_amb(self.level)
            if self.level >= 2:
                kinds += ['cry', 'laugh', 'slam']
            if self.level >= 3:
                kinds.append('musicbox')
            self.ambient(random.choice(kinds))

    # ------------------------------------------------ رسم
    def draw(self, s):
        st = self.state
        if st == 'help':
            self.draw_help(s)
        elif st in ('title', 'profile'):
            self.draw_title(s)
        elif st in ONLINE_STATES:
            self.draw_online(s)
        elif st == 'trans':
            self.draw_trans(s)
        else:
            self.draw_world(s)
            if st == 'pause':
                self.draw_pause(s)
            elif st == 'win':
                self.draw_win(s)
            elif st == 'lose':
                self.draw_lose(s)
        if self.js_t > 0:
            self.draw_js(s)

    def draw_decal(self, s, dc, cx, cy):
        x, y = int(dc['x'] - cx), int(dc['y'] - cy)
        if x < -140 or y < -140 or x > SW + 140 or y > SH + 140:
            return
        if dc['kind'] == 'hand':
            draw_hand(s, x, y, dc['ang'])
        else:
            surf = pygame.transform.rotate(txt(dc['text'], dc['size'], (150, 14, 14)), dc['ang'])
            s.blit(surf, (x - surf.get_width() // 2, y - surf.get_height() // 2))

    def draw_dash(self, s):
        d = self.dash
        k = d['t'] / d['dur']
        mk = d.get('mk', 0)
        spr = mon_big(mk, d['dir'] > 0)
        w, h = spr.get_size()
        x = -w + (SW + w) * k if d['dir'] > 0 else SW - (SW + w) * k
        y = SH - h + 120 + math.sin(self.t * 40) * 6
        red = pygame.Surface((SW, SH))
        red.fill((120, 0, 0))
        red.set_alpha(55)
        s.blit(red, (0, 0))
        spr.set_alpha(235)
        s.blit(spr, (int(x), int(y)))
        m = mon_of(mk)
        for fx_, fy_ in m['eyes']:
            lx = fx_ * w if d['dir'] > 0 else w - fx_ * w
            glow(s, int(x + lx), int(y + fy_ * h), 26, m['col'], min(255, int(240 * m['pw'])))

    def glitch(self, s):
        snap = s.copy()
        for _ in range(random.randint(2, 4)):
            y = random.randint(0, SH - 40)
            s.blit(snap, (random.randint(-30, 30), y), (0, y, SW, random.randint(6, 30)))
        for _ in range(8):
            y = random.randint(0, SH)
            pygame.draw.line(s, (120, 0, 0), (0, y), (SW, y), 1)

    def tiles(self):
        """الأرضيات والحيطان بتترسم مرة واحدة لكل مرحلة وبعدين بس بننسخ الجزء اللي ظاهر"""
        lv = self.lv
        bg = getattr(lv, '_bg', None)
        if bg is None:
            bg = pygame.Surface((lv.W * T, lv.H * T))
            bg.fill((0, 0, 0))
            grid, floorc = lv.grid, lv.floorc
            for j in range(lv.H):
                for i in range(lv.W):
                    x, y = i * T, j * T
                    if grid[j][i] == 1:
                        pygame.draw.rect(bg, (44, 36, 34), (x, y, T, T))
                        if j + 1 < lv.H and grid[j + 1][i] == 0:
                            pygame.draw.rect(bg, (84, 62, 54), (x, y + T - 12, T, 12))
                    else:
                        c = floorc[j][i]
                        v = (i * 7 + j * 13) % 5 * 2
                        pygame.draw.rect(bg, (c[0] + v, c[1] + v, c[2] + v), (x, y, T, T))
                        pygame.draw.line(bg, (c[0] // 2, c[1] // 2, c[2] // 2), (x, y + T - 1), (x + T, y + T - 1))
            lv._bg = bg
        return bg

    def draw_world(self, s):
        if self.fp_on():
            return self.draw_world_fp(s)
        lv = self.lv
        shx = shy = 0
        if self.shake > 0:
            shx, shy = random.randint(-6, 6), random.randint(-6, 6)
        elif self.fear > 75:
            shx, shy = random.randint(-2, 2), random.randint(-2, 2)
        camx, camy = self.cam_pos()
        cx = int(max(0, min(lv.W * T - SW, camx - SW / 2))) + shx
        cy = int(max(0, min(lv.H * T - SH, camy - SH / 2))) + shy
        s.fill((0, 0, 0))
        s.blit(self.tiles(), (-cx, -cy))
        for a, b, c_, d_, col in lv.rugs:
            pygame.draw.rect(s, col, (a * T - cx, b * T - cy, c_ * T, d_ * T), border_radius=6)
        for dc in self.decals:
            self.draw_decal(s, dc, cx, cy)
        for o in self.objs:
            r = o.rect.move(-cx, -cy)
            if r.right < 0 or r.bottom < 0 or r.left > SW or r.top > SH:
                continue
            if o.kind == 'door' and not o.solid:
                continue
            if 'هز' in str(o.name):                                   # الكرسي الهزّاز بيهتز لوحده
                r.x += int(math.sin(self.t * 2.2) * 2)
            pygame.draw.rect(s, o.color, r, border_radius=3)
            pygame.draw.rect(s, tuple(max(0, c - 40) for c in o.color), r, 3, border_radius=3)
            if o.kind in ('door', 'exit'):
                pygame.draw.circle(s, (220, 190, 60), (r.right - 8, r.centery), 4)
        for ci, (tx, ty) in enumerate(lv.candles):
            x, y = tx * T + 16 - cx, ty * T + 16 - cy
            pygame.draw.rect(s, (230, 225, 200), (x - 3, y - 2, 6, 12))
            if self.blackout <= 0 and ci not in self.out_c:
                pygame.draw.ellipse(s, (255, 190, 60), (x - 3, y - 9, 6, 8 + random.random() * 2))
        peer_pos = []
        plist = list(self.peers.values())
        if self.mimic:                                                # الفخ بيتعامل زي أي لاعب حقيقي
            mm = self.mimic
            plist.append(dict(id=mm['pid'], x=mm['x'], y=mm['y'], fx=mm['fx'], fy=mm['fy'], mv=0, fl=1,
                              lv=self.level, ls=0, ex='neutral', fake=True))
        for p in plist:                                               # اللاعبين التانيين
            if p['lv'] != self.level:
                continue
            for gx_, gy_, ga_, gk_ in p.get('gh', []):                # وحوش صحابك بتبان عندك
                draw_ghost(s, gx_ - cx, gy_ - cy, int(ga_ * 160), self.t, gk_)
            ppx, ppy = int(p['x'] - cx), int(p['y'] - cy)
            peer_pos.append((p, ppx, ppy))
            if -60 < ppx < SW + 60 and -80 < ppy < SH + 60:
                dead = p['id'] in self.dead_ids
                self.draw_char(s, ppx, ppy, p['fx'], p['fy'], p['mv'], self.t + p['id'], tint=PEER_TINTS[p['id'] % 8],
                               fl=p['fl'], mode='die' if dead else None, k=3)
        for g in self.ghosts:
            jx_, jy_ = (random.randint(-5, 5), random.randint(-3, 3)) if g.get('scare_t', 0.0) > 0 else (0, 0)
            draw_ghost(s, g['x'] - cx + jx_, g['y'] - cy + jy_, int(max(0, g['a']) * 190), self.t, g.get('mk', 0))
        px, py = int(self.px - cx), int(self.py - cy)
        self.draw_player(s, px, py)

        dk = self.dark
        dk.fill((0, 0, 6, 255 if self.blackout > 0 else 250))
        if self.blackout <= 0:
            for ci, (tx, ty) in enumerate(lv.candles):
                if ci in self.out_c:
                    continue
                x, y = tx * T + 16 - cx, ty * T + 16 - cy
                if -150 < x < SW + 150 and -150 < y < SH + 150:
                    light(dk, x, y, 125 * (1 + 0.06 * math.sin(self.t * 9 + tx) + random.random() * 0.03), 215)
        tv = 1.0 - 0.35 * max(0.0, (self.fear - 45) / 55)             # الخوف بيضيّق الرؤية (نفق)
        light(dk, px, py, int(56 * tv), 200)
        if self.flash_ok():
            m = tv
            near_g = any(g['a'] > 0.3 and math.hypot(g['x'] - self.px, g['y'] - self.py) < 230 for g in self.ghosts)
            if self.battery < 20 or self.fear > 70 or near_g:        # الكشاف بيرتعش لما وحش يقرّب
                m = tv * random.choice([1, 1, 1, 0.85, 0.55])
            light(dk, int(px + self.fx * 55), int(py + self.fy * 55), 150 * m, 240)
            light(dk, int(px + self.fx * 150), int(py + self.fy * 150), 110 * m, 235)
        for p, ppx, ppy in peer_pos:                                  # نور صحابك
            if p['id'] in self.dead_ids:
                continue
            light(dk, ppx, ppy, 56, 200)
            if p['fl']:
                light(dk, int(ppx + p['fx'] * 55), int(ppy + p['fy'] * 55), 140, 235)
        s.blit(dk, (0, 0))
        for p, ppx, ppy in peer_pos:
            for gx_, gy_, ga_, gk_ in p.get('gh', []):
                gxx_, gyy_ = draw_ghost_pos(gx_ - cx, gy_ - cy, self.t, gk_)
                ghost_eyes(s, gxx_, gyy_, ga_, gk_)
            if -80 < ppx < SW + 80 and -90 < ppy < SH + 60:
                draw_text(s, self.pname(p['id']), 16, PEER_COLS[p['id'] % 8], ppx, ppy - 64, 'c')

        for e in self.eyes:                                           # عيون حمرا في الضلمة
            if (self.t * 0.9 + e['ph']) % 4 < 0.14:
                continue
            a = min(1.0, e['t'] * 1.5)
            ex, ey = int(e['x'] - cx), int(e['y'] - cy)
            if -30 < ex < SW + 30 and -30 < ey < SH + 30:
                for off in (-9, 9):
                    glow(s, ex + off, ey, 12, (255, 30, 20), (80, 140, 200)[min(2, int(a * 3))])
                    pygame.draw.ellipse(s, (255, 200, 190), (ex + off - 3, ey - 2, 6, 4))
        for g in self.ghosts:
            gmk = g.get('mk', 0)
            gxx, gyy = draw_ghost_pos(g['x'] - cx, g['y'] - cy, self.t, gmk)
            if g.get('scare_t', 0.0) > 0:                             # بيرتعش من الكشاف
                gxx += random.randint(-5, 5)
                gyy += random.randint(-3, 3)
            ghost_eyes(s, gxx, gyy, g['a'], gmk)
            if g['say'] and g['a'] > 0.3:
                draw_text(s, str(g['say'][0]).replace("{name}", self.name()), 24, (220, 30, 30),
                          gxx + mon_of(gmk)['img'].get_width() // 2, gyy - 26, 'c')
        if self.app:
            amk = self.app[3] if len(self.app) > 3 else 0
            gxx, gyy = draw_ghost(s, self.app[0] - cx, self.app[1] - cy, 225, self.t, amk)
            ghost_eyes(s, gxx, gyy, 1.0, amk)
        self._world_tail(s)

    # ------------------------------------------------ منظور أول
    def fp_candle_img(self):
        im = A.get('fp_candle')
        if im is None:
            im = pygame.Surface((26, 90), pygame.SRCALPHA)
            pygame.draw.rect(im, (120, 100, 60), (11, 24, 4, 62))
            pygame.draw.ellipse(im, (150, 124, 70), (3, 80, 20, 8))
            pygame.draw.rect(im, (230, 224, 200), (9, 14, 8, 14))
            pygame.draw.ellipse(im, (150, 124, 70), (6, 26, 14, 5))
            A['fp_candle'] = im
        return im

    def fp_decal_img(self, dc):
        cache = A.setdefault('fp_decals', {})
        if len(cache) > 60:
            cache.clear()
        c = cache.get(id(dc))
        if c is None:
            if dc['kind'] == 'hand':
                im = pygame.Surface((80, 90), pygame.SRCALPHA)
                draw_hand(im, 40, 36, dc['ang'])
                wd, hd = 1.0, 1.1
            else:
                tx = pygame.transform.rotate(txt(dc['text'], dc['size'], (150, 14, 14)), dc['ang'])
                im = tx
                wd, hd = tx.get_width() / 28.0, tx.get_height() / 28.0
            c = cache[id(dc)] = (im, wd, hd)
        return c

    def fp_sprites(self):
        out = []
        t = self.t
        for p in list(self.peers.values()):                           # وحوش صحابك
            if p['lv'] != self.level:
                continue
            for gx_, gy_, ga_, gk_ in p.get('gh', []):
                m = mon_of(gk_)
                out.append(dict(x=gx_ / T, y=gy_ / T, img=m['img'], h=2.0, z0=0.1, alpha=int(ga_ * 170), eyes=m['eyes'],
                                ecol=m['col'], epow=120))
        for g in self.ghosts:
            mk = g.get('mk', 0)
            m = mon_of(mk)
            beh = m.get('beh', 'plain')
            hgt = {'doll': 1.0, 'boss': 2.8, 'hag': 1.8}.get(beh, 2.0)
            a = max(0.0, g['a'])
            gx, gy = g['x'] / T, g['y'] / T
            if g.get('scare_t', 0.0) > 0:
                gx += random.uniform(-0.05, 0.05)
                gy += random.uniform(-0.05, 0.05)
            out.append(dict(x=gx, y=gy, img=m['img'], h=hgt, z0=(0.08 + 0.07 * math.sin(t * 2.2 + g['x'] * 0.01)) if beh == 'plain' else 0.0,
                            alpha=int(a * 225), eyes=m['eyes'], ecol=m['col'],
                            epow=min(255, int(m['pw'] * 60 * (1 + int(min(a, 0.99) * 3)))), g=g))
        if self.app:
            amk = self.app[3] if len(self.app) > 3 else 0
            m = mon_of(amk)
            out.append(dict(x=self.app[0] / T, y=self.app[1] / T, img=m['img'], h=2.0, z0=0.1, alpha=225, eyes=m['eyes'],
                            ecol=m['col'], epow=200))
        plist = list(self.peers.values())
        if self.mimic:
            mm = self.mimic
            plist.append(dict(id=mm['pid'], x=mm['x'], y=mm['y'], fx=mm['fx'], fy=mm['fy'], mv=0, fl=1, lv=self.level, ls=0,
                              ex='neutral', fake=True))
        for p in plist:                                               # اللاعبين التانيين
            if p['lv'] != self.level:
                continue
            dead = p['id'] in self.dead_ids
            vx, vy = self.px - p['x'], self.py - p['y']
            dd = math.hypot(vx, vy) or 1.0
            dot = (p['fx'] * vx + p['fy'] * vy) / dd
            cr = p['fx'] * vy - p['fy'] * vx
            row = 0 if dot > 0.5 else (3 if dot < -0.5 else (2 if cr > 0 else 1))
            tint = PEER_TINTS[p['id'] % 8]
            fi = int((t + p['id']) * 9) % 4 if p['mv'] else 0
            if dead:
                spr = self.tinted_fx(7, tint) if (tint and any(tint)) else A['pfx'][7]
            else:
                spr = (self.tinted_dir(tint) if (tint and any(tint)) else A['pdir'])[row][fi]
            out.append(dict(x=p['x'] / T, y=p['y'] / T, img=spr, h=1.7, z0=0.0, alpha=255, name=self.pname(p['id']),
                            ncol=PEER_COLS[p['id'] % 8]))
        cimg = self.fp_candle_img()
        for ci, (tx, ty) in enumerate(self.lv.candles):
            out.append(dict(x=tx + 0.5, y=ty + 0.5, img=cimg, h=1.2, z0=0.0, alpha=255))
        for dc in self.decals[-12:]:
            im, wd, hd = self.fp_decal_img(dc)
            out.append(dict(x=dc['x'] / T, y=dc['y'] / T, img=im, w=wd, h=hd, alpha=220, floor=True))
        return out

    def draw_world_fp(self, s):
        self.fx, self.fy = math.cos(self.ang), math.sin(self.ang)
        shx = shy = 0
        if self.shake > 0:
            shx, shy = random.randint(-6, 6), random.randint(-6, 6)
        elif self.fear > 75:
            shx, shy = random.randint(-2, 2), random.randint(-2, 2)
        bob = 0.0
        if self.moving and self.state == 'play':
            bob = math.sin(self.t * (14 if self.running else 9.5)) * (5 if self.running else 3)
        s.fill((0, 0, 0))
        self.fp.draw(s, self, self.fp_sprites(), light, glow, bob, shx, shy)
        fpv = self.fp
        for sp, x0, y0, wpx, hpx, cz in fpv.last_sp:                  # كلام الوحوش واسامي اللاعبين
            g = sp.get('g')
            if g and g['say'] and g['a'] > 0.3:
                draw_text(s, str(g['say'][0]).replace("{name}", self.name()), 24, (220, 30, 30), int(x0 + wpx / 2), int(y0 - 26), 'c')
            if sp.get('name'):
                draw_text(s, sp['name'], 16, sp['ncol'], int(x0 + wpx / 2), int(y0 - 18), 'c')
        for e in self.eyes:                                           # عيون حمرا في الضلمة
            if (self.t * 0.9 + e['ph']) % 4 < 0.14:
                continue
            a = min(1.0, e['t'] * 1.5)
            pr = fpv.project(self, e['x'] / T, e['y'] / T, 1.35)
            if not pr:
                continue
            ex, ey, cz = pr
            col = int(ex // fpv.cw)
            if cz > 16 or (0 <= col < len(fpv.zwall) and fpv.zwall[col] < cz):
                continue
            sz = max(4, int(fpv.f * 0.09 / cz))
            for off in (-sz, sz):
                glow(s, int(ex) + off, int(ey), max(8, int(sz * 1.3)), (255, 30, 20), (80, 140, 200)[min(2, int(a * 3))])
                pygame.draw.ellipse(s, (255, 200, 190), (int(ex) + off - sz // 3, int(ey) - sz // 5, max(2, sz * 2 // 3), max(2, sz // 3)))
        self.fp_hand(s, bob)
        cx_, cy_ = SW // 2, SH // 2
        tgt = self.nearest() if (self.state == 'play' and not self.dlg) else None
        pygame.draw.circle(s, (255, 235, 200) if tgt else (150, 150, 150), (cx_, cy_), 3 if tgt else 2)
        if tgt:
            pygame.draw.circle(s, (255, 235, 200), (cx_, cy_), 11, 1)
        self._world_tail(s)

    def fp_hand(self, s, bob):
        """الكشاف في إيدك (تحت يمين الشاشة)"""
        sw_ = math.sin(self.t * (9.5 if self.running else 6)) * 6 if self.moving else math.sin(self.t * 1.4) * 1.5
        ox, oy = SW - 150 + int(sw_), SH - 6 + int(abs(bob) * 1.5)
        body = [(ox - 22, oy), (ox + 22, oy), (ox + 16, oy - 120), (ox - 16, oy - 120)]
        pygame.draw.polygon(s, (30, 30, 34), body)
        pygame.draw.polygon(s, (60, 60, 66), [(ox - 22, oy), (ox - 8, oy), (ox - 6, oy - 120), (ox - 16, oy - 120)])
        pygame.draw.rect(s, (90, 90, 98), (ox - 20, oy - 150, 40, 36), border_radius=4)
        pygame.draw.rect(s, (50, 50, 56), (ox - 20, oy - 150, 40, 36), 2, border_radius=4)
        pygame.draw.ellipse(s, (255, 244, 190) if self.flash_ok() else (70, 70, 74), (ox - 15, oy - 158, 30, 14))
        if self.flash_ok():
            glow(s, ox, oy - 152, 26, (255, 240, 170), 120)

    def _world_tail(self, s):
        if self.dash:
            self.draw_dash(s)
        if self.hall:                                                 # هلوسة سريعة
            _t, kind, hx, hy, word = self.hall
            if kind == 'ghost':
                draw_ghost(s, hx, hy + 90, 150, self.t, int(hx) % max(1, nmon() - 1))
            elif kind == 'word':
                draw_text(s, word, 64, (200, 10, 10), hx, hy, 'c')
            else:
                for off in (-14, 14):
                    glow(s, hx + off, hy, 14, (255, 30, 20), 200)
        if self.say:
            draw_text(s, self.say[0], 52, (200, 20, 20), SW // 2 + random.randint(-4, 4),
                      SH // 2 - 130 + random.randint(-4, 4), 'c')
        if self.pulse > 0.03 and self.state == 'play':                     # نبضة حمرا مع كل دقّة قلب
            pv = A.get('pulse')
            if pv is None:
                pv = A['pulse'] = pygame.Surface((SW, SH))
                pv.fill((150, 0, 0))
            pv.set_alpha(int(80 * self.pulse))
            s.blit(pv, (0, 0))
        if self.fear > 5:
            pulse = 1.0 + (0.12 * math.sin(self.t * (4 + self.fear / 15)) if self.fear > 40 else 0.0)
            A['vig'].set_alpha(min(255, int(255 * min(1, self.fear / 100) * pulse)))
            s.blit(A['vig'], (0, 0))
        if self.fear > 60 and self.state == 'play':                   # خرابيش دم على حروف الشاشة
            rr = random.Random(int(self.t * 5))
            for _ in range(int((self.fear - 55) / 8) + 1):
                x = rr.choice((rr.randint(0, 90), rr.randint(SW - 90, SW)))
                y = rr.randint(0, SH - 120)
                pygame.draw.line(s, (130 + rr.randint(0, 70), 8, 8), (x, y),
                                 (x + rr.randint(-30, 30), y + rr.randint(40, 110)), rr.randint(1, 3))
        if self.glitch_t > 0:
            self.glitch(s)
        self.draw_hud(s)
        if self.show_map:
            self.draw_map(s)
        if self.net_on:
            self.draw_chat(s)

    def draw_map(self, s):
        lv = self.lv
        sc = min((SW - 160) / lv.W, (SH - 200) / lv.H)
        ox, oy = (SW - lv.W * sc) / 2, 100 + (SH - 200 - lv.H * sc) / 2
        ov = pygame.Surface((SW, SH), pygame.SRCALPHA)
        ov.fill((0, 0, 0, 248))
        s.blit(ov, (0, 0))
        draw_text(s, "الخريطة - Tab للإغلاق", 30, (240, 200, 100), SW // 2, 36, 'c')
        seen = []
        for i, (nm, (x, y, w, h), c) in enumerate(lv.rooms):
            r = pygame.Rect(int(ox + x * sc), int(oy + y * sc), int(w * sc), int(h * sc))
            if i in self.visited:
                seen.append(pygame.Rect(x - 3, y - 3, w + 6, h + 6))
                pygame.draw.rect(s, tuple(min(255, v + 30) for v in c), r)
                pygame.draw.rect(s, (200, 170, 110), r, 1)
                if r.w > 70 and r.h > 24:
                    draw_text(s, nm, 16, (255, 255, 255), r.centerx, r.centery - 9, 'c')
            else:
                pygame.draw.rect(s, (46, 40, 38), r, 1)
        for o in self.objs:
            if o.kind in ('door', 'exit') and o.solid and any(z.collidepoint(o.rect.centerx // T, o.rect.centery // T) for z in seen):
                r = pygame.Rect(int(ox + o.rect.x / T * sc) - 2, int(oy + o.rect.y / T * sc) - 2,
                                max(5, int(o.rect.w / T * sc)) + 4, max(5, int(o.rect.h / T * sc)) + 4)
                pygame.draw.rect(s, (220, 40, 40) if o.kind == 'exit' else (230, 190, 60), r)
        pygame.draw.circle(s, (90, 200, 255), (int(ox + self.px / T * sc), int(oy + self.py / T * sc)), 5 + int(2 * math.sin(self.t * 6)))
        draw_text(s, "أحمر: باب الشقة   أصفر: باب مقفول   أزرق: إنت", 18, (180, 180, 180), SW // 2, SH - 40, 'c')

    def tinted_dir(self, tint):
        d = A['pdir_t'].get(tint)
        if d is None:
            d = []
            for row in A['pdir']:
                nr = []
                for f in row:
                    g = f.copy()
                    g.fill(tint, special_flags=pygame.BLEND_RGB_ADD)
                    nr.append(g)
                d.append(nr)
            A['pdir_t'][tint] = d
        return d

    def tinted_fx(self, idx, tint):
        key = (idx, tint)
        g = A['pfx_t'].get(key)
        if g is None:
            g = A['pfx'][idx].copy()
            g.fill(tint, special_flags=pygame.BLEND_RGB_ADD)
            A['pfx_t'][key] = g
        return g

    def draw_char(self, s, px, py, fx, fy, moving, t, tint=None, fl=False, mode=None, k=0):
        """الشخصية من الـ sprite sheet. mode: None عادي، 'hurt' إصابة، 'die' موت"""
        pygame.draw.ellipse(s, (0, 0, 0), (px - 11, py + 6, 22, 9))
        tint = tint if (tint and any(tint)) else None
        if mode in ('die', 'hurt'):
            idx = (4 if mode == 'die' else 0) + max(0, min(3, k))
            spr = self.tinted_fx(idx, tint) if tint else A['pfx'][idx]
        else:
            if abs(fx) > abs(fy):
                row = 1 if fx < 0 else 2
            else:
                row = 0 if fy > 0 else 3
            fi = int(t * 9) % 4 if moving else 0
            spr = (self.tinted_dir(tint) if tint else A['pdir'])[row][fi]
        bob = 0 if (moving or mode) else int(math.sin(t * 2.2) * 1.2)
        s.blit(spr, (px - spr.get_width() // 2, py + 12 - spr.get_height() + bob))
        if fl and mode is None:
            glow(s, int(px + fx * 14), int(py - 2 + fy * 8), 12, (255, 240, 170), 170)

    def draw_player(self, s, px, py):
        if A.get('art'):
            mode, k = None, 0
            if self.state == 'lose':
                mode, k = 'die', int(self.lose_t * 3)
            elif self.hurt_t > 0:
                mode, k = 'hurt', int((0.9 - self.hurt_t) * 6) % 4
            self.draw_char(s, px, py, self.fx, self.fy, self.moving and self.state == 'play', self.t,
                           fl=self.flash_ok(), mode=mode, k=k)
            return
        self.draw_player_old(s, px, py)

    def draw_player_old(self, s, px, py):
        t, fx, fy = self.t, self.fx, self.fy
        mv = self.moving
        bob = math.sin(t * 13) * 2 if mv else math.sin(t * 2) * 1
        pygame.draw.ellipse(s, (0, 0, 0), (px - 12, py + 6, 24, 10))
        tx, ty = px - fx * 18 + math.sin(t * 6) * 3, py + 12 - fy * 12
        cape = [(px - 9, py - 5 + bob), (px + 9, py - 5 + bob), (tx + 8, ty + 3), (tx - 8, ty - 2)]
        pygame.draw.polygon(s, (120, 18, 30), cape)
        pygame.draw.polygon(s, (70, 8, 16), cape, 2)
        pygame.draw.ellipse(s, (46, 66, 108), (px - 8, py - 8 + bob, 16, 20))
        pygame.draw.line(s, (200, 160, 60), (px - 8, py + 3 + bob), (px + 8, py + 3 + bob), 2)
        pygame.draw.rect(s, (30, 24, 24), (px - 6, py + 10, 5, 4))
        pygame.draw.rect(s, (30, 24, 24), (px + 1, py + 10 + (2 if mv and int(t * 8) % 2 else 0), 5, 4))
        hx, hy = px + fx * 2, py - 13 + bob
        pygame.draw.circle(s, (88, 18, 30), (int(px), int(py - 12 + bob)), 9)
        pygame.draw.circle(s, (232, 200, 168), (int(hx), int(hy + fy * 1.5)), 6)
        pygame.draw.circle(s, (20, 16, 16), (int(hx + fx * 2.5 - 2), int(hy + 1 + fy * 2)), 1)
        pygame.draw.circle(s, (20, 16, 16), (int(hx + fx * 2.5 + 2), int(hy + 1 + fy * 2)), 1)
        ax, ay = px + fx * 15, py - 2 + fy * 15 + bob
        pygame.draw.line(s, (232, 200, 168), (px + fx * 5, py - 2 + bob), (ax, ay), 3)
        pygame.draw.circle(s, (120, 120, 126), (int(ax), int(ay)), 4)
        if self.flash_ok():
            glow(s, int(ax), int(ay), 14, (255, 240, 170), 200)
            pygame.draw.circle(s, (255, 250, 200), (int(ax + fx * 2), int(ay + fy * 2)), 2)
        pygame.draw.circle(s, (90, 230, 255), (int(px), int(py - 1 + bob)), 2)

    def draw_bar(self, s, x, y, w, frac, color):
        pygame.draw.rect(s, (20, 20, 24), (x, y, w, 14))
        pygame.draw.rect(s, color, (x, y, int(w * max(0, min(1, frac))), 14))
        pygame.draw.rect(s, (150, 150, 150), (x, y, w, 14), 1)

    def draw_button(self, s, text, rect, selected=False, size=26):
        pygame.draw.rect(s, (60, 14, 14) if selected else (24, 20, 22), rect, border_radius=8)
        pygame.draw.rect(s, (200, 150, 80) if selected else (110, 90, 70), rect, 2, border_radius=8)
        draw_text(s, text, size, (255, 240, 210) if selected else (200, 190, 180), rect.centerx,
                  rect.centery - size * 0.7, 'c')

    def draw_hud(self, s):
        panel = pygame.Surface((SW, 78), pygame.SRCALPHA)
        panel.fill((0, 0, 0, 120))
        s.blit(panel, (0, 0))
        self.draw_face(s, 8, 8)
        draw_text(s, "الكشاف", 20, (230, 230, 200), 82, 8, 'l')
        self.draw_bar(s, 150, 12, 130, self.battery / 100 if self.flash else 0, (240, 210, 90))
        draw_text(s, S("بطاريات: {n}", n=self.spare), 20, (230, 230, 200), 290, 8, 'l')
        draw_text(s, "الخوف", 20, (230, 160, 160), 82, 38, 'l')
        self.draw_bar(s, 150, 42, 130, self.fear / 100, (200, 30, 30))
        draw_text(s, S("الشقة {a} / {b}", a=self.level, b=MAX_LEVEL), 22, (240, 200, 120), SW // 2, 6, 'c')
        r = pygame.Rect(SW // 2 - 50, 38, 100, 30)
        if self.net_on:
            draw_text(s, S("غرفة {r}  |  {n}/{m}", r=self.room_id, n=len(self.players), m=MAX_PLAYERS), 20, (160, 220, 255), SW // 2, 42, 'c')
        else:
            self.draw_button(s, "حفظ" if TOUCH else "حفظ - F5", r, False, 20)
        rx = SW - 16 - (125 if TOUCH else 0)                 # على اللمس: مكان لزراير الخريطة والقايمة
        draw_text(s, self.room, 26, (255, 255, 255), rx, 6, 'r')
        items = [str(self.lv.item_names[i]) if isinstance(self.lv.item_names[i], S) else tr(self.lv.item_names[i])
                 for i in ('ka', 'kb', 'small', 'exit') if i in self.inv and i in self.lv.item_names]
        draw_text(s, S("معاك: {i}", i=("، " if LANG == 'ar' else ", ").join(items) if items else "مفيش حاجة"), 18, (240, 210, 100), rx, 44, 'r')
        draw_text(s, S("الهدف: {g}", g=self.lv.goal(self)), 20, (200, 200, 200), 16, SH - 32, 'l')
        if not TOUCH:
            draw_text(s, "E: تفاعل   F: كشاف   Shift/K: جري   Tab: خريطة   Esc: قايمة", 18, (140, 140, 140), SW - 16, SH - 30, 'r')
        self.btns = [(r, 'save')] if (self.state == 'play' and not self.net_on) else []
        if self.net_on:
            self.draw_team(s)
        o = self.nearest()
        if o and not self.dlg and self.js_t <= 0 and self.state == 'play':
            draw_text(s, S("المس زر التفاعل - {n}" if TOUCH else "اضغط E - {n}", n=o.name), 24, (255, 255, 255), SW // 2, SH - 90, 'c')
        if self.toast_t > 0 and not self.dlg:
            t = txt(self.toast_s, 24, (255, 235, 200))
            bg = pygame.Surface((t.get_width() + 30, t.get_height() + 14), pygame.SRCALPHA)
            bg.fill((0, 0, 0, 170))
            s.blit(bg, (SW // 2 - bg.get_width() // 2, 100))
            s.blit(t, (SW // 2 - t.get_width() // 2, 107))
        if self.dlg:
            rtl = LANG == 'ar'
            lines = [tr(str(x)).replace("{name}", self.name()) for x in self.dlg]
            n = len(lines)
            h = 90 + 34 * n
            box = pygame.Surface((SW - 120, h), pygame.SRCALPHA)
            box.fill((10, 8, 8, 235))
            by = SH - h - 30
            s.blit(box, (60, by))
            pygame.draw.rect(s, (150, 120, 70), (60, by, SW - 120, h), 2)
            ax, al = (SW - 84, 'r') if rtl else (84, 'l')
            draw_text(s, self.dlg_title, 26, (240, 200, 100), ax, by + 10, al)
            for i, ln in enumerate(lines):
                draw_text(s, ln, 24, (230, 230, 230), ax, by + 50 + i * 34, al)
            draw_text(s, "المس الشاشة للمتابعة" if TOUCH else "اضغط E للمتابعة", 18, (150, 150, 150), 84 if rtl else SW - 84, by + h - 28, 'l' if rtl else 'r')

    def draw_face(self, s, x, y):
        """وش الشخصية في الركن: بيتغير حسب اللي بيحصل (خوف، خضّة، فرحة...)"""
        ex = self.expression()
        pygame.draw.rect(s, (10, 8, 12), (x - 2, y - 2, 66, 66), border_radius=6)
        face = A.get('expr_hud', {}).get(ex)
        if face is not None:
            jx = random.randint(-1, 1) if ex in ('scared', 'surprised') else 0
            jy = random.randint(-1, 1) if ex == 'scared' and self.fear >= 75 else 0
            s.blit(face, (x + jx, y + jy))
        col = {'scared': (220, 60, 60), 'surprised': (240, 210, 90), 'angry': (230, 110, 60),
               'sad': (110, 140, 220), 'happy': (120, 220, 120)}.get(ex, (150, 130, 110))
        pygame.draw.rect(s, col, (x - 2, y - 2, 66, 66), 2, border_radius=6)

    def small_face(self, name):
        d = A.setdefault('expr_s', {})
        f = d.get(name)
        if f is None and name in A.get('expr', {}):
            f = d[name] = pygame.transform.smoothscale(A['expr'][name], (24, 24))
        return f

    def draw_team(self, s):
        """قايمة صحابك: وشهم (بيتغير زي وشك) واسمهم، والميت بيبان بالرمادي"""
        y = 88
        for pid in sorted(self.players):
            if pid == self.my_id:
                continue
            p = self.peers.get(pid)
            dead = pid in self.dead_ids
            ex = 'sad' if dead else (p['ex'] if p else 'neutral')
            f = self.small_face(ex)
            if f is not None:
                s.blit(f, (SW - 16 - 24, y))
            col = (130, 130, 130) if dead else PEER_COLS[pid % 8]
            nm = self.pname(pid) + (str(S(" (خسر)")) if dead else "")
            draw_text(s, nm, 16, col, SW - 16 - 30, y + 2, 'r')
            y += 27

    def draw_js(self, s):
        el = self.js_dur - self.js_t
        if el < 0.07:
            s.fill((255, 255, 255))
            return
        s.fill((8, 0, 0))
        f0 = self.js_face or A['js'][0]
        z = 1.05 + el * 0.32
        th = int(SH * z)
        tw = int(f0.get_width() * th / f0.get_height())
        f = pygame.transform.smoothscale(f0, (tw, th))
        ox, oy = random.randint(-10, 10), random.randint(-10, 10)
        s.blit(f, (SW // 2 - tw // 2 + ox, int(SH * 0.42 - th * 0.25) + oy))
        red = pygame.Surface((SW, SH))
        red.fill((170, 0, 0))
        red.set_alpha(60 + random.randint(0, 30))
        s.blit(red, (0, 0))
        if self.js_text:
            draw_text(s, self.js_text, 72, (230, 20, 20), SW // 2 + random.randint(-6, 6),
                      SH - 170 + random.randint(-6, 6), 'c')
        fade = min(0.35, self.js_dur * 0.4)
        if self.js_t < fade:
            blk = pygame.Surface((SW, SH))
            blk.set_alpha(int(255 * (1 - self.js_t / fade)))
            s.blit(blk, (0, 0))

    def title_opts(self):
        o = []
        if self.profile and self.saved:
            o.append(('continue', S("كمّل اللعبة: {p} - الشقة {l}", p=self.profile['name'], l=self.saved['level'])))
        o += [('new', "لعبة جديدة"), ('online', "لعب أونلاين (لحد 8 لاعبين)"), ('quit', "خروج")]
        return o

    def draw_title(self, s):
        s.fill((0, 0, 0))
        self.btns = []
        if self.state == 'title':
            self.draw_menu(s)
        elif TOUCH:
            self.draw_profile_touch(s)
        else:
            self.draw_profile(s)
        A['vig'].set_alpha(90 if self.state == 'title' else 140)
        s.blit(A['vig'], (0, 0))

    def draw_help(self, s):
        """شاشة التحكمات بالعربي والإنجليزي مع اسامي صنّاع اللعبة"""
        self.btns = []
        if self.help_prev == 'pause':
            self.draw_world(s)
            ov = pygame.Surface((SW, SH), pygame.SRCALPHA)
            ov.fill((0, 0, 0, 215))
            s.blit(ov, (0, 0))
        else:
            s.fill((0, 0, 0))
        gold, dim, white = (240, 200, 100), (150, 150, 150), (225, 220, 210)
        draw_raw(s, "Controls", 40, gold, SW // 2 - 24, 36, 'r', 'en')
        draw_raw(s, "•", 40, (150, 40, 40), SW // 2, 36, 'c', 'en')
        draw_raw(s, "التحكمات", 40, gold, SW // 2 + 24, 36, 'l', 'ar')
        back = pygame.Rect(16, 12, 130, 40)
        pygame.draw.rect(s, (60, 14, 14), back, border_radius=8)
        pygame.draw.rect(s, (200, 150, 80), back, 2, border_radius=8)
        draw_raw(s, "Back", 20, (255, 240, 210), back.x + 14, back.y + 7, 'l', 'en')
        draw_raw(s, "رجوع", 20, (255, 240, 210), back.right - 14, back.y + 5, 'r', 'ar')
        self.btns.append((back, 'help_back'))
        y0, step = 96, 28
        for i, (key, en, ar) in enumerate(CONTROLS):
            y = y0 + i * step
            cap = pygame.Rect(SW // 2 - 120, y - 1, 240, 25)
            pygame.draw.rect(s, (30, 24, 26), cap, border_radius=6)
            pygame.draw.rect(s, (120, 95, 70), cap, 2, border_radius=6)
            draw_raw(s, key, 17, (255, 235, 200), cap.centerx, cap.y + 2, 'c', 'en')
            draw_raw(s, en, 19, white, 60, y, 'l', 'en')
            draw_raw(s, ar, 19, white, SW - 60, y - 2, 'r', 'ar')
        ty = y0 + len(CONTROLS) * step + 6
        draw_raw(s, "Touch: left stick = move  |  drag right side = look  |  USE = interact  |  LIGHT = flashlight", 15, dim, SW // 2, ty, 'c', 'en')
        draw_raw(s, "اللمس: الجويستيك = حركة  |  اسحب يمين الشاشة = بصّ حواليك  |  تفاعل  |  كشاف", 15, dim, SW // 2, ty + 20, 'c', 'ar')
        pygame.draw.line(s, (120, 95, 60), (SW // 2 - 280, 535), (SW // 2 + 280, 535), 1)
        draw_raw(s, CREDITS_EN, 22, gold, SW // 2, 543, 'c', 'en')
        draw_raw(s, CREDITS_AR, 22, gold, SW // 2, 570, 'c', 'ar')
        draw_raw(s, "© 2026  All rights reserved", 14, dim, SW // 2 - 14, 606, 'r', 'en')
        draw_raw(s, "جميع الحقوق محفوظة", 14, dim, SW // 2 + 14, 604, 'l', 'ar')
        A['vig'].set_alpha(90)
        s.blit(A['vig'], (0, 0))

    def draw_menu(self, s):
        logo = title_logo()
        logo.set_alpha(235 if random.random() > 0.04 else 110)             # وميض خفيف
        s.blit(logo, (28, (SH - logo.get_height()) // 2))
        cx = 705
        draw_text(s, "10 شقق... كل واحدة أكبر وأخطر.", 24, (210, 200, 190), cx, 62, 'c')
        draw_text(s, "دوّر على المفتاح واهرب.", 24, (210, 200, 190), cx, 96, 'c')
        draw_text(s, "لو الخوف اتملى أو الوحش لمسك... بتخسر وتعيد الشقة!", 21, (200, 120, 120), cx, 134, 'c')
        opts = self.title_opts()
        self.sel = min(self.sel, len(opts) - 1)
        bh, gap = (66, 80) if TOUCH else (56, 72)
        if len(opts) >= 4:
            bh, gap = (56, 68) if TOUCH else (50, 62)
        for i, (a, label) in enumerate(opts):
            r = pygame.Rect(cx - 215, 195 + i * gap, 430, bh)
            self.draw_button(s, label, r, i == self.sel, 24)
            self.btns.append((r, a))
        r = pygame.Rect(SW - 196, 10, 180, 48 if TOUCH else 40)
        self.draw_button(s, "English" if LANG == 'ar' else "العربية", r, False, 22)
        self.btns.append((r, 'lang'))
        r = pygame.Rect(SW - 196 - 190, 10, 180, 48 if TOUCH else 40)
        self.draw_button(s, "التحكمات", r, False, 22)
        self.btns.append((r, 'help'))
        if TOUCH:
            tips = ["الجويستيك: حركة - اسحبه بعيد للجري", "زر تفاعل: فتح وتقليب   |   زر كشاف: نور"]
        else:
            tips = ["WASD / الأسهم: حركة   |   Shift/K: جري", "E: تفاعل   |   F: كشاف   |   Tab: خريطة",
                    "L: اللغة   |   M: كتم الصوت   |   F11: ملء الشاشة"]
        tips += ["الكشاف بيخلّي الشبح يتراجع، والشموع بتهدّي خوفك.", "حاجة بتتحرك لما تدير ضهرك؟ بصّلها بالكشاف."]
        for i, ln in enumerate(tips):
            draw_text(s, ln, 18, (150, 150, 150), cx, max(445, 195 + len(opts) * gap + 12) + i * 27, 'c')
        draw_raw(s, CREDITS_EN, 15, (170, 140, 80), cx, 594, 'c', 'en')
        draw_raw(s, CREDITS_AR, 15, (170, 140, 80), cx, 614, 'c', 'ar')

    def draw_profile(self, s):
        fl = 150 + int(80 * abs(math.sin(self.t * 3))) if random.random() > 0.05 else 60
        draw_text(s, "بيت الهمس", 72, (fl, 20, 20), SW // 2, 50, 'c')
        draw_text(s, "عرّفنا بنفسك...", 34, (240, 200, 100), SW // 2, 140, 'c')
        labels = [('name', "الاسم"), ('day', "يوم الميلاد من 1 إلى 31"), ('month', "شهر الميلاد من 1 إلى 12")]
        rtl = LANG == 'ar'
        for i, (key, lab) in enumerate(labels):
            y = 230 + i * 80
            if rtl:
                draw_text(s, lab, 26, (230, 230, 220), SW // 2 + 300, y, 'r')
                box = pygame.Rect(SW // 2 - 300, y - 8, 360, 48)
            else:
                draw_text(s, lab, 26, (230, 230, 220), SW // 2 - 300, y, 'l')
                box = pygame.Rect(SW // 2 - 40, y - 8, 360, 48)
            pygame.draw.rect(s, (24, 20, 22), box, border_radius=6)
            pygame.draw.rect(s, (220, 170, 80) if i == self.field else (100, 90, 80), box, 2, border_radius=6)
            cur = "|" if (i == self.field and int(self.t * 2) % 2 == 0) else " "
            val = self.form[key]
            if val or i == self.field:
                if rtl:
                    draw_text(s, val + cur, 28, (255, 255, 255), box.right - 12, box.y + 6, 'r')
                else:
                    draw_text(s, val + cur, 28, (255, 255, 255), box.x + 12, box.y + 6, 'l')
            self.btns.append((box, 'field%d' % i))
        if self.form_err:
            draw_text(s, self.form_err, 22, (230, 80, 80), SW // 2, 470, 'c')
        r = pygame.Rect(SW // 2 - 150, 520, 300, 54)
        self.draw_button(s, "ابدأ - Enter", r, True)
        self.btns.append((r, 'submit'))
        draw_text(s, "Tab: الحقل اللي بعده   |   Esc: رجوع", 18, (140, 140, 140), SW // 2, 595, 'c')

    def draw_profile_touch(self, s):
        """شاشة التسجيل على الموبايل: كيبورد على الشاشة (من غير كيبورد النظام)"""
        rtl = LANG == 'ar'
        draw_text(s, "عرّفنا بنفسك...", 28, (240, 200, 100), SW // 2, 6, 'c')
        r = pygame.Rect(10, 8, 120, 42)
        self.draw_button(s, "رجوع", r, False, 22)
        self.btns.append((r, 'back'))
        spec = [(0, 'name', "الاسم", 330), (1, 'day', "يوم الميلاد", 190), (2, 'month', "شهر الميلاد", 190)]
        total = sum(w for _i, _k, _l, w in spec) + 40
        order = list(reversed(spec)) if rtl else spec
        x = (SW - total) // 2
        for i, key, lab, w in order:
            draw_text(s, lab, 17, (200, 200, 190), x + (w if rtl else 0), 54, 'r' if rtl else 'l')
            box = pygame.Rect(x, 78, w, 50)
            on = i == self.field
            pygame.draw.rect(s, (24, 20, 22), box, border_radius=8)
            pygame.draw.rect(s, (220, 170, 80) if on else (100, 90, 80), box, 2, border_radius=8)
            val = self.form[key] + ("|" if (on and int(self.t * 2) % 2 == 0) else " ")
            if self.form[key] or on:
                if rtl:
                    draw_text(s, val, 28, (255, 255, 255), box.right - 10, box.y + 6, 'r')
                else:
                    draw_text(s, val, 28, (255, 255, 255), box.x + 10, box.y + 6, 'l')
            self.btns.append((box, 'field%d' % i))
            x += w + 20
        if self.form_err:
            draw_text(s, self.form_err, 19, (230, 80, 80), SW // 2, 136, 'c')
        nxt = "التالي" if self.field < 2 else "ابدأ"
        top = 168
        if self.field == 0:
            rows = AR_ROWS if self.kb_lang == 'ar' else EN_ROWS
            kw, kh, gp = 70, 74, 8
            y = top
            for row in rows:
                x0 = (SW - (len(row) * kw + (len(row) - 1) * gp)) // 2
                for j, ch in enumerate(row):
                    rc = pygame.Rect(x0 + j * (kw + gp), y, kw, kh)
                    self.draw_button(s, ch, rc, False, 28)
                    self.btns.append((rc, 'k:' + ch))
                y += kh + gp
            bar = [('kbmode', "ABC" if self.kb_lang == 'ar' else "أب", 120), ('k: ', "مسافة", 330),
                   ('bksp', "مسح", 140), ('next', nxt, 200)]
            x0 = (SW - (sum(w for _a, _l, w in bar) + gp * (len(bar) - 1))) // 2
            for a, lab, w in bar:
                rc = pygame.Rect(x0, y + 6, w, kh)
                self.draw_button(s, lab, rc, a == 'next', 24)
                self.btns.append((rc, a))
                x0 += w + gp
        else:
            kw, kh, gp = 140, 78, 8
            x0 = (SW - (3 * kw + 2 * gp)) // 2
            keys = [('k:1', '1'), ('k:2', '2'), ('k:3', '3'), ('k:4', '4'), ('k:5', '5'), ('k:6', '6'),
                    ('k:7', '7'), ('k:8', '8'), ('k:9', '9'), ('bksp', "مسح"), ('k:0', '0'), ('next', nxt)]
            for n, (a, lab) in enumerate(keys):
                rc = pygame.Rect(x0 + (n % 3) * (kw + gp), top + (n // 3) * (kh + gp), kw, kh)
                self.draw_button(s, lab, rc, a == 'next', 28)
                self.btns.append((rc, a))

    def draw_trans(self, s):
        s.fill((0, 0, 0))
        a = min(1.0, self.trans_t / 0.8, (3.4 - self.trans_t) / 0.6)
        col = lambda c: tuple(int(v * max(0, a)) for v in c)
        n = self.next_n
        cells = DIMS[n][0] * DIMS[n][1]
        draw_text(s, S("الشقة {n}", n=n), 80, col((200, 30, 30)), SW // 2 + random.randint(-2, 2), 190, 'c')
        draw_text(s, "المفتاح فتح الباب... وقدامك شقة تانية.", 28, col((210, 200, 190)), SW // 2, 320, 'c')
        draw_text(s, S("عدد الأوض: {n}", n=cells), 28, col((240, 200, 100)), SW // 2, 370, 'c')
        if n in CHAPTER:
            draw_text(s, CHAPTER[n], 26, col((170, 150, 190)), SW // 2, 490, 'c')
        if n >= 6:
            draw_text(s, "الأشباح هنا أكتر... خلّي بالك.", 24, col((200, 90, 90)), SW // 2, 430, 'c')
        elif n >= 3:
            draw_text(s, "الشقة دي أصعب... والخضّات أكتر.", 24, col((200, 90, 90)), SW // 2, 430, 'c')

    # ------------------------------------------------ شاشات الأونلاين
    def online_opts(self):
        o = [('o_create', "افتح غرفة جديدة"), ('o_join', "ادخل غرفة برقم ID"),
             ('o_server', S("السيرفر: {a}", a=SERVER_ADDR or "مش متحدد - اضغط هنا"))]
        if not ANDROID:
            o.append(('o_local', "شغّل سيرفر على جهازي"))
        o.append(('o_back', "رجوع"))
        return o

    def key_btn(self, s, label, rect, action, size=26):
        self.draw_button(s, label, rect, False, size)
        self.btns.append((rect, action))

    def draw_keypad(self, s):
        """كيبورد أرقام على الشاشة للموبايل"""
        kw, kh, g = 110, 64, 10
        x0, y0 = SW // 2 - (3 * kw + 2 * g) // 2, 215
        keys = ['1', '2', '3', '4', '5', '6', '7', '8', '9', 'obksp', '0', 'o_go']
        for i, k in enumerate(keys):
            r = pygame.Rect(x0 + (i % 3) * (kw + g), y0 + (i // 3) * (kh + g), kw, kh)
            if k == 'obksp':
                self.key_btn(s, "مسح", r, k, 24)
            elif k == 'o_go':
                self.key_btn(s, "ادخل", r, k, 24)
            else:
                self.key_btn(s, k, r, 'ok:' + k, 30)

    def draw_osk(self, s):
        """كيبورد إنجليزي صغير لكتابة عنوان السيرفر"""
        rows = ["1234567890", "qwertyuiop", "asdfghjkl", "zxcvbnm.:-"]
        kw, kh, g = 84, 54, 6
        for ri, row in enumerate(rows):
            x0 = SW // 2 - (len(row) * (kw + g) - g) // 2
            for ci, ch in enumerate(row):
                r = pygame.Rect(x0 + ci * (kw + g), 215 + ri * (kh + g), kw, kh)
                self.key_btn(s, ch, r, 'ok:' + ch, 26)
        y = 215 + 4 * (kh + g)
        self.key_btn(s, "مسح", pygame.Rect(SW // 2 - 220, y, 200, kh), 'obksp', 24)
        self.key_btn(s, "حفظ", pygame.Rect(SW // 2 + 20, y, 200, kh), 'o_saveserver', 24)

    def draw_online(self, s):
        s.fill((0, 0, 0))
        self.btns = []
        st, cx = self.state, SW // 2
        if st == 'online':
            draw_text(s, "اللعب الأونلاين", 46, (240, 200, 100), cx, 36, 'c')
            draw_text(s, S("غرف بنظام الـ ID - لحد {n} لاعبين مع بعض", n=MAX_PLAYERS), 22, (200, 190, 180), cx, 98, 'c')
            opts = self.online_opts()
            self.sel = min(self.sel, len(opts) - 1)
            bh, gap = (60, 72) if TOUCH else (54, 66)
            for i, (a, label) in enumerate(opts):
                r = pygame.Rect(cx - 250, 145 + i * gap, 500, bh)
                self.draw_button(s, label, r, i == self.sel, 24)
                self.btns.append((r, a))
            y = 145 + len(opts) * gap + 6
            if self.online_err:
                draw_text(s, self.online_err, 22, (240, 110, 110), cx, y, 'c')
            if self.local_srv_msg:
                draw_text(s, self.local_srv_msg, 20, (160, 220, 255), cx, y + 32, 'c')
        elif st == 'online_join':
            draw_text(s, "اكتب رقم الغرفة (ID)", 40, (240, 200, 100), cx, 30, 'c')
            box = pygame.Rect(cx - 210, 92, 420, 90)
            pygame.draw.rect(s, (24, 20, 22), box, border_radius=10)
            pygame.draw.rect(s, (200, 150, 80), box, 2, border_radius=10)
            caret = "|" if int(self.t * 2) % 2 == 0 and len(self.inp) < 5 else ""
            draw_text(s, (self.inp + caret) or "-----", 64, (255, 240, 210), cx, 100, 'c')
            if self.online_err:
                draw_text(s, self.online_err, 22, (240, 110, 110), cx, 190, 'c')
            if TOUCH:
                self.draw_keypad(s)
                self.key_btn(s, "رجوع", pygame.Rect(16, 16, 130, 48), 'o_back2', 22)
            else:
                draw_text(s, "اكتب الأرقام بالكيبورد وبعدين Enter   |   Esc: رجوع", 20, (150, 150, 150), cx, 205, 'c')
                self.key_btn(s, "ادخل", pygame.Rect(cx - 150, 270, 300, 54), 'o_go', 24)
                self.key_btn(s, "رجوع", pygame.Rect(cx - 150, 340, 300, 54), 'o_back2', 24)
        elif st == 'online_server':
            draw_text(s, "عنوان السيرفر", 40, (240, 200, 100), cx, 24, 'c')
            box = pygame.Rect(cx - 400, 88, 800, 62)
            pygame.draw.rect(s, (24, 20, 22), box, border_radius=10)
            pygame.draw.rect(s, (200, 150, 80), box, 2, border_radius=10)
            caret = "|" if int(self.t * 2) % 2 == 0 else ""
            draw_text(s, self.inp + caret, 34, (255, 240, 210), cx, 96, 'c')
            draw_text(s, "مثال: 192.168.1.5:8765   (لو مكتبتش بورت بيتاخد 8765)", 18, (150, 150, 150), cx, 160, 'c')
            if TOUCH:
                self.draw_osk(s)
                self.key_btn(s, "رجوع", pygame.Rect(16, 16, 130, 48), 'o_back2', 22)
            else:
                self.key_btn(s, "حفظ", pygame.Rect(cx - 150, 230, 300, 54), 'o_saveserver', 24)
                self.key_btn(s, "رجوع", pygame.Rect(cx - 150, 300, 300, 54), 'o_back2', 24)
        elif st == 'connecting':
            draw_text(s, str(S("بيتصل بالسيرفر")) + "." * (int(self.t * 3) % 4), 40, (240, 200, 100), cx, 220, 'c')
            draw_text(s, SERVER_ADDR, 24, (160, 160, 160), cx, 280, 'c')
            self.key_btn(s, "إلغاء", pygame.Rect(cx - 150, 380, 300, 56), 'o_cancel', 24)
        elif st == 'lobby':
            draw_text(s, "رقم الغرفة", 26, (200, 190, 180), cx, 18, 'c')
            draw_text(s, self.room_id, 80, (255, 220, 120), cx, 46, 'c')
            draw_text(s, "ابعت الرقم ده لصحابك عشان يدخلوا الغرفة", 20, (170, 170, 170), cx, 146, 'c')
            ids = sorted(self.players)
            for i in range(MAX_PLAYERS):
                r = pygame.Rect(cx - 410 + (i % 2) * 420, 190 + (i // 2) * 52, 400, 44)
                pygame.draw.rect(s, (24, 20, 22), r, border_radius=8)
                pygame.draw.rect(s, (110, 90, 70), r, 2, border_radius=8)
                if i < len(ids):
                    pid = ids[i]
                    label = "%d. %s" % (i + 1, self.pname(pid))
                    if pid == self.host_id:
                        label += str(S("  (صاحب الغرفة)"))
                    if pid == self.my_id:
                        label += str(S("  (إنت)"))
                    draw_text(s, label, 22, PEER_COLS[pid % 8], r.centerx, r.y + 6, 'c')
                else:
                    draw_text(s, "- فاضي -", 20, (90, 90, 90), r.centerx, r.y + 8, 'c')
            draw_text(s, S("اللاعبين: {n} / {m}", n=len(ids), m=MAX_PLAYERS), 22, (200, 200, 200), cx, 410, 'c')
            if self.my_id == self.host_id:
                self.draw_button(s, "ابدأ اللعب", pygame.Rect(cx - 160, 460, 320, 56), self.sel == 0, 26)
                self.btns.append((pygame.Rect(cx - 160, 460, 320, 56), 'o_start'))
            else:
                draw_text(s, "مستني صاحب الغرفة يبدأ اللعب...", 24, (255, 230, 150), cx, 470, 'c')
            self.key_btn(s, "اخرج من الغرفة", pygame.Rect(cx - 160, 540, 320, 52), 'o_leave', 22)
        A['vig'].set_alpha(100)
        s.blit(A['vig'], (0, 0))
        if st == 'lobby':
            self.draw_chat(s)
            if not self.chat_open:
                draw_text(s, "T: شات" if not TOUCH else "", 16, (140, 140, 140), 16, SH - 30, 'l')
        if self.toast_t > 0 and st == 'lobby':
            draw_text(s, self.toast_s, 22, (255, 235, 200), cx, 606, 'c')

    def draw_lose(self, s):
        t = self.lose_t
        cx = SW // 2
        spectating = self.net_on and bool(self.spec_list()) and t > 2.6
        ov = pygame.Surface((SW, SH), pygame.SRCALPHA)
        a_ = 190 if not spectating else max(40, int(190 - (t - 2.6) * 200))
        ov.fill((50, 0, 0, min(a_, int(t * 160))))
        s.blit(ov, (0, 0))
        if spectating:                                                # بتتفرج على صحابك
            sl = self.spec_list()
            p = sl[self.spec_i % len(sl)]
            bar = pygame.Surface((SW, 70), pygame.SRCALPHA)
            bar.fill((0, 0, 0, 170))
            s.blit(bar, (0, 0))
            draw_text(s, S("خسرت - بتتفرج على: {n}", n=self.pname(p['id'])), 28, PEER_COLS[p['id'] % 8], cx, 6, 'c')
            hint = "" if TOUCH else "◄ ► / A D: غيّر اللي بتتفرج عليه   |   T: شات"
            draw_text(s, hint, 16, (170, 170, 170), cx, 44, 'c')
            if len(sl) > 1:
                r1, r2 = pygame.Rect(16, SH // 2 - 30, 70, 60), pygame.Rect(SW - 86, SH // 2 - 30, 70, 60)
                self.key_btn(s, "<", r1, 'sp-', 34)
                self.key_btn(s, ">", r2, 'sp+', 34)
            self.key_btn(s, "اخرج من الغرفة", pygame.Rect(SW - 196, SH - 54, 180, 42), 'menu', 18)
            return
        if t < 0.6:
            return
        shx = random.randint(-3, 3) if t < 2 else 0
        draw_text(s, "خسرت!", 84, (210, 30, 30), cx + shx, 40, 'c')
        why = "الخوف ملا العداد... قلبك مستحملش!" if self.lose_why == 'fear' else "الوحش مسكك!"
        draw_text(s, why, 30, (240, 200, 190), cx, 150, 'c')
        face = A.get('expr', {}).get(self.expression())
        if face is not None:
            fs = pygame.transform.scale(face, (150, 150))
            s.blit(fs, (cx - 75, 205))
            pygame.draw.rect(s, (220, 60, 60) if t < 1.6 else (110, 140, 220), (cx - 77, 203, 154, 154), 3, border_radius=8)
        if self.net_on:
            if not self.spec_list():
                draw_text(s, "كلكم خسرتوا... الشقة هتبدأ من الأول!", 28, (255, 230, 150), cx, 395, 'c')
            else:
                draw_text(s, "هتتفرج على صحابك...", 28, (255, 230, 150), cx, 395, 'c')
            self.key_btn(s, "اخرج من الغرفة", pygame.Rect(cx - 160, 540, 320, 52), 'menu', 22)
        else:
            draw_text(s, S("الشقة {n} هتبدأ من الأول", n=self.level), 28, (255, 230, 150), cx, 385, 'c')
            if t > 1.2:
                r1, r2 = pygame.Rect(cx - 170, 450, 340, 58), pygame.Rect(cx - 170, 522, 340, 52)
                self.draw_button(s, "حاول تاني", r1, True, 26)
                self.draw_button(s, "القايمة الرئيسية", r2, False, 22)
                self.btns += [(r1, 'retry'), (r2, 'menu')]

    def draw_pause(self, s):
        ov = pygame.Surface((SW, SH), pygame.SRCALPHA)
        ov.fill((0, 0, 0, 170))
        s.blit(ov, (0, 0))
        draw_text(s, "قايمة اللعبة", 44, (240, 200, 100), SW // 2, 130, 'c')
        self.btns = []
        for i, (a, label) in enumerate([('resume', "كمّل"), ('save', "حفظ اللعبة"), ('help', "التحكمات"),
                                        ('lang', "English" if LANG == 'ar' else "العربية"),
                                        ('menu', "القايمة الرئيسية"), ('quit', "خروج")]):
            r = pygame.Rect(SW // 2 - 200, 180 + i * 58, 400, 48)
            self.draw_button(s, label, r, i == self.sel)
            self.btns.append((r, a))
        if self.toast_t > 0:
            draw_text(s, self.toast_s, 24, (255, 235, 200), SW // 2, 545, 'c')

    def draw_win(self, s):
        self.win_t += 1 / 60
        ov = pygame.Surface((SW, SH))
        ov.fill((245, 245, 235))
        ov.set_alpha(min(255, int(self.win_t / 3 * 255)))
        s.blit(ov, (0, 0))
        if self.win_t > 2.5:
            draw_text(s, "هربت!", 80, (40, 90, 40), SW // 2, 130, 'c')
            draw_text(s, S("برافو يا {n}... عديت الشقق العشرة!", n=self.name()), 32, (50, 50, 50), SW // 2, 270, 'c')
            draw_text(s, "طلع عليك نور الفجر... والبيوت ورا ضهرك ساكتة.", 26, (50, 50, 50), SW // 2, 330, 'c')
            draw_text(s, S("بس سمعت همس بيقول: \"{n}... استنّى\"", n=self.name()), 26, (130, 40, 40), SW // 2, 380, 'c')
            draw_text(s, STORY_END, 24, (110, 40, 40), SW // 2, 432, 'c')
            draw_text(s, "المس الشاشة للرجوع للقايمة" if TOUCH else "Enter: القايمة الرئيسية      Esc: خروج", 26, (60, 60, 60), SW // 2, 500, 'c')

    # ------------------------------------------------ أحداث
    def form_input(self, text):
        key = ('name', 'day', 'month')[self.field]
        if key != 'name':
            text = text.translate({0x660 + i: ord('0') + i for i in range(10)})
            text = ''.join(c for c in text if c.isdigit())
        else:
            text = ''.join(c for c in text if c.isprintable())
        lim = 14 if key == 'name' else 2
        self.form[key] = (self.form[key] + text)[:lim]
        self.form_err = ""

    def form_next(self):
        if self.field < 2 and self.form[('name', 'day', 'month')[self.field]]:
            self.field += 1
        else:
            self.submit_form()

    def on_background(self):
        """التطبيق راح للخلفية: بنوقّف اللعبة ونحفظ"""
        if self.state == 'play' and self.js_t <= 0:
            self.state, self.sel = 'pause', 0
        try:
            if self.profile:
                self.save(silent=True)
        except Exception:
            pass

    def submit_form(self):
        n = self.form['name'].strip()
        try:
            d, m = int(self.form['day']), int(self.form['month'])
        except ValueError:
            d = m = 0
        if not n:
            self.form_err, self.field = "اكتب اسمك الأول!", 0
            return
        if not (1 <= d <= 31 and 1 <= m <= 12):
            self.form_err = "تاريخ الميلاد مش صح: اليوم من 1 إلى 31 والشهر من 1 إلى 12"
            return
        self.profile = dict(name=n, day=d, month=m, seed=random.randint(1, 10 ** 6))
        self.saved = None
        prepare_voice_async(n)
        pygame.key.stop_text_input()
        pygame.key.set_repeat()
        if self.after_profile == 'online':                 # جاي من زرار الأونلاين: نحفظ البروفايل ونروح لقايمة الأونلاين
            self.after_profile = None
            write_save(dict(profile=self.profile))
            self.state, self.sel, self.online_err = 'online', 0, ""
            return
        self.new_session()
        self.state = 'play'
        self.save(silent=True)
        self.maybe_birthday()

    def online_input(self, text):
        self.online_err = ""
        if self.state == 'online_join':
            text = text.translate({ord(c): ord('0') + i for i, c in enumerate("٠١٢٣٤٥٦٧٨٩")})
            self.inp = (self.inp + ''.join(c for c in text if c in '0123456789'))[:5]
        elif self.state == 'online_server':
            self.inp = (self.inp + ''.join(c for c in text if c.isascii() and c.isprintable() and c != ' '))[:60]

    def start_local_server(self):
        """بيشغّل السيرفر جوه اللعبة على الكمبيوتر (صحابك على نفس الشبكة أو VPN بيدخلوا بالـ IP)"""
        try:
            import server as srv
            srv.run_in_thread(NET_PORT)
            m = "السيرفر اشتغل على جهازك."
        except OSError:
            m = "فيه سيرفر شغّال بالفعل على البورت ده - هنستخدمه."
        except Exception:
            self.online_err = "مقدرتش أشغّل السيرفر هنا."
            return
        set_server("127.0.0.1:%d" % NET_PORT)
        self.online_err = ""
        self.local_srv_msg = S("{m} صحابك يكتبوا في خانة السيرفر: {a}", m=m, a="%s:%d" % (lan_ip(), NET_PORT))

    def do_action(self, a):
        if a == 'quit':
            return False
        if a == 'continue':
            if 'voice' not in SND:
                prepare_voice_async(self.name())
            self.load_game()
            self.state = 'play'
            self.maybe_birthday()
        elif a == 'new':
            self.after_profile = None
            self.state, self.field, self.form_err = 'profile', 0, ""
            self.form = {'name': '', 'day': '', 'month': ''}
            self.kb_lang = LANG
            if not TOUCH:
                pygame.key.start_text_input()
                pygame.key.set_repeat(400, 40)
        elif a == 'lang':
            set_lang('en' if LANG == 'ar' else 'ar')
            pygame.display.set_caption("Whispering House" if LANG == 'en' else "بيت الهمس")
        elif a == 'help':
            self.help_prev = self.state if self.state in ('title', 'pause') else 'title'
            self.state = 'help'
        elif a == 'help_back':
            self.state, self.sel = self.help_prev, 0
        elif a == 'resume':
            self.state = 'play'
        elif a == 'save':
            self.save()
            if self.state == 'pause':
                self.toast_t = max(self.toast_t, 2.0)
        elif a == 'menu':
            if self.net_on or self.net:
                self.net_close()
            self.dying = False
            self.js_t, self.js_after = 0.0, None
            self.saved = (load_save() or {}).get('game')
            self.state, self.sel = 'title', 0
        elif a == 'retry':
            if self.state == 'lose' and not self.net_on:
                self.retry()
        elif a == 'online':
            if not self.profile:
                self.do_action('new')
                self.after_profile = 'online'
            else:
                self.state, self.sel, self.online_err = 'online', 0, ""
        elif a == 'o_create':
            self.start_connect(dict(t='create'))
        elif a == 'o_join':
            self.inp, self.online_err, self.state = "", "", 'online_join'
            if not TOUCH:
                pygame.key.start_text_input()
        elif a == 'o_go':
            if len(self.inp) == 5:
                pygame.key.stop_text_input()
                self.start_connect(dict(t='join', room=self.inp))
            else:
                self.online_err = "الرقم لازم يبقى 5 أرقام."
        elif a == 'o_server':
            self.inp, self.online_err, self.state = SERVER_ADDR, "", 'online_server'
            if not TOUCH:
                pygame.key.start_text_input()
        elif a == 'o_saveserver':
            set_server(self.inp)
            pygame.key.stop_text_input()
            self.state, self.sel, self.local_srv_msg = 'online', 0, ""
        elif a == 'o_local':
            self.start_local_server()
        elif a == 'o_back':
            self.state, self.sel = 'title', 0
        elif a == 'o_back2':
            pygame.key.stop_text_input()
            self.state, self.sel, self.online_err = 'online', 0, ""
        elif a == 'o_start':
            if self.my_id == self.host_id:
                self.net_send(dict(t='start'))
        elif a in ('o_leave', 'o_cancel'):
            self.leave_online('online')
        elif a.startswith('q:'):
            self.send_chat(CHAT_QUICK[int(a[2:])])
            self.close_chat()
        elif a == 'sp+':
            self.spec_i += 1
        elif a == 'sp-':
            self.spec_i -= 1
        elif a == 'qx':
            self.close_chat()
        elif a == 'obksp':
            self.inp = self.inp[:-1]
        elif a.startswith('ok:'):
            self.online_input(a[3:])
        elif a == 'submit':
            self.submit_form()
        elif a == 'back':
            self.after_profile = None
            pygame.key.stop_text_input()
            pygame.key.set_repeat()
            self.state = 'title'
        elif a.startswith('k:'):
            self.form_input(a[2:])
        elif a == 'bksp':
            key = ('name', 'day', 'month')[self.field]
            self.form[key] = self.form[key][:-1]
        elif a == 'kbmode':
            self.kb_lang = 'en' if self.kb_lang == 'ar' else 'ar'
        elif a == 'next':
            self.form_next()
        elif a.startswith('field'):
            self.field = int(a[5:])
        return True

    def handle(self, e):
        st = self.state
        if self.chat_open and self.net_on and e.type in (pygame.KEYDOWN, pygame.TEXTINPUT):
            if self.chat_event(e):
                return True
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and self.js_t <= 0 and not self.dlg:
            for r, a in self.btns:
                if r.collidepoint(e.pos):
                    return self.do_action(a)
        elif e.type == pygame.MOUSEMOTION and st in ('title', 'pause', 'online', 'lobby', 'lose'):
            for i, (r, _a) in enumerate(self.btns):
                if r.collidepoint(e.pos):
                    self.sel = i
        elif e.type == pygame.TEXTINPUT and st == 'profile':
            self.form_input(e.text)
        elif e.type == pygame.TEXTINPUT and st in ('online_join', 'online_server'):
            self.online_input(e.text)
        elif e.type == pygame.KEYDOWN:
            k = e.key
            if st == 'title':
                n = len(self.title_opts())
                if k == pygame.K_UP:
                    self.sel = (self.sel - 1) % n
                elif k == pygame.K_DOWN:
                    self.sel = (self.sel + 1) % n
                elif k in (pygame.K_RETURN, pygame.K_SPACE) and self.btns:
                    return self.do_action(self.btns[self.sel][1])
                elif k == pygame.K_h:
                    return self.do_action('help')
                elif k == pygame.K_ESCAPE:
                    return False
            elif st == 'help':
                if k in (pygame.K_ESCAPE, pygame.K_RETURN, pygame.K_SPACE, pygame.K_h, pygame.K_BACKSPACE):
                    return self.do_action('help_back')
            elif st == 'profile':
                if k == pygame.K_ESCAPE:
                    pygame.key.stop_text_input()
                    pygame.key.set_repeat()
                    self.state = 'title'
                elif k in (pygame.K_TAB, pygame.K_DOWN):
                    self.field = (self.field + 1) % 3
                elif k == pygame.K_UP:
                    self.field = (self.field - 1) % 3
                elif k == pygame.K_BACKSPACE:
                    key = ('name', 'day', 'month')[self.field]
                    self.form[key] = self.form[key][:-1]
                elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    if self.field < 2 and self.form[('name', 'day', 'month')[self.field]]:
                        self.field += 1
                    else:
                        self.submit_form()
            elif st == 'play' and self.js_t <= 0:
                if k == pygame.K_ESCAPE:
                    if self.dlg:
                        self.close_dialog()
                    else:
                        self.state, self.sel = 'pause', 0
                elif k in (pygame.K_e, pygame.K_SPACE, pygame.K_RETURN):
                    if self.dlg:
                        self.close_dialog()
                    else:
                        self.interact()
                elif k == pygame.K_f and not self.dlg:
                    self.flash = not self.flash
                elif k == pygame.K_F5:
                    self.save()
                elif k == pygame.K_t and self.net_on:
                    self.open_chat()
                elif k == pygame.K_TAB:
                    self.show_map = not self.show_map
            elif st == 'pause':
                if k == pygame.K_ESCAPE:
                    self.state = 'play'
                elif k == pygame.K_UP:
                    self.sel = (self.sel - 1) % 6
                elif k == pygame.K_DOWN:
                    self.sel = (self.sel + 1) % 6
                elif k == pygame.K_h:
                    return self.do_action('help')
                elif k in (pygame.K_RETURN, pygame.K_SPACE):
                    return self.do_action(self.btns[self.sel][1])
            elif st == 'online':
                n = len(self.online_opts())
                if k == pygame.K_UP:
                    self.sel = (self.sel - 1) % n
                elif k == pygame.K_DOWN:
                    self.sel = (self.sel + 1) % n
                elif k in (pygame.K_RETURN, pygame.K_SPACE) and self.btns:
                    return self.do_action(self.btns[min(self.sel, len(self.btns) - 1)][1])
                elif k == pygame.K_ESCAPE:
                    self.do_action('o_back')
            elif st in ('online_join', 'online_server'):
                if k == pygame.K_ESCAPE:
                    self.do_action('o_back2')
                elif k == pygame.K_BACKSPACE:
                    self.inp = self.inp[:-1]
                elif k in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    self.do_action('o_go' if st == 'online_join' else 'o_saveserver')
            elif st == 'connecting':
                if k == pygame.K_ESCAPE:
                    self.do_action('o_cancel')
            elif st == 'lobby':
                if k == pygame.K_t:
                    self.open_chat()
                elif k == pygame.K_ESCAPE:
                    self.do_action('o_leave')
                elif k in (pygame.K_RETURN, pygame.K_SPACE) and self.my_id == self.host_id:
                    self.do_action('o_start')
            elif st == 'lose':
                if k == pygame.K_t and self.net_on:
                    self.open_chat()
                elif self.net_on and k in (pygame.K_RIGHT, pygame.K_d):
                    self.spec_i += 1
                elif self.net_on and k in (pygame.K_LEFT, pygame.K_a):
                    self.spec_i -= 1
                elif k in (pygame.K_RETURN, pygame.K_SPACE, pygame.K_e) and not self.net_on and self.lose_t > 1.2:
                    self.retry()
                elif k == pygame.K_ESCAPE:
                    self.do_action('menu')
            elif st == 'win':
                if k == pygame.K_ESCAPE:
                    return False
                if k == pygame.K_RETURN and self.win_t > 2.5:
                    if self.net_on:
                        self.net_close()
                    else:
                        self.saved = None
                    self.state, self.sel = 'title', 0
        return True


# ================================================================= الشاشة واللمس
REAL_GEO = dict(ox=0, oy=0, sc=1.0)
_TLOGO = {}
_pres = {}


def title_logo():
    if 'img' not in _TLOGO:
        img = pygame.image.load(asset("logo.png")).convert()
        h = SH - 16
        _TLOGO['img'] = pygame.transform.smoothscale(img, (int(img.get_width() * h / img.get_height()), h))
    return _TLOGO['img']


def show_splash(screen, msg=""):
    """شاشة تحميل باللوجو"""
    try:
        img = title_logo()
        screen.fill((0, 0, 0))
        screen.blit(img, ((SW - img.get_width()) // 2, 8))
        if msg:
            pygame.draw.rect(screen, (0, 0, 0), (0, SH - 60, SW, 60))
            draw_text(screen, msg, 22, (200, 190, 180), SW // 2, SH - 44, 'c')
        present(screen)
        pygame.event.pump()
    except Exception:
        pass


def unity_splash(screen, fade_in=0.9, hold=2.0, fade_out=0.8):
    """شاشة افتتاحية زي Unity: اللوجو بيظهر بالتدريج، بيثبت، وبعدين بيختفي. أي ضغطة بتعدّيها."""
    try:
        raw = pygame.image.load(asset("logo.png")).convert()
        sc = min(SW / raw.get_width(), SH / raw.get_height())                 # بنفس النسبة من غير قص
        img = pygame.transform.smoothscale(raw, (max(1, int(raw.get_width() * sc)), max(1, int(raw.get_height() * sc))))
        pos = ((SW - img.get_width()) // 2, (SH - img.get_height()) // 2)
        clock = pygame.time.Clock()
        total = fade_in + hold + fade_out
        t = 0.0
        while t < total:
            for e in pygame.event.get():
                if e.type == pygame.QUIT:
                    pygame.quit()
                    raise SystemExit
                if e.type in (pygame.KEYDOWN, pygame.MOUSEBUTTONDOWN, pygame.FINGERDOWN) and t > 0.3:
                    t = max(t, total - fade_out)                              # تخطّي: يروح على الاختفاء علطول
            if t < fade_in:
                a = t / fade_in
            elif t < fade_in + hold:
                a = 1.0
            else:
                a = max(0.0, (total - t) / fade_out)
            a = a * a * (3 - 2 * a)                                           # حركة ناعمة (smoothstep)
            screen.fill((0, 0, 0))
            img.set_alpha(int(255 * a))
            screen.blit(img, pos)
            present(screen)
            t += min(clock.tick(60) / 1000.0, 0.05)
        screen.fill((0, 0, 0))
        present(screen)
    except SystemExit:
        raise
    except Exception:
        pass


def present(canvas, touch=None, game=None):
    """على الموبايل: بنكبّر الصورة على الشاشة الحقيقية (بنفس النسبة) وبنرسم أزرار اللمس فوقها"""
    real = pygame.display.get_surface()
    if not TOUCH or real is None or real is canvas:
        pygame.display.flip()
        return
    rw, rh = real.get_size()
    key = (rw, rh, id(real))
    if _pres.get('key') != key:
        sc = min(rw / SW, rh / SH)
        dw, dh = max(1, int(SW * sc)), max(1, int(SH * sc))
        ox, oy = (rw - dw) // 2, (rh - dh) // 2
        real.fill((0, 0, 0))
        _pres.update(key=key, size=(dw, dh), sub=real.subsurface((ox, oy, dw, dh)))
        REAL_GEO.update(ox=ox, oy=oy, sc=sc)
    ox, oy = REAL_GEO['ox'], REAL_GEO['oy']
    if ox:
        real.fill((0, 0, 0), (0, 0, ox, rh))
        real.fill((0, 0, 0), (rw - ox, 0, ox, rh))
    if oy:
        real.fill((0, 0, 0), (0, 0, rw, oy))
        real.fill((0, 0, 0), (0, rh - oy, rw, oy))
    try:
        if ANDROID:
            pygame.transform.scale(canvas, _pres['size'], _pres['sub'])
        else:
            pygame.transform.smoothscale(canvas, _pres['size'], _pres['sub'])
    except Exception:
        real.blit(pygame.transform.scale(canvas, _pres['size']), (ox, oy))
    if touch is not None:
        touch.draw(real, game)
    pygame.display.flip()


class Touch:
    """زراير اللمس: جويستيك (بيظهر مكان إصبعك في الشمال) + تفاعل + كشاف + خريطة + قايمة"""
    DEAD = 0.2
    KEYS = {'E': (pygame.K_e, 'e'), 'F': (pygame.K_f, 'f'), 'MAP': (pygame.K_TAB, ''), 'PAUSE': (pygame.K_ESCAPE, ''), 'CHAT': (pygame.K_t, 't')}
    LABELS = {'E': "تفاعل", 'F': "كشاف", 'MAP': "خريطة", 'PAUSE': None, 'CHAT': "شات"}

    def __init__(self):
        self.stick = None            # dict(id, ox, oy, x, y)
        self.held = {}               # إصبع -> زر
        self.finger_seen = False
        self.look = None             # سحب الإصبع اليمين بيلفّ الكاميرا
        self._spr = {}

    # ---------------- أماكن الأزرار (بالبكسل الحقيقي للشاشة)
    def geo(self, rw, rh):
        u = rh / 640.0
        ox, oy, sc = REAL_GEO['ox'], REAL_GEO['oy'], REAL_GEO['sc']
        return {'E': ((rw - 135 * u, rh - 140 * u), 66 * u),
                'F': ((rw - 275 * u, rh - 92 * u), 48 * u),
                'MAP': ((ox + (SW - 112) * sc, oy + 39 * sc), 27 * sc),
                'PAUSE': ((ox + (SW - 44) * sc, oy + 39 * sc), 27 * sc),
                'CHAT': ((ox + (SW - 180) * sc, oy + 39 * sc), 27 * sc)}

    def active(self, game):
        return game.state == 'play' and not game.dlg and game.js_t <= 0 and not game.show_map and not game.chat_open

    def to_logical(self, x, y):
        sc = REAL_GEO['sc'] or 1.0
        return (x - REAL_GEO['ox']) / sc, (y - REAL_GEO['oy']) / sc

    def hit(self, x, y, rw, rh, game=None):
        for role, ((cx, cy), r) in self.geo(rw, rh).items():
            if role == 'CHAT' and not (game and game.net_on):
                continue
            if math.hypot(x - cx, y - cy) <= r * 1.25:
                return role
        return None

    def key(self, game, k, ch=''):
        return game.handle(pygame.event.Event(pygame.KEYDOWN, key=k, mod=0, unicode=ch, scancode=0))

    # ---------------- الأحداث: بيرجّع (اتصرّف فيه؟، اللعبة شغّالة؟)
    def handle_event(self, e, game):
        t = e.type
        real = pygame.display.get_surface()
        rw, rh = real.get_size()
        if t in (pygame.FINGERDOWN, pygame.FINGERUP, pygame.FINGERMOTION):
            self.finger_seen = True
            x, y, fid = e.x * rw, e.y * rh, ('f', e.finger_id)
            kind = {pygame.FINGERDOWN: 'down', pygame.FINGERUP: 'up', pygame.FINGERMOTION: 'move'}[t]
        elif t == pygame.MOUSEBUTTONDOWN and e.button == 1:
            x, y, fid, kind = e.pos[0], e.pos[1], ('m',), 'down'
        elif t == pygame.MOUSEBUTTONUP and e.button == 1:
            x, y, fid, kind = e.pos[0], e.pos[1], ('m',), 'up'
        elif t == pygame.MOUSEMOTION and e.buttons[0]:
            x, y, fid, kind = e.pos[0], e.pos[1], ('m',), 'move'
        else:
            return False, True
        if fid == ('m',) and self.finger_seen:                # الماوس هنا مجرد نسخة مكرّرة من اللمس
            return True, True
        if kind == 'down':
            return True, self.down(fid, x, y, game, rw, rh)
        if kind == 'move':
            self.move(fid, x, y, rh, game)
        else:
            self.up(fid, game)
        return True, True

    def down(self, fid, x, y, game, rw, rh):
        st = game.state
        if self.active(game):
            role = self.hit(x, y, rw, rh, game)
            if role:
                self.held[fid] = role
                return self.key(game, *self.KEYS[role])
            if x < rw * 0.5 and self.stick is None:               # جويستيك عايم: بيظهر مكان إصبعك
                self.stick = dict(id=fid, ox=x, oy=y, x=x, y=y)
                return True
            if x >= rw * 0.5 and y > rh * 0.22 and self.look is None and game.fp_on():
                self.look = dict(id=fid, x=x)
                return True
        lx, ly = self.to_logical(x, y)
        click = pygame.event.Event(pygame.MOUSEBUTTONDOWN, pos=(int(lx), int(ly)), button=1)
        if st == 'play':
            if game.js_t > 0:
                return True
            if game.dlg:
                return self.key(game, pygame.K_e, 'e')            # أي لمسة = كمّل الكلام
            if game.show_map:
                return self.key(game, pygame.K_TAB)
            return game.handle(click)                             # زرار الحفظ في الـ HUD
        if st == 'win':
            return self.key(game, pygame.K_RETURN)
        if st in ('title', 'pause', 'help', 'profile', 'lose') or st in ONLINE_STATES or game.chat_open:
            return game.handle(click)
        return True

    def move(self, fid, x, y, rh, game):
        lk = self.look
        if lk and lk['id'] == fid:
            game.ang += (x - lk['x']) * 0.0058 * (640.0 / max(1, rh))
            lk['x'] = x
            return
        st = self.stick
        if not st or st['id'] != fid:
            return
        st['x'], st['y'] = x, y
        R = 92 * rh / 640.0
        dx, dy = x - st['ox'], y - st['oy']
        d = math.hypot(dx, dy)
        v = min(1.0, d / R)
        if v < self.DEAD:
            game.joy, game.joy_run = (0.0, 0.0), False
        else:
            game.joy, game.joy_run = (dx / d, dy / d), d > R * 1.2    # اسحب بره الدايرة = جري

    def up(self, fid, game):
        self.held.pop(fid, None)
        if self.look and self.look['id'] == fid:
            self.look = None
        if self.stick and self.stick['id'] == fid:
            self.stick = None
            game.joy, game.joy_run = (0.0, 0.0), False

    # ---------------- الرسم
    def sprite(self, role, r, state):
        k = (role, int(r), state, LANG)
        sp = self._spr.get(k)
        if sp is None:
            R = int(r)
            d = 2 * R + 6
            sp = pygame.Surface((d, d), pygame.SRCALPHA)
            fill = {'n': (18, 8, 8, 140), 'h': (96, 24, 22, 190), 'p': (160, 48, 36, 220)}[state]
            edge = (150, 110, 70, 200) if state == 'n' else (235, 185, 100, 240)
            pygame.draw.circle(sp, fill, (R + 3, R + 3), R)
            pygame.draw.circle(sp, edge, (R + 3, R + 3), R, max(2, R // 16))
            if role == 'PAUSE':
                bw, bh = max(4, R // 5), max(10, R // 2)
                for dx in (-bw, bw):
                    pygame.draw.rect(sp, (255, 240, 215, 240), (R + 3 + dx - bw // 2, R + 3 - bh // 2, bw, bh), border_radius=2)
            else:
                t = txt(self.LABELS[role], max(12, int(R * 0.44)), (255, 240, 215))
                sp.blit(t, ((d - t.get_width()) // 2, (d - t.get_height()) // 2))
            self._spr[k] = sp
        return sp

    def ring(self, r, kind):
        k = ('ring', int(r), kind)
        sp = self._spr.get(k)
        if sp is None:
            R = int(r)
            d = 2 * R + 6
            sp = pygame.Surface((d, d), pygame.SRCALPHA)
            if kind == 'base':
                pygame.draw.circle(sp, (255, 255, 255, 22), (R + 3, R + 3), R)
                pygame.draw.circle(sp, (255, 255, 255, 80), (R + 3, R + 3), R, 3)
            elif kind == 'idle':
                pygame.draw.circle(sp, (255, 255, 255, 12), (R + 3, R + 3), R)
                pygame.draw.circle(sp, (255, 255, 255, 45), (R + 3, R + 3), R, 2)
            else:
                pygame.draw.circle(sp, (214, 150, 90, 130), (R + 3, R + 3), R)
                pygame.draw.circle(sp, (240, 200, 130, 200), (R + 3, R + 3), R, 3)
            self._spr[k] = sp
        return sp

    def draw(self, real, game):
        if game is None or not self.active(game):
            return
        rw, rh = real.get_size()
        u = rh / 640.0
        R = 92 * u
        if self.stick:
            st = self.stick
            real.blit(self.ring(R, 'base'), (st['ox'] - R - 3, st['oy'] - R - 3))
            dx, dy = st['x'] - st['ox'], st['y'] - st['oy']
            d = math.hypot(dx, dy)
            if d > R:
                dx, dy = dx / d * R, dy / d * R
            real.blit(self.ring(40 * u, 'knob'), (st['ox'] + dx - 40 * u - 3, st['oy'] + dy - 40 * u - 3))
        else:
            real.blit(self.ring(R, 'idle'), (150 * u - R - 3, rh - 150 * u - R - 3))
        near = game.nearest() is not None
        pressed = set(self.held.values())
        for role, ((cx, cy), r) in self.geo(rw, rh).items():
            if role == 'CHAT' and not game.net_on:
                continue
            if role in pressed:
                state = 'p'
            elif (role == 'E' and near) or (role == 'F' and game.flash and game.battery > 0):
                state = 'h'
            else:
                state = 'n'
            real.blit(self.sprite(role, r, state), (cx - r - 3, cy - r - 3))


# ================================================================= التشغيل
def setup():
    global SR, AUDIO, SND
    pygame.mixer.pre_init(44100, -16, 1, 1024 if ANDROID else 512)
    pygame.init()
    pygame.display.set_caption("Whispering House")
    try:
        pygame.display.set_icon(pygame.image.load(asset("icon_window.png")))      # أيقونة اللعبة
    except Exception:
        pass
    if TOUCH:
        try:
            pygame.display.set_mode((0, 0) if ANDROID else (1280, 576),
                                    pygame.FULLSCREEN if ANDROID else pygame.RESIZABLE)
        except Exception:
            pygame.display.set_mode((SW, SH))
        screen = pygame.Surface((SW, SH)).convert()                                  # اللعبة بترسم هنا وبعدين بتتكبّر
    else:
        try:
            screen = pygame.display.set_mode((SW, SH), pygame.FULLSCREEN | pygame.SCALED)   # ملء الشاشة
        except Exception:
            screen = pygame.display.set_mode((SW, SH))
    unity_splash(screen)                                                           # دخلة اللوجو قبل أي حاجة
    show_splash(screen)
    try:
        if not pygame.mixer.get_init():
            pygame.mixer.init(44100, -16, 1, 1024 if ANDROID else 512)
        SR = pygame.mixer.get_init()[0]
        SND = load_or_build_sounds(lambda m: show_splash(screen, m))
        AUDIO = True
    except Exception as ex:
        print("الصوت مش شغال:", ex)
        AUDIO = False
    A['faces'] = [make_face(7, 0), make_face(21, 1), make_face(33, 2)]
    A['ghost'] = make_ghost()
    A['ghost_big'] = pygame.transform.smoothscale(A['ghost'], (250, 416))
    A['ghost_big_f'] = pygame.transform.flip(A['ghost_big'], True, False)
    A['vig'] = make_vignette()
    load_art()
    add_extra_monsters()
    return screen


def main():
    global VIEW3D
    load_settings()
    screen = setup()
    game = Game()
    touch = Touch() if TOUCH else None
    pygame.display.set_caption("Whispering House" if LANG == 'en' else "بيت الهمس")
    if game.profile:
        prepare_voice_async(game.name())
    clock = pygame.time.Clock()
    if AUDIO:
        SND['drone'].play(loops=-1)
        apply_volume()
    game.maybe_birthday()          # لو النهارده عيد ميلادك: الوحش بيستقبلك أول ما تفتح اللعبة
    back_key = getattr(pygame, 'K_AC_BACK', None)               # زرار الرجوع في أندرويد
    bg_event = getattr(pygame, 'APP_WILLENTERBACKGROUND', None)
    running = True
    grabbed = False
    while running:
        dt = min(clock.tick(60) / 1000.0, 0.05)
        for e in pygame.event.get():
            if bg_event is not None and e.type == bg_event:
                game.on_background()
                continue
            if touch:
                handled, alive = touch.handle_event(e, game)
                if handled:
                    running = running and alive
                    continue
            if e.type == pygame.KEYDOWN and back_key is not None and e.key == back_key:
                e = pygame.event.Event(pygame.KEYDOWN, key=pygame.K_ESCAPE, mod=0, unicode='', scancode=0)
            if e.type == pygame.KEYDOWN and e.key == pygame.K_F11:
                if not TOUCH:
                    pygame.display.toggle_fullscreen()
                continue
            if (e.type == pygame.MOUSEMOTION and not TOUCH and game.fp_on() and game.state == 'play'
                    and not game.dlg and not game.chat_open and not game.show_map and game.js_t <= 0):
                game.ang += e.rel[0] * MOUSE_SENS                    # الماوس بيلفّ الكاميرا
                continue
            if e.type == pygame.KEYDOWN and game.state not in ('profile', 'online_join', 'online_server'):
                if e.key == pygame.K_v and game.state in ('play', 'pause'):
                    VIEW3D = not VIEW3D
                    game.toast("المنظور: أول (3D)" if VIEW3D else "المنظور: من فوق", 1.8)
                    continue
                if e.key == pygame.K_l:
                    game.do_action('lang')
                    continue
                if e.key == pygame.K_m:
                    change_volume(mute=True)
                    game.toast(S("الصوت: {n}%", n=int(MASTER * 100)), 1.5)
                    continue
                if e.key in (pygame.K_MINUS, pygame.K_KP_MINUS, pygame.K_EQUALS, pygame.K_PLUS, pygame.K_KP_PLUS):
                    change_volume(-0.1 if e.key in (pygame.K_MINUS, pygame.K_KP_MINUS) else 0.1)
                    game.toast(S("الصوت: {n}%", n=int(MASTER * 100)), 1.5)
                    continue
            if e.type == pygame.QUIT or not game.handle(e):
                running = False
        want = (not TOUCH and game.fp_on() and game.state == 'play' and not game.dlg and not game.chat_open
                and not game.show_map and game.js_t <= 0)
        if want != grabbed:                                           # الماوس بيتقفل جوه اللعبة وقت اللعب بس
            grabbed = want
            pygame.event.set_grab(want)
            pygame.mouse.set_visible(not want)
        game.tick_js(dt)
        game.net_tick(dt)
        if game.state == 'play':
            game.update(dt)
        elif game.state == 'trans':
            game.update_trans(dt)
        elif game.state == 'lose':
            game.update_lose(dt)
        else:
            game.t += dt
            in_pause = game.state == 'pause' or (game.state == 'help' and game.help_prev == 'pause')
            if game.js_t <= 0 or in_pause:
                game.update(dt) if in_pause else None
        game.draw(screen)
        present(screen, touch, game)
    pygame.quit()


# ================================================================= الترجمة الإنجليزية
EN.update({
'''المنظور: أول (3D)''': '''View: first person (3D)''',
'''المنظور: من فوق''': '''View: top-down''',
'''تحت وسادة الكنبة''': '''under the sofa cushion''',
'''في الدرج''': '''in the drawer''',
'''ورا الكتب''': '''behind the books''',
'''في الدولاب العلوي''': '''in the upper cupboard''',
'''بين الكتب''': '''between the books''',
'''البيت القديم''': '''The Old House''',
'''أوضة النوم''': '''Bedroom''',
'''المكتبة''': '''Library''',
'''المطبخ''': '''Kitchen''',
'''الصالة''': '''Hall''',
'''الحمّام''': '''Bathroom''',
'''أوضة الأطفال''': '''Children's Room''',
'''المخزن''': '''Storeroom''',
'''أوضة الضيوف''': '''Guest Room''',
'''السفرة''': '''Dining Room''',
'''البدروم''': '''Basement''',
'''العلّية''': '''Attic''',
'''المكتب''': '''Study''',
'''أوضة الغسيل''': '''Laundry Room''',
'''الشرفة''': '''Balcony''',
'''أوضة الخياطة''': '''Sewing Room''',
'''أوضة الموسيقى''': '''Music Room''',
'''المرسم''': '''Art Studio''',
'''الطرقة الكبيرة''': '''Grand Corridor''',
'''أوضة الأجداد''': '''Grandparents' Room''',
'''أوضة الصلاة''': '''Prayer Room''',
'''غرفة الكتب القديمة''': '''Old Books Room''',
'''أوضة الألعاب''': '''Playroom''',
'''الأنتريه''': '''Sitting Room''',
'''المخبأ''': '''Hideout''',
'''غرفة المراية''': '''Mirror Room''',
'''مخزن الخشب''': '''Woodshed''',
'''أوضة الساعة''': '''Clock Room''',
'''غرفة المرضى''': '''Sickroom''',
'''القبو''': '''Cellar''',
'''أوضة الضوء الأحمر''': '''Red Light Room''',
'''غرفة الدُمى''': '''Doll Room''',
'''أوضة السفرجي''': '''Butler's Room''',
'''غرفة النجف''': '''Chandelier Room''',
'''{n}... استنّى''': '''{n}... wait''',
'''مش هتهرب يا {n}''': '''You won't escape, {n}''',
'''{n}.. ورااااك''': '''{n}.. behind youuuu''',
'''أنا شايفك يا {n}''': '''I see you, {n}''',
'''تعالى يا {n}... متخافش''': '''Come here, {n}... don't be afraid''',
'''{n}... كنت مستنيك''': '''{n}... I was waiting for you''',
'''{n}... أنا واقف ورا الباب''': '''{n}... I'm standing behind the door''',
'''{n}.. بصّ ورا''': '''{n}.. look behind you''',
'''مش لوحدك يا {n}''': '''You're not alone, {n}''',
'''{n}... سامعك وإنت بتتنفّس''': '''{n}... I can hear you breathing''',
'''فاضل خطوة واحدة يا {n}''': '''One step left, {n}''',
'''ليه سبتني لوحدي يا {n}؟''': '''Why did you leave me alone, {n}?''',
'''فاضي.''': '''Empty.''',
'''مفيش حاجة هنا... بس حاسس إن حد بيبصلك.''': '''Nothing here... but it feels like someone is watching you.''',
'''الغبار هنا لسه مهزوز... حد لمس المكان من لحظة.''': '''The dust here is still disturbed... someone touched this a moment ago.''',
'''سمعت همس خفيف طالع من هنا.''': '''You hear a faint whisper coming from here.''',
'''ريحة رطوبة تقيلة... وحاجة تانية أوحش.''': '''A heavy smell of damp... and something worse.''',
'''فيه بصمة إيد صغيرة على السطح.''': '''A small handprint on the surface.''',
'''فيه خربشة على الخشب: "اخرج".''': '''Scratched into the wood: "GET OUT".''',
'''مفيش حاجة جوه... بس كان فيه حد هنا.''': '''Nothing inside... but someone was here.''',
'''حاسس إن المكان ده اتحرّك ورايا... مش متأكد.''': '''It feels like this moved behind me... not sure.''',
'''أوضة المعيشة''': '''Living Room''',
'''الممر''': '''Corridor''',
'''ورقة على الترابيزة''': '''Note on the Table''',
'''ورقة بين الكتب''': '''Note Between the Books''',
'''مذكرات قديمة''': '''Old Diary''',
'''ورقة على المكتب''': '''Note on the Desk''',
'''السرير''': '''Bed''',
'''ترابيزة القهوة''': '''Coffee Table''',
'''البوتجاز''': '''Stove''',
'''الحوض''': '''Sink''',
'''الكتب''': '''Books''',
'''الكرسي الهزّاز''': '''Rocking Chair''',
'''الخزنة''': '''Safe''',
'''الترابيزة''': '''Table''',
'''الباب الأمامي''': '''Front Door''',
'''المكتبة الصغيرة''': '''Small Bookcase''',
'''الكنبة''': '''Sofa''',
'''البيانو''': '''Piano''',
'''الكومودينو''': '''Nightstand''',
'''الدولاب''': '''Wardrobe''',
'''الدُرج''': '''Drawer''',
'''رف الكتب''': '''Bookshelf''',
'''مكتب المكتبة''': '''Library Desk''',
'''كرسي هزّاز''': '''Rocking Chair''',
'''التلاجة''': '''Fridge''',
'''الدولاب العلوي''': '''Upper Cupboard''',
'''ترابيزة السفرة''': '''Dining Table''',
'''باب المكتب - مقفول''': '''Study Door - locked''',
'''مكتب كبير''': '''Big Desk''',
'''الصورة الكبيرة''': '''Large Portrait''',
'''مفتاح المكتب النحاسي''': '''Brass Study Key''',
'''المفتاح الصغير''': '''Small Key''',
'''مفتاح الباب الأمامي''': '''Front Door Key''',
'''دوّر على مفتاح المكتب النحاسي''': '''Find the brass study key''',
'''الصندوق الخشب''': '''Wooden Chest''',
'''الخزانة''': '''Cabinet''',
'''المراية الكبيرة''': '''Large Mirror''',
'''الصورة''': '''Portrait''',
'''الدُمية الكبيرة''': '''Large Doll''',
'''مفتاح الشقة''': '''Apartment Key''',
'''فاضي دلوقتي.''': '''Empty now.''',
'''اقرا الأوراق ودوّر على المفاتيح''': '''Read the notes and look for keys''',
'''ورقة مكتوبة بخط مرتعش:''': '''A note in shaky handwriting:''',
'''"الباب الكبير اتقفل لوحده... ومش هيتفتح غير بمفتاحه.''': '''"The big door locked itself... and only its key will open it.''',
'''المفتاح في المكتب اللي فوق، والمكتب مقفول.''': '''The key is in the study upstairs, and the study is locked.''',
'''دوّر كويس... وماتبصّش ورا."''': '''Search well... and do not look behind you."''',
'''لقيت ورقة قديمة:''': '''You found an old note:''',
'''"المفتاح النحاسي بتاع المكتب كنت دايمًا''': '''"I always kept the brass key to the study''',
'''أخبّيه في دولاب أوضة النوم."''': '''hidden in the bedroom wardrobe."''',
'''"كل ليلة بسمع خطوات قدام باب الأوضة.''': '''"Every night I hear footsteps outside the bedroom door.''',
'''النهارده الخطوات وقفت... جوه الأوضة."''': '''Tonight the footsteps stopped... inside the room."''',
'''آخر صفحة متبلّلة بحاجة حمرا...''': '''The last page is soaked in something red...''',
'''"درج المكتب الكبير مفتاحه صغير.''': '''"The big desk drawer has a small key.''',
'''كنت بحطه في حتة باردة... في المطبخ."''': '''I kept it somewhere cold... in the kitchen."''',
'''السرير متبهدل... والملاية لسه دافية!''': '''The bed is a mess... and the sheet is still warm!''',
'''كوباية شاي على الترابيزة... ولسه بتطلّع بخار.''': '''A cup of tea on the table... still steaming.''',
'''البوتجاز بارد... بس سامع صوت غليان من جوه الحلّة!''': '''The stove is cold... but you hear boiling from inside the pot!''',
'''حوالين الترابيزة أربع كراسي. الكرسي الرابع لسه بيهتز.''': '''Four chairs around the table. The fourth is still shaking.''',
'''الحنفية بتنقّط... والميّه لونها مش طبيعي.''': '''The tap is dripping... and the water is an unnatural color.''',
'''كل الكتب دي عن الأرواح والأحلام المزعجة.''': '''All these books are about spirits and disturbing dreams.''',
'''كتاب مفتوح على صفحة مكتوب فيها: "هو شايفك".''': '''A book open to a page that reads: "He sees you".''',
'''الكرسي بيهتز لوحده... بعدت عنه بسرعة.''': '''The chair rocks by itself... you back away quickly.''',
'''خزنة محتاجة رقم سري، ومفيش حاجة هنا تفتحها.''': '''A safe that needs a code, and nothing here opens it.''',
'''الدولاب فاضي دلوقتي.''': '''The wardrobe is empty now.''',
'''التلاجة فاضية... وريحتها وحشة.''': '''The fridge is empty... and it smells awful.''',
'''الدرج فاضي دلوقتي.''': '''The drawer is empty now.''',
'''باب المكتب''': '''Study Door''',
'''فتحت باب المكتب!''': '''You opened the study door!''',
'''اهرب من الباب الأمامي!''': '''Escape through the front door!''',
'''افتح باب المكتب، فوق ناحية اليمين''': '''Open the study door, upper right''',
'''الشقة {n}''': '''Apartment {n}''',
'''باب الشقة''': '''Apartment Door''',
'''مفتاح {r}''': '''{r} Key''',
'''محتاج مفتاح صغير.''': '''You need a small key.''',
'''والأوضة مقفولة، وعلى بابها قفل تقيل.''': '''The room is locked, with a heavy lock on its door.''',
'''ورقة مرمية''': '''Discarded Note''',
'''اهرب من باب الشقة!''': '''Escape through the apartment door!''',
'''يا غريب''': '''stranger''',
'''الخريطة - Tab للإغلاق''': '''Map - Tab to close''',
'''أحمر: باب الشقة   أصفر: باب مقفول   أزرق: إنت''': '''Red: apartment door   Yellow: locked door   Blue: you''',
'''الكشاف''': '''Flashlight''',
'''الخوف''': '''Fear''',
'''حفظ - F5''': '''Save - F5''',
'''التحكمات''': '''Controls''',
'''E: تفاعل   F: كشاف   Shift/K: جري   Tab: خريطة   Esc: قايمة''': '''E: interact   F: flashlight   Shift/K: run   Tab: map   Esc: menu''',
'''بيت الهمس''': '''Whispering House''',
'''المفتاح فتح الباب... وقدامك شقة تانية.''': '''The key opened the door... and another apartment lies ahead.''',
'''قايمة اللعبة''': '''Game Menu''',
'''تاريخ الميلاد مش صح: اليوم من 1 إلى 31 والشهر من 1 إلى 12''': '''Invalid birth date: day 1 to 31, month 1 to 12''',
'''جوه الدولاب لقيت مفتاح نحاسي تقيل.''': '''Inside the wardrobe you found a heavy brass key.''',
'''ده مفتاح المكتب.''': '''It is the study key.''',
'''التلاجة ريحتها وحشة...''': '''The fridge smells terrible...''',
'''لقيت مفتاح صغير متلزّق في الباب من جوه.''': '''You found a small key stuck to the door from the inside.''',
'''الدرج الكبير مقفول بقفل صغير.''': '''The big drawer is locked with a small lock.''',
'''فتحت الدرج بالمفتاح الصغير...''': '''You opened the drawer with the small key...''',
'''لقيت مفتاح كبير صدّي: مفتاح الباب الأمامي!''': '''You found a big rusty key: the front door key!''',
'''يلا اجري على الباب!''': '''Now run to the door!''',
'''الباب مقفول بمفتاح نحاسي.''': '''The door is locked with a brass key.''',
'''لازم تلاقيه.''': '''You have to find it.''',
'''الباب تقيل ومقفول بإحكام.''': '''The door is heavy and tightly locked.''',
'''محتاج مفتاحه... ومش معاك.''': '''You need its key... and you don't have it.''',
'''افتح درج المكتب''': '''Open the desk drawer''',
'''دوّر على مفتاح صغير للدرج''': '''Find a small key for the drawer''',
'''أوضة {n}''': '''Room {n}''',
'''باب {r} - مقفول''': '''{r} Door - locked''',
'''في {f} في {r}''': '''in the {f} in the {r}''',
'''في {r}''': '''in the {r}''',
'''فتحت {f}...''': '''You opened the {f}...''',
'''ولقيت {k}!''': '''and found the {k}!''',
'''فيه قفل صغير على {f}.''': '''The {f} has a small lock on it.''',
'''المفتاح الكبير بتاع الشقة جوّه {r}.''': '''The big apartment key is inside the {r}.''',
'''مفتاح {r} مخبّي {h}.''': '''The {r} key is hidden {h}.''',
'''مفتاح {r} {h}.''': '''The {r} key is {h}.''',
'''المفتاح الصغير بتاع الدُرج... {h}.''': '''The small key to the drawer... {h}.''',
'''جوه {f}''': '''inside the {f}''',
'''دوّر على مفتاح الشقة جوه {r}''': '''Find the apartment key inside the {r}''',
'''افتح باب {r}''': '''Open the {r} door''',
'''باب {r}''': '''{r} Door''',
'''فتحت باب {r}!''': '''You opened the {r} door!''',
'''الباب مقفول بقفل تقيل.''': '''The door has a heavy lock.''',
'''محتاج مفتاح {r}.''': '''You need the {r} key.''',
'''محتاج مفتاح الشقة... ومش معاك.''': '''You need the apartment key... and you don't have it.''',
'''{t} - عدد الأوض: {n}''': '''{t} - Rooms: {n}''',
'''أهلًا بيك تاني يا {n}...''': '''Welcome back, {n}...''',
'''حاسس إن في حد بيراقبك...''': '''You feel like someone is watching you...''',
'''غيّرت بطارية الكشاف.''': '''You changed the flashlight battery.''',
'''بطاريات: {n}''': '''Batteries: {n}''',
'''الشقة {a} / {b}''': '''Apartment {a} / {b}''',
'''معاك: {i}''': '''Carrying: {i}''',
'''الهدف: {g}''': '''Goal: {g}''',
'''اضغط E للمتابعة''': '''Press E to continue''',
'''لعبة جديدة''': '''New Game''',
'''خروج''': '''Exit''',
'''10 شقق... كل واحدة أكبر وأخطر. دوّر على المفتاح واهرب.''': '''10 apartments... each bigger and scarier. Find the key and escape.''',
'''مفيش موت في اللعبة... بس خضّات كتير!''': '''No death in this game... just lots of scares!''',
'''عرّفنا بنفسك...''': '''Tell us about yourself...''',
'''ابدأ - Enter''': '''Start - Enter''',
'''Tab: الحقل اللي بعده   |   Esc: رجوع''': '''Tab: next field   |   Esc: back''',
'''عدد الأوض: {n}''': '''Rooms: {n}''',
'''الأشباح هنا أكتر... خلّي بالك.''': '''More ghosts here... be careful.''',
'''هربت!''': '''You escaped!''',
'''طلع عليك نور الفجر... والبيوت ورا ضهرك ساكتة.''': '''Dawn light rises on you... and the houses behind you fall silent.''',
'''Enter: القايمة الرئيسية      Esc: خروج''': '''Enter: main menu      Esc: exit''',
'''اكتب اسمك الأول!''': '''Type your name first!''',
'''تم حفظ اللعبة''': '''Game saved''',
'''مقدرتش أحفظ الملف!''': '''Couldn't save the file!''',
'''حاجة وقعت وراك!!''': '''Something fell behind you!!''',
'''النور رجع...''': '''The lights are back...''',
'''الكشاف فصل! دوّر على بطاريات.''': '''The flashlight died! Find batteries.''',
'''اضغط E - {n}''': '''Press E - {n}''',
'''الحركة: WASD أو الأسهم | Shift/K: جري | E: تفاعل | F: الكشاف | Tab: خريطة''': '''Move: WASD or arrows | Shift/K: run | E: interact | F: flashlight | Tab: map''',
'''نصيحة: الكشاف بيخلّي الشبح يتراجع، والشموع بتهدّي خوفك.''': '''Tip: the flashlight pushes ghosts back, and candles calm your fear.''',
'''L: اللغة   M: كتم الصوت   - / +: مستوى الصوت   F11: ملء الشاشة''': '''L: language   M: mute   - / +: volume   F11: fullscreen''',
'''الاسم''': '''Name''',
'''يوم الميلاد من 1 إلى 31''': '''Birth day, 1 to 31''',
'''شهر الميلاد من 1 إلى 12''': '''Birth month, 1 to 12''',
'''الشقة دي أصعب... والخضّات أكتر.''': '''This apartment is harder... with more scares.''',
'''كمّل''': '''Resume''',
'''حفظ اللعبة''': '''Save Game''',
'''القايمة الرئيسية''': '''Main Menu''',
'''برافو يا {n}... عديت الشقق العشرة!''': '''Bravo, {n}... you cleared all ten apartments!''',
'''بس سمعت همس بيقول: "{n}... استنّى"''': '''But you heard a whisper say: "{n}... wait"''',
'''...ومكتوب في آخرها: "{name}"''': '''...and at the very end it says: "{name}"''',
'''كل الأنوار طفت!...''': '''All the lights went out!...''',
'''دوّرت تاني... مفيش حاجة.''': '''You searched again... nothing.''',
'''سمعت صرير باب بيتفتح... في مكان ما.''': '''You hear a door creaking open... somewhere.''',
'''مين اللي بيهمس؟!''': '''Who's whispering?!''',
'''خطوات... جاية من فوق.''': '''Footsteps... coming from above.''',
'''مفيش حاجة''': '''Nothing''',
'''كمّل اللعبة: {p} - الشقة {l}''': '''Continue: {p} - Apartment {l}''',
'''لقيت بطارية للكشاف {w}!''': '''You found a flashlight battery {w}!''',
'''النغمة طلعت من البيانو... وإيدك لسه ما لمستوش!''': '''A note rang out from the piano... and you haven't touched it!''',
'''الصوت: {n}%''': '''Volume: {n}%''',
'''راجل عينيه بتتابعك في كل مكان...''': '''A man whose eyes follow you everywhere...''',
'''ويمكن عينيه اتحركت فعلًا.''': '''And maybe his eyes really did move.''',
'''، ''': ''', ''',
})


EN.update({
'''حد بيخبط... من جوه الحيطة!''': '''Someone is knocking... from inside the wall!''',
'''سمعت عياط طفل... بعيد.''': '''You hear a child crying... far away.''',
'''ضحكة طفل... ورا الباب!''': '''A child's giggle... behind the door!''',
'''علبة موسيقى بتشتغل لوحدها...''': '''A music box is playing by itself...''',
'''حاسس بنفس بارد ورا رقبتك...''': '''You feel cold breath on your neck...''',
'''باب اتقفل بقوة في مكان ما!''': '''A door slammed shut somewhere!''',
'''الباب اتقفل وراك بقوة!''': '''A door slammed shut behind you!''',
'''حاسس إن في عيون بتبصلك من الضلمة...''': '''You feel eyes watching you from the dark...''',
'''فيه حاجة واقفة في الضلمة... متدّيش ضهرك!''': '''Something stands in the dark... don't turn your back!''',
'''الشمعة طفت لوحدها!''': '''The candle went out by itself!''',
'''في الضلمة... حد بيتنفّس جنبك.''': '''In the dark... someone is breathing beside you.''',
'''المراية ساكتة... بس حاسس إنها مستنية.''': '''The mirror is still... but it feels like it's waiting.''',
'''بصّيت في المراية... مفيش غير انعكاسك.''': '''You looked into the mirror... only your reflection.''',
'''لحظة... ليه انعكاسك بيبتسم؟''': '''Wait... why is your reflection smiling?''',
'''دُمية قديمة وعنيها زجاج لامع.''': '''An old doll with shiny glass eyes.''',
'''رقبتها مايلة ناحيتك... مكانتش كده من شوية.''': '''Its neck is tilted toward you... it wasn't like that a moment ago.''',
'''الدُمية بتبصلك... ومكانها اتغيّر!''': '''The doll stares at you... and it has moved!''',
'''اطلع''': '''GET OUT''',
'''هو وراك''': '''HE'S BEHIND YOU''',
'''شايفك''': '''I SEE YOU''',
'''مش هتخرج''': '''YOU WON'T LEAVE''',
'''متبصّش''': '''DON'T LOOK''',
'''وراك''': '''BEHIND YOU''',
'''هو هنا''': '''HE'S HERE''',
'''حاجة بتتحرك لما تدير ضهرك؟ بصّلها بالكشاف... وهتقف مكانها.''': '''Something moves when you turn your back? Look at it with the flashlight... and it freezes.''',
})


EN.update({
'''جاري تجهيز الأصوات... (أول مرة بس)''': '''Preparing sounds... (first launch only)''',
'''10 شقق... كل واحدة أكبر وأخطر.''': '''10 apartments... each one bigger and deadlier.''',
'''دوّر على المفتاح واهرب.''': '''Find the key and escape.''',
'''الجويستيك: حركة - اسحبه بعيد للجري''': '''Joystick: move - drag far to run''',
'''زر تفاعل: فتح وتقليب   |   زر كشاف: نور''': '''USE button: open & search   |   LIGHT button: flashlight''',
'''WASD / الأسهم: حركة   |   Shift/K: جري''': '''WASD / Arrows: move   |   Shift/K: run''',
'''E: تفاعل   |   F: كشاف   |   Tab: خريطة''': '''E: interact   |   F: flashlight   |   Tab: map''',
'''L: اللغة   |   M: كتم الصوت   |   F11: ملء الشاشة''': '''L: language   |   M: mute   |   F11: fullscreen''',
'''الكشاف بيخلّي الشبح يتراجع، والشموع بتهدّي خوفك.''': '''The flashlight pushes ghosts back, and candles calm your fear.''',
'''حاجة بتتحرك لما تدير ضهرك؟ بصّلها بالكشاف.''': '''Moves when you look away? Light it up.''',
'''تفاعل''': '''USE''',
'''كشاف''': '''LIGHT''',
'''خريطة''': '''MAP''',
'''المس زر التفاعل - {n}''': '''Tap USE - {n}''',
'''المس الشاشة للمتابعة''': '''Tap to continue''',
'''المس الشاشة للرجوع للقايمة''': '''Tap to return to the menu''',
'''يوم الميلاد''': '''Birth day''',
'''شهر الميلاد''': '''Birth month''',
'''رجوع''': '''Back''',
'''مسح''': '''DEL''',
'''مسافة''': '''Space''',
'''التالي''': '''Next''',
'''ابدأ''': '''Start''',
'''حفظ''': '''Save''',
'''حرّك الجويستيك للمشي... وزر التفاعل لفتح الحاجات.''': '''Use the joystick to move... and the USE button to open things.''',
})


EN.update({
'لعب أونلاين (لحد 8 لاعبين)': 'Play Online (up to 8 players)',
'لو الخوف اتملى أو الوحش لمسك... بتخسر وتعيد الشقة!': 'If your fear fills up or a monster touches you... you lose and restart the apartment!',
'افتح غرفة جديدة': 'Create a New Room',
'ادخل غرفة برقم ID': 'Join a Room by ID',
'السيرفر: {a}': 'Server: {a}',
'مش متحدد - اضغط هنا': 'not set - press here',
'شغّل سيرفر على جهازي': 'Start a Server on This Device',
'اللعب الأونلاين': 'Online Play',
'غرف بنظام الـ ID - لحد {n} لاعبين مع بعض': 'ID-based rooms - up to {n} players together',
'اكتب رقم الغرفة (ID)': 'Type the Room ID',
'ادخل': 'Join',
'اكتب الأرقام بالكيبورد وبعدين Enter   |   Esc: رجوع': 'Type the digits, then Enter   |   Esc: back',
'عنوان السيرفر': 'Server Address',
'مثال: 192.168.1.5:8765   (لو مكتبتش بورت بيتاخد 8765)': 'Example: 192.168.1.5:8765   (port defaults to 8765)',
'بيتصل بالسيرفر': 'Connecting to the server',
'إلغاء': 'Cancel',
'رقم الغرفة': 'Room ID',
'ابعت الرقم ده لصحابك عشان يدخلوا الغرفة': 'Send this number to your friends so they can join',
'  (صاحب الغرفة)': '  (host)',
'  (إنت)': '  (you)',
'- فاضي -': '- empty -',
'اللاعبين: {n} / {m}': 'Players: {n} / {m}',
'ابدأ اللعب': 'Start Game',
'مستني صاحب الغرفة يبدأ اللعب...': 'Waiting for the host to start...',
'اخرج من الغرفة': 'Leave Room',
'خسرت!': 'You lost!',
'الخوف ملا العداد... قلبك مستحملش!': "Fear filled the meter... your heart couldn't take it!",
'الوحش مسكك!': 'The monster got you!',
'استنى صحابك... لسه {n} لاعب عايش': 'Wait for your friends... {n} still alive',
'لو حد منهم خرج بالمفتاح هتكمّل معاهم الشقة اللي بعدها.': 'If one of them escapes with the key, you continue with them in the next apartment.',
'ولو كلكم خسرتوا... الشقة بتبدأ من الأول.': 'And if you all lose... the apartment restarts.',
'كلكم خسرتوا... الشقة هتبدأ من الأول!': 'You all lost... the apartment restarts!',
'كلكم خسرتوا... الشقة بتبدأ من الأول!': 'You all lost... the apartment restarts!',
'الشقة {n} هتبدأ من الأول': 'Apartment {n} will restart',
'حاول تاني': 'Try Again',
'غرفة {r}  |  {n}/{m}': 'Room {r}  |  {n}/{m}',
' (خسر)': ' (lost)',
'الحفظ مش متاح أونلاين': "Saving isn't available online",
'اكتب عنوان السيرفر الأول (أو شغّل سيرفر على جهازك).': 'Enter the server address first (or start a server on your device).',
'الغرفة {r}  -  بالتوفيق!': 'Room {r}  -  good luck!',
'{n} دخل الغرفة': '{n} joined the room',
'{n} خرج من الغرفة': '{n} left the room',
'{n} لقى حاجة مهمة!': '{n} found something important!',
'{n} خسر! لازم تكملوا من غيره...': "{n} lost! You'll have to continue without them...",
'مفيش غرفة بالرقم ده.': 'No room with that number.',
'الغرفة مليانة (8 لاعبين).': 'The room is full (8 players).',
'السيرفر مشغول، جرّب كمان شوية.': 'The server is busy, try again shortly.',
'حصل خطأ.': 'Something went wrong.',
'مقدرتش أوصل للسيرفر: {a}': "Couldn't reach the server: {a}",
'اتقطع الاتصال بالسيرفر.': 'Lost connection to the server.',
'الرقم لازم يبقى 5 أرقام.': 'The ID must be 5 digits.',
'السيرفر اشتغل على جهازك.': 'The server is running on your device.',
'فيه سيرفر شغّال بالفعل على البورت ده - هنستخدمه.': 'A server is already running on this port - using it.',
'مقدرتش أشغّل السيرفر هنا.': "Couldn't start a server here.",
'{m} صحابك يكتبوا في خانة السيرفر: {a}': '{m} Friends enter this in the server box: {a}',
})


EN.update({
'تعالوا هنا!': 'Come here!',
'فيه وحش ورايا!': 'A monster is behind me!',
'ساعدوني!': 'Help me!',
'لقيت مفتاح': 'I found a key',
'استنوني': 'Wait for me',
'مين معاه بطارية؟': 'Anyone have a battery?',
'إغلاق': 'Close',
'شات': 'Chat',
'Enter: إرسال   |   Esc: إلغاء': 'Enter: send   |   Esc: cancel',
'T: شات': 'T: chat',
})


EN.update({
'خسرت - بتتفرج على: {n}': 'You lost - watching: {n}',
'هتتفرج على صحابك...': "You'll watch your friends...",
'◄ ► / A D: غيّر اللي بتتفرج عليه   |   T: شات': '◄ ► / A D: switch who you watch   |   T: chat',
})


EN.update({
"زمجرة... قريبة جداً!": "A growl... very close!",
"سلاسل بتتجرّ في الضلمة...": "Chains dragging in the dark...",
"حاجة تقيلة بتتسحب على الأرض...": "Something heavy is being dragged across the floor...",
"حد بيخربش الحيطة بضوافره...": "Someone is clawing at the wall...",
"جرس بيدق... ومفيش جرس في البيت!": "A bell is ringing... and there is no bell in this house!",
"ريح بتعوي... والشبابيك مقفولة!": "The wind howls... and the windows are shut!",
"نقطة... نقطة... مياه بتنزل من فوق.": "Drip... drip... water falling from above.",
"إزاز اتكسر في الأوضة اللي جنبك!": "Glass shattered in the next room!",
"راديو بيتكلم لوحده... بصوت مش مفهوم.": "A radio talks by itself... in a garbled voice.",
"ضحكة واطية... جاية من تحت السرير.": "A low giggle... from under the bed.",
"أنين طويل... مش بشري.": "A long moan... not human.",
"فحيح جنب ودنك!": "A hiss right next to your ear!",
"صوت عضم بيتكسّر...": "The sound of bones cracking...",
"سمعت زئير مرعب!!": "You heard a terrifying roar!!",
"صرخة... قريبة جداً!": "A scream... very close!",
"أصوات كتير بتهمس في ودنك...": "Many voices whisper in your ear...",
"حاجة بتزحف ورا ضهرك...": "Something is crawling behind you...",
})


EN.update({
'كارت قديم': 'Old business card',
'د. عادل الحكيم - طبيب أطفال': 'Dr. Adel El-Hakim - Pediatrician',
'الشقة 1 - عمارة الهمس - 1987': 'Apartment 1 - Whispering Building - 1987',
'جواب ماتبعتش': 'A letter never sent',
'حبيبتي سلمى، انتقلنا النهارده.': 'My dear Salma, we moved in today.',
'العمارة هادية أوي... هادية زيادة.': 'The building is so quiet... too quiet.',
'دفتر ليلى': "Layla's notebook",
'صاحبي الجديد ساكن في الحيطة.': 'My new friend lives in the wall.',
'بيقول اسمه "اللي تحت". بيحب الاستغماية.': 'He says his name is "The One Below". He loves hide and seek.',
'تحذير': 'A warning',
'عم رضوان قال: "متنزلوش البدروم بالليل".': 'Uncle Radwan said: "Never go down to the basement at night."',
'ومرضيش يقول ليه.': "He wouldn't say why.",
'ورقة صفرا': 'Yellowed paper',
'العمارة اتبنت فوق بير قديم.': 'The building was built over an old well.',
'كانوا بيرموا فيه كل اللي مش عايزينه... حتى ناس.': "They threw in everything they didn't want... even people.",
'دفتر عادل': "Adel's notebook",
'سلمى بتسمع همس بالليل.': 'Salma hears whispers at night.',
'قلتلها أعصاب. كنت غلطان.': 'I told her it was nerves. I was wrong.',
'رسمة بالشمع': 'Crayon drawing',
'ليلى رسمت بيتنا... وفي الأرض بير.': 'Layla drew our house... with a well in the ground.',
'وحوالين البير ناس كتير واقفين.': 'And many people standing around it.',
'رسالة عم رضوان': "Uncle Radwan's message",
'أنا حاولت أقفل البير بالأسمنت سنين.': 'I tried sealing the well with concrete for years.',
'كل مرة يرجع يتفتح من تحت.': 'Every time, it reopens from below.',
'سلمى اختفت امبارح. بابها مقفول من جوه.': 'Salma vanished yesterday. Her door is locked from inside.',
'والبوليس قال: "سافرت". هي مسافرتش.': 'The police said: "She left." She did not.',
'علبة موسيقى': 'Music box',
'مكتوب تحتها: "لسلمى... عشان تنامي".': 'Written underneath: "For Salma... so you can sleep."',
'واللحن بيشتغل لوحده من يومها.': 'The tune has played by itself ever since.',
'ورقة مبلولة': 'Damp paper',
'سمعتها بتنادي عليا من تحت.': 'I heard her calling me from below.',
'بس بتقول جملة واحدة: "ما تجيش".': 'But she only says one thing: "Don\'t come."',
'ماما بتلعب معانا استغماية دلوقتي.': 'Mama plays hide and seek with us now.',
'بس هي دايمًا اللي بتستخبى.': 'But she is always the one hiding.',
'تقرير طبي': 'Medical report',
'المريض: عادل الحكيم. بيسمع أصوات.': 'Patient: Adel El-Hakim. Hears voices.',
'النوم: صفر. التوصية: يسيب العمارة فورًا.': 'Sleep: none. Recommendation: leave the building at once.',
'ورقة بخط مرتعش': 'Shaky handwriting',
'ليلى مش بتنام في سريرها.': "Layla doesn't sleep in her bed.",
'بلاقيها واقفة قدام الحيطة... بتبتسم.': 'I find her standing before the wall... smiling.',
'نزلت البدروم. البير مفتوح.': 'I went down to the basement. The well is open.',
'وفيه سلم نازل لتحت... والتحت مضلّم.': 'There are stairs going down... and it is dark below.',
'نقش على الحيطة': 'Carving on the wall',
'"اللي بيفتح البير بيسكن العمارة للأبد".': '"Whoever opens the well lives in the building forever."',
'وتحتها أسماء كتير... آخرها: عادل.': 'Below it, many names... the last one: Adel.',
'ورقة من عادل': 'A page from Adel',
'مش قادر أخرج. كل باب بيطلّعني شقة تانية.': "I can't get out. Every door leads to another apartment.",
'كنت فاكر إني بدوّر على سلمى وليلى...': 'I thought I was searching for Salma and Layla...',
'اعتراف': 'Confession',
'الحقيقة: مفيش حد خطفهم.': 'The truth: nobody kidnapped them.',
'أنا اللي فتحت البير... وهما دخلوا وراي.': 'I opened the well... and they followed me in.',
'الصفحة الأخيرة': 'The last page',
'كل واحد يدخل العمارة فاكر إنه بيهرب.': 'Everyone who enters thinks they are escaping.',
'بس العمارة هي اللي بتختار مين يطلع.': 'But the building decides who gets out.',
'بخط ليلى': "In Layla's handwriting",
'لو وصلت هنا... هو مش عايز يخرّجك.': "If you made it here... he doesn't want to let you out.",
'عايزك تلعب معاه. افتح الباب واجري.': 'He wants you to play with him. Open the door and run.',
'الفصل 2: صاحب ليلى اللي في الحيطة': "Chapter 2: Layla's friend in the wall",
'الفصل 3: البير': 'Chapter 3: The Well',
'الفصل 4: الرسمة': 'Chapter 4: The Drawing',
'الفصل 5: اختفاء سلمى': 'Chapter 5: Salma Vanishes',
'الفصل 6: اللي بينادي من تحت': 'Chapter 6: The Voice From Below',
'الفصل 7: ليلى مبتنامش': "Chapter 7: Layla Doesn't Sleep",
'الفصل 8: السلم': 'Chapter 8: The Stairs',
'الفصل 9: الحقيقة': 'Chapter 9: The Truth',
'الفصل 10: اللي بيختار': 'Chapter 10: The One Who Chooses',
'وفي دفتر عادل القديم... اتكتب سطر جديد باسمك.': "In Adel's old notebook... a new line was written with your name.",
})


EN.update({
'بطيء... بس الكشاف مش بيأثر عليه!': "Slow... but the flashlight doesn't affect it!",
'لما يزأر... اجري! هيهجم!': "When it roars... run! It's about to charge!",
'بيسمع خطواتك... وقّف مكانك!': 'It hears your footsteps... stand still!',
'بتختفي وتظهر أقرب منك!': 'She vanishes and reappears closer!',
'بتقوى كل ما تخاف... اهدا!': 'She grows stronger as you fear... stay calm!',
'بتنط ناحيتك... والكشاف بيجمّدها!': 'She hops toward you... the flashlight freezes her!',
'كل ما تبصله بتخاف أكتر... وكل ما تبعد عينك بيقرّب!': 'The more you look, the more you fear... look away and he closes in!',
'بيتلوّى وبيقف يضحك... استغل وقفته واجري!': 'It weaves and stops to laugh... use the pause and run!',
'بطيء... بس رعبه بيوصل لبعيد!': 'Slow... but its dread reaches far!',
'سريع... بس بيحترق ويختفي بسرعة!': 'Fast... but it burns out quickly!',
})


EN.update({
'طفل بيعيّط... ومفيش أطفال في العمارة.': 'A child is crying... and there are no children in the building.',
'دبّان كتير... جاي منين؟': 'So many flies... where are they coming from?',
'حد بيجري ناحيتك في الضلمة!': 'Someone is running toward you in the dark!',
'تلات خبطات تقيلة على الباب...': 'Three heavy knocks on the door...',
'حد بيصفّر لحن قديم...': 'Someone is whistling an old tune...',
'تليفون بيرن... والخط مقطوع من سنين.': 'A phone is ringing... the line has been dead for years.',
'مقبض الباب بيتهز... من بره!': 'The doorknob is shaking... from outside!',
'ساعة بتدق... بس الساعات كلها واقفة.': 'A clock chimes... but every clock has stopped.',
'أرجوحة بتزيّ لوحدها...': 'A swing creaks by itself...',
'عواء بعيد... بيقرّب.': 'A distant howl... getting closer.',
'غراب بينعق... جوه الشقة!': 'A crow caws... inside the apartment!',
'ترتيل واطي... بلغة مش مفهومة.': 'A low chant... in an unknown language.',
'ضربة مرعبة!': 'A terrifying crash!',
'حشرجة... جنبك مباشرة.': 'A death rattle... right beside you.',
'همس معكوس... بيقول اسمك؟': 'Reversed whispers... saying your name?',
})


EN.update({
'اللي تحت صحي... اجري على الباب!': 'The One Below has awoken... run for the door!',
'بيزأر!... استعد!': 'It roars!... brace yourself!',
'مفيش وقت... بيجري ناحيتك!': "No time... it's running at you!",
'ورقة قديمة...': 'An old paper...',
'ورقة مطوية': 'Folded paper',
'ورقة بين الكتب': 'Paper between the books',
'مفتاح المكتب النحاسي مخبّي {h}.': 'The brass study key is hidden {h}.',
'المفتاح الصغير بتاع الدُرج... {h}.': 'The small drawer key... {h}.',
'في {f} في {r}': 'in the {f} in the {r}',
})


if __name__ == "__main__":
    main()

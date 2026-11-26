"""Обезличивание CIM XML. Выполнили: Бельтюков Н.М. КЭ-206, Букрин С.С. КЭ-206, Недочукова С.А. КЭ-206"""

import argparse
import base64
import hashlib
import io
import ipaddress
import json
import os
import re
import sqlite3
import string
import sys
import tempfile
import time
import unicodedata
import uuid
from collections import Counter
from contextlib import closing
from functools import lru_cache
from itertools import count
from pathlib import Path
from urllib.parse import urljoin
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape, quoteattr
from zipfile import BadZipFile, ZIP_DEFLATED, ZipFile, ZipInfo


# 1. Словари и правила. Для другого экспорта новые правила добавлять сюда.
RDF = "{http://www.w3.org/1999/02/22-rdf-syntax-ns#}"
XML = "{http://www.w3.org/XML/1998/namespace}"
XSI = "{http://www.w3.org/2001/XMLSchema-instance}"
SAFE_BASE = "https://example.invalid/model/"
SUBJECT_FIELDS = {RDF + "about", RDF + "ID", RDF + "nodeID"}
TYPE_FIELDS = {RDF + "datatype", XSI + "type", XSI + "nil", XML + "space"}
FRUITS_EN = "Apple Pear Cherry Plum Peach Apricot Orange Lemon Lime Mango Banana Melon Pumpkin Carrot Beet Cucumber Tomato Pepper Turnip Radish Cabbage Celery Onion Garlic".split()
FRUITS_RU = "Яблочная Грушевая Вишнёвая Сливовая Персиковая Абрикосовая Апельсиновая Лимонная Лаймовая Манговая Банановая Дынная Тыквенная Морковная Свекольная Огуречная Томатная Перечная Репная Редисовая Капустная Сельдерейная Луковая Чесночная".split()
PEOPLE_EN = "Aster Borin Cedar Darin Elmar Ferin Galen Ivor Lorin Miren Nerin Orin Ravin Sorin Tarin Velin".split()
PEOPLE_RU = "Астер Борин Седар Дарин Эльмар Ферин Гален Ивор Лорин Мирен Нерин Орин Равин Сорин Тарин Велин".split()
WORDS = {
    "en": {"fruits": FRUITS_EN, "people": PEOPLE_EN, "surname": "in", "middle": "on",
           "object": "Object", "substation": "Substation", "transformer": "TP",
           "line": "Line", "point": "RP", "organization": "Company", "street": "Street",
           "address": "Address", "voltage": "kV", "redacted": "[Redacted]"},
    "ru": {"fruits": FRUITS_RU, "people": PEOPLE_RU, "surname": "ов", "middle": "ович",
           "object": "Объект", "substation": "ПС", "transformer": "ТП", "line": "ЛЭП",
           "point": "РП", "organization": "Компания", "street": "Улица",
           "address": "Адрес", "voltage": "кВ", "redacted": "[Удалено]"},
}
CATALOGS = set("AggregationMethod BaseVoltage CableInfo CalendarDay CalendarMonth CalendarYear ClassDescriptor ClassNode DayType DocumentType MeasurementType MeasurementValueType NameType NominalFrequency OMSCustomerKind OperationalLimitSetType OperationalLimitType OverheadWireInfo PSRType Season TransitionDataType UnitLabel ValueAliasSet ValueToAlias ViolatedLimitType ViolationSeverity WireInfo GeographicalRegion SubGeographicalRegion".split())
SPECIAL_FIELDS = {
    "alias": "Name.name", "sections": "ACLineSegment.sections", "filter": "DjCategory.allowedObjectsFilter",
    "formula": "Expression.formula FormulaTemplate.formula", "name": "FolderNode.folderName",
    "ip": "IPConnectionPoint.address", "number": "PowerSystemResource.ccsCode",
    "media": "BlobStorage.image EventSound.sound MarkerType.additionalView MarkerType.diagramView",
    "diagram": "MonitelDiagram.image",
    "template": """DirectiveTemplate.text DjRecordTemplate.text MarkerTemplate.djRecordText
                   RTDBEventTypeConfiguration.textTemplate SetMarkerTemplate.markerText WorkOrderDJRecordTemplate.text""",
    "keep": """SensorWinding.accuracyClass Asset.type CurrentTransformer.accuracyClass CurrentTransformer.ctClass
              Season.endDate Season.startDate InUseDate.inUseDate BasicIntervalSchedule.points CalendarDay.date
              Curve.points DjAttributeSet.xsd DocumentType.fileExtension Equipment.nameplate HISPartitionBase.prefix
              IEC870RemoteUnitComponent.commonAddress PSRType.className PSRType.prefix RatioTapChangerTable.points
              RemotePoint.addrStr1 Shift.endTime Shift.startTime VCTimeSpan.endTime VCTimeSpan.startTime
              VCValidityPeriod.endDate VCValidityPeriod.startDate CurrentTransformer.ioptsat CurrentTransformer.it2p2
              CurrentTransformer.it2pl CurrentTransformer.pbranch Model.created Model.version
              Model.profile Model.scenarioTime Model.name""",
}
SPECIAL = {field: action for action, fields in SPECIAL_FIELDS.items() for field in fields.split()}
NAME_TYPES = {"Cable line series section": "redact", "LoadSheddingSV": "keep",
              "rcBlocking": "keep", "busNameMarkerRange": "keep", "number": "keep"}
FIELD_GROUPS = {
    "identifier": "fiasid fiasstreetid fiasaddressid mrid mridstr uuid guid",
    "first": "firstname givenname forename",
    "last": "lastname surname familyname",
    "middle": "patronymic middlename",
    "person": "fullname fio",
    "number": "inn kpp ogrn ogrnip tin taxid vatnumber passport passportseries snils",
    "redact": "log logs logtext",
    "keep": "xposition yposition zposition xvalue yvalue zvalue latitude longitude lat lon",
}
EXACT_FIELDS = {key: action for action, fields in FIELD_GROUPS.items() for key in fields.split()}
NUMBER_FIELDS = ("phone", "mobile", "fax", "telephone", "account", "contract", "personnel",
                 "inventory", "meterreading", "customerid")
PRIVATE_TEXT = ("password", "secret", "token", "signature", "attachment", "content",
                "comment", "description", "note", "url", "uri", "path")
NAME_FIELDS = set("name aliasname shortname longname dispatchname dispatchingname designation label".split())
ORDINAL_FIELDS = set("endnumber sectionnumber stagenumber terminalnumber phasenumber passportvalueformat".split())
TECHNICAL_FIELDS = set("ratedu nominalu district phasecode phases unitsymbol unitmultiplier".split())
NUMBER = re.compile(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?\Z", re.ASCII)
UUID = re.compile(r"[0-9a-fA-F]{8}(?:-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}")
VOLTAGE = re.compile(r"(?<![\w.])(\d+(?:[.,]\d+)?(?:\s*/\s*\d+(?:[.,]\d+)?)*)\s*(?:кВ|kV)\b", re.I)
TOKEN = re.compile(r'(?P<comment>//[^\n]*|/\*[\s\S]*?\*/)|(?P<string>"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\')|(?P<number>0[xX][0-9a-fA-F]+|(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)|(?P<word>(?:[^\W\d]|_)\w*)|(?P<other>[\s\S])')
KEYWORDS = set("if else return true false null NaN INF and or not".split())
TECHNICAL_TEXT = {"true", "false", "NaN", "INF", "-INF"}
PERSON_ACTIONS = {"first", "last", "middle", "person", "email", "street", "address"}
ALPHABETS = (string.digits, string.ascii_lowercase, string.ascii_uppercase,
             "абвгдеёжзийклмнопрстуфхцчшщъыьэюя", "АБВГДЕЁЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЫЬЭЮЯ")
ALPHABET_BY_CHARACTER = {character: alphabet for alphabet in ALPHABETS for character in alphabet}

# В пакете схемы эти поля предназначены для подписей и свободного текста.
DIAGRAM_PRIVATE = set("description elementname text tooltip username stringofnames genericsourcename genericinstancename geninstancename url".split())
DIAGRAM_LABELS = set("Cell Name IdentifiedItem NavigationLink Layer ElementSet UnitClass".split())
DIAGRAM_EXTERNAL = {"Script", "Formula"}
DIAGRAM_CATALOG_IDS = {"MeasurementType", "MeasurementValueType", "MeasurementValueSource"}
DIAGRAM_FORMATS = re.compile(r"(?:#[0-9A-Fa-f]{6,8}|[\d.,+\- ;:]+)\Z")
DIAGRAM_TECHNICAL = set("""
    Alignment Arrow ArrowAttachStyle Assembly AutoType Brush Category CellContent CellFormat CellMeasureParam
    ChangeDateTo ClassIconKey ClipRect Color ConnectionZone Control Cursor DashCap DashStyle Dashes Direction
    DirectionType EndLineCap EndStepMode FigureType FillRule FillStyle FontShape FontType FormatDate FormatMedium
    FormatStyle FormatTime FormatValue GenericDataSource GradientOrigin IntervalTimeKind ItemName LastBounds LevelType
    LineJoin LineType LogicOperator MarkerForm MasterSide Operator Origin PackageID PhaseCode PositionBehavior Precision
    PropertyName PropertyType QCodeParamName Rendering RequestStepKind RequestStepRelativeKind RuleName Sets SpreadMethod
    StartLineCap StartStepMode State Status StrokeStyle Suffix TableOrient TableSort TempStyleValue Template TextStyle
    ThumbnailKey TiTime TimeFormat TimeMode TimeStepKind TriggerKind Trimming Type TypeName UniMargin UnitClassID
    UnitMembers UpdateIntervalKind ValueAttribute ValueFormatString VerticalAlignment ViewPointPosition aDir context
    ctype fmt init_p kind lprop lsrc master_property mside mt pattern phases style_name w.ck
""".split())
DIAGRAM_NAME_KEYS = set("ElementProperty FillStyle File Item Measurement Operand Prop StrokeStyle TextStyle".split())
DIAGRAM_FILES = {"diogen/diagram.xml", "_rels/.rels", "[Content_Types].xml"}
IMAGE_RELATIONSHIPS = "diogen/_rels/diagram.xml.rels"
PNG_PATH = re.compile(r"diogen/media/Image\d*\.png\Z")
TRANSPARENT_PREVIEW = base64.b64decode("iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNgYAAAAAMAASsJTYQAAAAASUVORK5CYII=")

def local(tag):
    return tag.rsplit("}", 1)[-1]

def is_person(class_name):
    return bool(re.search(r"person|employee|individual|physicalcustomer|физлицо|сотрудник", class_name, re.I))

def name_action(class_name):
    if class_name in CATALOGS:
        return "keep"
    return "person" if is_person(class_name) else "name"

@lru_cache(maxsize=8192)
def field_rule(field, class_name):
    """Сначала точные исключения, затем общие правила по названию свойства."""
    field = local(field)
    key = field.rsplit(".", 1)[-1].lower().replace("_", "")
    if field in SPECIAL:
        return SPECIAL[field]
    if (key.endswith("sequencenumber") or key in ORDINAL_FIELDS
            or (class_name in {"CalendarYear", "CalendarMonth"} and key == "number")):
        return "keep"
    if key in EXACT_FIELDS:
        return EXACT_FIELDS[key]
    if "email" in key or "electronicmail" in key:
        return "email"
    if (key.endswith("number") or any(word in key for word in NUMBER_FIELDS)
            or (key == "value" and class_name in {"Reading", "MeterReading", "BillingReading"})):
        return "number"
    if any(word in key for word in PRIVATE_TEXT):
        return "redact"
    field = field.lower()
    if key in {"x", "y", "z"} and any(word in field + class_name.lower() for word in ("position", "location", "coordinate", "geopoint")):
        return "keep"
    if "street" in field:
        return "street" if key in {"name", "street", "streetname"} else "address"
    if any(word in field for word in ("address", "town", "postal", "postcode", "zipcode")):
        return "number" if key in {"postalcode", "postcode", "zipcode", "buildingnumber"} else "address"
    if key in NAME_FIELDS:
        return "symbol" if "Operand" in class_name else name_action(class_name)
    return "keep" if key in TECHNICAL_FIELDS else "unknown"


# 2. Постепенное чтение XML: в памяти находится одна сущность, а не весь файл.
class CheckedReader:
    def __init__(self, file):
        self.file = file
        self.hash = hashlib.sha256()
        self.bytes = 0
        self.last_object = 0
        self.previous = b""

    def read(self, size):
        data = self.file.read(size)
        self.hash.update(data)
        self.bytes += len(data)
        # Удаление нулей позволяет обнаружить DTD также в UTF-16/UTF-32.
        fragment = self.previous + data.replace(b"\0", b"")
        if b"<!DOCTYPE" in fragment or b"<!ENTITY" in fragment:
            raise ValueError("DTD и объявления сущностей в XML не поддерживаются")
        self.previous = fragment[-16:]
        if self.bytes - self.last_object > 64 * 1024 * 1024:
            raise ValueError("Одна XML-сущность превышает 64 МиБ; требуется отдельная обработка")
        return data

def read_xml(path, information, progress=None):
    """Возвращает заголовок и отдельные объекты вместе с их пространствами имён."""
    with open(path, "rb") as file:
        reader = CheckedReader(file)
        parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True, insert_pis=True))
        events = ET.iterparse(reader, events=("start", "end", "start-ns", "comment", "pi"), parser=parser)
        stack = [({"xml": XML[1:-1]}, Path(path).resolve().as_uri())]
        pending, contexts = {}, {}
        root, objects = None, 0
        for event, element in events:
            if event == "start-ns":
                prefix, uri = element
                pending[prefix] = uri
            elif event == "start":
                namespaces, base = stack[-1]
                namespaces = namespaces | pending if pending else namespaces
                pending.clear()
                base = urljoin(base, element.get(XML + "base", ""))
                stack.append((namespaces, base))
                if len(stack) > 101:
                    raise ValueError("Слишком большая вложенность XML")
                if root is None:
                    root = element
                    if root.tag != RDF + "RDF":
                        raise ValueError("Ожидается корень rdf:RDF")
                    header = ET.Element(root.tag, root.attrib)
                    yield "root", header, {header: (namespaces, base)}
                else:
                    contexts[element] = (namespaces, base)
            elif event in {"comment", "pi"} and len(stack) <= 2:
                yield "misc", element, {}
                if root is not None:
                    root.remove(element)
            elif event == "end":
                if len(stack) == 3:
                    yield "object", element, contexts
                    root.remove(element)
                    contexts = {}
                    reader.last_object = reader.bytes
                    objects += 1
                    if progress and objects % 25000 == 0:
                        progress(objects)
                stack.pop()
        information.update(sha256=reader.hash.hexdigest(), bytes=reader.bytes)

def canonical(value, context, kind="resource"):
    namespaces, base = context
    if kind == "nodeID":
        return "blank:" + value
    if kind == "ID":
        value = "#" + value
    prefix, colon, ending = value.partition(":")
    if colon and prefix in namespaces:
        return namespaces[prefix] + ending
    return urljoin(base, value)

def schema_reference(value, context, field):
    namespaces, _ = context
    return (field == RDF + "type" or (":" in value and value.split(":", 1)[0] in namespaces)
            or any(value.startswith(uri) for uri in namespaces.values() if uri.endswith(("#", "/schema/"))))

def subject(element, contexts):
    attributes = SUBJECT_FIELDS.intersection(element.attrib)
    if len(attributes) != 1:
        raise ValueError("У каждого объекта должен быть один RDF-идентификатор")
    key = attributes.pop()
    return canonical(element.get(key), contexts[element], local(key))

def object_class(element, contexts):
    if element.tag == RDF + "Description":
        for child in element.findall(RDF + "type"):
            if RDF + "resource" in child.attrib:
                return re.split(r"[#/]", canonical(child.get(RDF + "resource"), contexts[child]))[-1]
    return local(element.tag)


# 3. Генератор замен и временная база соответствий.
def file_fingerprint(path):
    with open(path, "rb") as file:
        return hashlib.file_digest(file, "sha256").digest()


class ReplacementGenerator:
    """Один и тот же отпечаток даёт одну и ту же последовательность замен."""

    def __init__(self, fingerprint):
        self.fingerprint = fingerprint
        self.blocks = (hashlib.sha256(fingerprint + index.to_bytes(8, "big")).digest() for index in count(1))

    def below(self, maximum):
        # Отбрасывает неполный остаток диапазона, чтобы все варианты были равновероятны.
        limit = 2**64 - 2**64 % maximum
        while True:
            number = int.from_bytes(next(self.blocks)[:8], "big")
            if number < limit:
                return number % maximum

    def choice(self, values):
        return values[self.below(len(values))]

    def new_uuid(self):
        return uuid.UUID(bytes=next(self.blocks)[:16], version=4)

def create_database(path):
    db = sqlite3.connect(path)
    db.executescript("""
        PRAGMA journal_mode=OFF;
        PRAGMA synchronous=OFF;
        PRAGMA cache_size=-16384;
        CREATE TABLE objects(old TEXT PRIMARY KEY, new TEXT UNIQUE, class TEXT, uuid TEXT);
        CREATE INDEX uuid_index ON objects(uuid);
        CREATE TABLE replacements(id INTEGER PRIMARY KEY, kind TEXT, old TEXT, new TEXT,
                                  UNIQUE(kind, old), UNIQUE(kind, new));
        CREATE TABLE people(owner TEXT PRIMARY KEY, first TEXT, last TEXT, middle TEXT, email TEXT);
        CREATE TABLE aliases(owner TEXT PRIMARY KEY, target TEXT, type TEXT, value TEXT);
        CREATE TABLE name_types(owner TEXT PRIMARY KEY, code TEXT);
        CREATE TABLE customer_kinds(owner TEXT PRIMARY KEY, kind TEXT);
        CREATE TABLE symbols(old TEXT PRIMARY KEY, new TEXT UNIQUE, used INTEGER, defined INTEGER);
    """)
    return db

def first_value(db, query, *parameters):
    row = db.execute(query, parameters).fetchone()
    return row[0] if row else None

@lru_cache(maxsize=32768)
def mapped_id(db, generator, original):
    new = first_value(db, "SELECT new FROM objects WHERE old=?", original)
    if new is None:
        new = "_" + str(generator.new_uuid())
        db.execute("INSERT INTO objects(old,new) VALUES(?,?)", (original, new))
    return new

@lru_cache(maxsize=32768)
def known_id(db, original):
    return first_value(db, "SELECT new FROM objects WHERE old=? AND class IS NOT NULL", original)

def replacement(db, kind, original):
    return first_value(db, "SELECT new FROM replacements WHERE kind=? AND old=?", kind, original)

def replacement_taken(db, kind, new):
    return first_value(db, "SELECT 1 FROM replacements WHERE kind=? AND new=?", kind, new)

def save_replacement(db, kind, original, new):
    db.execute("INSERT INTO replacements(kind,old,new) VALUES(?,?,?)", (kind, original, new))
    return new

def make_person(db, generator, owner, words):
    row = db.execute("SELECT first,last,middle,email FROM people WHERE owner=?", (owner,)).fetchone()
    if not row:
        index = generator.below(len(words["people"]))
        first = words["people"][index]
        number = db.execute("INSERT INTO people(owner) VALUES(?)", (owner,)).lastrowid
        last = first + words["surname"] + "-" + str(number)
        middle = first + words["middle"]
        email = PEOPLE_EN[index % len(PEOPLE_EN)].lower() + "." + str(number) + "@example.invalid"
        row = first, last, middle, email
        db.execute("UPDATE people SET first=?,last=?,middle=?,email=? WHERE owner=?", (*row, owner))
    return dict(zip(("first", "last", "middle", "email"), row))

def name_kind(class_name, value):
    class_name = class_name.lower()
    if re.match(r"\s*ТП\b", value, re.I):
        return "transformer"
    if re.match(r"\s*РП\b", value, re.I):
        return "point"
    if "substation" in class_name or re.match(r"\s*ПС\b", value, re.I):
        return "substation"
    if any(word in class_name for word in ("line", "feeder")) or re.match(r"\s*(ЛЭП|ВЛ|КЛ)\b", value, re.I):
        return "line"
    if any(word in class_name for word in ("organisation", "organization", "company", "legalcustomer", "corporate")):
        return "organization"
    return "object"

def make_name(db, generator, value, class_name, words):
    value = unicodedata.normalize("NFC", value.strip())
    kind = name_kind(class_name, value)
    group = "name:" + kind
    new = replacement(db, group, value)
    if new is None:
        number = db.execute("INSERT INTO replacements(kind,old) VALUES(?,?)", (group, value)).lastrowid
        fruit = generator.choice(words["fruits"])
        if words["language"] == "ru" and kind in {"object", "address"}:
            fruit = fruit[:-2] + ("ий" if fruit.endswith("яя") else "ый")
        voltage = VOLTAGE.search(value)
        voltage = voltage.group(1) + " " + words["voltage"] if voltage else ""
        new = " ".join(f"{fruit} {words[kind]} {voltage} {number:06d}".split())
        db.execute("UPDATE replacements SET new=? WHERE id=?", (new, number))
    return new

def make_number(db, generator, value, group, indexing):
    """Повторяемая замена цифр и букв с сохранением длины и разделителей."""
    group = "number:" + group
    new = replacement(db, group, value)
    if new is not None:
        return new
    numeric = bool(NUMBER.fullmatch(value.strip()))
    if not numeric and any(ch.isalpha() and ch not in ALPHABET_BY_CHARACTER for ch in value):
        raise ValueError("Буква в номере требует отдельного правила")
    choices = [ch if numeric and ch in "eE" else ALPHABET_BY_CHARACTER.get(ch, ch) for ch in value]
    if all(len(alphabet) == 1 for alphabet in choices):
        raise ValueError("В идентификаторе нет поддерживаемых букв или цифр")
    for _ in range(2000):
        new = "".join(generator.choice(alphabet) for alphabet in choices)
        if new != value and not replacement_taken(db, group, new):
            return save_replacement(db, group, value, new)
    # В коротком диапазоне (например, 0..9) последним свободным может быть исходное
    # значение. Пока идёт первый проход, можно обменять две замены без потери ссылок.
    if indexing and not replacement_taken(db, group, value):
        for old, previous in db.execute("SELECT old,new FROM replacements WHERE kind=? ORDER BY id", (group,)):
            if len(previous) == len(value) and all(ch in alphabet for ch, alphabet in zip(previous, choices)):
                db.execute("UPDATE replacements SET new=? WHERE kind=? AND old=?", (value, group, old))
                return save_replacement(db, group, value, previous)
    raise ValueError("Не удалось подобрать уникальный номер: слишком маленький диапазон")

def symbol(db, generator, name, flag, create=True):
    new = first_value(db, "SELECT new FROM symbols WHERE old=?", name)
    used, defined = flag == "used", flag == "defined"
    if new:
        db.execute("UPDATE symbols SET used=MAX(used,?),defined=MAX(defined,?) WHERE old=?", (used, defined, name))
    elif create:
        new = "s_" + generator.choice(FRUITS_EN).lower() + "_" + generator.new_uuid().hex
        db.execute("INSERT INTO symbols VALUES(?,?,?,?)", (name, new, used, defined))
    return new

def formula(db, generator, value, register=False):
    cleaned = TOKEN.sub(lambda match: "".join("\n" if ch == "\n" else " " for ch in match.group())
                        if match.lastgroup == "comment" else match.group(), value)
    variables = KEYWORDS | set(re.findall(r"(?<![\w.])((?:[^\W\d]|_)\w*)\s*=(?!=)", cleaned))
    result = []
    for token in TOKEN.finditer(cleaned):
        text = token.group()
        if token.lastgroup == "string":
            raise ValueError("Строковая константа в формуле требует отдельного правила")
        if (token.lastgroup == "word" and text not in variables
                and not cleaned[token.end():].lstrip().startswith("(")):
            text = symbol(db, generator, text, "used")
        result.append(text)
    return value if register else "".join(result)

def blob_xml(db, generator, value, action, context, words):
    data = base64.b64decode("".join(value.split()), validate=True)
    fragment = data.replace(b"\0", b"")
    if b"<!DOCTYPE" in fragment or b"<!ENTITY" in fragment:
        raise ValueError("DTD внутри вложенного XML запрещён")
    root = ET.fromstring(data)
    if action == "sections":
        allowed = set("SequenceNumber Length R1 R0 X1 X0 G1 G0 B1 B0 ThermoStabilty CableLayingMethod Nameplate IsCable Name LayingMethod S".split())
        if root.tag != "Sections" or any(e.tag not in {"Sections", "Section"} for e in root.iter()):
            raise ValueError("Неизвестная структура участков линии")
        for element in root.iter():
            if set(element.attrib) - allowed or (element.text and element.text.strip()):
                raise ValueError("Неизвестные данные внутри участков линии")
            if element.get("Name"):
                element.set("Name", make_name(db, generator, element.get("Name"), "ACLineSeriesSection", words))
    else:
        if root.tag != "ObjectsFilters":
            raise ValueError("Неизвестная структура фильтра объектов")
        def replace_uuid(match):
            raw = match.group()
            for candidate in ("#_" + raw, "#" + raw, "urn:uuid:" + raw):
                new = known_id(db, canonical(candidate, context))
                if new:
                    return new.lstrip("_")
            return raw  # Здесь также бывают идентификаторы классов и полей схемы.
        for element in root.iter():
            for key, text in list(element.attrib.items()):
                element.set(key, UUID.sub(replace_uuid, text))
            if element.text and element.text.strip():
                text = element.text.strip()
                if UUID.fullmatch(text):
                    element.text = UUID.sub(replace_uuid, element.text)
                elif not NUMBER.fullmatch(text) and text not in {"true", "false"}:
                    raise ValueError("Неизвестное текстовое условие во вложенном фильтре")
    return base64.b64encode(ET.tostring(root, encoding="utf-8", xml_declaration=True)).decode("ascii")


# Схемы хранятся как ZIP с векторным XML и картинкой предпросмотра.
def parse_part(data):
    text = data.replace(b"\0", b"")
    if b"<!DOCTYPE" in text or b"<!ENTITY" in text:
        raise ValueError("DTD внутри пакета схемы")
    return ET.fromstring(data)

@lru_cache(maxsize=32768)
def diagram_id(db, fingerprint, original, catalog=False):
    rows = db.execute("SELECT new FROM objects WHERE uuid=? LIMIT 2", (original,)).fetchall()
    if len(rows) == 1:
        return rows[0][0].lstrip("_")
    if catalog:
        return original
    # Для идентификаторов, которых нет в RDF, отдельная последовательность
    # не влияет на порядок выдачи замен в основном XML.
    digest = hashlib.sha256(b"diagram-id\0" + fingerprint + original.encode("ascii")).digest()
    return str(uuid.UUID(bytes=digest[:16], version=4))

def clean_diagram(root, db, fingerprint, redacted):
    if root.tag != "Diagram":
        raise ValueError("Неизвестный формат схемы")
    for element in root.iter():
        tag = local(element.tag)
        has_map = tag == "GeoSubstrateSettings" and (len(element) or element.attrib or (element.text or "").strip())
        if tag in DIAGRAM_EXTERNAL or has_map:
            raise ValueError("Схема содержит внешний слой, формулу или скрипт")
        for key, value in element.attrib.items():
            if not value.strip():
                continue
            label = key.lower() in DIAGRAM_PRIVATE and (tag, key) != ("ElementProperty", "ElementName")
            label |= key.lower() == "name" and tag in DIAGRAM_LABELS
            label |= key in {"CurrentExpression", "OpenFormParams"}
            if label:
                element.set(key, redacted)
            elif key == "DiogenID" and tag == "Diagram" and value.upper() == "{719C8CD5-965C-4BD9-9120-E95B0CD177A1}":
                continue  # Идентификатор самого формата, одинаковый в пакетах.
            elif UUID.search(value) and (key.lower().endswith(("uid", "guid")) or key in DIAGRAM_CATALOG_IDS | {"link", "psr"}):
                def replace_id(match):
                    raw = match.group()
                    new = diagram_id(db, fingerprint, raw.lower(), key in DIAGRAM_CATALOG_IDS)
                    return raw if new == raw.lower() else new.upper() if raw == raw.upper() else new
                element.set(key, UUID.sub(replace_id, value))
            elif NUMBER.fullmatch(value) or value.lower() in {"true", "false", "nan", "infinity", "-infinity"}:
                continue
            elif DIAGRAM_FORMATS.fullmatch(value) or key in DIAGRAM_TECHNICAL:
                continue
            elif (key == "Name" and tag in DIAGRAM_NAME_KEYS) or (tag, key) == ("ElementProperty", "ElementName"):
                continue
            elif (tag, key) == ("File", "name") and re.fullmatch(r"diogenshared[\w.]*", value, re.I):
                continue
            elif key in {"Value", "value", "Name", "name"}:
                element.set(key, redacted)
            else:
                raise ValueError(f"Неизвестное поле схемы: {tag}.{key}")
        if (element.text or "").strip():
            if UUID.fullmatch(element.text):
                element.text = diagram_id(db, fingerprint, element.text.lower(), tag in DIAGRAM_CATALOG_IDS)
            elif tag in {"Cell", "Name"}:
                element.text = redacted
            elif not NUMBER.fullmatch(element.text.strip()) and (tag, element.text) != ("Field", "value"):
                raise ValueError(f"Неизвестный текст схемы: {tag}")
        if (element.tail or "").strip():
            raise ValueError("Смешанный текст внутри схемы")
        if tag == "Thumbnail" and "ThumbnailKey" in element.attrib:
            element.set("ThumbnailOutdated", "true")

def clean_descriptor(data, name, image_path):
    root = parse_part(data)
    relations = "http://schemas.openxmlformats.org/diogenDiagram/2013/relationships/"
    if name == "[Content_Types].xml":
        types = {"xml": "text/xml", "png": "image/png", "scrap": "unit/scrap",
                 "rels": "application/vnd.openxmlformats-package.relationships+xml"}
        scheme = "{http://schemas.openxmlformats.org/package/2006/content-types}"
        accepted = root.tag == scheme + "Types" and all(node.tag == scheme + "Default"
            and set(node.attrib) == {"Extension", "ContentType"}
            and types.get(node.get("Extension")) == node.get("ContentType") for node in root)
    else:
        target = image_path if name == IMAGE_RELATIONSHIPS else "diogen/diagram.xml"
        kind = "image" if name == IMAGE_RELATIONSHIPS else "diogenDiagram"
        scheme = "{http://schemas.openxmlformats.org/package/2006/relationships}"
        accepted = root.tag == scheme + "Relationships" and len(root) == 1 and all(
            node.tag == scheme + "Relationship" and set(node.attrib) == {"Type", "Target", "Id"}
            and node.get("Type") == relations + kind and node.get("Target") == "/" + target
            and re.fullmatch(r"(?:R[0-9A-Fa-f]{16}|h[0-9a-f]{32})", node.get("Id", "")) for node in root
        )
    if (not accepted or root.attrib or (root.text or "").strip()
            or any(len(node) or (node.text or "").strip() or (node.tail or "").strip() for node in root)):
        raise ValueError("Неизвестное описание компонентов схемы")
    # Убираются комментарии из XML описания пакета, сохранение его пространство имён.
    return ET.tostring(root, encoding="utf-8", xml_declaration=True)

def diagram_package(db, generator, text, redacted):
    try:
        binary = base64.b64decode("".join(text.split()), validate=True)
        with ZipFile(io.BytesIO(binary)) as source:
            entries = source.infolist()
            files = {entry.filename for entry in entries}
            previews = [name for name in files if PNG_PATH.fullmatch(name)]
            expected = DIAGRAM_FILES | {IMAGE_RELATIONSHIPS, previews[0]} if len(previews) == 1 else DIAGRAM_FILES
            if (len(entries) != len(files) or files != expected
                    or sum(entry.file_size for entry in entries) > 32 * 1024 * 1024):
                return ""
            output = io.BytesIO()
            with ZipFile(output, "w") as archive:
                for entry in entries:
                    name = entry.filename
                    if name == "diogen/diagram.xml":
                        root = parse_part(source.read(entry))
                        clean_diagram(root, db, generator.fingerprint, redacted)
                        data = ET.tostring(root, encoding="utf-8", xml_declaration=True)
                    elif name in previews:
                        data = TRANSPARENT_PREVIEW
                    else:
                        data = clean_descriptor(source.read(entry), name, previews[0] if previews else "")
                    archive.writestr(ZipInfo(name), data, compress_type=ZIP_DEFLATED)
        return base64.b64encode(output.getvalue()).decode("ascii")
    except (BadZipFile, ET.ParseError, ValueError, RuntimeError, NotImplementedError):
        return ""

def reviewed_media(text, whitelist):
    try:
        data = base64.b64decode("".join(text.split()), validate=True)
    except ValueError:
        return ""
    return whitelist.get(hashlib.sha256(data).hexdigest(), "")


# 4. Обработка значений. Технические числа пропускаются только после правил.
def choose_action(db, field, class_name, owner, value):
    action = field_rule(field, class_name)
    text = value.strip()
    if action == "alias":
        row = db.execute("""SELECT a.target,o.class,t.code FROM aliases a
                            LEFT JOIN objects o ON o.old=a.target
                            LEFT JOIN name_types t ON t.owner=a.type WHERE a.owner=?""", (owner,)).fetchone()
        target, target_class, code = row or (None, None, None)
        class_name, owner = target_class or class_name, target or owner
        action = NAME_TYPES.get(code) or name_action(class_name)
        if code not in NAME_TYPES and action == "name" and text.isascii() and text.isdecimal():
            action = "number"
    if action == "unknown" and text:
        if not (NUMBER.fullmatch(text) or text in TECHNICAL_TEXT):
            raise ValueError("Нет правила для текстового поля " + local(field) + " класса " + class_name)
        action = "keep"
    return action, class_name, owner

def transform_value(db, generator, value, action, class_name, owner, context, words, field, indexing=False, datatype=""):
    text = value.strip()
    if not text or action == "keep":
        return value
    if action in {"name", "symbol"}:
        new = symbol(db, generator, text, "defined", create=action == "symbol")
        return new or make_name(db, generator, value, class_name, words)
    if action == "formula":
        return formula(db, generator, value, indexing)
    if action in {"sections", "filter"}:
        return blob_xml(db, generator, value, action, context, words)
    if action == "diagram":
        return diagram_package(db, generator, text, words["redacted"])
    if action == "media":
        return reviewed_media(text, words["reviewed_media"])
    if action in PERSON_ACTIONS:
        person = make_person(db, generator, owner, words)
        if action == "person":
            return f"{person['last']} {person['first']} {person['middle']}"
        if action in person:
            return person[action]
        if NUMBER.fullmatch(text):
            return make_number(db, generator, value, "address", indexing)
        street = words["street"] + " " + person["last"]
        return street if action == "street" else words["address"] + " " + street
    if action == "number":
        return make_number(db, generator, value, local(field), indexing)
    if action == "identifier":
        raw = text.removeprefix("urn:uuid:").lstrip("#_")
        owner_uuid = owner.rsplit("#", 1)[-1].removeprefix("urn:uuid:").lstrip("_").rsplit("/", 1)[-1]
        if UUID.fullmatch(raw) and raw.lower() == owner_uuid.lower():
            new = mapped_id(db, generator, owner)
        else:
            new = known_id(db, canonical(text, context))
            if not new and UUID.fullmatch(raw):
                rows = db.execute("SELECT new FROM objects WHERE uuid=?", (raw.lower(),)).fetchall()
                if len(rows) > 1:
                    raise ValueError("Неоднозначная ссылка на UUID в текстовом поле")
                new = rows[0][0] if rows else None
        if new:
            return new.lstrip("_") if UUID.fullmatch(text) else new
        group = "identifier"
        new = replacement(db, group, value)
        return new or save_replacement(db, group, value, str(generator.new_uuid()))
    if action == "ip":
        ipaddress.ip_address(text)
        new = replacement(db, "ip", text)
        if new:
            return new
        while True:
            new = str(ipaddress.IPv4Address(int(ipaddress.IPv4Address("198.18.0.0")) + generator.below(131070) + 1))
            if not replacement_taken(db, "ip", new):
                return save_replacement(db, "ip", text, new)
    if action == "template":
        placeholders = re.findall(r"\$\{[A-Za-z_][A-Za-z_0-9]*\}|\{[0-9]+(?::[A-Za-z0-9 .:/+_\-]+)?\}", value)
        return " ".join([words["redacted"], *placeholders])
    if action in {"empty", "redact"}:
        if action == "empty" or datatype.endswith(("base64Binary", "hexBinary")):
            return ""
        if datatype.endswith(("integer", "decimal", "double", "float")):
            return "0"
        if datatype.endswith("boolean"):
            return "false"
        return words["redacted"]
    raise ValueError("Неизвестное действие: " + action)

def index_object(db, generator, element, contexts, words):
    owner = subject(element, contexts)
    class_name = object_class(element, contexts)
    mapped_id(db, generator, owner)
    raw_uuid = owner.rsplit("#", 1)[-1].removeprefix("urn:uuid:").lstrip("_").rsplit("/", 1)[-1]
    db.execute("UPDATE objects SET class=?,uuid=? WHERE old=?", (class_name, raw_uuid.lower() if UUID.fullmatch(raw_uuid) else None, owner))
    if is_person(class_name):
        make_person(db, generator, owner, words)
    if class_name == "Name":
        children = {local(child.tag): child for child in element if isinstance(child.tag, str)}
        links = []
        for key in ("Name.IdentifiedObject", "Name.NameType"):
            child = children.get(key)
            links.append(None if child is None else canonical(child.get(RDF + "resource", ""), contexts[child]))
        name = children["Name.name"].text if "Name.name" in children else None
        db.execute("INSERT OR REPLACE INTO aliases VALUES(?,?,?,?)", (owner, *links, name or ""))
    for field in element.iter():
        if not isinstance(field.tag, str):
            continue
        if RDF + "parseType" in field.attrib:
            raise ValueError("rdf:parseType требует отдельного обработчика")
        if field is not element and (RDF + "about" in field.attrib or RDF + "ID" in field.attrib):
            raise ValueError("Вложенный RDF-объект требует отдельного обработчика")
        for key, value in field.attrib.items():
            if key == RDF + "resource" and not schema_reference(value, contexts[field], field.tag):
                target = canonical(value, contexts[field])
                mapped_id(db, generator, target)
                if local(field.tag) == "Customer.OMSKind":
                    db.execute("INSERT OR REPLACE INTO customer_kinds VALUES(?,?)", (owner, target))
            elif key == RDF + "nodeID" and field is not element:
                mapped_id(db, generator, canonical(value, contexts[field], "nodeID"))
        value = field.text or ""
        action = field_rule(field.tag, class_name)
        if local(field.tag) == "NameType.name" or (class_name == "OMSCustomerKind" and local(field.tag) == "IdentifiedObject.name"):
            db.execute("INSERT OR REPLACE INTO name_types VALUES(?,?)", (owner, value))
        if value.strip() and action in {"number", "formula"}:
            transform_value(db, generator, value, action, class_name, owner, contexts[field], words, field.tag, True)

def transform_object(db, generator, element, contexts, words, actions):
    owner = subject(element, contexts)
    class_name = object_class(element, contexts)
    if class_name == "Customer":
        class_name = first_value(db, "SELECT class FROM objects WHERE old=?", owner)
    fixed_attributes = {XML + "base": SAFE_BASE, XML + "lang": words["language"],
                        XSI + "schemaLocation": "", XSI + "noNamespaceSchemaLocation": ""}

    def visit(field, redacted=False):
        # Комментарии и инструкции очищаются при записи, чтобы правило было одно.
        if not isinstance(field.tag, str):
            return
        original = field.text or ""
        if redacted:
            action, semantic_class, seed = "redact", class_name, owner
        else:
            action, semantic_class, seed = choose_action(db, field.tag, class_name, owner, original)
        redacted = redacted or action in {"redact", "empty"}
        datatype = field.get(RDF + "datatype", field.get(XSI + "type", ""))
        context = contexts[field]
        for key, value in list(field.attrib.items()):
            if key in SUBJECT_FIELDS:
                kind = local(key)
                new = mapped_id(db, generator, canonical(value, context, kind))
                field.set(key, "#" + new if kind == "about" else new)
            elif key == RDF + "resource":
                new = known_id(db, canonical(value, context))
                field.set(key, "#" + new if new else value)
            elif key in fixed_attributes:
                field.set(key, fixed_attributes[key])
            elif key not in TYPE_FIELDS:
                attr_action, attr_class, attr_owner = choose_action(db, key, class_name, owner, value)
                field.set(key, transform_value(db, generator, value, "redact" if redacted else attr_action,
                                               attr_class, attr_owner, context, words, key))
        if original.strip():
            action = "redact" if redacted and action != "empty" else action
            field.text = transform_value(db, generator, original, action, semantic_class, seed, context,
                                         words, field.tag, datatype=datatype)
            if action in {"media", "diagram"}:
                action += "_retained" if field.text else "_cleared"
            actions[action] += 1
        for child in field:
            visit(child, redacted)
            if child.tail and child.tail.strip():
                if not redacted:
                    raise ValueError("Смешанный XML-текст требует отдельного правила")
                child.tail = words["redacted"]
    visit(element)


# 5. Запись и проверка. Пространства имён сохраняются, включая локальные объявления.
def qualified(tag, namespaces, attribute=False):
    if not tag.startswith("{"):
        return tag
    uri, name = tag[1:].split("}", 1)
    for prefix, namespace in namespaces.items():
        if namespace == uri and (prefix or not attribute):
            return prefix + ":" + name if prefix else name
    raise ValueError("Не найден префикс пространства имён " + uri)

def serialize(element, contexts, parent_namespaces, header=False):
    tail = escape(element.tail or "")
    if element.tag is ET.Comment:
        return "<!-- redacted -->" + tail
    if element.tag is ET.ProcessingInstruction:
        text = element.text or ""
        if not text.lower().startswith(("iec61970-552 ", "floatexporter ")):
            text = "redacted"
        return f"<?{text}?>" + tail
    namespaces, _ = contexts[element]
    tag = qualified(element.tag, namespaces)
    parts = ["<" + tag]
    for prefix, uri in namespaces.items():
        if parent_namespaces.get(prefix) != uri:
            declaration = "xmlns:" + prefix if prefix else "xmlns"
            parts.append(f" {declaration}={quoteattr(uri)}")
    parts.extend(f" {qualified(key, namespaces, True)}={quoteattr(value)}" for key, value in element.attrib.items())
    opening = "".join(parts) + ">"
    if header:
        return opening + "\n"
    children = "".join(serialize(child, contexts, namespaces) for child in element)
    return f"{opening}{escape(element.text or '')}{children}</{tag}>{tail}"

def digest_element(digest, element):
    if not isinstance(element.tag, str):
        return
    value = element.text or ""
    event = [element.tag, sorted(element.attrib.items()), value if value.strip() else ""]
    digest.update(json.dumps(event, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
    for child in element:
        digest_element(digest, child)
        if child.tail and child.tail.strip():
            digest.update(json.dumps(["tail", child.tail], ensure_ascii=False).encode("utf-8"))
    digest.update(b"/end")

def read_dictionary(path):
    words = json.loads(Path(path).read_text(encoding="utf-8-sig"))
    if not isinstance(words, dict) or WORDS["en"].keys() - words.keys():
        raise ValueError("В словаре должны быть все поля встроенного английского словаря")
    for key in WORDS["en"]:
        is_list = key in {"fruits", "people"}
        values = words[key] if is_list else [words[key]]
        if not isinstance(values, list) or not values or not all(isinstance(v, str) and v.strip() for v in values):
            message = "Некорректный список в словаре: " if is_list else "Некорректное слово в словаре: "
            raise ValueError(message + key)
    return words

def discover_dictionaries():
    folder = Path.cwd() / "dictionary"
    try:
        folder.mkdir(exist_ok=True)
        entries = sorted(folder.iterdir(), key=lambda path: (path.name.lower(), path.name))
    except OSError:
        return {}

    dictionaries = {}
    for path in entries:
        code = path.stem.lower()
        if (path.suffix.lower() != ".json" or code in WORDS or code in dictionaries
                or not re.fullmatch(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*", code)):
            continue
        try:
            if not path.is_file():
                continue
            words = read_dictionary(path)
        except (OSError, ValueError, RecursionError):
            continue
        name = words.get("language_name")
        name = name.strip() if isinstance(name, str) else ""
        dictionaries[code] = (path, f"{name} ({path.name})")
    return dictionaries


def load_words(language, dictionary=None):
    if not dictionary and language not in WORDS:
        raise ValueError("Добавьте словарь в папку dictionary или укажите его через --dictionary")
    words = read_dictionary(dictionary) if dictionary else WORDS[language]
    reviewed = Path(__file__).with_name("reviewed-media.json")
    whitelist = json.loads(reviewed.read_text(encoding="utf-8")) if reviewed.is_file() else {}
    if not isinstance(whitelist, dict):
        raise ValueError("Список проверенных вложений должен быть JSON-словарём")
    return {**words, "language": language, "reviewed_media": whitelist}


def model_paths(source, output):
    source, output = Path(source).resolve(), Path(output).resolve()
    if source == output or (source.is_file() and output.is_file() and os.path.samefile(source, output)):
        raise ValueError("Исходный и выходной файлы должны различаться")
    if output.is_dir():
        raise ValueError("Путь выходного XML указывает на папку")
    return source, output


def process(source, output, language="en", dictionary=None, *, write_report=False):
    source, output = model_paths(source, output)
    report_path = output.with_suffix(".report.json") if write_report else None
    if report_path == source:
        raise ValueError("Файл отчёта и исходный XML должны различаться")
    if report_path is not None and report_path.is_dir():
        raise ValueError("Путь отчёта указывает на папку")
    words = load_words(language, dictionary)
    output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    classes, actions = Counter(), Counter()
    information, second_information = {}, {}
    report = {"version": "2.3-simple", "language": language, "persistent_key": False,
              "repeatable_between_runs": True, "stages_seconds": {}}
    print("Подготовка: вычисление отпечатка исходного файла", flush=True)
    fingerprint = file_fingerprint(source)
    generator = ReplacementGenerator(fingerprint)
    report["stages_seconds"]["fingerprint"] = round(time.monotonic() - started, 3)
    with (tempfile.TemporaryDirectory(prefix="cim-work-", dir=output.parent) as work,
          closing(create_database(Path(work) / "index.sqlite")) as db):
        temporary = Path(work) / "result.xml"
        def progress(label, count):
            db.commit()
            print(f"  {label}: {count:,}", flush=True)

        try:
            stage = time.monotonic()
            print("1/3: Чтение модели и сбор соответствий", flush=True)
            records = read_xml(source, information, lambda count: progress("Прочитано объектов", count))
            with closing(records):
                for kind, element, contexts in records:
                    if kind == "object":
                        index_object(db, generator, element, contexts, words)
                        classes[local(element.tag)] += 1
            if information["sha256"] != fingerprint.hex():
                raise ValueError("Исходный файл изменился во время обработки")
            missing = first_value(db, "SELECT COUNT(*) FROM objects WHERE class IS NULL")
            if missing:
                raise ValueError(f"В исходной модели {missing} ссылок на отсутствующие объекты")
            # Вид абонента хранится отдельно от его класса Customer. Сам граф не меняется.
            customers = db.execute("SELECT c.owner,t.code FROM customer_kinds c JOIN name_types t ON t.owner=c.kind ORDER BY c.rowid").fetchall()
            physical = [owner for owner, code in customers
                        if re.sub(r"\W+", "", code.casefold()) in {"naturalperson", "физическоелицо", "физлицо"}]
            for owner in physical:
                db.execute("UPDATE objects SET class='PersonCustomer' WHERE old=?", (owner,))
                make_person(db, generator, owner, words)
            report["physical_customers"] = len(physical)
            for owner, value in db.execute("SELECT owner,value FROM aliases ORDER BY rowid").fetchall():
                action, _, _ = choose_action(db, "Name.name", "Name", owner, value)
                if action == "number" and value.strip():
                    make_number(db, generator, value, "Name.name", True)
            db.commit()
            report["stages_seconds"]["index"] = round(time.monotonic() - stage, 3)
            expected = hashlib.sha256()
            stage = time.monotonic()
            print("2/3: Запись обезличенной модели", flush=True)
            records = read_xml(source, second_information, lambda count: progress("Записано объектов", count))
            with closing(records), open(temporary, "w", encoding="utf-8", newline="\n") as file:
                file.write('<?xml version="1.0" encoding="utf-8"?>\n')
                root_namespaces, root_tag = {}, ""
                for kind, element, contexts in records:
                    if kind == "root":
                        root_namespaces, _ = contexts[element]
                        root_attributes = {XML + "base": SAFE_BASE, XML + "lang": language}
                        for key in element.attrib:
                            if key not in root_attributes:
                                raise ValueError("Неизвестный атрибут корня XML: " + key)
                            element.set(key, root_attributes[key])
                        root_tag = qualified(element.tag, root_namespaces)
                        file.write(serialize(element, contexts, {"xml": XML[1:-1]}, header=True))
                        digest_element(expected, element)
                    elif kind == "misc":
                        file.write(serialize(element, contexts, root_namespaces) + "\n")
                    else:
                        transform_object(db, generator, element, contexts, words, actions)
                        digest_element(expected, element)
                        file.write(serialize(element, contexts, root_namespaces))
                file.write("\n</" + root_tag + ">\n")
            if information != second_information:
                raise ValueError("Исходный файл изменился во время обработки")
            report["stages_seconds"]["transform"] = round(time.monotonic() - stage, 3)
            print("3/3: Проверка записанного XML", flush=True)
            stage = time.monotonic()
            actual, output_information = hashlib.sha256(), {}
            for kind, element, contexts in read_xml(temporary, output_information):
                if kind in {"root", "object"}:
                    digest_element(actual, element)
            if expected.digest() != actual.digest():
                raise ValueError("Проверка XML не пройдена: записанные данные отличаются от ожидаемых")
            report["stages_seconds"]["verification"] = round(time.monotonic() - stage, 3)
            report.update({"objects": sum(classes.values()), "classes": dict(classes),
                           "actions": dict(actions), "source": {"bytes": information["bytes"]}, "output": output_information,
                           "verified": True, "seconds": round(time.monotonic() - started, 3),
                           "formula_variables_without_definition": first_value(db, "SELECT COUNT(*) FROM symbols WHERE used=1 AND defined=0")})
            if report_path is not None:
                temporary_report = Path(work) / "report.json"
                temporary_report.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
            os.replace(temporary, output)
            if report_path is not None:
                os.replace(temporary_report, report_path)
        finally:
            mapped_id.cache_clear()
            known_id.cache_clear()
            diagram_id.cache_clear()
    print(f"Готово: {output}", flush=True)
    if report_path is not None:
        print(f"Отчёт: {report_path}", flush=True)
    return report


def menu_path(label, current):
    entered = input(f"{label} [{current}]\n> ").strip()
    if len(entered) >= 2 and entered[0] == entered[-1] and entered[0] in "\"'":
        entered = entered[1:-1]
    return entered or current


def console_menu():
    settings = argparse.Namespace(input="input.xml", output="output.xml", language="en", dictionary=None, report=False)
    dictionaries = discover_dictionaries()
    languages = {"en": "Английский", "ru": "Русский"}
    languages.update({code: label for code, (_, label) in dictionaries.items()})
    choices = {str(index): code for index, code in enumerate(languages, 1)}
    while True:
        report_state = "Включён" if settings.report else "Выключен"
        print(f"""
        Обезличивание модели CIM XML
------------------------------------------
1. Исходный файл    {settings.input}
2. Выходной файл    {settings.output}
3. Язык результата  {languages[settings.language]}
4. Отчёт JSON       {report_state}

5. Начать обработку
0. Выйти
""")
        choice = input("Выбери пункт: ").strip()
        try:
            if choice == "1":
                path = menu_path("Исходный файл", settings.input)
                if not Path(path).is_file():
                    raise ValueError(f"Исходный файл не найден: {path}")
                settings.input = path
            elif choice == "2":
                path = menu_path("Выходной файл", settings.output)
                model_paths(settings.input, path)
                settings.output = path
            elif choice == "3":
                for number, code in choices.items():
                    print(f"{number}. {languages[code]}")
                selected = input("Выбери язык или нажми Enter: ").strip()
                if selected:
                    if selected not in choices:
                        raise ValueError("Выбери номер языка из списка")
                    settings.language = choices[selected]
                    entry = dictionaries.get(settings.language)
                    settings.dictionary = entry[0] if entry else None
            elif choice == "4":
                settings.report = not settings.report
            elif choice == "5":
                if not Path(settings.input).is_file():
                    raise ValueError("Исходный файл не найден. Укажи его в пункте 1")
                model_paths(settings.input, settings.output)
                return settings
            elif choice == "0":
                return None
            else:
                print("Введи номер пункта меню")
        except (OSError, ValueError) as error:
            print(f"Ошибка: {error}")


def main():
    parser = argparse.ArgumentParser(description="Обезличивание CIM XML без постоянного ключа",
                                     epilog="Запуск без аргументов открывает консольное меню.")
    parser.add_argument("input", help="Исходный XML")
    parser.add_argument("output", help="Результат XML")
    parser.add_argument("--language", default="en", help="Язык результата: en, ru или код своего словаря")
    parser.add_argument("--dictionary", help="JSON-словарь для другого языка")
    parser.add_argument("--report", action="store_true", help="Записать JSON-отчёт рядом с выходным XML")
    try:
        if len(sys.argv) == 1:
            try:
                args = console_menu()
            except EOFError:
                return
            if args is None:
                return
        else:
            args = parser.parse_args()
            dictionaries = discover_dictionaries()
            entry = dictionaries.get(args.language.lower())
            if args.dictionary is None and entry:
                args.dictionary, _ = entry
        process(args.input, args.output, args.language, args.dictionary, write_report=args.report)
    except (ValueError, OSError, ET.ParseError, sqlite3.Error, RecursionError) as error:
        parser.exit(1, "Ошибка: " + str(error) + "\n")
    except KeyboardInterrupt:
        parser.exit(130, "Обработка остановлена. Временные файлы удалены.\n")


if __name__ == "__main__":
    main()

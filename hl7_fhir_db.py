# hl7_fhir_db.py
# Read HL7 VXU^V04 -> build FHIR R4 Bundle (pure Python: hl7apy + fhir.resources),
# then print an "essentials" key/value map IN MEMORY (no bundle.json needed).
#
# Requires:
#   pip install hl7apy fhir.resources==7.* pydantic==2.*   (pydantic v1 also OK)

import json, uuid, re, argparse, sys
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Dict, Any, Tuple

from hl7apy.parser import parse_message
from fhir.resources.bundle import Bundle, BundleEntry, BundleEntryRequest
from fhir.resources.patient import Patient
from fhir.resources.humanname import HumanName
from fhir.resources.identifier import Identifier
from fhir.resources.immunization import Immunization
from fhir.resources.codeableconcept import CodeableConcept
from fhir.resources.coding import Coding
from fhir.resources.reference import Reference
from fhir.resources.quantity import Quantity

# ----------------------------
# Utilities
# ----------------------------

def urn(prefix: str) -> str:
    return f"urn:uuid:{prefix}-{uuid.uuid4()}"

def normalize_hl7_cr(text: str) -> str:
    """HL7 v2 requires segments to end with a single CR '\r'."""
    t = re.sub(r"\r?\n", "\r", text.strip())
    if not t.endswith("\r"):
        t += "\r"
    return t

def _extract_dt_digits(s: Optional[str]) -> Optional[str]:
    """Keep only the first 8–14 digits from an HL7 TS/DT field (e.g., '20230923^XYZ' -> '20230923')."""
    if not s:
        return None
    s = s.strip()
    if not s:
        return None
    m = re.match(r"(\d{8,14})", s)
    return m.group(1) if m else None

def ymd_to_date(v: Optional[str]) -> Optional[str]:
    d = _extract_dt_digits(v)
    if not d:
        return None
    return datetime.strptime(d[:8], "%Y%m%d").date().isoformat()

def ymd_to_dt(v: Optional[str]) -> Optional[str]:
    d = _extract_dt_digits(v)
    if not d:
        return None
    if len(d) >= 14:
        return datetime.strptime(d[:14], "%Y%m%d%H%M%S").isoformat()
    else:
        return datetime.strptime(d[:8], "%Y%m%d").isoformat()

# pydantic v1/v2 compatibility
def allowed_fields(model_cls) -> set:
    if hasattr(model_cls, "__fields__"):      # pydantic v1
        return set(model_cls.__fields__.keys())
    if hasattr(model_cls, "model_fields"):    # pydantic v2
        return set(model_cls.model_fields.keys())
    return set()

# ---- Type-agnostic component helpers (CWE/CE/CX/XPN/etc.) ----

_COMP_PREFIXES = ("cwe", "ce", "cx", "xpn", "ei", "hd", "ts", "st", "id", "is", "nm", "si", "tx", "ft")

def comp_text(comp, idx: int) -> Optional[str]:
    """
    Get the text of component idx (1-based) regardless of composite type.
    Avoid hasattr() (hl7apy may raise ChildNotValid during lookup).
    """
    for p in _COMP_PREFIXES:
        attr = f"{p}_{idx}"
        try:
            child = getattr(comp, attr)
        except Exception:
            continue
        if child:
            try:
                return child.to_er7()
            except Exception:
                continue
    try:
        return comp.to_er7()
    except Exception:
        return None

def coding_from_composite(comp) -> Coding:
    code = comp_text(comp, 1)
    display = comp_text(comp, 2)
    system = comp_text(comp, 3)
    if system and not str(system).startswith("http"):
        system = f"urn:id:{system}"
    return Coding(code=code, display=display, system=system)

# ----------------------------
# Patient mapping (PID)
# ----------------------------

def map_patient(pid) -> Patient:
    identifiers: List[Identifier] = []
    pid3 = pid.pid_3 if isinstance(pid.pid_3, list) else [pid.pid_3]
    for rep in pid3:
        if not rep:
            continue
        val = comp_text(rep, 1)  # CX.1 – ID
        aa = None
        try:
            if getattr(rep, "cx_4", None):
                aa = comp_text(rep.cx_4, 1)  # HD.1 namespace
        except Exception:
            aa = None
        if val:
            identifiers.append(Identifier(system=f"urn:id:{aa}" if aa else None, value=val))

    name = None
    if pid.pid_5:
        n = pid.pid_5[0] if isinstance(pid.pid_5, list) else pid.pid_5
        family = comp_text(n, 1)  # XPN.1 family
        given  = comp_text(n, 2)  # XPN.2 given
        if family or given:
            name = [HumanName(family=family, given=[g for g in [given] if g])]

    birth = ymd_to_date(pid.pid_7.ts_1.to_er7()) if getattr(pid, "pid_7", None) and getattr(pid.pid_7, "ts_1", None) else None

    gmap = {"F": "female", "M": "male", "O": "other", "U": "unknown"}
    gender = gmap.get(pid.pid_8.to_er7(), None) if getattr(pid, "pid_8", None) else None

    return Patient(
        id=str(uuid.uuid4()),
        identifier=identifiers or None,
        name=name,
        birthDate=birth,
        gender=gender,
    )

# ----------------------------
# Immunization mapping (RXA/RXR + OBX)
# ----------------------------

def map_immunization(rxa, rxr, patient_ref: Reference, obx_list) -> Immunization:
    imm_fields = allowed_fields(Immunization)

    # RXA-3 occurrence
    occurrence = ymd_to_dt(rxa.rxa_3.ts_1.to_er7()) if getattr(rxa, "rxa_3", None) and getattr(rxa.rxa_3, "ts_1", None) else None

    # RXA-5 CVX (CE/CWE)
    vaccine_code = None
    if getattr(rxa, "rxa_5", None):
        vaccine_code = CodeableConcept(coding=[coding_from_composite(rxa.rxa_5)])

    # RXA-6/7 dose quantity (7 is CWE units)
    dose_qty = None
    if getattr(rxa, "rxa_6", None):
        try:
            val = float(rxa.rxa_6.to_er7())
        except Exception:
            val = None
        unit = None
        if getattr(rxa, "rxa_7", None):
            unit = comp_text(rxa.rxa_7, 1)
        if val is not None:
            if unit == "ML":
                unit = "mL"  # UCUM-friendly tweak
            dose_qty = Quantity(value=val, unit=unit)

    # RXA-15 lot (prefer text if present)
    if getattr(rxa, "rxa_15", None):
        lot_id  = comp_text(rxa.rxa_15, 1)
        lot_txt = comp_text(rxa.rxa_15, 2)
        lot = lot_txt or lot_id
    else:
        lot = None

    # RXA-16 expiration
    exp = ymd_to_date(rxa.rxa_16.to_er7()) if getattr(rxa, "rxa_16", None) else None

    # RXA-20 completion status
    status = "completed"
    if getattr(rxa, "rxa_20", None):
        status = "completed" if rxa.rxa_20.to_er7().upper() in ("CP", "PA", "CM", "OK") else "not-done"

    # RXR route/site (CWE)
    route = site = None
    if rxr:
        if getattr(rxr, "rxr_1", None):
            route = CodeableConcept(coding=[coding_from_composite(rxr.rxr_1)])
        if getattr(rxr, "rxr_2", None):
            site = CodeableConcept(coding=[coding_from_composite(rxr.rxr_2)])

    # OBX extras: VIS presentation date & funding eligibility
    education: List[dict] = []
    program_eligibility: List[CodeableConcept] = []

    for obx in obx_list:
        code = comp_text(obx.obx_3, 1) if getattr(obx, "obx_3", None) else None
        val  = obx.obx_5.to_er7() if getattr(obx, "obx_5", None) else None

        if code == "29769-7":  # VIS Presentation Date (LOINC)
            dt = ymd_to_dt(val)
            if dt:
                education.append({"presentationDate": dt})

        elif code == "64994-7":  # Vaccine funding program eligibility (LOINC)
            try:
                coding = coding_from_composite(obx.obx_5)
            except Exception:
                coding = Coding(code=val)
            program_eligibility.append(CodeableConcept(coding=[coding]))

    # Build dict then filter to allowed fields (handles version differences)
    imm_data: Dict[str, Any] = {
        "id": str(uuid.uuid4()),
        "status": status,
        "vaccineCode": vaccine_code,
        "patient": patient_ref,
        "occurrenceDateTime": occurrence,
        "lotNumber": lot,
        "expirationDate": exp,
        "doseQuantity": dose_qty,
        "route": route,
        "site": site,
        "programEligibility": program_eligibility or None,
        # 'manufacturer' intentionally omitted (some versions require a Reference)
    }

    if education:
        if "education" in imm_fields:
            imm_data["education"] = education
        elif "note" in imm_fields:
            notes = [{"text": f"VIS presented: {e.get('presentationDate')}"} for e in education if e.get("presentationDate")]
            if notes:
                imm_data["note"] = notes

    imm_data = {k: v for k, v in imm_data.items() if v is not None and k in imm_fields}
    return Immunization(**imm_data)

# ----------------------------
# Build Bundle (in memory)
# ----------------------------

def vxu_to_bundle(vxu_text: str) -> Bundle:
    vxu_text_norm = normalize_hl7_cr(vxu_text)
    msg = parse_message(vxu_text_norm, find_groups=False, validation_level=None)

    pid = msg.PID
    patient = map_patient(pid)
    pat_url = urn("patient")
    pat_ref = Reference(reference=pat_url)

    rxa = msg.RXA[0] if isinstance(msg.RXA, list) else msg.RXA
    rxr = (msg.RXR[0] if hasattr(msg, "RXR") and isinstance(msg.RXR, list)
           else (msg.RXR if hasattr(msg, "RXR") else None))
    if hasattr(msg, "OBX"):
        obx_list = msg.OBX if isinstance(msg.OBX, list) else [msg.OBX]
    else:
        obx_list = []

    imm = map_immunization(rxa, rxr, pat_ref, obx_list)

    entries = [
        BundleEntry(
            fullUrl=pat_url,
            resource=patient,
            request=BundleEntryRequest(method="POST", url="Patient"),
        ),
        BundleEntry(
            fullUrl=urn("immunization"),
            resource=imm,
            request=BundleEntryRequest(method="POST", url="Immunization"),
        ),
    ]
    return Bundle(type="transaction", entry=entries)

# ----------------------------
# Essentials map (from Bundle in memory)
# ----------------------------

def _pick_coding(codeable: Dict[str, Any]) -> Tuple[Optional[str], Optional[str]]:
    if not codeable:
        return (None, None)
    codings = (codeable.get("coding") or [])
    for c in codings:
        sys_ = (c.get("system") or "").lower()
        if "cvx" in sys_:
            return (c.get("code"), c.get("display"))
    if codings:
        c = codings[0]
        return (c.get("code"), c.get("display"))
    return (None, None)

def bundle_to_essentials(bundle_obj: Any) -> Dict[str, Any]:
    """
    Accepts Bundle model / JSON string / dict and returns a concise key → value dict.
    """
    if isinstance(bundle_obj, Bundle):
        try:
            data = bundle_obj.model_dump(by_alias=True, exclude_none=True)  # pydantic v2
        except Exception:
            data = json.loads(bundle_obj.json(by_alias=True, exclude_none=True))  # v1
    elif isinstance(bundle_obj, str):
        data = json.loads(bundle_obj)
    elif isinstance(bundle_obj, dict):
        data = bundle_obj
    else:
        raise TypeError("bundle_to_essentials: unsupported type")

    entries = data.get("entry", [])
    patient = next((e.get("resource", {}) for e in entries if e.get("resource", {}).get("resourceType") == "Patient"), {})
    imm     = next((e.get("resource", {}) for e in entries if e.get("resource", {}).get("resourceType") == "Immunization"), {})

    # MRN pick
    mrn_val = mrn_sys = None
    for ident in (patient.get("identifier") or []):
        if ident.get("value"):
            mrn_val = ident.get("value"); mrn_sys = ident.get("system"); break

    def first(lst, default=None):
        return lst[0] if lst else default

    cvx_code, cvx_disp = _pick_coding(imm.get("vaccineCode") or {})
    route_code, route_disp = _pick_coding(imm.get("route") or {})
    site_code, site_disp   = _pick_coding(imm.get("site") or {})

    essentials = {
        "patient.id": patient.get("id"),
        "patient.mrn.system": mrn_sys,
        "patient.mrn.value": mrn_val,
        "patient.name.family": (first(patient.get("name") or []) or {}).get("family"),
        "patient.name.given": first(((first(patient.get("name") or []) or {}).get("given") or [])),
        "patient.birthDate": patient.get("birthDate"),
        "patient.gender": patient.get("gender"),
        "immunization.id": imm.get("id"),
        "immunization.status": imm.get("status"),
        "immunization.vaccine.cvx": cvx_code,
        "immunization.vaccine.display": cvx_disp,
        "immunization.occurrenceDateTime": imm.get("occurrenceDateTime"),
        "immunization.lotNumber": imm.get("lotNumber"),
        "immunization.expirationDate": imm.get("expirationDate"),
        "immunization.dose.value": (imm.get("doseQuantity") or {}).get("value"),
        "immunization.dose.unit": (imm.get("doseQuantity") or {}).get("unit"),
        "immunization.route.code": route_code,
        "immunization.route.display": route_disp,
        "immunization.site.code": site_code,
        "immunization.site.display": site_disp,
    }
    return essentials

def print_essentials_map(ess: Dict[str, Any]) -> None:
    for k in sorted(ess.keys()):
        print(f"{k}: {ess[k]}")

# ----------------------------
# CLI
# ----------------------------

def main():
    ap = argparse.ArgumentParser(description="HL7 VXU -> FHIR Bundle (in memory) + essentials map")
    ap.add_argument("--hl7", help="Path to HL7 VXU file", required=True)
    ap.add_argument("-o", "--out", help="Optional: write full FHIR Bundle JSON here")
    ap.add_argument("--as-json", action="store_true", help="Print essentials as JSON instead of key:value lines")
    args = ap.parse_args()

    path = Path(args.hl7)
    if not path.exists():
        print(f"[error] Can't find HL7 file: {path.resolve()}")
        sys.exit(1)

    # 1) Read HL7 & convert in memory
    vxu_text = path.read_text(encoding="utf-8")
    bundle_model = vxu_to_bundle(vxu_text)

    # 2) Optionally write full Bundle JSON
    if args.out:
        try:
            payload = bundle_model.model_dump_json(indent=2, by_alias=True, exclude_none=True)
        except Exception:
            payload = bundle_model.json(indent=2, by_alias=True, exclude_none=True)
        Path(args.out).write_text(payload, encoding="utf-8")

    # 3) Print essentials (map) to stdout
    ess = bundle_to_essentials(bundle_model)
    if args.as_json:
        sys.stdout.write(json.dumps(ess, indent=2))
    else:
        print_essentials_map(ess)

if __name__ == "__main__":
    main()

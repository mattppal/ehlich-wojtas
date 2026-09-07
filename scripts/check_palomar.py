#!/usr/bin/env python3
"""Mechanical Palomar intake checks that do not need Comparator."""

from __future__ import annotations

import json
import re
import sys
import urllib.request
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]
ARXIV_URL = (
    "https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/"
    "main/taxonomies/arxiv-categories.json"
)
MSC_URL = (
    "https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/"
    "main/taxonomies/msc2020-codes.json"
)
GIT_URL = re.compile(r"^https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?$")
SHA = re.compile(r"^[0-9a-f]{40}$")
COMPARATOR_KEYS = {
    "challenge_module",
    "solution_module",
    "theorem_names",
    "definition_names",
    "permitted_axioms",
    "enable_nanoda",
}
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
SOURCE_REL = {
    "formalizes",
    "adapts",
    "independently-proves",
    "background",
    "other",
}
SOURCE_TYPE = {
    "paper",
    "book",
    "web discussion",
    "folklore",
    "original-proof",
    "other",
}
ARTIFACT_SUFFIXES = (
    ".olean",
    ".ilean",
    ".a",
    ".bc",
    ".dll",
    ".dylib",
    ".o",
    ".obj",
    ".so",
    ".trace",
)
LICENSE_NAMES = {
    "license",
    "licence",
    "copying",
    "unlicense",
    "ofl",
    "license.md",
    "licence.md",
    "copying.md",
    "license.txt",
    "licence.txt",
    "copying.txt",
}


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def load_json_url(url: str) -> dict:
    with urllib.request.urlopen(url, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"))


def placeholder_paths(value, path="$") -> list[str]:
    if isinstance(value, dict):
        out = []
        for key, child in value.items():
            out.extend(placeholder_paths(child, f"{path}.{key}"))
        return out
    if isinstance(value, list):
        out = []
        for i, child in enumerate(value):
            out.extend(placeholder_paths(child, f"{path}[{i}]"))
        return out
    if isinstance(value, str) and value.lstrip().startswith("TEMPLATE"):
        return [path]
    return []


def check_yaml(doc: dict) -> None:
    if doc.get("version") != "v0.4":
        fail(f'version must be "v0.4", got {doc.get("version")!r}')
    project = doc.get("project")
    if not isinstance(project, dict):
        fail("project must be a mapping")
    name = project.get("name")
    if not isinstance(name, str) or not name.strip():
        fail("project.name must be a nonempty string")
    desc = project.get("description")
    if not isinstance(desc, str) or not desc.strip() or len(desc.strip()) > 10_000:
        fail("project.description must be nonempty text of at most 10000 characters")
    authors = project.get("authors")
    if not isinstance(authors, list) or not authors or not all(
        isinstance(a, str) and a.strip() for a in authors
    ):
        fail("project.authors must be a nonempty list of nonempty strings")
    if project.get("license") != "Apache-2.0":
        fail("project.license must be Apache-2.0")
    maintainers = project.get("responsible_maintainers")
    if not isinstance(maintainers, list) or not maintainers or not all(
        isinstance(a, str) and a.strip() for a in maintainers
    ):
        fail("project.responsible_maintainers must be a nonempty list of nonempty strings")
    if "repository" in doc:
        fail("omit repository unless this is a thin wrapper")

    classification = doc.get("classification")
    if not isinstance(classification, dict):
        fail("classification must be a mapping")
    arxiv = classification.get("arxiv")
    msc = classification.get("msc2020")
    if not isinstance(arxiv, list) or not (1 <= len(arxiv) <= 8):
        fail("classification.arxiv must have 1 to 8 codes")
    if not isinstance(msc, list) or len(msc) > 8:
        fail("classification.msc2020 must have at most 8 codes")
    if len(arxiv) != len(set(arxiv)) or len(msc) != len(set(msc)):
        fail("classification codes must be unique")

    try:
        arxiv_tax = load_json_url(ARXIV_URL)
        msc_tax = load_json_url(MSC_URL)
    except Exception as exc:
        fail(f"could not fetch Palomar taxonomies: {exc}")
    for code in arxiv:
        if code not in arxiv_tax:
            fail(f"arxiv code {code!r} is not in Palomar taxonomy")
    for code in msc:
        if code not in msc_tax:
            fail(f"msc2020 code {code!r} is not in Palomar taxonomy")

    sources = doc.get("sources")
    if not isinstance(sources, list) or not sources:
        fail("sources must be nonempty")
    original = False
    substantive = False
    for i, src in enumerate(sources):
        if not isinstance(src, dict):
            fail(f"sources[{i}] must be a mapping")
        if not isinstance(src.get("title"), str) or not src["title"].strip():
            fail(f"sources[{i}].title must be nonempty")
        rel = src.get("relationship")
        if rel not in SOURCE_REL:
            fail(f"sources[{i}].relationship must be one of {sorted(SOURCE_REL)}")
        typ = src.get("type")
        if typ is not None and typ not in SOURCE_TYPE:
            fail(f"sources[{i}].type must be one of {sorted(SOURCE_TYPE)}")
        if typ == "original-proof":
            original = True
            if rel != "other":
                fail("original-proof sources must use relationship other")
        if rel in {"formalizes", "adapts", "independently-proves"}:
            substantive = True
    if original and substantive:
        fail("original-proof cannot mix with formalizes/adapts/independently-proves")
    if original:
        extra = [s.get("relationship") for s in sources if s.get("type") == "original-proof"]
        if any(r not in {"background", "other"} for r in (s.get("relationship") for s in sources)):
            fail("original-result sources may only use background or other")
        _ = extra
    elif not substantive:
        fail("source-based result needs formalizes, adapts, or independently-proves")

    automation = doc.get("automation")
    if not isinstance(automation, dict):
        fail("automation must be a mapping")
    methods = automation.get("methods")
    if not isinstance(methods, list) or not methods:
        fail("automation.methods must be nonempty")
    for i, method in enumerate(methods):
        if not isinstance(method, dict) or not str(method.get("method") or "").strip():
            fail(f"automation.methods[{i}].method must be nonempty")

    review = doc.get("review")
    if not isinstance(review, dict) or not str(review.get("status") or "").strip():
        fail("review.status must be nonempty")

    status = doc.get("status")
    if isinstance(status, dict):
        for key in ("sorry_count", "sorry_in_definitions"):
            val = status.get(key)
            if val is not None and not (isinstance(val, int) and val >= 0):
                fail(f"status.{key} must be an unquoted nonnegative integer")

    placeholders = placeholder_paths(doc)
    if placeholders:
        fail("TEMPLATE sentinels remain: " + ", ".join(placeholders))


def check_comparator() -> None:
    cfg = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    extra = set(cfg) - COMPARATOR_KEYS
    if extra:
        fail(f"comparator.json has unknown keys: {sorted(extra)}")
    for key in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
        if key not in cfg:
            fail(f"comparator.json missing {key}")
    if cfg["challenge_module"] == cfg["solution_module"]:
        fail("Challenge and Solution modules must differ")
    if cfg["theorem_names"] != ["EhlichWojtas.ehlich_wojtas_bound"]:
        fail("theorem_names must be [EhlichWojtas.ehlich_wojtas_bound]")
    if cfg.get("definition_names") not in ([], None):
        fail("definition_names must be empty")
    if set(cfg["permitted_axioms"]) != PERMITTED_AXIOMS:
        fail("permitted_axioms must be exactly the three standard axioms")
    if cfg.get("enable_nanoda") is not True:
        fail("enable_nanoda must be true")


def check_manifest() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    for pkg in manifest.get("packages", []):
        url = pkg.get("url", "")
        rev = pkg.get("rev", "")
        name = pkg.get("name", "?")
        if not GIT_URL.match(url):
            fail(f"{name} URL is not a bare public GitHub https URL: {url}")
        if not SHA.match(rev):
            fail(f"{name} rev is not a 40-character lowercase SHA: {rev}")


def check_challenge() -> None:
    text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    lines = text.splitlines()
    if len(lines) > 300:
        fail(f"Challenge.lean has {len(lines)} lines; Palomar warns above 300")
    if len(text.encode("utf-8")) > 32 * 1024:
        fail("Challenge.lean is larger than 32 KiB")
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("import ") and not stripped.startswith("import Mathlib."):
            fail(f"Challenge import is not Mathlib: {stripped}")
    if "theorem ehlich_wojtas_bound" not in text:
        fail("Challenge.lean is missing theorem ehlich_wojtas_bound")
    if "sorry" not in text:
        fail("Challenge.lean must keep its statement sorry")


def check_proof_sorry() -> None:
    paths = [ROOT / "Solution.lean", ROOT / "EhlichWojtas.lean"]
    paths.extend(sorted((ROOT / "EhlichWojtas").glob("*.lean")))
    hits = []
    for path in paths:
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if re.search(r"\bsorry\b", line):
                hits.append(f"{path.relative_to(ROOT)}:{i}:{line.strip()}")
    if hits:
        fail("sorry remains in the proof development:\n  " + "\n  ".join(hits))


def check_license() -> None:
    licenses = [
        p
        for p in ROOT.iterdir()
        if p.is_file() and p.name.lower() in LICENSE_NAMES
    ]
    if len(licenses) != 1:
        fail(f"expected exactly one root licence file, found {[p.name for p in licenses]}")
    text = licenses[0].read_text(encoding="utf-8")
    if "Apache License" not in text or "Version 2.0" not in text:
        fail(f"{licenses[0].name} is not an Apache-2.0 licence text")


def check_artifacts() -> None:
    skip = {".lake", ".cache", ".git", "agent-tools"}
    bad = []
    for path in ROOT.rglob("*"):
        if any(part in skip for part in path.parts):
            continue
        if path.suffix in ARTIFACT_SUFFIXES:
            bad.append(str(path.relative_to(ROOT)))
    if bad:
        fail("compiled artifacts outside .lake: " + ", ".join(bad))


def main() -> int:
    doc = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    if not isinstance(doc, dict):
        fail("formalization.yaml must be one mapping")
    check_yaml(doc)
    check_comparator()
    check_manifest()
    check_challenge()
    check_proof_sorry()
    check_license()
    check_artifacts()
    print("check_palomar.py OK")
    print(f"  arxiv={doc['classification']['arxiv']}")
    print(f"  msc2020={doc['classification']['msc2020']}")
    print(f"  sources={len(doc['sources'])}")
    print("  Challenge imports Mathlib only")
    print("  lake-manifest GitHub pins are 40-character SHAs")
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Check copied foundations and jointly elaborate the four chapters and their bridges.

Uses the unchanged chapter verifier for source screening, inventory and axiom checks.
Run from any directory; Lake uses RevealedPreference's pinned external dependencies.
No root Lake package or cross-chapter dependency is introduced.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = (
    "ChoicePreferenceUtility", "PreferenceProperties", "ConsumerDemand", "RevealedPreference"
)
BASELINE = ROOT / "Volume1/ChoicePreferenceUtility/scripts/verify.py"
spec = importlib.util.spec_from_file_location("chapter_verifier", BASELINE)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


class ConsistencyError(ValueError):
    """A copied foundation, dependency or compatibility check failed."""


def require(condition, message):
    if not condition:
        raise ConsistencyError(message)


def normalize_source(raw, replacements=()):
    """Ignore nested comments and layout, preserving literal strings and operators."""
    code, strings = [], []
    i = 0
    while i < len(raw):
        if raw.startswith("--", i):
            end = raw.find("\n", i)
            i = len(raw) if end < 0 else end
            code.append(" ")
        elif raw.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(raw):
                if raw.startswith("/-", i):
                    depth += 1
                    i += 2
                elif raw.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, "Unclosed Lean comment")
            code.append(" ")
        elif raw[i] == '"':
            start = i
            i += 1
            while i < len(raw) and raw[i] != '"':
                i += 2 if raw[i] == "\\" else 1
            require(i < len(raw), "Unclosed Lean string")
            i += 1
            strings.append(raw[start:i])
            code.append(f"\x00{len(strings) - 1}\x00")
        else:
            code.append(raw[i])
            i += 1
    normalized = "".join(code)
    for old, new in replacements:
        normalized = normalized.replace(old, new)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    for index, value in enumerate(strings):
        normalized = normalized.replace(f"\x00{index}\x00", value)
    return normalized


def check_copies(root=ROOT):
    inventory = json.loads((root / "consistency/copies.json").read_text(encoding="utf-8"))
    seen = set()
    for entry in inventory["copies"]:
        source, destination = entry["source"], entry["destination"]
        require(destination not in seen, f"Duplicate copied destination: {destination}")
        seen.add(destination)
        original = normalize_source((root / source).read_text(encoding="utf-8"))
        copied = normalize_source((root / destination).read_text(encoding="utf-8"),
                                  entry["replacements"])
        require(original == copied, f"Copied foundation drift: {source} -> {destination}")
    require(seen, "Empty copy inventory")
    return len(seen)


def check_environment(root=ROOT):
    reference = root / "Volume1" / CHAPTERS[0]
    manifest = json.loads((reference / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest.pop("name")
    config = tomllib.loads((reference / "lakefile.toml").read_text(encoding="utf-8"))
    toolchain = (reference / "lean-toolchain").read_text().strip()
    for chapter in CHAPTERS:
        folder = root / "Volume1" / chapter
        other = json.loads((folder / "lake-manifest.json").read_text(encoding="utf-8"))
        other.pop("name")
        require(other == manifest, f"Dependency revision drift: {chapter}")
        require((folder / "lean-toolchain").read_text().strip() == toolchain,
                f"Lean toolchain drift: {chapter}")
        options = tomllib.loads((folder / "lakefile.toml").read_text(encoding="utf-8"))
        for field in ("leanOptions", "require"):
            require(options[field] == config[field], f"Lake {field} drift: {chapter}")
        for name in ("verify.py", "test_verify.py"):
            require((folder / "scripts" / name).read_bytes() ==
                    (reference / "scripts" / name).read_bytes(),
                    f"Verifier baseline drift: {chapter}/{name}")
    return toolchain


def collect_joint_sources(root=ROOT):
    imports, bodies, declarations, hashes = [], [], [], {}
    total_theorems = 0
    for chapter in CHAPTERS:
        folder = root / "Volume1" / chapter
        config = json.loads((folder / "proof-manifest.json").read_text(encoding="utf-8"))
        _, found, counts, _ = verifier.collect_sources(folder, config)
        declarations.extend(found)
        total_theorems += sum(counts.values())
        for name in config["modules"]:
            path = folder / name
            hashes[path.relative_to(root).as_posix()] = verifier.digest(path)
            raw = path.read_text(encoding="utf-8")
            body = []
            for line, clean in zip(raw.splitlines(), verifier.uncomment(raw).splitlines()):
                imported = verifier.imports_on_line(clean)
                if imported is None:
                    body.append(line)
                else:
                    for item in imported:
                        if not verifier.is_library_import(item, config) and item not in imports:
                            require(not any(item == c or item.startswith(c + ".")
                                            for c in CHAPTERS),
                                    f"Unexpected cross-chapter package import: {item}")
                            imports.append(item)
            bodies.append("\n".join(body))
        for name in (chapter + ".lean", "proof-manifest.json", "lake-manifest.json",
                     "lakefile.toml", "lean-toolchain", "scripts/verify.py", "scripts/test_verify.py"):
            path = folder / name
            hashes[path.relative_to(root).as_posix()] = verifier.digest(path)
    bridge = root / "consistency/ChapterBridges.lean"
    raw = bridge.read_text(encoding="utf-8")
    clean = verifier.uncomment(raw)
    verifier.check_source(clean, "consistency/ChapterBridges.lean")
    bridges, bridge_theorems = verifier.scan_declarations(clean, "consistency/ChapterBridges.lean")
    declarations.extend(bridges)
    body, bridge_imports = [], []
    for line, clean_line in zip(raw.splitlines(), clean.splitlines()):
        imported = verifier.imports_on_line(clean_line)
        if imported is None:
            body.append(line)
        else:
            bridge_imports.extend(imported)
    require(set(bridge_imports) == set(CHAPTERS), "Bridge file must import exactly the four libraries")
    require(all(len(line) <= 100 for line in raw.splitlines()), "Long line in ChapterBridges.lean")
    require(b"\r" not in bridge.read_bytes(), "ChapterBridges.lean must use LF")
    bodies.append("\n".join(body))
    names = [item["name"] for item in declarations]
    require(len(names) == len(set(names)), "Duplicate declarations across chapters")
    for name in ("consistency/ChapterBridges.lean", "consistency/copies.json",
                 "scripts/verify_consistency.py", "scripts/test_consistency.py"):
        hashes[name] = verifier.digest(root / name)
    fresh = "\n".join("import " + item for item in imports)
    fresh += "\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n"
    fresh += "set_option maxSynthPendingDepth 3\n\n" + "\n\n".join(bodies)
    fresh += "\n\nset_option linter.style.longLine false\n"
    fresh += "\n".join("#print axioms " + name for name in names) + "\n"
    return fresh, declarations, hashes, total_theorems, bridge_theorems, bridges


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()
    toolchain = check_environment()
    copies = check_copies()
    fresh, declarations, hashes, total, bridge_count, bridges = collect_joint_sources()
    output = ROOT / "consistency"
    audit = output / "FreshAudit.lean"
    audit.write_text(fresh, encoding="utf-8", newline="\n")
    if args.generate_only:
        print(f"Generated joint source: {audit}")
        return
    result = subprocess.run([args.lake, "env", "lean", *verifier.SOURCE_LINT_OPTIONS, str(audit)],
                            cwd=ROOT / "Volume1/RevealedPreference", capture_output=True,
                            text=True, encoding="utf-8", errors="replace", timeout=1200)
    log = result.stdout + result.stderr
    (output / "audit.txt").write_text(log, encoding="utf-8", newline="\n")
    verifier.validate_compiler_result(result.returncode, log)
    axioms = verifier.audit_axioms(log, declarations)
    for name, digest in hashes.items():
        require(verifier.digest(ROOT / name) == digest, f"Source changed during audit: {name}")
    record = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_toolchain": toolchain, "copied_modules_checked": copies,
        "chapter_theorems": total, "bridge_theorems": bridge_count,
        "audited_declarations": len(declarations), "joint_fresh_compilation": "passed",
        "axioms_used": sorted({axiom for used in axioms.values() for axiom in used}),
        "bridge_axioms": {item["name"]: axioms[item["name"]] for item in bridges},
        "source_sha256": hashes, "fresh_audit_sha256": verifier.digest(audit),
    }
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n",
                                              encoding="utf-8", newline="\n")
    print(f"Passed {copies} copy checks, joint fresh compilation, {bridge_count} bridge theorems "
          f"and {len(declarations)} declaration axiom audits.")


if __name__ == "__main__":
    main()

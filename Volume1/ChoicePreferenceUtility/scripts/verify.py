"""Build, freshly elaborate all library source, and audit named declaration axioms."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# `lake env lean` sets the import path but does not apply Lake's leanOptions.
# Enforce the same standard lint set in the fresh-source audit explicitly. The
# header linter stays on in `lake build`, where it checks every module's Apache
# header; it is off here only because the audit concatenates all modules into
# one file, which has a single header position.
SOURCE_LINT_OPTIONS = ["-Dlinter.mathlibStandardSet=true", "-Dlinter.style.header=false"]
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide)\b")
DECLARATION = re.compile(
    r"(?:@\[[^]]*\]\s*)*(?:(?:noncomputable|protected)\s+)*"
    r"(theorem|lemma|def|abbrev|structure)\s+([\w.']+)(?=\s|[:({⦃]|$)")


class VerificationError(RuntimeError):
    """A source, compiler, or proof audit failed."""


def require(condition, message):
    # Checks must remain active with python -O and PYTHONOPTIMIZE.
    if not condition:
        raise VerificationError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def uncomment(source):
    """Mask nested comments and strings, preserving line boundaries and offsets.

    This lexical aid supports the library's ordinary Lean declarations; Lean
    itself still parses, elaborates, and kernel-checks the original source.
    """
    out, index, depth, quoted = [], 0, 0, False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif quoted:
            if char == "\\" and index + 1 < len(source):
                out.extend("\n" if c == "\n" else " " for c in source[index:index + 2])
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
                if char == '"':
                    quoted = False
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            end = len(source) if end == -1 else end
            out.extend(" " * (end - index))
            index = end
        elif char == '"':
            quoted = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1
    require(depth == 0 and not quoted, "Unclosed Lean comment or string")
    return "".join(out)


def check_source(clean, module):
    match = FORBIDDEN.search(clean)
    require(match is None, f"Forbidden proof construct in {module}: "
            f"{match.group() if match else ''}")


def imports_on_line(line):
    stripped = line.strip()
    if not stripped.startswith("import "):
        return None
    modules = stripped[len("import "):].split()
    require(modules and all(re.fullmatch(r"[\w.]+", item) for item in modules),
            f"Unsupported import syntax: {stripped}")
    return modules


def libraries(config):
    """The primary library followed by any additional audited libraries."""
    return [config["library"]] + list(config.get("additional_libraries", []))


def is_library_import(item, config):
    return any(item == lib or item.startswith(lib + ".") for lib in libraries(config))


def validate_inventory(root, config):
    modules = config["modules"]
    require(len(modules) == len(set(modules)), "Duplicate modules in proof manifest")
    inventory = set()
    for library in libraries(config):
        inventory |= {p.relative_to(root).as_posix() for p in (root / library).rglob("*.lean")}
    require(set(modules) == inventory,
            f"Proof manifest must cover every library module: {set(modules) ^ inventory}")
    require(set(config["theorem_counts"]) == inventory,
            "Theorem-count inventory must match all library modules")
    for library in libraries(config):
        library_modules = {m for m in inventory if m.startswith(library + "/")}
        root_source = uncomment((root / f"{library}.lean").read_text(encoding="utf-8"))
        check_source(root_source, f"{library}.lean")
        root_imports = set()
        for line in root_source.splitlines():
            if not line.strip():
                continue
            imported = imports_on_line(line)
            require(imported is not None, "Root library must contain only imports and comments")
            root_imports.update(item.replace(".", "/") + ".lean" for item in imported
                                if item.startswith(library + "."))
        require(root_imports == library_modules,
                f"Root library must import every audited module: {root_imports ^ library_modules}")


def scan_declarations(clean, module):
    """Enumerate the ordinary declaration forms used in this library.

    Structures use the default mk constructor and simple named fields. These
    generated constants are also audited. Unsupported declaration forms fail
    explicitly rather than being silently omitted.
    """
    namespaces, declarations, structure = [], [], None
    count = 0
    for raw_line in clean.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if structure and raw_line == line:
            structure = None
        if line.startswith("namespace "):
            name = line[len("namespace "):].strip()
            require(re.fullmatch(r"[\w.']+", name), f"Unsupported namespace in {module}: {line}")
            namespaces.append(name)
        elif line == "end" or line.startswith("end "):
            require(namespaces, f"Unmatched namespace end in {module}: {line}")
            require(line == "end" or namespaces[-1] == line[len("end "):].strip(),
                    f"Mismatched namespace end in {module}: {line}")
            namespaces.pop()
        elif match := DECLARATION.match(line):
            kind, local_name = match.groups()
            name = ".".join(namespaces + [local_name])
            declarations.append({"name": name, "kind": kind, "module": module})
            count += kind in ("theorem", "lemma")
            if kind == "structure":
                require(line.endswith("where") and "extends" not in line,
                        f"Unsupported structure syntax in {module}: {line}")
                structure = name
                declarations.append({"name": name + ".mk", "kind": "constructor", "module": module})
        elif structure and re.match(r"^  [\w']+\s*:", raw_line):
            field = raw_line.strip().split(":", 1)[0].strip()
            declarations.append({"name": structure + "." + field,
                                 "kind": "projection", "module": module})
        elif re.match(r"(?:@\[[^]]*\]\s*)*(?:(?:private|protected|noncomputable|partial)\s+)*"
                      r"(?:theorem|lemma|def|abbrev|structure|inductive|opaque|instance)\b", line):
            raise VerificationError(f"Unsupported declaration syntax in {module}: {line}")
    require(not namespaces, f"Unclosed namespaces in {module}: {namespaces}")
    return declarations, count


def collect_sources(root, config):
    validate_inventory(root, config)
    imports, bodies, declarations, counts, hashes = [], [], [], {}, {}
    for module in config["modules"]:
        path = root / module
        raw = path.read_text(encoding="utf-8")
        clean = uncomment(raw)
        check_source(clean, module)
        found, counts[module] = scan_declarations(clean, module)
        declarations.extend(found)
        hashes[module] = digest(path)
        body = []
        for raw_line, clean_line in zip(raw.splitlines(), clean.splitlines()):
            imported = imports_on_line(clean_line)
            if imported is None:
                body.append(raw_line)
            else:
                for item in imported:
                    if not is_library_import(item, config):
                        statement = "import " + item
                        if statement not in imports:
                            imports.append(statement)
        bodies.append("\n".join(body))
    require(counts == config["theorem_counts"],
            f"Theorem counts differ: {counts} != {config['theorem_counts']}")
    names = [item["name"] for item in declarations]
    require(len(set(names)) == len(names), "Duplicate named declarations in fresh audit")
    fresh = "\n".join(imports) + "\nset_option autoImplicit false\n\n" + "\n\n".join(bodies)
    # The audit's own `#print axioms` lines carry fully qualified names, which can exceed the
    # 100-column style limit; the sources above are line-length checked by `lake build`.
    fresh += "\n\nset_option linter.style.longLine false\n"
    fresh += "\n".join("#print axioms " + name for name in names) + "\n"
    return fresh, declarations, counts, hashes


def validate_compiler_result(returncode, log):
    require(returncode == 0, f"Lean command failed with status {returncode}:\n{log}")
    require(not any(token in log for token in
                    ("error:", "error(", "PANIC", "sorryAx", "warning:")),
            f"Lean emitted an error, warning, or placeholder:\n{log}")


def audit_axioms(log, declarations):
    axioms = {}
    for declaration in declarations:
        name = declaration["name"]
        match = re.search(re.escape("'" + name + "'") + r" depends on axioms:\s*\[([^]]*)\]", log)
        if match:
            found = [a.strip() for a in match[1].split(",") if a.strip()]
        else:
            require("'" + name + "' does not depend on any axioms" in log,
                    f"Missing axiom audit for {name}")
            found = []
        require(set(found) <= ALLOWED, f"Unaccepted axioms for {name}: {found}")
        axioms[name] = found
    return axioms


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    args = parser.parse_args()
    config = json.loads((ROOT / "proof-manifest.json").read_text(encoding="utf-8"))
    fresh, declarations, counts, hashes = collect_sources(ROOT, config)
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    freshpath = out / "FreshAudit.lean"
    freshpath.write_text(fresh, encoding="utf-8", newline="\n")

    def run(command, filename):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                encoding="utf-8", errors="replace", timeout=1200)
        log = result.stdout + result.stderr
        (out / filename).write_text(log, encoding="utf-8", newline="\n")
        validate_compiler_result(result.returncode, log)
        return log

    run([args.lake, "build"], "build.txt")
    log = run([args.lake, "env", "lean", *SOURCE_LINT_OPTIONS, str(freshpath)], "fresh-audit.txt")
    axioms = audit_axioms(log, declarations)
    for name in (*(f"{library}.lean" for library in libraries(config)),
                 "lean-toolchain", "lakefile.toml",
                 "lake-manifest.json", "proof-manifest.json", "scripts/verify.py", "LICENSE"):
        hashes[name] = digest(ROOT / name)
    record = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "theorems": sum(counts.values()), "module_theorems": counts,
        "audited_declarations": len(declarations), "declarations": declarations,
        "full_build": "passed", "fresh_source_compilation": "passed",
        "fresh_source_lint_options": SOURCE_LINT_OPTIONS,
        "axioms": axioms, "source_sha256": hashes,
        "fresh_audit_sha256": digest(freshpath),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "scope": config["scope"], "source": config.get("source"),
    }
    (out / "verification.json").write_text(json.dumps(record, indent=2) + "\n",
                                          encoding="utf-8", newline="\n")
    print(f"Passed build, fresh source elaboration, and {len(declarations)} declaration axiom audits "
          f"({sum(counts.values())} theorems).")


if __name__ == "__main__":
    main()

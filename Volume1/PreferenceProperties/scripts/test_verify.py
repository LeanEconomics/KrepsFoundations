"""Regression tests for verifier failures that could otherwise report success."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

import verify


class VerifierTests(unittest.TestCase):
    def make_library(self, root):
        (root / "Sample").mkdir()
        (root / "Sample/A.lean").write_text(
            "namespace Sample\nlemma checked : True := by trivial\nend Sample\n",
            encoding="utf-8")
        (root / "Sample.lean").write_text("import Sample.A\n", encoding="utf-8")
        return {"library": "Sample", "modules": ["Sample/A.lean"],
                "theorem_counts": {"Sample/A.lean": 1}}

    def test_unlisted_module_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.make_library(root)
            (root / "Sample/Omitted.lean").write_text("", encoding="utf-8")
            with self.assertRaisesRegex(verify.VerificationError, "every library module"):
                verify.validate_inventory(root, config)

    def test_missing_root_import_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.make_library(root)
            (root / "Sample.lean").write_text("/- import Sample.A -/\n", encoding="utf-8")
            with self.assertRaisesRegex(verify.VerificationError, "every audited module"):
                verify.validate_inventory(root, config)

    def test_unscanned_root_declaration_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.make_library(root)
            (root / "Sample.lean").write_text(
                "import Sample.A\nlemma overlooked : True := by trivial\n", encoding="utf-8")
            with self.assertRaisesRegex(verify.VerificationError, "only imports"):
                verify.validate_inventory(root, config)

    def make_additional_library(self, root, config):
        (root / "Extra").mkdir()
        (root / "Extra/B.lean").write_text(
            "namespace Extra\nlemma checked : True := by trivial\nend Extra\n",
            encoding="utf-8")
        (root / "Extra.lean").write_text("import Extra.B\n", encoding="utf-8")
        config["additional_libraries"] = ["Extra"]
        config["modules"].append("Extra/B.lean")
        config["theorem_counts"]["Extra/B.lean"] = 1
        return config

    def test_additional_library_is_audited(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.make_additional_library(root, self.make_library(root))
            verify.validate_inventory(root, config)
            (root / "Extra/Omitted.lean").write_text("", encoding="utf-8")
            with self.assertRaisesRegex(verify.VerificationError, "every library module"):
                verify.validate_inventory(root, config)

    def test_additional_library_root_must_import_its_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.make_additional_library(root, self.make_library(root))
            (root / "Extra.lean").write_text("/- import Extra.B -/\n", encoding="utf-8")
            with self.assertRaisesRegex(verify.VerificationError, "every audited module"):
                verify.validate_inventory(root, config)

    def test_manifest_duplicate_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config = self.make_library(root)
            config["modules"].append("Sample/A.lean")
            with self.assertRaisesRegex(verify.VerificationError, "Duplicate"):
                verify.validate_inventory(root, config)

    def test_nested_comments_and_strings_do_not_hide_code(self):
        source = ('/- outer\n /- namespace Bogus\n axiom fake : False -/\n-/\n'
                  'def message : String := "sorry /- \\\" --"\n'
                  '-- theorem fake : False := sorry\n'
                  'lemma realProof : True := by trivial\n')
        clean = verify.uncomment(source)
        self.assertEqual(len(source), len(clean))
        self.assertEqual(source.count("\n"), clean.count("\n"))
        verify.check_source(clean, "Sample.lean")
        declarations, count = verify.scan_declarations(clean, "Sample.lean")
        self.assertEqual([d["name"] for d in declarations], ["message", "realProof"])
        self.assertEqual(count, 1)

    def test_forbidden_source_is_rejected_even_when_unused(self):
        for source in ("axiom unused : False", "theorem x : True := by sorry",
                       "lemma x : True := by admit", "unsafe def x := 1",
                       "theorem x : True := by native_decide"):
            with self.subTest(source=source):
                with self.assertRaises(verify.VerificationError):
                    verify.check_source(verify.uncomment(source), "Sample.lean")

    def test_declarations_include_definitions_and_generated_structure_constants(self):
        source = ("namespace Sample\n"
                  "structure Data where\n  amount : Nat\n  feasible : 0 <= amount\n"
                  "noncomputable def value : Nat := 1\n"
                  "abbrev other := value\n"
                  "  @[simp] lemma checked : True := by trivial\n"
                  "theorem checkedAgain'\n  : True := checked\nend Sample\n")
        declarations, count = verify.scan_declarations(source, "Sample/A.lean")
        self.assertEqual([d["name"] for d in declarations], [
            "Sample.Data", "Sample.Data.mk", "Sample.Data.amount", "Sample.Data.feasible",
            "Sample.value", "Sample.other", "Sample.checked", "Sample.checkedAgain'"])
        self.assertEqual(count, 2)

    def test_unsupported_declaration_is_not_silently_skipped(self):
        for source in ("private lemma hidden : True := by trivial",
                       "theorem\n  splitName : True := by trivial"):
            with self.subTest(source=source):
                with self.assertRaises(verify.VerificationError):
                    verify.scan_declarations(source, "Sample/A.lean")

    def test_missing_and_unapproved_axiom_records_fail(self):
        declarations = [{"name": "Sample.checked"}]
        for log in ("", "'Sample.checked' depends on axioms: [Injected.false]"):
            with self.subTest(log=log):
                with self.assertRaises(verify.VerificationError):
                    verify.audit_axioms(log, declarations)
        self.assertEqual(verify.audit_axioms(
            "'Sample.checked' depends on axioms: [propext, Classical.choice]", declarations),
            {"Sample.checked": ["propext", "Classical.choice"]})

    def test_failed_compiler_and_warnings_fail(self):
        for code, log in ((1, ""), (0, "warning: declaration uses sorry"),
                          (0, "error: proof failed")):
            with self.subTest(code=code, log=log):
                with self.assertRaises(verify.VerificationError):
                    verify.validate_compiler_result(code, log)

    def test_python_optimization_does_not_disable_checks(self):
        code = """
import verify
checks = [lambda: verify.validate_compiler_result(1, ''),
          lambda: verify.audit_axioms('', [{'name': 'missing'}]),
          lambda: verify.audit_axioms("'x' depends on axioms: [sorryAx]", [{'name': 'x'}]),
          lambda: verify.check_source('axiom unchecked : False', 'test')]
for check in checks:
    try:
        check()
    except verify.VerificationError:
        continue
    raise SystemExit('verification check disappeared under -O')
"""
        result = subprocess.run([sys.executable, "-O", "-c", code],
                                cwd=Path(__file__).resolve().parent,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_current_library_inventory_and_all_theorem_counts(self):
        config = json.loads((verify.ROOT / "proof-manifest.json").read_text(encoding="utf-8"))
        fresh, declarations, counts, _ = verify.collect_sources(verify.ROOT, config)
        self.assertEqual(sum(counts.values()), sum(config["theorem_counts"].values()))
        self.assertGreater(len(declarations), sum(counts.values()))
        for declaration in declarations:
            self.assertIn("#print axioms " + declaration["name"], fresh)
        names = {d["name"] for d in declarations}
        structures = [d["name"] for d in declarations if d["kind"] == "structure"]
        for structure in structures:
            self.assertIn(structure + ".mk", names)
        if structures:
            self.assertTrue(any(d["kind"] == "projection" for d in declarations))
        for library in verify.libraries(config):
            self.assertNotIn("import " + library, fresh)


if __name__ == "__main__":
    unittest.main()

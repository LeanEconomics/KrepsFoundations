"""Regression tests for chapter reuse and the shared pinned environment."""

from pathlib import Path
import json
import shutil
import tempfile
import unittest

import verify_consistency as consistency


ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = (
    "ChoicePreferenceUtility", "PreferenceProperties", "ConsumerDemand", "RevealedPreference"
)


class ConsistencyTests(unittest.TestCase):
    def test_current_copy_inventory_and_parity(self):
        manifest = json.loads((ROOT / "consistency/copies.json").read_text(encoding="utf-8"))
        self.assertEqual(len(manifest["copies"]), 23)
        destinations = [entry["destination"] for entry in manifest["copies"]]
        self.assertEqual(len(set(destinations)), 23)
        consistency.check_copies(ROOT)

    def test_current_environment_matches_across_all_chapters(self):
        consistency.check_environment(ROOT)

    def test_documentation_and_declared_namespace_changes_are_ignored(self):
        source = "namespace Source\ndef condition (x : Nat) := x <= 1\nend Source"
        destination = (
            "/- Added attribution /- nested comment -/ ends here -/\n"
            "namespace Destination\n"
            "-- The condition is unchanged.\n"
            "def condition (x : Nat) := x <= 1\nend Destination"
        )
        self.assertEqual(
            consistency.normalize_source(source, []),
            consistency.normalize_source(destination, [["Destination", "Source"]]),
        )

    def test_strictness_quantifiers_and_endpoints_are_preserved(self):
        original = "def condition : Prop := ∀ x : Nat, 0 ≤ x"
        for mutation in (
            original.replace("≤", "<"),
            original.replace("∀", "∃"),
            original.replace("0", "1"),
        ):
            with self.subTest(mutation=mutation):
                self.assertNotEqual(
                    consistency.normalize_source(original, []),
                    consistency.normalize_source(mutation, []),
                )

    def test_proof_body_changes_are_preserved(self):
        self.assertNotEqual(
            consistency.normalize_source("theorem t : True := by trivial", []),
            consistency.normalize_source("theorem t : True := by exact True.intro", []),
        )

    def test_string_contents_are_preserved(self):
        for before, after in (
            ('def value := "a  b"', 'def value := "a b"'),
            ('def value := "before"', 'def value := "after"'),
            ('def value := "-- not a comment"', 'def value := "-- changed"'),
            ('def value := "/- not a comment -/"', 'def value := "/- changed -/"'),
        ):
            with self.subTest(before=before):
                self.assertNotEqual(
                    consistency.normalize_source(before, []),
                    consistency.normalize_source(after, []),
                )

    def test_changed_copy_is_rejected(self):
        manifest_path = ROOT / "consistency/copies.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            (target / "consistency").mkdir()
            shutil.copy2(manifest_path, target / "consistency/copies.json")
            for entry in manifest["copies"]:
                for key in ("source", "destination"):
                    path = target / entry[key]
                    path.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(ROOT / entry[key], path)
            consistency.check_copies(target)
            path = target / manifest["copies"][0]["destination"]
            original = path.read_text(encoding="utf-8")
            self.assertIn("u y ≤ u x", original)
            path.write_text(original.replace("u y ≤ u x", "u y < u x", 1),
                            encoding="utf-8", newline="\n")
            with self.assertRaises(ValueError):
                consistency.check_copies(target)

    def test_changed_dependency_pin_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for chapter in CHAPTERS:
                for name in (
                    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
                    "scripts/verify.py", "scripts/test_verify.py",
                ):
                    relative = Path("Volume1") / chapter / name
                    (target / relative).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(ROOT / relative, target / relative)
            consistency.check_environment(target)
            path = target / "Volume1/ConsumerDemand/lake-manifest.json"
            manifest = json.loads(path.read_text(encoding="utf-8"))
            mathlib = next(package for package in manifest["packages"]
                           if package["name"] == "mathlib")
            mathlib["rev"] = "0" * 40
            path.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaises(ValueError):
                consistency.check_environment(target)


if __name__ == "__main__":
    unittest.main()

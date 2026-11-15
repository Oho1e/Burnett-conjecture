"""Regression checks for genuine omissions and invalid dependencies in the plan."""

from copy import deepcopy
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from check_slices import SliceError, load, validate
from prepare_slice import build_packet


ROOT = Path(__file__).resolve().parent.parent


class SlicePlanChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = load(ROOT / "docs/formalization/slices.json")

    def altered(self, change, diagnostic):
        plan = deepcopy(self.plan)
        change(plan)
        with self.assertRaisesRegex(SliceError, diagnostic):
            validate(ROOT, plan)

    def test_real_plan_covers_locked_article(self):
        report = validate(ROOT, self.plan)
        self.assertEqual(report["formal_results_mapped"], 17)
        self.assertEqual(report["source_lines_partitioned"], 3475)
        self.assertFalse(report["paper_formalization_verified"])

    def test_source_gap_is_rejected(self):
        self.altered(lambda p: p["slices"][1].__setitem__("source_start", p["slices"][1]["source_start"] + 1), "partition:")

    def test_missing_result_is_rejected(self):
        self.altered(lambda p: p["formal_results"].pop(), "formal-binding:")

    def test_missing_proof_coverage_is_rejected(self):
        def change(p):
            row = next(r for r in p["formal_results"] if r["claim_id"] == "thm:quadratic")
            row["proof_slices"] = [row["closure_slice"]]
        self.altered(change, "proof-range-coverage:")

    def test_missing_inventory_item_is_rejected(self):
        self.altered(lambda p: p["inventory_placement"].pop(), "inventory-placement:")

    def test_unrelated_closure_is_rejected(self):
        def change(p):
            row = next(r for r in p["formal_results"] if r["claim_id"] == "thm:quadratic")
            other = next(r["closure_slice"] for r in p["formal_results"] if r["claim_id"] == "lem:lift")
            row["proof_slices"].append(other)
            row["closure_slice"] = other
        self.altered(change, "closure-location:")

    def test_required_unnumbered_result_is_not_dropped(self):
        self.altered(lambda p: p["required_unnumbered_results"].pop(), "unnumbered-binding:")

    def test_overview_edge_cannot_be_dangling(self):
        self.altered(lambda p: p["overview"]["edges"].append(["UNKNOWN", p["overview"]["nodes"][0]["id"]]), "overview-edge:")

    def test_inverted_canonical_proof_locator_is_rejected(self):
        index = load(ROOT / "docs/statements/source-index.json")
        index["formal_results"][0]["argument_locator"].update(source_line=100, source_endline=90)
        with patch("check_slices.load", side_effect=lambda path: index if path.name == "source-index.json" else load(path)):
            with self.assertRaisesRegex(SliceError, "proof-locator-range:"):
                validate(ROOT, self.plan)

    def test_out_of_range_canonical_inventory_is_rejected(self):
        scope = load(ROOT / "docs/formalization/scope.json")
        row = next(r for r in scope["inventory"] if r["claim_id"] == "ricci:kernel-pure-gauge")
        row["source_ref"].update(line=4000, endline=4001)
        with patch("check_slices.load", side_effect=lambda path: scope if path.name == "scope.json" else load(path)):
            with self.assertRaisesRegex(SliceError, "inventory-source-range:"):
                validate(ROOT, self.plan)

    def test_dangling_dependency_is_rejected(self):
        self.altered(lambda p: p["edges"][0].__setitem__("to", "UNKNOWN"), "edge-endpoint:")

    def test_circular_proof_inputs_are_rejected(self):
        def change(p):
            edge = next(e for e in p["edges"] if e["kind"] == "proof-input")
            p["edges"].append({"from": edge["to"], "to": edge["from"],
                               "kind": "proof-input", "reason": "Deliberate circular premise",
                               "source_lines": edge["source_lines"]})
        self.altered(change, "dependency-cycle:")

    def test_source_identity_change_is_rejected(self):
        self.altered(lambda p: p["paper"].__setitem__("sha256", "0" * 64), "paper-hash:")

    def test_structure_cannot_certify_paper(self):
        self.altered(lambda p: p.__setitem__("paper_formalization_verified", True), "completion:")

    def test_packets_include_their_open_external_interfaces(self):
        for ident in ("P01", "L01", "X03", "X06"):
            with self.subTest(slice_id=ident):
                packet = build_packet(ROOT, ident)
                self.assertIn("## 外部开放接口", packet)
                for interface in self.plan["external_interfaces"]:
                    if ident in interface["consumers"]:
                        self.assertIn(interface["id"], packet)
                        self.assertIn(interface["status"], packet)
                self.assertIn("docs/formalization/library-audit.md", packet)

    def test_packets_preserve_the_exact_source_slice(self):
        source = (ROOT / self.plan["paper"]["path"]).read_text(encoding="utf-8").splitlines()
        for ident in ("A04", "X03", "X06"):
            with self.subTest(slice_id=ident):
                node = next(n for n in self.plan["slices"] if n["id"] == ident)
                packet = build_packet(ROOT, ident)
                exact = "\n".join(source[node["source_start"] - 1:node["source_end"]])
                self.assertIn("```tex\n" + exact + "\n```", packet)
                self.assertIn(self.plan["paper"]["sha256"], packet)

    def test_failed_run_replaces_previous_success_receipt(self):
        scratch = ROOT / ".project-verification/slicing"
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="receipt-regression-", dir=scratch) as temp:
            repo = Path(temp).resolve()
            self.assertTrue(repo.is_relative_to(scratch.resolve()))
            for relative in ("paper/burnett.tex", "docs/formalization/scope.json",
                             "docs/statements/source-index.json", "docs/formalization/slices.json",
                             "docs/formalization/slices.md"):
                target = repo / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((ROOT / relative).read_bytes())
            command = [sys.executable, "-B", str(ROOT / "scripts/check_slices.py"), "--repo", str(repo)]
            good = subprocess.run(command, capture_output=True, text=True, encoding="utf-8")
            self.assertEqual(good.returncode, 0, good.stdout + good.stderr)
            changed = deepcopy(self.plan)
            changed["slices"][1]["source_start"] += 1
            (repo / "docs/formalization/slices.json").write_text(json.dumps(changed), encoding="utf-8")
            bad = subprocess.run(command, capture_output=True, text=True, encoding="utf-8")
            self.assertEqual(bad.returncode, 1)
            receipt = load(repo / ".project-verification/slicing/result.json")
            self.assertEqual(receipt["status"], "slicing-structure-failed")
            self.assertIn("partition:", receipt["error"])


if __name__ == "__main__":
    unittest.main()

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import verify_poincare_status_viewer as v  # noqa: E402


class TestPoincareStatusViewer(unittest.TestCase):
    def _write(self, body: str) -> Path:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / "status.html"
        path.write_text(body, encoding="utf-8")
        return path

    def test_real_status_page_passes(self):
        report = v.run()
        self.assertTrue(report.ok, "\n".join(report.failures))

    def test_main_returns_zero(self):
        self.assertEqual(v.main([]), 0)

    def test_missing_file_fails(self):
        report = v.run(Path("/tmp/poincare-status-viewer-missing.html"))
        self.assertFalse(report.ok)
        self.assertTrue(any("missing status page" in f for f in report.failures))

    def test_forbidden_positive_claim_fails(self):
        original = v.STATUS_PAGE.read_text(encoding="utf-8")
        page = self._write(
            original.replace(
                "Not claimed. External theorem-level mathematics.",
                "This repository proves a new Poincaré theorem.",
            )
        )
        report = v.run(page)
        self.assertFalse(report.ok)
        self.assertTrue(any("forbidden positive claim" in f for f in report.failures))

    def test_negated_boundary_passes(self):
        original = v.STATUS_PAGE.read_text(encoding="utf-8")
        page = self._write(
            original.replace(
                "This repository records a finite",
                "This repository does not prove a new Poincaré theorem. This repository records a finite",
                1,
            )
        )
        report = v.run(page)
        self.assertTrue(report.ok, report.failures)

    def test_missing_visual_separation_fails(self):
        original = v.STATUS_PAGE.read_text(encoding="utf-8")
        page = self._write(
            original.replace("surf cond", "surf").replace("tag cond", "tag")
        )
        report = v.run(page)
        self.assertFalse(report.ok)
        self.assertTrue(any("required CSS marker missing" in f for f in report.failures))

    def test_all_forbidden_positive_phrases_are_guarded(self):
        original = v.STATUS_PAGE.read_text(encoding="utf-8")
        for phrase in v.FORBIDDEN_POSITIVE:
            with self.subTest(phrase=phrase):
                page = self._write(
                    original.replace("</main>", f"<section>{phrase}</section></main>")
                )
                report = v.run(page)
                self.assertFalse(report.ok, phrase)


if __name__ == "__main__":
    unittest.main()

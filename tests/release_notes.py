import importlib.util
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "release_notes_tool", Path(__file__).resolve().parents[1] / "tools/release_notes.py")
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


class ReleaseNotesTest(unittest.TestCase):
    def test_selects_only_exact_version_and_preserves_bullets(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / "1.0.1.md"
            path.write_text("# 1.0.1\n\n## 1.0.1\n\n- Stable summary\n\n"
                            "## 1.0.1.dev3\n\n- A fix\n- Another change\n\n"
                            "## 1.0.1.dev2\n\n- Older changes\n")
            self.assertEqual(TOOL.extract_notes("v1.0.1.dev3", root), "- A fix\n- Another change\n")
            self.assertEqual(TOOL.extract_notes("1.0.1", root), "- Stable summary\n")

    def test_current_notes_use_bullets_without_category_subsections(self):
        directory = Path(__file__).resolve().parents[1] / "docs/releases"
        for stable, count in (("1.0.0", 3), ("1.0.1", 4)):
            for development in range(1, count + 1):
                with self.subTest(stable=stable, development=development):
                    notes = TOOL.extract_notes("v{}.dev{}".format(stable, development), directory)
                    self.assertNotIn("###", notes)
                    self.assertTrue(all(line.startswith("- ") for line in notes.splitlines() if line.strip()))

    def test_rejects_missing_duplicate_empty_and_unfinished_notes(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / "1.0.1.md"
            for content in ("# 1.0.1\n", "## 1.0.1.dev3\n",
                            "## 1.0.1.dev3\nTODO\n", "## 1.0.1.dev3\nTBD\n",
                            "## 1.0.1.dev3\nA\n## 1.0.1.dev3\nB\n"):
                path.write_text(content)
                with self.subTest(content=content), self.assertRaises(ValueError):
                    TOOL.extract_notes("v1.0.1.dev3", root)
            with self.assertRaises(ValueError):
                TOOL.extract_notes("v2.0.0", root)

    def test_rejects_unsupported_tags_and_paths(self):
        for tag in ("../1.0.1", "v1.0.1.rc1", "v1.0", "v1.0.1;echo bad"):
            with self.subTest(tag=tag), self.assertRaises(ValueError):
                TOOL.extract_notes(tag, ".")


if __name__ == "__main__":
    unittest.main()

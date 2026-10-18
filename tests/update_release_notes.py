import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1] / "tools"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


NOTES = load("notes_extractor_for_update_test", TOOLS / "release_notes.py")
with mock.patch.dict(sys.modules, {"release_notes": NOTES}):
    TOOL = load("notes_updater_for_test", TOOLS / "update_release_notes.py")


class UpdateReleaseNotesTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "1.0.1.md").write_text("# 1.0.1\n\n## 1.0.1.dev2\n\n- A fix.\n")
        self.output = self.root / "preview"
        self.release = dict(id=42, tag_name="v1.0.1.dev2", body="Old notes",
                            name="Keep this title", draft=False, prerelease=True,
                            assets=[{"id": 11}])

    def prepare(self):
        with mock.patch.object(TOOL, "api", return_value=self.release) as api:
            TOOL.prepare("v1.0.1.dev2", "stlmc/stlmc", self.root, self.output)
        return api

    def test_preview_reads_only_and_saves_previous_body(self):
        api = self.prepare()
        api.assert_called_once_with("stlmc/stlmc", "GET", "releases/tags/v1.0.1.dev2")
        self.assertEqual((self.output / "notes-before.md").read_text(), "Old notes")
        self.assertEqual((self.output / "notes-proposed.md").read_text(), "- A fix.\n")
        self.assertEqual(json.loads((self.output / "release-before.json").read_text()), self.release)
        self.assertIn("- A fix.", (self.output / "notes.diff").read_text())

    def test_apply_patches_only_body(self):
        self.prepare()
        updated = dict(self.release, body="- A fix.\n")
        with mock.patch.object(TOOL, "api", side_effect=[self.release, updated]) as api:
            TOOL.apply(self.output)
        self.assertEqual(api.call_args_list, [
            mock.call("stlmc/stlmc", "GET", "releases/42"),
            mock.call("stlmc/stlmc", "PATCH", "releases/42", {"body": "- A fix.\n"})])

    def test_refuses_changed_body_or_identity(self):
        self.prepare()
        for changed in (dict(self.release, body="Someone edited this"),
                        dict(self.release, tag_name="v1.0.1.dev3")):
            with self.subTest(changed=changed), \
                    mock.patch.object(TOOL, "api", return_value=changed) as api:
                with self.assertRaises(ValueError):
                    TOOL.apply(self.output)
                self.assertEqual(api.call_count, 1)

    def test_noop_does_not_patch(self):
        self.release["body"] = "- A fix.\n"
        self.prepare()
        with mock.patch.object(TOOL, "api", return_value=self.release) as api:
            TOOL.apply(self.output)
        self.assertEqual(api.call_count, 1)

    def test_invalid_notes_fail_before_any_network_call(self):
        with mock.patch.object(TOOL, "api") as api:
            with self.assertRaises(ValueError):
                TOOL.prepare("v2.0.0", "stlmc/stlmc", self.root, self.output)
        api.assert_not_called()

    def test_api_uses_json_body_without_shell_or_metadata_updates(self):
        with mock.patch.object(TOOL.subprocess, "run") as run:
            run.return_value.stdout = '{"id":42}'
            TOOL.api("stlmc/stlmc", "PATCH", "releases/42", {"body": "Text with $() and quotes"})
        self.assertEqual(json.loads(run.call_args.kwargs["input"]), {"body": "Text with $() and quotes"})
        self.assertNotIn("shell", run.call_args.kwargs)
        self.assertEqual(run.call_args.args[0][-2:], ["--input", "-"])

    def test_invalid_repository_does_not_execute_gh(self):
        with mock.patch.object(TOOL.subprocess, "run") as run:
            with self.assertRaises(ValueError):
                TOOL.api("stlmc/stlmc;echo bad", "GET", "releases/42")
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()

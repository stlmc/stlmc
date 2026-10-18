"""Static dependency audits must fail closed without executing candidates."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from stlmc.cli import native_linkage as linkage


class NativeLinkageTest(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.executable = Path(directory.name) / "solver"
        self.executable.touch()

    def linux(self, dynamic="", program=""):
        if dynamic:
            dynamic = "Dynamic section at offset 0x10 contains 2 entries:\n0x1 " + dynamic + "\n0x0 (NULL) 0x0\n"
        else:
            dynamic = "There is no dynamic section in this file.\n"
        if "Requesting program interpreter:" in program:
            program = " INTERP 0\n" + program
        with mock.patch.object(linkage, "_tool", return_value="/usr/bin/readelf"), \
                mock.patch.object(linkage, "_inspect", side_effect=["ELF Header:\nType: EXEC", dynamic, "  LOAD 0\n" + program]) as inspect:
            result = linkage.audit_static_linkage(self.executable, platform="linux")
        self.assertTrue(all(call.args[0][0] == "/usr/bin/readelf" for call in inspect.call_args_list))
        return result

    def test_static_elf(self):
        self.assertTrue(self.linux()["fully_static"])

    def test_object_or_empty_elf_report_rejected(self):
        for outputs in (["ELF Header:\nType: REL"], ["ELF Header:\nType: EXEC", "", ""]):
            with self.subTest(outputs=outputs), \
                    mock.patch.object(linkage, "_tool", return_value="readelf"), \
                    mock.patch.object(linkage, "_inspect", side_effect=outputs), \
                    self.assertRaisesRegex(RuntimeError, "ELF executable"):
                linkage.audit_static_linkage(self.executable, platform="linux")

    def test_empty_or_unparsed_dynamic_report_is_rejected(self):
        for dynamic in ("", "garbage", "Dynamic section at offset 0x10 contains 2 entries:\n0x1 (NEEDED) libClp.so.1\n0x0 (NULL) 0x0"):
            with self.subTest(dynamic=dynamic), \
                    mock.patch.object(linkage, "_tool", return_value="readelf"), \
                    mock.patch.object(linkage, "_inspect", side_effect=["ELF Header:\nType: EXEC", dynamic, " LOAD 0"]), \
                    self.assertRaisesRegex(RuntimeError, "report"):
                linkage.audit_static_linkage(self.executable, platform="linux")

    def test_auxiliary_library_loading_is_rejected(self):
        for tag in ("AUDIT", "DEPAUDIT", "FILTER", "AUXILIARY"):
            with self.subTest(tag=tag), self.assertRaisesRegex(RuntimeError, "auxiliary"):
                self.linux("(" + tag + ") Audit library: [libcustom.so]")

    def test_only_system_runtimes_permitted(self):
        report = self.linux("(NEEDED) Shared library: [libc.so.6]",
                            "[Requesting program interpreter: /lib64/ld-linux-x86-64.so.2]")
        self.assertFalse(report["fully_static"])
        self.assertEqual(report["dependencies"], ["libc.so.6"])

    def test_third_party_dependency_rejected(self):
        for name in ("libClp.so.1", "libnlopt.so.0", "libz.so.1", "/private/libc.so.6"):
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, "Third-party"):
                self.linux("(NEEDED) Shared library: [" + name + "]")

    def test_loader_overrides_rejected(self):
        for tag in ("RPATH", "RUNPATH"):
            with self.subTest(tag=tag), self.assertRaisesRegex(RuntimeError, "search path"):
                self.linux("(" + tag + ") Library path: [$ORIGIN/lib]")

    def test_private_or_relative_interpreter_rejected(self):
        for path in ("/private/ld-linux-x86-64.so.2", "/lib/../private/ld-linux-x86-64.so.2"):
            with self.subTest(path=path), self.assertRaisesRegex(RuntimeError, "interpreter"):
                self.linux(program="[Requesting program interpreter: " + path + "]")

    def test_shared_object_is_not_an_executable(self):
        with self.assertRaisesRegex(RuntimeError, "no executable interpreter"):
            self.linux("(NEEDED) Shared library: [libc.so.6]")

    def macos(self, dependency="/usr/lib/libSystem.B.dylib", loads=None):
        if loads is None:
            loads = "cmd LC_MAIN\ncmd LC_LOAD_DYLINKER\ncmdsize 32\nname /usr/lib/dyld (offset 12)\n"
        output = str(self.executable) + ":\n\t" + dependency + " (compatibility version 1.0.0, current version 1.0.0)\n"
        with mock.patch.object(linkage, "_tool", return_value="/usr/bin/otool"), \
                mock.patch.object(linkage, "_inspect", side_effect=[output, loads]):
            return linkage.audit_static_linkage(self.executable, platform="darwin")

    def test_macos_system_runtime(self):
        self.assertEqual(self.macos()["format"], "Mach-O")

    def test_macos_foreign_dependency_rejected(self):
        for path in ("@rpath/libnlopt.dylib", "/opt/homebrew/lib/libnlopt.dylib", "/usr/lib/../local/libbad.dylib"):
            with self.subTest(path=path), self.assertRaisesRegex(RuntimeError, "Third-party"):
                self.macos(path)

    def test_macos_search_path_and_library_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "LC_RPATH"):
            self.macos(loads="cmd LC_MAIN\ncmd LC_RPATH\n")
        with self.assertRaisesRegex(RuntimeError, "LC_MAIN"):
            self.macos(loads="cmd LC_ID_DYLIB\n")

    def test_macos_private_or_missing_loader_rejected(self):
        for loads in ("cmd LC_MAIN\n", "cmd LC_MAIN\ncmd LC_LOAD_DYLINKER\ncmdsize 32\nname /private/custom-dyld (offset 12)\n"):
            with self.subTest(loads=loads), self.assertRaisesRegex(RuntimeError, "interpreter"):
                self.macos(loads=loads)

    def test_macos_loader_environment_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "environment override"):
            self.macos(loads="cmd LC_MAIN\ncmd LC_DYLD_ENVIRONMENT\n")

    def test_inspection_timeout_is_an_error(self):
        with mock.patch.object(linkage, "_tool", return_value="readelf"), \
                mock.patch.object(linkage, "_inspect", side_effect=subprocess.TimeoutExpired("readelf", 30)), \
                self.assertRaisesRegex(RuntimeError, "audit failed"):
            linkage.audit_static_linkage(self.executable, platform="linux")

    def test_missing_audit_tool_is_an_error(self):
        with mock.patch.object(linkage.shutil, "which", return_value=None), \
                self.assertRaisesRegex(RuntimeError, "required to audit"):
            linkage.audit_static_linkage(self.executable, platform="linux")

    def test_no_implicit_fallback_on_unsupported_platform(self):
        with self.assertRaisesRegex(RuntimeError, "Linux and macOS only"):
            linkage.audit_static_linkage(self.executable, platform="win32")

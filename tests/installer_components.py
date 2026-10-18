"""Installer routing and transactional builds, with no downloads or OS installs."""
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from stlmc.cli import installer


class ComponentInstallerTest(unittest.TestCase):
    def setUp(self):
        # Routing/package tests exercise the validated installer profile, not
        # whichever Python happens to execute this mock-only suite.
        profile = mock.patch.object(installer.sys, "version_info", (3, 10))
        profile.start()
        self.addCleanup(profile.stop)

    def test_combined_multi_target_install(self):
        with mock.patch.object(installer.solvers, "main", return_value=0) as engine, \
                mock.patch.object(installer, "_visualize", return_value=0) as visual:
            self.assertEqual(installer.main(["install", "--solver", "z3", "cvc5", "--visualize", "html", "pdf"]), 0)
        self.assertEqual(engine.call_args_list, [mock.call(["z3"]), mock.call(["cvc5"])])
        self.assertEqual(visual.call_args_list, [mock.call(check=False, output_format="html"), mock.call(check=False, output_format="pdf")])

    def test_install_all_is_explicit_and_routes_every_target(self):
        with mock.patch.object(installer.solvers, "main", return_value=0) as engine, \
                mock.patch.object(installer, "_visualize", return_value=0) as visual:
            self.assertEqual(installer.main(["install", "--all"]), 0)
        self.assertEqual(engine.call_count, 4)
        self.assertEqual(visual.call_count, 3)

    def test_checks_continue_after_individual_failure_or_exception(self):
        with mock.patch.object(installer.solvers, "main", side_effect=[RuntimeError("missing first"), 1, 0]) as engine, \
                mock.patch.object(installer, "_visualize", side_effect=[RuntimeError("missing HTML"), 0]) as visual, \
                mock.patch("sys.stderr", new=io.StringIO()):
            self.assertEqual(installer.main(["check", "--solver", "z3", "cvc5", "dreal", "--visualize", "html", "pdf"]), 1)
        self.assertEqual(engine.call_count, 3)
        self.assertEqual(visual.call_count, 2)

    def test_unvalidated_visualization_profile_fails_without_installing(self):
        with mock.patch.object(installer.sys, "version_info", (3, 14)), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch.object(installer.solvers, "main") as engine, \
                mock.patch("sys.stderr", new=io.StringIO()) as stderr:
            self.assertEqual(installer.main(["install", "--solver", "z3", "--visualize", "html"]), 1)
            self.assertIn("No validated", stderr.getvalue())
        pip.assert_not_called()
        engine.assert_not_called()

    def test_visualization_native_crash_is_contained(self):
        with mock.patch.object(installer.subprocess, "run", return_value=subprocess.CompletedProcess([], -11, "", "native crash")):
            status = installer.visualize_status(["matplotlib"])
        self.assertFalse(status["matplotlib"][0])
        self.assertIn("-11", status["matplotlib"][1])

    def test_visualization_version_mismatch_skips_smoke(self):
        with mock.patch.object(installer.solvers, "_python_package_status", return_value=(False, "installed other, expected pinned")):
            self.assertEqual(installer._probe_visualization("matplotlib", "matplotlib==3.10.8"),
                             (False, "installed other, expected pinned"))

    def test_invalid_or_missing_targets_never_install_or_probe(self):
        for args in (["solver", "z3"], ["visualize"], ["install"],
                     ["install", "--solver", "all"], ["check", "--solver", "unknown"],
                     ["install", "--solver", "z3", "z3"],
                     ["check", "--solver", "z3", "--solver", "cvc5"],
                     ["check", "--visualize", "html", "html"],
                     ["check", "--visualize", "html", "--visualize", "pdf"],
                     ["install", "--all", "--all"],
                     ["install", "--all", "--solver", "z3"]):
            with self.subTest(args=args), mock.patch.object(installer.solvers, "main") as solver, \
                    mock.patch.object(installer, "_visualize") as visual, \
                    mock.patch.object(installer, "build_yices") as build, \
                    mock.patch("sys.stderr", new=io.StringIO()):
                with self.assertRaises(SystemExit) as error:
                    installer.main(args)
                self.assertEqual(error.exception.code, 2)
            solver.assert_not_called()
            visual.assert_not_called()
            build.assert_not_called()

    def test_install_and_check_are_mutually_exclusive(self):
        for args in (["install", "--check", "--solver", "z3"],
                     ["check", "--install", "--visualize", "html"],
                     ["--check", "visualize", "--install"]):
            with self.subTest(args=args), mock.patch("sys.stderr", new=io.StringIO()), \
                    mock.patch.object(installer.solvers, "main") as engine:
                with self.assertRaises(SystemExit) as error:
                    installer.main(args)
                self.assertEqual(error.exception.code, 2)
                engine.assert_not_called()

    def test_solver_install_is_explicit(self):
        with mock.patch.object(installer.solvers, "main", return_value=0) as engine:
            self.assertEqual(installer.main(["install", "--solver", "z3"]), 0)
        engine.assert_called_once_with(["z3"])

    def test_no_arguments_only_show_help(self):
        with mock.patch.object(installer.solvers, "main") as old, mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(installer.main([]), 0)
        old.assert_not_called()

    def test_global_check_checks_both_components(self):
        with mock.patch.object(installer.solvers, "main", return_value=1) as old, \
                mock.patch.object(installer, "_visualize", return_value=0) as visual, \
                mock.patch.object(installer.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")):
            self.assertEqual(installer.main(["check"]), 1)
        self.assertEqual(old.call_args_list, [mock.call([name, "--check"]) for name in ("z3", "cvc5", "yices", "dreal")])
        self.assertEqual(visual.call_args_list, [mock.call(check=True, output_format=name) for name in ("html", "pdf", "text")])

    def test_selected_check_cannot_install(self):
        with mock.patch.object(installer.solvers, "main", return_value=0) as old:
            self.assertEqual(installer.main(["check", "--solver", "z3"]), 0)
        old.assert_called_once_with(["z3", "--check"])

    def test_legacy_solver_engine_routing(self):
        with mock.patch.object(installer.solvers, "main", return_value=0) as old:
            self.assertEqual(installer.main(["check", "--solver", "dreal"]), 0)
        old.assert_called_once_with(["dreal", "--check"])

    def test_build_defaults_to_mcsat_and_supports_thread_safety(self):
        with mock.patch.object(installer, "build_yices") as build, \
                mock.patch.object(installer.solvers, "_install_python_package"):
            self.assertEqual(installer.main(["install", "--solver", "yices", "--build", "--thread-safe", "--jobs", "3"]), 0)
        self.assertTrue(build.call_args.kwargs["mcsat"])
        self.assertTrue(build.call_args.kwargs["thread_safe"])
        self.assertEqual(build.call_args.kwargs["jobs"], 3)

    def test_explicit_without_mcsat_is_forwarded(self):
        with mock.patch.object(installer, "build_yices") as build, \
                mock.patch.object(installer.solvers, "_install_python_package"):
            self.assertEqual(installer.main(["install", "--solver", "yices", "--build", "--without-mcsat"]), 0)
        self.assertFalse(build.call_args.kwargs["mcsat"])

    def test_source_check_is_read_only_and_checks_native_flags(self):
        with mock.patch.object(installer.solvers, "main", return_value=0), \
                mock.patch.object(installer.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, "thread_safe=False", "")) as probe, \
                mock.patch.object(installer, "build_yices") as build:
            self.assertEqual(installer.main(["check", "--solver", "yices", "--thread-safe"]), 1)
        build.assert_not_called()
        self.assertEqual(probe.call_args.args[0][-2:], ["1", "1"])
        self.assertEqual(probe.call_args.kwargs["timeout"], 30)

    def test_without_mcsat_check_is_a_minimum_capability_check(self):
        with mock.patch.object(installer.solvers, "main", return_value=0), \
                mock.patch.object(installer.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "")) as probe:
            self.assertEqual(installer.main(["check", "--solver", "yices", "--thread-safe", "--without-mcsat"]), 0)
        self.assertEqual(probe.call_args.args[0][-2:], ["1", "0"])

    def test_failed_yices_baseline_skips_capabilities_and_continues(self):
        with mock.patch.object(installer.solvers, "main", side_effect=[1, 0]) as engine, \
                mock.patch.object(installer.subprocess, "run") as probe, \
                mock.patch.object(installer, "_visualize", return_value=0) as visual:
            self.assertEqual(installer.main(["check", "--solver", "yices", "z3", "--visualize", "text"]), 1)
        self.assertEqual(engine.call_args_list, [mock.call(["yices", "--check"]), mock.call(["z3", "--check"])])
        probe.assert_not_called()
        visual.assert_called_once_with(check=True, output_format="text")

    def test_yices_capability_missing_binding_has_no_traceback(self):
        real_run = subprocess.run
        def missing_binding(command, **kwargs):
            command = list(command)
            command[2] = "import sys; sys.modules['yices'] = None\n" + command[2]
            return real_run(command, **kwargs)
        with mock.patch.object(installer.solvers, "main", return_value=0), \
                mock.patch.object(installer.subprocess, "run", side_effect=missing_binding), \
                mock.patch("sys.stderr", new=io.StringIO()) as stderr:
            self.assertEqual(installer.main(["check", "--solver", "yices", "--thread-safe"]), 1)
        self.assertIn("Yices unavailable", stderr.getvalue())
        self.assertNotIn("Traceback", stderr.getvalue())

    def test_invalid_source_options_fail_before_actions(self):
        for args in [["install", "--solver", "z3", "--build"], ["install", "--solver", "yices", "--thread-safe"],
                     ["install", "--solver", "yices", "--build", "--jobs", "0"],
                     ["install", "--solver", "yices", "z3", "--build"],
                     ["install", "--solver", "yices", "--visualize", "html", "--build"],
                     ["install", "--solver", "yices", "--jobs", "1"],
                     ["check", "--solver", "yices", "--build"],
                     ["check", "--solver", "yices", "--jobs", "1"],
                     ["check", "--solver", "yices", "--prefix", "/tmp/build"],
                     ["check", "--solver", "yices", "--source", "/tmp/src"],
                     ["check", "--solver", "yices", "z3", "--without-mcsat"]]:
            with self.subTest(args=args), mock.patch("sys.stderr", new=io.StringIO()), \
                    mock.patch.object(installer, "build_yices") as build:
                with self.assertRaises(SystemExit):
                    installer.main(args)
                build.assert_not_called()

    def test_pip_failure_does_not_activate_new_native_build(self):
        with mock.patch.object(installer.solvers, "_install_python_package", side_effect=RuntimeError("pip failed")), \
                mock.patch.object(installer, "build_yices") as build, mock.patch("sys.stderr", new=io.StringIO()):
            self.assertEqual(installer.main(["install", "--solver", "yices", "--build"]), 1)
        build.assert_not_called()

    def test_visualize_optional_dependencies_do_not_fail_html(self):
        status = {name: (True, "ok") for name in installer.VISUALIZE_PACKAGES}
        status.update(matplotlib=(False, "missing"))
        with mock.patch.object(installer, "visualize_status", return_value=status), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(installer.main(["check", "--visualize", "html"]), 0)
            self.assertEqual(installer.main(["check", "--visualize", "pdf"]), 1)
            self.assertEqual(installer.main(["check", "--visualize", "text"]), 0)
        pip.assert_not_called()

    def test_visualize_repairs_missing_python_packages_only(self):
        missing = {name: (False, "missing") for name in installer.VISUALIZE_PACKAGES}
        available = dict(missing, **{name: (True, "ok") for name in installer.VISUALIZE_PACKAGES})
        with mock.patch.object(installer, "visualize_status", side_effect=[missing, available]), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(installer.main(["install", "--visualize", "html"]), 0)
        self.assertEqual([x.args[0] for x in pip.call_args_list],
                         [installer.VISUALIZE_PACKAGES[n] for n in ("numpy", "scipy", "bokeh")])

    def test_pdf_does_not_require_or_install_bokeh(self):
        status = {name: (True, "ok") for name in installer.VISUALIZE_PACKAGES}
        status.update(bokeh=(False, "not installed"))
        with mock.patch.object(installer, "visualize_status", return_value=status), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(installer.main(["install", "--visualize", "pdf"]), 0)
            self.assertEqual(installer.main(["check", "--visualize", "pdf"]), 0)
            self.assertEqual(installer.main(["check", "--visualize", "html"]), 1)
        pip.assert_not_called()

    def test_text_checks_and_repairs_base_dependencies_only(self):
        status = {name: (False, "missing") for name in installer.VISUALIZE_PACKAGES}
        with mock.patch.object(installer, "visualize_status", return_value=status), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(installer.main(["check", "--visualize", "text"]), 1)
            pip.assert_not_called()
            self.assertEqual(installer.main(["install", "--visualize", "text"]), 1)
        self.assertEqual(pip.call_args_list, [mock.call(installer.VISUALIZE_PACKAGES[n]) for n in ("numpy", "scipy")])

    def test_explicit_pdf_installs_missing_matplotlib(self):
        missing = {name: (True, "ok") for name in installer.VISUALIZE_PACKAGES}
        missing.update(matplotlib=(False, "missing"))
        ready = dict(missing, matplotlib=(True, "ok"))
        with mock.patch.object(installer, "visualize_status", side_effect=[missing, ready]), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(installer.main(["install", "--visualize", "pdf"]), 0)
        pip.assert_called_once_with(installer.VISUALIZE_PACKAGES["matplotlib"])

    def test_pdf_install_errors_are_reported_without_tracebacks(self):
        status = {name: (True, "ok") for name in installer.VISUALIZE_PACKAGES}
        status.update(matplotlib=(False, "missing"))
        for error in [RuntimeError("pip failed"),
                      subprocess.CalledProcessError(1, ["sudo", "apt-get"])]:
            with self.subTest(error=error), mock.patch.object(installer, "visualize_status", return_value=status), \
                    mock.patch.object(installer.solvers, "_install_python_package", side_effect=error), \
                    mock.patch("sys.stderr", new=io.StringIO()) as stderr:
                self.assertEqual(installer.main(["install", "--visualize", "pdf"]), 1)
                self.assertNotIn("Traceback", stderr.getvalue())
                self.assertTrue(stderr.getvalue().strip())

    def test_failed_probe_after_install_does_not_deny_install_attempt(self):
        status = {name: (True, "ok") for name in installer.VISUALIZE_PACKAGES}
        status.update(matplotlib=(False, "PDF unavailable"))
        with mock.patch.object(installer, "visualize_status", return_value=status), \
                mock.patch.object(installer.solvers, "_install_python_package") as install, \
                mock.patch("sys.stdout", new=io.StringIO()) as stdout:
            self.assertEqual(installer.main(["install", "--visualize", "pdf"]), 1)
            self.assertNotIn("No administrator commands were run", stdout.getvalue())
        install.assert_called_once_with(installer.VISUALIZE_PACKAGES["matplotlib"])

    def test_backend_status_contains_native_crashes(self):
        with mock.patch.object(installer.solvers.subprocess, "run", return_value=subprocess.CompletedProcess([], -11, "", "crashed")):
            available, detail = installer.solvers._backend_status("cvc5")
        self.assertFalse(available)
        self.assertIn("-11", detail)


class SourceBuildTransactionTest(unittest.TestCase):
    def fake_build(self, command, cwd, environment, log):
        self.commands.append(command)
        if "--prefix=" in " ".join(command):
            self.prefix = Path(next(x.split("=", 1)[1] for x in command if x.startswith("--prefix=")))
            self.environment = environment
        if command == ["make", "install"]:
            (self.prefix / "lib").mkdir(parents=True)
            (self.prefix / "lib" / "libyices.so").write_bytes(b"fake-library")

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        (self.source / "configure").write_text("#!/bin/sh\n")
        self.commands = []

    def tearDown(self):
        self.temporary.cleanup()

    def patches(self, probe):
        from contextlib import ExitStack
        stack = ExitStack()
        stack.enter_context(mock.patch.object(installer, "solver_data_dir", return_value=self.root / "data"))
        stack.enter_context(mock.patch.object(installer.shutil, "which", return_value="/tool"))
        stack.enter_context(mock.patch.object(installer, "_logged", side_effect=self.fake_build))
        stack.enter_context(mock.patch.object(installer, "_probe_library", return_value=probe))
        stack.enter_context(mock.patch("sys.stdout", new=io.StringIO()))
        return stack

    def test_activate_only_verified_native_build(self):
        flags = dict(version="2.7.0", thread_safe=True, mcsat=True)
        with self.patches(flags):
            result = installer.build_yices(source=self.source, thread_safe=True, jobs=2)
        active = json.loads((self.root / "data/yices/active.json").read_text())
        self.assertEqual(active, result)
        self.assertTrue(Path(active["library"]).is_file())
        self.assertIn("--enable-mcsat", self.commands[0])
        self.assertIn("--enable-thread-safety", self.commands[0])
        self.assertEqual(self.commands[1], ["make", "-j", "2"])
        self.assertIn(str(self.prefix / "lib"), self.environment["LDFLAGS"])
        self.assertTrue((self.source / "configure").exists())

    def test_capability_failure_preserves_previous_activation(self):
        active = self.root / "data/yices/active.json"
        active.parent.mkdir(parents=True)
        active.write_text('{"library":"previous"}')
        with self.patches(dict(version="2.7.0", thread_safe=False, mcsat=True)):
            with self.assertRaisesRegex(RuntimeError, "previous installation remains active"):
                installer.build_yices(source=self.source, thread_safe=True)
        self.assertEqual(active.read_text(), '{"library":"previous"}')

    def test_without_mcsat_verified_and_labelled(self):
        with self.patches(dict(version="2.7.0", thread_safe=True, mcsat=False)):
            result = installer.build_yices(source=self.source, thread_safe=True, mcsat=False)
        self.assertFalse(result["mcsat"])
        self.assertIn("--disable-mcsat", self.commands[0])

    def test_missing_tools_do_not_download(self):
        with mock.patch.object(installer.shutil, "which", return_value=None), \
                mock.patch.object(installer.urllib.request, "urlretrieve") as download:
            with self.assertRaisesRegex(RuntimeError, "Missing Yices build tools"):
                installer.build_yices(prefix=self.root)
        download.assert_not_called()

    def test_archive_rejects_traversal_and_symlinks(self):
        for name, kind in [("../escape", tarfile.REGTYPE), ("safe/link", tarfile.SYMTYPE)]:
            archive = self.root / "unsafe.tar.gz"
            with tarfile.open(archive, "w:gz") as output:
                member = tarfile.TarInfo(name); member.type = kind
                if kind == tarfile.SYMTYPE: member.linkname = "/tmp/escape"
                output.addfile(member)
            with self.assertRaisesRegex(RuntimeError, "Unsafe"):
                installer._extract_source(archive, self.root / "out")


if __name__ == "__main__":
    unittest.main()

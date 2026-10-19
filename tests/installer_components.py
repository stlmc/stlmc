"""Installer routing and transactional builds, with no downloads or OS installs."""
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from stlmc.cli import installer


class ComponentInstallerTest(unittest.TestCase):
    def setUp(self):
        # Routing/package tests exercise the validated installer profile, not
        # whichever Python happens to execute this mock-only suite.
        profile = mock.patch.object(installer.sys, "version_info", (3, 11))
        profile.start()
        self.addCleanup(profile.stop)

    def test_supported_python_versions_share_pins_and_isolated_profiles(self):
        from stlmc.cli.dependency_policy import visualization_packages
        expected = {"numpy": "numpy==2.3.5", "scipy": "scipy==1.16.3",
                    "bokeh": "bokeh==3.8.2", "matplotlib": "matplotlib==3.10.8"}
        for minor in range(11, 15):
            with self.subTest(minor=minor):
                result = visualization_packages((3, minor, 0))
                self.assertEqual(result, expected)
                result["numpy"] = "changed"
                self.assertEqual(visualization_packages((3, minor)), expected)
                with mock.patch.object(installer.sys, "version_info", (3, minor)), \
                        mock.patch.object(installer, "_visualize", return_value=0) as visual:
                    self.assertEqual(installer.main(["install", "--visualize", "html", "pdf"]), 0)
                    self.assertEqual(installer.main(["check", "--visualize", "html", "pdf"]), 0)
                    self.assertEqual(visual.call_count, 4)

    def test_base_and_installer_numerical_pins_remain_consistent(self):
        import tomllib
        from stlmc.cli.dependency_policy import visualization_packages
        project = tomllib.loads((Path(__file__).resolve().parent.parent / "pyproject.toml").read_text())["project"]
        self.assertEqual(project["requires-python"], ">=3.11,<3.15")
        self.assertIn("sympy==1.14.0", project["dependencies"])
        self.assertIn("mpmath==1.3.0", project["dependencies"])
        for name in ("numpy", "scipy"):
            self.assertIn(visualization_packages((3, 11))[name], project["dependencies"])

    def test_managed_install_uses_packaged_transitive_constraints(self):
        constraints = Path(installer.solvers.__file__).with_name("dependency-constraints.txt")
        self.assertTrue(constraints.is_file())
        pins = {line.strip() for line in constraints.read_text().splitlines()
                if line.strip() and not line.startswith("#")}
        self.assertTrue(set(installer.VISUALIZE_PACKAGES.values()) <= pins)
        with mock.patch.object(installer.solvers, "_run") as run:
            installer.solvers._install_python_package("bokeh==3.8.2")
        self.assertEqual(run.call_args.args[0][-3:],
                         ["--constraint", str(constraints), "bokeh==3.8.2"])

    def test_out_of_range_python_versions_are_rejected(self):
        from stlmc.cli.dependency_policy import visualization_packages
        for version in ((3, 8), (3, 9), (3, 10), (3, 15), (4, 0)):
            with self.subTest(version=version), self.assertRaisesRegex(RuntimeError, "3.11 through 3.14"):
                visualization_packages(version)

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
        with mock.patch.object(installer.sys, "version_info", (3, 10)), \
                mock.patch.object(installer.solvers, "_install_python_package") as pip, \
                mock.patch.object(installer.solvers, "main") as engine, \
                mock.patch("sys.stderr", new=io.StringIO()) as stderr:
            self.assertEqual(installer.main(["install", "--solver", "z3", "--visualize", "html"]), 1)
            self.assertIn("No supported", stderr.getvalue())
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

    def test_explicit_dreal_build_does_not_install_bindings_or_use_legacy_download(self):
        with mock.patch.object(installer, "build_dreal") as build, \
                mock.patch.object(installer, "build_yices") as yices, \
                mock.patch.object(installer.solvers, "main") as legacy, \
                mock.patch.object(installer.solvers, "_install_python_package") as pip:
            self.assertEqual(installer.main(["install", "--solver", "dreal", "--experimental-build",
                                             "--jobs", "3", "--prefix", "/private/managed"]), 0)
        build.assert_called_once_with(prefix=Path('/private/managed'), jobs=3)
        yices.assert_not_called()
        legacy.assert_not_called()
        pip.assert_not_called()

    def test_dreal_default_install_and_check_never_start_a_source_build(self):
        for action in ('install', 'check'):
            with self.subTest(action=action), mock.patch.object(installer, 'build_dreal') as build, \
                    mock.patch.object(installer.solvers, 'main', return_value=0) as legacy:
                self.assertEqual(installer.main([action, '--solver', 'dreal']), 0)
                legacy.assert_called_once_with(['dreal'] + (['--check'] if action=='check' else []))
                build.assert_not_called()

    def test_dreal_install_success_does_not_bypass_stricter_check_failure(self):
        with mock.patch.object(installer, 'build_dreal') as build, \
                mock.patch.object(installer.solvers, 'main', side_effect=[0, 1]) as legacy:
            self.assertEqual(installer.main(['install', '--solver', 'dreal']), 0)
            self.assertEqual(installer.main(['check', '--solver', 'dreal']), 1)
        self.assertEqual(legacy.call_args_list,
                         [mock.call(['dreal']), mock.call(['dreal', '--check'])])
        build.assert_not_called()

    def test_dreal_rejects_yices_flags_local_source_and_combined_builds(self):
        invalid = [
            ['install', '--solver', 'dreal', '--build'],
            ['install', '--solver', 'dreal', '--experimental-build', '--build'],
            ['install', '--solver', 'dreal', '--experimental-build', '--thread-safe'],
            ['install', '--solver', 'dreal', '--experimental-build', '--without-mcsat'],
            ['install', '--solver', 'dreal', '--experimental-build', '--source', '/local/source'],
            ['install', '--solver', 'yices', '--experimental-build'],
            ['install', '--solver', 'z3', '--experimental-build'],
            ['install', '--all', '--experimental-build'],
            ['install', '--solver', 'dreal', 'yices', '--experimental-build'],
            ['install', '--solver', 'dreal', '--visualize', 'text', '--experimental-build'],
            ['check', '--solver', 'dreal', '--experimental-build'],
            ['install', '--solver', 'dreal', '--build', '--thread-safe'],
            ['install', '--solver', 'dreal', '--build', '--without-mcsat'],
            ['install', '--solver', 'dreal', '--build', '--source', '/local/source'],
            ['install', '--solver', 'dreal', '--jobs', '2'],
            ['install', '--solver', 'dreal', 'yices', '--build'],
            ['install', '--solver', 'dreal', '--visualize', 'text', '--build'],
            ['check', '--solver', 'dreal', '--build'],
            ['check', '--solver', 'dreal', '--thread-safe'],
        ]
        for arguments in invalid:
            with self.subTest(arguments=arguments), mock.patch.object(installer, 'build_dreal') as build, \
                    mock.patch.object(installer.solvers, 'main') as legacy, \
                    mock.patch('sys.stderr', new=io.StringIO()):
                with self.assertRaises(SystemExit) as failure:
                    installer.main(arguments)
                self.assertEqual(failure.exception.code, 2)
                build.assert_not_called()
                legacy.assert_not_called()

    def test_dreal_build_failure_is_a_clear_nonzero_result(self):
        with mock.patch.object(installer, 'build_dreal', side_effect=RuntimeError('previous installation remains active')), \
                mock.patch('sys.stderr', new=io.StringIO()) as output:
            self.assertEqual(installer.main(['install', '--solver', 'dreal', '--experimental-build']), 1)
        self.assertIn('previous installation remains active', output.getvalue())
        self.assertNotIn('Traceback', output.getvalue())

    def test_dreal_experimental_help_and_warning_are_explicit(self):
        help_text = installer.build_parser()._subparsers._group_actions[0].choices['install'].format_help()
        self.assertIn('--experimental-build', help_text)
        self.assertIn('ODE soundness is not certified', ' '.join(help_text.split()))
        with mock.patch.object(installer, 'build_dreal') as build, \
                mock.patch('sys.stderr', new=io.StringIO()) as output:
            self.assertEqual(installer.main(['install', '--solver', 'dreal', '--experimental-build']), 0)
        build.assert_called_once_with(prefix=None, jobs=1)
        self.assertIn('does not certify general ODE soundness', output.getvalue())

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


class DrealBuildTransactionTest(unittest.TestCase):
    def setUp(self):
        from contextlib import ExitStack
        temporary_root = Path(__file__).resolve().parent.parent / '.tmp'
        temporary_root.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='dreal-activation-', dir=temporary_root)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.active = self.root / 'data/dReal3/dReal'
        self.active.parent.mkdir(parents=True)
        self.active.write_bytes(b'previous-valid-solver')
        self.active.chmod(0o755)
        self.events = []
        self.builder = mock.Mock(side_effect=self.fake_build)
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        self.stack.enter_context(mock.patch.dict(sys.modules, {
            'stlmc.cli.dreal_build': SimpleNamespace(build_dreal=self.builder)}))
        self.stack.enter_context(mock.patch.object(installer, 'solver_data_dir', return_value=self.root / 'data'))
        self.stack.enter_context(mock.patch.object(installer.solvers, 'user_dreal_path', return_value=self.active))
        self.audit = self.stack.enter_context(mock.patch.object(installer, 'audit_static_linkage', side_effect=self.fake_audit))
        self.runtime = self.stack.enter_context(mock.patch.object(installer.solvers, 'validate_dreal_runtime', side_effect=self.fake_runtime))
        self.stack.enter_context(mock.patch('sys.stdout', new=io.StringIO()))

    def fake_build(self, destination, jobs):
        self.assertFalse(destination.exists())
        self.destination = destination
        (destination / 'bin').mkdir(parents=True)
        (destination / 'licenses').mkdir()
        (destination / 'licenses/NOTICE').write_text('private dependency licenses')
        (destination / 'build-manifest.json').write_text('{"source":"pinned"}')
        binary = destination / 'bin/dReal'
        binary.write_bytes(b'new-verified-static-solver')
        self.events.append('build')
        return binary

    def fake_audit(self, binary):
        self.assertEqual(self.active.read_bytes(), b'previous-valid-solver')
        self.assertEqual(binary.read_bytes(), b'new-verified-static-solver')
        self.events.append('audit')
        return {'policy': 'static-third-party-system-runtime-only'}

    def fake_runtime(self, binary):
        self.assertEqual(self.active.read_bytes(), b'previous-valid-solver')
        self.assertEqual(binary.read_bytes(), b'new-verified-static-solver')
        self.events.append('runtime')
        return {'version': 'dReal v3.16.12', 'ode_supported': True}

    def assert_previous_untouched(self):
        self.assertEqual(self.active.read_bytes(), b'previous-valid-solver')
        self.assertEqual(list(self.active.parent.glob('activate-dreal-*')), [])

    def test_only_audited_and_runtime_verified_bytes_are_activated(self):
        original_replace = installer.os.replace
        def activate(source, target):
            self.assertEqual(self.active.read_bytes(), b'previous-valid-solver')
            self.events.append('activate' if Path(target) == self.active else 'receipt')
            original_replace(source, target)
        with mock.patch.object(installer.os, 'replace', side_effect=activate):
            result = installer.build_dreal(jobs=2)
        self.assertEqual(self.events, ['build', 'audit', 'runtime', 'receipt', 'activate'])
        self.assertEqual(self.active.read_bytes(), b'new-verified-static-solver')
        self.assertEqual(result['executable'], str(self.active))
        self.assertEqual(result['build_jobs'], 2)
        self.assertTrue((self.destination / 'licenses/NOTICE').is_file())
        self.assertTrue((self.destination / 'build-manifest.json').is_file())
        self.assertEqual(list(self.active.parent.glob('activate-dreal-*')), [])
        # Activation is a copy, not a symlink into a disposable build tree.
        installer.shutil.rmtree(self.destination)
        self.assertEqual(self.active.read_bytes(), b'new-verified-static-solver')

    def test_custom_prefix_is_only_the_private_build_root(self):
        base = self.root / 'custom-builds'
        result = installer.build_dreal(prefix=base, jobs=3)
        self.assertIn(base, Path(result['prefix']).parents)
        self.assertEqual(result['executable'], str(self.active))
        self.assertEqual(self.builder.call_args.kwargs['jobs'], 3)

    def test_build_failure_preserves_previous_install(self):
        self.builder.side_effect = RuntimeError('compiler failed')
        with self.assertRaisesRegex(RuntimeError, 'previous installation remains active'):
            installer.build_dreal()
        self.audit.assert_not_called()
        self.runtime.assert_not_called()
        self.assert_previous_untouched()

    def test_linkage_failure_preserves_previous_install_and_cleans_staging(self):
        self.audit.side_effect = RuntimeError('unexpected shared GMP dependency')
        with self.assertRaisesRegex(RuntimeError, 'unexpected shared GMP'):
            installer.build_dreal()
        self.runtime.assert_not_called()
        self.assert_previous_untouched()

    def test_runtime_failure_preserves_previous_install_and_cleans_staging(self):
        from stlmc.exceptions import SolverUnavailableError
        self.runtime.side_effect = SolverUnavailableError('broken parameter invariant')
        with self.assertRaisesRegex(RuntimeError, 'broken parameter invariant'):
            installer.build_dreal()
        self.assert_previous_untouched()

    def test_failed_replace_preserves_previous_install_and_cleans_staging(self):
        with mock.patch.object(installer.os, 'replace', side_effect=PermissionError('activation denied')):
            with self.assertRaisesRegex(RuntimeError, 'activation denied'):
                installer.build_dreal()
        self.assert_previous_untouched()

    def test_out_of_prefix_builder_result_is_rejected(self):
        outside = self.root / 'unexpected-binary'
        outside.write_bytes(b'not-from-the-private-prefix')
        self.builder.side_effect = None
        self.builder.return_value = outside
        with self.assertRaisesRegex(RuntimeError, 'private bin/dReal'):
            installer.build_dreal()
        self.audit.assert_not_called()
        self.assert_previous_untouched()

    def test_broad_prefix_and_invalid_jobs_never_invoke_builder(self):
        repository = Path(__file__).resolve().parent.parent
        for prefix in (Path('/'), Path('/usr/local'), Path.home(), repository, repository.parent):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(RuntimeError, 'dedicated user-owned'):
                installer.build_dreal(prefix=prefix)
        with self.assertRaisesRegex(RuntimeError, '--jobs'):
            installer.build_dreal(jobs=0)
        self.builder.assert_not_called()
        self.assert_previous_untouched()


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

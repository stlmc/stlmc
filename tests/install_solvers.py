import os
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.cli import install_solvers
from stlmc.solver import availability


AVAILABLE = {
    "cvc5": (True, "ok"),
    "z3": (True, "ok"),
    "yices": (True, "ok"),
    "dreal": (True, "/solver/dReal"),
}
MISSING = {
    "cvc5": (False, "missing"),
    "z3": (False, "missing"),
    "yices": (False, "missing"),
    "dreal": (False, "missing"),
}


class InstallerCliTest(unittest.TestCase):
    def test_python_solver_version_mismatch_is_unavailable(self):
        with mock.patch.object(install_solvers.importlib, "import_module"), \
                mock.patch.object(install_solvers, "version", return_value="9.9"):
            available, detail = install_solvers._python_package_status(
                "cvc5", "cvc5", "cvc5==1.3.4", "available"
            )

        self.assertFalse(available)
        self.assertEqual(detail, "installed 9.9, expected 1.3.4")

    def test_help_explains_targets_locations_and_check_mode(self):
        help_text = install_solvers.build_parser().format_help()
        normalized_help = " ".join(help_text.split())

        for expected in (
            "CVC5, Z3, Yices, and dReal (default)",
            "without downloading or installing anything",
            "dReal lookup order",
            "Application Support/stlmc/solvers/dReal3/dReal",
            "XDG_DATA_HOME",
            "x86-64 Linux",
            "brew trust --formula sri-csl/sri-csl/yices2",
            "brew trust --formula sri-csl/sri-csl/libpoly",
            "brew trust --formula sri-csl/sri-csl/cudd",
            "entire SRI tap is not required",
            "DYLD_LIBRARY_PATH",
            "stlmc-installer install --solver dreal",
        ):
            with self.subTest(expected=expected):
                self.assertIn(expected, normalized_help)

    def test_check_reports_failure_without_installing(self):
        with mock.patch.object(sys, "argv", ["internal-solver-installer", "--check"]), \
                mock.patch.object(install_solvers, "_status", return_value=MISSING), \
                mock.patch.object(install_solvers, "_install_python_package") as pip, \
                mock.patch.object(install_solvers, "_install_yices") as yices, \
                mock.patch.object(install_solvers, "_install_dreal") as dreal:
            self.assertEqual(install_solvers.main(), 1)

        pip.assert_not_called()
        yices.assert_not_called()
        dreal.assert_not_called()

    def test_default_installs_every_missing_solver(self):
        with mock.patch.object(sys, "argv", ["internal-solver-installer"]), \
                mock.patch.object(
                    install_solvers, "_status", side_effect=[MISSING, AVAILABLE]
                ), \
                mock.patch.object(install_solvers, "_install_python_package") as pip, \
                mock.patch.object(install_solvers, "_install_yices") as yices, \
                mock.patch.object(install_solvers, "_install_dreal") as dreal:
            self.assertEqual(install_solvers.main(), 0)

        self.assertEqual(
            pip.call_args_list,
            [mock.call("cvc5==1.3.4"), mock.call("z3-solver==4.15.4.0"),
             mock.call("yices==1.1.6")],
        )
        yices.assert_called_once_with()
        dreal.assert_called_once_with()

    def test_individual_selection_only_installs_requested_solver(self):
        with mock.patch.object(
                sys, "argv", ["internal-solver-installer", "dreal"]
             ), mock.patch.object(
                install_solvers, "_status", side_effect=[MISSING, AVAILABLE]
             ), mock.patch.object(
                install_solvers, "_install_python_package"
             ) as pip, mock.patch.object(
                install_solvers, "_install_yices"
             ) as yices, mock.patch.object(
                install_solvers, "_install_dreal"
             ) as dreal:
            self.assertEqual(install_solvers.main(), 0)

        pip.assert_not_called()
        yices.assert_not_called()
        dreal.assert_called_once_with()

    def test_macos_yices_uses_official_homebrew_tap(self):
        with mock.patch.object(install_solvers.sys, "platform", "darwin"), \
                mock.patch.object(install_solvers.shutil, "which", return_value="/brew"), \
                mock.patch.object(install_solvers, "_run") as run:
            install_solvers._install_yices()

        run.assert_called_once_with(
            ["brew", "install", "SRI-CSL/sri-csl/yices2"]
        )

    def test_linux_yices_installs_cli_and_native_library(self):
        with mock.patch.object(install_solvers.sys, "platform", "linux"), \
                mock.patch.object(
                    install_solvers.shutil, "which", return_value="/usr/bin/apt-get"
                ), mock.patch.object(install_solvers, "_run") as run:
            install_solvers._install_yices()

        self.assertEqual(
            run.call_args_list,
            [
                mock.call(
                    ["sudo", "add-apt-repository", "-y", "ppa:sri-csl/formal-methods"]
                ),
                mock.call(["sudo", "apt-get", "update"]),
                mock.call(
                    ["sudo", "apt-get", "install", "-y", "yices2", "yices2-dev"]
                ),
                mock.call(["sudo", "ldconfig"]),
            ],
        )

    def test_dreal_archive_is_installed_as_an_executable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            destination = root / "solvers" / "dReal3" / "dReal"
            archive_source = root / "dreal.zip"
            member = "dReal-3.16.06.02-darwin/bin/dReal"
            with zipfile.ZipFile(str(archive_source), "w") as archive:
                archive.writestr(member, b"#!/bin/sh\nexit 0\n")

            def copy_archive(_url, output):
                shutil.copyfile(str(archive_source), output)

            with mock.patch.object(install_solvers.sys, "platform", "darwin"), \
                    mock.patch.object(
                        install_solvers, "user_dreal_path", return_value=destination
                    ), mock.patch.object(
                        install_solvers.urllib.request,
                        "urlretrieve",
                        side_effect=copy_archive,
                    ), mock.patch.object(install_solvers, "_verify_dreal_archive"), \
                    mock.patch.object(install_solvers, "_dreal_status", return_value=(True, "validated")):
                install_solvers._install_dreal()

            self.assertEqual(destination.read_bytes(), b"#!/bin/sh\nexit 0\n")
            self.assertTrue(os.access(str(destination), os.X_OK))


class NativeVersionCheckTest(unittest.TestCase):
    def test_three_component_dreal_version_is_reported_as_mismatch(self):
        with mock.patch.object(install_solvers.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 0, "dReal v3.16.12 (commit 6fa469fb1f84)\n", "")) as run:
            available, detail = install_solvers._dreal_status("/test/dReal")
        self.assertFalse(available)
        self.assertIn("version 3.16.12, expected 3.16.06.02", detail)
        run.assert_called_once()

    def test_yices_native_version_mismatch_is_reported(self):
        binding = mock.Mock()
        binding.Yices.version = "2.6.5"
        with mock.patch.object(install_solvers, "load_yices_binding", return_value=binding), \
                mock.patch.object(install_solvers, "_python_package_status", return_value=(True, "binding ok")):
            available, detail = install_solvers._probe_one("yices")
        self.assertFalse(available)
        self.assertIn("2.6.5, expected 2.7.0", detail)
        self.assertIn("not automatically downgraded", detail)
        self.assertIn("install --solver yices --build", detail)

    def test_dreal_probe_checks_version_then_sat_query_with_timeouts(self):
        results = [subprocess.CompletedProcess([], 0, "dReal v3.16.06.02 (commit abc)\n", ""),
                   subprocess.CompletedProcess([], 0, "delta-sat\n", ""),
                   subprocess.CompletedProcess([], 0, "delta-sat\n", ""),
                   subprocess.CompletedProcess([], 0, "unsat\n", "")]
        with mock.patch.object(install_solvers.subprocess, "run", side_effect=results) as run:
            available, detail = install_solvers._dreal_status("/solver/dReal")
        self.assertTrue(available, detail)
        self.assertEqual(run.call_count, 4)
        self.assertEqual(run.call_args_list[0].args[0], ["/solver/dReal", "--version"])
        for call in run.call_args_list:
            self.assertGreater(call.kwargs["timeout"], 0)
            self.assertLessEqual(call.kwargs["timeout"], 10)

    def test_dreal_wrong_version_is_rejected_before_smoke(self):
        with mock.patch.object(install_solvers.subprocess, "run", return_value=
                               subprocess.CompletedProcess([], 0, "dReal v4.21.06.2", "")) as run:
            available, detail = install_solvers._dreal_status("/solver/dReal")
        self.assertFalse(available)
        self.assertIn("expected 3.16.06.02", detail)
        run.assert_called_once()

    def test_dreal_rejects_broken_ode_or_interior_forall(self):
        version_result = subprocess.CompletedProcess([], 0, "dReal v3.16.06.02", "")
        sat = subprocess.CompletedProcess([], 0, "delta-sat\n", "")
        unsat = subprocess.CompletedProcess([], 0, "unsat\n", "")
        for replies, label in (([version_result, sat, unsat], "ODE SAT"),
                               ([version_result, sat, sat, sat], "ODE interior UNSAT")):
            with self.subTest(label=label), mock.patch.object(
                    install_solvers.subprocess, "run", side_effect=replies):
                available, detail = install_solvers._dreal_status("/solver/dReal")
                self.assertFalse(available)
                self.assertIn(label, detail)

    def test_dreal_hanging_or_wrong_smoke_result_is_rejected(self):
        version_result = subprocess.CompletedProcess([], 0, "dReal v3.16.06.02", "")
        for result in (subprocess.TimeoutExpired("dReal", 10),
                       subprocess.CompletedProcess([], 0, "unsat\n", ""),
                       subprocess.CompletedProcess([], -11, "", "crashed")):
            with self.subTest(result=result), mock.patch.object(
                    install_solvers.subprocess, "run", side_effect=[version_result, result]):
                self.assertFalse(install_solvers._dreal_status("/solver/dReal")[0])

    def test_failed_dreal_validation_preserves_previous_install(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            destination = root / "installed" / "dReal"
            destination.parent.mkdir()
            destination.write_bytes(b"previous")
            archive_source = root / "dreal.zip"
            with zipfile.ZipFile(str(archive_source), "w") as archive:
                archive.writestr("dReal-3.16.06.02-darwin/bin/dReal", b"invalid")
            with mock.patch.object(install_solvers.sys, "platform", "darwin"), \
                    mock.patch.object(install_solvers, "user_dreal_path", return_value=destination), \
                    mock.patch.object(install_solvers.urllib.request, "urlretrieve",
                                      side_effect=lambda _url, output: shutil.copyfile(str(archive_source), output)), \
                    mock.patch.object(install_solvers, "_verify_dreal_archive"), \
                    mock.patch.object(install_solvers, "_dreal_status", return_value=(False, "bad version")):
                with self.assertRaisesRegex(RuntimeError, "failed validation"):
                    install_solvers._install_dreal()
            self.assertEqual(destination.read_bytes(), b"previous")

    def test_dreal_archive_checksum_mismatch_rejects_changed_download(self):
        import hashlib
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / "fixture.zip"
            archive.write_bytes(b"expected release bytes")
            expected = hashlib.sha256(archive.read_bytes()).hexdigest()
            with mock.patch.dict(install_solvers.DREAL_ARCHIVE_SHA256, {"fixture.zip": expected}):
                install_solvers._verify_dreal_archive(archive, "fixture.zip")
                archive.write_bytes(b"changed download")
                with self.assertRaisesRegex(RuntimeError, "SHA256 mismatch"):
                    install_solvers._verify_dreal_archive(archive, "fixture.zip")

    def test_dreal_changed_download_never_replaces_previous_install(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "dReal"
            destination.write_bytes(b"previous")
            def changed_download(_url, output):
                Path(output).write_bytes(b"not the pinned archive")
            with mock.patch.object(install_solvers.sys, "platform", "darwin"), \
                    mock.patch.object(install_solvers, "user_dreal_path", return_value=destination), \
                    mock.patch.object(install_solvers.urllib.request, "urlretrieve", side_effect=changed_download), \
                    mock.patch.object(install_solvers, "_dreal_status") as probe:
                with self.assertRaisesRegex(RuntimeError, "SHA256 mismatch"):
                    install_solvers._install_dreal()
            probe.assert_not_called()
            self.assertEqual(destination.read_bytes(), b"previous")


class DRealDiscoveryTest(unittest.TestCase):
    def test_path_executable_is_used_without_managed_install(self):
        with mock.patch.object(
                availability.shutil, "which", return_value="/path/dReal"
             ), mock.patch.object(
                availability, "user_dreal_path", return_value=Path("/nonexistent/stlmc/dReal")
             ):
            self.assertEqual(availability.find_dreal(), "/path/dReal")

    def test_managed_installation_prevents_path_shadowing(self):
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / "dReal"
            executable.touch()
            executable.chmod(0o755)
            with mock.patch.object(availability.shutil, "which", return_value="/old/dReal"), \
                    mock.patch.object(availability, "user_dreal_path", return_value=executable):
                self.assertEqual(availability.find_dreal(), str(executable))

    def test_user_installation_is_used_as_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / "dReal"
            executable.write_text("#!/bin/sh\n", encoding="utf-8")
            executable.chmod(0o755)
            with mock.patch.object(availability.shutil, "which", return_value=None), \
                    mock.patch.object(
                        availability, "user_dreal_path", return_value=executable
                    ):
                self.assertEqual(availability.find_dreal(), str(executable))

    def test_linux_user_directory_honors_xdg_data_home(self):
        with mock.patch.object(availability.sys, "platform", "linux"), \
                mock.patch.dict(
                    availability.os.environ,
                    {"XDG_DATA_HOME": "/xdg/data"},
                    clear=False,
                ):
            self.assertEqual(
                availability.user_dreal_path(),
                Path("/xdg/data/stlmc/solvers/dReal3/dReal"),
            )


if __name__ == "__main__":
    unittest.main()

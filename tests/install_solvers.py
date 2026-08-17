import os
import shutil
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
    "z3": (True, "ok"),
    "yices": (True, "ok"),
    "dreal": (True, "/solver/dReal"),
}
MISSING = {
    "z3": (False, "missing"),
    "yices": (False, "missing"),
    "dreal": (False, "missing"),
}


class InstallerCliTest(unittest.TestCase):
    def test_help_explains_targets_locations_and_check_mode(self):
        help_text = install_solvers.build_parser().format_help()
        normalized_help = " ".join(help_text.split())

        for expected in (
            "Z3, Yices, and dReal (default)",
            "without downloading or installing anything",
            "dReal lookup order",
            "Application Support/stlmc/solvers/dReal3/dReal",
            "XDG_DATA_HOME",
            "x86-64 Linux",
            "stlmc-install-solvers dreal",
        ):
            with self.subTest(expected=expected):
                self.assertIn(expected, normalized_help)

    def test_check_reports_failure_without_installing(self):
        with mock.patch.object(sys, "argv", ["stlmc-install-solvers", "--check"]), \
                mock.patch.object(install_solvers, "_status", return_value=MISSING), \
                mock.patch.object(install_solvers, "_install_python_package") as pip, \
                mock.patch.object(install_solvers, "_install_yices") as yices, \
                mock.patch.object(install_solvers, "_install_dreal") as dreal:
            self.assertEqual(install_solvers.main(), 1)

        pip.assert_not_called()
        yices.assert_not_called()
        dreal.assert_not_called()

    def test_default_installs_every_missing_solver(self):
        with mock.patch.object(sys, "argv", ["stlmc-install-solvers"]), \
                mock.patch.object(
                    install_solvers, "_status", side_effect=[MISSING, AVAILABLE]
                ), \
                mock.patch.object(install_solvers, "_install_python_package") as pip, \
                mock.patch.object(install_solvers, "_install_yices") as yices, \
                mock.patch.object(install_solvers, "_install_dreal") as dreal:
            self.assertEqual(install_solvers.main(), 0)

        self.assertEqual(
            pip.call_args_list,
            [mock.call("z3-solver"), mock.call("yices")],
        )
        yices.assert_called_once_with()
        dreal.assert_called_once_with()

    def test_individual_selection_only_installs_requested_solver(self):
        with mock.patch.object(
                sys, "argv", ["stlmc-install-solvers", "dreal"]
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
                    ):
                install_solvers._install_dreal()

            self.assertEqual(destination.read_bytes(), b"#!/bin/sh\nexit 0\n")
            self.assertTrue(os.access(str(destination), os.X_OK))


class DRealDiscoveryTest(unittest.TestCase):
    def test_path_executable_has_priority(self):
        with mock.patch.object(
                availability.shutil, "which", return_value="/path/dReal"
             ), mock.patch.object(
                availability, "user_dreal_path", return_value=Path("/user/dReal")
             ):
            self.assertEqual(availability.find_dreal(), "/path/dReal")

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

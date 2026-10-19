import os
import io
import shutil
import subprocess
import sys
import tempfile
import tarfile
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
    def setUp(self):
        patch = mock.patch.object(install_solvers.platform, "machine", return_value="x86_64")
        patch.start()
        self.addCleanup(patch.stop)

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
            "SHA256-pinned official 2.7.0 archives",
            "macOS Intel 12+",
            "Apple Silicon 15+",
            "native CUDD dependencies",
            "No system package manager or administrator privileges",
            "stlmc-installer install --solver dreal",
            "stlmc-installer install --solver dreal --experimental-build --jobs 2",
        ):
            with self.subTest(expected=expected):
                self.assertIn(expected, normalized_help)
        self.assertNotIn("brew trust", normalized_help)
        self.assertNotIn("through apt", normalized_help)

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
                mock.patch.object(install_solvers, "find_dreal", return_value=None), \
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
             ) as pip, mock.patch.object(install_solvers, "find_dreal", return_value=None), mock.patch.object(
                install_solvers, "_install_yices"
             ) as yices, mock.patch.object(
                install_solvers, "_install_dreal"
             ) as dreal:
            self.assertEqual(install_solvers.main(), 0)

        pip.assert_not_called()
        yices.assert_not_called()
        dreal.assert_called_once_with()

    def test_macos_yices_uses_managed_official_release(self):
        with mock.patch.object(install_solvers.sys, "platform", "darwin"), \
                mock.patch('stlmc.cli.installer.install_official_yices') as install, \
                mock.patch.object(install_solvers, "_run") as run:
            install_solvers._install_yices()
        install.assert_called_once_with()
        run.assert_not_called()

    def test_linux_yices_installs_cli_and_native_library(self):
        with mock.patch.object(install_solvers.sys, "platform", "linux"), \
                mock.patch('stlmc.cli.installer.install_official_yices') as install, \
                mock.patch.object(install_solvers, "_run") as run:
            install_solvers._install_yices()
        install.assert_called_once_with()
        run.assert_not_called()

    def test_official_archive_is_installed_with_warning_and_executable_mode(self):
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
                    mock.patch.object(install_solvers, "_dreal_install_status", return_value=(True, "validated")), \
                    mock.patch.object(install_solvers.sys, "stderr", new_callable=io.StringIO) as warning:
                self.assertEqual(install_solvers._install_dreal(), destination)
                self.assertEqual(destination.read_bytes(), b"#!/bin/sh\nexit 0\n")
                self.assertTrue(destination.stat().st_mode & 0o111)
                self.assertIn("known correctness limitations", warning.getvalue())


    def test_failed_download_preserves_a_preexisting_executable(self):
        scratch = PROJECT_ROOT / '.tmp'
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='disabled-dreal-', dir=scratch) as directory:
            active = Path(directory) / 'dReal'
            active.write_bytes(b'previous-compatible-solver')
            active.chmod(0o755)
            with mock.patch.object(install_solvers, 'user_dreal_path', return_value=active), \
                    mock.patch.object(install_solvers.urllib.request, 'urlretrieve', side_effect=OSError('network failed')) as download, \
                    mock.patch.object(install_solvers, '_run') as install:
                with self.assertRaisesRegex(OSError, 'network failed'):
                    install_solvers._install_dreal()
            self.assertEqual(active.read_bytes(), b'previous-compatible-solver')
            download.assert_called_once()
            install.assert_not_called()


class NativeVersionCheckTest(unittest.TestCase):
    def setUp(self):
        patch = mock.patch.object(install_solvers.platform, "machine", return_value="x86_64")
        patch.start()
        self.addCleanup(patch.stop)

    def test_recognized_official_limitations_are_allowed_without_claiming_invariant_pass(self):
        replies=[subprocess.CompletedProcess([],0,text,'') for text in
                 ('dReal v3.16.06.02\n','sat\n','delta-sat\n','unsat\n')]
        metadata={'zero_derivative_forall':False,'known_limitations':['zero-derivative invariant omitted']}
        with mock.patch.object(install_solvers.subprocess,'run',side_effect=replies), \
                mock.patch.object(install_solvers,'validate_dreal_runtime',return_value=metadata):
            available,detail=install_solvers._dreal_status('/official/dReal')
        self.assertTrue(available)
        self.assertIn('official dReal 3.16.06.02',detail)
        self.assertIn('feature checks only',detail)
        self.assertIn('invariant check FAILED',detail)
        self.assertIn('#325',detail)
        self.assertNotIn('parameter checks passed',detail)
        self.assertNotIn('compatible external build',detail)

    def test_nonofficial_or_unrecognized_failed_capability_is_not_silently_allowed(self):
        for version,metadata in (
                ('3.16.12',{'zero_derivative_forall':False,'known_limitations':['failure']}),
                ('3.16.06.02',{'zero_derivative_forall':False})):
            replies=[subprocess.CompletedProcess([],0,text,'') for text in
                     ('dReal v'+version+'\n','sat\n','delta-sat\n','unsat\n')]
            with self.subTest(version=version,metadata=metadata), \
                    mock.patch.object(install_solvers.subprocess,'run',side_effect=replies), \
                    mock.patch.object(install_solvers,'validate_dreal_runtime',return_value=metadata):
                self.assertFalse(install_solvers._dreal_status('/test/dReal')[0])

    def test_old_version_label_does_not_override_failed_parameter_check(self):
        from stlmc.exceptions import SolverUnavailableError
        replies=[subprocess.CompletedProcess([],0,text,'') for text in
                 ('dReal v3.16.06.02\n','sat\n','delta-sat\n','unsat\n')]
        with mock.patch.object(install_solvers.subprocess,'run',side_effect=replies), \
                mock.patch.object(install_solvers,'validate_dreal_runtime',
                                  side_effect=SolverUnavailableError('zero-derivative parameter invariant failed')):
            available,detail=install_solvers._dreal_status('/test/dReal')
        self.assertFalse(available)
        self.assertIn('zero-derivative parameter invariant failed',detail)

    def test_wrong_archive_structure_preserves_file_without_replace(self):
        with tempfile.TemporaryDirectory() as directory:
            existing=Path(directory)/'dReal'
            existing.write_bytes(b'preserve this executable')
            with mock.patch.object(install_solvers,'user_dreal_path',return_value=existing), \
                    mock.patch.object(install_solvers.urllib.request,'urlretrieve', side_effect=OSError('download failed')) as download, \
                    mock.patch.object(install_solvers.os,'replace') as replace:
                with self.assertRaisesRegex(OSError,'download failed'):
                    install_solvers._install_dreal()
            download.assert_called_once()
            replace.assert_not_called()
            self.assertEqual(existing.read_bytes(),b'preserve this executable')

    def test_external_dreal_three_component_version_is_checked_by_capability(self):
        replies=[subprocess.CompletedProcess([],0,text,'') for text in
                 ('dReal v3.16.12 (commit 6fa469fb1f84)\n','sat\n','delta-sat\n','unsat\n')]
        with mock.patch.object(install_solvers.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 0, "unused", ""),side_effect=replies) as run, \
                mock.patch.object(install_solvers,'validate_dreal_runtime',return_value={'version':'3.16.12'}) as validate:
            available, detail = install_solvers._dreal_status("/test/dReal")
        self.assertTrue(available,detail)
        self.assertIn('compatible external build; not a verified managed release',detail)
        self.assertEqual(run.call_count,4)
        validate.assert_called_once_with('/test/dReal')

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
        with mock.patch.object(install_solvers.subprocess, "run", side_effect=results) as run, \
                mock.patch.object(install_solvers,'validate_dreal_runtime',return_value={'version':'3.16.06.02'}):
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
        self.assertIn("expected dReal 3", detail)
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
                    mock.patch.object(install_solvers, "_dreal_install_status", return_value=(False, "bad version")):
                with self.assertRaisesRegex(RuntimeError, "installation validation failed"):
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
                    mock.patch.object(install_solvers, "_dreal_install_status") as probe:
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


class OfficialReleaseInstallationTest(unittest.TestCase):
    def test_install_probe_does_not_call_strict_runtime_guard(self):
        replies=[subprocess.CompletedProcess([],0,text,'') for text in
                 ('dReal v3.16.06.02 (commit d6645637507b)\n','delta-sat\n')]
        with mock.patch.object(install_solvers.subprocess,'run',side_effect=replies), \
                mock.patch.object(install_solvers,'validate_dreal_runtime') as strict:
            available,detail=install_solvers._dreal_install_status('/test/dReal')
        self.assertTrue(available)
        self.assertIn('NOT an ODE correctness approval',detail)
        self.assertIn('#325',detail)
        strict.assert_not_called()

    def test_install_probe_requires_exact_version_and_sat(self):
        for replies in (
                [('dReal v3.16.12\n',0)],
                [('dReal v3.16.06.02\n',0),('unsat\n',0)],
                [('dReal v3.16.06.02\n',0),('delta-sat\n',1)]):
            with self.subTest(replies=replies), mock.patch.object(
                    install_solvers.subprocess,'run',side_effect=[
                        subprocess.CompletedProcess([],code,text,'') for text,code in replies]):
                self.assertFalse(install_solvers._dreal_install_status('/test/dReal')[0])

    def test_already_installed_official_release_is_not_downloaded_again(self):
        detail='Warning: known correctness limitations'
        with mock.patch.object(install_solvers,'_status',return_value=MISSING), \
                mock.patch.object(install_solvers,'find_dreal',return_value='/official/dReal'), \
                mock.patch.object(install_solvers,'_dreal_install_status',return_value=(True,detail)), \
                mock.patch.object(install_solvers,'_install_dreal') as download, \
                mock.patch('sys.stdout',new_callable=io.StringIO) as output:
            self.assertEqual(install_solvers.main(['dreal']),0)
        download.assert_not_called()
        self.assertIn(detail,output.getvalue())

    def test_new_install_success_is_not_overridden_by_strict_failure(self):
        with mock.patch.object(install_solvers,'_status',return_value=MISSING), \
                mock.patch.object(install_solvers,'find_dreal',return_value=None), \
                mock.patch.object(install_solvers,'_install_dreal',return_value=Path('/new/dReal')), \
                mock.patch.object(install_solvers,'_dreal_install_status',return_value=(True,'known limitations')):
            self.assertEqual(install_solvers.main(['dreal']),0)

    def test_compatible_external_build_is_not_downgraded(self):
        with mock.patch.object(install_solvers,'_status',return_value=AVAILABLE), \
                mock.patch.object(install_solvers,'_install_dreal') as download, \
                mock.patch.object(install_solvers,'_dreal_install_status') as basic:
            self.assertEqual(install_solvers.main(['dreal']),0)
        download.assert_not_called()
        basic.assert_not_called()

    def test_check_stays_strict_and_never_calls_installation_probe(self):
        with mock.patch.object(install_solvers,'_status',return_value=MISSING), \
                mock.patch.object(install_solvers,'_install_dreal') as download, \
                mock.patch.object(install_solvers,'_dreal_install_status') as basic:
            self.assertEqual(install_solvers.main(['dreal','--check']),1)
        download.assert_not_called()
        basic.assert_not_called()

    def test_linux_exact_member_is_used_without_extracting_other_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            archive_path=root/'fixture.tar.gz'
            with tarfile.open(archive_path,'w:gz') as tar:
                for name,payload in [('dReal-3.16.06.02-linux/bin/dReal',b'official'),('../escape',b'unsafe')]:
                    member=tarfile.TarInfo(name)
                    member.size=len(payload)
                    tar.addfile(member,io.BytesIO(payload))
            active=root/'target'/'dReal'
            with mock.patch.object(install_solvers.sys,'platform','linux'), \
                    mock.patch.object(install_solvers.platform,'machine',return_value='x86_64'), \
                    mock.patch.object(install_solvers,'user_dreal_path',return_value=active), \
                    mock.patch.object(install_solvers.urllib.request,'urlretrieve',side_effect=lambda url,out:shutil.copyfile(archive_path,out)) as download, \
                    mock.patch.object(install_solvers,'_verify_dreal_archive'), \
                    mock.patch.object(install_solvers,'_dreal_install_status',return_value=(True,'ok')):
                install_solvers._install_dreal()
            self.assertEqual(active.read_bytes(),b'official')
            self.assertFalse((root/'escape').exists())
            self.assertEqual(download.call_args.args[0],'https://github.com/dreal/dreal3/releases/download/v3.16.06.02/dReal-3.16.06.02-linux.tar.gz')

    def test_symlink_or_duplicate_member_is_rejected_without_replacement(self):
        for duplicate in (False,True):
            with self.subTest(duplicate=duplicate), tempfile.TemporaryDirectory() as directory:
                root=Path(directory)
                archive_path=root/'fixture.tar.gz'
                with tarfile.open(archive_path,'w:gz') as tar:
                    for _ in range(2 if duplicate else 1):
                        member=tarfile.TarInfo('dReal-3.16.06.02-linux/bin/dReal')
                        if not duplicate:
                            member.type=tarfile.SYMTYPE
                            member.linkname='/other/dReal'
                        tar.addfile(member)
                active=root/'dReal'
                active.write_bytes(b'previous')
                with mock.patch.object(install_solvers.sys,'platform','linux'), \
                        mock.patch.object(install_solvers.platform,'machine',return_value='x86_64'), \
                        mock.patch.object(install_solvers,'user_dreal_path',return_value=active), \
                        mock.patch.object(install_solvers.urllib.request,'urlretrieve',side_effect=lambda url,out:shutil.copyfile(archive_path,out)), \
                        mock.patch.object(install_solvers,'_verify_dreal_archive'):
                    with self.assertRaisesRegex(RuntimeError,'unique regular executable'):
                        install_solvers._install_dreal()
                self.assertEqual(active.read_bytes(),b'previous')

    def test_unsupported_platform_fails_before_download(self):
        with mock.patch.object(install_solvers.sys,'platform','linux'), \
                mock.patch.object(install_solvers.platform,'machine',return_value='arm64'), \
                mock.patch.object(install_solvers.urllib.request,'urlretrieve') as download:
            with self.assertRaisesRegex(RuntimeError,'x86-64'):
                install_solvers._install_dreal()
        download.assert_not_called()

    def test_macos_arm_uses_intel_release_only_when_rosetta_is_available(self):
        for machine in ('arm64','aarch64'):
            with self.subTest(machine=machine), tempfile.TemporaryDirectory() as directory:
                root=Path(directory)
                archive_path=root/'fixture.zip'
                with zipfile.ZipFile(archive_path,'w') as archive:
                    archive.writestr('dReal-3.16.06.02-darwin/bin/dReal',b'intel binary')
                target=root/'active'/'dReal'
                with mock.patch.object(install_solvers.sys,'platform','darwin'), \
                        mock.patch.object(install_solvers.platform,'machine',return_value=machine), \
                        mock.patch.object(install_solvers.subprocess,'run',return_value=subprocess.CompletedProcess([],0,'','')) as run, \
                        mock.patch.object(install_solvers,'user_dreal_path',return_value=target), \
                        mock.patch.object(install_solvers.urllib.request,'urlretrieve',side_effect=lambda url,out:shutil.copyfile(archive_path,out)), \
                        mock.patch.object(install_solvers,'_verify_dreal_archive'), \
                        mock.patch.object(install_solvers,'_dreal_install_status',return_value=(True,'ok')):
                    self.assertEqual(install_solvers._install_dreal(),target)
                self.assertEqual(target.read_bytes(),b'intel binary')
                run.assert_called_once_with(['/usr/bin/arch','-x86_64','/usr/bin/true'],capture_output=True,text=True,timeout=5)

    def test_macos_arm_missing_rosetta_stops_before_download_or_target_creation(self):
        for response in (subprocess.CompletedProcess([],1,'','unavailable'),
                         OSError('missing arch'),subprocess.TimeoutExpired('arch',5)):
            with self.subTest(response=response), \
                    mock.patch.object(install_solvers.sys,'platform','darwin'), \
                    mock.patch.object(install_solvers.platform,'machine',return_value='arm64'), \
                    mock.patch.object(install_solvers.subprocess,'run',side_effect=response if isinstance(response,Exception) else None,return_value=response), \
                    mock.patch.object(install_solvers.urllib.request,'urlretrieve') as download, \
                    mock.patch.object(install_solvers,'user_dreal_path') as target:
                with self.assertRaisesRegex(RuntimeError,'requires Rosetta.*No OS software'):
                    install_solvers._install_dreal()
            download.assert_not_called()
            target.assert_not_called()


if __name__ == "__main__":
    unittest.main()

"""Mocked installer source-build contracts; no downloads or real builds."""

import hashlib
import io
import json
import os
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from stlmc.cli import dreal_build as builder


class DrealBuildTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="stlmc-build-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def archive(self, entries):
        target = self.root / "source.tar.gz"
        with tarfile.open(target, "w:gz") as tar:
            for name, value in entries:
                info = tarfile.TarInfo(name)
                if isinstance(value, tuple):
                    info.type = tarfile.SYMTYPE
                    info.linkname = value[0]
                    tar.addfile(info)
                else:
                    info.size = len(value)
                    tar.addfile(info, io.BytesIO(value))
        return target

    def test_existing_prefix_is_never_modified(self):
        destination = self.root / "existing"
        destination.mkdir()
        sentinel = destination / "old"
        sentinel.write_text("keep")
        with mock.patch.object(builder, "_prerequisites") as check:
            with self.assertRaisesRegex(RuntimeError, "already exists"):
                builder.build_dreal(destination)
        check.assert_not_called()
        self.assertEqual(sentinel.read_text(), "keep")

    def test_unverified_platform_fails_closed(self):
        with mock.patch.object(builder.platform, "system", return_value="Darwin"):
            with self.assertRaisesRegex(RuntimeError, "Linux x86-64"):
                builder._prerequisites(4)

    def test_missing_build_tool_is_actionable_without_installing(self):
        with mock.patch.object(builder.platform, "system", return_value="Linux"), \
                mock.patch.object(builder.platform, "machine", return_value="x86_64"), \
                mock.patch.object(builder.shutil, "which", side_effect=lambda n: None if n == "libtoolize" else "/tools/" + n):
            with self.assertRaisesRegex(RuntimeError, "libtoolize.*no system packages"):
                builder._prerequisites(4)

    def test_jobs_are_positive_not_arbitrarily_capped(self):
        with mock.patch.object(builder.platform, "system", return_value="Linux"), \
                mock.patch.object(builder.platform, "machine", return_value="x86_64"), \
                mock.patch.object(builder.shutil, "which", side_effect=lambda n: "/tools/" + n):
            self.assertEqual(builder._prerequisites(32)[0], 32)
            for value in [0, -1, True, "4"]:
                with self.subTest(value=value), self.assertRaises(ValueError):
                    builder._prerequisites(value)

    def test_host_cmake_is_not_a_prerequisite(self):
        with mock.patch.object(builder.platform, "system", return_value="Linux"), \
                mock.patch.object(builder.platform, "machine", return_value="x86_64"), \
                mock.patch.object(builder.shutil, "which", side_effect=lambda n: None if n == "cmake" else "/tools/" + n):
            self.assertNotIn("cmake", builder._prerequisites(1)[1])

    def test_private_cmake_uses_own_python_and_native_wheel_binary(self):
        binary = self.root / "tool-env/lib/python3.10/site-packages/cmake/data/bin/cmake"
        binary.parent.mkdir(parents=True)
        binary.write_bytes(b"private cmake")
        with mock.patch.object(builder.venv, "EnvBuilder") as environment, \
                mock.patch.object(builder, "_run") as install, \
                mock.patch.object(builder.subprocess, "run", return_value=mock.Mock(stdout="cmake version 3.29.6\n\nCMake suite")) as version:
            executable, metadata = builder._prepare_cmake(self.root, {}, self.root / "build.log")
        environment.assert_called_once_with(with_pip=True)
        environment.return_value.create.assert_called_once_with(str(self.root / "tool-env"))
        command = install.call_args.args[0]
        self.assertEqual(command[:3], [self.root / "tool-env/bin/python", "-m", "pip"])
        for value in ("--isolated", "--require-virtualenv", "--no-cache-dir",
                      "--only-binary=:all:", "--no-deps", "cmake==3.29.6"):
            self.assertIn(value, command)
        self.assertEqual(executable, binary.resolve())
        self.assertEqual(version.call_args.args[0], [str(binary.resolve()), "--version"])
        self.assertEqual(metadata["executable_sha256"], hashlib.sha256(b"private cmake").hexdigest())

    def test_private_cmake_version_mismatch_and_missing_binary_are_rejected(self):
        with mock.patch.object(builder.venv, "EnvBuilder"), mock.patch.object(builder, "_run"):
            with self.assertRaisesRegex(RuntimeError, "native executable"):
                builder._prepare_cmake(self.root, {}, self.root / "build.log")
            binary = self.root / "tool-env/lib/python3.10/site-packages/cmake/data/bin/cmake"
            binary.parent.mkdir(parents=True)
            binary.write_bytes(b"wrong")
            with mock.patch.object(builder.subprocess, "run", return_value=mock.Mock(stdout="cmake version 4.0.0\n")):
                with self.assertRaisesRegex(RuntimeError, "does not match"):
                    builder._prepare_cmake(self.root, {}, self.root / "build.log")

    def test_private_cmake_install_failure_propagates_without_system_fallback(self):
        with mock.patch.object(builder.venv, "EnvBuilder"), \
                mock.patch.object(builder, "_run", side_effect=RuntimeError("wheel unavailable")), \
                mock.patch.object(builder.subprocess, "run") as version:
            with self.assertRaisesRegex(RuntimeError, "wheel unavailable"):
                builder._prepare_cmake(self.root, {}, self.root / "build.log")
        version.assert_not_called()

    def test_safe_internal_symlink_is_materialized(self):
        archive = self.archive([("source/README", b"read me"), ("source/doc/readme", ("../README",))])
        result = builder._unpack(archive, self.root / "unpacked")
        self.assertEqual((result / "doc/readme").read_bytes(), b"read me")
        self.assertFalse((result / "doc/readme").is_symlink())

    def test_parent_traversal_is_rejected(self):
        archive = self.archive([("../escape", b"bad")])
        with self.assertRaisesRegex(RuntimeError, "unsafe"):
            builder._unpack(archive, self.root / "unpacked")
        self.assertFalse((self.root / "escape").exists())

    def test_escaping_symlink_is_rejected(self):
        archive = self.archive([("source/file", b"ok"), ("source/link", ("../../escape",))])
        with self.assertRaisesRegex(RuntimeError, "escapes"):
            builder._unpack(archive, self.root / "unpacked")

    def test_multiple_archive_roots_are_rejected(self):
        archive = self.archive([("one/file", b"a"), ("two/file", b"b")])
        with self.assertRaisesRegex(RuntimeError, "single source"):
            builder._unpack(archive, self.root / "unpacked")

    def test_cached_source_is_still_hashed(self):
        cache = self.root / "cache"
        cache.mkdir()
        (cache / "input.tar.gz").write_bytes(b"bad")
        with mock.patch.object(builder.urllib.request, "urlopen") as download:
            with self.assertRaisesRegex(RuntimeError, "SHA256 mismatch"):
                builder._download("https://example.invalid", "0" * 64, self.root / "input.tar.gz", cache)
        download.assert_not_called()

    def test_valid_cache_does_not_need_network(self):
        cache = self.root / "cache"
        cache.mkdir()
        content = b"pinned"
        (cache / "input.tar.gz").write_bytes(content)
        with mock.patch.object(builder.urllib.request, "urlopen") as download:
            result = builder._download("https://example.invalid", hashlib.sha256(content).hexdigest(), self.root / "input.tar.gz", cache)
        self.assertEqual(result.read_bytes(), content)
        download.assert_not_called()

    def fake_source(self, archive, destination):
        tree = destination / "source"
        tree.mkdir(parents=True)
        (tree / "LICENSE").write_text("test license")
        if destination.name == "source-dreal3":
            (tree / "src/util").mkdir(parents=True)
            (tree / "src/util/CMakeLists.txt").write_text("get_git_head_revision(GIT_REFSPEC GIT_SHA1)\n")
            (tree / "src/CMakeLists.txt").write_text("\n".join('set(EXTRA_LIBS "{}" ${{EXTRA_LIBS}})'.format(name) for name in ["picosat", "prim", "glpk", "nlopt", "adept", "capd", "ibex"])+"\nBUILD_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf build\n")
        return tree

    def fake_compilers(self, build, identity="GNU"):
        folder = build / "CMakeFiles/test-version"
        folder.mkdir(parents=True, exist_ok=True)
        for language in ("C", "CXX"):
            (folder / ("CMake"+language+"Compiler.cmake")).write_text(
                'set(CMAKE_{}_COMPILER_ID "{}")\nset(CMAKE_{}_COMPILER_VERSION "9.4.0")\n'.format(language, identity, language))

    def test_success_is_private_audited_and_manifested(self):
        destination = self.root / "prefix"
        tools = {name: "/tools/" + name for name in ["gcc", "g++", "cmake", "make", "python2.7", "bison", "flex", "git", "pkg-config", "libtoolize"]}
        calls = []
        def run(command, env, log, cwd=None, timeout=1800):
            calls.append(command)
            self.assertNotIn("LD_LIBRARY_PATH", env)
            self.assertNotIn("CMAKE_LIBRARY_PATH", env)
            self.assertNotIn("CONFIG_SITE", env)
            self.assertNotIn("DESTDIR", env)
            self.assertNotIn("GNUMAKEFLAGS", env)
            self.assertNotIn("CMAKE_GENERATOR", env)
            log.write_text("build log")
            if "-S" in command:
                build = Path(command[command.index("-B") + 1]);build.mkdir(exist_ok=True)
                (build / "CMakeCache.txt").write_text("CMAKE_EXE_LINKER_FLAGS:STRING=-Wl,-u,pthread_self\n" + "\n".join(name+":BOOL=ON" for name in ["USE_LOCAL_THIRD_PARTY", "SUPPORT_ODE", "BUILD_STATIC_BIN", "CMAKE_DISABLE_FIND_PACKAGE_GLPK", "CMAKE_DISABLE_FIND_PACKAGE_NLOPT", "CMAKE_DISABLE_FIND_PACKAGE_CLP"]))
                self.fake_compilers(build)
            if "--build" in command:
                build = Path(command[2]);build.mkdir(exist_ok=True)
                (build / "dReal").write_bytes(b"verified binary")
        def download(url, digest, target, cache):
            target.write_bytes(b"source archive mocked")
            return target
        with mock.patch.object(builder, "_prerequisites", return_value=(4, tools)), \
                mock.patch.object(builder, "_prepare_cmake", return_value=(Path("/private/cmake"), {"version": "3.29.6"})), \
                mock.patch.object(builder, "_download", side_effect=download), \
                mock.patch.object(builder, "_unpack", side_effect=self.fake_source), \
                mock.patch.object(builder, "_run", side_effect=run), \
                mock.patch("stlmc.cli.native_linkage.audit_static_linkage", return_value={"fully_static": True}) as linkage, \
                mock.patch("stlmc.solver.dreal_runtime.validate_dreal_runtime", return_value={"ode_supported": True}) as runtime, \
                mock.patch.dict(os.environ, {"LD_LIBRARY_PATH": "/bad", "CMAKE_LIBRARY_PATH": "/bad", "CONFIG_SITE": "/bad", "DESTDIR": "/bad", "GNUMAKEFLAGS": "--eval=unsafe", "CMAKE_GENERATOR": "Ninja"}):
            executable = builder.build_dreal(destination, jobs=4)
        self.assertEqual(executable, destination / "bin/dReal")
        self.assertEqual(executable.read_bytes(), b"verified binary")
        linkage.assert_called_once();runtime.assert_called_once()
        manifest = json.loads((destination / "build-manifest.json").read_text())
        self.assertEqual(len(manifest["sources"]), 12)
        self.assertEqual(len(manifest["patches"]), 3)
        self.assertEqual(manifest["runtime"]["executable"], str(executable))
        self.assertEqual(manifest["cmake_tool"]["version"], "3.29.6")
        self.assertEqual(calls[0][0], Path("/private/cmake"))
        self.assertFalse(manifest["policy"]["clp"])
        self.assertIn("-DCMAKE_DISABLE_FIND_PACKAGE_GLPK=TRUE", calls[0])
        self.assertIn("-DCMAKE_DISABLE_FIND_PACKAGE_NLOPT=TRUE", calls[0])
        self.assertIn("-DCMAKE_DISABLE_FIND_PACKAGE_CLP=TRUE", calls[0])
        self.assertIn("-DBUILD_STATIC_BIN=ON", calls[0])
        self.assertIn("-DCMAKE_EXE_LINKER_FLAGS=-Wl,-u,pthread_self", calls[0])
        self.assertEqual(manifest["policy"]["static_thread_link_flag"], "-Wl,-u,pthread_self")
        self.assertEqual(calls[0][calls[0].index("-G") + 1], "Unix Makefiles")
        self.assertEqual(manifest["cmake_cache_audit"]["compilers"]["CXX"]["id"], "GNU")
        self.assertTrue((destination / "licenses/dreal3/LICENSE").exists())

    def test_host_library_cache_is_rejected(self):
        build = self.root / "build"
        build.mkdir()
        text = "\n".join(name+":BOOL=ON" for name in ["USE_LOCAL_THIRD_PARTY", "SUPPORT_ODE", "BUILD_STATIC_BIN", "CMAKE_DISABLE_FIND_PACKAGE_GLPK", "CMAKE_DISABLE_FIND_PACKAGE_NLOPT", "CMAKE_DISABLE_FIND_PACKAGE_CLP"])
        (build / "CMakeCache.txt").write_text(text+"\nCMAKE_EXE_LINKER_FLAGS:STRING=-Wl,-u,pthread_self\nNLOPT_LIBRARIES:FILEPATH=/host/libnlopt.so\n")
        with self.assertRaisesRegex(RuntimeError, "ambient native dependency"):
            builder._audit_cache(build)

    def test_missing_forced_static_pthread_symbol_is_rejected(self):
        build = self.root / "build"
        build.mkdir()
        (build / "CMakeCache.txt").write_text("CMAKE_EXE_LINKER_FLAGS:STRING=-static\n")
        with self.assertRaisesRegex(RuntimeError, "missing forced pthread_self"):
            builder._audit_cache(build)

    def test_static_link_cache_failure_preserves_existing_installation(self):
        destination = self.root / "new-prefix"
        existing = self.root / "active-dReal"
        existing.write_bytes(b"previous valid executable")
        tools = {name: name for name in ["gcc", "g++", "make", "python2.7", "bison", "flex", "git", "pkg-config", "libtoolize"]}
        def configure(command, env, log, **kwargs):
            log.write_text("configure diagnostic")
        with mock.patch.object(builder, "_prerequisites", return_value=(1, tools)), \
                mock.patch.object(builder, "_prepare_cmake", return_value=(Path("/private/cmake"), {})), \
                mock.patch.object(builder, "_download", side_effect=lambda u,d,p,c:p), \
                mock.patch.object(builder, "_unpack", side_effect=self.fake_source), \
                mock.patch.object(builder, "_run", side_effect=configure) as run, \
                mock.patch.object(builder, "_audit_cache", side_effect=RuntimeError("missing forced pthread_self")):
            with self.assertRaisesRegex(RuntimeError, "missing forced pthread_self.*Existing installations were not changed"):
                builder.build_dreal(destination, jobs=1)
        self.assertEqual(run.call_count, 1)  # No compilation after rejected configure.
        self.assertFalse(destination.exists())
        self.assertEqual(existing.read_bytes(), b"previous valid executable")
        self.assertFalse(list(self.root.glob(".dreal-build-*")))

    def test_actual_compiler_identity_must_be_gnu_not_just_named_gcc(self):
        build = self.root / "build"
        build.mkdir()
        text = "\n".join(name+":BOOL=ON" for name in ["USE_LOCAL_THIRD_PARTY", "SUPPORT_ODE", "BUILD_STATIC_BIN", "CMAKE_DISABLE_FIND_PACKAGE_GLPK", "CMAKE_DISABLE_FIND_PACKAGE_NLOPT", "CMAKE_DISABLE_FIND_PACKAGE_CLP"])
        (build / "CMakeCache.txt").write_text(text + "\nCMAKE_EXE_LINKER_FLAGS:STRING=-Wl,-u,pthread_self\n")
        with self.assertRaisesRegex(RuntimeError, "compiler identity"):
            builder._audit_cache(build)
        self.fake_compilers(build, "Clang")
        with self.assertRaisesRegex(RuntimeError, "verified GNU"):
            builder._audit_cache(build)
        self.fake_compilers(build, "GNU")
        self.assertEqual(builder._audit_cache(build)["compilers"]["C"]["version"], "9.4.0")

    def test_runtime_failure_does_not_publish_prefix(self):
        destination = self.root / "prefix"
        tools = {name: name for name in ["gcc", "g++", "cmake", "make", "python2.7", "bison", "flex", "git", "pkg-config", "libtoolize"]}
        def run(command, env, log, **kwargs):
            log.write_text("failed build diagnostic")
            raise RuntimeError("test compile failure")
        with mock.patch.object(builder, "_prerequisites", return_value=(4, tools)), \
                mock.patch.object(builder, "_prepare_cmake", return_value=(Path("/private/cmake"), {})), \
                mock.patch.object(builder, "_download", side_effect=lambda u,d,p,c:p), \
                mock.patch.object(builder, "_unpack", side_effect=self.fake_source), \
                mock.patch.object(builder, "_run", side_effect=run):
            with self.assertRaisesRegex(RuntimeError, "Existing installations were not changed"):
                builder.build_dreal(destination, jobs=4)
        self.assertFalse(destination.exists())
        self.assertIn("diagnostic", destination.with_name("prefix.failed-build.log").read_text())

    def test_tool_environment_failure_cleans_staging_without_publishing(self):
        destination = self.root / "prefix"
        tools = {name: name for name in ["gcc", "g++", "make", "python2.7", "bison", "flex", "git", "pkg-config", "libtoolize"]}
        with mock.patch.object(builder, "_prerequisites", return_value=(1, tools)), \
                mock.patch.object(builder, "_download", side_effect=lambda u,d,p,c:p), \
                mock.patch.object(builder, "_unpack", side_effect=self.fake_source), \
                mock.patch.object(builder, "_prepare_cmake", side_effect=RuntimeError("ensurepip unavailable")), \
                mock.patch.object(builder, "_run") as compile_command:
            with self.assertRaisesRegex(RuntimeError, "ensurepip unavailable.*Existing installations were not changed"):
                builder.build_dreal(destination, jobs=1)
        compile_command.assert_not_called()
        self.assertFalse(destination.exists())
        self.assertFalse(list(self.root.glob(".dreal-build-*")))


if __name__ == "__main__":
    unittest.main()

"""Record source provenance in wheels and sdists without requiring Git at runtime."""

from pathlib import Path
import runpy

from setuptools import setup
from setuptools.command.build_py import build_py
from setuptools.command.sdist import sdist


ROOT = Path(__file__).resolve().parent


def build_commit():
    namespace = runpy.run_path(str(ROOT / "src/stlmc/version_info.py"))
    commit = namespace["_source_commit"](ROOT)
    if commit:
        return commit
    existing = ROOT / "src/stlmc/_build_info.py"
    if existing.is_file():
        return runpy.run_path(str(existing)).get("COMMIT", "unknown")
    return "unknown"


def write_build_info(destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(
        '"""Source revision recorded when this distribution was built."""\n'
        'COMMIT = {!r}\n'.format(build_commit()), encoding="utf-8",
    )


class BuildWithRevision(build_py):
    def run(self):
        super().run()
        write_build_info(Path(self.build_lib) / "stlmc/_build_info.py")

    def get_outputs(self, include_bytecode=1):
        outputs = super().get_outputs(include_bytecode)
        generated = str(Path(self.build_lib) / "stlmc/_build_info.py")
        return outputs if generated in outputs else outputs + [generated]


class SdistWithRevision(sdist):
    def make_release_tree(self, base_dir, files):
        super().make_release_tree(base_dir, files)
        write_build_info(Path(base_dir) / "src/stlmc/_build_info.py")


setup(cmdclass={"build_py": BuildWithRevision, "sdist": SdistWithRevision})

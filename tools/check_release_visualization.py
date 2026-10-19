"""Exercise the installed distribution with the README example and renderers."""

import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent


def run_cli(module, arguments, working, environment):
    completed = subprocess.run(
        [sys.executable, "-c",
         "from {} import main; raise SystemExit(main())".format(module),
         *arguments],
        cwd=working, env=environment, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=90,
    )
    print(completed.stdout, end="", flush=True)
    if completed.returncode:
        raise RuntimeError("{} exited with {}".format(module, completed.returncode))
    return completed.stdout


def main():
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    section = readme.split("## Quick start\n", 1)[1].split("\n## ", 1)[0]
    model = re.search(r"```text\n(.*?)\n```", section, re.S).group(1)
    command = shlex.split(re.search(r"```sh\n(.*?)\n```", section, re.S).group(1))
    if command[0] != "stlmc":
        raise RuntimeError("Expected an STLmc quick-start command")
    environment = dict(os.environ, STLMC_DISABLE_UPDATE_CHECK="1",
                       OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
    # Do not let a source-checkout override bypass the installed wheel.
    environment.pop("PYTHONPATH", None)
    temporary_root = ROOT / ".tmp"
    temporary_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="release-render-", dir=temporary_root) as directory:
        working = Path(directory)
        environment["MPLCONFIGDIR"] = str(working / "matplotlib")
        (working / "quickstart.model").write_text(model + "\n", encoding="utf-8")
        output = run_cli("stlmc.cli.mc", command[1:], working, environment)
        if re.search(r"status\s*:\s*violated at bound [012]", output) is None:
            raise RuntimeError("Quick-start verification did not find its expected counterexample")
        artifacts = list(working.glob("*.counterexample"))
        if len(artifacts) != 1 or not artifacts[0].with_suffix(".cfg").is_file():
            raise RuntimeError("Expected one counterexample and its visualization configuration")
        artifact = artifacts[0]
        for output_format in ("html", "pdf", "text"):
            run_cli("stlmc.cli.visualize", [str(artifact), "-cfg",
                    str(artifact.with_suffix(".cfg")), "-output", output_format],
                    working, environment)
        html = list(working.glob("*.html"))
        pdf = list(working.glob("*.pdf"))
        text = list(working.glob("*.txt"))
        if not html or not all("<html" in path.read_text(encoding="utf-8").lower() for path in html):
            raise RuntimeError("HTML output is missing or invalid")
        if not pdf or not all(path.read_bytes().startswith(b"%PDF-") for path in pdf):
            raise RuntimeError("PDF output is missing or invalid")
        if not text or not all(path.stat().st_size for path in text):
            raise RuntimeError("Text output is missing or empty")
        print("Installed-package visualization smoke: PASS (HTML, PDF, text)")


if __name__ == "__main__":
    main()

"""Preview or apply a body-only update to an existing GitHub Release."""

import argparse
import difflib
import json
from pathlib import Path
import re
import subprocess

from release_notes import VERSION, extract_notes


def api(repository, method, resource, payload=None):
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None:
        raise ValueError("invalid owner/repository")
    command = ["gh", "api", "--method", method,
               "repos/{}/{}".format(repository, resource)]
    if payload is not None:
        command.extend(["--input", "-"])
    result = subprocess.run(command, input=json.dumps(payload) if payload is not None else None,
                            capture_output=True, text=True, check=True, timeout=60)
    return json.loads(result.stdout)


def prepare(tag, repository, directory, output):
    notes = extract_notes(tag, directory)
    tag = tag if tag.startswith("v") else "v" + tag
    release = api(repository, "GET", "releases/tags/" + tag)
    if release.get("tag_name") != tag or type(release.get("id")) is not int:
        raise ValueError("GitHub returned an unexpected release")
    before = release.get("body") or ""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    plan = dict(repository=repository, tag=tag, release_id=release["id"])
    (output / "plan.json").write_text(json.dumps(plan, indent=2), encoding="utf-8")
    (output / "release-before.json").write_text(json.dumps(release, indent=2), encoding="utf-8")
    (output / "notes-before.md").write_text(before, encoding="utf-8")
    (output / "notes-proposed.md").write_text(notes, encoding="utf-8")
    diff = "".join(difflib.unified_diff(before.splitlines(True), notes.splitlines(True),
                                        fromfile="previous body", tofile="proposed body"))
    (output / "notes.diff").write_text(diff, encoding="utf-8")
    print("Prepared {} in {}. No GitHub content was changed.".format(tag, output))


def apply(output):
    output = Path(output)
    plan = json.loads((output / "plan.json").read_text(encoding="utf-8"))
    old = json.loads((output / "release-before.json").read_text(encoding="utf-8"))
    if VERSION.fullmatch(plan["tag"]) is None or type(plan["release_id"]) is not int:
        raise ValueError("invalid saved release plan")
    resource = "releases/{}".format(plan["release_id"])
    current = api(plan["repository"], "GET", resource)
    if current.get("tag_name") != plan["tag"] or current.get("id") != old.get("id"):
        raise ValueError("release identity changed; prepare a new preview")
    if current.get("body") != old.get("body"):
        raise ValueError("release body changed since preview; prepare a new preview")
    notes = (output / "notes-proposed.md").read_text(encoding="utf-8")
    if not notes.strip():
        raise ValueError("refusing to replace a release body with empty notes")
    if (current.get("body") or "") == notes:
        print("Release notes already match; no update needed.")
        return
    # Deliberately omit tag, name, assets, draft, prerelease, and make_latest.
    updated = api(plan["repository"], "PATCH", resource, {"body": notes})
    (output / "release-after.json").write_text(json.dumps(updated, indent=2), encoding="utf-8")
    print("Updated only the body of {}.".format(plan["tag"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("preview", "apply"))
    parser.add_argument("--tag")
    parser.add_argument("--repository")
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parents[1] / "docs/releases")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.mode == "preview":
            if not args.tag or not args.repository:
                parser.error("preview requires --tag and --repository")
            prepare(args.tag, args.repository, args.directory, args.output)
        else:
            apply(args.output)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, "release notes error: {}\n".format(error))


if __name__ == "__main__":
    main()

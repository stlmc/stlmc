"""Extract one release section from its stable-version Markdown file."""

import argparse
from pathlib import Path
import re


VERSION = re.compile(r"v?(\d+\.\d+\.\d+)(?:\.dev\d+)?\Z")


def extract_notes(tag, directory):
    match = VERSION.fullmatch(tag)
    if match is None:
        raise ValueError("expected a tag such as v1.0.1 or v1.0.1.dev3")
    version = tag[1:] if tag.startswith("v") else tag
    path = Path(directory) / (match.group(1) + ".md")
    if not path.is_file():
        raise ValueError("missing release notes: {}".format(path))
    content = path.read_text(encoding="utf-8")
    sections = list(re.finditer(r"^## ([^\n]+)[ \t]*$", content, re.M))
    selected = [i for i, section in enumerate(sections) if section.group(1).strip() == version]
    if len(selected) != 1:
        raise ValueError("{} must contain exactly one '## {}' section".format(path, version))
    index = selected[0]
    end = sections[index + 1].start() if index + 1 < len(sections) else len(content)
    notes = content[sections[index].end():end].strip()
    if not notes or re.search(r"\b(?:TODO|TBD)\b", notes):
        raise ValueError("release notes for {} are empty or unfinished".format(version))
    return notes + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tag")
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parents[1] / "docs/releases")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        notes = extract_notes(args.tag, args.directory)
    except ValueError as error:
        parser.error(str(error))
    if args.output:
        args.output.write_text(notes, encoding="utf-8")
    else:
        print(notes, end="")


if __name__ == "__main__":
    main()

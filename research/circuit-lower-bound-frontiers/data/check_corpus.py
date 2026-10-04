#!/usr/bin/env python3
"""Validates: local Markdown links, document reachability, and canonical citations."""

from pathlib import Path
import hashlib
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


def prose(text):
    """Exclude fenced code and inline code from citation/link checks."""
    result = []
    fence = None
    for line in text.splitlines():
        match = re.match(r"^\s*(`{3,}|~{3,})", line)
        if match:
            marker = match.group(1)
            if fence is None:
                fence = marker
            elif marker[0] == fence[0] and len(marker) >= len(fence):
                fence = None
            result.append("")
        elif fence is None:
            result.append(re.sub(r"(`+).*?\1", "", line))
        else:
            result.append("")
    return "\n".join(result)


def main():
    errors = []
    documents = sorted(ROOT.rglob("*.md"))
    links = {path: set() for path in documents}
    sources = ROOT / "sources.md"
    source_text = sources.read_text()
    anchors_list = re.findall(r'<a\s+(?:id|name)="([^"]+)"\s*>', source_text)
    anchors = set(anchors_list)
    if len(anchors) != len(anchors_list):
        errors.append("sources.md: duplicate bibliography anchors")
    used = set()
    snapshot = ROOT / "graph-perspective/data/realization-source.txt"
    expected_digest = "280af8fd79953606c1092b348bbf256c4c7cbdbe2513b716d598e06f8fcd91be"
    if hashlib.sha256(snapshot.read_bytes()).hexdigest() != expected_digest:
        errors.append("realization-source.txt: snapshot digest mismatch")
    if expected_digest not in source_text:
        errors.append("sources.md: snapshot digest missing")

    for path in documents:
        text = prose(path.read_text())
        relative = str(path.relative_to(ROOT))
        definitions = dict(re.findall(r"^\[([^\]]+)\]:\s+(\S+)", text, re.M))
        citations = re.findall(r"\[([^\]\n]+)\]\[([^\]\n]+)\]", text)
        for label, key in citations:
            if label != key or key.lower() != key:
                errors.append(f"{relative}: noncanonical citation [{label}][{key}]")
            if key not in definitions:
                errors.append(f"{relative}: undefined citation {key}")
                continue
            target = urlsplit(definitions[key])
            target_file = (path.parent / unquote(target.path)).resolve()
            if target_file != sources or target.fragment != key or key not in anchors:
                errors.append(f"{relative}: citation {key} must resolve to sources.md#{key}")
            used.add(key)

        targets = list(definitions.values())
        targets += re.findall(r"\[[^\]\n]*\]\(([^\s)]+)\)", text)
        for raw in targets:
            target = urlsplit(raw.strip("<>"))
            if target.scheme or target.netloc:
                continue
            if Path(unquote(target.path)).is_absolute():
                errors.append(f"{relative}: nonportable absolute local link {raw}")
                continue
            destination = (path.parent / unquote(target.path)).resolve() if target.path else path
            if not destination.exists():
                errors.append(f"{relative}: missing local target {raw}")
            elif destination in links:
                links[path].add(destination)

    reached = set()
    todo = [ROOT / "index.md"]
    while todo:
        path = todo.pop()
        if path in reached:
            continue
        reached.add(path)
        todo.extend(links.get(path, ()))
    for path in documents:
        if path not in reached:
            errors.append(f"orphan Markdown document: {path.relative_to(ROOT)}")
    for key in sorted(anchors - used):
        errors.append(f"sources.md: uncited source anchor {key}")

    if errors:
        print("\n".join(errors))
        return 1
    print(f"PASS: {len(documents)} Markdown documents, {len(anchors)} cited sources; "
          "local links and reachability checked")
    return 0


if __name__ == "__main__":
    sys.exit(main())

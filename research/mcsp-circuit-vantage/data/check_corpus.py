#!/usr/bin/env python3
"""Validates: reachable documents, local links, and canonical source citations.

Adapted from the repository's circuit-lower-bound-frontiers corpus checker.
Fenced examples and inline code are excluded from prose citation matching.
"""

from pathlib import Path
import hashlib
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


def prose(text):
    lines = []
    fence = None
    for line in text.splitlines():
        marker = re.match(r"^\s*(`{3,}|~{3,})", line)
        if marker:
            value = marker.group(1)
            if fence is None:
                fence = value
            elif value[0] == fence[0] and len(value) >= len(fence):
                fence = None
            lines.append("")
        elif fence is None:
            lines.append(re.sub(r"(`+).*?\1", "", line))
    return "\n".join(lines)


def main():
    errors = []
    documents = sorted(ROOT.rglob("*.md"))
    sources = ROOT / "sources.md"
    anchors_list = re.findall(r'<a\s+(?:id|name)="([^"]+)"\s*>', sources.read_text())
    anchors = set(anchors_list)
    for snapshot, digest in {
        "sources/interface-capacity.txt":
            "e1cd0af68b1f1a678236dcef0280806fa17eb9627d92d8d8dbfb97a861fc7246",
        "sources/charging.txt":
            "71d2a06374ac4693aa6a52881f6c15ead3c7a93bc508d2522945b80c90f2943f",
    }.items():
        if hashlib.sha256((ROOT / snapshot).read_bytes()).hexdigest() != digest:
            errors.append(f"Source snapshot changed: {snapshot}")
        if digest not in sources.read_text():
            errors.append(f"Source snapshot digest missing from bibliography: {snapshot}")
    if len(anchors_list) != len(anchors):
        errors.append("sources.md: duplicate anchors")
    used = set()
    links = {path: set() for path in documents}
    for path in documents:
        text = prose(path.read_text())
        relative = path.relative_to(ROOT)
        if "## Local References" in text:
            errors.append(f"{relative}: unassembled Local References")
        definitions = dict(re.findall(r"^\[([^\]]+)\]:\s+(\S+)", text, re.M))
        for label, key in re.findall(r"\[([^\]\n]+)\]\[([^\]\n]+)\]", text):
            if label != key or key.lower() != key:
                errors.append(f"{relative}: noncanonical [{label}][{key}]")
            if key not in definitions:
                errors.append(f"{relative}: undefined citation {key}")
                continue
            target = urlsplit(definitions[key])
            destination = (path.parent / unquote(target.path)).resolve()
            if destination != sources or target.fragment != key or key not in anchors:
                errors.append(f"{relative}: citation {key} does not resolve to master source")
            used.add(key)
        targets = list(definitions.values())
        targets += re.findall(r"\[[^\]\n]*\]\(([^\s)]+)\)", text)
        for raw in targets:
            target = urlsplit(raw.strip("<>"))
            if target.scheme or target.netloc:
                continue
            decoded = unquote(target.path)
            destination = (path.parent / decoded).resolve() if decoded else path
            if not destination.exists():
                errors.append(f"{relative}: missing local target {raw}")
            elif destination in links:
                links[path].add(destination)
            if target.fragment.startswith("L") and target.fragment[1:].isdigit():
                line = int(target.fragment[1:])
                if destination.is_file() and line > len(destination.read_text().splitlines()):
                    errors.append(f"{relative}: line anchor outside file {raw}")
    reached = set()
    pending = [ROOT / "index.md"]
    while pending:
        path = pending.pop()
        if path not in reached:
            reached.add(path)
            pending.extend(links.get(path, ()))
    errors.extend(f"Orphan: {path.relative_to(ROOT)}" for path in documents if path not in reached)
    errors.extend(f"Unused source: {key}" for key in sorted(anchors - used))
    if errors:
        print("\n".join(errors))
        return 1
    print(f"PASS: {len(documents)} reachable documents, {len(anchors)} canonical cited sources.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

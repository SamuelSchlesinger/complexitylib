#!/usr/bin/env python3
"""Validates: corpus links/citations, pinned source bytes, and finite sampler checks.

Run without arguments for all self-contained checks. Optional --source-dir and
--pdf paths also compare downloaded source bytes to source-manifest.json.
This is document and finite-example validation, not a proof of derandomization.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
REVISION = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def prose(text):
    """Exclude fenced code and inline code before inspecting Markdown citations."""
    result = []
    fence = None
    for line in text.splitlines():
        marker = re.match(r"^\s*(`{3,}|~{3,})", line)
        if marker:
            token = marker.group(1)
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence):
                fence = None
            continue
        if fence is None:
            result.append(re.sub(r"(`+).*?\1", "", line))
    return "\n".join(result)


def check_documents():
    documents = {p.resolve() for p in ROOT.rglob("*.md")}
    sources = ROOT / "sources.md"
    anchors = set(re.findall(r'<a id="([a-z0-9-]+)"></a>', sources.read_text()))
    used = set()
    links = {}
    errors = []
    for path in sorted(documents):
        body = prose(path.read_text())
        links[path] = set()
        definitions = dict(re.findall(r"^\[([a-z0-9-]+)\]:\s*(\S+)", body, re.M))
        for display, key in re.findall(r"\[([^\]\n]+)\]\[([a-z0-9-]+)\]", body):
            if display != key:
                errors.append(f"{path.relative_to(ROOT)}: citation display drift: {display}/{key}")
            if key not in anchors or key not in definitions:
                errors.append(f"{path.relative_to(ROOT)}: undefined citation {key}")
                continue
            target, _, anchor = definitions[key].partition("#")
            if (path.parent / target).resolve() != sources.resolve() or anchor != key:
                errors.append(f"{path.relative_to(ROOT)}: noncanonical target for {key}")
            used.add(key)
        targets = re.findall(r"(?<!!)\[[^\]\n]+\]\(([^)\s]+)\)", body)
        targets.extend(definitions.values())
        for target in targets:
            if re.match(r"[a-z]+:", target):
                continue
            filename = target.split("#", 1)[0]
            destination = (path.parent / filename).resolve() if filename else path
            if not destination.exists():
                errors.append(f"{path.relative_to(ROOT)}: missing link {target}")
            if destination in documents:
                links[path].add(destination)
        if "## Local References" in body:
            errors.append(f"{path.relative_to(ROOT)}: unassembled local references")
    if anchors - used:
        errors.append(f"unused bibliography anchors: {sorted(anchors - used)}")
    seen, pending = set(), [(ROOT / "index.md").resolve()]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        pending.extend(links.get(current, set()) - seen)
    if documents - seen:
        errors.append("unreachable documents: " + ", ".join(
            str(p.relative_to(ROOT)) for p in sorted(documents - seen)))
    if errors:
        raise AssertionError("\n".join(errors))
    print(f"Documents: {len(documents)} reachable; {len(anchors)} canonical sources; links pass")


def check_provenance(source_dir, pdf):
    manifest = json.loads((ROOT / "data/source-manifest.json").read_text())
    assert manifest["revision"] == REVISION
    assert manifest["source_key"] == "oai26"
    assert len(manifest["files"]) == 14
    checked = 0
    for record in manifest["files"]:
        assert f"/openai/math/{REVISION}/" in record["url"]
        assert record["url"].endswith("/" + record["path"])
        assert re.fullmatch(r"[0-9a-f]{40}", record["git_blob_sha1"])
        assert re.fullmatch(r"[0-9a-f]{64}", record["sha256"])
        local = None
        if record["path"] == "paper.pdf":
            local = pdf
        elif source_dir:
            local = source_dir / Path(record["path"]).name
        if local:
            data = local.read_bytes()
            assert len(data) == record["bytes"], local
            assert hashlib.sha256(data).hexdigest() == record["sha256"], local
            blob = b"blob " + str(len(data)).encode() + b"\0" + data
            assert hashlib.sha1(blob).hexdigest() == record["git_blob_sha1"], local
            checked += 1
    for document in ROOT.rglob("*.md"):
        for revision in re.findall(r"\b[0-9a-f]{40}\b", document.read_text()):
            assert revision == REVISION, (document, revision)
    print(f"Provenance: 14 pinned entries; {checked} local byte identities checked")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path)
    parser.add_argument("--pdf", type=Path)
    args = parser.parse_args()
    check_documents()
    check_provenance(args.source_dir, args.pdf)
    subprocess.run([sys.executable, str(ROOT / "target/data/validate_sampler.py")], check=True)
    print("Corpus audit passed; no claim of general theorem verification.")


if __name__ == "__main__":
    main()

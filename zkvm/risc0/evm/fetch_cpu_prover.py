#!/usr/bin/env python3
"""Extract genuine CPU prover files from the pinned official amd64 OCI image.

This installs unmodified binaries and the existing trusted setup. It does not
generate a proof, run a new ceremony, supply a fake Docker command, or contact
a proving service. Public Docker Registry downloads are authenticated with a
short-lived public pull token which is never printed or saved.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import urllib.request

REPOSITORY = "risczero/risc0-groth16-prover"
TAG = "v2026-10-20.1"
MANIFEST = "sha256:49093ed164b82aca9305dd80e4a6eb996bd443201ac7bd50b52909b2761ef583"
FILES = {
    "usr/local/bin/prover", "usr/local/bin/stark_verify", "app/stark_verify.cs",
    "app/stark_verify_final.pk.dmp", "app/stark_verify.dat", "app/prover.sh",
}


def digest_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    root = args.output_dir.resolve()
    root.mkdir(parents=True, exist_ok=True)
    if shutil.disk_usage(root).free < 12 * 1024**3:
        raise SystemExit("At least 12 GiB free is required before this setup download; preserve 4 GiB reserve")
    downloads = root / "downloads"
    downloads.mkdir(exist_ok=True)

    token_url = "https://auth.docker.io/token?service=registry.docker.io&scope=repository:" + REPOSITORY + ":pull"
    with urllib.request.urlopen(token_url, timeout=60) as response:
        token = json.load(response)["token"]

    def request(kind: str, digest: str):
        url = "https://registry-1.docker.io/v2/" + REPOSITORY + "/" + kind + "/" + digest
        return urllib.request.urlopen(urllib.request.Request(url, headers={
            "Authorization": "Bearer " + token,
            "Accept": "application/vnd.oci.image.manifest.v1+json",
        }), timeout=60)

    with request("manifests", MANIFEST) as response:
        manifest_bytes = response.read(1024 * 1024)
    if "sha256:" + hashlib.sha256(manifest_bytes).hexdigest() != MANIFEST:
        raise SystemExit("OCI manifest digest mismatch")
    manifest = json.loads(manifest_bytes)
    (root / "oci-manifest.json").write_bytes(manifest_bytes)
    extracted = {}
    # The first layer is Debian's base filesystem. Only the subsequent official
    # prover layers are needed; no container filesystem is installed on the host.
    for index, layer in enumerate(manifest["layers"][1:], start=1):
        digest = layer["digest"]
        path = downloads / (digest.removeprefix("sha256:") + ".tar.gz")
        if not (path.exists() and path.stat().st_size == layer["size"] and digest_file(path) == digest):
            if shutil.disk_usage(root).free < layer["size"] + 4 * 1024**3:
                raise SystemExit("Insufficient disk reserve for the next official image layer")
            partial = path.with_suffix(".part")
            print(f"Downloading official layer {index}: {layer['size']} bytes", flush=True)
            count = 0
            calculated = hashlib.sha256()
            with request("blobs", digest) as response, partial.open("wb") as stream:
                while chunk := response.read(1024 * 1024):
                    count += len(chunk)
                    if count > layer["size"]:
                        raise SystemExit("OCI layer exceeds its pinned declared size")
                    stream.write(chunk)
                    calculated.update(chunk)
            if count != layer["size"] or "sha256:" + calculated.hexdigest() != digest:
                raise SystemExit("OCI layer size/digest mismatch")
            partial.replace(path)
        with tarfile.open(path, "r:gz") as archive:
            for member in archive:
                name = member.name.removeprefix("./")
                if name not in FILES:
                    continue
                if not member.isfile():
                    raise SystemExit(f"Expected a regular official prover file: {name}")
                if shutil.disk_usage(root).free < member.size + 4 * 1024**3:
                    raise SystemExit("Insufficient disk reserve to extract official prover file")
                archive.extract(member, path=root, filter="data")
                extracted[name] = {"size": member.size, "sha256": digest_file(root / name), "layer": digest}
                print(f"Verified and extracted {name} ({member.size} bytes)", flush=True)
    if set(extracted) != FILES:
        raise SystemExit(f"Official image did not contain all expected files: {FILES - set(extracted)}")
    report = {"repository": REPOSITORY, "tag": TAG, "manifest": MANIFEST, "files": extracted}
    (root / "cpu-prover-install.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("Installed genuine official CPU prover/setup files; no proof has been generated", flush=True)


if __name__ == "__main__":
    main()

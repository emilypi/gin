#!/usr/bin/env bash
# Tool installation for the Ubuntu 24.04 x86_64 GitHub Actions runner.
set -euo pipefail

sudo apt-get update
sudo apt-get install --yes --no-install-recommends iverilog verilator python3

nvc_url=https://github.com/nickg/nvc/releases/download/r1.23.1
nvc_file=nvc_1.23.1-1_amd64_ubuntu-24.04.deb
nvc_sha=836b86c93d7ac0fa6d6313b651c0409476f04f59718fb270515e6bc6232477cd
curl --fail --location --retry 3 "$nvc_url/$nvc_file" --output "$RUNNER_TEMP/nvc.deb"
printf '%s  %s\n' "$nvc_sha" "$RUNNER_TEMP/nvc.deb" | sha256sum --check
sudo apt-get install --yes --no-install-recommends "$RUNNER_TEMP/nvc.deb"

elan_url=https://github.com/leanprover/elan/releases/download/v4.2.4
elan_file=elan-x86_64-unknown-linux-gnu.tar.gz
elan_sha=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
curl --fail --location --retry 3 "$elan_url/$elan_file" \
  --output "$RUNNER_TEMP/elan.tar.gz"
printf '%s  %s\n' "$elan_sha" "$RUNNER_TEMP/elan.tar.gz" | sha256sum --check
mkdir -p "$RUNNER_TEMP/elan"
tar -xzf "$RUNNER_TEMP/elan.tar.gz" -C "$RUNNER_TEMP/elan"
IFS= read -r lean_toolchain < lean/lean-toolchain
"$RUNNER_TEMP/elan/elan-init" -y --no-modify-path --default-toolchain "$lean_toolchain"
printf '%s\n' "$HOME/.elan/bin" >> "$GITHUB_PATH"

python3 --version
iverilog -V
verilator --version
nvc --version
"$HOME/.elan/bin/lean" --version

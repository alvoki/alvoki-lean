#!/usr/bin/env bash
set -euo pipefail

toolchains=${1:-"$PWD/../work/toolchains"}
mkdir -p "$toolchains"
cd "$toolchains"
export ELAN_HOME="$PWD/elan"
export PATH="$ELAN_HOME/bin:$PATH"

downloads=$(mktemp -d)
trap 'rm -rf "$downloads"' EXIT
fetch() {
  local url=$1 digest=$2 file=$3
  curl -fsSLo "$file" "$url"
  printf '%s  %s\n' "$digest" "$file" | sha256sum --check --status
}

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  fetch https://github.com/leanprover/elan/releases/download/v4.4.0/elan-x86_64-unknown-linux-gnu.tar.gz \
    0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2 "$downloads/elan.tar.gz"
  tar -xzf "$downloads/elan.tar.gz" -C "$downloads"
  "$downloads/elan-init" -y --no-modify-path --default-toolchain none
fi

elan toolchain install leanprover/lean4:v4.36.0
lake +leanprover/lean4:v4.36.0 --version

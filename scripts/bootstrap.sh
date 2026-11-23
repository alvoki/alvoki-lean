#!/usr/bin/env bash
set -euo pipefail

toolchains=${1:-"$PWD/../work/toolchains"}
mkdir -p "$toolchains"
cd "$toolchains"
export ELAN_HOME="$PWD/elan" RUSTUP_HOME="$PWD/rustup" CARGO_HOME="$PWD/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

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

if [[ ! -x "$CARGO_HOME/bin/rustup" ]]; then
  fetch https://static.rust-lang.org/rustup/archive/1.29.3/x86_64-unknown-linux-gnu/rustup-init \
    b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55 "$downloads/rustup-init"
  chmod +x "$downloads/rustup-init"
  "$downloads/rustup-init" -y --no-modify-path --profile minimal --default-toolchain none
fi
rustup toolchain install 1.100.0 --profile minimal --no-self-update
rustc +1.100.0 --version

release=0.2026.11.22.1ce6a59
archive="verus-$release-x86-linux.zip"
if [[ ! -x verus-x86-linux/verus ]]; then
  fetch "https://github.com/verus-lang/verus/releases/download/release/$release/$archive" \
    c955d5958877f4f907cce80aa996d4239a481984829d82e325938c7bf242b0db "$downloads/$archive"
  unzip -oq "$downloads/$archive"
fi
verus_version=$(./verus-x86-linux/verus --version)
printf '%s\n' "$verus_version"
if ! grep -Fxq "  Version: $release" <<< "$verus_version"; then
  echo "Expected Verus $release in $PWD/verus-x86-linux" >&2
  exit 1
fi

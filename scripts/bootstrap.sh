#!/usr/bin/env bash
set -euo pipefail

toolchains=${1:-"$PWD/../work/toolchains"}
mkdir -p "$toolchains"
cd "$toolchains"
export ELAN_HOME="$PWD/elan" RUSTUP_HOME="$PWD/rustup" CARGO_HOME="$PWD/cargo"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"

if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl -fsSLo elan.sh https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
  sh elan.sh -y --no-modify-path --default-toolchain leanprover/lean4:v4.36.0
fi
elan toolchain install leanprover/lean4:v4.36.0
lake +leanprover/lean4:v4.36.0 --version

if [[ ! -x "$CARGO_HOME/bin/rustup" ]]; then
  curl -fsSLo rustup.sh https://sh.rustup.rs
  sh rustup.sh -y --no-modify-path --profile minimal --default-toolchain 1.100.0
fi
rustup toolchain install 1.100.0 --profile minimal
rustc +1.100.0 --version

release=0.2026.11.22.1ce6a59
archive="verus-$release-x86-linux.zip"
if [[ ! -x verus-x86-linux/verus ]]; then
  curl -fsSLo "$archive" "https://github.com/verus-lang/verus/releases/download/release/$release/$archive"
  unzip -q "$archive"
fi
./verus-x86-linux/verus --version

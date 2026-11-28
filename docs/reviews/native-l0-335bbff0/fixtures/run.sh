#!/usr/bin/env bash
set -euo pipefail

fixtures=$(cd "$(dirname "$0")" && pwd)
repository=${1:-$fixtures}
commit=335bbff012b09d70847b9caef3dbf7be13a53296
tree=867325cb266c85371af7b5b21463f3a974d85ca3
if [[ $(git -C "$repository" rev-parse "$commit^{tree}") != "$tree" ]]; then
  echo "Candidate tree mismatch" >&2
  exit 1
fi
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
git -C "$repository" archive "$commit" lean | tar -x -C "$out"
cp "$fixtures/HistoryProbe.lean" "$fixtures/RecoveryProbe.lean" "$out/lean/"
cd "$out/lean"
if [[ -n ${ALVOKI_TOOLCHAINS:-} ]]; then
  export ELAN_HOME="$ALVOKI_TOOLCHAINS/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
case "$(lean --version)" in
  *"version 4.36.0,"*"commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"*) ;;
  *) echo "These fixtures require the candidate's pinned Lean 4.36.0 release" >&2; exit 1 ;;
esac
printf 'Candidate %s tree %s\n' "$commit" "$tree"
lake build crc32cArchive manifestNativeCheck
prefix=$(lean --print-prefix)
export LEAN_PATH="$out/modules"
mkdir -p "$LEAN_PATH"

# Recompile the public native operation's import closure exactly once.
# The two external drivers are linked separately to keep their entry points distinct.
declare -A compiled
objects=()
compile() {
  local module=$1 dependency
  if [[ ! -f $module.lean || -n ${compiled[$module]:-} ]]; then
    return
  fi
  while read -r dependency; do
    compile "${dependency//./\/}"
  done < <(awk '$1 == "import" { for (i=2; i<=NF && $i !~ /^--/; i++) print $i }' "$module.lean")
  local target="$LEAN_PATH/$module"
  mkdir -p "$(dirname "$target")"
  lean -o "$target.olean" -c "$target.c" "$module.lean"
  cc -O1 -fPIC -I"$prefix/include" -c "$target.c" -o "$target.o"
  objects+=("$target.o")
  compiled[$module]=1
}
compile Alvoki/Experiments/L0/Native
for probe in HistoryProbe RecoveryProbe; do
  lean -c "$out/$probe.c" "$probe.lean"
  cc -O1 -fPIC -I"$prefix/include" "$out/$probe.c" "${objects[@]}" \
    native/{fsync,read_dir_checked,sstable}.c .lake/build/native/libalvoki_crc32c.a \
    -lstdc++ -L"$prefix/lib/lean" -Wl,-rpath,"$prefix/lib/lean" -lleanshared -o "$out/$probe"
done

"$out/HistoryProbe"
cc -shared -fPIC "$fixtures/cut-truncate.c" -ldl -o "$out/cut-truncate.so"
cc -shared -fPIC native/l0_interrupt_fixture.c -ldl -o "$out/cut-sync.so"

expect_exit() {
  local expected=$1 actual=0
  shift
  "$@" || actual=$?
  if (( actual != expected )); then
    printf 'Expected exit %s, observed %s\n' "$expected" "$actual" >&2
    exit 1
  fi
}
for policy in logOnly boundary; do
  store="$out/$policy"
  mkdir "$store"
  "$out/RecoveryProbe" seed "$store" "$policy"
  segment="$store/wal/segment-1/segment"
  original_size=$(stat -c %s "$segment")
  printf '\377' >> "$segment"
  expect_exit 75 env LD_PRELOAD="$out/cut-truncate.so" "$out/RecoveryProbe" check "$store"
  expect_exit 73 env LD_PRELOAD="$out/cut-sync.so" ALVOKI_L0_CUT=data "$out/RecoveryProbe" check "$store"
  [[ $(stat -c %s "$segment") == "$original_size" ]]
  for attempt in 1 2; do
    "$out/RecoveryProbe" check "$store"
  done
  printf '%s recovery: exits 75,73; restored %s bytes; both reopens passed\n' "$policy" "$original_size"
done

strace -f -qq -yy -e trace=openat,close,fsync,rename -o "$out/manifest.trace" .lake/build/bin/manifestNativeCheck
python3 "$fixtures/check-trace.py" "$out/manifest.trace"

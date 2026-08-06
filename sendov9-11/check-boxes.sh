#!/bin/sh
# Kernel-check the degree-10/11 box certificates, one file at a time — the same way they
# were certified (see VERIFICATION.md Part II). Re-checks only boxes without a clean
# axiom footprint in certlogs1011/, so it is safe to interrupt and resume.
#
# Usage:   ./check-boxes.sh [10|11|all]     (default: all)
# Cost:    ~53 s per box single-threaded on the certification machine.
# WARNING: do not raise -P above 4 — parallel `lake env lean` above that has produced
#          spurious infrastructure failures (bad_alloc, olean read races) on Windows.
cd "$(dirname "$0")"
which=${1:-all}
mkdir -p certlogs1011

# The boxes import Sendov911Bern by module name; build its olean first and put the build
# tree plus the box directories on LEAN_PATH.
lake build Sendov911Bern || exit 1
LP="$(lake env printenv LEAN_PATH)"
case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) SEP=';' ;;
  *) SEP=':' ;;
esac
export LEAN_PATH="$LP${SEP}.lake/build/lib/lean"

# NOTE: the degree-11 v1 boxes (boxes11/, c4 = 70/3) were superseded by boxes11v2/
# (c4 = 1447/50) and removed from the working tree; use ./check-boxes11v2.sh for
# degree 11. This script now covers degree 10 only.
for d in boxes10; do
  [ "$which" = all ] || [ "$d" = "boxes$which" ] || continue
  for f in "$d"/Sendov911Box*_*.lean; do
    base=$(basename "$f")
    log="certlogs1011/$base.log"
    if [ -s "$log" ] && grep -q 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' "$log"; then
      continue
    fi
    echo "$f"
  done
done | xargs -P 3 -I{} sh -c 'f={}; b=$(basename "$f"); lake env lean "$f" > "certlogs1011/$b.log" 2>&1; echo "$? $b" >> certlogs1011/RESULTS-resume.txt; echo "done $b"'

c10=$(grep -l 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' certlogs1011/Sendov911Box10_*.log 2>/dev/null | wc -l)
echo "degree 10 interior verified clean: $c10 / 50"
echo "(degree 11 v2: run ./check-boxes11v2.sh)"

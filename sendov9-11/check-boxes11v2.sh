#!/bin/sh
# Kernel pass for the regenerated (c4 = 1447/50) degree-11 boxes in boxes11v2/, one file
# at a time — the same way they were certified (logs shipped in certlogs11v2/).
# Re-checks only boxes without a clean footprint, so it is safe to interrupt and resume.
# WARNING: do not raise -P above 4 (see check-boxes.sh).
cd "$(dirname "$0")"
mkdir -p certlogs11v2

# The boxes import Sendov911Bern by module name; build its olean first and put the build
# tree on LEAN_PATH (adapted from the certification machine's flat-layout original).
lake build Sendov911Bern || exit 1
LP="$(lake env printenv LEAN_PATH)"
case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) SEP=';' ;;
  *) SEP=':' ;;
esac
export LEAN_PATH="$LP${SEP}.lake/build/lib/lean"

for f in boxes11v2/Sendov911Box11_*.lean boxes11v2/Sendov911Box11Boundary.lean; do
  b="$(basename "$f")"
  log="certlogs11v2/$b.log"
  if [ -s "$log" ] && grep -q 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' "$log"; then
    continue
  fi
  echo "$f"
done | xargs -P 3 -I{} sh -c 'b="$(basename {})"; lake env lean {} > "certlogs11v2/$b.log" 2>&1; echo "$? $b" >> certlogs11v2/RESULTS11V2.txt'
echo "verified clean: $(grep -l 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' certlogs11v2/Sendov911Box11*.log | wc -l) / 531"

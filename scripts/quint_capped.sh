#!/bin/bash
# Elaborate one Lean file with a hard wall-clock cap (SIGKILL) and low priority, so that a check
# that does not finish cannot keep the machine busy.
# Usage: scripts/quint_capped.sh FILE.lean [SECONDS=120] [THREADS=4]
cd "$(dirname "$0")/.."
f=$1; cap=${2:-120}; threads=${3:-4}
# cvc5's native library, for commands that call the solver in-process (as `lake build` does)
dyn=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib
[ -f "$dyn" ] || dyn=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so
LEAN_NUM_THREADS=$threads nice -n 10 lake env lean ${dyn:+--load-dynlib="$dyn"} "$f" &
pid=$!
( sleep "$cap"; pkill -9 -f "lean $f" && echo "KILLED after ${cap}s: $f" >&2 ) 2>/dev/null &
wd=$!
wait $pid; code=$?
kill $wd 2>/dev/null; pkill -P $wd 2>/dev/null
exit $code

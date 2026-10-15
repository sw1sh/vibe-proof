#!/bin/bash
# usage: run1.sh <inner-timeout-seconds> <command...>
# Waits up to ~12 s for any other lean/lake compile process to finish, then runs the
# command under `timeout`, measuring wall time and peak RSS with /usr/bin/time -l.
busy() {
  ps -axo pid,command | grep -E "/bin/(lean|lake)( |$)" | grep -vE -- "--server|lake serve|grep" | grep -v "^ *$$ "
}
for i in 1 2 3 4 5 6 7 8 9 10 11 12; do
  b="$(busy)"
  [ -z "$b" ] && break
  sleep 1
done
b="$(busy)"
if [ -n "$b" ]; then
  echo "BUSY: another lean/lake process is running; not starting"
  echo "$b"
  exit 99
fi
t="$1"; shift
/usr/bin/time -l timeout "$t" "$@" 2> >(grep -E "real|maximum resident" >&2)
rc=$?
echo "rc=$rc"
exit $rc

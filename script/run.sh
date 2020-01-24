#!/usr/bin/env bash

# Settings/Utilities
# ------------------

# terminate on error
set -e

# error if an variable is referenced before being set
set -u

# set variables
top_dir="$(pwd)"
benchmark_dir="$top_dir/../benchmark"

progress() { echo "===== " $@ ; }

# timeout with SIGKILL
time_out() {
  (
  if
    timeout -s SIGKILL $1 ${@:2};
  then
    echo "================== Done ==================" 1>&2
    echo "================== Done =================="
  else
    echo "
    Error:
      Timeout Occured
================== Done ==================" 1>&2
    echo "
    Error:
      Timeout
================== Done =================="
  fi
  )
}

thread() {
  mkdir -p $benchmark_dir/out
  echo "================== Run  ==================
    Settings:
      model: $3Linear,
      bound: $1,
      solver: $2,
      path: $benchmark_dir/model/linear/$3Linear.model"
  echo "================== Run  ==================
    Settings:
      model: $3Linear,
      bound: $1,
      solver: $2,
      path: $benchmark_dir/model/linear/$3Linear.model" > "$benchmark_dir/out/$3_$1_linear_$2"
  time_out 15s stlmc -l $1 -u $1 -solver $2 -logic "linear" \
  "$benchmark_dir/model/linear/$3Linear.model" -visualize true -log true >> "$benchmark_dir/out/$3_$1_linear_$2"
}


# Main
# ----

command="$1" ; shift
case "$command" in

    railroad) thread              "$@" ;;
    *)      echo "
    usage: $0 <options>

    $0 railroad <bound> <solver> <logic>:   run railroad benchmark model with <bound>, <solver>, and <logic> options.
" ;;
esac
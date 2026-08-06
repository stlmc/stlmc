#!/usr/bin/env bash

# Settings/Utilities
# ------------------

# Stop immediately on command, unset-variable, or pipeline failures.
set -euo pipefail

# set variables
top_dir="$(pwd)"
src_dir="$(pwd)/src"

third_party="$top_dir/3rd_party"


# functionality
progress() { echo "===== " $@ ; }

prepare() {
    get_antlr
    get_dreal3
}

#
get_antlr() {
  progress "Get Antlr4"
  antlr_dir="$third_party/antlr4"
  
  mkdir -p "$antlr_dir"
  curl --fail --location --show-error \
    --output "$third_party/antlr4/antlr4-13.2-complete.jar" \
    https://www.antlr.org/download/antlr-4.13.2-complete.jar

  target=$src_dir/stlmc/syntax

  cd "$target"
  (
    java -jar "$antlr_dir/antlr4-13.2-complete.jar" -Dlanguage=Python3 ./model/model.g4 -no-listener -visitor
    java -jar "$antlr_dir/antlr4-13.2-complete.jar" -Dlanguage=Python3 ./config/config.g4 -no-listener -visitor
    java -jar "$antlr_dir/antlr4-13.2-complete.jar" -Dlanguage=Python3 ./visualize/visualize.g4 -no-listener -visitor
  )
}

# build tecla
get_dreal3() {
  progress "Get dReal3"
  mkdir -p "$third_party/dReal3"
  cd "$third_party/dReal3"
  ( 
    os=$(uname)
    if [[ "$os" == "Darwin" ]]; then
      curl --fail --location --show-error \
        --output "dReal-3.16.06.02-darwin.zip" \
        https://github.com/dreal/dreal3/releases/download/v3.16.06.02/dReal-3.16.06.02-darwin.zip
      unzip "dReal-3.16.06.02-darwin.zip"
      mv dReal-3.16.06.02-darwin/bin/dReal ./dReal && rm -rf dReal-3.16.06.02-darwin.zip dReal-3.16.06.02-darwin
    else
      curl --fail --location --show-error \
        --output "dReal-3.16.06.02-linux.tar.gz" \
        https://github.com/dreal/dreal3/releases/download/v3.16.06.02/dReal-3.16.06.02-linux.tar.gz
      tar -xvzf "dReal-3.16.06.02-linux.tar.gz" 
      mv dReal-3.16.06.02-linux/bin/dReal ./dReal && rm -rf dReal-3.16.06.02-linux.tar.gz dReal-3.16.06.02-linux
    fi
  )
}

# Follow the below steps
#  1. prepare

# Main
# ----

build_command="$1" ; shift
case "$build_command" in
    prep)               prepare                   "$@" ;;
    *)      echo "
    usage: $0 [prep]
           $0 script <options>

    $0 prep     :   prepare STLmc
" ;;
esac

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

runLinear() {
  stlmc -l 1 -u 10 -solver $2 -logic "linear" \
  "$benchmark_dir/model/linear/$1Linear.model" -visualize true -log true
}

runPoly() {
  stlmc -l 1 -u 10 -solver $2 -logic "nonlinear" \
  "$benchmark_dir/model/linear/$1Poly.model" -visualize true -log true
}

runAll() {

  # linear
  runLinear railroad yices
  runLinear railroad z3

  runLinear twoBattery yices
  runLinear twoBattery z3

  runLinear twoCar yices
  runLinear twoCar z3

  runLinear twoThermostat yices
  runLinear twoThermostat z3

  runLinear twoWatertank yices
  runLinear twoWatertank z3

  # non linear
  runPoly railroad yices
  runPoly railroad z3

  runPoly twoBattery yices
  runPoly twoBattery z3

  runPoly twoCar yices
  runPoly twoCar z3

  runPoly twoThermostat yices
  runPoly twoThermostat z3

  runPoly twoWatertank yices
  runPoly twoWatertank z3
}


# Main
# ----

command="$1" ; shift
case "$command" in

    benchmark) runAll                               "$@" ;;
    railroadLinear) runLinear railroad              "$@" ;;
    railroadPoly) runPoly railroad                  "$@" ;;
    twoBatteryLinear) runLinear twoBattery          "$@" ;;
    twoBatteryPoly) runPoly twoBattery              "$@" ;;
    twoCarLinear) runLinear twoCar                  "$@" ;;
    twoCarPoly) runPoly twoCar                      "$@" ;;
    twoThermostatLinear) runLinear twoThermostat    "$@" ;;
    twoThermostatPoly) runPoly twoThermostat        "$@" ;;
    twoWatertankLinear) runLinear twoWatertank      "$@" ;;
    twoWatertankPoly) runPoly twoWatertank          "$@" ;;
    *)      echo "
    usage:

    $0 benchmark :
      run all benchmark model with bound 1 to 10 using z3 and yices solver.
    $0 railroadLinear <solver> :
      run railroadLinear benchmark model with bound 1 to 10 using a <solver> option.
    $0 railroadPoly <solver> :
      run railroadPoly benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoBatteryLinear <solver> :
      run twoBatteryLinear benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoBatteryPoly <solver> :
      run twoBatteryPoly benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoCarLinear <solver> :
      run twoCarLinear benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoCarPoly <solver> :
      run twoCarPoly benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoThermostatLinear <solver> :
      run twoThermostatLinear benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoThermostatPoly <solver> :
      run twoThermostatPoly benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoWatertankLinear <solver> :
      run twoWatertankLinear benchmark model with bound 1 to 10 using a <solver> option.
    $0 twoWatertankPoly <solver> :
      run twoWatertankPoly benchmark model with bound 1 to 10 using a <solver> option.

" ;;
esac
#!/bin/bash
python3.5 twoThermostatNon.py
../2.Watertank/dReal-3.16.04-linux/bin/dReal twoThermostatNon_noSTL.smt2 --short_sat --delta_heuristic --delta --sat-prep-bool


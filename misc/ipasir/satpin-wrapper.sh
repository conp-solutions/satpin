#!/usr/bin/env bash
# Norbert Manthey, 2017
#
# This script calls a IPASIR linked SATPin with the required input
#
# usage: satpin-sat2017-wrapper.sh SATPINBINARY INPUTQUERY BENCHMARKDIRECTORY
#
# SATPINBINARY ......... path to the binary that should be used
# INPUTQUERY ........... basename of the query file that should be used for the call
# BENCHMARKDIRECTORY ... path to the directory where the .cnf, .assumptions, and query files are stored
#

SATPIN="$1"
PROBLEM="$2"
BENCHDIR="$3"

# basic check whether we have all parameters
if [ -z "$BENCHDIR" ] || [ -n "$4" ]; then
  echo "error: not enough parameters specified (expected 3): $*"
  echo "usage: $0 SATPINBINARY INPUTQUERY BENCHMARKDIRECTORY"
  exit 1
fi

# static parameters
ontology=full
param="-keepSearch -ipasir -no-minimal"

# call the solver
echo "run: ./$SATPIN $BENCHDIR/$ontology.cnf -assumptions=$BENCHDIR/$ontology.assumptions -question=$BENCHDIR/$PROBLEM $param"
./$SATPIN "$BENCHDIR"/$ontology.cnf -assumptions="$BENCHDIR"/$ontology.assumptions -question="$BENCHDIR"/"$PROBLEM" $param

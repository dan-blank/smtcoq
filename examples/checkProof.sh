#!/bin/bash
set -e
#set -x
# 1 and 2 inconsistency
if [ -z "$1" ]
then
    echo "No input formula was supplied. Please input a .smt2 file."
    exit 1
fi
if [ -z "$2" ]
then
    echo "No input proof was supplied. Please input a .smt2 file."
    exit 1
fi
# necessary?
formulaname=${1%.smt2}
proofname=${2%.smt2}

cat > proofchecker.v <<EOF
Require Import SMTCoq.SMTCoq.
Section File.
Smtinterpol_Checker "$formulaname.smt2" "$proofname.smt2".
End File.
EOF

echo "Checking SMTInterpol proof with Coq directly..."

coqc proofchecker.v

exit 0

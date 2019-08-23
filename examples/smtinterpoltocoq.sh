#!/bin/bash
set -e
set -x
# 1 and 2 inconsistency
if [ -z "$1" ]
then
    echo "No SMTInterpol jar supplied."
    exit 1
fi
if [ -z "$2" ]
then
    echo "No input formula was supplied. Please input a .smt2 file."
    exit 1
fi
# necessary?
name=${1%.*}
smtinterpoljarpath=$2

echo "Running SMTInterpol... "
# -q should subsume -w
java -jar $smtinterpoljarpath -o produce-proofs=true -w -no-success -q -smt2 $name.smt2 | sed -n '1!p' >> smtinterpolproof

echo "Creating the Coq file."

cat > ${name}.v <<EOF
Require Import SMTCoq.SMTCoq.
Section File.
Smtinterpol_Checker "$name.smt2" "smtinterpolproof".
End File.
EOF

echo "Checking SMTInterpol proof with Coq directly..."

coqc ${name}.v

exit 0

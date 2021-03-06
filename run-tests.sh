#!/bin/bash


Normal () { printf '\e[m'"$*"; }
Tred () { printf '\e[0;31m'"$*"'\e[m'; }
Tgreen () { printf '\e[0;32m'"$*"'\e[m'; }
Tbrown () { printf '\e[0;33m'"$*"'\e[m'; }

test_out=/tmp/test_out
test_err=/tmp/test_err
diff="git diff"

failed=0
oks=0

RunTest () {
  test_runner=$1
  test=$2
  expected=$3

  Tbrown "> Running a test for "
  Tgreen $test "\n"
  $test_runner $test > $test_out 2>&1
  exit_code=$?
  if [ $exit_code -ne 0 ]; then
    Tred "Program Failed\n\n"
    Tbrown "Exited with exit code: $exit_code \n"
    Tbrown "STDERR: >>>\n"
    cat $test_err
    Tbrown "STDERR: <<<\n"
    continue
  fi

  $diff $expected $test_out
  if [ $? -eq 0 ]; then
    Tgreen "OK\n"
    ((oks++))
  else
    Tred "FAIL\n"
    ((failed++))
  fi

  echo
  echo
  echo
}

for test_file in tests/tests/scanner/input/*; do
  RunTest "./run.sh -t scan" $test_file tests/tests/scanner/output/`basename $test_file`.out
done

for test_file in tests/tests/scanner-hidden/input/*; do
  RunTest "./run.sh -t scan" $test_file tests/tests/scanner-hidden/output/`basename $test_file`.out
done


echo
echo
echo -----------------------------------
Tgreen "$oks passed "
Tred "$failed failed\n"

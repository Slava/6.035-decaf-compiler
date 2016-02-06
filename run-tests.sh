#!/bin/bash

SCRIPT=./tests/tests/scanner/test.sh
sed -i '' 's/tempfile/mktemp XXXX/' $SCRIPT
$SCRIPT
sed -i '' 's/mktemp XXXX/tempfile/' $SCRIPT


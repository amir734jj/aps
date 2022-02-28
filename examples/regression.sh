#!/bin/bash

# declare an array called files, that contains 3 values
files=( "first" "follow" "nested-cycles" "simple-oag" "simple-coag"
        "local-fiber-cycle" "below-fiber-cycle" "below-single-fiber-cycle"
        "broad-fiber-cycle" "simple-binding"
        "simple-binding1" "simple-binding2" "simple-binding3" )

for i in "${files[@]}"
do
  echo "=> Working on $i.aps"
  ../bin/apssched -p .:../base -DTo $i
  echo 
done || exit 0

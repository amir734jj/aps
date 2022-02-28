#!/bin/bash

files=( "first" "follow" "nested-cycles" "simple-oag" "simple-coag"
        "local-fiber-cycle" "below-fiber-cycle" "below-single-fiber-cycle"
        "broad-fiber-cycle" "simple-binding"
        "simple-binding1" "simple-binding2" "simple-binding3"
        "cool-noinherit-semant" )

for i in "${files[@]}"
do
  echo "=> Working on $i.aps"
  ../bin/apssched -p .:../base $i
  echo 
done || exit 0

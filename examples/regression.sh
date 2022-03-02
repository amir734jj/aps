#!/bin/bash

primary=( "first" "follow" "nested-cycles" "simple-oag" "simple-coag"
        "local-fiber-cycle" "below-fiber-cycle" "below-single-fiber-cycle"
        "broad-fiber-cycle" )

misc=( "simple-binding" "simple-binding1" "simple-binding2" "simple-binding3"
      "cool-noinherit-semant" )

files=()

if [[ $1 = "all" ]]; then
  files=("${primary[@]}" "${misc[@]}")
else
  files=(${primary[@]})
fi

for i in "${files[@]}"
do
  echo "=> Working on $i.aps"
  ../bin/apssched -p .:../base $i
  echo 
done || exit 0

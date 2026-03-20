#!/bin/sh

# usage : ./test.sh [typechecker]

err=0
nb=0

for file in ./pass/*.mle; do
    "$1" "$file" 2> "$file".err
    if [ "$?" = 1 ]; then
       err=$((err+1))
       echo "test $file failed"
    fi
    nb=$((nb+1))
done

for file in ./fail/*.mle; do
    "$1" "$file" 2> "$file".err
    if [ "$?" = 0 ]; then
       err=$((err+1))
       echo "test $file failed"
    fi
    nb=$((nb+1))
done

echo "failed $err tests out of $nb"

[ "$err" = 0 ]

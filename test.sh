#!/bin/sh

# usage: ./test.sh [typechecker] [test directory]

err=0
nb=0

if [ "$#" -ne 2 ] || ! [ -x "$1" ] || ! [ -d "$2" ]; then
    echo "usage: ./test.sh [typechecker] [test directory]"
    exit 1
fi

for file in "$2/pass/"*.mle; do
    "$1" "$file" 2> "$file".err
    if [ "$?" -ge 1 ] ; then
       err=$((err+1))
       echo "test $file failed"
    fi
    nb=$((nb+1))
done

for file in "$2/fail/"*.mle; do
    "$1" "$file" 2> "$file".err
    if [ "$?" = 0 ]; then
       err=$((err+1))
       echo "test $file failed"
    fi
    nb=$((nb+1))
done

echo "failed $err tests out of $nb"

[ "$err" = 0 ]

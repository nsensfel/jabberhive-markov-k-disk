#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

while true
do
   rm -f $1
   valgrind --leak-check=full $SCRIPT_DIR/jh-markov-k-disk $1 $2 $3
   sleep 60
done

#!/bin/bash

CURRENT_DIRECTORY=$(cd `dirname $0` && pwd)

if [[ "$#" != "1" ]];
then
   echo "Expected single argument: socket file."
   exit
fi

while true
do
   rm -f $1
   # Run with listenin socket on $1 and Markov rank 3.
   $CURRENT_DIRECTORY/bin/jabberhive-markov-k-ram $1 3
done

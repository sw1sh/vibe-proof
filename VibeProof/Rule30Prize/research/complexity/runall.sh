#!/bin/bash
# all primitive binary words up to rotation, length 2..5, not constant
for w in 10 100 110 1000 1100 1110 10000 11000 10100 11100 11010 11110; do
  for L in 10 14 18; do
    timeout 60 ./leftsearch $w $L 110 0 | head -1
  done
done

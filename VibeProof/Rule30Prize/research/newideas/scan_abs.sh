#!/bin/zsh
while read w; do ./absorb_c $w 3000 24 200 9; done < $1

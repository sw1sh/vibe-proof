# Coordinator findings during round 1 (2026-10-15)

Scripts: /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/driven/

1. Driven halves (left_driven.py): the left half driven by any periodic word (from the seed) keeps column -1
   aperiodic over 6000 steps. So "periodic center column ⇒ periodic column -1" is false for the driven
   left half, and Jen cannot be applied via the left side for general words.

2. Absorbing words, right half (absorb_map.py, absorb_long.py), random right-half starts with the cone edge:
   - Period 4: 0001 and 0011 make column 1 eventually periodic from all 10 random starts (within ~400
     steps); 0111 does NOT (1 of 10).
   - Length 8: absorbing in 3 random trials: 00000001, 00000011, 00000101, 00011101, 00011111, 00111101,
     00111111 (00110111 mixed). Length 5: 01111. Lengths 2, 3, 6, 7: none (001 mixed).
   - After absorption (driver 0001) there is a fixed "skeleton" of forced (column, phase) cells, identical
     across trials: columns 1-3 fully periodic (0011, 0110, 1101), columns 4-11 partially forced
     (0*0*, ***1, 01**, ***1, 000*, **11, 0**0, 11*1), columns ≥ 12 free. Driver 0011 gives the same
     skeleton shifted by one column.

3. Finite certificate attempt (adversary_fix.py): columns 1..K exact, column K+1 adversarial (any bits),
   driver 0001. A closed set where column 1 follows a fixed pattern (0011, and from K = 18 also 0001)
   exists from K = 16 on: once entered, column 1 stays periodic against any environment. But not every
   state is forced to enter it: attracted fraction 2.9% (K=16), 7.7% (K=18), 12.6% (K=20), 17.3% (K=22).
   So with an adversarial environment there is no finite-K proof of universal absorption; a rigorous
   exclusion of eventual period 0001 would need extra structure of the real right half (the environment
   is not arbitrary), or a proof that the real dynamics cannot avoid the closed set forever.

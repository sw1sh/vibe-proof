import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g2369 import *
# relators listed for G2369 (2006 and 2008), in a, b, c; X^-1 written as the capital letter
rels = ['AbAb', 'BcBc', 'BcAbAc', 'AAbbABab', 'AAbaBBab', 'AcAcAcAc', 'BcAcBcAc', 'AbaBAbbA',
        'ABab' * 2]
for r in rels:
    print(r, 'as written:', is_trivial(elt(r)), ' reversed:', is_trivial(elt(r[::-1])))
for w in ['a', 'b', 'c', 'ab', 'aB', 'cC', 'hk', 'khkh', 'khkhkhkh', 'ABab']:
    print(w, is_trivial(elt(w)))

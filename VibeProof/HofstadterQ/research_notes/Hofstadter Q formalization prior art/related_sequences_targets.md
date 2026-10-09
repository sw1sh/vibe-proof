# Relatives of Hofstadter's Q-sequence with proven totality, slowness or structure, and their value as Lean 4 + Mathlib formalization targets

Provenance tags used on every finding:
- **[P]** I read it in the primary source: the paper's full text via arXiv/JIS/EJC PDF, or the authors' own abstract, README or certificate files.
- **[S]** Secondhand: OEIS, a zbMATH review, Wikipedia, publisher or Crossref metadata, a search-result summary, or a later paper's description of an earlier one.
- **[C]** A light local Python check run in this session (2026-10-10). No files were saved.

Paywalled items I could not read in full are Mallows 1991, Kubo–Vakil 1996, Tanny 1992, Conolly 1989, Grytczuk 2004, Ruskey 2011, Isgur et al. 2016 and Golomb's manuscript. Everything I say about them is [S].

## Q1. Conway's $10,000 sequence A004001: what is proven, by whom, and which proofs are short or long?

### Takeaway
Totality of Conway's sequence is a three-line triviality, and both Mallows and Kubo–Vakil say so explicitly. Its slowness is a short Monthly-problem argument. The deep content is the asymptotics a(n)/n → 1/2 with the explicit threshold n₀ = 1490 (last violation at n = 1489). Those proofs run 16 pages (Mallows 1991) and 28 pages (Kubo–Vakil 1996, via a "compression operation"). It is a good formalization showcase, but it says almost nothing about Q's totality.

### Cited Findings
- **Definition.** a(1)=a(2)=1, a(n) = a(a(n−1)) + a(n−a(n−1)). OEIS A004001. [P] — [OEIS A004001](https://oeis.org/A004001)
- **History of the prize.** At a Bell Labs colloquium on 15 Jul 1988, Conway said he could prove a(n)/n → 1/2 "but that the proof was extremely difficult". He offered $100 for any n₀ with |a(n)/n − 1/2| < 0.05 for all n ≥ n₀, and $10,000 for the least such n₀. He "meant to say $1000". "The prize was claimed by Colin Mallows, who agreed not to cash the check." (Sloane, OEIS comment, 2015.) [S] — [OEIS A004001](https://oeis.org/A004001)
- **Mallows's paper.** C. L. Mallows, "Conway's challenge sequence", Amer. Math. Monthly 98 (1991) 5–20, which is 16 pages. [S] — [Crossref/JSTOR 10.2307/2324028](https://doi.org/10.2307/2324028)
- **zbMATH review of Mallows.** It says Δa(n) ∈ {0,1} and a(n)/n → 1/2, and that the author studies A(n)=2a(n)−n and D(n)=2Δa(n)−1 "using diagrams and empiric arguments". [S] — [zbMATH 0738.11014](https://zbmath.org/?q=an:0738.11014)
- **The 1489 fact.** The last n with |a(n)/n − 1/2| ≥ 1/20 is n = 1489, so the least n₀ is 1490. The coordinator's session check already verified this numerically (see 00_session_findings.md). A search-result summary also attributes N(1/20)=1489 and N(1/40)=6,083,008,742 to Mallows's Monthly article. I did not verify the N(1/40) value. [S] — [skrause.org Conway page (search result)](https://skrause.org/math/conway.shtml)
- **Wikipedia's account.** It says Mallows proved |a(n)/n − 1/2| = O(1/√log n). I could not check this against Mallows's text. [S] — [Wikipedia: Hofstadter sequence](https://en.wikipedia.org/wiki/Hofstadter_sequence)
- **Slowness.** a(n) − a(n−1) ∈ {0,1} was D. Newman's Problem E3274, Amer. Math. Monthly 95 (1988) 555. The solution is by D. J. Kleitman, Monthly 98 (1991) 958–959, about 2 pages. [S] — [OEIS A004001 references](https://oeis.org/A004001)
- **Totality is trivial, and the authors say so.** Pelesko notes that "Both authors [Mallows; Kubo–Vakil] note that c(n) ≤ n and then go on to say 'so that c(n) is well-defined by the recurrence.'" [P] — [Pelesko, JIS 7 (2004) 04.3.5](https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.pdf)
- **Kubo–Vakil.** T. Kubo and R. Vakil, "On Conway's recursive sequence", Discrete Math. 152 (1996) 225–252, which is 28 pages. [S] — [Crossref DOI](https://doi.org/10.1016/0012-365X(94)00303-Z)
  - zbMATH review: the paper "introduces a compression operation on finite sets, from which most known properties of this famous sequence can be read off. This is the first combinatorial insight toward understanding the Conway-Mallows sequence and its generalizations." [S] — [zbMATH 0852.05010](https://zbmath.org/?q=an:0852.05010)
  - Pelesko's summary of Kubo–Vakil: "The use of a compression operation to characterize the sequence allowed for simple proofs of many of A004001's interesting properties." [P] — [Pelesko 2004](https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.pdf)
  - Pelesko lists these properties, taken from Kubo–Vakil: (1) c(n) ≤ n; (2) c(n) − c(n−1) ∈ {0,1}; (3) c(n) ≥ n/2, with equality iff n is a power of 2 and n ≠ 1; (4) c(n)/n → 1/2. [P] — [Pelesko 2004](https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.pdf)
- **Powers of 2.** a(2^n − i) = 2^(n−1) for 0 ≤ i ≤ n−1, and a(2^n + 1) = 2^(n−1) + 1. This formula is due to Cloitre (2002) and was corrected by Alkan (2017). [S] — [OEIS A004001](https://oeis.org/A004001)
- **A conflicting OEIS entry.** OEIS still lists "a(n) = n/2 iff n = 2^k" as a 2019 conjecture by Forgues. Pelesko attributes the equivalent equality case of property (3) to the Kubo–Vakil list. [S] — [OEIS A004001](https://oeis.org/A004001); [Pelesko 2004](https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.pdf)
- **Generalizations with totality and slowness proofs.**
  - Isgur–Rahman, EJC 18 (2011) P96, 10 pages. They study A(n) = A(n−a−A^k(n−b)) + A(A^k(n−b)) and C(n) = C(n−s−C(n−1)) + C(n−s−2−C(n−3)). They prove that, under suitable initial conditions, both are "defined for all positive integers, and be monotonic with their forward difference sequences consisting only of 0 and 1". [P] — [arXiv 1407.0425](https://arxiv.org/abs/1407.0425)
  - Isgur, Lech, Moore, Tanny, Verberne and Zhang, SIAM J. Discrete Math. 30 (2016) 1128–1147. They give a general method that turns any known slow generalized-Conolly or generalized-Conway recursion into a family of recursions with slow solutions, and apply it to the V and Conway recursions. [S] — [Crossref abstract, DOI 10.1137/15M1040505](https://doi.org/10.1137/15M1040505)
  - Grytczuk 2004, Discrete Math. 282, 149–161, a triply nested variant. [S] — [DOI](https://doi.org/10.1016/j.disc.2003.10.022); [Cloitre 2604.06237 intro](https://arxiv.org/abs/2604.06237)
  - Pelesko 2004 k-sequences. [P] — [Pelesko 2004](https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.pdf)
  - Alkan–Fox–Aybar 2017, "heart sequences", which subtract Q from Conway's sequence. This is exploratory. [S] — [Crossref, Complexity 2017](https://doi.org/10.1155/2017/2614163)
- **Formalization status.** facebookresearch/atlas-lean (created 2026-05-26) has `MathlibExt/NumberTheory/ConwayHofstadterLikeSequence.lean`. It contains only the predicate `IsConwayHofstadterLikeSequence k c` for Pelesko's k-sequences (k=1 is Conway-like) and no theorems. [P] — [atlas-lean file](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ConwayHofstadterLikeSequence.lean)

### Inferences
- **Short proofs:** totality (3 lines), slowness (about 1–2 pages), and the a(2^k) identities (short inductions once slowness and the block structure are known).
- **Long proofs:** a(n)/n → 1/2 and the explicit N(ε) (16–28 pages, plus computation).
- A Lean proof of "the least n₀ for ε = 1/20 is 1490" would need both the asymptotic theory, to show there are no violations after 1489, and a finite check, which `decide` can handle at this size.
- The recurrence shape a(a(n−1)) differs from Q's n − Q(n−k) lookbacks, and totality is trivial. Formalizing Conway therefore teaches little about Q-totality, though it is a good warm-up for slowness-induction infrastructure.

### Gaps
- I could not read Mallows's or Kubo–Vakil's full text, because ScienceDirect and JSTOR returned 403. Exact theorem statements, the error-term statement (Wikipedia's O(1/√log n)) and the rigor of Mallows's treatment rest on secondary sources. zbMATH's phrase "diagrams and empiric arguments" suggests that parts of Mallows's analysis may be informal, but I could not confirm this.
- N(1/40) = 6,083,008,742 is unverified.

## Q2. Hofstadter–Huber V-sequence A063882: what BKT 2007 proves, how, and whether Allouche–Shallit gives an independent route

### Takeaway
Balamohan, Kuznetsov and Tanny (BKT) prove V is slow by a self-contained, elementary simultaneous induction on two difference statements. The proof takes about 3.5 pages (pp. 5–8 of a 29-page paper) with a base table up to n = 20, and slowness immediately gives totality. The frequency sequence and the "generations" come afterwards and are not needed for totality. Allouche–Shallit's 2-automaticity result concerns the frequency sequence F, not V, and takes BKT's frequency rules as input. It is therefore not an independent or shorter route to totality.

### Cited Findings
- **Definition.** V(1)=V(2)=V(3)=V(4)=1 and V(n) = V(n−V(n−1)) + V(n−V(n−4)) for n > 4. This is the Hofstadter–Huber sequence Q_{1,4}, OEIS A063882. [P] — [BKT, JIS 10 (2007) 07.7.1](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html)
- **Paper size.** The BKT PDF is 29 pages. [P] — [BKT PDF](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf)
- **What the abstract claims.** [P] — [BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html)
  - V is monotone, its increments are 0 or 1, and it hits every positive integer.
  - Structural properties and periodicities of the frequency sequence allow V(n) to be computed iteratively.
  - V partitions naturally into "generations", blocks in which "terms in one block determine the terms in the next".
  - For every other set of four initial conditions that yields a solution, "the resulting sequence is essentially the same as the one with initial conditions all ones".
- **Theorem 1, the totality-relevant result.** (4) V(n) − V(n−1) ∈ {0,1} for n > 1, and (5) V(n) − V(n−3) ∈ {1,2} for n > 8. [P] — [BKT p. 5](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf)
  - The proof is "a multi-statement induction proof on both (4) and (5) simultaneously". The base is Table 3: (4) holds for n ≤ 20 and (5) for 9 ≤ n ≤ 20.
  - The induction step uses Pinn's "mother/father spot" terminology.
  - It splits (4) into Case 1, V(n−2) = V(n−4)+2, and Case 2, V(n−2) = V(n−4)+1. These apply after the reduction V(n−1)=V(n−2), V(n−4)=V(n−5), and V(n−V(n−1)) = V(n−1−V(n−2)) + 1.
  - It splits (5) into three cases on V(n−1) − V(n−3).
  - The proof spans pp. 5–8 and uses only integer equalities and inequalities.
- **Prior unpublished proof.** BKT's footnote says the result "was first observed in 1999 by Hofstadter and Huber". Huber described their unpublished proof as "a long, tedious, case by case tracking down of many branches of cases and sub-cases" using "K-tables" (after Kellie Gutman). [P] — [BKT p. 5 footnote](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf)
- **Further results.** [P] — [BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf); [OEIS A063882](https://oeis.org/A063882)
  - Corollaries 2–4 cover mother/father spot sequences; mother and father differ by 0, 1 or 2.
  - Proposition 5: n/2 < V(n) ≤ n/2 + log₂ n − 1 for n > 6.
  - Corollary 6: lim V(n)/n = 1/2.
- **Frequency sequence.** F(a) ∈ {1,2,3}. Lemmas 7–19 cover local and "remote" properties. Table 5 and Table 7 ("Gutman's rules", first conjectured by K. O'Connor Gutman, Math. Intelligencer 23(3), 2001) compute F(2a) and F(2a+1) from F(a−2..a+1). Section 4 develops the generations. [P] — [BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf); [OEIS A063882](https://oeis.org/A063882)
- **The Hofstadter–Huber conjecture and W.** For all-ones initial conditions, the only (r,s) for which Q_{r,s} does not die are conjectured to be (1,2), (1,4) and (2,4). The (2,4) case, W = A087777, "appears to display even more inscrutably wild behavior … to date nothing has been proved about this sequence". [P] — [BKT p. 2](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf); OEIS: "It is not known if this sequence is defined for all positive n." [S] — [OEIS A087777](https://oeis.org/A087777)
- **Allouche–Shallit's publication data.** "A variant of Hofstadter's sequence and finite automata", J. Aust. Math. Soc. 93 (2012) 1–8. arXiv 1103.1133, v2 dated 2011-06-13, 9 pages. [P] — [arXiv 1103.1133](https://arxiv.org/abs/1103.1133); [Crossref DOI 10.1017/s1446788713000074](https://doi.org/10.1017/s1446788713000074)
- **What Allouche–Shallit take as input.** They quote BKT's Lemmas 13–19 and Table 5 as their "Theorem 1": explicit maps g, h : {1,2,3}⁴ → {1,2,3} with F(2a) = g(F(a−2), F(a−1), F(a), F(a+1)) and F(2a+1) = h(…) for a > 3. They also correct quantifiers in BKT's Lemma 13. [P] — [arXiv 1103.1133 PDF](https://arxiv.org/pdf/1103.1133v2)
- **What they prove.** A general criterion (their Theorem 4), giving Corollary 7: "The sequence F = (F(n)) is 2-automatic". They give an automaton A, minimized to a 20-state automaton B. Correctness has two parts. Part (a) "can be verified by a computation, which we omit". Part (b) "requires a tedious simultaneous induction … we omit most of the details". [P] — [arXiv 1103.1133 PDF](https://arxiv.org/pdf/1103.1133v2)
- **What they leave open.** "It would be interesting to know whether the first difference sequence … (V(n+1) − V(n)) is also 2-automatic." [P] — [arXiv 1103.1133 PDF](https://arxiv.org/pdf/1103.1133v2)
- **Correction to the session notes.** 00_session_findings.md says "Allouche–Shallit show it [V] is 2-automatic". In the body, the automatic object is the frequency sequence F (A132157). The paper's abstract speaks loosely of the "variant" being 2-automatic. [P] — [arXiv 1103.1133](https://arxiv.org/pdf/1103.1133v2)
- **Later context.** Campbell–Cloitre (2026) build "meta-automatic sequences" around the Allouche–Shallit automaticity criterion. [P] — [arXiv 2602.23395 abstract](https://arxiv.org/abs/2602.23395)
- **Precedent for an automata route.** A 2026 Lean 4 development checks kernel-verified automaton certificates for another nested recurrence (see Q7). [P] — [arXiv 2609.33421](https://arxiv.org/abs/2609.33421)

### Inferences
- **Slowness gives totality.** With V(1..4)=1, Theorem 1(4) gives 1 ≤ V(n) ≤ n − 3 for n ≥ 4. Both lookback indices then lie in [1, n−1], so totality follows. Only BKT pp. 5–8 is needed.
- **Lean shape.** A Lean proof is an elementary case analysis (omega/linarith-friendly), plus a `decide` base table for n ≤ 20, plus the usual partiality design. Either use a padded total definition and prove the padding is never triggered, or prove ∃ f satisfying a relational spec. My rough estimate is a few hundred to about 1,000 lines. That is an estimate, not a measurement.
- **Allouche–Shallit is downstream of BKT.** Formalizing it would start from BKT's slowness and Lemmas 7–19. An automata-based totality proof of V would need V itself, or its difference sequence, to be automatic or synchronized, which A–S explicitly leave open.

### Gaps
- I found no paper after 2012 resolving whether V(n+1) − V(n) is 2-automatic, and none giving a Walnut proof of V's slowness. Absence from my searches is not proof of nonexistence.
- I did not read BKT's Section 6 proof for "all other sets of four initial conditions" in detail.

## Q3. Tanny's sequence A006949 (Tanny 1992, "A well-behaved cousin of the Hofstadter sequence")

### Takeaway
Tanny proved slowness, an exact block-length rule, and T(n)/n → 1/2 in a 13-page Discrete Math. paper. Later papers reproved and generalized this combinatorially, via binary trees and compact codes, with Das 2011 being a 12-page reproof. Because the recurrence is "shifted", slowness proofs are easier than for V. It is a good warm-up but farther from Q.

### Cited Findings
- **Definition.** a(n) = a(n−1−a(n−1)) + a(n−2−a(n−2)) for n > 2, with a(0)=a(1)=a(2)=1. OEIS A006949. [P] — [OEIS A006949](https://oeis.org/A006949)
- **Paper.** S. M. Tanny, Discrete Math. 105 (1992) 227–239, 13 pages. [S] — [Crossref DOI](https://doi.org/10.1016/0012-365X(92)90145-6)
- **zbMATH review.** Tanny proves T(n+1) = T(n) or T(n)+1 for every n > 0, that "there are exactly x+2 consecutive integers n for which T(n) = 2^x", and that T(n)/n → 1/2. [S] — [zbMATH 0766.11008](https://zbmath.org/?q=an:0766.11008)
- **OEIS notes.** OEIS says "See Higham–Tanny 1993 for updates and corrections". It lists other initial triples (X,Y,Z) that give nontrivial sequences and notes that "Most other initial values do not produce a nontrivial sequence". [S] — [OEIS A006949](https://oeis.org/A006949)
- **Callaghan–Chew–Tanny.** SIAM J. Discrete Math. 18 (2005) 794–824, 31 pages. They study T_{a,k}(n) = Σ_{i=0}^{k−1} T(n−i−a−T(n−i−1)) with all-ones initial conditions. Tanny's recurrence is (a,k) = (1,2) and Conolly's is (0,2). The case a = 0, k odd is "analyzed in detail, giving a complete characterization … the first time that such a parametric family … has been solved". [S] — [Crossref abstract](https://doi.org/10.1137/S0895480103421397)
- **Das 2011.** "A combinatorial approach to the Tanny sequence", DMTCS 13(2) 97–108, 12 pages. It reproves Tanny's results combinatorially through a tree-leaf interpretation (T(n) = number of true leaves of a tree VLR(n), from Chandran–Das–Ruskey) and generalizes them. [P] — [Das 2011](https://doi.org/10.46298/dmtcs.547)
- **[C] Local check.** A006949 is slow up to n = 10^6.

### Inferences
- Tanny's T appears as the s = 1 member of the Jackson–Ruskey family (Q4). That gives three proof routes: Tanny's induction, a tree count, or Jackson–Ruskey's explicit word D_{n+1} = 0 D_n D_n.
- For Lean, I expect a direct induction or the word characterization to be cheaper than infinite labelled trees.

### Gaps
- I could not read Tanny 1992 or Higham–Tanny 1993, so the length and structure of Tanny's induction are unverified, as is what Higham–Tanny corrected.

## Q4. Conolly's sequence A046699 and the tree/compact-code interpretations: which slow families have the cleanest totality proofs?

### Takeaway
Conolly's sequence is the classic "shifted" slow sequence: m occurs 1 + ν₂(m) times. Its slowness was a 1990 Canadian MO problem, so a one-to-two-page induction exists. Jackson–Ruskey (2006) give a one-page tree proof and an explicit word description. Isgur–Reiss–Tanny (2009, 40 pp.) and Erickson et al. (2012, 33 pp.) extend the tree method to large families. For Lean, the olympiad-style induction or the explicit-word route is likely the cleanest. The tree bijections are short on paper, but they rest on pictorial "chopping the last level" arguments that need nontrivial infinite-tree infrastructure.

### Cited Findings
- **Definition.** a(1)=a(2)=1 and a(n) = a(n−a(n−1)) + a(n−1−a(n−2)). OEIS A046699. Except for the first term, n occurs A001511(n) = 1 + ν₂(n) times. [S] — [OEIS A046699](https://oeis.org/A046699)
- **Original source.** B. W. Conolly, "Meta-Fibonacci sequences", in S. Vajda, *Fibonacci & Lucas Numbers and the Golden Section* (1989), pp. 127–138. [S] — [OEIS A004001 refs](https://oeis.org/A004001)
- **Canadian MO 1990, Problem 5.** f(1)=1, f(2)=2, f(n+2) = f(n+2−f(n+1)) + f(n+1−f(n)). (a) Prove 0 ≤ f(n+1) − f(n) ≤ 1, and that f(n+1) = f(n)+1 if f(n) is odd. (b) Find all n with f(n) = 2^10 + 1. OEIS credits these properties of A046699 to this problem. [P] — [IMO Compendium, CanMO 1990](https://imomath.com/othercomp/Can/CanMO90.pdf); [OEIS A046699](https://oeis.org/A046699)
- **Jackson–Ruskey 2006.** "Meta-Fibonacci sequences, binary trees and extremal compact codes", EJC 13 R26, 13 pages. [P] — [arXiv math/0504400](https://arxiv.org/abs/math/0504400)
  - They study a_s(n) = a_s(n−s−a_s(n−1)) + a_s(n−s−1−a_s(n−2)). The case s = 0 is Conolly and s = 1 is Tanny.
  - a_s(n) counts leaves at the largest level in an infinite forest of complete binary trees of sizes 1, 1, 3, 7, …, labelled in preorder, with super-nodes of size s.
  - Theorem 2.1 states the recurrence for n > s+2, with base values a_s(n)=1 for n ≤ s+1 and a_s(s+2) = 2.
  - The proof of Theorem 2.1 is about one page and uses "chopping the last level", with Cases 1a/1b/2a/2b on whether n−1 and n are leaves.
  - They also give the string characterization D₀ = 1, D_{n+1} = 0 D_n D_n, generating functions, and the link to Norwood's compact codes.
- **Isgur–Reiss–Tanny 2009.** "Trees and meta-Fibonacci sequences", EJC 16 R129, 40 pages. [P] — [EJC R129 PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v16i1r129)
  - They treat C(n) = Σ_{p=1}^k C(n − a_p − C(n − b_p)).
  - For k = 2 they give "compelling empirical evidence that solutions exist only for two particular families of parameters".
  - All recursions in these families "count the number of labels on the leaves of certain infinite labeled trees", which yields closed forms and asymptotics.
  - The structure is a sequence of pruning lemmas (Lemmas 3.1–3.4: T* = T up to relabelling; R*(n − qj) = R(n − s − (q−1)j − R(n − qj))).
- **Erickson, Isgur, Jackson, Ruskey and Tanny 2012.** "Nested recurrence relations with Conolly-like solutions", SIAM J. Discrete Math. 26, 206–238, 33 pages. [P] — [arXiv 1509.02613](https://arxiv.org/abs/1509.02613)
  - A sequence is (α,β)-Conolly if the frequency of m is α + β(1 + ν₂(m)).
  - For fixed k and p_i, only finitely many (α,β) are possible.
  - They give a bijective tree proof that H(n) = H(n−H(n−2)) + H(n−3−H(n−5)) also has the Conolly solution.
  - For k = 2 and p₁ = p₂ they construct an (α,β)-Conolly recursion for every possible pair.
- **Related results.**
  - Deugau–Ruskey 2009, JIS 12 09.4.3, k-ary trees. [S] — [OEIS A046699](https://oeis.org/A046699)
  - Isgur–Rahman–Tanny 2013, non-homogeneous recursions via trees. [S] — [OEIS A046699](https://oeis.org/A046699)
  - Fox 2022, JDEA, 48 pages, generalizes the classical examples to families parametrized by linear recurrences. These can be built three ways: nested recurrence, labelled infinite trees, or Zeckendorf-like frequency strings. [P] — [arXiv 2203.09340](https://arxiv.org/abs/2203.09340)
  - Celaya–Ruskey 2013 interpret a nested family, including Conolly and Tanny, as fixed points of morphisms. [P] — [arXiv 1307.0153](https://arxiv.org/abs/1307.0153)
- **Fox's assessment of slowness proofs.** "There are two methods commonly used to prove that Hofstadter-like sequences are slow … counting leaves in nested tree structures. The sequence counting the leaves is obviously slow; the main difficulty comes in showing that the nested recurrence also describes the same structure … The other proofs of slowness usually go by induction with complicated inductive hypotheses … [the bare hypothesis Δ ∈ {0,1}] is never enough … While the 'shifted' sequences have similar proofs to each other, the proof for the Hofstadter V-sequence uses a different sort of inductive hypothesis." [P] — [Fox, arXiv 1609.06342](https://arxiv.org/abs/1609.06342)
- **[C] Local checks.** A046699 is slow up to n = 10^6. The CanMO version (f(1)=1, f(2)=2) is slow, and f(n) odd ⇒ f(n+1) = f(n)+1, up to n = 10^6.

### Inferences
- **Cleanest totality proofs for Lean, in order.** (1) The CanMO-style strong induction for Conolly, probably 200–500 lines. (2) The Jackson–Ruskey or Celaya–Ruskey explicit-word or morphic description: define the increment word, prove the recurrence by induction on levels. (3) Tree bijections, which need formal infinite labelled trees, preorder labels and pruning lemmas. The Isgur–Reiss–Tanny generality is 40 pages.
- **Closeness to Q is moderate.** The −1 shift in the second term is what makes these sequences tame, as Fox notes. Their proofs do not transfer to Q, which is not slow.

### Gaps
- I did not read Conolly's 1989 chapter or check whether it proves slowness or only observes it.
- I did not compare the official CanMO solution's length.

## Q5. The Q-recurrence with other initial conditions: Golomb, Ruskey, Fox's families, and known dying initial conditions

### Takeaway
Golomb's [3,2,1] gives a period-3 quasilinear solution that is total under Hofstadter's own convention. Its totality proof is a three-case algebraic check, essentially trivial in Lean. Two conventions must be kept apart:
- Ruskey's Fibonacci embedding [3,6,5,3,6,8] and Fox's higher-degree quasipolynomial solutions exist only under the convention Q(n) = 0 for n ≤ 0. Under Hofstadter's "undefined" convention, Ruskey's dies at n = 7.
- Fox (2020) proves a parametric death theorem with a short symbolic proof. The Q-recurrence with initial condition 1, 2, …, N dies for N = 8, 11, 12 and every N ≥ 14.

### Cited Findings
- **Golomb.** S. W. Golomb, "Discrete chaos: sequences satisfying 'strange' recursions", unpublished manuscript, circa 1990/91. With Q(1..3) = 3, 2, 1 the solution is Q(3k) = 3k−2, Q(3k+1) = 3, Q(3k+2) = 3k+2, which satisfies a_n = 2a_{n−3} − a_{n−6}. [P, Fox's description] — [Fox, arXiv 1609.06342](https://arxiv.org/abs/1609.06342); [Fox, arXiv 1807.01365](https://arxiv.org/abs/1807.01365); [OEIS cached copy of Golomb](https://oeis.org/A005185/a005185_1.pdf)
- **[C] Golomb checks.** Under the undefined convention it survives to n = 20,000. The period-3 closed form checks numerically. By hand, each residue class reduces to one line:
  - Q(3k+3) = Q(1) + Q(3k) = 3 + 3k − 2.
  - Q(3k+1) = Q(3) + Q(2) = 3.
  - Q(3k+2) = Q(3k−1) + Q(4) = (3k−1) + 3.
  This agrees with the session note's indexing (Q(3k+3) = 3k+1).
- **Ruskey.** F. Ruskey, "Fibonacci meets Hofstadter", Fibonacci Quart. 49(3) (2011) 227–230. The initial condition ⟨0̄; 3, 6, 5, 3, 6, 8⟩ (zeros at nonpositive indices) gives Q(3k) = F_{k+4}, Q(3k+1) = 3, Q(3k+2) = 6, which satisfies a_n = 2a_{n−3} − a_{n−9}. [P, Fox's description] — [Fox 1609.06342](https://arxiv.org/abs/1609.06342); [Fox 1807.01365](https://arxiv.org/abs/1807.01365)
- **[C] Ruskey checks.** Without the zero convention, Ruskey's initial condition dies at n = 7, because Q(7) needs Q(7 − Q(6)) = Q(−1). With zeros it runs (checked to n = 300, with 196 reads of nonpositive indices), and the terms 5, 8, 13, 21, … appear at positions 3k.
- **Fox, quasipolynomial solutions.** Integers 16 (2016) A68 (arXiv 1511.06484, 7 pages) constructs eventual quasipolynomial solutions of every positive degree, stating "Throughout this paper … we will use the convention that Q(n) = 0 for n ≤ 0". [P] — [arXiv 1511.06484](https://arxiv.org/abs/1511.06484)
- **Fox, symbolic method.** J. Symbolic Comput. 87 (2018) 99–126 (arXiv 1609.06342) gives an algorithm and a Maple package (`nicehof`) that find infinite families of interleaved linear-recurrent solutions. The paper says "the proofs in the second case [eventually linear-recurrent] are highly automatable". [P] — [arXiv 1609.06342](https://arxiv.org/abs/1609.06342)
- **Fox, linear-recurrent subsequences.** JDEA 2016 (arXiv 1508.01840) answers Ruskey's question affirmatively for linear recurrences with positive coefficients. [P] — [arXiv 1508.01840](https://arxiv.org/abs/1508.01840)
- **Fox 2020, Theorem 1.** "A new approach to the Hofstadter Q-recurrence", Integers 20A (2020) A8 (arXiv 1807.01365, 32 pages). [P] — [arXiv 1807.01365](https://arxiv.org/abs/1807.01365)
  - Q_N, the sequence with initial condition 1, 2, …, N, dies for N = 8, 11, 12, or N ≥ 14.
  - For N ≥ 21 it has exactly N + 28 terms; for 14 ≤ N ≤ 20 it has exactly N + 32 terms.
  - Proof: compute 28 terms symbolically as functions of N, valid for N ≥ 13. Then Q_N(N+29) needs Q_N(21 − N), which is undefined for N ≥ 21. Four more symbolic steps handle 14 ≤ N ≤ 20. N = 8, 11 and 12 are concrete computations: Q₈(420) = 430, Q₁₁(199) = 206, Q₁₂(69) = 77.
  - N ∈ {2, …, 7, 9, 10, 13} remain unknown, and all last at least 30 million terms. Q₂ and Q₃ are Hofstadter's Q without its first term.
  - Theorem 2 characterizes ⟨0̄; 1..N⟩ for large N under the zero convention.
- **[C] Fox 2020 check.** The lengths match exactly: 420, 199 and 69 terms for N = 8, 11 and 12; N+32 for 14–20; N+28 for 21–30. N ∈ {2–7, 9, 10, 13} all survive to 2·10^5.
- **Other dying examples.**
  - Q_{2,3} with all ones (A063892) is "undefined for n > 54 since a(53) = 69 ≥ 55". [S] — [OEIS A063892](https://oeis.org/A063892)
  - The Hofstadter–Huber all-ones conjecture is in Q2. [P] — [BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html)
  - Alkan–Aybar–Akdeniz 2022 (extended abstract) study "control of mortality" for H(n) = H(n−H(n−2)) + H(n−H(n−3)). [P, abstract only] — [arXiv 2211.06092](https://arxiv.org/abs/2211.06092)
- **Undecidability.** Celaya–Ruskey 2012 show that, for the specific nested recurrence A(n) = A(n−4−A(A(n−4))) + 4A(A(n−4)) + A(2A(n−4−A(n−2)) + A(n−2)), it is undecidable whether a given finite initial condition yields a "calculable" (total) sequence, by simulating Post 2-tag systems. [P, abstract] — [arXiv 1203.0586](https://arxiv.org/abs/1203.0586)
- **Alkan's generalizations.** Alkan 2018 (Open Math. 16, 1490–1500; Complexity 2018) proposes generalizations and conjectures about infinitely many solutions. These are statistical or conjectural, not totality proofs. [S] — [Crossref abstract, Open Math](https://doi.org/10.1515/math-2018-0124); [Crossref abstract, Complexity](https://doi.org/10.1155/2018/8517125)

### Inferences
- **Short inductive totality proofs under Hofstadter's convention.** Golomb's [3,2,1] (three residue cases), and presumably the quasilinear members of Fox's symbolic families that never read nonpositive indices. Fox calls these proofs "highly automatable", so a generator that emits Lean proofs from Fox's symbolic certificates is plausible.
- **The zero convention changes the problem.** Ruskey's and the higher-degree quasipolynomial solutions do not count as "total" in Hofstadter's sense. Totality there means "never self-referential", a different and weaker property. Any formal statement must fix the convention explicitly.
- **Fox 2020 is a cheap, novel negative result.** Its Theorem 1 is parametric in N (symbolic `omega`/`simp` reasoning) plus three concrete `decide` computations, the largest needing 420 terms. It would show that formal Q-recurrence infrastructure handles death as well as life.

### Gaps
- I could not read Golomb's manuscript or Ruskey's paper directly, so their descriptions are via Fox (an author in the area). I did not check whether Golomb's manuscript contains further proven-dying or proven-total initial conditions.
- I found no published proof that any of Q_N for N ∈ {4,…,7, 9, 10, 13} is total or dies.

## Q6. Fox's slow relative (B-recurrence) and other Fox results proving slowness or totality

### Takeaway
Fox (JIS 2017) proves that B(n) = B(n−B(n−1)) + B(n−B(n−2)) + B(n−B(n−3)) with B(i) = i for i ≤ 5 is slow. He also characterizes its frequency sequence exactly: m appears twice iff m = k·3^i + a_i, else once. The proof is a roughly 10-page induction. B has no shifts and no positive inner coefficient, which makes it, after V, the closest "pure" Q-type slow sequence. Fox's other results are solution constructions, mostly under the zero convention, and parametric death theorems.

### Cited Findings
- **Paper.** N. Fox, "A Slow Relative of Hofstadter's Q-Sequence", J. Integer Seq. 20 (2017) Art. 17.7.3 (arXiv 1611.08244, 15 pages). [P] — [arXiv 1611.08244](https://arxiv.org/abs/1611.08244); [JIS 17.7.3](https://cs.uwaterloo.ca/journals/JIS/VOL20/Fox/fox2.html)
- **Definition.** B(n) = B(n−B(n−1)) + B(n−B(n−2)) + B(n−B(n−3)) with B(1..5) = 1, 2, 3, 4, 5. OEIS A278055. [P] — [arXiv 1611.08244](https://arxiv.org/pdf/1611.08244v1)
- **Theorems.** [P] — [arXiv 1611.08244](https://arxiv.org/pdf/1611.08244v1)
  - Theorem 1: B is slow.
  - Theorem 2: let a₁ = 3 and a_i = 3a_{i−1} − 1, so a_i = (5/2)·3^{i−1} + 1/2. Then m appears twice if m = k·3^i + a_i for some k ≥ 1, i ≥ 1, and once otherwise; B is monotone.
  - The proof is by induction on propositions P_m (through value m) and T_n (through index n), using "witness pairs", Lemmas 1–6, and cases on m mod 3. It spans roughly pp. 3–12.
  - Theorem 3: B is the only nontrivial slow sequence from the k-term recurrence B_k with initial condition B_k(i) = i for i ≤ N.
  - Proposition 1: k ≥ 4 is not slow.
- **Fox's reason for choosing B.** Most known slow sequences have an inner positive coefficient (Conway-like) or a shift (Conolly-like). "The only ones that have neither property are the V-sequence and sequences constructed from it." [P] — [arXiv 1611.08244](https://arxiv.org/pdf/1611.08244v1)
- **[C] Local checks.** B is slow up to n = 10^6, and Theorem 2's frequency rule holds for every m < 666,673.
- **Fox 2024.** B with initial conditions 1..N: "our sequences are all finite for sufficiently large N". This is a complete characterization for large N, with data on GitHub. [P] — [arXiv 2406.00904](https://arxiv.org/abs/2406.00904)
- **Other Fox results.** [P] — [Fox 2024 references](https://arxiv.org/pdf/2406.00904v1); [arXiv abstracts](https://arxiv.org/abs/2203.09340)
  - Quasipolynomial solutions (Integers 2016) and the symbolic linear-recurrent families (JSC 2018); see Q5.
  - Parametric death of Q_N (Integers 2020); see Q5.
  - Slow solutions tied to linear recurrent sequences (JDEA, arXiv 2203.09340); see Q4.
  - PhD thesis (Rutgers 2017), "An exploration of nested recurrences using Experimental Mathematics".

### Inferences
- **B for Lean.** B is a strong second-tier target: three-term Q shape, initial conditions 1..5, no shifts, and novel. Its proof is longer and more number-theoretic than V's (3-adic witness bookkeeping), perhaps 1–3k Lean lines (my estimate).
- **A possible automata route (speculative).** Theorem 2's frequency rule is a base-3 digit condition. B might therefore be 3-automatic or synchronized, in which case Walnut plus a Lean kernel check of automaton certificates (as in Q7) could give a mechanized alternative proof. Nobody has done this as far as I found.

### Gaps
- I did not verify that Fox's talk "Hofstadter-like Sequences over Nonstandard Integers" (cited in 00_session_findings.md) contains proven totality or slowness results.
- I found no Walnut or automata proof for B.

## Q7. Formalization precedents: Hofstadter G, H, F_k (Letouzey) and other proof-assistant work on nested recurrences

### Takeaway
Two developments formalize nested recurrences, both in cases where totality is trivial. Letouzey's Rocq development covers G, H and F_k (2015–2026). Cloitre–Ma–Zhang's September 2026 Lean 4 development covers A076502, with kernel-checked automata certificates, only the standard axioms, and no `native_decide`. I found no proof-assistant formalization of any relative where totality is nontrivial (V, Conolly, Tanny, B, Golomb, A394051), nor of Conway's slowness or asymptotics.

### Cited Findings
- **Letouzey's `letouzey/hofstadter_g`.** A Coq/Rocq development "started in summer 2015", covering G, its generalizations F_k, and morphic words extending the Fibonacci word. It depends on Coquelicot. [P] — [GitHub README](https://github.com/letouzey/hofstadter_g)
  - Letouzey–Li–Steiner, "Pointwise order of generalized Hofstadter functions G, H and beyond", JIS 29 (2026) Art. 26.3.3, proves F_k(n) ≤ F_{k+1}(n) and states: "We provide a certified formalization of all these results in the Rocq proof assistant." [P] — [arXiv 2410.00529](https://arxiv.org/abs/2410.00529)
  - Letouzey 2025 (discrepancy and numeration systems) solves two OEIS conjectures about F₃ and F₄. [P] — [arXiv 2502.12615](https://arxiv.org/abs/2502.12615)
- **Cloitre, Ma and Zhang (2026-09-27).** "A Padovan-automatic description of a nested recurrence", arXiv 2609.33421, 14 pages. It studies a(n) = n − a(n − a(n − a(n−1))) (A076502). [P] — [arXiv 2609.33421](https://arxiv.org/abs/2609.33421)
  - The Lean development "checks canonical greedy representations, recognition, carry and delay semantics, finite-language inclusion and projection, totality, and identification with the literal nested recurrence". It also proves the offset set, morphic identity, balance constant 4, and so on.
  - "Final theorem axiom closures contain only propext, Classical.choice, and Quot.sound. No admitted proofs, extra axioms, or native decision axioms are used. Kernel reduction checks the generated finite certificates."
  - It uses Lean 4.33.0 with a pinned Mathlib commit, and Walnut 7.1.0 as an independent cross-check. The authors disclose use of Claude, GPT-5.6 and GPT-6 Astra (via Codex).
  - The package is on Zenodo under DOI 10.5281/zenodo.22979217. That record returned HTTP 504 when I tried it, so I could not inspect it.
- **atlas-lean.** It contains only a definition of Pelesko's Conway–Hofstadter-like k-sequences, with no theorems (see Q1). [P] — [atlas-lean](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ConwayHofstadterLikeSequence.lean)
- **GitHub code search (2026-10-10).** Searches for "Hofstadter" in Lean, Coq and Isabelle, and for "Conolly", "metaFibonacci", "HofstadterConway", the CanMO recurrence text and "Mantovanelli", found only the items above, plus formal-conjectures Erdős 422/423, Mathlib's MIU archive and Letouzey's repository. Compfiles has no Canada 1990 P5. [P] — [compfiles](https://github.com/dwrensha/compfiles); [formal-conjectures 422](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/422.lean)
- **A Walnut precedent.** A 2025 paper on the Narayana morphism verifies an automaton for Hofstadter's H-sequence (A005374) in Walnut. [S, search-result summary] — [arXiv 2503.01026](https://arxiv.org/pdf/2503.01026)

### Inferences
- **The Cloitre–Ma–Zhang pipeline is directly reusable.** It runs from a Python/Walnut-discovered automaton or finite certificate, through Lean kernel-checked finite-language inclusion, to identification with the literal nested recurrence, with no `native_decide`. It applies to any relative whose structure is automatic or synchronized, and possibly to the finite kernel of Mantovanelli's certificate (Q8).
- **Lean conventions to borrow.** These precedents show that a padded total definition plus a "spec" predicate and kernel `decide` certificates is a workable Lean pattern. It matches the session's own QDefinition and QKernelDecide experiments.

### Gaps
- GitHub code search indexes only part of GitHub, and private or Isabelle-AFP-style hosting may be missed. "Not found" means not found by these searches.
- I did not search the Isabelle AFP index or the Lean Zulip directly.

## Q8. Mantovanelli's parity-perturbed Q (A394051): proofs, formalization difficulty, and whether the Zenodo certificate can be imported and checked by `decide` or `native_decide`

### Takeaway
A394051 (Q(1)=Q(2)=1, Q(n) = Q(n−Q(n−1)) + Q(n−Q(n−2)) + (−1)^n) now has two independent 2026 proofs of well-definedness, both unrefereed preprints.
- **Mantovanelli (v3, 27 pp.)** gives a computer-assisted return-word induction. The finite kernel is tiny and easily `decide`-able in Lean, but most of the formalization work is in about 13 pages of all-level word inductions and gluing. Versions 1 and 2 contained a gap that the author acknowledges.
- **Cloitre (v3, 50 pp.)** gives a direct, self-contained, certificate-free human proof. Well-definedness takes only Sections 2–3 (pp. 5–14) and uses explicit recursively defined binary words, a two-tape interleaving, and Dyck-height invariants.
For Lean, the Cloitre route is the better primary path, and Mantovanelli's certificate is a useful independent cross-check.

### Cited Findings
- **Sequence and OEIS entry.** OEIS A394051, "Hofstadter Q-sequence perturbed by (−1)^n". "All terms are odd." It "does not terminate for all n ≤ 3·10^10 (verified computationally)". The terms are 1,1,1,3,3,3,5,5,5,7,5,9,7,9,7,11,9,11,11,11. [S] — [OEIS A394051](https://oeis.org/A394051); [C] the first 20 terms match.
- **Mantovanelli paper and versions.** M. Mantovanelli, "Certified Return-Word Induction for a Perturbed Hofstadter Recursion", arXiv 2603.29622. v1 2026-03-31, v2 2026-05-18, v3 2026-07-22. v3 is 27 pages, 3 figures, math.CO/math.NT, MSC 11B37, 68Q45. [P] — [arXiv abs](https://arxiv.org/abs/2603.29622)
  - OEIS records an earlier title, "Certified Finite-State Induction…". [S] — [OEIS A394051](https://oeis.org/A394051)
  - v3's own version note says the title changed from "finite-state" to "return-word". [P] — [v3 PDF](https://arxiv.org/pdf/2603.29622v3)
- **The acknowledged gap in v1/v2.** v3's version note: "Version 3 replaces the symbolic S → T → U → V closure argument of Version 2. That earlier finite-state abstraction did not by itself establish semantic faithfulness to the recurrence at every future position." Section 12 adds that "closure of the abstract overlap graph did not imply that every future recurrence position realized the required source context". [P] — [v3 PDF](https://arxiv.org/pdf/2603.29622v3)
- **Status regarding unperturbed Q, by version.** [P] — [v1 PDF](https://arxiv.org/pdf/2603.29622v1); [v2 PDF](https://arxiv.org/pdf/2603.29622v2)
  - v1: the perturbation "enables a finite-state reduction that does not appear to be available in the unperturbed case".
  - v2: "the proof does not resolve the well-definedness problem for the classical unperturbed recursion".
  - v3 has no such sentence. This corrects the attribution in 00_session_findings.md, which quotes it without a version.
- **Mantovanelli Layer 1: reduction to a binary system, short and fully human.** [P] — [v3 §2](https://arxiv.org/pdf/2603.29622v3)
  - Define T_n = n − Q(n−1) and s_n = (Q(n+1) − Q(n−1))/2.
  - Lemma 2.1: T_{n+2} = T_n + 2(1 − s_n).
  - Lemma 2.2: s_{n+1} = (1−s_n)·s_{T_n+1} + (1−s_{n−1})·s_{T_{n−1}+2}.
  - Lemma 2.3: the unique bad configuration is (s_{n−1}, s_n, s_{h_n}, s_{k_n}) = (0,0,1,1).
  - Theorem 2.4, the reconstruction principle: any binary solution with T₂=1, T₃=2, s₂=0, s₃=1 gives Q(n) = n + 1 − T_{n+1}, satisfying the recurrence with all arguments in [1, n−1]. The proof uses a 2-periodic residual R_{n+2} − R_n = 0.
- **Mantovanelli Layer 2: the finite local kernel, computer-checked (Proposition 3.4).** [P] — [v3 §3](https://arxiv.org/pdf/2603.29622v3)
  - 21 seven-bit C₇ codes.
  - 13 return-word types, of lengths 2, 31, 8, 10, 39, 20, 30, 40, 20, 30, 31, 40, 39.
  - 92 synchronized states and 122 transition rules.
  - 29 word pairs, giving 52 atom rules.
  - 28,025 semantic A/B-window combinations.
  - 24 ambiguous selector keys, with 0 simultaneously prefix-compatible rule pairs.
  - Finite prefix alignment by direct evaluation of the recurrence up to marker 793 (default checker limit 1200), giving a handoff at block 74.
- **Mantovanelli Layer 3: all-level human inductions.** [P] — [v3 §§5–9](https://arxiv.org/pdf/2603.29622v3)
  - Rank words A_n, B_n and an epoch grammar (§5).
  - Four stationary chunk transductions for all m ≥ 3 (§6), plus six bridge-tail schemas (§7). Together they reduce to 10 zero-loop schemas, each extended by inserting copies of self-loop rule 0 or rule 64.
  - Free-monoid port factorization and absolute-address gluing (§8, Lemma 8.1 to Theorem 8.8).
  - Causality: a role graph with 184 nodes and 244 edges, of which 176 role nodes and 118 rules are reachable. A nonnegative potential with Bellman–Ford finding no negative cycle gives block lag ≥ 38 (§9).
- **Mantovanelli's trusted base and formalization status.** The trusted base is "the mathematical reductions and gluing arguments printed in this paper; … the 122-rule table …; the short deterministic checkers; … the Python runtime". "The result is not claimed to be formalized in Lean, Coq, Isabelle, or HOL." [P] — [v3 §11.1](https://arxiv.org/pdf/2603.29622v3)
- **The Zenodo certificate.** [P] — [Zenodo 10.5281/zenodo.21495335](https://doi.org/10.5281/zenodo.21495335), inspected in memory
  - It is record v3.0.0 (2026-07-22): one zip of 223,189 bytes, about 1.0 MB uncompressed.
  - It needs CPython ≥ 3.11 and no third-party packages. `python run_all_checks.py` runs the checks; the record's description says nine, while RUN_REPORT.md lists ten commands.
  - The record states: "The package is not a Lean, Coq, Isabelle, or HOL formalization. The free-monoid gluing arguments and the final residual reconstruction remain human-readable mathematical arguments in the associated manuscript."
- **Archive contents, as I listed them.** [P] — [Zenodo](https://zenodo.org/records/21495335)
  - About 7,650 lines of Python across 21 checker/generator modules.
  - Kernel data is about 20 KB:
    - `complete_transition_rules_122.csv`: 122 rows, 18 columns, including an `observed_count_to_50m` column. The rules were first observed in traces up to 50M.
    - `basic_cursor_states.csv`: 92 rows.
    - `return_words.json`: 13 words.
    - `atom_rule_table.csv` and `pair_rule_table.csv`.
    - `block_lag_potential_certificate.csv`: 176 role potentials.
  - The two largest files are diagnostic audits (`pi_rho_order_identity_audit.csv` 409 KB; `exact_source_identity_audit.csv` 180 KB). The paper says these diagnostic expansions are "regression tests, not logical hypotheses".
- **The author's own validation status.** [P] — [Zenodo archive](https://zenodo.org/records/21495335)
  - `RUN_REPORT.md` lists ten passing checks totalling about 259 s. `exact_source_identities` alone takes 81 s.
  - `proof_status_matrix_phase17.csv` lists "proof-assistant formalization, not performed, optional validation" and "independent external review, not performed, recommended".
  - The German `proof_obligations_phase17.md` names the lemmas that "could be formalized in Lean, Coq or Isabelle": overlap concatenation, the ten zero-loop inductions, rank-word factorizations, global factor induction, and residual periodicity. It also recommends an independent checker that replays the 25 stationary primitives, 15 tail/connector primitives, 10 loop schemas and 5 seed identities.
- **AI disclosure.** OpenAI's ChatGPT was used for "the development and checking of proof ideas, and the drafting and refactoring of verification code". [P] — [v3 PDF](https://arxiv.org/pdf/2603.29622v3)
- **Cloitre's paper.** B. Cloitre, "The Mantovanelli-Hofstadter Sequence", arXiv 2604.06237. v1 2026-04-04, v3 2026-07-22, 50 pages. OEIS gives the original title as "On a perturbed Hofstadter Q-recursion". [P] — [arXiv 2604.06237](https://arxiv.org/abs/2604.06237); [S] — [OEIS A394051](https://oeis.org/A394051)
  - Theorem 1.1: (i) well-definedness and lim Q̃(n)/n = 1/2; (ii) arch amplitudes W_r = C(2r+1, r) (OEIS A001700); (iii) Q̃(n) = n/2 + O(n/√log n), and the error is not o(n/√log n); (iv) explicit positive bounds on the normalized limsup. [P]
  - Mantovanelli v3 confirms that Cloitre "proved global well-definedness, the limit Q(n)/n → 1/2, and the estimate…". [P] — [Mantovanelli v3 §1](https://arxiv.org/pdf/2603.29622v3)
  - Cloitre calls his paper "a direct self-contained proof without a finite-state certificate". [P] — [Cloitre v3](https://arxiv.org/pdf/2604.06237v3)
- **Cloitre's well-definedness proof (Sections 2–3, pp. 5–14).** [P] — [Cloitre v3 §§2–3](https://arxiv.org/pdf/2604.06237v3)
  - **Parity split (Lemma 2.2).** Let a(m) = (Q̃(2m−1)+1)/2 and b(m) = (Q̃(2m)+1)/2. Then:
    - a(m) = b(m−b(m−1)) + b(m−a(m−1)) − 1 (RA);
    - b(m) = a(m+1−a(m)) + a(m+1−b(m−1)) (RB).
  - **Two-tape interleaving.** Interleave(X, Y, ε) is a two-tape transducer with an "exact fit" notion (Def. 2.3). Heights are additive (Lemma 2.4).
  - **Explicit arch words.**
    - P₀ = 001011.
    - N_r = Interleave(P_r[2:], P_r[0:|P_r|−1], 1).
    - P_{r+1} = Interleave(00 N_r 1, 0 N_r, 0).
    - |P_r| = 2a_r, where a₀ = 3 and a_{r+1} = 4a_r − 1.
    - Positions are u_r = 2a_r − r − 2 and v_r = 4a_r − r − 2.
  - **Dyck invariants and exact fit.** The invariant AP(r) says each P_r is a primitive Dyck word starting with 00. Lemmas 2.6–2.10 prove it at every level and show that neither interleaving uses fallback (exact fit).
  - **Slow sequences and the induction.**
    - Section 3 defines a and b from the arch-word increments.
    - Lemma 3.1: increments are binary and 1 ≤ a(m), b(m) ≤ m.
    - Lemmas 3.2–3.4 give linear bridge identities and parked-head coordinates.
    - Theorem 3.5 proves RA and RB by an arch-by-arch induction, with a finite base table for m ≤ 10.
    - Theorem 3.6 concludes well-definedness and 1 ≤ Q̃(n) ≤ n.
    - No computer certificate is used beyond that 10-row table. Sections 4–8 (Toeplitz forests, ECO rules, asymptotics) are not needed for totality.
- **Companion papers.**
  - Mantovanelli's "A Dyadic Frequency Law…" (arXiv 2603.16111 v3, 20 pages) proves {F(s) : 2^k ≤ s < 2^{k+1}} = {3 + ν₂(j) : 1 ≤ j ≤ 2^k} as multisets, where F(s) = #{n : Q(n) = 2s−1}. Its v3 notes say "Two incorrect ancillary statements … have been removed" and that the proof now rests on "Cloitre's canonical forest structure". [P] — [arXiv 2603.16111](https://arxiv.org/abs/2603.16111)
  - A 40-page zeta-function paper, arXiv 2609.02412, 2026-09-02. [P] — [arXiv 2609.02412](https://arxiv.org/abs/2609.02412)
- **[C] Local checks to n = 10^6.** A394051 is defined, all values are odd, and Q(n+1) − Q(n−1) ∈ {0, 2}, so Mantovanelli's s_n is binary. Cloitre's RA/RB hold and a, b are slow up to m = 5·10^5.

### Inferences
- **Can the certificate be imported and checked?** Yes, for the finite part, and cheaply.
  - The kernel data (122 rules, 92 states, 13 words, 176 potentials, 236 reachable edges) can be emitted as Lean literals by a script.
  - The local checks are all small decidable statements over bounded data: the 21 codes, overlaps, 28,025 windows, the selector-collision audit, and the potential inequality on 236 edges.
  - The 1200-term prefix evaluation is within the session's measured kernel `decide +kernel` capacity (about 3 s for N = 1000).
  - `native_decide` would be trivial. A kernel-only route in the Cloitre–Ma–Zhang style also looks feasible with a careful Nat- or bitvector encoding.
- **The infinite part is the real work.** The ten parameterized loop schemas are simple inductions, but the rank-word, epoch-grammar, free-monoid and absolute-address gluing arguments (§§5–8) are dense. The physical versus logical A/B role swaps and the shared-boundary ⊙ conventions are exactly where v2 failed. They need full formalization; the finite check does not cover them. I estimate the Mantovanelli route at more than 5k Lean lines, with high risk (a guess).
- **The Cloitre route looks shorter and conceptually cleaner.** It needs:
  - lists of booleans and a total Interleave function;
  - height and Dyck predicates and the exact-fit lemma;
  - the level induction for AP(r);
  - the arch-by-arch proof of RA and RB.
  I estimate 3–8k lines (a guess). Its risk is that terse steps ("direct summation gives…") hide gaps, and Lean would expose them, which is itself valuable for an unrefereed preprint.
- **Recommended plan.** Formalize Mantovanelli's Theorem 2.4 (reconstruction principle, about 1 page) and Cloitre's Lemma 2.2 first; both are small and independent. Then do the Cloitre construction, and optionally replay Mantovanelli's finite kernel as a cross-check.
- **Neither route transfers to plain Q.** Both depend on the perturbation forcing odd values and binary increments on each parity class. For unperturbed Q, Q(n+1) − Q(n−1) is not confined to {0, 2}. Both authors say or imply that the reduction does not extend to Q.

### Gaps
- I could not confirm the emergentmind title "A Finite-State Proof of the Well-Definedness…" reported in the session notes.
- Neither 2026 paper has been refereed, and I found no independent review of Cloitre's proof.
- I did not open Cloitre's Section 2 lemma proofs line by line to spot-check rigor. The proofs I read (Lemmas 2.4–2.10, 3.1–3.4, Theorem 3.5) are explicit but terse in places.

## Q9. Other nested recurrences whose totality was open and then proven, or shown to die, 2000–2026

### Takeaway
The main proven-total results are:
- V (observed 1999, proved 2007);
- the Tanny/Conolly families and tree-counted generalizations (2005–2016, 2022);
- Fox's B (2017);
- the Deane–Gentile "diluted Hofstadter" family (2023);
- the parity-perturbed Q (2026, two proofs).
The proven-death results are Fox's parametric families (2020; 2024 for the B-recurrence). General undecidability for a designed nested recurrence (Celaya–Ruskey 2012) frames why each case needs its own argument. Q itself, W = Q_{2,4}, and Q_N for N ∈ {4–7, 9, 10, 13} remain open.

### Cited Findings
- **Deane–Gentile (2023, 17 pages).** They study q(n) = q(n − q(n−1)) + f(n) with q(1) = 1. Theorem 1.3: for every f with property D₀ (f(1) = 0 and f(n+1) − f(n) ∈ {0, 1}), q exists for all n, that is, 1 ≤ q(n) ≤ n. The proof is a set-valued strong induction: Lemma 3.5 shows T_{i,n} ⊂ U_{i,n}, and Corollary 3.6 gives q(n) ∈ {1..n}. The existence proof occupies Sections 2–3 (Lemmas 2.1–3.5, Corollary 3.6), a minority of the 17-page paper; I did not measure exact pages. The abstract adds that the slow condition is "sufficient but not necessary". [P] — [arXiv 2311.13854](https://arxiv.org/abs/2311.13854)
- **Deane–Gentile follow-up (2025, 29 pages)** studies subsets of the set F of admissible f. [P] — [arXiv 2509.17764](https://arxiv.org/abs/2509.17764)
- **V.** See Q2. [P] — [BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html)
- **Tree and induction families of slow sequences.** [P/S] — [arXiv 1407.0425](https://arxiv.org/abs/1407.0425); [arXiv 1509.02613](https://arxiv.org/abs/1509.02613); [Crossref, Isgur et al. 2016](https://doi.org/10.1137/15M1040505); [Crossref, Callaghan–Chew–Tanny 2005](https://doi.org/10.1137/S0895480103421397)
  - Callaghan–Chew–Tanny 2005: T_{0,k}, k odd.
  - Jackson–Ruskey 2006.
  - Deugau–Ruskey 2009.
  - Isgur–Reiss–Tanny 2009.
  - Isgur–Rahman 2011: Conway and Conolly variants proven total and slow.
  - Erickson et al. 2012.
  - Isgur–Kuznetsov–Tanny 2012/13: ceiling-function and non-slow solutions.
  - Isgur–Rahman–Tanny 2013.
  - Isgur et al. 2016: families from V and Conway.
  - Fox 2022.
- **Fox's B-sequence (2017).** See Q6. [P] — [arXiv 1611.08244](https://arxiv.org/abs/1611.08244)
- **Proven deaths.** Fox 2020 (Q_N for N = 8, 11, 12, ≥ 14) and Fox 2024 (B with initial conditions 1..N, all finite for large N). [P] — [arXiv 1807.01365](https://arxiv.org/abs/1807.01365); [arXiv 2406.00904](https://arxiv.org/abs/2406.00904)
- **Parity-perturbed Q (2026).** See Q8. [P] — [arXiv 2603.29622](https://arxiv.org/abs/2603.29622); [arXiv 2604.06237](https://arxiv.org/abs/2604.06237)
- **G-type families with trivial totality.**
  - Cloitre 2025: a(n+1) = n − a^{(m)}(n) + a^{(m+1)}(n) is solved exactly via an arithmetical h(n). [P] — [arXiv 2506.00093](https://arxiv.org/abs/2506.00093)
  - Cloitre–Ma–Zhang 2026: A076502. [P] — [arXiv 2609.33421](https://arxiv.org/abs/2609.33421)
  - Sobolewski–Ulas 2022: f(n) = f(n−f(n−1)) + f(n−2) with f(n) = 1 for n ≤ 1, linked to binary partitions. [P, abstract] — [arXiv 2204.04011](https://arxiv.org/abs/2204.04011)
- **Undecidability.** Celaya–Ruskey 2012; see Q5. [P, abstract] — [arXiv 1203.0586](https://arxiv.org/abs/1203.0586)
- **Still open.**
  - Q (A005185).
  - W = Q_{2,4} (A087777).
  - Pinn's F_{i,j} family, of which only (0,0), (0,1), (1,0), (1,1) "appear well-defined".
  - Q_N for N ∈ {4–7, 9, 10, 13}.
  Sources: [S] — [OEIS A087777](https://oeis.org/A087777); [Wikipedia](https://en.wikipedia.org/wiki/Hofstadter_sequence); [P] — [arXiv 1807.01365](https://arxiv.org/abs/1807.01365)
- **Recent exploratory work with no totality proofs.** Pinn 2026 models Conway, Pinn's D and Q by continuous functional equations. [P] — [arXiv 2603.17509](https://arxiv.org/abs/2603.17509)
- **Not a nested recurrence.** Tang 2026 resolves an Erdős #423-type question about the "Hofstadter consecutive-sum sequence" (A005243). This is the formal-conjectures 423 sequence, not Q. [S, title and listing] — [arXiv 2603.09939](https://arxiv.org/abs/2603.09939)

### Inferences
- **Deane–Gentile is an underappreciated scoped target.** It keeps exactly one of Q's two nested terms and quantifies over all slow forcings f. The proof is a few pages of elementary set induction, and as far as I found it is not formalized.
- **It does not settle Q.** Setting f(n) = Q(n − Q(n−2)) would need that term to be slow, and it is not (Q(11) = 6, Q(12) = 8). Still, it is the closest proven statement "half-way" to Q's own lookback structure.

### Gaps
- I did not read Deane–Gentile's full proof for length and rigor, beyond the theorem and lemma statements.
- I did not survey the 2011–2016 tree papers beyond their abstracts.

## Q10. Ranking: targets for a Lean 4 + Mathlib formalization as a meaningful "scoped result" toward Q's totality

### Takeaway
Best overall target: the **parity-perturbed Q (A394051) via Cloitre's §§2–3 human proof**. It is closest to Q (same recurrence plus (−1)^n, same initial conditions), its totality was open until 2026, both existing proofs are unrefereed and one had a gap, and it has not been formalized.

Best quick win, and recommended first: **Hofstadter–Huber V via BKT Theorem 1**. It is a 3.5-page elementary simultaneous induction for a genuine Q_{r,s} family member, and it builds the slowness and partial-recurrence infrastructure that the A394051 proof reuses.

Next come Fox's B-sequence, Deane–Gentile's diluted Hofstadter, and a pair of small exact-Q-recurrence results (Golomb [3,2,1] total; Fox's Q_N die). These are cheap and novel and make a reusable "Q-recurrence with initial condition" library. Conway, Conolly and Tanny are useful warm-ups but far from Q.

### Cited Findings
- **Ranking table.** The ingredients are cited in Q1–Q9.
  - "Size/source" is the length of the needed argument in the primary source.
  - "Lean estimate" is my own rough guess, not a measurement.
  - "Formalized?" reflects the searches in Q7.

| Rank | Target | Closeness to Q | Totality nontrivial? | Needed proof (size/source) | Machine-checkable certificate | Formalized? | Lean estimate / risk |
|---|---|---|---|---|---|---|---|
| 1 | A394051 parity-perturbed Q, Cloitre route | Highest: same recurrence + (−1)^n, same initial conditions | Yes (open until 2026) | Cloitre §§2–3, about 10 pp., human, base table m ≤ 10 — [arXiv 2604.06237](https://arxiv.org/abs/2604.06237) | Not needed; Mantovanelli kernel available as cross-check | No — [Mantovanelli §11.1](https://arxiv.org/pdf/2603.29622v3) | 3–8k lines; medium-high risk (terse word combinatorics) |
| 2 | Hofstadter–Huber V = Q_{1,4} (A063882), BKT Thm 1 | Very high: two-term Q_{r,s}, all-ones initial conditions, no shift | Yes (observed 1999, proved 2007) | about 3.5 pp. simultaneous induction, base n ≤ 20 — [BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf) | Base table only (`decide`) | Not found | 0.3–1k lines; low risk |
| 3 | Fox B-sequence (A278055) | High: three-term Q analog, initial conditions 1..5, no shift | Yes | about 10 pp. induction plus 3-adic frequency rule — [arXiv 1611.08244](https://arxiv.org/abs/1611.08244) | None published (automata route speculative) | Not found | 1–3k lines; medium risk |
| 4 | Deane–Gentile diluted Hofstadter (∀ slow f) | Medium-high: keeps Q's nested term q(n − q(n−1)) | Yes | Sections 2–3 of a 17-pp. paper, set-valued induction — [arXiv 2311.13854](https://arxiv.org/abs/2311.13854) | None needed | Not found | 0.5–1.5k lines; low-medium risk |
| 5 | Exact Q-recurrence pair: Golomb [3,2,1] total, plus Fox 2020 Q_N dies (N=8, 11, 12, ≥14) | Exact Q-recurrence and Hofstadter convention | Golomb: trivial. Q_N death: short symbolic proof | 3 cases; 28 symbolic terms + `decide` up to 420 terms — [arXiv 1807.01365](https://arxiv.org/abs/1807.01365) | `decide` for N = 8, 11, 12 | Not found | 0.1k + 0.3–0.6k lines; low risk |
| 6 | A394051, Mantovanelli certificate route | Highest | Yes | 27 pp.; §§5–8 all-level gluing is the bulk — [arXiv 2603.29622](https://arxiv.org/abs/2603.29622) | Yes: about 20 KB kernel, `decide`-able; ~7.6k lines of Python checkers — [Zenodo](https://doi.org/10.5281/zenodo.21495335) | No (author lists it as "not performed") | more than 5k lines; high risk (v1/v2 gap history) |
| 7 | Conolly (A046699) / Tanny (A006949) and families | Medium: shifted variants | Mild | CanMO-level induction (1–2 pp.); Tanny 13 pp.; trees: Jackson–Ruskey 1 p., Isgur–Reiss–Tanny 40 pp. — [CanMO 1990](https://imomath.com/othercomp/Can/CanMO90.pdf) | None needed | Not found | 0.2–0.5k lines (induction); trees much more |
| 8 | Conway A004001 | Low: different nesting a(a(n−1)), trivial totality | No (trivial) | Slowness 1–2 pp.; a(n)/n → 1/2 16–28 pp. — [zbMATH 0852.05010](https://zbmath.org/?q=an:0852.05010) | `decide` for the n ≤ 1489 part | Definition only (atlas-lean) | Slowness small; asymptotics large |
| 9 | Allouche–Shallit automaticity of V's frequency sequence; Isgur et al. 2016 families | Derivative of V | n/a | 8 pp. + BKT Lemmas 7–19 — [J. Aust. Math. Soc.](https://doi.org/10.1017/s1446788713000074) | 20-state automaton | Not found | Follow-on to #2 |
| — | G, H, F_k; A076502 | Low (trivial totality) | No | — | — | Yes: Rocq (Letouzey), Lean 4 (Cloitre–Ma–Zhang) — [hofstadter_g](https://github.com/letouzey/hofstadter_g); [arXiv 2609.33421](https://arxiv.org/abs/2609.33421) | Precedents, not targets |

### Inferences
- **Why A394051 ranks first despite more effort.** It is the only total, nontrivial recurrence with Q's exact lookback structure and initial conditions; the perturbation is the only change. A Lean proof would independently verify a 2026 claim with an acknowledged history of gaps, and it would sit naturally next to formal-conjectures' Erdős 422 file. Mantovanelli's own archive names proof-assistant formalization and external review as the outstanding validation steps.
- **Why V first in practice.** Its proof is short and elementary, `omega`-friendly, and needs no word combinatorics. It exercises the key design decisions: partial versus padded definitions, the relational spec "∃ f, IsSpec f", and kernel `decide` for base tables. It would be the first formal totality proof for any Hofstadter–Huber Q_{r,s} sequence.
- **Shared infrastructure.** A small library could serve ranks 1–5 and 7 together: a convention-faithful `IsSolution (lookbacks) (ic) f`; "total ⟺ ∀ n, Q(n) ≤ n − (shift)"; uniqueness; and a generic "slow + base ⇒ total" lemma. It would also let the formal-conjectures Erdős 422 file state the missing `∃ f, IsHofstadterQ f` cleanly.
- **What none of these establishes.** None says anything new about Q itself. Every known totality proof exploits a slowness-type invariant (binary increments, possibly per parity class) that Q lacks, since Q(12) − Q(11) = 2 and later Q decreases. As a "scoped result toward Q" each is a formally verified instance of the method frontier, not a step that composes into Q's totality.

### Gaps
- All Lean size estimates are my own unvalidated guesses. No one has published Lean line counts for any of these targets.
- I could not inspect the Cloitre–Ma–Zhang Zenodo package (HTTP 504), which would be the best guide to encoding automata certificates for kernel checking.
- Whether V, B, Conolly or Tanny are automatic or synchronized, which would give a Walnut-to-Lean mechanized route, is unknown or open for V's differences. I found no work deciding it for B.

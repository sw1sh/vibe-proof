# Hofstadter's Q-sequence (OEIS A005185): mathematical state of the art, 1977 to October 2026

Researched 2026-10-10. **Tags:** [P] means I read it in the primary source: paper text, the author's own arXiv, OEIS or Zenodo metadata, or an author's own post. [S] means secondhand: a third party's summary, an aggregator, an unrefereed forum post, or a summarizer's paraphrase of a page I could not read in full. [Session] marks facts already in `00_session_findings.md`; these are not re-derived, only corrected or extended. Q̃ denotes the parity-perturbed sequence Q̃(n)=Q̃(n−Q̃(n−1))+Q̃(n−Q̃(n−2))+(−1)^n, Q̃(1)=Q̃(2)=1 (OEIS A394051).

## 1. What is proven, conjectured, heuristically understood and computed about Q itself?

### Takeaway
Three things are established about Q itself:
- finite computation (Q exists for n ≤ 3·10^10);
- elementary restatements of totality;
- one conditional fact credited to Golomb: *if* lim Q(n)/n exists, it equals 1/2.

Beyond these, no theorem about Q itself has been published, and every serious source from 1994 to 2026 says so outright. Open questions include totality, convergence of Q(n)/n, the growth rate and the missing values (Erdős #422). Even unboundedness has no published proof, though an elementary argument (Inferences below; my derivation) gives it conditionally on totality. Beyond computation, the literature offers three things:
- Heuristics and statistics: Pinn's generations; amplitude exponent α ≈ 0.88; generation lengths ≈ (2−η)^k with η ≈ 0.006.
- Many rigorous theorems about relatives: other initial conditions, and shifted, diluted, three-term or parity-perturbed recurrences.
- A 2026 conjecture (Cloitre) tying Q to the fully analysed perturbed Q̃.

### Cited Findings
**Explicit "open / nothing proved" statements (who, where)**
- OEIS, verbatim: "Rate of growth is not known. In fact it is not even known if this sequence is defined for all positive n." The entry is at revision #283, last edited 2026-07-27 [P]. ([OEIS A005185](https://oeis.org/A005185))
- Erdős #422 is attributed "Asked by Hofstadter" and cited as [ErGr80]. Its statement reads: "Does f(n) miss infinitely many integers? What is its behaviour?" The page notes that well-definedness for all n is unknown [P]. ([erdosproblems.com/422](https://www.erdosproblems.com/422))
  - The database row has `status: open` (last update 2025-08-31) and `formalized: yes` (2025-11-11) [P]. ([teorth/erdosproblems data](https://github.com/teorth/erdosproblems))
- Balamohan–Kuznetsov–Tanny (2007): "Virtually nothing has been proved about the enigmatic behavior of this sequence …, including whether or not the sequence remains well defined for all positive n" [P]. ([JIS 10 (2007) Art. 07.7.1](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html))
- Nathan Fox's thesis (Rutgers, 2017), abstract: Q "has much apparent structure. But, almost nothing has been rigorously proved about it." Chapter 2 adds: "We do not know for sure whether the Hofstadter Q-sequence dies … We do know that it exists for at least 10^10 terms … and empirical evidence suggests that it lives forever [Pinn]" [P]. ([Fox thesis PDF](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- Fox, DIMACS talk abstract (2016-11-10): "almost nothing has been proved about this sequence … we still do not know whether Q(n) even exists for all n" [P]. ([DIMACS abstract](https://archive.dimacs.rutgers.edu/archive/Events/2016/abstracts/fox2.html))
- Fox, arXiv:1609.06342 (2016): Q "has defied all attempts at analyzing its behavior … nobody even knows whether the sequence is infinite" [P]. ([arXiv:1609.06342](https://arxiv.org/abs/1609.06342))
- Cloitre, arXiv:2604.06237v1 (2026-04-04): "virtually nothing has been proved rigorously about Q itself. It is not known whether Q(n) is defined for all n, nor whether Q(n)/n converges" [P]. ([arXiv:2604.06237v1 HTML](https://arxiv.org/html/2604.06237v1))
- Pinn, arXiv:2603.17509 (2026-03-18): "So far, rigorous results exist only for the 'tame' or 'slow' sequences, but not for the more chaotic types" [P]. ([arXiv:2603.17509](https://arxiv.org/html/2603.17509v1))
- MathWorld, citing Guy 1994: "There are currently no rigorous analyses or detailed predictions of the rather erratic behavior of Q(n)" [S: MathWorld's wording, attributed to Guy]. ([MathWorld](https://mathworld.wolfram.com/HofstadtersQ-Sequence.html))

**What is actually established about Q (all elementary or finite)**
- **Conditional limit (Golomb, as reported by Fox).** Fox's thesis, Ch. 2: "On the global level, Q(n) seems to oscillate around n/2 … But, all that is known rigorously is that if lim_{n→∞} Q(n)/n exists, it must equal one half [15]". Reference [15] is Golomb's "Discrete chaos" manuscript [P for Fox's statement; Golomb's own proof not read, since the scan is image-only]. ([Fox thesis, Ch. 2](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- **Death criterion.**
  - Fox: "If Q(n − 1) ≥ n, then the value of Q(n) depends on the value of Q at a nonpositive index … we say that the sequence dies after n − 1 terms, or that it dies at index n" [P]. ([Fox, arXiv:1807.01365 §1](https://arxiv.org/abs/1807.01365))
  - Balamohan–Kuznetsov–Tanny (footnote 2): totality means "whether or not Q(n − 1) and Q(n − 2) are both less than n for all positive n" [P]. ([BKT 2007](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html))
  - Deane–Gentile: for q_h to exist for all n "it must be true … that 1 ≤ q_h(n) ≤ n" [P]. ([arXiv:2311.13854](https://arxiv.org/abs/2311.13854))
  - All three agree with the coordinator's "Q total ⟺ ∀n Q(n) ≤ n" [Session].
- **Finite existence:** Q exists for n ≤ 10^10 (Pearce, 2014) and n ≤ 3·10^10 (Carr, 2023); see Section 3 [P]. ([OEIS A005185](https://oeis.org/A005185))
- **Q is not slow:** "Q(12)=8 while Q(11)=6, and monotonicity fails shortly thereafter" [P]. ([Fox, arXiv:1611.08244](https://arxiv.org/abs/1611.08244))
  - The first decrease is Q(15)=10 → Q(16)=9, read off the OEIS data [P]. ([OEIS A005185](https://oeis.org/A005185))
  - The first 200 terms are tabulated in BKT 2007 (e.g. Q(191..195) = 96, 128, 72, 96, 115) [P]. ([BKT 2007 Table 1](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf))
- **Initial-condition aliases of Q:** with the initial condition ⟨1,2⟩, "Q2 is Hofstadter's sequence without the initial 1". Since Q2(3)=3, the initial condition ⟨1,2,3⟩ "also gives Hofstadter's sequence" [P]. ([Fox, arXiv:1807.01365 §2](https://arxiv.org/abs/1807.01365); [Fox thesis §9.1](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))

**Conjectures and heuristics, with authors**
- **Totality, i.e. Q "lives forever".**
  - Fox's thesis: "empirical evidence suggests that it lives forever" [P].
  - BKT 2007, footnote 2: "In a private communication Hofstadter indicates that the Q-sequence has been computed to billions of terms. On this basis it seems highly unlikely that the sequence dies" [P]. ([BKT 2007](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf))
- **Hofstadter–Huber (around 1999) conjecture**, as reported by BKT. For Q_{r,s}(n)=Q(n−Q(n−r))+Q(n−Q(n−s)): "for the initial values all ones the only values of (r, s) for which the recurrence (2) does not eventually become undefined ('dies') are (1,2), (1,4) and (2,4)". Q is the case (1,2), renamed U. W = Q_{2,4} "appears to display even more inscrutably wild behavior", and "Like the original Q-sequence, to date nothing has been proved about this sequence" [P as reported by BKT; I did not locate the Hofstadter–Huber source, BKT's ref. [8]]. ([BKT 2007](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf))
- **Q(n) ≈ n/2 and scaling (Pinn 1999).**
  - Let S(n)=Q(n)−n/2. The mean square of S over generation k grows like 2^{αk} with α = 0.88(1).
  - R(n)=S(n)/n^α has a well-defined, strongly non-Gaussian distribution p*.
  - The increments x_m = R(n)−R(n−m) have distribution λ_m p*(x/λ_m). Pinn conjectures λ_m → √2 [P abstract]. ([Pinn, chao-dyn/9803012](https://arxiv.org/abs/chao-dyn/9803012); Complexity 4(3) (1999) 41–46)
- Fox (2018): "plots of the sequence suggest that Q(n) remains close to n/2, and there appears to be a sort of fractal structure" [P]. ([arXiv:1807.01365](https://arxiv.org/abs/1807.01365))
- **Cloitre's proxy conjecture (v1, 2026-04-04).**
  - Statement: "Numerical experiments suggest the conjecture Q(n) − Q̃(n) = O(n/√log n), indicating that Q̃ may serve as a tractable proxy for Q."
  - §11 evidence, numerics to n = 200 000:
    - max |Q−Q̃| on the r-th arch ≈ 5.3·V⁺(r), with the ratio in [5.0, 5.8] for r = 2..6;
    - plotted envelope ±0.70·n/√log n;
    - "a proof would imply Q(n)/n → 1/2 and the well-definedness of Q for all n".
  - Open problem 1 asks to "Prove Q(n) − Q̃(n) = o(n), or the conjectured bound" [P]. ([arXiv:2604.06237v1](https://arxiv.org/html/2604.06237v1))
  - The v2/v3 abstracts no longer contain the proxy sentence, and a keyword search of the v3 HTML found no "proxy" text [P]. ([v3](https://arxiv.org/html/2604.06237v3))
- **Generation structure.**
  - Pinn 1999: "the Q(n) can be grouped into a sequence of generations. The k-th generation has 2**k members which have 'parents' mostly in generation k-1, and a few from generation k-2. In this sense the series becomes Fibonacci type on a logarithmic scale" [P]. ([chao-dyn/9803012](https://arxiv.org/abs/chao-dyn/9803012))
  - Dalton–Rahman–Tanny (2011): their spot-based generation method covers "even some highly chaotic sequences, such as Hofstadter's famous Q-sequence" [P abstract]. ([arXiv:1105.1797](https://arxiv.org/abs/1105.1797); Exp. Math. 20(2) (2011) 129–137)
- **Quantitative generation data (Pinn 2026, Appendix A).**
  - Uses Dalton et al.'s mother-spot generation M(n)=M(n−Q(n−1))+1, M(1)=M(2)=1. The boundary b(k) is the least n with M(n)=k.
  - b(k) = 3·2^{k−2} exactly for 3 ≤ k ≤ 10. From k=11 it falls below: b(11)=1522 vs 1536, b(12)=3031, b(13)=6043, b(14)=12056, b(15)=24086, b(16)=48043, b(17)=95286, b(18)=189268 vs 196608.
  - η_k = 2 − ((b(k)−b(k−1))/3)^{1/(k−3)} converges to η ≈ 0.006 for k = 17..26, so generation lengths scale like 3(2−η)^k.
  - The amplitude exponent is α ≈ 0.884 [P]. ([arXiv:2603.17509 App. A](https://arxiv.org/html/2603.17509v1))
- Wikipedia, citing Pinn 1999 pp. 4–5: parents lie in generation g−1 or g−2 and "never in an older generation" [S]. ([Wikipedia](https://en.wikipedia.org/wiki/Hofstadter_sequence))
- **Missing values (Erdős #422) are data-only and unverified.** One forum post (Zeraoulia Rafik, 2026-02-10) reports:
  - direct computation to n ≤ 1.1·10^8;
  - missed values up to 200 starting 7, 13, 15, 18, 27;
  - "7 does not occur" in that range;
  - 302 values missing from {1..2000};
  - missing fraction ≈ 0.169, 0.140, 0.138, 0.137 at K = 10^3, 10^4, 10^5, 2·10^5, which the poster calls "purely empirical" [S]. ([Erdős #422 forum](https://www.erdosproblems.com/forum/thread/422))
- **formal-conjectures** states the Erdős variants (misses infinitely many, surjective, growth rate, eventually constant) relative to a predicate whose satisfiability is equivalent to totality. It does not state totality itself [Session].

### Inferences
- **Golomb's conditional limit is elementary, and I checked it (my sketch).** Assume Q is total and Q(n)/n → c.
  - If 0 < c < 1, the lookbacks n − Q(n−1) ≈ (1−c)n → ∞. So Q(n) ≈ 2c(1−c)n, which forces c = 1/2.
  - If c = 1, the lookbacks are o(n), so Q(n) = o(n), a contradiction.
  - If c = 0, both lookbacks lie in [(1−ε)n, n). So the minimum of Q over [(1−ε)^{−k}N, (1−ε)^{−k−1}N) at least doubles with each k. That gives Q(n) ≥ n^{log 2/log(1/(1−ε))}, which is superlinear for ε < 1/2 and contradicts Q(n) ≤ εn.
  - This is a genuinely Q-specific conditional theorem and a good Lean target (Section 6).
- **A slightly stronger elementary statement (my derivation; not found in the literature examined, though Golomb's manuscript may contain it).** If Q is total, then liminf Q(n)/n ≤ 1/2 ≤ limsup Q(n)/n.
  - *limsup ≥ 1/2.* Suppose instead Q(m) ≤ εm for all m ≥ N, with ε < 1/2. Put r = 1/(1−ε) < 2 and windows I_k = [N'r^k, N'r^{k+1}). Strong induction gives Q ≥ 2^k·μ on I_k (μ ≥ 1), so Q(n) ≥ (μ/2)(n/N')^{log 2/log r}. The exponent exceeds 1, which contradicts Q(n) ≤ εn.
  - *liminf ≤ 1/2.* Suppose instead Q(m) ≥ δm eventually, with δ > 1/2. The lookbacks are ≤ (1−δ)n + O(1), so U := limsup Q(n)/n ≤ 2U(1−δ). Since U ≥ δ > 0, this is impossible.
  - Golomb's statement follows at once. This "if Q is total then …" theorem is fully formalizable.
- Every Erdős #422-type question is entangled with totality:
  - If Q dies, its range is finite, so "misses infinitely many integers" is trivially true and "surjective" false.
  - Even "7 ∉ range(Q)" is open, because no proof exists that Q(n) → ∞ or even that Q is bounded below by 8 eventually.
- Pinn's heuristic |Q(n)−n/2| ~ n^{0.88} grows more slowly than n/√log n. So Cloitre's conjectured envelope |Q−Q̃| = O(n/√log n) would be dominated by Q̃'s own proven fluctuation of order n/√log n, and the two heuristics are mutually consistent.
- **Subtlety in the ⟨1,2⟩ alias (my derivation).**
  - Q2(n)=Q(n+1) holds only while Q(n) ≤ n−1: Q2's lookback is n − Q2(n−1) = n − Q(n). Q itself needs only Q(n) ≤ n.
  - So the two could differ only if Q(n)=n for some n ≥ 3.
  - This is a small, formalizable lemma.

### Gaps
- I did not obtain the primary text of Guy's E31 (any edition) or of Erdős–Graham 1980. I cannot quote exactly what they say about growth or totality.
- I found no published statistics for max or min Q(n)/n, or for max |Q(n)−n/2|, over the verified range.
- I found no OEIS sequence of "numbers not in A005185". Missing-value data come only from the unverified forum post.

## 2. History and literature timeline (1977 to October 2026)

### Takeaway
The problem comes from 1977–1980: Hofstadter's letter to Sloane, GEB, Erdős–Graham's problem book and Guy's E31. Experimental and statistical work followed (Golomb about 1990, Pinn 1998–2000). Then came a large rigorous literature on relatives: slow and tree-structured sequences (Conolly, Tanny and coauthors, 1989–2016), and solutions of the same recurrence under special initial conditions (Golomb, Ruskey 2011, and Fox 2015–2018 plus his 2017 thesis), including proofs that whole families die. From 2019 to 2026, Q-adjacent output comes mainly from:
- Alkan and coauthors, and Fox (2022, 2024);
- Deane–Gentile's "diluted" existence theorem (2023, 2025);
- the burst of 2026 work on the (−1)^n perturbation by Mantovanelli and Cloitre, plus Pinn's return.

None of it settles anything about Q itself.

### Cited Findings
**1977–1999**
- **Origin date.** Fox's thesis says the Q-sequence "was first introduced by Douglas Hofstadter in the 1960s [18]" [P: thesis Ch. 2; the date is not otherwise verified]. ([Fox thesis](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- **1977: Hofstadter's letter to Sloane.**
  - OEIS hosts "D. R. Hofstadter and N. J. A. Sloane, Correspondence, 1977 and 1991" as an image-only scan [P link]. ([OEIS A006336 scan](https://oeis.org/A006336/a006336.pdf))
  - Wolfram's 2024 essay says the letter called Q "a horse of an entirely nother color", the "absolutely CRAZY" Q sequence [S: quoted by Wolfram]. ([Wolfram, "Nestedly Recursive Functions", 2024-09-27](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/))
- **1979: Gödel, Escher, Bach (Basic Books).**
  - OEIS cites "Random House, 1980, p. 138" [P]; MathWorld cites the Vintage 1980 edition, pp. 137–138 [S].
  - Wolfram says GEB "listed only 17 terms" [S]. ([OEIS](https://oeis.org/A005185); [MathWorld](https://mathworld.wolfram.com/HofstadtersQ-Sequence.html); [Wolfram 2024](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/))
- **1980: Erdős & Graham**, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L'Enseignement Mathématique 28, Geneva (128 pp.). This is erdosproblems' [ErGr80] for #422 [P citation]. ([erdosproblems #422](https://www.erdosproblems.com/422); [catalogue](https://ci.nii.ac.jp/ncid/BA00634411))
  - Wolfram: Ron Graham stated it "in a characteristic 'state-it-as-a-problem' Erdős form" [S].
  - Tang (2026) cites [ErGr80, p. 83] for the *companion* Hofstadter consecutive-sum problem (#423) [P]. ([arXiv:2603.09939](https://arxiv.org/abs/2603.09939))
- **Guy, UPINT §E31 (all three editions).**
  - 1st edition (1981): listed as E31 [S: Bielefeld index]. ([Sillke index](https://www.math.uni-bielefeld.de/~sillke/SEQUENCES/series012))
  - 2nd edition (1994): "Three Sequences of Hofstadter", §E31, pp. 231–232 [S: MathWorld bibliography]. ([MathWorld](https://mathworld.wolfram.com/HofstadtersQ-Sequence.html))
  - 3rd edition (2004): E31 [P citation in Tang 2026]. ([arXiv:2603.09939](https://arxiv.org/abs/2603.09939))
  - E31 groups three Hofstadter sequences: A005243 (consecutive sums, Erdős #423), A005244 (c_i·c_j − 1, Erdős #424) and Q (A005185, #422) [S: MathWorld "Hofstadter Sequences" page via search summary; the #422/#423/#424 OEIS links are confirmed in the erdosproblems database (P)]. ([teorth/erdosproblems](https://github.com/teorth/erdosproblems))
- **1986: Guy.** "Some suspiciously simple sequences", Amer. Math. Monthly 93 (1986) 186–190, with follow-ups 94 (1987) 965 and 96 (1989) 905. Also Guy's letter to Sloane of 1986-09-25 [P: OEIS links]. ([OEIS](https://oeis.org/A005185))
- **1989: Conolly**, "Meta-Fibonacci sequences" (in Vajda's book).
  - The Conolly recurrence C(n)=C(n−C(n−1))+C(n−1−C(n−2)), C(1)=C(2)=1, is slow, and "every k > 1 appears once for each factor of 2 that divides it".
  - It differs from Q only by the "−1" shift [P: Fox thesis §2.3]. ([Fox thesis](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- **About 1990–1991: Golomb**, "Discrete chaos: sequences satisfying 'strange' recursions", an unpublished manuscript "circa 1990" (annotated scan on OEIS) [P link]. ([OEIS](https://oeis.org/A005185))
  - Fox: "In 1991, Solomon Golomb discovered a quasilinear solution to Hofstadter's Q-recurrence" [P]. ([arXiv:1511.06484](https://arxiv.org/abs/1511.06484))
  - Wolfram: Golomb "computed 280 terms" and never finished his paper [S].
- **1991:** OEIS entry authored by Plouffe & Sloane, May 20 1991. Ilan Vardi emailed Sloane in June 1991 (scan) [P]. ([OEIS](https://oeis.org/A005185))
- **1992: Tanny.** T(n)=T(n−1−T(n−1))+T(n−2−T(n−2)) is monotone and hits every positive integer [P: as stated by Deane–Gentile and Cloitre]. Discrete Math. 105 (1992) 227–239. ([arXiv:2311.13854](https://arxiv.org/abs/2311.13854))
- **1998–2000: Pinn.**
  - "Order and chaos in Hofstadter's Q(n) sequence", Complexity 4(3) (1999) 41–46, arXiv chao-dyn/9803012 (1998). Wolfram calls it the "first published large-scale picture" [P/S]. ([arXiv](https://arxiv.org/abs/chao-dyn/9803012))
  - "A chaotic cousin of Conway's recursive sequence", Exp. Math. 9(1) (2000) 55–66, on D(n)=D(D(n−1))+D(n−1−D(n−2)). Pinn offered "$100 to the first providing a proof of some conjectures about D(n)" [P]. ([cond-mat/9808031](https://arxiv.org/abs/cond-mat/9808031); [DOI](https://doi.org/10.1080/10586458.2000.10504635))
- **About 1999: Hofstadter–Huber** introduce the Q_{r,s} family [P: per BKT 2007]. ([BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.pdf))

**2000–2018 (rigorous work on relatives, plus Fox)**
- 2002: Wolfram, NKS p. 129 [P: OEIS ref]. ([OEIS](https://oeis.org/A005185))
- 2005: Callaghan–Chew–Tanny, SIAM J. Discrete Math. 18(4) 794–824 [P: OEIS link].
- 2007: BKT prove the Hofstadter–Huber V-sequence (r,s)=(1,4) is slow (monotone, steps ≤ 1). They also prove Gutman's frequency rules [P]. ([BKT](https://cs.uwaterloo.ca/journals/JIS/VOL10/Tanny/tanny3.html))
- 2011: Allouche–Shallit, "A variant of Hofstadter's sequence and finite automata" (J. Aust. Math. Soc.). The frequency sequence of V is 2-automatic [S: as summarized in Campbell–Cloitre's 2026 abstract and in the session notes; I did not read the paper]. ([arXiv:1103.1133](https://arxiv.org/abs/1103.1133); [Campbell–Cloitre](https://arxiv.org/abs/2602.23395))
- 2011: Dalton–Rahman–Tanny, spot-based generations [P]. ([arXiv:1105.1797](https://arxiv.org/abs/1105.1797))
- **2011: Ruskey, "Fibonacci meets Hofstadter",** Fib. Quart. 49(3) 227–230. The initial condition ⟨0̄; 3,6,5,3,6,8⟩ (zero at nonpositive indices) gives "an interleaving of two constant sequences with the Fibonacci sequence" [P: Fox 2018 §1.2; Crossref]. ([DOI](https://doi.org/10.1080/00150517.2011.12428045); [Fox 2018](https://arxiv.org/abs/1807.01365))
  - Ruskey asked whether every linear recurrent sequence occurs in some meta-Fibonacci solution [P: Fox 1508.01840 abstract].
- **2012: Celaya–Ruskey, "An undecidable nested recurrence relation"** (CiE 2012, LNCS 7318; arXiv:1203.0586).
  - A(n)=A(n−4−A(A(n−4)))+4A(A(n−4))+A(2A(n−4−A(n−2))+A(n−2)) is undecidable: given finite initial conditions, it is undecidable whether the recurrence is "calculable" (total).
  - The proof simulates Post 2-tag systems [P]. ([arXiv:1203.0586](https://arxiv.org/abs/1203.0586))
- 2013: Isgur–Rahman–Tanny, Ann. Comb. 17(4) [P: OEIS]; Celaya–Ruskey, morphic words [P]. ([arXiv:1307.0153](https://arxiv.org/abs/1307.0153))
- 2014: Hofstadter's Rutgers Experimental Math Seminar lecture (2014-04-10), "Curious patterns and non-patterns in a family of meta-Fibonacci recursions" [P: OEIS link]. Pearce's 10^10 computation is recorded in an OEIS comment dated 2014-08-29 [P].
- **2015: Fox.**
  - "Linear recurrent subsequences of meta-Fibonacci sequences" (arXiv:1508.01840; J. Difference Equ. Appl. 2016) answers Ruskey's question "in the affirmative for recurrences with positive coefficients" [P]. ([arXiv:1508.01840](https://arxiv.org/abs/1508.01840))
  - "Quasipolynomial solutions to the Hofstadter Q-recurrence" (arXiv:1511.06484; Integers 16 (2016) A68) constructs "eventual quasipolynomial solutions of all positive degrees" [P]. ([arXiv:1511.06484](https://arxiv.org/abs/1511.06484))
- 2015: Hendel, "Quasi-periods for the Hofstadter Q function", Fib. Quart. 53(2) 112–123 [P: metadata only; content not examined]. ([DOI](https://doi.org/10.1080/00150517.2015.12428273))
- **2016: Fox.**
  - arXiv:1609.06342 gives a symbolic algorithm for eventually linear-recurrent solutions: "there are hundreds of easy to describe families based on the Hofstadter Q-recurrence alone" [P].
  - arXiv:1611.08244 (JIS 20 (2017) Art. 17.7.3): B(n)=B(n−B(n−1))+B(n−B(n−2))+B(n−B(n−3)) with a generalized initial condition is slow, with its frequency sequence fully described [P]. ([JIS](https://cs.uwaterloo.ca/journals/JIS/VOL20/Fox/fox2.html))
  - DIMACS talk "Hofstadter-like Sequences over Nonstandard Integers" (2016-11-10) gives "a method for proving that certain infinite families of these sequences all die" [P]. ([abstract](https://archive.dimacs.rutgers.edu/archive/Events/2016/abstracts/fox2.html); [video](https://vimeo.com/191094180))
  - OEIS A278055–A278068 ("Relative of Hofstadter Q-sequence") cover the ⟨1..N⟩ family (A278056–A278065), the three-term relative A278055, and the initial conditions ⟨5,2⟩, ⟨37,2⟩, ⟨57,2⟩ (A278066–A278068) [P: names]. Per a search summary they were added by Fox in 2016, citing the talk [S]. ([A278056](https://oeis.org/A278056))
- **2017: Fox's PhD thesis**, "An Exploration of Nested Recurrences Using Experimental Mathematics" (Rutgers, degree date 2017-05; xi+227 pp.). Committee: Zeilberger (chair), Kopparty, Komlós, Sloane [P]. ([RUcore record](https://rucore.libraries.rutgers.edu/rutgers-lib/53613/record/); [PDF](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
  - Chapters include:
    - Ch. 3: symbolic discovery of nice solutions;
    - Ch. 4: embedding polynomials in Q-recurrence solutions;
    - Ch. 7: semi-predictable solutions;
    - Ch. 8: parametrized families of initial conditions, with symbols treated as nonstandard or p-adic integers;
    - Ch. 9: initial conditions 1..N, with "weak death" and "strong death";
    - Ch. 11: open problems;
    - App. A: infinite families of nice Q-recurrence solutions of periods 2–5 [P: thesis TOC].
- 2017: Alkan–Fox–Aybar, "On Hofstadter heart sequences", Complexity 2017:2614163. Q subtracted from the Conway sequence gives heart-shaped patterns [P abstract]. ([DOI](https://doi.org/10.1155/2017/2614163))
- **2018:**
  - Fox, arXiv:1807.01365, "A New Approach to the Hofstadter Q-Recurrence" (32 pp., v1 only, no journal-ref on arXiv) [P].
  - Alkan, "On a conjecture about generalized Q-recurrence", Open Math. 16 (2018) 1490–1500. It proposes "a generalized conjecture regarding the existence of infinitely many different solutions for all corresponding recurrences of this generalization" [P abstract]. ([DOI](https://doi.org/10.1515/math-2018-0124))
  - Alkan, Complexity 2018:8517125: a generalization of Q with chaotic generational structures, analysed with Pinn's statistical technique [P abstract]. ([DOI](https://doi.org/10.1155/2018/8517125))

**2019 to October 2026**
- 2019: Sloane and Haran, Numberphile "Amazing Graphs III" [P: OEIS link].
- 2020: Alkan–Fox–Aybar–Akdeniz, "On some solutions to Hofstadter's V-recurrence" (mortality, quasi-periodic solutions) [P]. ([arXiv:2002.03396](https://arxiv.org/abs/2002.03396))
- 2022: Fox, "Connecting slow solutions to nested recurrences with linear recurrent sequences" (arXiv:2203.09340; accepted to JDEA per the arXiv comment) [P]. Alkan–Aybar–Akdeniz, "control of mortality" for H(n)=H(n−H(n−2))+H(n−H(n−3)) [P]. ([arXiv:2211.06092](https://arxiv.org/abs/2211.06092))
- **2023:**
  - Carr's 3·10^10 computation (2023-07-02) [P].
  - Deane–Gentile, "A diluted version of the problem of the existence of the Hofstadter sequence" (2023-11-23). For q(n)=q(n−q(n−1))+f(n), q(1)=1, they prove existence for all n whenever f is slow with f(1)=0 (Theorem 1.3); the condition is "sufficient but not necessary" [P]. ([arXiv:2311.13854](https://arxiv.org/abs/2311.13854))
  - Shallit, Walnut and automata proofs for greedy recurrences [P]. ([arXiv:2308.06544](https://arxiv.org/abs/2308.06544))
- 2024: Fox, "The behavior of a three-term Hofstadter-like recurrence with linear initial conditions" (arXiv:2406.00904; JIS 27). For B with initial values 1..N, "our sequences are all finite for sufficiently large N", in both conventions [P]. ([arXiv:2406.00904](https://arxiv.org/abs/2406.00904); [JIS PDF](https://cs.uwaterloo.ca/journals/JIS/VOL27/Fox/fox7.pdf))
- 2024: Wolfram's essay (2024-09-27) on nestedly recursive functions [P: date; content partly S].
- 2024: Miska–Sobolewski–Ulas, "Binary sequences meet the Fibonacci sequence" (cites Q, p. 20) [P: OEIS link]. ([arXiv:2412.11319](https://arxiv.org/abs/2412.11319))
- 2025: Deane–Gentile, "Some subsets of set F in the diluted Hofstadter problem", where F is the set of f for which q exists [P]. ([arXiv:2509.17764](https://arxiv.org/abs/2509.17764))
  - Cloitre, nested-recurrence families [P]. ([arXiv:2506.00093](https://arxiv.org/abs/2506.00093); [arXiv:2506.18103](https://arxiv.org/abs/2506.18103))
  - Letouzey, generalized Hofstadter G-functions: "Almost all this article has been formalized and verified in the Coq/Rocq proof assistant" [P]. ([arXiv:2502.12615](https://arxiv.org/abs/2502.12615))
- **2026:**
  - Erdős #422 forum posts (Feb) [S].
  - Campbell–Cloitre, "Meta-automatic sequences" (arXiv:2602.23395) [P].
  - Tang proves the companion Hofstadter consecutive-sum sequence A005243 "omits infinitely many positive integers", with n+Ω(log log n) ≤ a_n ≪ n^{4175/2506+o(1)} (Erdős #423 context) [P]. ([arXiv:2603.09939](https://arxiv.org/abs/2603.09939))
  - The perturbed-Q cluster (Section 4):
    - Mantovanelli: OEIS A394051 (03-08); arXiv:2603.16111 (03-17); 2603.29622 (03-31, revised 05-18 and 07-22); 2609.02412 (09-02).
    - Cloitre: arXiv:2604.06237 (04-04, revised 07-16 and 07-22).
  - Pinn, arXiv:2603.17509 (03-18) [P].
  - Mantovanelli, averaged Golomb triangular recursion (arXiv:2605.11250) [P].
  - Cloitre–Ma–Zhang, "A Padovan-automatic description of a nested recurrence" (A076502), with a reproducibility package in "Python, Lean 4, Walnut" and results formalized in Lean (2026-09-27) [P]. ([arXiv:2609.33421](https://arxiv.org/abs/2609.33421))

**Which initial conditions make the Q-recurrence die or survive**
- **Fox 2018, Theorem 1 ("weak death": nonpositive indices undefined; initial condition ⟨1,2,…,N⟩).** "For N = 8, N = 11, N = 12, or N ≥ 14, the sequence Q_N dies. Furthermore, if N ≥ 21, the sequence has exactly N + 28 terms, and if 14 ≤ N ≤ 20, the sequence has exactly N + 32 terms" [P]. ([arXiv:1807.01365](https://arxiv.org/abs/1807.01365))
  - The finite witnesses are Q_8(420)=430, Q_11(199)=206 and Q_12(69)=77.
  - For N ≥ 21 the proof computes 28 symbolic terms valid for N ≥ 13. Then Q_N(N+29) needs Q_N(−N+21), which is undefined [P].
  - For N ∈ {2,3,4,5,6,7,9,10,13} the fate is unknown. N=2,3 give Q itself. "All of these sequences last for at least 30 million terms" [P].
  - OEIS records: A278056 (N=4): "not known if this sequence is defined for all positive n … a(n) exists for n <= 3*10^7". A278060 (N=8): "exactly 420 terms, since a(420)=430 and computing a(421) would refer to a(-9)". A278065 (N=13): unknown, ≥ 3·10^7 [P]. ([A278056](https://oeis.org/A278056), [A278060](https://oeis.org/A278060), [A278065](https://oeis.org/A278065))
- **Fox 2018, Theorem 2 ("strong death": zero at nonpositive indices; ⟨0̄;1..N⟩, N ≥ 35).** This is a complete structure description: 28+6 terms, then period-5 quasilinear chunks whose endpoints follow auxiliary sequences A_i, B_i, C_i.
  - The fate is decided by the first j with C_j ≠ 1: C_j ∈ {0,3,4} means finite, and C_j = 2 means Proposition-1 behaviour, conjectured infinite.
  - C_i(N) depends only on N mod 5^j (Prop. 2 and Cor. 1). This gives a tree on base-5 strings, which "is poorly understood".
  - The thesis adds: "We do not know if this tree is infinite." If it is, König's lemma gives a 5-adic N₀ whose sequence consists entirely of period-5 pieces [P]. ([arXiv:1807.01365](https://arxiv.org/abs/1807.01365); [thesis §9.1.2](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- **Fox 2018 §3.4 (the 55 exceptional N, strong convention).** If N ≤ 27, the sequence "appears to behave chaotically and last for a long time (at least 10 million terms), unless N ∈ {19, 23, 26}", which are finite. Beyond 27, all are finite except N ∈ {33, 36, 67, 71}, which reach Proposition-1 behaviour and "are therefore conjectured to be infinite" [P].
- **Fox 2018, Proposition 1 (semi-predictable solutions).** The initial condition ⟨0̄; a_1..a_K, 5, λ, 4, μ⟩ with λ ≥ 9 and μ ≥ K+6 yields the period-5 pattern 5R(k), 5S(k), λT(k), 4, 5R(k). It holds as long as the auxiliary sequences R, S, T "live", and their totality is itself open [P].
- **Golomb's initial condition ⟨3,2,1⟩** gives Q_G(3k)=3k−2, Q_G(3k+1)=3, Q_G(3k+2)=3k+2. It "lives, and the pattern visible here continues forever", and the thesis gives a proof [P: Fox 2018 §1.2; thesis §2.2].
  - OEIS A244477 adds a(n) = 2a(n−3) − a(n−6) for n > 6 and quotes Golomb's description "quasi-periodic sequence with a quasi-period of 3" [P]. ([A244477](https://oeis.org/A244477))
- **Quasipolynomial and linear-recurrent families.**
  - Eventual quasipolynomial solutions exist in all degrees [P: arXiv:1511.06484]. The thesis notes: "It is unknown whether there exist purely quasipolynomial solutions to the Hofstadter Q-recurrence of degrees greater than 1" [P: thesis Ch. 4].
  - "Hundreds" of eventually linear-recurrent families exist [P: arXiv:1609.06342].
  - Example (Deane–Gentile, quoting Fox): r(3..12) = 1,1,3,5,1,4,7,6,4,9 gives an eventually period-5 quasilinear solution for n > 12 [P]. ([arXiv:2311.13854](https://arxiv.org/abs/2311.13854))
- **Three-term analogue (Fox 2024).** With initial values 1..N, all sequences are finite for sufficiently large N, with complete characterization [P]. ([arXiv:2406.00904](https://arxiv.org/abs/2406.00904))
- **General undecidability:** "the death question is undecidable given a generic nested recurrence and initial condition [Celaya–Ruskey]" [P: Fox thesis Ch. 2]. ([arXiv:1203.0586](https://arxiv.org/abs/1203.0586))

### Inferences
- **The pattern across the literature.** Rigorous *survival* proofs for the Q-recurrence exist only when the solution has exploitable structure: quasipolynomial, linear-recurrent, or Fox's 5-periodic chunks (which themselves rest on the conjectural R, S, T sequences). Rigorous *death* proofs are routine, by finite or symbolic computation. No initial condition yielding Pinn-style chaotic behaviour (Q itself, ⟨1..N⟩ for N ∈ {4,…,7,9,10,13}, Q_{2,4}=W) has a survival proof.
- The 2026 perturbed result fits this pattern rather than breaking it: the (−1)^n term converts the recurrence into two slow interleaved sequences (Section 4).

### Gaps
- The 1977 letter, Golomb's manuscript, Guy's 1986 letter and Vardi's 1991 email exist on OEIS only as image scans. I did not read them; the constraints forbid downloading files for visual reading.
- I did not find Hofstadter–Huber's own write-up (BKT's ref. [8]; Fox's thesis cites it as [19]).
- I did not examine the content of Hendel 2015 or of the Trojovský 2020 papers on related meta-Fibonacci sequences.
- I did not confirm the exact page in Erdős–Graham 1980 for #422. p. 83 is confirmed (via Tang) only for the companion #423.

## 3. Computational records

### Takeaway
The verified-to-exist bound for Q is 10^10 (Roman Pearce, August 2014, recorded by Sloane), then 3·10^10 (M. Eric Carr, July 2023, via "result caching"). Neither record has a published method, hardware, memory, runtime, data or independent verification. I found no newer record for Q as of 2026-10-10. A "3·10^10" claim also appears for the perturbed A394051.

### Cited Findings
- OEIS comment: "_Roman Pearce_, Aug 29 2014, has computed that a(n) exists for n <= 10^10. - _N. J. A. Sloane_" [P]. ([OEIS A005185](https://oeis.org/A005185))
- OEIS comment: "a(n) exists for n <= 3*10^10. - _M. Eric Carr_, Jul 02 2023" [P]. ([OEIS A005185](https://oeis.org/A005185))
- **OEIS edit history (revisions #225–#230, 2023-07-02/03).**
  - Carr's original wording: "has extended this result; a(n) has been computed to exist for n<= 3*10^10".
  - His discussion note: "Computed the first thirty billion terms using result caching; please let me know if specific evidence is needed etc.; this is my first OEIS submission. If such contributions are useful, I may be able to extend this further."
  - Joerg Arndt and Jon E. Schoenfield edited the wording [P]. ([OEIS history](https://oeis.org/history?seq=A005185))
- I found no Pearce write-up (web or seqfan) describing the method or memory. Fox's papers cite "at least 10^10 terms" via OEIS [P]. ([arXiv:1609.06342](https://arxiv.org/abs/1609.06342); [arXiv:1807.01365](https://arxiv.org/abs/1807.01365))
- Earlier informal computations:
  - Hofstadter (private communication to BKT, around 2007): "billions of terms" [P: BKT footnote].
  - OEIS links a "Plot of first 100 million terms" by Hofstadter [P].
  - Golomb computed 280 terms [S: Wolfram].
- Related computations:
  - Fox's unresolved ⟨1..N⟩ sequences: ≥ 3·10^7 terms [P].
  - Strong-convention chaotic cases: ≥ 10^7 [P].
  - Erdős forum user: Q to 1.1·10^8 [S].
- Perturbed sequence: A394051 states "The sequence does not terminate for all n <= 3*10^10 (verified computationally)". This is unattributed within Mantovanelli's entry [P]. ([OEIS A394051](https://oeis.org/A394051))
- Lean feasibility (kernel decide ≈ 10^4, native_decide ≈ 10^7) [Session].

### Inferences
- **Memory.** A naive array to 3·10^10 needs about 3·10^10 × 4 bytes ≈ 120 GB at 32 bits.
  - 32 bits suffice only for a detrended value such as Q(n) − ⌊n/2⌋, since Q(n) itself reaches about 1.5·10^10 > 2^32. Storing raw values in 64 bits would take about 240 GB.
  - The lookbacks n − Q(n−1) land near n/2, so roughly the first 40% of the table could be discarded, a modest saving. "Result caching" implies a memo table of this kind.
  - These are my estimates, not reported figures.
- Both records are single-person, unrefereed computations. OEIS acceptance is editorial, not verification.

### Gaps
- No hardware, memory, runtime, code, checksums or data are published for either record.
- I found no record beyond 3·10^10.

## 4. Mantovanelli, arXiv:2603.29622, and the 2026 perturbed-Q cluster

### Takeaway
Mantovanelli introduced Q̃ (OEIS A394051, 2026-03-08) and first studied it numerically (arXiv:2603.16111v1). Two independent well-definedness proofs then appeared.
- **Mantovanelli's computer-assisted proof (arXiv:2603.29622).**
  - It went through three titles and proof architectures. v1 (finite-state "two-mode/critical-core") had a gap found by Cloitre. v2 (certified finite-state induction) had a "semantic gap". v3 (2026-07-22) gives a return-word induction with a finite kernel of 13 return words, 92 states and 122 rules, all-level parameter inductions, and a lag-potential certificate (lag ≥ 38).
  - Its Zenodo archive is about 218 KB.
- **Cloitre's human, certificate-free proof (arXiv:2604.06237).** It is now the reference result: Mantovanelli's own later papers credit Cloitre with proving global well-definedness. It also proves Q̃(n)/n → 1/2 and Q̃(n) = n/2 + O(n/√log n), with that order optimal.

Both methods rest on the fact that the perturbation makes every value odd, which splits Q̃ into two *slow* binary-increment sequences. Q has no such structure. Mantovanelli states his proof "does not directly apply" to Q, and Cloitre notes the corresponding conclusions "remain open for Q". None of these papers is refereed or published in a journal (arXiv shows no journal-ref). I found no discussion outside the authors' own papers and OEIS.

### Cited Findings
**(a) Origin and the object**
- OEIS A394051, "Hofstadter Q-sequence perturbed by (-1)^n", was authored by Marco Mantovanelli on 2026-03-08 and is at revision #64 (2026-10-09). Its comments:
  - "All terms are odd"; a(n) ~ n/2 numerically; "does not terminate for all n <= 3*10^10 (verified computationally)".
  - Cloitre added formulas: a(n)/n = 1/2 + O(1/√log n) (2026-04-03), and 1/(3√(2π)) < limsup √(log₂n)·|a(n)/n−1/2| ≤ 1/(2√(2π)) (2026-07-13).
  - Sloane noted on 2026-10-09 that Cloitre's paper was retitled [P]. ([OEIS A394051](https://oeis.org/A394051))
- Mantovanelli, arXiv:2603.16111v1 (2026-03-17), "Dyadic Self-Similarity in a Perturbed Hofstadter Q-Recursion", is purely numerical and heuristic: Q̃ ≈ n/2, dyadic self-similarity of E(n)=Q̃(n)−n/2. It concludes: "Establishing rigorous results for these phenomena remains an open problem" [P]. ([arXiv:2603.16111v1](https://arxiv.org/abs/2603.16111v1))
- Author: Marco Mantovanelli, "Independent Researcher" (marco@mantovanelli.de) [P: v3 front matter].

**(b) The theorem (v3, Theorem 1.1)**
- "The recursion (1) is well-defined for every n ≥ 1. Equivalently, every recursive argument is a positive integer strictly smaller than the current index, and the recursion determines a unique infinite sequence" [P]. ([arXiv:2603.29622v3 HTML](https://arxiv.org/html/2603.29622v3))
- MSC 11B37, 68Q45; secondary 37B10, 03D25, 68Q60. The subtitle is "A finite-kernel proof of global well-definedness" [P].

**(c) How the v3 proof works [all P, from the v3 text]**
1. **Binary reduction (§2).**
   - Define T_n = n − Q̃(n−1) and s_n = (Q̃(n+1) − Q̃(n−1))/2.
   - The two-step clock is T_{n+2} = T_n + 2(1 − s_n).
   - The two backward cursor heads are h_n = T_n + 1 and k_n = T_{n−1} + 2.
   - For binary s, subtracting the recurrence at n from the one at n+2 cancels the parity terms. This gives the **binary local recurrence** s_{n+1} = (1−s_n)·s_{h_n} + (1−s_{n−1})·s_{k_n}, with head dynamics h_{n+1} = k_n + 1 − 2s_{n−1} and k_{n+1} = h_n + 1.
   - **Unique bad configuration:** s_{n+1}=2 iff (s_{n−1}, s_n, s_{h_n}, s_{k_n}) = (0,0,1,1).
   - **Reconstruction principle (Thm 2.4).**
     - Hypotheses: any integer T and binary s with T_2=1, T_3=2, s_2=0, s_3=1, satisfying the clock and binary recurrences.
     - Q(n) := n + 1 − T_{n+1} then satisfies the perturbed recursion with all arguments in [1, n).
     - The residual R_n = Q(n) − Q(T_n) − Q(T_{n−1}+1) − (−1)^n obeys R_{n+2} = R_n, with R_3 = R_4 = 0.
     - Because each parity subsequence of T starts at 1 or 2 and grows by 0 or 2, 1 ≤ T_n ≤ n−1.
2. **Finite local kernel (§3).**
   - The C₇-code is the 7-bit window (s_{n−2}, s_{n−1}, s_n, s_{n+1}, s_{n+2}, s_{T_n+1}, s_{T_{n−1}+2}); 21 codes occur.
   - The C₇ stream parses into **13 return-word types** of lengths 2, 31, 8, 10, 39, 20, 30, 40, 20, 30, 31, 40, 39.
   - A synchronized state is (previous type, source types r_A, r_B, offsets δ_A, δ_B, marker parity). There are **92 states** and **122 two-source transition rules**. Odd "swap" types (1, 4, 10, 12) exchange the physical A/B streams.
   - The finite checker verifies:
     - all 21 codes satisfy the local identity;
     - overlaps;
     - 29 word pairs reduce to 52 atom rules;
     - all **28 025** semantically consistent A/B windows;
     - 24 ambiguous selector keys with 36 rule pairs, none prefix-compatible on both streams, so fixed streams select at most one rule.
   - The initial alignment evaluates the recurrence directly (default limit 1200; handoff at marker 793). Initial word boundaries are 37, 39, 70, 78. At target block 74 the lags are 38 and 41.
3. **All-level structure (§§4–8).**
   - Exact composition of judgements uses inclusive bridges (⊙).
   - Rank words A_n, B_n are defined noncircularly (A_n = E_n U(B_n), B_{n+1} = O_n V(A_n)), together with epoch words 𝓔_A(n), 𝓔_B(n) and bridges 𝓐_n, 𝓑_n.
   - **Four stationary chunk families** (C3P, C3Q, C4H, C4K) and **four linear bridge-tail families** (E_{A,2}, D_{A,3}, E_{B,2}, D_{B,3}) reduce to **ten zero-loop schemas** (4 stationary, 6 tail). Each schema is proved for all parameters d by induction, since d→d+1 inserts one copy of rule 0 or 64.
   - A free-monoid port factorization (Lemma 8.1) identifies source words exactly.
   - **Absolute addresses** have closed forms in the basis {4^n, 1, n, …, n^4}, e.g. |𝓔_A(n)| = (96·4^n − n^4 − 12n^3 − 53n^2 − 108n − 90)/3. A symbolic checker reduces 34 residual identities coefficientwise to zero.
   - Induction then runs around the four-factor cycle 𝓐_n → 𝓔_B(n) → 𝓑_{n+1} → 𝓔_A(n).
4. **Causality (§9).**
   - The weighted role graph has 184 nodes and 244 edges, of which 176 nodes, 88 states and 118 rules are reachable.
   - A nonnegative potential Φ (Bellman–Ford, no negative cycle, checked on all 236 reachable role edges) gives **j − p_A ≥ 38 and j − p_B ≥ 38**. So every source read is strictly in the generated past.
5. **Conclusion (§10).** A total binary solution is reconstructed via Thm 2.4.
- **Trusted base (§11.1):**
  - the paper's reductions;
  - the 122-rule table and kernel data;
  - "the short deterministic checkers";
  - the Python runtime.
- "The result is not claimed to be formalized in Lean, Coq, Isabelle, or HOL. An independent reimplementation … would further reduce implementation risk."
- **Diagnostic (non-logical) expansions:**
  - 232 stationary chunks through parameter 60;
  - 398 tails through level 100;
  - 39 bridges through level 20;
  - 349 504 epoch macrosegments and 87 364 gap anchors through level 8;
  - 443 exact source identities totalling 10 919 761 local target steps.
- **AI disclosure:** "OpenAI's ChatGPT was used for language editing, bibliographic organization, LaTeX assistance, exploratory calculations, the development and checking of proof ideas, and the drafting and refactoring of verification code" [P].

**(d) Version history and the errors (the earlier title is confirmed)** [P: arXiv API and abstract pages; text of each version]
| Version | Date (UTC) | Title | Size and comments |
|---|---|---|---|
| v1 | 2026-03-31 | "A Finite-State Proof of the Well-Definedness of a Perturbed Hofstadter Sequence" | 41 pp., 2 figs; "complete finite-state reduction and a machine-checkable verification of the critical core" |
| v2 | 2026-05-18 | "Certified Finite-State Induction for a Perturbed Hofstadter Recursion" | 38 pp., 2 figs; "Major revision with explicit certificate semantics, realization and extension records, faithfulness verification, parity checking, and reproducibility infrastructure"; arXiv source 2,308 KB |
| v3 | 2026-07-22 | "Certified Return-Word Induction for a Perturbed Hofstadter Recursion" | 27 pp., 3 figs; "Major Revision … the previous finite-state closure argument is replaced by an exact return-word induction with absolute source addresses and an explicit causality certificate" |
([abs v1](https://arxiv.org/abs/2603.29622v1), [abs v2](https://arxiv.org/abs/2603.29622v2), [abs v3](https://arxiv.org/abs/2603.29622v3))
- **The v1 method:**
  - symbolic "contexts" (e.g. λ₀ = (C,E,B,R₁,pos=1,parity=1,debt=0));
  - a compatibility graph Ψ;
  - "valid assignments split into two global modes";
  - sensitive contexts;
  - a **critical core of 4 contexts** {λ₀, λ₂, λ₁₄, λ₂₄};
  - an exhaustive check of all 15 nonempty subsets (C/C++ programs `two_mode_automaton.c`, `branch_comparison_solver.c`, `checkall.cpp`).
  - The key inference was that failure of the recursion corresponds to an "obstruction" in this finite system. v1 also called the proof "well-suited for formal verification in a proof assistant such as Lean or Coq" [P]. ([v1 HTML](https://arxiv.org/html/2603.29622v1))
- **An error was found in v1.** v2's acknowledgments: "I thank Benoît Cloitre for his careful analysis of the first version of this paper and for identifying a gap in the proof. His comments were a major motivation for the revised certificate format" [P]. ([v2 HTML](https://arxiv.org/html/2603.29622v2))
- **v2 also had a gap**, which v3 states explicitly:
  - The v3 version note: "Version 3 replaces the symbolic S→T→U→V closure argument of Version 2. That earlier finite-state abstraction did not by itself establish semantic faithfulness to the recurrence at every future position."
  - §12: v2 "attempted to derive global well-definedness from a finite symbolic renormalization cycle extracted from a long trace … [it] left a semantic gap: closure of the abstract overlap graph did not imply that every future recurrence position realized the required source context."
  - The title changed "from 'finite-state' to 'return-word' induction" [P]. ([v3 HTML](https://arxiv.org/html/2603.29622v3))
- v3 acknowledgments thank Cloitre "for comments on earlier versions of the manuscript that helped clarify the limitations of the previous finite-state formulation" [P].
- **The companion paper was also corrected.** arXiv:2603.16111 went through three versions [P]. ([arXiv:2603.16111](https://arxiv.org/abs/2603.16111))
  - v1 (03-17): "Dyadic Self-Similarity…", numerical.
  - v2 (05-31): "Dyadic Frequency Laws, Clock Dynamics, and Defect Scaling…", 47 pp., proving the frequency law via "Cloître's binary interleaving structure".
  - v3 (07-18): "A Dyadic Frequency Law…", 20 pp. It replaces the "rank-lifting and mass-closure proof" with "a direct folded-degree proof based on Cloitre's canonical forest structure".
  - v3 adds: "Two incorrect ancillary statements concerning bounded first differences and non-dyadic cumulative frequencies have been removed. The main dyadic frequency multiset theorem is unchanged."
  - Main theorem: for F(s) = #{n: Q̃(n)=2s−1}, {F(s): 2^k ≤ s < 2^{k+1}} = {3+ν₂(j): 1 ≤ j ≤ 2^k} as multisets.
  - Its v3 abstract states: "Cloître proved that the recursion is globally well-defined" [P].

**(e) Why the method does not extend to unperturbed Q**
- **Correction to the session note.** The session note quotes the paper as saying the reduction "does not appear to extend to the unperturbed sequence". I did not find that phrase verbatim in any version.
  - The closest is v1 §1: the perturbation "enables a finite-state reduction that does not appear to be available in the unperturbed case" [P].
  - v3, which I read in full, does not discuss extension to Q at all beyond its introduction.
- v2 §10.2: "the proof does not resolve the well-definedness problem for the classical unperturbed recursion … The alternating perturbation plays an essential role in the finite symbolic structure verified here."
- v2 §11.8: "The classical Hofstadter Q-sequence remains substantially harder. The present proof does not directly apply to it … It would be interesting to investigate whether partial symbolic models exist for the unperturbed case, and if so, why they fail to close" [P]. ([v2 HTML](https://arxiv.org/html/2603.29622v2))
- **The structural reason, visible in both proofs.**
  - The (−1)^n term makes every value odd: odd + odd ± 1 is odd [P: Cloitre v1].
  - Hence Q̃(n+1) − Q̃(n−1) ∈ {0, 2}, which is exactly the binary s_n of Mantovanelli §2.
  - Equivalently, both parity subsequences a(m) = (Q̃(2m−1)+1)/2 and b(m) = (Q̃(2m)+1)/2 are slow, with increments in {0,1} [P: Cloitre v3 §1, §2.2, Lemma 3.1].
- Cloitre v3's introduction contrasts Q with Conway's sequence: its ratio tends to 1/2, as analysed by Mallows and by Kubo–Vakil, and Grytczuk studied a triply nested variant. He adds: "The corresponding conclusions remain open for Q." He then presents his proof as specific to Q̃'s "words and forests" [P]. ([v3 HTML](https://arxiv.org/html/2604.06237v3))

**(f) The Zenodo data and the certificate size**
- **Zenodo for v3:** DOI 10.5281/zenodo.21495335, version 3.0.0, published 2026-07-22. It is the only version under that concept, with **223 189 bytes** of files in total (about 218 KB) [P: Zenodo versions API].
  - Contents, per paper App. D: `kernel_data/` (13 return words, 92-state table, 122-rule table, atom/pair rules, cursor transforms, odd swaps), `code/` (rank, epoch, chunk, tail, bridge, lag, semantic, symbolic-address, selector and global-closure checkers), `data/` (audit tables), `SHA256SUMS.txt`, and `run_all_checks.py`, which writes `data/run_all_checks_audit.json` with `"passed": true`.
  - Named data files include `data/block_lag_potential_certificate.csv`, `data/phase17_rule_selector_audit.json` and `data/phase17_symbolic_address_residuals.csv` [P]. ([Zenodo](https://doi.org/10.5281/zenodo.21495335); [Zenodo API](https://zenodo.org/api/records/21495335/versions))
- **v2 code:** GitHub `Mantovanelli1110/Certified-Finite-State-Induction-for-a-Perturbed-Hofstadter-Recursion` [P: v2 reference 17]. ([GitHub](https://github.com/Mantovanelli1110/Certified-Finite-State-Induction-for-a-Perturbed-Hofstadter-Recursion))
- **Certificate inventory (v3 Table 4):**
  - 25 stationary primitive paths; 4 stationary loop schemas;
  - 15 tail/bridge connector primitives; 6 tail loop schemas;
  - 92 states; 122 rules; 28 025 semantic windows;
  - 236 role-graph edges; 5 seed transductions; 71-block alignment;
  - 13 cursor transforms; 36 selector pairs; 34 symbolic identities;
  - all with 0 violations [P].
- The zeta-function paper's reproducibility archive is Zenodo 10.5281/zenodo.22250518 [P]. ([arXiv:2609.02412](https://arxiv.org/abs/2609.02412))

**(g) Cloitre's independent, certificate-free proof (arXiv:2604.06237)**
- **Versions:**
  - v1 (2026-04-04): "On a perturbed Hofstadter Q-recursion", 30 pp.
  - v2 (2026-07-16): retitled "The Mantovanelli-Hofstadter Sequence", 53 pp., "Substantially revised and expanded".
  - v3 (2026-07-22): 50 pp., "Minor editorial revisions".
  - Author: Benoît Cloitre, independent researcher, Paris [P]. ([arXiv API/abs](https://arxiv.org/abs/2604.06237))
- **Theorem 1.1 (v3):**
  - (i) Q̃ is well-defined and unique, and Q̃(n)/n → 1/2.
  - (ii) Arch-amplitude increments W_r = C(2r+1, r) (OEIS A001700), so V_r = 2 + Σ_{j≤r} C(2j+1,j) ~ (8/(3√π))·4^r/√r (A024718).
  - (iii) Q̃(n) = n/2 + O(n/√log n), and "The error is not o(n/√log n)".
  - (iv) C_layer ≤ limsup (Q̃(n)/n − 1/2)√(log₂ n) ≤ limsup |…|√(log₂ n) ≤ 1/(2√(2π)), with C_layer > 1/(3√(2π)). The exact limsup is open [P]. ([v3 HTML](https://arxiv.org/html/2604.06237v3))
- **Method:**
  - Parity split (Lemma 2.2): (RA) a(m) = b(m−b(m−1)) + b(m−a(m−1)) − 1 and (RB) b(m) = a(m+1−a(m)) + a(m+1−b(m−1)).
  - Arches are generated by exact-fit two-tape interleavings from P₀ = 001011: N_r = Interleave(P_r[2:], P_r[0:|P_r|−1], 1) and P_{r+1} = Interleave(00N_r1, 0N_r, 0), with |P_r| = 2a_r and a_r = (2·4^{r+1}+1)/3.
  - The sequences are constructed "without assuming that the original recurrence continues", with 1 ≤ a(m), b(m) ≤ m (Lemma 3.1). Dyck paths and plane forests, the Toeplitz property, ECO succession rules and Catalan generating functions give the amplitudes.
  - v3: "The present paper gives a direct self-contained proof without a finite-state certificate" [P].
- **Correction inside Cloitre's own work.** v1 claimed, *conditionally* on two observations verified only for r ≤ 6, that limsup |Q̃(n)/n − 1/2|·√(log₂ n) = 1/(3√(2π)). v3 proves this limsup is ≥ C_layer > 1/(3√(2π)), stating "The strict lower inequality is exact, not numerical". So the v1 conditional value is superseded [P: v1 abstract, v3 Thm 1.1(iv)]. v1 also had Corollary 4.14: Q̃ well-defined with 1 ≤ Q̃(n) ≤ n [P].

**(h) Follow-ups on Q̃**
- Mantovanelli, arXiv:2609.02412 (2026-09-02), works with the Dirichlet series Z(s,t) = Σ n^{−s} Q̃(n)^{−t}.
  - Absolute convergence holds exactly for Re(s+t) > 1.
  - For E(n) = 2Q̃(n) − n, A(X) = Σ_{n≤X} E(n) = X log₂X + X·Ω(log₂(3X/32)) + O(X/√log X), where Ω is continuous and periodic.
  - There are boundary resonances at w = 0 and 2πim/log 2.
  - "We do not claim a full-slice continuation across Re w = 0" [P]. ([arXiv:2609.02412](https://arxiv.org/abs/2609.02412))
- Mantovanelli 2603.16111v2: exact identity R(n) = Q̃(2n) − 2Q̃(n) = 2t₁(n+1) − t₁(2n+1) − 1, with t₁(n) = n − Q̃(n−1) [P].
- Cloitre v1 also studied a perturbed Conway–Mallows sequence b(n) = b(b(n−1)) + b(n−b(n−1)) + (−1)^n. It is open problem 3 there: prove or disprove b(n)/n → 1/(2φ) [P].

**(i) Citations, discussion and refereeing**
- **Refereeing:** the arXiv API shows **no journal-ref** for 2603.29622, 2604.06237, 2603.16111 or 2609.02412 as of 2026-10-10. None of the comments mention acceptance [P]. ([arXiv API](https://export.arxiv.org/api/query?id_list=2603.29622,2604.06237,2603.16111,2609.02412))
- **Cross-citation:**
  - Mantovanelli v3 cites Cloitre (arXiv:2604.06237v2) and his own 2603.16111v3.
  - Cloitre v3 cites Mantovanelli's "certified finite-state induction" and his numerical paper.
  - OEIS A005185 links Cloitre's paper ("See p. 1"), and A394051 links all of them [P].
- **Index counts:** OpenAlex reports cited_by_count = 0 for 2603.29622, 2604.06237 and 2603.16111. This is clearly incomplete, given the verified cross-citations [P]. ([OpenAlex](https://api.openalex.org/works/doi:10.48550/arxiv.2603.29622)) The Semantic Scholar API was rate-limited, so its counts are unknown.
- **Discussion:** the Erdős #422 forum thread (2 comments, Feb 2026) does not mention the perturbed results [S]. A web search found no blog, MathOverflow or other third-party discussion [P: absence in search].

**(j) Other well-definedness proofs for perturbed, shifted, diluted or modified variants**
- **Shifted:**
  - Conolly's C(n)=C(n−C(n−1))+C(n−1−C(n−2)) is slow [P: Fox thesis].
  - Tanny's T(n)=T(n−1−T(n−1))+T(n−2−T(n−2)) is monotone and hits every positive integer [P: per Deane–Gentile].
  - Callaghan–Chew–Tanny (2005) and Isgur et al. (2016) construct families of slow solutions [P: OEIS links].
- **Lags (1,4):** the V-sequence is slow (BKT 2007) [P], and its frequency sequence is 2-automatic (Allouche–Shallit) [S].
- **Three-term:** Fox's B with a suitable initial condition is slow and total (2016/2017) [P].
- **Diluted:** Deane–Gentile prove totality of q(n)=q(n−q(n−1))+f(n) for every slow f with f(1)=0. This is "sufficient but not necessary"; the 2025 follow-up studies subsets of the admissible set F [P]. ([arXiv:2311.13854](https://arxiv.org/abs/2311.13854); [arXiv:2509.17764](https://arxiv.org/abs/2509.17764))
- **Pinn's F_{i,j} index-shift family:** only (i,j) ∈ {(0,0),(0,1),(1,0),(1,1)} "appear well-defined" [S: Wikipedia citing Pinn 2000 p. 16]. ([Wikipedia](https://en.wikipedia.org/wiki/Hofstadter_sequence))
- **Parity-perturbed, +(−1)^n:** proved by Cloitre, independently by Mantovanelli v3 [P].
- **"+1" or other additive perturbations of Q:** OEIS searches returned only A394051, and I found no paper [P: absence].

### Inferences
- As of 2026-10-10, the safest citation for "the (−1)^n-perturbed Q is total" is Cloitre, arXiv:2604.06237v3. It is human-readable, computer-free, and credited by Mantovanelli himself. Mantovanelli v3 is a complementary, computer-assisted proof whose trusted base includes the Python checkers and runtime, which are not formally verified.
- Both are unrefereed preprints. Each author has already corrected substantive errors: Mantovanelli v1 and v2, the 2603.16111 ancillary statements, and Cloitre's v1 conditional constant. Formalization would therefore add real value here.
- Q̃ is a better first formalization target than anything about Q:
  - the totality proof reduces to slow sequences with 1 ≤ a(m), b(m) ≤ m;
  - Mantovanelli's reconstruction principle (Thm 2.4) is a short, self-contained lemma;
  - Cloitre's interleaving laws are explicit word recursions.
- **Why neither method touches Q.**
  - For Q, Q(n+1)−Q(n−1) is not confined to two values. From BKT Table 1: Q(24)−Q(22) = 16−12 = 4, and Q(26)−Q(24) = 14−16 = −2.
  - Q takes both parities, so there is no parity split.
  - Any "finite kernel plus all-level word induction" for Q would need an unbounded local alphabet, or a new idea.

### Gaps
- I did not download or run the Zenodo archive, so I have not checked that `run_all_checks.py` passes or that the files match the claims.
- I could not read Mantovanelli v2's full logical argument beyond its abstract, TOC, scope sections and acknowledgments.
- Semantic Scholar citation counts are unknown (rate-limited). I could not find Google Scholar data.
- I found no referee reports, journal submissions or public expert assessments of either proof.

## 5. Is there a credible proof strategy for totality, and what do experts say about difficulty?

### Takeaway
No credible complete strategy for Q's totality has been proposed. The expert consensus, spanning Guy (1994) through Tanny et al. (2007), Fox (2016–17), Pinn (2026), Cloitre (2026), Mantovanelli (2026) and Wolfram (2024), is threefold:
- nothing nontrivial is proved, beyond Golomb's conditional "limit, if it exists, is 1/2";
- the chaotic, non-slow behaviour defeats existing tree, slow-sequence, automata and finite-state methods;
- empirically Q "lives forever".

The only Q-specific programme on record is Cloitre's 2026 proxy idea: bound |Q − Q̃| on the defined prefix. Its evidence is numerical only (to n = 2·10^5).

### Cited Findings
- **Expert statements.**
  - Hofstadter, 1977: Q is "absolutely CRAZY" [S: Wolfram].
  - Guy (via MathWorld): no rigorous analyses or detailed predictions [S].
  - BKT (Tanny and coauthors, 2007): "Virtually nothing has been proved"; given billions of computed terms, "it seems highly unlikely that the sequence dies" [P].
  - Fox: "almost nothing has been proved"; "nobody even knows whether the sequence is infinite"; "empirical evidence suggests that it lives forever"; "the death question is undecidable given a generic nested recurrence and initial condition" [P]. ([thesis](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf); [arXiv:1609.06342](https://arxiv.org/abs/1609.06342))
  - Pinn 2026: rigorous results exist only for "tame" or "slow" sequences [P].
  - Mantovanelli v2: "The classical Hofstadter Q-sequence remains substantially harder" [P].
  - Cloitre v1: "virtually nothing has been proved rigorously about Q itself" [P].
- **Wolfram (2024).** Nestedly recursive functions show "too much computational irreducibility", which makes them "pretty difficult to say much about" by traditional mathematical methods. Their study "is really a matter of ruliology", and whether such definitions are consistent or total remains open in general.
  - Wolfram also writes: "In retrospect, back in 1981 I should have been able to take the 'Q sequence' and recognize in it the essential 'rule 30 phenomenon'" [S: summarizer paraphrase with short quotes from the essay]. ([Wolfram 2024](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/))
- **Undecidability context.** Celaya–Ruskey: for one explicit nested recurrence, whether a given finite initial condition yields a total ("calculable") sequence is undecidable, by simulating Post 2-tag systems [P]. ([arXiv:1203.0586](https://arxiv.org/abs/1203.0586))
- **The proxy strategy (Cloitre v1 §11–12).** Prove |Q(n) − Q̃(n)| = o(n), or O(n/√log n). "A proof would imply Q(n)/n → 1/2 and the well-definedness of Q" [P]. ([v1](https://arxiv.org/html/2604.06237v1))
- **The finite-symbolic-model strategy.** Mantovanelli v2 §11.8 proposes investigating "whether partial symbolic models exist for the unperturbed case, and if so, why they fail to close" [P].
- **Methods that work for relatives, and why they need structure:**
  - slow sequences and tree interpretations (Tanny school; Isgur et al.; Dalton–Rahman–Tanny);
  - automata and Walnut (Allouche–Shallit for V; Shallit 2023; Campbell–Cloitre 2026; Cloitre–Ma–Zhang 2026 with Lean 4);
  - symbolic induction for quasipolynomial or linear-recurrent solutions and parametric death proofs (Fox);
  - Pinn's continuous functional-equation and random-matrix model, which reproduces Q's anomalous scaling (2−η)^k and 2^{αk}. Pinn presents it as an exploratory model, not a proof [P]. ([arXiv:2603.17509](https://arxiv.org/abs/2603.17509))
- **Fox's thesis, Ch. 11 ("Summary of Open Problems and Conjectures") [P].**
  - "The primary and most classical open question about nested recurrences is whether the Hofstadter Q-sequence weakly dies."
  - The sequences he could analyse "have either an interleaved or slow structure. But, it is theoretically possible that, after a very long initial condition, the Hofstadter Q-sequence eventually becomes interleaved or slow. We consider this an unlikely, but remote, possibility."
  - "proofs of slowness are typically considerably more involved and ad hoc than proofs of interleaved structure."
  - His code (slow-solution search, `nicehof`, `nonstdhof`) is at github.com/nhf216/thesis. ([Fox thesis](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- I found no published statements by Shallit or Sloane specifically assessing how hard Q's totality is, beyond Sloane's OEIS comment [P: absence].

### Inferences
- Any proof of totality must establish an a priori bound Q(n) ≤ n along the defined prefix (equivalently Q(n−1) < n). In practice this means proving something like |Q(n) − n/2| < n/2 for all n.
- Because Pinn's statistics show fluctuations of order n^{0.88}, the margin is huge but the control problem is global. The lookbacks n − Q(n−1) ≈ n/2 couple scale n to scale n/2 in a "renormalization" fashion; Mantovanelli 2603.16111v1 makes the same point for Q̃.
- So a plausible route is a two-scale induction with an error envelope that grows more slowly than n/2. The difficulty is that the fluctuation at scale n is a nonlinear function of fluctuations at scale n/2, with apparently random signs. This is my reading, not a published programme.
- Totality is a Π⁰₁ statement ("for every n the computation doesn't die"). It cannot be refuted except by a finite counterexample, which the computations to 3·10^10 have not found. The Celaya–Ruskey undecidability concerns a different recurrence and the uniform problem, not Q's individual truth value.

### Gaps
- I found no talk, preprint or post by Tanny, Shallit, Sloane or Wolfram giving a concrete strategy or difficulty estimate for Q's totality.
- I did not read Guy's E31 text, which might contain Guy's or Conway's remarks.
- Fox's thesis Ch. 11 contains no proof strategy for Q's totality, only the framing quoted above.

## 6. Equivalent reformulations and intermediate statements that are meaningful Lean targets

### Takeaway
Q's totality itself is far out of reach. There is, however, a ladder of meaningful, literature-backed targets:
1. Exact specifications and equivalences: uniqueness; total ⟺ ∀n Q(n) ≤ n; the death criterion; the ⟨1,2⟩ and ⟨1,2,3⟩ aliases; shift invariance. Golomb's conditional limit (if Q(n)/n converges, the limit is 1/2) is the one Q-specific theorem.
2. Finite verifications: existence to N; generation boundaries b(k) = 3·2^{k−2} for k ≤ 10; Fox's witnesses Q₈(420)=430 and others.
3. Parametric theorems about the same recurrence: Fox's "⟨1..N⟩ dies for all N ≥ 21 at index N+29"; Golomb's ⟨3,2,1⟩ solution; Ruskey's Fibonacci solution; Fox's quasipolynomials.
4. Proven totality theorems for relatives: Deane–Gentile's diluted theorem; Conolly, Tanny and V slow sequences; above all the 2026 perturbed Q̃ (Cloitre's proof, plus Mantovanelli's reconstruction lemma).
5. Conditional statements: Erdős #422 consequences under totality; Cloitre's proxy implication.

### Cited Findings
- **Definitions and equivalences** [P]:
  - Fox's death definition (dies at n iff Q(n−1) ≥ n) [arXiv:1807.01365](https://arxiv.org/abs/1807.01365).
  - BKT: both Q(n−1), Q(n−2) < n.
  - Deane–Gentile: exists ⟺ ∀n 1 ≤ q(n) ≤ n, with the lower bound trivial since q(n) is a sum of positive terms [arXiv:2311.13854](https://arxiv.org/abs/2311.13854).
  - The coordinator's padded definition, `IsQ` and `HofstadterQTotal := ∃ f, IsQ f` [Session].
- **Aliases:** ⟨1,2⟩ gives "Hofstadter's sequence without the initial 1", and ⟨1,2,3⟩ is the same sequence [P: Fox 2018 §2; thesis §9.1].
- **Shift invariance (Fox thesis, Prop. 2.7).** Take any "basic linear" nested recurrence with constant P(n)=c (the Q-recurrence is one) under the *strong-death / zero* convention.
  - If (a_n) solves it with initial condition ⟨a_1..a_k⟩, then b_1 = 0, b_n = a_{n−1} also solves it, generated by ⟨0, a_1, …, a_k⟩.
  - The proof is a one-line induction after extending by zeros to nonpositive indices [P]. ([Fox thesis §2.4](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf))
- **Golomb's conditional limit:** if lim Q(n)/n exists, it equals 1/2 [P: Fox thesis Ch. 2, attributing it to Golomb]. Section 1 sketches an elementary proof.
- **Finite facts suitable for `decide` or `native_decide` checks** [P unless noted]:
  - existence to 3·10^10 (only ~10^4–10^7 is feasible in Lean per the [Session] notes);
  - Q(12)=8 > Q(11)+1;
  - the first decrease at n=16;
  - Q₈(420)=430, Q₁₁(199)=206, Q₁₂(69)=77 (death witnesses);
  - the Dalton et al. generation function M(n)=M(n−Q(n−1))+1 with b(k)=3·2^{k−2} for 3 ≤ k ≤ 10 [P: Pinn 2026 Table 2].
- **Parametric, all-N statements about the Q-recurrence** [P]:
  - Fox Thm 1: for N ≥ 21 the ⟨1..N⟩ sequence has exactly N+28 terms, from 28 symbolic terms valid for N ≥ 13; for 14 ≤ N ≤ 20 it has N+32. This is a good target for symbolic or `omega` reasoning.
  - Fox Thm 2 (strong convention) and Proposition 1, Lemma 1 (period-5 patterns by induction).
- **Explicit total solutions (each "lives" by an induction proof)** [P]:
  - Golomb ⟨3,2,1⟩: Q_G(3k)=3k−2, Q_G(3k+1)=3, Q_G(3k+2)=3k+2 (A244477).
  - Ruskey ⟨0̄;3,6,5,3,6,8⟩ (Fibonacci).
  - Fox's quasipolynomial families (Integers 16 (2016) A68) and the App. A families of the thesis (periods 2–5).
- **Theorems on relatives** [P]:
  - Deane–Gentile Thm 1.3 (diluted).
  - BKT: V is slow.
  - Fox: B is slow.
  - Conolly and Tanny sequences.
  - Q̃ well-defined (Cloitre Thm 1.1(i); Mantovanelli Thm 1.1).
  - Mantovanelli Thm 2.4 (binary reconstruction principle) and Lemmas 2.1–2.3. Cloitre Lemma 2.2 (parity split) and Lemma 3.1.
- **Lean and Coq precedents for nested recurrences** [P]:
  - Cloitre–Ma–Zhang 2026 formalize, in Lean 4, the identification of A076502 with a Padovan-numeration shift, its discrepancy bound, its offset set, a morphic identity and a balance constant [arXiv:2609.33421](https://arxiv.org/abs/2609.33421).
  - Letouzey formalized most of his results on generalized Hofstadter G-functions in Coq/Rocq [arXiv:2502.12615](https://arxiv.org/abs/2502.12615).
  - Mantovanelli v1 and v2 named Lean/Coq formalization as future work, and v3 states it is not formalized [P].
- **Conditional statements** [P/Session]:
  - formal-conjectures' Erdős-422 statements are implications from `IsHofstadterQ f`. They are vacuous if no such f exists, and there is no separate totality statement [Session].
  - Cloitre's implication (v1 §11): for the conjectured |Q(n)−Q̃(n)| = O(n/√log n), "Since n/√log n = o(n), a proof would imply Q(n)/n → 1/2 and the well-definedness of Q for all n". Open problem 1 asks for the weaker o(n) bound [P]. For Lean, the hypothesis must be stated on the defined prefix, e.g. "∀ n, Q defined on [1,n] → |Q(n) − Q̃(n)| ≤ g(n)" with g(n) = o(n); otherwise it presupposes totality.

### Inferences
**A suggested ladder of targets** (my synthesis; sources as above):
1. **(Easy)** Uniqueness of solutions to the relational spec; `total ↔ ∀ n ≥ 1, Q n ≤ n`; `total ↔ ∀ n ≥ 3, Q (n-1) < n`; "Q dies at n ↔ Q(n−1) ≥ n" for the first such n.
2. **(Easy)** The shift lemma: the ⟨1,2⟩-sequence equals n ↦ Q(n+1) on any prefix where Q(m) ≤ m−1. Also ⟨1,2,3⟩ = ⟨1,2⟩. Fox's Prop. 2.7, shift invariance under the zero convention, is a clean general lemma.
2a. **(Easy–medium; Q-specific and nontrivial in spirit)** Golomb's conditional limit: `total → (Q n / n → c) → c = 1/2`. My three-case sketch in Section 1 uses only Q(m) ≤ m and Q ≥ 1, plus a doubling argument for c = 0. This is the only published "theorem about Q itself" found, so it makes a natural flagship target. A stronger form, `total → liminf Q(n)/n ≤ 1/2 ∧ 1/2 ≤ limsup Q(n)/n`, is my unpublished derivation (Section 1) and should be checked by formalization.
3. **(Finite)** Existence to N (the coordinator's experiments), the death witnesses for N = 8, 11, 12, and b(k) for k ≤ 10.
4. **(Medium; probably the best "real mathematics" target on the Q-recurrence itself)** Fox Thm 1 for all N ≥ 21. Its 28 symbolic terms and final lookback −N+21 ≤ 0 give a uniform, parameterised death proof.
5. **(Medium)** Golomb's ⟨3,2,1⟩ quasilinear solution is total; Ruskey's Fibonacci solution; one of Fox's quasipolynomial families.
6. **(Medium–hard)** Deane–Gentile Thm 1.3; slow-sequence totality theorems (Conolly, V).
7. **(Hard but finite in scope)** Totality of Q̃ via Cloitre's interleaving construction. A Lean-checked replay of Mantovanelli's certificate would be an alternative, but it needs his checkers to be reverified.
8. **(Conditional)** "If |Q(n) − n/2| ≤ n/2 − 1 whenever Q is defined on [1, n], then Q is total", trivially. Cloitre's proxy implication is a nontrivial variant, but it has to be phrased on the defined prefix to avoid presupposing totality.
9. **(Open; state only)** Totality of Q; Q(n)/n → 1/2; Erdős #422. State these as Props, not as theorems with `sorry`, to keep `answer(sorry)`-style ambiguity out.

### Gaps
- Apart from Golomb's conditional limit (reported by Fox, not seen in Golomb's own text), I found no published "if Q is total then …" theorems with nontrivial content.
  - My unpublished sketch (Section 1) gives "total ⇒ liminf Q(n)/n ≤ 1/2 ≤ limsup Q(n)/n", and hence "total ⇒ Q unbounded".
  - Nothing in the literature or in my sketch gives "total ⇒ Q(n) ≥ cn for all large n" or "total ⇒ Q(n) → ∞".
- I found no published invariant that holds for all computed terms beyond existence itself: no verified bounds on Q(n)/n or on generation-parent structure over the full 3·10^10 range.

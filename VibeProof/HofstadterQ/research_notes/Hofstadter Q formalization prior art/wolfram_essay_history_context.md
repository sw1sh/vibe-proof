# Wolfram's "Nestedly Recursive Functions" (27 Sep 2024): history and context for formalizing whether Hofstadter's Q is total

**Source tags.**
- **[E]**: the essay's prose.
- **[E-img]**: a document or code shown as an image inside the essay. I transcribed these from the downloaded images.
- **[E-bib]**: the essay's bibliography PDF, in its 2024-09-27 version and its 2025-02-18 revision.
- **[NKS]**: *A New Kind of Science* online (2002).
- **[WM]**: Wolfram's public 2021 and 2024 "WorkingMaterial" notebooks on the Wolfram Cloud.
- **[O]**: other sources.

"Inferences" are my own reasoning. "Checked" means a keyword search or computation I ran on the downloaded text.

**How this was read.** I read the essay in full. I fetched it with curl and extracted the text. I viewed the ~70 images that carry content (letter scans, code, family definitions) and both bibliography PDFs. I also read all 5 pages of the OEIS scan of the 1977/1991 Hofstadter–Sloane correspondence.

**Relation to existing notes.** This file replaces the WebFetch-based summary in `ai_labs_and_ai_for_math.md` §9, whose author had not read the thanks or bibliography. It also fills the gap in `q_sequence_mathematics.md` §2 ("I did not read [the letter scan]").

**Main correction to earlier notes.** The essay *prose* never mentions existence or totality of Q. The "EXISTS … 50,000 terms" sentence appears only inside the reproduced letter image.

---

## 1. History: how Q and the "does Q(n) exist for all n?" question arose and spread (1961–1998)

### Takeaway
The essay's "Some History" section tells the story mostly through scanned documents. The existence question appears only in the reproduced excerpt of Hofstadter's 15 July 1977 letter to Sloane ("it is not obvious by any means that Q(n) even EXISTS for all n -- yet it 'clearly' does, from computing it out to 50,000 terms"). Wolfram's prose quotes only "horse of an entirely nother color" and "absolutely CRAZY".

The sequence then spread through several channels:
- Sloane passed the letter to Graham, leading to Erdős–Graham (1980). Their problem asks whether f "miss[es] infinitely many integers", not whether it exists.
- Guy's E31.
- GEB p. 137 (17 terms).
- Conolly (1986).
- Golomb's unfinished manuscript (c. 1990; 280 terms).
- Vardi in 1991: "Nothing is known about this sequence".
- Pinn (1998), the first published large-scale picture.

Tanny appears only in the bibliography. Female/Male and Figure-Figure are not mentioned in the essay, although both are in the full 1977 letter.

### Cited Findings

#### The 15 July 1977 letter (three excerpts reproduced in the essay)
- [E] Framing: "in 1977 he sent a letter to Neil Sloane, creator of the 1973 A Handbook of Integer Sequences (and what's now the Online Encyclopedia of Integer Sequences, or OEIS)". The prose gives only the year; the exact date is visible on the scan. — [essay, "Some History"](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] **Excerpt 1.**
  - Letterhead: Stanford University, Institute for Mathematical Studies in the Social Sciences, Ventura Hall. Dated "July 15, 1977".
  - Addressed to "N.J.A. Sloane, Mathematics Research Center, Bell Telephone Laboratories, Murray Hill". Salutation: "Dear 'N.J.A.',".
  - Opening: "I have quite a few sequences to offer you, for your new edition. A lot of them are based on the following notion, which I call 'Eta-sequences': eta_k(r;s) = [(k+1)r + s] − [kr + s]".
  - Handwritten sequence-ID annotations in the margin: 6336, 6341, 6999, 48973, 1030, 5206, 5374, 5378, 5379, 5185, 5228, 5243.
  - — [scan in essay](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg10.png)
- [E] Wolfram on excerpt 1: "Doug's 'eta sequences' had actually been studied in number theory before—in fact, since at least the 1920s (they are now usually called Beatty sequences)." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] **Excerpt 2.** "Now for some other kinds of sequences. How about the recursive functions G(0) = 0, G(n) = n − G(G(n−1)) [annotated A5206]; H(0) = 0, H(n) = n − H(H(H(n−1))) [A5374] etc.. You can plot them as 'trees' (i.e. put n above G(n)) and you get an interestingly recursive Fibonacci-tree for G:" An ASCII tree follows. — [scan in essay](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg11.png)
- [E] Wolfram on excerpt 2: "these particular sequences (which were derived from golden ratio versions of his 'eta sequences') have a very regular form—which we would now call nested … just a small change in initial conditions in what I'm calling S1 would have led to much wilder behavior. But that apparently wasn't something Doug happened to notice." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] **Excerpt 3 (verbatim).** "Now the following sequence is a horse of an entirely nother color. Q(1) = Q(2) = 1; Q(n) = Q(n−Q(n−1)) + Q(n−Q(n−2)). This sequence is absolutely CRAZY. I showed it to Paul Erdős, and he found it quite intriguing. It is like Fibonacci-numbers because you're always adding previous terms, but you are told how far back to count by the last two terms (instead of just adding them). There is NO rhyme nor rule to the behavior of this sequence (despite the fact that if you try the first several values at n = 3 times a power of 2, you will think you see a pattern. But it flops out there somewhere. In fact, it is not obvious by any means that Q(n) even EXISTS for all n -- yet it "clearly" does, from computing it out to 50,000 terms."
  - The margin reads "✓ 5185", i.e. A005185.
  - In the typescript the second Q of the recurrence looks like an "O": "+ O(n−Q(n−2))".
  - — [scan in essay](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg12.png)
- [E] Wolfram's prose on excerpt 3 is only: "there was another nestedly recursive sequence—that Doug described as a 'horse of an entirely nother color': the 'absolutely CRAZY' Q sequence".
  - Checked: "EXISTS", "50,000", and the whole words "exist", "existence", "die", "dies" and "dying" do not occur in the prose.
  - The 50,000-term computation is alluded to only obliquely, in the GEB paragraph: "Doug listed only 17 terms (which, until I was writing this, was all I assumed he had computed)". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)

#### The rest of the 1977 letter and Sloane's 1991 reply (OEIS scan; not shown in the essay)
- [O] The scan is titled "D. R. Hofstadter and N. J. A. Sloane, Correspondence, 1977 and 1991". It is 5 pages and is the first entry in the essay's bibliography. Beyond the essay's excerpts it contains the following.
  - Four "interesting" eta-sequence choices (r = √2 or φ; s = 0 or 1/2).
  - "I am enclosing an unfinished write-up on Eta-sequences which I believe ought to be of interest not only to you, but also to R.L. Graham and perhaps others at Bell Labs … I have been too busy writing a book called 'Goedel, Escher, Bach: an Eternal Golden Braid' to finish 'Eta-Lore'".
  - On G: "In the case of G, it equals the sequence [n phi]. But not for H or higher orders."
  - The intertwined Female/Male pair, "F(0) = 1, M(0) = 0, F(n) = n − M(F(n−1)), G(n) = n − F(M(n−1))" [sic; annotated 5378, 5379], followed by "Make the trees!".
  - After Q, the "weird numbers" 1, 3, 7, 12, 18, 26, 35, … (annotated 5228; this is Figure-Figure): "the top sequence is the complement of its first-difference sequence".
  - a(n) = [3a(n−1)/2]+1: "I believe (but have never shown) that it is intimately related to the 3n+1 problem".
  - The "C-bar numbers" 4, 7, 9, 12, … (annotated 5243): "it is intriguing to ask if they are even infinite in number, or if eventually every number is a c-number. Erdős liked this question quite a lot, too."
  - "Another Erdős liked": products of two earlier elements minus 1 (annotated 5244), with the question "How dense is this asymptotically?"
  - v(n) (annotated 6336): "I have never tried to prove this so I don't even know if this is trivial or deep. I have made up so many problems in my life that I haven't had the time to think about most of them, unfortunately."
  - P.S.: "From Aug. 10 on, at Computer Science Dept, Indiana Univ., Bloomington".
  - Page 5 is Sloane's letter to Hofstadter of June 25, 1991 (AT&T Bell Laboratories): "I enclose a copy of your letter. It is probably the most interesting I received in eighteen years of correspondence!"
  - — [OEIS scan a006336.pdf](https://oeis.org/A006336/a006336.pdf)

#### Gödel, Escher, Bach (1979)
- [E] "Two years later, Doug's Gödel, Escher, Bach book was published—and in it, tucked away at the bottom of page 137 … there was the Q sequence". Then: "Strangely, though, there was no picture of it, and Doug listed only 17 terms". And: "So now nestedly recursive sequences were out in the open—in what quickly became a very popular book. But I don't think many people noticed them there (though, as I'll discuss, I did)." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] The GEB text as reproduced:
  - "A Chaotic Sequence. One last example of recursion in number theory leads to a small mystery. … Q(n) = Q(n − Q(n−1)) + Q(n − Q(n−2)) for n > 2, Q(1) = Q(2) = 1."
  - It lists the first 17 terms, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 6, 8, 8, 8, 10, 9, 10, and walks through computing Q(18) = 11.
  - "The resulting sequence is, to put it mildly, erratic. The further out you go, the less sense it seems to make. … chaos produced in a very orderly manner. One is naturally led to wonder whether the apparent chaos conceals some subtle regularity. … what is of interest is whether there is another way of characterizing this sequence—and with luck, a nonrecursive way."
  - The excerpt says nothing about existence.
  - — [scan 1](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg13.png), [scan 2](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg14.png)
- [E-bib] The bibliography cites GEB's sections "Diagram G and Recursive Sequences" and "A Chaotic Sequence", Basic Books, pp. 135–138. — [bibliography, 2025 revision](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)
- [E] Checked: the prose never names Female/Male, Figure-Figure or the "Diagram G" material. G and H appear only in the letter scan. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/)

#### Hofstadter before 1977 ("as Doug tells it")
- [E] "Back in 1961, right on the Stanford campus, a then-16-year-old Douglas Hofstadter was being led towards nestedly recursive functions."
  - He noticed that squares fall in gaps of 1 or 2 between triangular numbers, with patterns in those gaps.
  - He used Algol, which "(like LISP and unlike Fortran) supported recursion".
  - He played an Eleusis-like "function game" and "found that functions that were defined recursively were the ones people found it hardest to guess".
  - In the mid-1970s he was "back at Stanford—writing what became his book Gödel, Escher, Bach".
  - Thanks section: "Thanks to Doug Hofstadter for extensive answers to questions about history for this piece."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#thanks)

#### Spread: Sloane → Graham → Erdős–Graham; Guy's E31
- [E] "Neil Sloane showed Doug's 1977 letter to his Bell Labs colleague Ron Graham, who within a year made a small mention of the Q sequence in a staid academic math publication (in a characteristic 'state-it-as-a-problem' Erdös form)". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] The Erdős–Graham text as reproduced, verbatim: "The following problems were recently raised by Hofstadter [Hofs (77)]. (i) Define f(n) as follows: f(1) = f(2) = 1, f(n) = f(n − f(n−1)) + f(n − f(n−2)), n > 2. Does f(n) miss infinitely many integers? What is its behavior in general?" — [scan in essay](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg16.png)
- [E-bib] Bibliography entry: P. Erdős and R.L. Graham (1980), *Old and New Problems and Results in Combinatorial Number Theory*, L'Enseignement Mathématique, Université de Genève, linked at mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf. — [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)
- [E] "There was a small and tight-knit circle of serious mathematicians—essentially all of whom, as it happens, I personally knew—who would chase these kinds of easy-to-state-but-hard-to-solve problems. Another was Richard Guy, who soon included the sequence as part of problem E31 in his Unsolved Problems in Number Theory, and mentioned it again a few years later." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-bib] Guy's entries:
  - R. Guy (1981), "E31. Three sequences of Hofstadter", UPINT (Springer), pp. 129–130, with a note on the 2nd edition (1994).
  - R. Guy (1986), "Some Suspiciously Simple Sequences", AMM 93(3), 186–190.
  - — [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)

#### Conolly, Conway's $10,000 sequence, Mallows (1986–1991)
- [E] "for most of the 1980s little was heard about the sequence." Brian Conolly, "a senior British applied mathematician" outside the tight-knit circle, had "made some progress, and in 1986 had written to Guy about it. Guy apparently misplaced the letter, but later told Conolly that John Conway and Sol Golomb had worked on similar things." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E] "Conway presumably got the idea from Hofstadter's work (though he had a habit of obfuscating his sources)."
  - "On July 15, 1988, Conway gave a talk at Bell Labs entitled 'Some Crazy Sequences' (note the word 'crazy', just like in Hofstadter's letter to Sloane)".
  - The talk concerned the "regular-enough-to-be-mathematically-interesting sequence (which we're calling G3111 here)". The essay's code image gives it as `f[1] = f[2] = 1; f[n_] := f[f[n − 1]] + f[n − f[n − 1]]` (OEIS A004001).
  - "Conway couldn't mathematically prove certain features of the wiggles in the sequence—and in his talk offered a $10,000 prize for anyone who could. By August a Bell Labs mathematician named Colin Mallows had done it. Conway claimed (later to be contradicted by video evidence) that he'd only offered $1000".
  - The affair became the New York Times story of August 30, 1988, "Intellectual Duel: Brash Challenge, Swift Response", and the sequence "became known as 'Conway's Challenge Sequence'".
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history); [code image](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg19.png)
- [E-bib] Related bibliography entries:
  - J.H. Conway (1988), *Some Crazy Sequences* [video], July 15, 1988.
  - D. Newman (1988), "E3274", AMM 95(6).
  - B.W. Conolly (1989), "Meta-Fibonacci sequences (a letter from B.W. Conolly)", in Vajda's *Fibonacci & Lucas Numbers, and the Golden Section*, pp. 127–138.
  - C.L. Mallows (1991), "Conway's Challenge Sequence", AMM 98(1), 5–20.
  - Kubo–Vakil (1996).
  - — [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)

#### Golomb's unfinished "Discrete Chaos" manuscript (c. 1990)
- [E] Golomb "started writing a paper—though never finished it. … He'd computed 280 terms of the Q sequence (he wasn't much of a computer user) and noticed a few coincidences."
  - Golomb also introduced `f[n_] := f[n − f[n − 1]]`, "no doubt inspired by his work on feedback shift registers".
  - Its behaviour "depends greatly on the initial conditions, though is always eventually periodic—with his student Unjeng Cheng having found long-period examples."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] The manuscript's title page reads "Discrete Chaos: Sequences Satisfying 'Strange' Recursions", Solomon W. Golomb, Communication Sciences Institute, USC. Its "Historical Summary" says Hofstadter called {q_n} "a 'strange' recursion, in that the subscripts depend on terms in the sequence itself. He asserted that this sequence has no discernible regularities, and this remains very nearly true." — [scan 1](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg21.png), [scan 2](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg22.png)

#### Vardi (1991), "Not so much", Pinn (1998)
- [E-img] Ilan Vardi's email to Wolfram, from the February 1991 exchange reproduced in the essay:
  - "I didn't find out very much. I thought that it would be interesting to check out the series for n around a billion or so, but that required a Cray for its large memory."
  - "Nothing is known about this sequence."
  - He relays Conolly's point that "Hofstadter's sequence is not the right thing to look at" because the second term is not "symmetric in n". He gives Conolly's alternative F(n) = F(n−F(n−1)) + F(n−1−F(n−2)) with the formula F(2^m + k) = 2^(m−1) + F(k+1).
  - "This is one of the reasons why I stopped looking at the Hofstadter function (along with the fact that I couldn't prove anything about it)."
  - Wolfram replied: "certainly my hope that the output of the sequence would be 'random' seems fairly remote".
  - — [email 1](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg8.png), [email 2](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg9.png)
- [E] "OK, so by 1988 nestedly recursive functions had at least some notoriety. So what happened next? Not so much. There's a modest academic literature … mostly concentrated very specifically around 'Conway's Challenge Sequence', Hofstadter's Q function, or very similar 'meta Fibonacci' generalizations of them. And so far as I know, even the first published large-scale picture of the Q sequence only appeared in 1998 (though I had pictures of it many years earlier)". The prose does not name Pinn; the scans that follow identify the work as Klaus Pinn's "Order and Chaos in Hofstadter's Q(n) Sequence" ("Received May 26, 1998; accepted June 30, 1998") and its Figure 1, "The first 2,000 Q-numbers". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E] Why more wasn't done: "they tend to have too much computational irreducibility—making it pretty difficult to say much about them in traditional mathematical ways. But perhaps more important, studying them broadly is really a matter of ruliology". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)

#### Tanny and the wider meta-Fibonacci literature
- [E] Checked: the prose never mentions Tanny, Fox, Ruskey, Celaya, Alkan or Allouche. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/)
- [E-bib] The bibliography's "Specific Research Discussions" section (pp. 1–5) lists the following.
  - Tanny: Tanny (1992), "A well-behaved cousin of the Hofstadter sequence"; Higham–Tanny (1993) and (1994), the latter "A tamely chaotic meta-Fibonacci sequence"; Barbeau–Tanny (1996), "On a Strange Recursion of Golomb"; Barbeau–Chew–Tanny (1997); Callaghan–Chew–Tanny (2005); several Isgur et al. papers; Sunohara–Tanny (2018), "On the solution space of the Golomb recursion".
  - Fox:
    - (2016) "Linear Recurrent Subsequences…" and "Quasipolynomial Solutions to the Hofstadter Q-Recurrence";
    - (2017) thesis and "A Slow Relative of Hofstadter's Q-Sequence";
    - (2018) JSC "Discovering linear-recurrent solutions to Hofstadter-like recurrences using symbolic computation".
  - Others: Downey–Griswold (1984); Arkin et al. (1990); Kiss–Zay (1992); Fraenkel (1994); Kubo–Vakil (1996); Pinn (1998, 2000); Grytczuk (2004); Ruskey (2011); Allouche–Shallit (2012); Alkan (2017, 2018 ×2); Naimi–Sundberg (2019); Sobolewski–Ulas (2023).
  - Hofstadter's 2014 Rutgers seminar video.
  - Student projects: Song (2021) and Adler (2024).
  - Fox's arXiv 1807.01365 ("A New Approach to the Hofstadter Q-Recurrence", with the death theorems for ⟨1..N⟩) is **not** listed.
  - — [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)

#### Chronology (dates from the prose or from the reproduced documents)

| Date | Event | Shown in essay? | Source |
|---|---|---|---|
| 1961 | Hofstadter (16) at Stanford; triangular-number gaps; Algol recursion; "function game" | no | [E] |
| mid-1970s | Hofstadter back at Stanford writing GEB | no | [E] |
| 1977-07-15 | Letter to Sloane: eta sequences, G, H, (F/M), Q incl. "EXISTS … 50,000 terms", (Figure-Figure, C-bar, products−1, v(n)) | 3 excerpts; the full letter is on OEIS | [E-img], [O] |
| 1979 | GEB pp. 135–138: "A Chaotic Sequence", 17 terms; Wolfram sees GEB "soon after it came out" | GEB yes | [E], [E-img] |
| 1980 (essay: "within a year" of seeing the letter) | Erdős–Graham problem (i) | yes | [E-img], [E-bib] |
| 1981 | Guy, UPINT E31; Wolfram's SMP 1.0 "XHof" (Jul 1981) | SMP page yes | [E-bib], [E-img] |
| 1986 | Conolly writes to Guy; Guy's "Suspiciously Simple Sequences" | no | [E], [E-bib] |
| 1987-09-26 | Mathematica (then "Technique") test file with `Hofstadter[n]` | yes | [E-img] |
| 1988-06-23 | Mathematica 1.0 book: "A complete package for the Hofstadter function" (p. 518) | yes | [E-img] |
| 1988-07-15 | Conway, "Some Crazy Sequences", $10,000 prize | plot | [E] |
| 1988-08 / 08-30 | Mallows' solution; NYT story | no | [E] |
| c. 1990 | Golomb, "Discrete Chaos" (280 Q terms) | yes | [E], [E-img] |
| 1991-02-03/04 | Wolfram–Vardi emails ("Nothing is known about this sequence") | yes | [E-img] |
| 1991-06-25 | Sloane's reply to Hofstadter | no | [O] |
| 1993-08-13 | Wolfram's enumeration; "checked out to 10 million terms" | yes | [E] |
| 1998 | Pinn, first published large-scale picture of Q | yes | [E] |
| 2002 | NKS pp. 128–131 plus 7 notes; Q is rule (e) | gallery | [E], [NKS] |
| 2003-06 / 07-11 | Summer School live experiment; convention f=1 off the positive integers; T311 | yes | [E] |
| 2024-09-27 | Essay; bibliography revised 2025-02-18 | — | [E], [E-bib] |

### Inferences
- **Where the existence question comes from.** It is Hofstadter's own remark of July 1977, paired with an empirical check to 50,000 terms. Neither GEB (1979) nor Erdős–Graham (1980), as reproduced, raises existence. GEB asks for a "nonrecursive" characterization; Erdős–Graham asks about missed integers and "behavior in general".
- **Why #422's statements are vacuous if Q dies.** Erdős #422 inherits the Erdős–Graham phrasing, which silently presupposes that f is defined everywhere. This is the root of the vacuity issue in formal-conjectures noted in `00_session_findings.md`.
- **The documented "verified range" history.**
  - Hofstadter: 50,000 terms (1977).
  - Golomb: 280 terms (c. 1990).
  - Vardi: wanted ~10^9 but lacked memory (1991).
  - Wolfram's 1993 enumeration: run "out to 10 million terms". The essay does not say explicitly that Q was among the runs (see §3).
  - Then Pearce 10^10 (2014) and Carr 3·10^10 (2023), from existing notes.
- **An early observation of Q's structure.** Hofstadter's 1977 remark about n = 3·2^k ("you will think you see a pattern. But it flops out there somewhere") is the earliest documented observation of the dyadic "generation" structure that Pinn later studied. This is my reading; the essay does not draw the connection.
- **Reliability.** The essay is reliable on documents it reproduces. Some prose claims are oral history or opinion and cannot be checked from the essay: "As Doug tells it", Conway "obfuscating his sources", and the $1000-vs-$10,000 "video evidence".

### Gaps
- I did not open the Erdős–Graham PDF or Guy's E31 text. The page number of problem (i) is unconfirmed, and so is the exact wording Guy used about existence.
- The essay says Graham wrote it up "within a year" of seeing the 1977 letter, but its bibliography dates the publication 1980. An earlier printing may exist; I did not resolve this.
- Neither the essay nor the letter says how or on what machine Hofstadter computed 50,000 terms.

---

## 2. History: earlier roots of nested recursion (recursion theory, Ackermann, Péter, McCarthy's 91, Takeuchi)

### Takeaway
The essay traces nested recursion through several strands:
- induction and Fibonacci numbers;
- Peano and Hilbert;
- Ackermann's 1927/28 function, which contains a nested recursion "without any particular comment";
- Gödel, and Rózsa Péter's chapter "Nested Recursion";
- Tait's 1961 "Nested Recursion";
- the program-verification line: McCarthy's 91 function (c. 1968), Manna's 1974 "Fixpoints of Functionals", Takeuchi's 1978 TAK.

Wolfram's verdict is that in all these the focus was on evaluation, not behaviour. The bibliography's "Nested Recursion in General" section, which includes Giesl's 1997 paper on termination of nested recursion, is the formal-methods lineage most relevant to Lean.

### Cited Findings
- [E] "Once one has the concept of functions and the concept of recursion, nestedly recursive functions aren't in some sense a 'complicated idea'. And between this fact and the fact that nestedly recursive functions haven't historically had a clear place in any major line of mathematical or other development it's quite difficult to be sure one's accurately tracing their history." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E] From antiquity to the 1800s:
  - induction in Euclid (c. 300 BC);
  - Fibonacci numbers in Indian prosody;
  - Fibonacci's *Liber Abaci* (1202), which "explicitly listed the Fibonacci numbers up to 377";
  - "explicit recursively defined sequences remained largely a curiosity until as late as the latter part of the twentieth century";
  - Peano's axioms (1891);
  - under Hilbert's program, "it was generally assumed that all (integer) functions of interest could actually be defined specifically using primitive recursion."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E] "in 1927 Wilhelm Ackermann (a student of Hilbert's) introduced (in completely modern notation) a 'reasonable mathematical function' that … he showed was not primitive recursive. And right there, in his paper, without any particular comment, is a nestedly recursive function definition". Scans of the paper are shown. [E-bib] dates the paper 1928, "Zum Hilbertschen Aufbau der reellen Zahlen", *Math. Annalen* 99. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history); [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)
- [E] "In 1931 Kurt Gödel further streamlined the representation of recursion, and solidified the notion of general recursion. There soon developed a whole field of recursion theory—though most of it was concerned with general issues, not with specific, concrete recursive functions. A notable exception was the work of Rózsa Péter (Politzer), beginning in the 1930s, and leading in 1957 to her book Recursive Functions—which contains a chapter on 'Nested Recursion' … this chapter doesn't stray far from the particular function Ackermann defined (or at least Péter's variant of it)."
  - [E-bib] lists Péter (1935) and *Rekursive Funktionen* (De Gruyter, **1958**; English translation 1967). This is a minor date mismatch with the prose's 1957.
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E] Recreational mathematics, e.g. Lucas's 1883 Tower of Hanoi: "it doesn't seem as if nestedly recursive functions ever showed up." Theoretical papers on "nested recursion" did appear, for example "one in 1961 by William Tait, then at Stanford" (scan shown). — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E] McCarthy:
  - LISP, and the 1960 paper "Recursive Functions of Symbolic Expressions and Their Computation by Machine".
  - He founded the Stanford AI Lab in 1962.
  - "by 1968 these two topics had come together in an effort to use 'AI methods' to prove properties of programs … John McCarthy came up with an example he intended to be awkward—that's exactly a nestedly recursive function".
  - In Wolfram notation it is `f[n_] := If[n > 100, n − 10, f[f[n + 11]]]`, "known as 'McCarthy's 91-function' … f[n] = 91 only up to n = 102". [Sic: f(102) = 92; the essay presumably means "below 102".]
  - "in pure recursive evaluation the recursion stack can get deep—which back then was a struggle for LISP systems to handle."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-img] The reproduced McCarthy-91 source page reads: "f(x) ⇐ if x>100 then x−10 else f(f(x+11)), where D = {the integers}. For a given integer x, we can construct a sequence of terms, called the computation sequence of f(x). … f(99) → f(f(110)) → f(100) → f(f(111)) → f(101) → 91. In this case we say that f(99) is defined and f(99) = 91."
  - The source is not captioned. [E-bib] lists Manna–Pnueli (1968), "The Validity Problem of the 91-Function" (Stanford AIM-68), and Manna–McCarthy (1970), "Properties of Programs and Partial Function Logic".
  - — [scan in essay](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg5.png)
- [E] Manna's 1974 *Mathematical Theory of Computation*, "in a section entitled 'Fixpoints of Functionals'—presents the 91-function and other nestedly recursively functions, particularly in the context of evaluation-order questions". Takeuchi's 1978 triple recursion and the LISP benchmarks follow. "But in all these cases the focus was on how these functions would be evaluated, not on what their behavior would be (and it was typically very simple)." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#some-history)
- [E-bib] The "Nested Recursion in General" section lists:
  - Skolem (1923); Sudan (1927); Ackermann (1928); Péter (1935, 1958); Kleene (1936); R. Robinson (1948), "Recursion and Double Recursion"; Tait (1961), "Nested Recursion", *Math. Annalen* 143.
  - Manna–Pnueli (1968; and 1970 JACM, "Formalization of Properties of Functional Programs"); Manna–McCarthy (1970); Vuillemin (1973, Stanford thesis), "Proof Techniques for Recursive Programs"; Manna (1974).
  - Takeuchi (1978); Gabriel (1985); Knuth (1991), "Textbook Examples of Recursion"; Vardi (1991), *Computational Recreations in Mathematica*.
  - **Giesl (1997), "Termination of Nested and Mutually Recursive Algorithms", *J. Automated Reasoning* 19**.
  - Wolfram (2023), "Expression Evaluation and Fundamental Physics".
  - — [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)
- [NKS] The 2002 history note: "despite their simple forms, recursive sequences of the kind I discuss here do not for the most part ever appear to have been studied before—although sequence (c) was mentioned in lectures by John Conway around 1988, and the first 17 terms of sequence (e) were given by Douglas Hofstadter in 1979." — [NKS note "History [of recursive sequences]"](https://www.wolframscience.com/nks/notes-4-3--history-of-recursive-sequences/)

### Inferences
- The only strand in the essay's history that directly concerns *proving* things about nested recursion is the program-verification line: partial function logic, fixpoint semantics, Vuillemin, and Giesl's termination of nested recursion. The essay treats it purely historically.
- For Lean, McCarthy's 91 is the classical analogue of Q's totality problem. In both, termination of the nested call cannot be shown without simultaneously proving a value invariant (91: f(x) = max(x−10, 91); Q: Q(k) ≤ k for all k < n).
- The McCarthy scan's notion that "f(99) is defined" because its computation sequence terminates is exactly the partial-function semantics in which "Q(n) EXISTS for all n" is a meaningful claim.

### Gaps
- I did not open Giesl 1997, Manna–McCarthy 1970, Vuillemin 1973 or Knuth 1991. Their usefulness for Q is my inference, not something the essay states.

---

## 3. Wolfram's own history with these functions (1979–2024), and his contacts with the protagonists

### Takeaway
Wolfram's timeline runs as follows:
- **1979:** he sees GEB.
- **1981:** Q goes into SMP 1.0 as `XHof` ("whose values have several properties of randomness").
- **1987–88:** it is a Mathematica test case and a book example.
- **1991:** he emails Vardi about it.
- **1993-08-13:** he enumerates nested recursions, keeping only those with f[1]=f[2]=1 that never look below f[1], and checks "out to 10 million terms".
- **2002:** NKS pp. 128–131 and notes, with Q as rule (e).
- **2003:** a Summer School participant proposes f = 1 off the positive integers, and T311 is found.
- **2007/08:** Demonstrations.
- **2024:** the essay.

His regret: "back in 1981 I should have been able to take the 'Q sequence' and recognize in it the essential 'rule 30 phenomenon'".

### Cited Findings
- [E] "It was soon after it came out in 1979 that I first saw Douglas Hofstadter's book. … I just wanted to know what the 'science meat' in it was. And somehow I found the page about the Q sequence, and filed it away as 'something interesting'." — [essay, "My Personal Story"](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E] "by the time we released Version 1.0 in July 1981, there it was: an external package (hence the 'X' prefix) for evaluating 'Hofstadter's recursive function', elegantly using memoization".
- [E-img] The SMP library page:
  - "XHof — Hofstadter's recursive function — double recursion — generalized Fibonacci sequence — recursion testing — S.Wolfram, Jul 1981."
  - "Hof[n] gives a recursive function defined by Hofstadter, whose values have several properties of randomness."
  - Code: `Hof[1]:Hof[2]:1` and `Hof[$n_=Natp[$n]] :: Hof[$n]:Hof[$n-Hof[$n-1]]+Hof[$n-Hof[$n-2]]`. The definition is guarded to natural-number arguments.
  - Rerun in an SMP 1.5.3 (Aug 4 1986) virtual machine, it gives `Hof[100]` = 56 and the first 50 values.
  - — [SMP page](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg1.png); [SMP VM](https://content.wolfram.com/sites/43/2024/09/sw09252024personalAimg2A.png)
- [E-img] Mathematica:
  - The test file `CombinatorialFunctions.tq`, dated Sat Sep 26 1987 (".tq" comes from the 1987 working name "Technique"), contains `Hofstadter[n_Integer?Positive] := Hofstadter[n] = Hofstadter[n - Hofstadter[n-1]] + Hofstadter[n - Hofstadter[n-2]]` and `Hofstadter[1] = Hofstadter[2] = 1`.
  - The Mathematica 1.0 book (released June 23, 1988), p. 518, "A. Some Examples of Mathematica Packages", shows the same definition captioned "A complete package for the Hofstadter function".
  - — [test file](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg5.png); [book](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg7.png)
- [E] "I don't think I was aware of Conway's lecture that occurred just 18 days later." By the essay's own dates (June 23 to July 15) it is 22 days. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E] 1991: an email exchange with Vardi, who "was working at Wolfram Research and writing a book entitled Computational Recreations in Mathematica, which included a long section on the analysis of Takeuchi's nested recursive function". Vardi suggested a "more symmetrical" function, which turned out to be Conolly's. Wolfram replied with "a picture that made it fairly clear that this particular function would have only nested behavior". See §1 for the email text. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E] **1993-08-13.**
  - "I came to be enumerating possible symbolic forms for recursive functions—and selecting ones that could generate at least 10 terms".
  - The code image shows `Select[allrecs, (Length[RecurrenceTable[#]] == 10)&]`. A companion image calls `RecurrenceTable[f[n - f[n-1]] + 1, 100]`, i.e. right-hand side plus length. That signature differs from today's built-in `RecurrenceTable[eqns, expr, {n, nmax}]`, so it was presumably a personal 1993 helper (my inference).
  - "Was this complexity somehow going to end? I checked out to 10 million terms."
  - "Somewhat shortsightedly I was always using 'Fibonacci-like' initial conditions f[1] = f[2] = 1—and I rejected any recurrence that tried to 'look back' to f[0], f[–1], etc. And at the time, with this constraint, I only found 'really interesting' behavior in two-term recurrences."
  - The first complex case found that night (code image) was `RecurrenceTable[f[f[n-1]] + f[n - 1 - f[n-2]], 400]`, plotted minus n/2.
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions); [1993 code](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg11.png); [first complex case](https://content.wolfram.com/sites/43/2024/09/sw09192024surpriseimg4.png)
- [E-img] A 1993 "survivors" panel shows one rule failing at n ≈ 14 with the message "Graphics::gptn: Coordinate 20 + arg[20] … is not a floating-point number". This is a sequence whose recursion reached an undefined value; in Hofstadter's terms it "died". — [image](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg12.png)
- [E] 1994: "adding a note 'solving' a few of them, and discussing the evaluation graphs of others". 2002: NKS devoted "just four pages (and 7 notes) to 'recursive sequences'", whose gallery "became a favorite page of mine". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#yet-another-ruliological-surprise)
- [NKS] Q in NKS is rule (e) on p. 129: "f[n] = f[n − f[n − 1]] + f[n − f[n − 2]], f[1] = 1, f[2] = 1". The p. 129 caption: "Examples of sequences generated by rules that do not depend only on elements a fixed distance back. Most such rules eventually end up involving meaningless quantities such as f[0] and f[–1], but the particular rules shown here all avoid this problem." — [NKS p. 129](https://www.wolframscience.com/nks/p129--recursive-sequences/)
- [E-img]/[NKS] The NKS "Close approaches" note: "Late 1970s: Douglas Hofstadter studies a recursive sequence with complicated behavior (see page 907), but does not take it far enough to conclude much." — [NKS note](https://www.wolframscience.com/nks/notes-2-3--close-approaches-to-core-discoveries/)
- [E] "In retrospect, back in 1981 I should have been able to take the 'Q sequence' and recognize in it the essential 'rule 30 phenomenon'. … recursive functions were an example where I always felt there was more to do; I felt I'd only just scratched the surface." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E] **The 2003 Summer School** (June 2003; first-day "live experiment"):
  - "At first lots of functions 'didn't work' because they were looking back too far. But then someone piped up 'Why not just say that f[n] is 1 whenever n isn't a positive integer?' Good idea!"
  - T311 was found immediately.
  - "I just couldn't believe that years earlier I'd failed to see the obvious generalization of having 'infinite' initial conditions."
  - A write-up notebook dated the afternoon of July 11, 2003 is titled "The Simplest Recursive Functions with Complex Behavior".
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E] Later activity:
  - January 2004: pictures that "perhaps I should investigate now".
  - "In 2008, they seemed like an 'obvious interesting thing' to add to our Demonstrations Project". [E-bib] dates the three Demonstrations 2007, 2007 and 2008.
  - After the 2020 Physics Project came a "burst of 'finish this' intellectual energy … after a journey of 43 years".
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E] Thanks section:
  - "Thanks to Brad Klee for extensive help."
  - Summer-program students: Roberto Martinez (2003), Eric Rowland (2003), Chris Song (2021), Thomas Adler (2024).
  - Interactions: Ilan Vardi (1991), Tal Kubo (1993), Robby Villegas (2003), Todd Rowland (2003 etc.), Jim Propp (2004), Matthew Szudzik (2005 etc.), Joseph Stocke (2021 etc.), Christopher Gilbert (2024), Max Niedermann (2024).
  - "Thanks to Doug Hofstadter for extensive answers to questions about history for this piece."
  - People he knew personally, with the year met: "John Conway (1984), Paul Erdös (1986), Sol Golomb (1981), Ron Graham (1983), Benoit Mandelbrot (1986), John McCarthy (1981) and Neil Sloane (1983)."
  - — [essay, Thanks](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#thanks)

### Inferences
- **Early implementations used Hofstadter's partial semantics.** SMP 1981 has the `Natp` guard; Mathematica 1987/88 has `n_Integer?Positive`. If Q ever died, these would return an unevaluated expression. The "1 off the positive integers" padding dates only from June 2003, and it came from a participant, not from Hofstadter or Wolfram.
- **Did the 1993 run check Q to 10^7?** The essay says the survivors were "checked out to 10 million terms". Q is a survivor (NKS rule (e)), and the survivor filter rejected any rule that looked back to f[0] or below. Together these suggest Wolfram checked Q's existence to about 10^7 in 1993. The essay never states this for Q explicitly.
- **Identity of the 1993 "first complex" function.** It is NKS rule (g) (f[f[n−1]] + f[n−f[n−2]−1]). It has the same form as Pinn's later "chaotic cousin of Conway's recursive sequence", D(n) = D(D(n−1)) + D(n−1−D(n−2)); see `q_sequence_mathematics.md`. I matched the formulas; the essay does not say this.
- **Wolfram and Hofstadter.** Hofstadter is not in Wolfram's "personally known (date met)" list. The only contact the essay documents is the 2024 historical Q&A.

### Gaps
- When (or whether) Wolfram and Hofstadter met is not stated.
- The essay does not say whether Hofstadter's 2024 answers covered the 50,000-term computation.
- The essay does not say whether the 1993 10^7 check included Q.

---

## 4. Conventions: f[n] = 1 for n ≤ 0 versus Hofstadter's partial setup (where the sequence can "die")

### Takeaway
The essay's "standard initial condition" is f[n] = 1 for all n ≤ 0, implemented as `f[n_ /; n ≤ 0] = 1` or `If[n ≤ 0, 1, …]`. It makes every P/T-type function total by construction ("it always just finds value 1"). The essay never uses the words "die", "dies" or "exist".

It discusses the original-style failure only as rules "looking back too far" (pre-2003) and as "f[n] = f[n]"-type non-progress or inconsistency. It gives no statistics on how often rules die. NKS 2002 says only that "the vast majority of rules written down at random" hit f[0], f[−1].

The essay never analyses Q under Hofstadter's convention. Its F412 (the Q recurrence), under the padding, is exactly Hofstadter's Q shifted by two indices, so Q's totality is equivalent to F412 never looking back beyond its two seed values.

### Cited Findings
- [E-img] P312 is defined as `f[n_ /; n ≤ 0] = 1; f[n_] := 3 + f[n – f[n – 2]]`, "which we can also write as" `f[n_] := If[n ≤ 0, 1, 3 + f[n – f[n – 2]]]`. — [essay, "The Basic Idea"](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#the-basic-idea); [code](https://content.wolfram.com/sites/43/2024/09/sw09192024basicimg2A.png)
- [E] "The gray nodes represent initial conditions: places where f[n] was sampled for n ≤ 0." "We'll be using this same basic setup throughout". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#the-basic-idea)
- [E] 1993: "(For some reason I wanted to keep the same initial conditions as Fibonacci: f[1] = f[2] = 1.)" 2003: "At first lots of functions 'didn't work' because they were looking back too far. But then someone piped up 'Why not just say that f[n] is 1 whenever n isn't a positive integer?'" — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions)
- [E-img] The 2003 Summer School code:
  - `RSValues[list_, t_, init_:1] := Module[{f}, ((f[n_] := f[n] = #1) &)[Plus @@ (#1*f[n - #2*f[n - #3]] &) @@@ list]; f[n_ /; n ≤ 0] = init; Table[f[n], {n, t}]]`, plus a `Sow`/`Reap` variant that records sampled n.
  - The general form is f[n] = Σ_i a_i f[n − b_i f[n − c_i]]. Q is `list = {{1,1,1},{1,1,2}}`.
  - T311 is `f[n_] := f[n] = 3 f[n – f[n – 1]]; f[n_ /; n < 1] = 1`.
  - — [code](https://content.wolfram.com/sites/43/2024/09/sw09252024personalboxc2cimg1.png); [T311](https://content.wolfram.com/sites/43/2024/09/sw09192024surpriseimg6A.png)
- [E] Non-progress and inconsistency (the essay's only "failure modes"):
  - P312 with f[0] = z: "If z ≤ 0 the function f[n] is basically not defined, because the recursion is trying to compute f[n] from f[n], f[n + 1], etc., so never 'makes progress'."
  - T212: "not all choices of initial conditions are possible; some lead to 'f[n] = f[n]' or 'f[n] = f[n + 1]' situations, where the evaluation of the function can't 'make progress'."
  - S10: "Our standard initial condition f[n] = 1 for n ≤ 0 doesn't work here, because it implies that f[1] = 1 – f[1]."
  - The definition `f[n_ /; n ≤ 0] = 1; f[n_] := n – f[f[n – 1]]` gives "f[1] = 1 – f[1], or, in other words, an inconsistency … it seems conceivable that there could be 'insidious inconsistencies' that show up only after many applications of a recursive definition. And it's also conceivable that one could end up with 'loops' like f[i] = f[i]. And things like this could be reasons that f[n] might not be a 'total function', defined for all n."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [E] Why the padding makes things total: the T311 Fold form uses "`Lookup` to give 1 if the value it's trying to look up hasn't been filled in yet, implementing the fact that f[n] = 1 for n ≤ 0. So, yes, our recursive definition might look back further and further. But it always just finds value 1". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [NKS] p. 129: "There is some subtlety here because in the abstract nothing guarantees that n – f[n – 1] will necessarily be a positive number. And if it is not, then results obtained by applying the rule can involve meaningless quantities such as f[0], f[–1] and f[–2]." p. 131: "For the vast majority of rules written down at random, such problems do indeed occur. But it is possible to find rules in which they do not". p. 130 caption: "All the rules shown start with f[1]=f[2]=1." — [NKS p. 129](https://www.wolframscience.com/nks/p129--recursive-sequences/); [p. 131](https://www.wolframscience.com/nks/p131--recursive-sequences/); [p. 130](https://www.wolframscience.com/nks/p130--recursive-sequences/)
- [NKS] Meaningfulness depends on evaluation strategy: "The question of which recursive definitions yield meaningful sequences can depend on the details of how the rules are applied. For example, f[-1] may occur, but if the complete expression is f[-1] - f[-1], then the actual value of f[-1] is irrelevant. The default form of evaluation … is the so-called leftmost innermost scheme … and will therefore never notice if f[k] in fact occurs only in the combination f[k] - f[k]." — [NKS note "Computation of [recursive] sequences"](https://www.wolframscience.com/nks/notes-4-3--computation-of-recursive-sequences/)
- [E-img] The F4 family definition is `f[n_] := f[n - f[n - a]] + f[n - f[n - b]]`, so F412 is the Q recurrence. Plots of F412, F423, F424 and F416 are shown. The text says only "the typical behavior here does not seem much different from what we already saw with one-term definitions involving only two f's", and "(Note that F4aa is equivalent to S2a [sic]. Cases like F413 lead after a transient to pure exponential growth.)" The initial condition for the F4 plots is not restated. — [essay, "More Complicated Rules"](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#more-complicated-rules); [definition](https://content.wolfram.com/sites/43/2024/09/sw09232024rulesimg11.png); [plots](https://content.wolfram.com/sites/43/2024/09/sw09232024rulesimg13.png)
- [O] Ed Pegg confirms the identification. Wolfram "came up with a code for them. The one he calls F412 is the Hofstadter's Q-Sequence." Pegg's implementation also pads: `g[n_?NumericQ] := g[n] = If[n < 3, 1, g[n - g[n - 1]] + g[n - g[n - 2]]]`. — [Wolfram Community, 2025-09-24](https://community.wolfram.com/t/the-continuous-case-of-the-hofstadters-q-sequence/26003)
- [WM] Wolfram's own working notes:
  - 2021: "Is it obvious that there will always be termination [yes, because there is an 'absorbing boundary at n < 1']".
  - 2024 notebook 04, "General Questions": "If f[n] always less than n? Or at least asymptotically." It also has a "Different init … This is a failure to halt....." remark.
  - 2024 notebook 06: "[ When does the function exist ? ]" for parameters {1,1,2}.
  - — [Evaluation-01 (2021)](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2021/Evaluation-01.nb); [NestedlyRecursive-04 (2024)](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-04.nb); [NestedlyRecursive-06](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-06.nb)
- [O] Brad Klee's follow-up, "Ground Principles":
  - "In the exploration of nestedly recursive functions, the principal difficulty is unbounded evaluation ultimately leading to TerminatedEvaluation."
  - "More in general, we expect a successful result when s(n) is bounded above by n and bounded below by a set of initial values. The question posed by nestedly recursive functions is this one: What happens if we allow s(n) to depend on a value from the range of f?"
  - "if we choose f(n) to ensure s(n) < n, we still need to concern ourselves how the function will terminate around the origin."
  - — [Klee, "Finding missing gems amidst chaos", 2024-10-03](https://community.wolfram.com/t/finding-missing-gems-amidst-chaos/24627)

### Inferences
- **Identification (checked by computation and by a shift argument).** Under f[n] = 1 for n ≤ 0, F412 satisfies f[n] = Q(n+2), with Q in OEIS indexing, wherever Hofstadter's Q is defined.
  - The argument: g(m) := f[m−2] satisfies g(m) = g(m − g(m−1)) + g(m − g(m−2)) with g ≡ 1 for m ≤ 2.
  - On 2026-10-10 I ran a Python check for 1 ≤ n ≤ 10^6. Both agree, and F412's outer lookback never went below f[0].
  - Consequence: Hofstadter's Q is total ⟺ F412 (padded) never makes an outer lookback below f[−1] ⟺ its "blue graph trees" are rooted only at the two seeds f[−1], f[0] ⟺ ∀n, Q(n) ≤ n (as in `00_session_findings.md`).
- **The essay's lookback analysis fits Q exactly but is not applied to it.** The essay applies its "lookback" / "how many initial conditions are sampled" analysis to P312, T212, F3ab and the S family, but never to F412. Its padding hides exactly the property at stake.
- **Dying under Hofstadter seeds.** "Pure exponential growth" cases like F413 must read padded values arbitrarily far back, so with Hofstadter-style seeds they would die. The essay does not draw this link.
- **Lean: padding choice.** The session's padded Lean definition (`max 1` clamp, q 0 = 0) is a different total extension from Wolfram's (value 1 at all non-positive indices, plus the index shift of 2). Both coincide with Q while Q is alive and can differ after a hypothetical death. Equivalence lemmas must therefore be stated per padding (see §9).
- **Lean: evaluation strategy.** Lean's strict evaluation of `+` matches Wolfram's "leftmost innermost" default. Q has no f[k] − f[k] cancellations, so the evaluation-strategy subtlety in the NKS note does not change Q's "definedness". It does matter if one generalizes the formalization to arbitrary nested recurrences.

### Gaps
- The essay does not state the initial condition used for the F4 plots. I am assuming the standard one; it is consistent with Pegg's reading.
- The essay gives no statistics on how many enumerated rules die. NKS gives only the qualitative "vast majority".
- The essay does not discuss Q under the original convention anywhere in its technical sections.

---

## 5. Classification, naming scheme and reported behaviours, and what is said about Q itself

### Takeaway
The essay has three main one-term families: P ("plus-like", Pabc), T ("times-like", Tabc) and S ("subtract-like", Sab). Its table gives asymptotics ~√n, ~n^α "(?)" and ~αn, with "finite / infinite / finite" initial conditions sampled. It adds multi-term and deeper families (F3ab, F4ab ∋ Q, G3abc ∋ Conway, S31, depth-d nestings) and a continuous analogue.

Reported behaviours range from exact formulas and nesting (P111, P123, S1 = Hofstadter's G, G3111) through long transients resolving into regularity (P312) to persistent apparent randomness (T212, T311, S1 with f = 1 for n ≤ 3, F4 cases).

On Q specifically the essay offers only history, qualitative labels and four F412 plots. It does not discuss Q's growth rate, generations, value set or existence.

### Cited Findings
- [E-img] The families table, verbatim:

  | | designation | recursion | asymptotics | initial condition |
  |---|---|---|---|---|
  | Plus-like | Pabc | a + f[n − b f[n − c]] | ~ √n | finite |
  | Times-like | Tabc | a f[n − b f[n − c]] | ~ n^α (?) | infinite |
  | Subtract-like | Sab | n − f[f[n − a] − b] | ~ α n | finite |

  — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#the-basic-idea); [table image](https://content.wolfram.com/sites/43/2024/09/sw09192024basicimg11.png)
- [WM] An earlier naming in the 2024 working notes reads "T311 Tabc a f[n - b f[n-c]] (exponential) | P311 Pabc a + f[n - b f[n-c]] (sqrt growth) | … | Mab n - f[f[n-a] - b] (linear growth)". The S family was first called "M". — [NestedlyRecursive-07](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-07.nb)
- [E] **P family.** — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#a-closer-look-at-p312--fn--3--fn---fn---2)
  - **P312** (`3 + f[n − f[n − 2]]`) is "the first 'seriously complex' example". It "seems to 'resolve itself'".
    - "the f[–3] and f[–2] trees stop contributing to f[n] when n is (respectively) 537 and 296, and these trees are finite (and have sizes 53 and 15)".
    - It has a messy but recursion-free "direct formula" with "6 separate riffled ('mod') subsequences". "For n = 1000 we're not yet in the 'simple' regime".
    - Growth f[n] ≈ √(6n).
    - "the only values needed are f[–3], f[–2], f[–1] and f[0]", supported by a plot of f[n−2] vs n: "only for very few values of n does f[n – 2] exceed n—and it's these values that probe back".
    - With f[0] = z, "the lookback goes to –z for z ≥ 3, and to z – 4 for 1 ≤ z ≤ 2". "for any specified initial configuration of values, there is always only bounded lookback—with the bound apparently being determined by the largest of the initial values".
    - The number of "surviving trees" varies "quite erratically" with f[0]. With f[n] = s for n ≤ 0 and s ≥ 2 the behaviour is simple.
    - Residues mod 3 are preserved; "apart from this constraint, it seems that all values for f[n] are obtained".
  - **P111** has blocks of length k with value k, and `f[n] = Floor[1/2 + Sqrt[2 n + 1]]`.
  - **P123** has plateau lengths given exactly by a substitution system (nested).
  - **P213** shows a transient until n = 68, then a √-pattern.
- [E] **T family.** — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#the-t-family)
  - "T1xx cases … are always trivial".
  - **T212** is the "first 'complicated case'":
    - Unbounded lookback ("unlike for the P family—the number of lookbacks isn't limited … to compute T212 for progressively larger n, progressively more information about its initial conditions is needed").
    - Values are powers of 2. The average of log₂ f fits 0.38 Log[n], so "f[n] asymptotically approximates n^0.26".
    - "fluctuates very intensely". Values are "very close to exponentially distributed".
    - "eventually it seems as if all length-b blocks for any given b will appear".
  - Contrast with ordinary recurrences: "When one deals with ordinary, unnested recurrence relations, one's always dealing with a fixed lookback … But for the nested recurrence relation T212 … there can be an unboundedly large lookback."
  - **T311**, the "Summer School" sequence: lookbacks grow ~0.44 n. "T212 seems to have already 'filled out the computational possibilities', so T311 'doesn't have anything to add'."
- [E] **S family.** — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#the-s-family-fn--n--ffn--a--b)
  - **S10 ("S1")**, i.e. n − f[f[n − 1]], with f[n] = 1 for n ≤ 1: "f[n] is given exactly by" `Floor[(n + 1)/GoldenRatio]` (Hofstadter's G).
    - Its single tree is "a very simple 'Fibonacci tree' form (which … has been known since the 1970s)".
    - Slope 1/ϕ, from substituting f[n] = σ n: "For large n all that survives is the condition for the coefficients of n".
  - With f[n] = 1 for n ≤ 3: "considerably more complicated". There is "bursting" behaviour; "regions of calm" grow by a factor ϕ; an audio rendering is provided.
  - "In all cases, only a limited number of initial conditions are sampled (bounded by the value of a + b in the original definition)."
  - [O] The WSRP26 project states explicitly: "S10 (S1), which is also known as the Hofstadter G-Sequence". — [Gracelyn Chen, 2026-07-09](https://community.wolfram.com/t/wsrp26-analyzing-properties-and-behaviors-of-s-family-nestedly-recursive-functions/27232)
- [E] **"More complicated rules".** "The Principle of Computational Equivalence … suggests that it'll be 'more of the same': that once one's passed a fairly low threshold the computational sophistication—and complexity—of behavior will no longer change." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#more-complicated-rules)
  - **F3ab**, `f[n − f[n − a]] + f[n − b]`: "F312 has unbounded lookback (at least starting with f[n] = 1 for n ≤ 0), but for larger b, F31b has bounded lookback".
  - **F4ab**, `f[n − f[n − a]] + f[n − f[n − b]]`, which contains Q as F412. See §4.
  - **G3abc**, `f[n − a f[n − b]] + f[f[n − c]]`. G3111 (Conway's sequence) with f[1] = f[2] = 1 has f[n] − n/2 with "a nested structure that is closely related to the result of concatenating binary digit sequences of successive integers". Its "evaluation graph … is not particularly simple".
  - **S31**, `n − f[f[f[n − 1]]]` (Hofstadter's H form), with f = 1 for n ≤ 3: slope ≈ 0.682 from x = 1 − x³. At depth d the slope solves x = 1 − x^d, and "in all cases the only initial conditions probed are f[1] = 1 and f[3] = 1".
  - Deeper "n − f[n − f[f[…]]]" nestings have slopes like 1/ϕ and ≈ 0.544.
  - Other directions are listed but not discussed: Mod/Floor primitives, multiple functions, multiple arguments.
- [E] **Continuous case.** Real-argument analogues ("Fibonacci delay equation"). S1's plateaus fall at Wythoff numbers. For T212 with f[x] = Abs[x − 1] for x ≤ 0 there are "regions of noise" and "presumably in the limit x → ∞ … the analog of an essential singularity". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#an-aside-the-continuous-case)
- [E][E-img] **Everything said about Q itself:**
  - "absolutely CRAZY" (letter);
  - "chaos produced in a very orderly manner" (GEB scan);
  - "values have several properties of randomness" (SMP 1981);
  - "the first published large-scale picture of the Q sequence only appeared in 1998";
  - the "rule 30 phenomenon" retrospective;
  - the F412 plots.

  Checked: the prose has no statement about Q's growth rate, value set, "generations", or whether it is known to be total. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/)
- [NKS] What NKS says about Q (rule (e)):
  - p. 131 on rules (c)–(h): "There is a steady overall increase, but superimposed on this increase are fluctuations". "In cases (c) and (d), these fluctuations turn out to have a very regular nested form. But in the other cases, the fluctuations seem instead in many respects random."
  - The "Properties" note: "The total lengths of these chains (corresponding to the depth of the evaluation tree) seem to increase roughly like Log[n] for all the rules on this page."
  - — [NKS p. 131](https://www.wolframscience.com/nks/p131--recursive-sequences/); [NKS note](https://www.wolframscience.com/nks/notes-4-3--properties-of-recursive-sequences/)

### Inferences
- **Slope heuristic for F412.** The essay's slope heuristic (substitute f[n] = σn and match coefficients) applied to F412 gives σ = 2σ(1 − σ), hence σ = 1/2, matching Q(n) ≈ n/2. The essay does not do this computation.
- **Where Q sits in the classification.** Q is a two-term ("Fibonacci-style") member of F4. In the essay's PCE framing such rules are "more of the same" as T212 and P312, so Q receives no special treatment.
- **A classification fact relevant to Lean.** The P and S families sample a bounded set of initial conditions. T212 and F312 sample an unbounded set. Q's totality is exactly the claim that F412 is in the "bounded, and in fact ≤ 2 seeds" class.

### Gaps
- The essay gives no quantitative data on F4/Q: lookback counts, tree counts, or growth fits.

---

## 6. Provability, irreducibility, undecidability, automated proof, and explicitly open questions

### Takeaway
The essay contains no proofs and no theorem-proving, formal-verification or AI content. It never says Q's totality is open or unknown.

What it offers on provability:
- **Primitive recursion.** Padded nested recursions are primitive recursive ("finding values f[n] is primitive recursive"). NKS's earlier version is conditional: "if they never sample values below f[0]".
- **Irreducibility.** This is why "it's pretty difficult to say much about them in traditional mathematical ways".
- **Universality.** A Principle-of-Computational-Equivalence conjecture that "naturally occurring cases" like P312 or T212 are computation-universal.
- **Insidious inconsistencies.** These could make f non-total.

The February 2025 bibliography revision added Celaya–Ruskey's undecidability paper. A 2025 Summer School project built a nested recursion that simulates 2-tag systems.

### Cited Findings
- [E] "On the face of it, our nestedly recursive functions seem like they must be primitive recursive, since they don't for example appear to be 'searching for anything'. But things like the presence of longer and longer lookbacks raise questions." — [essay, "Primitive Recursive or Not?"](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [E] "So our nestedly recursive functions as we're using them are indeed primitive recursive. Or, more strictly, finding values f[n] is primitive recursive. Asking questions like 'For what n does f[n] reach 1000?' might not be primitive recursive. (The obvious way of answering them involves a FoldWhile-style non-primitive-recursive search, but proving that there's no primitive recursive way to answer the question is likely very much harder.)"
  - Supporting construction: Fold plus an Association, a tupling function to pack lists into one integer, and `If[n ≤ 0, 1, f[n]]` written in primitive-recursive form as `r[c[s, z], c[f, c[s, p[2]]]][n]`.
  - Caveat: "We've simply assumed f[n] = 1 for n ≤ 0. But what if there was something more complicated there? Even if f[–m] was given by some primitive recursive function … one could end up somehow 'bouncing back and forth' between positive and negative arguments … and in doing that searching one could find oneself outside the domain of primitive recursive functions."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [NKS] "it turns out that if they never sample values below f[0] the functions in the main text are also all primitive recursive. (Their definitions have a primitive recursive structure, but to operate correctly they must be given integers that are non-negative.)" Also: "(Ordinary primitive recursive functions are always total functions … But general recursive functions can be partial functions, that do not terminate for some inputs.)" — [NKS note "Primitive recursive functions"](https://www.wolframscience.com/nks/notes-4-3--primitive-recursive-functions/)
- [E] "while for primitive recursive functions it's always possible to compute a value f[n] for any n, that's not necessarily true for general recursive functions … in evaluating primitive recursive functions, the computations always halt, while for general recursive functions, they may not." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [E] **Universality conjecture.**
  - There are two ways to "program" a nested recursion: pack rule, data and step number into n via tupling; or feed "a 'program' through the initial conditions … to emulate a nestedly recursive function with any other recursive definition (or, say, for a start, any linear recurrence)."
  - "Perhaps one could construct a complicated nestedly recursive function that would have this property. But what the Principle of Computational Equivalence suggests is that it should be possible to find the property even in 'naturally occurring cases'—like P312 or T212."
  - The analogy: "rule 110 … or the s = 2, k = 3 596440 Turing machine … later, with great effort, it became possible to actually prove computation universality."
  - "It's not clear how to harness this diversity to extract some form of universality. But it seems likely that the 'raw material' is there."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [E] **Reducibility example.** P312: "at the cost of 'messiness' we've—somewhat surprisingly—been able to unravel all the recursion in P312 to arrive at a 'direct formula'". [O] Klee: "candidate P312 turned out to be a red herring in its ultimate reducibility." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#a-closer-look-at-p312--fn--3--fn---fn---2); [Klee 2024](https://community.wolfram.com/t/finding-missing-gems-amidst-chaos/24627)
- [E] **Explicit open items, quoted.**
  - Closing paragraph: "(Needless to say, there are many, many additional questions and issues to explore. Different primitives, e.g. Mod, Floor, etc. Multiple functions that refer to each other. Multiway cases. Functions based on rational numbers. And endless potential approaches to analysis, identifying pockets of regularity and computational reducibility.)"
  - The 2003 notes are introduced with "(some of which should still be explored!)". [E-img] They list:
    - "Other things one might have looked at: Simultaneous recursion relations; Multiple argument functions; Rational numbers; Other constructor functions (e.g. Floor etc.)".
    - "Things that are related: 3n+1 problem iteration system; Primitive recursive functions; FIR/IIR filters; Wavelet recursion relations; Fibonacci sequences; Ackermann functions; Double recursion".
    - "Why is this interesting? … Perhaps a simple model for pointer-based encoding".
  - The 2003 write-up draft (on polynomial definitions): "We haven't found anything interesting. … Can we prove that nothing 'interesting' can happen?". On nested ones: "often the functions have to use an infinite set of initial values. Sometimes they make do with a finite set. For the cases that look simpler, there are formulas for what happens."
  - The table's "~ n^α (?)" for the T family.
  - The hedged "apparently" for P312's lookback bound.
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#my-personal-story-with-nestedly-recursive-functions); [2003 notes](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg22.png); [2003 draft](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg23.png)
- [E] Checked absences in the prose: "undecid…" 0 times; "theorem" only in "proving theorems about programs" (McCarthy history); "conjecture" 0; "not known" or "unknown" 0; "open" only as "out in the open". There is no mention of automated theorem proving, FindEquationalProof, formal verification or LLMs. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/)
- [E-bib] **Bibliography revision of 2025-02-18.** Diffing the two PDFs, the only substantive change is the addition of "M. Celaya and F. Ruskey (2012), 'An Undecidable Nested Recurrence Relation', CiE 2012, LNCS 7318, 107–117 [arXiv:1203.0586]". The other differences are reorderings. — [2024 version](https://content.wolfram.com/sites/43/2024/09/NestedlyRecursiveFunctions-Bibliography-9-27.pdf); [2025 version](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)
- [WM] Wolfram's 2024 working notes have proof-oriented to-dos and questions:
  - On P312 (`f[n_]:=3 + f[n-f[n-2]]`): "Get a proof that this only gets to f[-3]", and "Brad's closed form".
  - On `3 + f[n-f[n-1]]`: "Explain why it's (apparently) sampling down to -a".
  - "A machine with one stack isn't universal, but two are".
  - "[[ If function is below f[n] ≤ n then there must be bounded lookback; for S family ]] Lookback is bounded by a primitive recursive function of n …"
  - "Does there exist a value of n for which f[n] is ____ : not PR".
  - "Universality: Can we set up values for f[n] with n < 1 so that f[m] with m > XXX corresponds to any possible function?"
  - "Pre-Universality: Set up initial conditions so that the sequence generated follows any specified linear recurrence".
  - — [NestedlyRecursive-05](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-05.nb); [-09 "Deeper Nesting"](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-09.nb); [-04](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-04.nb); [-07](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-07.nb)
- [O] **WSS25, Bowei Xv**, "Computability on Nestedly Recursive Function (NRF)", 2025-07-10.
  - The project "studies a specific Nestedly Recursive Function which could simulate 2-tag system, that is Turing complete. This shows NRF is indeed capable of universal computation, and sheds light into a deeper question: 'what is the simplest universal nested recursive function?'"
  - It quotes Celaya–Ruskey's definition: "calculable means that for every n ≥ 0, either A(n) is an initial condition or the calculation of A(n) involves only invocations of A on arguments in {0, 1, …, n − 1}".
  - It concludes that the question "must be undecidable" for its NRF, noting "it uses a exponential number of initial conditions".
  - It cites Wolfram 2024 and Celaya–Ruskey. The mentors' names in the extracted page text ended "…ietro Pepe, Stephen Wolfram"; I take the first to be Pietro Pepe.
  - — [Wolfram Community](https://community.wolfram.com/t/wss25-computability-on-nestedly-recursive-function-nrf/25684)

### Inferences
- **What kind of statement Q's totality is.** It is a single Π⁰₁ sentence (∀n, Q(n) ≤ n, each instance decidable by finite computation).
  - The undecidability results the essay's orbit points to (Celaya–Ruskey; WSS25) concern *families* of recurrences with engineered initial conditions. They imply nothing about Q's instance, beyond explaining why no uniform decision method for totality exists.
  - A refutation would be a finite certificate (the first n with Q(n−1) ≥ n). A proof needs an invariant.
- **What Wolfram's framing implies.** It (irreducibility, PCE) predicts no simple formula for Q, but it is not an argument that totality is unprovable. The essay does not claim that.
- **Primitive recursion in Lean terms.** NKS's conditional primitive-recursion statement is the cleanest statement of the formal situation.
  - The padded function is primitive recursive (course-of-values recursion, since padded values are ≥ 1).
  - Hofstadter's partial Q equals it on its domain, and that domain is everything iff Q never samples below its seeds.
  - In Lean: the padded version is an easy well-founded definition (as in the session's `QDefinition.lean`). Hofstadter's Q as a *function* needs either the totality theorem or a partial/relational encoding.
- **A tractable analogue of Q's totality.** P312's "only gets to f[−3]" is structurally the same kind of statement: bounded lookback into the seed region. Wolfram flagged it as needing a proof. Unlike Q, it has an explicit eventual "direct formula" (mod-6 blocks), so it is a plausible warm-up target for the Lean project. Pinning down where the regular regime starts is part of the work.

### Gaps
- I did not open Celaya–Ruskey here (covered in `q_sequence_mathematics.md`), nor the WSS25 notebook's construction details beyond its abstract and conclusion.
- No source states whether anyone proved P312's bounded lookback after the 2024 working note.

---

## 7. Methodology and reusable material (experiments, visualizations, Wolfram Language code, candidate theorems)

### Takeaway
The essay's methodology is ruliological: enumerate rule families, plot sequences and residuals, build evaluation (call) graphs, extract "blue graph trees" rooted at initial conditions, measure lookback, fit growth heuristically, look for substitution-system and digit structure, and vary initial conditions.

The code shown is reusable:
- memoized definitions;
- conditional base cases;
- `If`;
- Fold + Lookup with a default of 1;
- Sow/Reap sampling;
- the companion Function Repository `RecursiveFunction` (16 Sep 2024).

For Lean, the essay supplies a ladder of statements from easy to hard (see Inferences).

### Cited Findings
- [E][E-img] **Memoization.** "In the Wolfram Language, it's a very simple change to our original definition": `f[1] = f[2] = 1; f[n_] := f[n] = f[n – 1] + f[n – 2]`. "it's this kind of minimal evaluation graph that we've been using in everything we've discussed so far." [NKS] gives `f[n_] := f[n] = f[n - f[n - 1]] + f[n - f[n - 2]]`, i.e. Q itself, as the example: "it is essential to store all the values of f[n] that one has already computed". — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#how-do-you-actually-compute-recursive-functions); [NKS note](https://www.wolframscience.com/nks/notes-4-3--computation-of-recursive-sequences/)
- [E] **Evaluation graphs.**
  - "an 'evaluation graph' in which we show how each value of f[n] is computed from ones with smaller values of n". The two edge colours mark "the two different computations" (outer and inner f).
  - The "red" graph splits into path graphs; the "blue" graph into trees rooted at initial conditions.
  - Unrolled (tree) vs minimal (cached) graphs: "the maximum possible number of nodes in the unrolled graph will be 2^n" (Fibonacci ≈ 1.6^n; T212 ≈ 1.2^n unrolled vs ≈ 0.5n minimal).
  - Evaluation order is "leftmost innermost … In effect, we're traversing the graph in a depth-first way".
  - "With a pure stack machine, the unrolled graph is the only one possible. But if we allow (random-access) memory, then the minimal graph becomes possible."
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#how-do-you-actually-compute-recursive-functions)
- [E-img] **Primitive-recursive Fold form** (T311): `Fold[{f, n} ↦ Append[f, n → 3 Lookup[f, n – Lookup[f, n – 1, 1], 1]], Association[], Range[n]][n]`. — [image](https://content.wolfram.com/sites/43/2024/09/sw09252024primitiveimg23.png)
- [E] **Growth heuristics.** "Assume that for large n we can take f[n] = σ n. Then substitute this form into both sides … For large n all that survives is the condition for the coefficients of n". Examples: S family σ = 1/ϕ; S31 x = 1 − x³; P312 ≈ √(6n); P111 ≈ √(2n); T212 ≈ n^0.26 from a log-average fit. — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#the-s-family-fn--n--ffn--a--b)
- [E] Other instruments:
  - "lookback" plots, with roots of blue trees highlighted;
  - layer-size counts of trees;
  - residual plots (f − n/ϕ, f − n/2);
  - first-occurrence plots of length-b blocks (T212);
  - an "audio rendering" of S1 bursts;
  - continuous-argument analogues;
  - a video link at the top of the page.
  - — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/); [audio](https://www.wolframcloud.com/obj/sw-writings0/NestedlyRecursive/RecursiveAudio); [video](https://www.youtube.com/watch?v=xXEMs3lCy-g&t=468s)
- [E-img] **1993 and 2003 enumeration code.**
  - 1993: `Select[allrecs, (Length[RecurrenceTable[#]] == 10)&]`. Its `RecurrenceTable[rhs, n]` has a different signature from the built-in and was presumably a personal helper (my inference).
  - 2003: `RSValues`/`RSValuesSampled`, the latter using `Sow[n]`/`Reap` to log sampled arguments.
  - [WM] 2024: enumeration via `Groupings[...]` over f, Plus and negation, filtered with `Enclose`/`Confirm` to drop failing rules; parametrized schema code (`$PlusTimesShift`, `$TwoTerms` with "GrowTest" -> n > d, "Root" -> 1).
  - — [2003 code](https://content.wolfram.com/sites/43/2024/09/sw09252024personalboxc2cimg1.png); [NestedlyRecursive-08](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-08.nb); [NestedlyRecursive-05](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-05.nb)
- [O] **`ResourceFunction["RecursiveFunction"]`** (v1.0.0, 16 September 2024; Bradley Klee and Thomas Adler; Adler wrote the first "Stack" method at Summer School 2024).
  - "Obtain function values for an arbitrary recursive function".
  - Forms: `[fun, inits, n]`, `[fun, inits, {n1, n2, …}]` and an operator form. Method "Stack" (default; "never experiences difficulties with $RecursionLimit") or "SelfReferential".
  - It handles nestedly recursive functions "where RecurrenceTable fails".
  - Domain rule: it assumes f[n] does not depend on any f[m] with 0 < n < m, and "If and when this condition becomes invalid, a Failure object is thrown". The page calls this a "pragmatic feature".
  - A companion resource is `RecursiveFunctionCallGraph`.
  - [WM] shows usage like `RecursiveFunction[f[n] -> f[n - f[-1 + n]] + f[f[-1 + n]], {} -> {}, {n <= 2 -> 1}]`, and a thrown `Failure[Bound, Now -1, Next -2]` when evaluation would move from f[−1] to f[−2].
  - — [Function Repository](https://resources.wolframcloud.com/FunctionRepository/resources/RecursiveFunction/) (via WebFetch summary); [NestedlyRecursive-07](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-07.nb)
- [E-bib] **Demonstrations.** "Call Graphs of Nestedly Recursive Functions" (2007), "Multiterm Nestedly Recursive Functions" (2007), "One-Term Nestedly Recursive Functions" (2008). — [bibliography](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)

### Inferences

**Candidate Lean statements suggested by the essay, roughly ordered by expected difficulty.** Difficulty estimates are mine.
1. *Padding agreement.* Under f[n] = 1 for n ≤ 0, F412 gives f(n) = Q(n+2) wherever Q is defined. Also: Q total ⟺ the padded F412 never makes an outer lookback below −1 ⟺ ∀n, Q(n) ≤ n. Easy to moderate, and it removes the "trivial totality" confusion explicitly.
2. *T212 values are powers of 2* (given power-of-2 padding). Trivial induction.
3. *P111 closed form*, `Floor[1/2 + Sqrt[2n+1]]`. Easy to moderate; needs integer square-root lemmas.
4. *S1 = Hofstadter's G = `Floor[(n+1)/GoldenRatio]`*. Moderate. Prior formal work on G-like functions exists in Coq/Rocq (Letouzey; see `q_sequence_mathematics.md`).
5. *S-family bounded sampling* ("bounded by a + b") and *depth-d S nestings probe only f[1], f[3]*. These are lookback-boundedness statements of the same logical shape as Q's totality, but in self-limiting families. Moderate.
6. *P312 bounded lookback* (only f[−3..0]). Wolfram's working notes record "Get a proof that this only gets to f[-3]". A plausible route is a finite check through the transient (the essay says n = 2000 is already in the regular regime), then an induction on the explicit mod-6 block formula. Nontrivial but plausible; arguably the best "Q-shaped" warm-up the essay offers.
7. *Conway's G3111 totality*. Trivial (`00_session_findings.md`); Mallows' theorem is the hard part.
8. *Unbounded lookback* for F312 or T212. A ∀∃ statement. Likely hard in general; for specific n it is just evaluation.
9. *Q totality* itself. Open.

Tooling note: `RecursiveFunction`/`RecursiveFunctionCallGraph` (via the Wolfram MCP) can generate ground-truth tables and lookback data to cross-check Lean `#eval` and `decide` outputs. Its Failure-on-forward-dependency behaviour is a *different* partiality notion from Hofstadter's (looking below index 1). Check carefully before using it as an oracle for "death".

### Gaps
- I did not run `RecursiveFunction` myself; its exact behaviour when Q-style rules look below 1 with no padding is unverified.
- The essay's per-figure code is not linked from the page. Checked: no "click for code" links or notebook links except the audio object.

---

## 8. Follow-ups, 2024–2026 (Wolfram, the Wolfram Institute, Summer programs, and citations)

### Takeaway
Follow-ups are tooling, student projects and community posts, not research on Q's totality.
- `RecursiveFunction` (Sep 2024).
- Brad Klee's "missing gems" post (Oct 2024).
- A bibliography revision adding Celaya–Ruskey (Feb 2025).
- WSS25 Bowei Xv, universality and undecidability via 2-tag systems (Jul 2025).
- Ed Pegg, "The continuous case of the Hofstadter's Q-Sequence" (Sep 2025), which names F412 = Q.
- WSRP26 Gracelyn Chen on the S family (Jul 2026).

Wolfram's own 2025–2026 essays and the Wolfram Institute have nothing new on nested recursion. None of the 2023–2026 Q papers I checked cites the essay.

### Cited Findings
- [O] **Wolfram Institute.** It republished the essay at /output/nestedly-recursive-functions. As fetched on 2026-10-10, its "Nestedly Recursive Functions" tag page lists only that item (2024-09-27). Its "Recursion" tag page lists the essay and a 2023-09-09 item; the earlier notes identified that as "Expression Evaluation and Fundamental Physics". — [Institute copy](https://wolframinstitute.org/output/nestedly-recursive-functions); [tag page](https://wolframinstitute.org/output/tag/Nestedly+Recursive+Functions); [Recursion tag](https://wolframinstitute.org/output/tag/Recursion)
- [O] **Wolfram's later essays.** The essay page's "Related Writings" box (as of 2026-10-10) lists:
  - "What's the Future for Pure Math Research in the Age of AI?" (2026-09-28);
  - "Towards a Theory of Bugs" (2026-07-21);
  - "Games between Programs" (2026-06-04);
  - "P vs. NP and the Difficulty of Computation: A Ruliological Approach" (2026-01-30).

  Checked: none of the four contains "nestedly recursive", "nested recursi…", "Hofstadter", "Q sequence" or "McCarthy". — [AI & pure math essay](https://writings.stephenwolfram.com/2026/09/whats-the-future-for-pure-math-research-in-the-age-of-ai/); [P vs NP essay](https://writings.stephenwolfram.com/2026/01/p-vs-np-and-the-difficulty-of-computation-a-ruliological-approach/)
- [E-bib] **Bibliography revision of 2025-02-18.** It adds Celaya–Ruskey (2012). The essay's heading link points to the 2025 PDF, while the in-text link still points to the 2024-09-27 PDF. — [2025 PDF](https://content.wolfram.com/sites/43/2025/02/NestedlyRecursiveFunctions-Bibliography-02-18-2025.pdf)
- [O] **Function Repository.** `RecursiveFunction` v1.0.0, 2024-09-16 (Klee and Adler); related links cite the essay and NKS pp. 129–130. — [resource](https://resources.wolframcloud.com/FunctionRepository/resources/RecursiveFunction/)
- [O] **Brad Klee, "Finding missing gems amidst chaos"** (Wolfram Community, 2024-10-03). It starts from the essay, calls P312 "a red herring in its ultimate reducibility", and explores a G-related family. It poses the "missing gems conjecture": "We've just now observed that the missing gems … exist for millions of terms and have only conjectured that they will persist to infinity. Can anyone prove the missing gems conjecture?" — [post](https://community.wolfram.com/t/finding-missing-gems-amidst-chaos/24627)
- [O] **WSS24, Thomas Adler**, "Exploring call graphs of nestedly recursive functions" (2024-07-10, before the essay). It says: "Nestedly recursive functions are recursive functions that call themselves multiple times, in a nested fashion. This was termed by Stephen Wolfram, and an example is Hofstadter's Q-Sequence". It built the stack-based evaluator later published with Klee, and explores digit-based "shift operators". It notes that its implementations "will either hit recursion depth limits … or just run forever … if a functional form with unbounded growth is inputted." This confirms and adds to the earlier note's secondhand alumni-page snippet. — [post](https://community.wolfram.com/t/wss24-exploring-call-graphs-of-nestedly-recursive-functions/24234)
- [O] **WSS25, Bowei Xv**, "Computability on Nestedly Recursive Function (NRF)" (2025-07-10). See §6. — [post](https://community.wolfram.com/t/wss25-computability-on-nestedly-recursive-function-nrf/25684)
- [O] **Ed Pegg, "The continuous case of the Hofstadter's Q-Sequence."** (Wolfram Community, 2025-09-24).
  - "A year ago, Stephen Wolfram wrote about Nestedly Recursive Functions … The one he calls F412 is the Hofstadter's Q-Sequence."
  - He defines a real-argument Q, with g = 1 for n < 3, and a variant with f = n for n < 3 ("For the first 50000 integers, f[n] = g[n+1]"). He derives piecewise-linear forms up to ~55: "It gets much, much worse after 49 … I never managed to get 56".
  - "Sometimes, unsolved problems can be cracked by making them more complicated. Does the continuous function help with the Hofstadter's Q-Sequence?"
  - — [post](https://community.wolfram.com/t/the-continuous-case-of-the-hofstadters-q-sequence/26003)
- [O] **WSRP26, Gracelyn Chen**, "Analyzing properties and behaviors of S family nestedly recursive functions" (2026-07-09; mentor Daniel Sanchez). It denotes S_ab with f[n] = 1 for n ≤ c, notes that "using f[n] = 0 for n ≤ 1 leads to the circular definition f[1] = f[1]", and studies error plots and bursting. Its future work includes "connecting computed observations to the underlying definitions of the function". It cites the essay, `RecursiveFunction` and `RecursiveFunctionCallGraph`. — [post](https://community.wolfram.com/t/wsrp26-analyzing-properties-and-behaviors-of-s-family-nestedly-recursive-functions/27232)
- [O] **Earlier student work credited in the Thanks.** Chris Song, "[WSC21] Analysis of called values of nested recursive functions" (2021-07-15), on which negative arguments T-like rules call. [O, search summary only] Roberto Martinez's 2003 project describes these functions "as generalizations of Hofstadter's function" and classifies behaviour as uniform, repetitive, nested or chaotic. — [Song](https://community.wolfram.com/t/wsc21-analysis-of-called-values-of-nested-recursive-functions/18546); [Martinez alumni page](https://education.wolfram.com/summer-school/alumni/2003/martinez/)
- [O] **Citations of the essay in Q literature.** Checked by fetching arXiv HTML versions and searching for "Wolfram" and "nestedly". There are 0 hits in Mantovanelli 2603.29622, 2603.16111 and 2609.02412; Cloitre 2604.06237; Pinn 2603.17509; and Deane–Gentile 2311.13854 and 2509.17764. Mantovanelli 2603.29622 does cite Celaya–Ruskey. — [arXiv 2603.29622](https://arxiv.org/html/2603.29622)
- [O] Wikipedia's "Hofstadter sequence" page has no "Wolfram" mention. MathWorld's Q page does not link the essay. OEIS A005185 cites only "S. Wolfram, A New Kind of Science, Wolfram Media, 2002; p. 129" and still says "it is not even known if this sequence is defined for all positive n". — [Wikipedia](https://en.wikipedia.org/wiki/Hofstadter_sequence); [OEIS](https://oeis.org/A005185)

### Inferences
- **No follow-up on Q's totality.** Nothing in the Wolfram ecosystem addresses Q's totality under Hofstadter's convention. The closest items are:
  - (a) Pegg's continuous Q, which still pads;
  - (b) the WSS25 universality construction, which bears on undecidability for families, not Q;
  - (c) Klee's "ground principles" (s(n) < n plus a lower bound), which restate the totality condition in general form.
- **The essay's footprint in Q research is nil.** As of October 2026 the Q research community does not cite it. Its value for this project lies in conventions, vocabulary (lookback, evaluation graphs), history and tooling.

### Gaps
- Lean Zulip, X and Mathstodon were not searched here; `ai_labs_and_ai_for_math.md` §10 covers them.
- The WSRP25 post "On functional trees" (2025-07-22) appeared in a related-topics list. I did not check whether it concerns nested recursion.
- I did not read the full WSS25 notebook.

---

## 9. Which parts of the essay bear directly on Lean formalization choices

### Takeaway
Six parts of the essay matter for design:
- (1) its padding convention, and the fact that F412 is Q shifted by 2;
- (2) its "lookback / initial conditions sampled" vocabulary, which turns totality into a precise invariant;
- (3) its primitive-recursion discussion, together with NKS's conditional statement;
- (4) the NKS note that "meaningfulness" depends on evaluation strategy;
- (5) the non-progress and inconsistency examples, which mark where a relational spec differs from a functional one;
- (6) a menu of easier lookback-boundedness theorems (P312, S family), with P312's proof explicitly flagged by Wolfram as a to-do.

The essay offers no proof strategy for Q.

### Cited Findings
- [E] The convention and its effect: "Lookup to give 1 if the value it's trying to look up hasn't been filled in yet, implementing the fact that f[n] = 1 for n ≤ 0 … it always just finds value 1." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [E-img] The F4 family definition makes F412 the Q recurrence. [O] Pegg: "The one he calls F412 is the Hofstadter's Q-Sequence." — [definition](https://content.wolfram.com/sites/43/2024/09/sw09232024rulesimg11.png); [Pegg](https://community.wolfram.com/t/the-continuous-case-of-the-hofstadters-q-sequence/26003)
- [E] Lookback vocabulary: "If one just looks at the form of the recursive definition for P312 it's far from obvious 'how far back' it will need to probe, or, in other words, what values of f[n] one will need to specify as initial conditions." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#a-closer-look-at-p312--fn--3--fn---fn---2)
- [NKS] "if they never sample values below f[0] the functions in the main text are also all primitive recursive". — [NKS note](https://www.wolframscience.com/nks/notes-4-3--primitive-recursive-functions/)
- [NKS] "The question of which recursive definitions yield meaningful sequences can depend on the details of how the rules are applied." — [NKS note](https://www.wolframscience.com/nks/notes-4-3--computation-of-recursive-sequences/)
- [E] "things like this could be reasons that f[n] might not be a 'total function', defined for all n." — [essay](https://writings.stephenwolfram.com/2024/09/nestedly-recursive-functions/#primitive-recursive-or-not)
- [E-img] Historical encodings of Q's domain: SMP `Hof[$n_=Natp[$n]]` (1981) and Mathematica `Hofstadter[n_Integer?Positive]` (1987/88), both partial. — [SMP](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg1.png); [Mathematica book](https://content.wolfram.com/sites/43/2024/09/sw09242024personalimg7.png)
- [WM] "Get a proof that this only gets to f[-3]" (P312); "If f[n] always less than n?" — [NestedlyRecursive-05](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-05.nb); [NestedlyRecursive-04](https://www.wolframcloud.com/obj/wolframphysics/WorkingMaterial/2024/NestedlyRecursive-04.nb)
- [E-img] The Erdős–Graham phrasing ("Does f(n) miss infinitely many integers?") presupposes existence. — [scan](https://content.wolfram.com/sites/43/2024/09/sw09242024historyimg16.png)

### Inferences

**Design recommendations.** These are mine, derived from the above.

**1. Make the semantics explicit, with three named objects:**
- (a) Hofstadter's partial Q: a relational spec like the session's `IsQ`, or Option/fuel-valued.
- (b) Wolfram's total padded Q_W : ℤ → ℕ, with value 1 at all n ≤ 0 and Q_W(n) = Q_W(n − Q_W(n−1)) + Q_W(n − Q_W(n−2)) for n ≥ 1. Note that Q_W(n) = Q(n+2), not Q(n).
- (c) The session's clamped padding `q` from `QDefinition.lean`.

Prove the agreement lemmas: (a) defined at n ⇒ (b) and (c) agree with it, after the index shift for (b).

**2. State totality as a lookback invariant.** Use `HofstadterQTotal ↔ ∀ n ≥ 1, outer lookbacks of Q_W stay ≥ −1 ↔ ∀ n, Q n ≤ n`. This connects the essay's vocabulary to the session's `Q(n) ≤ n` criterion and to formal-conjectures' `IsHofstadterQ` (which has the constraints f(n−1) < n and f(n−2) < n built in).

**3. Avoid the trivial-totality trap.** Any theorem proved about (b) or (c) alone (growth, value sets, Erdős #422-style statements) says nothing about Hofstadter's Q unless combined with totality. The essay's own results are all about padded objects.

**4. Use primitive recursion as the definitional template.** The padded function is primitive recursive, being course-of-values with index n − Q_W(n−1) < n because values are ≥ 1. In Lean, `termination_by n` plus `omega` suffices, as the session already found. Hofstadter's partial Q becomes a *function* on ℕ+ only after totality is proved, which is NKS's conditional statement in Lean form.

**5. Use a strict relational spec for general nested recurrences.** For Q there is no cancellation issue. If the project generalizes to arbitrary nested recurrences (e.g., to formalize Celaya–Ruskey-style undecidability), it should fix strict ("leftmost innermost") semantics, per the NKS note.

**6. Warm-up ladder.** Before Q, prove lookback-boundedness for:
- P111 (closed form);
- S1 = G (closed form);
- S-family "bounded by a + b";
- **P312 "only f[−3..0]"**: the closest analogue, open as a formal statement per Wolfram's 2024 to-do; finite transient check plus an induction on the mod-6 block formula.

Then attempt Q's invariant ∀n, Q(n) ≤ n, for which neither the essay nor anyone else offers a strategy.

**7. Expectations from the essay.** Its irreducibility and PCE framing argues against expecting a P312-style "direct formula" for Q. Any proof will likely need a non-closed-form invariant, as in the 2026 perturbed-Q certificate approach (`q_sequence_mathematics.md` §4), or a genuinely new idea.

### Gaps
- No source evaluates whether P312's bounded lookback has been or can be proved. The suggestion is mine, based on Wolfram's working note and the essay's explicit formula.
- The essay does not discuss formalization, proof assistants or AI at all. Every design recommendation here is my inference, not the essay's position.

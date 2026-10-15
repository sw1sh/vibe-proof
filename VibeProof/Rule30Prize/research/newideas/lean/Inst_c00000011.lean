import Ruliology.CellularAutomata.Rule30Jen

/-!
# Strip certificates: excluding a periodic tail `w^∞` of the center column by a finite computation

Suppose the center column equals `w^∞` (phase `(t - T) % P`) from time `T` on.  The cells `1..b` of the
right half then evolve as a finite nondeterministic system: the next strip is
`lin3 (c :: s ++ [x])`, where `c` is the center cell and `x = cell t (b+1)` is unknown.

A *certificate* assigns to every node `(phase, strip)` a rank and a position such that along every edge
the rank does not increase, and along every rank-preserving edge the position advances like a counter
modulo `m` (only at the white phases of `w`) and, at white phases, column 1 is the `pos`-th letter of a
fixed word.  Along the true history the rank is eventually constant, after which column 1 restricted to
the white times is periodic; `masked_jen` (Jen's theorem with the right neighbour masked by the zeros of
the column) gives the contradiction.

`Cert.sound` is the soundness theorem; the checks `Cert.check`, `Cert.checkG` are Boolean computations
discharged by `decide` for each concrete certificate.
-/

namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

/-! ### Masked Jen -/

theorem masked_jen (i : Int) {T Q : Nat} (hQ : 0 < Q)
    (h0 : ∀ t, T ≤ t → cell (t + Q) i = cell t i)
    (h1 : ∀ t, T ≤ t → cell t i = false → cell (t + Q) (i + 1) = cell t (i + 1)) : False := by
  have hm : ∀ t, T ≤ t → cell (t + Q) (i - 1) = cell t (i - 1) := by
    intro t ht
    rw [cell_left (t + Q) i, cell_left t i, show t + Q + 1 = (t + 1) + Q by omega,
      h0 (t + 1) (by omega), h0 t ht]
    cases hc : cell t i with
    | false => rw [h1 t ht hc]
    | true => rfl
  have e : i - 1 + 1 = i := by omega
  refine not_adjacent (i - 1) ⟨T, Q, hQ, hm⟩ ?_
  rw [e]
  exact ⟨T, Q, hQ, h0⟩

/-! ### The right strip as lists -/

def lin3 : List Bool → List Bool
  | a :: b :: c :: rest => xor a (b || c) :: lin3 (b :: c :: rest)
  | _ => []

def seg (f : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => f 0 :: seg (fun i => f (i + 1)) n

theorem lin3_seg : ∀ (m : Nat) (f : Nat → Bool),
    lin3 (seg f (m + 2)) = seg (fun i => xor (f i) (f (i + 1) || f (i + 2))) m
  | 0, f => rfl
  | m + 1, f => by
    show xor (f 0) (f 1 || f 2) :: lin3 (seg (fun i => f (i + 1)) (m + 2)) = _
    rw [lin3_seg m (fun i => f (i + 1))]
    rfl

theorem seg_succ : ∀ (n : Nat) (f : Nat → Bool), seg f (n + 1) = seg f n ++ [f n]
  | 0, f => rfl
  | n + 1, f => by
    show f 0 :: seg (fun i => f (i + 1)) (n + 1) = f 0 :: (seg (fun i => f (i + 1)) n ++ [f (n + 1)])
    rw [seg_succ n (fun i => f (i + 1))]

theorem length_seg : ∀ (n : Nat) (f : Nat → Bool), (seg f n).length = n
  | 0, _ => rfl
  | n + 1, f => by simp [seg, length_seg n]

/-- Columns `1..m` at time `t`. -/
def rowR (t m : Nat) : List Bool := seg (fun i => cell t ((i : Int) + 1)) m

theorem cons_rowR (t m : Nat) :
    cell t 0 :: rowR t m = seg (fun i => cell t (i : Int)) (m + 1) := by
  show cell t 0 :: seg (fun i => cell t ((i : Int) + 1)) m = cell t ((0 : Nat) : Int) :: seg _ m
  congr 2

/-- One step of the strip: the new strip is `lin3` of the old one with the center cell in front and
cell `b+1` at the end. -/
theorem rowR_succ (t b : Nat) :
    rowR (t + 1) b = lin3 (cell t 0 :: (rowR t b ++ [cell t ((b : Int) + 1)])) := by
  have e1 : rowR t b ++ [cell t ((b : Int) + 1)] = rowR t (b + 1) := by
    unfold rowR; rw [seg_succ]
  rw [e1, cons_rowR, lin3_seg]
  unfold rowR
  congr 1
  funext i
  show rule (cell t ((i : Int) + 1 - 1)) (cell t ((i : Int) + 1)) (cell t ((i : Int) + 1 + 1)) =
    xor (cell t (i : Int)) (cell t ((i + 1 : Nat) : Int) || cell t ((i + 2 : Nat) : Int))
  rw [show ((i : Int) + 1 - 1) = (i : Int) by omega, show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega,
    show ((i + 2 : Nat) : Int) = (i : Int) + 1 + 1 by omega]
  rfl

theorem rowR_length (t b : Nat) : (rowR t b).length = b := length_seg b _

theorem rowR_head (t b : Nat) (hb : 0 < b) : (rowR t b).headD false = cell t 1 := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rfl

/-! ### Certificates -/

/-- Little-endian encoding of a strip. -/
def enc : List Bool → Nat
  | [] => 0
  | x :: l => (if x then 1 else 0) + 2 * enc l

/-- A certificate with packed tables: `rankP` (16-bit fields indexed by node), `posP` (8-bit fields by
node), `perP` (8-bit fields by rank), `wordP` (64-bit fields by rank, bit `p` = letter `p`). -/
structure Cert where
  w : List Bool
  b : Nat
  nranks : Nat
  rankP : Nat
  posP : Nat
  perP : Nat
  wordP : Nat

namespace Cert
variable (C : Cert)

def P : Nat := C.w.length
def wAt (φ : Nat) : Bool := C.w.getD φ false
def idx (φ : Nat) (s : List Bool) : Nat := φ * 2 ^ C.b + enc s
def rk (φ : Nat) (s : List Bool) : Nat := (C.rankP >>> (16 * C.idx φ s)) % 65536
def ps (φ : Nat) (s : List Bool) : Nat := (C.posP >>> (8 * C.idx φ s)) % 256
def m (r : Nat) : Nat := (C.perP >>> (8 * r)) % 256
def u (r p : Nat) : Bool := (C.wordP >>> (64 * r + p)) % 2 == 1

/-- Counter update at phase `φ` inside rank class `r`. -/
def nextPos (r p φ : Nat) : Nat := if C.wAt φ then p else (p + 1) % C.m r

/-- The edge condition for `(φ, s) → ((φ+1) % P, s')`. -/
def edgeOK (φ : Nat) (s s' : List Bool) : Bool :=
  let φ' := (φ + 1) % C.P
  let r := C.rk φ s
  decide (C.rk φ' s' ≤ r) &&
  (!(C.rk φ' s' == r) ||
    ((C.ps φ' s' == C.nextPos r (C.ps φ s) φ) && (C.wAt φ || (s.headD false == C.u r (C.ps φ s)))))

def check : Bool :=
  (List.range C.P).all fun φ => (allLists C.b).all fun s =>
    [false, true].all fun x => C.edgeOK φ s (lin3 (C.wAt φ :: (s ++ [x])))

/-- The counter-phase map `G (p, φ) = (nextPos p φ, (φ+1) % P)`. -/
def G (r : Nat) (q : Nat × Nat) : Nat × Nat := (C.nextPos r q.1 q.2, (q.2 + 1) % C.P)

end Cert

def Cert.iterG (C : Cert) (r : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, q => q
  | n + 1, q => Cert.iterG C r n (C.G r q)

namespace Cert
variable (C : Cert)

/-- Every node's position is below its period, every period is positive, and `G^(m P) = id`. -/
def checkG : Bool :=
  (List.range C.nranks).all (fun r => decide (0 < C.m r) &&
    ((List.range (C.m r)).all fun p => (List.range C.P).all fun φ =>
      C.iterG r (C.m r * C.P) (p, φ) == (p, φ))) &&
  ((List.range C.P).all fun φ => (allLists C.b).all fun s =>
    decide (C.rk φ s < C.nranks) && decide (C.ps φ s < C.m (C.rk φ s)))

end Cert

/-! ### Soundness -/

theorem allLists_mem (l : List Bool) (n : Nat) (h : l.length = n) : l ∈ allLists n := by
  subst h; exact mem_allLists l

theorem antitone_eventually_const (f : Nat → Nat) (T : Nat) (h : ∀ t, T ≤ t → f (t + 1) ≤ f t) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → f t = f T' := by
  have mono : ∀ t s, T ≤ t → f (t + s) ≤ f t := by
    intro t s ht
    induction s with
    | zero => exact Nat.le_refl _
    | succ s ih => exact Nat.le_trans (h (t + s) (by omega)) ih
  -- strong induction on the value f T
  suffices H : ∀ n, ∀ T₀, T ≤ T₀ → f T₀ ≤ n → ∃ T', T₀ ≤ T' ∧ ∀ t, T' ≤ t → f t = f T' by
    obtain ⟨T', h1, h2⟩ := H (f T) T (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨T', h1, h2⟩
  intro n
  induction n with
  | zero =>
    intro T₀ hT₀ hf
    refine ⟨T₀, Nat.le_refl _, fun t ht => ?_⟩
    have := mono T₀ (t - T₀) hT₀
    rw [show T₀ + (t - T₀) = t by omega] at this
    omega
  | succ n ih =>
    intro T₀ hT₀ hf
    by_cases hc : ∀ t, T₀ ≤ t → f t = f T₀
    · exact ⟨T₀, Nat.le_refl _, hc⟩
    · have : ∃ t, T₀ ≤ t ∧ f t ≠ f T₀ := by
        refine Classical.byContradiction fun hn => hc fun t ht => ?_
        exact Classical.byContradiction fun hne => hn ⟨t, ht, hne⟩
      obtain ⟨t₁, ht₁, hne⟩ := this
      have hle := mono T₀ (t₁ - T₀) hT₀
      rw [show T₀ + (t₁ - T₀) = t₁ by omega] at hle
      obtain ⟨T', h1, h2⟩ := ih t₁ (by omega) (by omega)
      exact ⟨T', by omega, h2⟩

theorem iterG_add (C : Cert) (r : Nat) : ∀ (a n : Nat) (q : Nat × Nat), C.iterG r (a + n) q = C.iterG r n (C.iterG r a q)
  | 0, n, q => by simp [Cert.iterG]
  | a + 1, n, q => by
    rw [show a + 1 + n = (a + n) + 1 by omega]
    show C.iterG r (a + n) (C.G r q) = C.iterG r n (C.iterG r a (C.G r q))
    exact iterG_add C r a n (C.G r q)

theorem Cert.sound (C : Cert) (hC : C.check = true) (hG : C.checkG = true) (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P)) : False := by
  -- the history
  let ph : Nat → Nat := fun t => (t - T) % C.P
  let st : Nat → List Bool := fun t => rowR t C.b
  have hph : ∀ t, T ≤ t → ph (t + 1) = (ph t + 1) % C.P := by
    intro t ht
    show (t + 1 - T) % C.P = ((t - T) % C.P + 1) % C.P
    rw [show t + 1 - T = (t - T) + 1 by omega]
    exact (Nat.mod_add_mod (t - T) C.P 1).symm
  have hphlt : ∀ t, ph t < C.P := fun t => Nat.mod_lt _ hP
  -- every true step is an edge of the certificate graph, hence satisfies edgeOK
  have hedge : ∀ t, T ≤ t → C.edgeOK (ph t) (st t) (st (t + 1)) = true := by
    intro t ht
    have hall := hC
    unfold Cert.check at hall
    have h1 := List.all_eq_true.1 hall (ph t) (List.mem_range.2 (hphlt t))
    have h2 := List.all_eq_true.1 h1 (st t) (allLists_mem _ _ (rowR_length t C.b))
    have h3 := List.all_eq_true.1 h2 (cell t ((C.b : Int) + 1)) (by cases cell t ((C.b : Int) + 1) <;> simp)
    have hs : st (t + 1) = lin3 (C.wAt (ph t) :: (st t ++ [cell t ((C.b : Int) + 1)])) := by
      show rowR (t + 1) C.b = _
      rw [rowR_succ, h t ht]
    rw [hs]; exact h3
  -- rank along the history
  let R : Nat → Nat := fun t => C.rk (ph t) (st t)
  have hRle : ∀ t, T ≤ t → R (t + 1) ≤ R t := by
    intro t ht
    have e := hedge t ht
    unfold Cert.edgeOK at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    show C.rk (ph (t + 1)) (st (t + 1)) ≤ C.rk (ph t) (st t)
    rw [hph t ht]; exact e.1
  obtain ⟨T', hT', hconst⟩ := antitone_eventually_const R T hRle
  let r := R T'
  -- along rank-preserving steps: counter update and output
  have hstep : ∀ t, T' ≤ t →
      C.ps (ph (t + 1)) (st (t + 1)) = C.nextPos r (C.ps (ph t) (st t)) (ph t) ∧
      (C.wAt (ph t) = false → cell t 1 = C.u r (C.ps (ph t) (st t))) := by
    intro t ht
    have e := hedge t (by omega)
    have hRt : R t = r := hconst t ht
    have hRt1 : R (t + 1) = r := hconst (t + 1) (by omega)
    unfold Cert.edgeOK at e
    rw [← hph t (by omega)] at e
    have hr1 : C.rk (ph (t + 1)) (st (t + 1)) = C.rk (ph t) (st t) := by
      show R (t + 1) = R t; rw [hRt, hRt1]
    simp only [hr1, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at e
    have hrt : C.rk (ph t) (st t) = r := hRt
    rw [hrt] at e
    refine ⟨e.2.1, fun hw => ?_⟩
    have e2 := e.2.2
    rw [hw, Bool.false_or, beq_iff_eq] at e2
    rw [← rowR_head t C.b hb]; exact e2
  -- the counter-phase pair follows G
  let q : Nat → Nat × Nat := fun t => (C.ps (ph t) (st t), ph t)
  have hq : ∀ t, T' ≤ t → q (t + 1) = C.G r (q t) := by
    intro t ht
    show (C.ps (ph (t + 1)) (st (t + 1)), ph (t + 1)) = (C.nextPos r (C.ps (ph t) (st t)) (ph t), (ph t + 1) % C.P)
    rw [(hstep t ht).1, hph t (by omega)]
  have hqiter : ∀ t, T' ≤ t → ∀ n, q (t + n) = C.iterG r n (q t) := by
    intro t ht n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show t + (n + 1) = (t + n) + 1 by omega, hq (t + n) (by omega), ih,
        show n + 1 = n + 1 from rfl, iterG_add C r n 1 (q t)]
      rfl
  -- checkG facts
  have hG' := hG
  unfold Cert.checkG at hG'
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq] at hG'
  obtain ⟨hGr, hGn⟩ := hG'
  have hrlt : r < C.nranks := (hGn (ph T') (hphlt T') (st T') (allLists_mem _ _ (rowR_length T' C.b))).1
  have hm : 0 < C.m r := (hGr r hrlt).1
  -- periodicity of the counter-phase pair after T'
  have hper : ∀ t, T' ≤ t → q (t + C.m r * C.P) = q t := by
    intro t ht
    rw [hqiter t ht]
    have hpos : C.ps (ph t) (st t) < C.m (C.rk (ph t) (st t)) :=
      (hGn (ph t) (hphlt t) (st t) (allLists_mem _ _ (rowR_length t C.b))).2
    have hrt : C.rk (ph t) (st t) = r := hconst t ht
    rw [hrt] at hpos
    exact (hGr r hrlt).2 _ hpos _ (hphlt t)
  -- conclude with masked Jen, Q = m * P
  refine masked_jen 0 (Q := C.m r * C.P) (Nat.mul_pos hm hP) (T := T') ?_ ?_
  · intro t ht
    rw [h (t + C.m r * C.P) (by omega), h t (by omega)]
    congr 1
    rw [show t + C.m r * C.P - T = (t - T) + C.P * C.m r by rw [Nat.mul_comm]; omega, Nat.add_mul_mod_self_left]
  · intro t ht hw
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hwt : C.wAt (ph t) = false := by rw [← h t (by omega)]; exact hw
    have hqe := hper t ht
    have hph' : ph (t + C.m r * C.P) = ph t := congrArg Prod.snd hqe
    have hps' : C.ps (ph (t + C.m r * C.P)) (st (t + C.m r * C.P)) = C.ps (ph t) (st t) := congrArg Prod.fst hqe
    have hwt' : C.wAt (ph (t + C.m r * C.P)) = false := by rw [hph']; exact hwt
    rw [(hstep (t + C.m r * C.P) (by omega)).2 hwt', (hstep t ht).2 hwt, hps']

end R30NewIdeas

namespace R30NewIdeas
open Ruliology.CellularAutomata.Rule30Jen

-- certificate for w = 00000011, strip width b = 6; generated by export_cert.py
def c00000011_w : List Bool := [false, false, false, false, false, false, true, true]
def c00000011_b : Nat := 6
def c00000011_nranks : Nat := 379
def c00000011_rankP : Nat := 5908444537978224163236655296421498429319017773728926993171828404275953012925332390425109119000201216083462427565142757871849860034626295403931223881241106222150053270466854427020618830510880731386842705443814880999594783283603562414106167428613391073541624499972952176041257964487185201265188274501364916375637453783096125412966729040738264837763245498509308195305617403379355993626269835575599165667633835335349760268041624215318172035553602258853210741899521520588387871713813488899669489346365892219983994031548046282376911597823844992527044282021521943211144368136118542009942969261082802584746445003177406667959687780471481438381226927659892140688804083855429404716349088729666022538008001157091463940885677568914633322104928629314563869611809232015069794040506250953797976457828286149011069602586248035031594358198147559852264021276766229959999329982737016015546050993520172023844311636110312681197707344860771099800649360263409831140795292281231716701191919599136702808141654932861426812314090649581309205702616332544890026199434624599931291165015472338453639465251874925016450272713079418577450432832586417709158654237002493185012643382384999937308940516192132378086242785134506776117779402139339578192968221538643280841921068358627415289097537490658949975342797154667244166474875791570145379791001481192492395970286549067029230609745171548152178890849834503126908805709936697254002368116916462337636977470779177778057421926068775587707223003811762221764731944417741068199673396954817160402226554607134007919986012861151845748153123255223567174269627478127135061383396582874498170371418984183696767447773403788691054932812490119919959417849268593701743002257077339514478004380792476206701938031208487667953021563127130250558892506245879941147512775648567607216033213000197401770370966883559651559079844330958519055134183306598100188036974694731916781016679327919753588452607314452408073354075766833614874356238186865217947652595507854500333807083797722627674560195439781973403780511847983417834988731421937560164194078090263146688775887587421526786916568804767180882022490329837692542831360686246698333817156921225407761241953488170383060856733588641395379521744216045949223077771200478253581793482355585838018753890098018319030481308335367686066997341554738929586666260480632709845825065782793088983902760969852443603447790898751946596110587764011015209849114615887537953087637611119889013739871505669034500845380607854888799699268389003257969101680672871
def c00000011_posP : Nat := 113468867123488522776110738442329421844101097150675934452456924570887630471630423523079603744824693542057907475960951883496790027913174019785447617839097786191275371657440967121299053696727209607798969224894284471651279288846941547866014513929170196622347621724980942065520587383081186963289929406325890527395186194300981924172630837476992509343072055987057164672601305725490170987098593173112763934305565202966222307943342760781957653418688069542609844835121961706799649842478673895801764184975815400214089371218339598678746403023058591266155012153893264975690653607953982367100522103832053935632236768177307917591038191954098948849439931006947144364481303663387133559069541371083555899379997713114999864421272550837282154880719250237005961992476457707853320723227019813898922126610475297734147493899376630802082081987992179517934813087679877372335876120996023434538490621853030053114518108504764119349155264693650147246080
def c00000011_perP : Nat := 20720807341871434971548591111075382931245597538362567183551515765170301561086294167553155850945491433513855528497659990477784743339583039456317061701698735754911081183010824753856806605347580950954596746159386072076740961932256853869261122119573338883596574516148500357707255312412231431434578516140232327088216468051091431784988475057266567128123138324065925448279579486114364737040276292275046511105449541762993321634220128725691028147801542313778252544822215994957935698608552271111344023969712380013171904144753260753831871485157142792096793275495641284957634382019569975693759688897193178515886940958588579348101890468652765609912956077654844299012676162460491077043880718573643589326573815908419270207645302276295427219494174657244021940097552321118889694825120316262326733568541226379827297146436930291422912218534664258817691972246358327595261755038601351874401252892680390532366407563464267509788639489
def c00000011_wordP : Nat := 32754260930411245273845066664824029604168534214239534371933563959653781958516941287413869865034745649469812489581941978090705548689166503309533416664702253768319974407938315218461354095938439345287502440309093681057177754150596827807980607723556261542351392015659755896833

def C_c00000011 : Cert := { w := c00000011_w, b := c00000011_b, nranks := c00000011_nranks, rankP := c00000011_rankP, posP := c00000011_posP, perP := c00000011_perP, wordP := c00000011_wordP }

theorem C_c00000011_check : C_c00000011.check = true := by decide +kernel
theorem C_c00000011_checkG : C_c00000011.checkG = true := by decide +kernel

/-- The center column of rule 30 is not eventually periodic with repeating block `00000011` (any phase: the
block starts at the time `T`). -/
theorem not_eventually_c00000011 (T : Nat)
    (h : ∀ t, T ≤ t → cell t 0 = C_c00000011.wAt ((t - T) % C_c00000011.P)) : False :=
  Cert.sound C_c00000011 C_c00000011_check C_c00000011_checkG (by decide) (by decide) T h

end R30NewIdeas

#print axioms R30NewIdeas.not_eventually_c00000011

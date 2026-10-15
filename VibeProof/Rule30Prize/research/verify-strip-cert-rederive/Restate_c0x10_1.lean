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

-- certificate for w = 00000000001, strip width b = 6; generated by export_cert.py
def c0x10_1_w : List Bool := [false, false, false, false, false, false, false, false, false, false, true]
def c0x10_1_b : Nat := 6
def c0x10_1_nranks : Nat := 591
def c0x10_1_rankP : Nat := 20499572890849714758802002292166847456668233397096234659741668290571380263653782326885946955910254932606640402468512014706530635757012394467680406288786577875179985452988458065013828096750290985814270286682046363118502718009940809255012416592872536436851547444569432608416414589910201868997355517973093186025903515959054179099212231157840425780460041953604440505669007133056767562234990202225887163779487326011919757171769570550540973495903953846608923199759593010357505017929708775224337746191965869242462606278137954181520449872288788436986457110713189673056320098288144959067319796005316514921834278850529193520395559122617873382040979191719744292191703056198660417039961314853431549924231521903458944613719146575936967109085173792641776734191558208328713698177612223434231627058733257478419562969797940319123940738159625587114385339213862021701677833289476104315393828974459038675283827297458992850362909225758601224668499336996573089394192309414220024066204161278867856928149152785180423243723753030666277946498017930940461345290951503411950088289336806669132608231940138126780941402636339739842712271565863494076440555477556319476465684417866024088918427337624464995092762825060074366529905748589173314945299905401206425664428390006462257528388180860904649326442348231547227966369452658543799694140223661854458657821494953166968160555695615785219109670678901672699010372557888778308550354602468910444204729978324366750426203518411851240724640616664493910130739582421989283488008137864384333520078135377401453359539270209661871409139162490791749664011290029368472127872078986402319291490289154864369928430218430199653074443346470481540033204398573403654933343948490109405152658266969528676441618686107671430778417021789898376330190185532813654156280185339864959490632917485459781958021513789417702362164701435987552046736126542740614452597669246074406172797075541489984504048287358764942878206910719106133599764060912250311958725613866245022191457136995988077489766555165471672522865810074973981017351801314051217935039797120821225308095506030843204886013086354497950478072449194972958977718321656441089237922905300686549718930135982032849677661593420849289158725864449740925440170939883072842298830960679666397864031273810038879141031934489830787697808810773430689670373626826718343181262841157834598802864049986597584543822667227904254840248106160459228732740572965822246733625937702726532198649046323988685182011539470567266011093932645514209418229539137519950764868967048897736299382832800992649283845822474036615877143818479037065933184963925857691405058085267437481688262155324689890211115857960179105408223997367780826713538028314765197793840549762954227115462307634811106013658395424363703569233669943207232254301877760277025693885539408884601835179053136523876158166336659715065407850637496420273449954015526684481237091706684286941417450348355346903359444476613212608150487095464422042182505004843861525163758372867412656061167534817326878368750949583279270934309404937333370816356024396793640519487739270005712218369634262224355444804042186517163481076139394919603754906034085597542795185329657791049594301730679977282895047261795250393548063705455038498745160144827618119759387826150757357114165088037954011552067051514109531122821577372008660433405166199711159902480591845536823203779902179068375585127663993024413285061017371560741273240580188276688747232710481968496852
def c0x10_1_posP : Nat := 100716450811544767765828808592932286966702401751483077192625988135117481886961519808039556183322039157784460092232985234295109128339192807544432156916491609285764168967075181055259199305091578113610631179842600069095995886533878571839082883644208335339053598478570349189308015084960093338188608829790926979482211529649055629084247781124751999740092539528204311493655410351864715382121160308247541643967083228623260180294277734072728071408956488116277298275589802926720358081602595525750777308302935623275918035456091846418119408399240262793144978647092748561497096657208556228470440149294568646413430991171393642276492368494390062285467918163755036580035930817976849981973361822831382774446769480663980609329383314613010377520098260114900427679336003466928065634189740890940351920760566621226660907134429976194955671424274204293750985682916033793652120877866896028382404074429677549167708470998070677604001534267020485341219571606679503287121731104487901096255521884030861114917142308315568772916462919146409919534417456467328925340228355304660137973526029715392737073780221896253302600272073477209491100695853025347800154835782661103399220991527761786912189193818144938267687672193227395580383875876375497780454069969325684094767834341857228108391262775128683631523387954273432908261522657663930146599312308965846387224414841564186782528597368232650294561403766400185603226356918817592143294110233839463073511108003264650769459992997084362535911898013219402496859273324475614676445752141352753546654467825947669796121579311251016646656
def c0x10_1_perP : Nat := 72992681574025384849311916886227051641478170824987319062298668003137282402606342525500004136114402333145510763013789798684162483311115462055150723186221669627704789966172435213776067168101367483032000499415497215616606060683376343597427004726287364284379693654809964766944469363799217907755109577479203836260801474536488742610475412421952166842566532699024950747863260712223518451618597032625693511694271381015842399184669388013655556559349488043854155487827089651752281840487600168509890763292524033108810057733952073393878047736875314413941782462875833707601959214961476185856657015432520914656829376496954694336292477975700743234616772901314825232845609027090934908757636520064684272817163192413387514893766213652056706322840078564136524114721929514445244008487721335641625911504688953829598565726090153163773782317721570212256710469071051108482494910325090142627181122182383489540351573031101729049465101252525449879604080388219826324388100494181827501912575906762582890586376258242553209083152012189095219422486190007006761452032020501924286343744215829104470134350292321313398423193312650555333598902885870809248117602640473956501150114025432708974252460386030292971696276483874374403502401425232912808908675985234248149945629573472864820732326798788434370032076810667844581640700889015360156409478534092000712646825710824876799042437560814143967286311810623854115837496848480679301404972368300139012904817285726474
def c0x10_1_wordP : Nat := 18211360393816091977223655565219208491611646289061517607899277381382106325875691709797533396739667160062002519036123019250208538139609428615435359862871587240640419588996950253011294346633089612951154902413742931452449146708959437005043705512760148840675777129643122369550643869257141449584823792448078408590413397239107408785989271051123446710801119696565202678447757384835699161586861103910217685824838322234973239773190038534625760026752335106237192642461182717582614023752375167584176635517847124647947866936758927725575301801453442540321896042426918126551617977206372031428052419877301143514755334979595924981375127087537027469277522361936784228983596156835252259681319715448700596446511376916435293714440257109831310402094389248177886501390095237987572074706425968559206179722874258587797950149010229582973347951043459712373261388582938870658943962585545218830465253530535856381003221677899896109043660871487399396363910418600454979274208799658272639746584501881199078557058475720220914746707897372848978235024387686054306533879907920662994440305844283188046770237284136662814051222095889549895313585728688218459977998036600972012883755795074300151265324380465177363439411673064769516656869844813206914739156367219033688261903734163034517003531415119297602537457400273145770460568989908509271727404505676525186852526374353532381325204506963101384971570590294886404976796380952907129069284492370052251641155427088903924074946115131859859157206173792000701133216168406512819713766512770888829944714279250977276054743681236069869260737544448074801594272611469730716047050732792459278750791669551886593632954175118110543800459546974270415682931609039696963383307338141702977434053507375847322256159480405917673092055657284720360640462980911294001807931689965571596542172774732199594427414549411808722830641814170893824310563931159665885246252860107752868301982305592638860845152910737084979409799737343294740296443193083190007464845083959910009474322522760773782804401323125614693204109811580242286999011702281567522449009687277651914360506179522928883549814413087618612222497983078679815206068259360321865035408119045761112175921404427185998422408896828153230061022834225492502443079682248897922895508813222462925051177101862225570835196286277422134650933221950264032441460349903886410780733801428598981688065365949731200260827944367366936576736650857223798733945116780840583124602379446991463526758479504409209664529441244326153941633707288867767956805850229245528738863694848579922315473150283552505667696047700556207739056296728507847747716287955465137386494787438079874109685992381249383214930544314076462904425698017825161125528006550903891429138029369248305664603082932643126906917071284855362010789721584738382124445947012505578083965740286712238232161960234603730637430822613396225599853849305502544652151998183891606189618305313416148788644752671684492987449457587230998643336272199076630141469169885352397492668840948174721359851693564835814958624834372066506479914593891078505202956348556568195626525974844947558072386879949537252255628610872144966862089735851943709259876057388087156188418082218349450502877629496409685217275913880034041897016506033188949912673016443939868790112086308633435470547747010321255205284811600883214059278772591286610745748500684982353748084940659963018697567064173899866906398269478199783688868151213020607318010937279922097999022324681984635855802333379185589234934247317757207702372273052829493807874842106581142241882691138839737146569218473309044003140956182440562296019362056937949743309381708212145356706163485345016260373941126924057724708740031791690879091851386658657197337191769321508688870344344856356423999586193784897477669883988896312860633136589267979817551371670446561182257260891122255926859836715191723627759383272991255822633389298115882457040228172081838372457416990605773302905966233564674204849395261202001333621565552402408068316063417034526900494949251569124908749419962752695806466363082465050477931954471047193791462649769749222645115686828160227554792725880305329426172730122310080269309511799702812961858350017938428

def C_c0x10_1 : Cert := { w := c0x10_1_w, b := c0x10_1_b, nranks := c0x10_1_nranks, rankP := c0x10_1_rankP, posP := c0x10_1_posP, perP := c0x10_1_perP, wordP := c0x10_1_wordP }

theorem C_c0x10_1_check : C_c0x10_1.check = true := by decide +kernel
theorem C_c0x10_1_checkG : C_c0x10_1.checkG = true := by decide +kernel

/-- The center column of rule 30 is not eventually periodic with repeating block `00000000001` (any phase: the
block starts at the time `T`). -/
theorem not_eventually_c0x10_1 (T : Nat)
    (h : ∀ t, T ≤ t → cell t 0 = C_c0x10_1.wAt ((t - T) % C_c0x10_1.P)) : False :=
  Cert.sound C_c0x10_1 C_c0x10_1_check C_c0x10_1_checkG (by decide) (by decide) T h

end R30NewIdeas

#print axioms R30NewIdeas.not_eventually_c0x10_1


namespace VerifyRestate
open Ruliology.CellularAutomata.Rule30Jen

theorem no_tail_c0x10_1 :
    ¬ ∃ T : Nat, ∀ t, T ≤ t → cell t 0 = ([false, false, false, false, false, false, false, false, false, false, true] : List Bool).getD ((t - T) % 11) false :=
  fun ⟨T, h⟩ => R30NewIdeas.not_eventually_c0x10_1 T h

theorem no_tail_rot_c0x10_1 :
    ¬ ∃ T k : Nat, ∀ t, T ≤ t → cell t 0 = ([false, false, false, false, false, false, false, false, false, false, true] : List Bool).getD ((t + k) % 11) false := by
  rintro ⟨T, k, h⟩
  refine R30NewIdeas.not_eventually_c0x10_1 (11 * T + (11 - k % 11)) fun t ht => ?_
  rw [h t (by omega)]
  show _ = List.getD ([false, false, false, false, false, false, false, false, false, false, true] : List Bool) ((t - (11 * T + (11 - k % 11))) % 11) false
  congr 1
  omega

end VerifyRestate

#print axioms VerifyRestate.no_tail_c0x10_1
#print axioms VerifyRestate.no_tail_rot_c0x10_1

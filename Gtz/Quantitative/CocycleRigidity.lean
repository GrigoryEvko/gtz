import Gtz.Quantitative.TwoGraphCollision
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.EdgeOrbitSectors

/-!
# Cocycle rigidity of the signed erase system

The edge law `Gtz.sum_erasePair_weight_mul_atomPairing`, multiplied through by the
edge pairing, turns every summand into an oriented triple product whose sign is the
two-graph parity `Gtz.tripleParity`.  What is left is a system of `C(m,2)` equations
in the `C(m,3)` triple signs -- the SIGNED ERASE SYSTEM -- which the design's own
parity solves.  A second solution is a PHANTOM: a sign pattern indistinguishable
from the design by the field-blind data, and therefore a seam in any argument that
reasons about a design through its moduli alone.

This file asks when the phantom seam is closed.  The answer is a dichotomy.

* **The difference principle.**  Two solutions of one weighted sign equation force
  the signed weights to cancel on their DISAGREEMENT set.  If that set is a
  singleton at some edge, one strictly positive term must vanish -- impossible.
  Both statements are proved over an arbitrary finite index set, so they are
  `m`-uniform and rank-uniform.

* **The census.**  A flip pattern is a two-graph, and the tree already carries the
  gauge-fixed encoding of two-graphs on six labels as a `link : Nat` below `1024`
  (`Gtz.sectorIncoherent`), already bridged to designs by
  `Gtz.sectorIncoherent_linkWordOf`.  Of the `1023` nontrivial links, `900` have an
  edge whose star meets the flip support exactly once and die unconditionally; the
  `123` survivors each flip at least EIGHT triples and impose an exact relation on
  at least TWELVE of the fifteen edges.  Both constants are attained.

* **The `tau_all` locus.**  The global flip solves exactly when every erase
  right-hand side vanishes; with nonvanishing pairings that says every pair of
  shares sums to one, hence -- from three labels up -- every share is `1/2`, which
  forces `size = 2 * rank`.  So the largest degeneracy component lives ONLY at the
  self-dual cells: at `(6,3)` it is present, at the rank-four top `(10,4)` it is
  absent.

* **The icosahedron.**  `Gtz.atomShare_icosaDesign` puts every icosahedral share at
  `1/2`, so the global flip solves there: rigidity is FALSE as a global statement
  over admissible designs, and the counterexample is a shipped object.

## What is new here, and what was already in the tree

| this file                                          | shipped twin it rests on                          |
| -------------------------------------------------- | ------------------------------------------------- |
| `Gtz.SolvesSignedEraseSystem`                       | `Gtz.sum_erasePair_weight_mul_atomPairing`         |
| `Gtz.tripleRadius`                                  | `Gtz.tripleParity_mul_abs_atomPairingProduct`      |
| `Gtz.flipStar`, `Gtz.flipSupport`, `Gtz.liveEdges`  | `Gtz.sectorIncoherent`, `Gtz.sectorCount`          |
| `Gtz.linkWordOf_icosaDesign`                        | `Gtz.linkWordOf`, `Gtz.icosahedralLink_mem_residualSectors` |

The two-graph vocabulary itself -- `Gtz.edgeSign`, `Gtz.tripleParity`, the sector
encoding and its design bridge -- is NOT introduced here; it is shipped in
`Gtz/Quantitative/SwitchingTwoGraph.lean` and `Gtz/Quantitative/TwoGraphCollision.lean`
and is consumed verbatim.  `Gtz.linkWordOf_icosaDesign` upgrades to a theorem the
identification that `Gtz.icosahedralLink_mem_residualSectors` records in prose as
"an ATTRIBUTION, not proved here".

## Two corrections to the record

1. The converse of the `tau_all` characterisation is FALSE.  `size = 2 * rank` does
   NOT force the shares to `1/2`: the shipped `Gtz.orthoSplitDesign` is a
   `WeightedDesign 6 3` -- so `size = 2 * rank` -- with shares
   `1/2, 1/2, 4/5, 1/5, 1/2, 1/2`.  Landed as
   `Gtz.not_forall_atomShare_eq_half_of_size_eq_two_mul_rank`.  Only the forward
   implication is a theorem, and only it is landed.

2. The relabelling transport lemmas `Gtz.atomPairing_relabelDesign`,
   `Gtz.edgeSign_relabelDesign` and `Gtz.tripleParity_relabelDesign` are NOT
   introduced here: they are shipped in `Gtz/Quantitative/EdgeOrbitSectors.lean`,
   each by `rfl`, and are imported and consumed.

3. The kill dichotomy is worth stating only in its SURVIVOR-CONDITIONAL form.  Of
   the `900` killed links, `825` also carry eight or more flipped triples, so a
   disjunctive phrasing "killed OR at least eight" is `825/900` covered by its own
   second arm and reports almost nothing.  `Gtz.killCensus` therefore quantifies
   over survivors only.
-/

namespace Gtz

open Finset

variable {sizeIndex : ℕ}

/-! ## 1. The difference principle

Two `±1` patterns solving one weighted sign equation cannot differ anywhere the
signed weights fail to cancel.  Nothing here knows about designs, triples or rank:
the statements are about a finite index set, a coefficient function and two sign
functions, which is exactly the generality the erase system consumes one edge at a
time. -/

/-- **THE DIFFERENCE PRINCIPLE.**  Two solutions of the same weighted sign equation
have signed weights summing to zero on the set where they DISAGREE.  Subtracting the
two equations cancels the agreement terms and doubles the disagreement ones. -/
theorem sum_disagreement_eq_zero_of_solvesSame {index : Type*} [DecidableEq index]
    (star : Finset index) (coeff signFirst signSecond : index → ℝ) (target : ℝ)
    (hunit : ∀ other ∈ star, signSecond other = signFirst other
      ∨ signSecond other = -signFirst other)
    (hfirst : ∑ other ∈ star, coeff other * signFirst other = target)
    (hsecond : ∑ other ∈ star, coeff other * signSecond other = target) :
    ∑ other ∈ star.filter (fun other => signSecond other ≠ signFirst other),
        coeff other * signFirst other = 0 := by
  classical
  have hdiff : ∑ other ∈ star,
      (coeff other * signFirst other - coeff other * signSecond other) = 0 := by
    rw [Finset.sum_sub_distrib, hfirst, hsecond, sub_self]
  have hsplit : ∑ other ∈ star,
        (coeff other * signFirst other - coeff other * signSecond other)
      = ∑ other ∈ star.filter (fun other => signSecond other ≠ signFirst other),
          (coeff other * signFirst other - coeff other * signSecond other) := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro other _ hnonzero hequal
    exact hnonzero (by rw [hequal]; ring)
  have hdouble : ∀ other ∈ star.filter (fun other => signSecond other ≠ signFirst other),
      coeff other * signFirst other - coeff other * signSecond other
        = 2 * (coeff other * signFirst other) := by
    intro other hother
    rw [Finset.mem_filter] at hother
    rcases hunit other hother.1 with hagree | hflip
    · exact absurd hagree hother.2
    · rw [hflip]; ring
  rw [hsplit, Finset.sum_congr rfl hdouble, ← Finset.mul_sum] at hdiff
  linarith [hdiff]

/-- A singleton disagreement forces its one coefficient-times-sign to vanish. -/
theorem coeff_eq_zero_of_singleton_disagreement {index : Type*} [DecidableEq index]
    (star : Finset index) (coeff signFirst signSecond : index → ℝ) (target : ℝ)
    (witness : index)
    (hunit : ∀ other ∈ star, signSecond other = signFirst other
      ∨ signSecond other = -signFirst other)
    (hfirst : ∑ other ∈ star, coeff other * signFirst other = target)
    (hsecond : ∑ other ∈ star, coeff other * signSecond other = target)
    (hsingle : star.filter (fun other => signSecond other ≠ signFirst other) = {witness}) :
    coeff witness * signFirst witness = 0 := by
  have hsum := sum_disagreement_eq_zero_of_solvesSame star coeff signFirst signSecond target
    hunit hfirst hsecond
  rwa [hsingle, Finset.sum_singleton] at hsum

/-- **THE SIZE-ONE KILL.**  With a strictly positive coefficient and a `±1` sign the
singleton disagreement is impossible.  This is the mechanism that removes `900` of
the `1023` nontrivial two-graphs at EVERY datum, real or complex -- it consumes only
positivity of the weight and nonvanishing of the radius, never the cocycle. -/
theorem disagreement_ne_singleton_of_pos {index : Type*} [DecidableEq index]
    (star : Finset index) (coeff signFirst signSecond : index → ℝ) (target : ℝ)
    (witness : index)
    (hunit : ∀ other ∈ star, signSecond other = signFirst other
      ∨ signSecond other = -signFirst other)
    (hfirst : ∑ other ∈ star, coeff other * signFirst other = target)
    (hsecond : ∑ other ∈ star, coeff other * signSecond other = target)
    (hcoeff : 0 < coeff witness) (hsign : signFirst witness = 1 ∨ signFirst witness = -1) :
    star.filter (fun other => signSecond other ≠ signFirst other) ≠ {witness} := by
  intro hsingle
  have hzero := coeff_eq_zero_of_singleton_disagreement star coeff signFirst signSecond target
    witness hunit hfirst hsecond hsingle
  rcases hsign with hplus | hminus
  · rw [hplus] at hzero; nlinarith
  · rw [hminus] at hzero; nlinarith

/-! ## 2. The signed erase system

`Gtz.sum_erasePair_weight_mul_atomPairing` reads the Parseval identity at two atoms.
Multiplying it by the edge pairing turns each summand into the oriented product of a
triple, which `Gtz.tripleParity_mul_abs_atomPairingProduct` splits into a parity bit
times a nonnegative radius.  The result is a system whose unknowns are the twenty
triple signs and whose data are field-blind. -/

/-- The RADIUS of a triple: the modulus of its oriented pairing product.  Together
with `Gtz.tripleParity` it factors the product into a bit and a magnitude. -/
noncomputable def tripleRadius (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) : ℝ :=
  |atomPairing D first second * atomPairing D first third * atomPairing D second third|

theorem tripleRadius_nonneg (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) : 0 ≤ tripleRadius D first second third :=
  abs_nonneg _

/-- The radius is strictly positive exactly on the nonvanishing-pairing stratum --
the hypothesis the campaign calls `E3`. -/
theorem tripleRadius_pos (D : WeightedDesign sizeIndex 3)
    {first second third : Fin sizeIndex}
    (hfirstSecond : atomPairing D first second ≠ 0)
    (hfirstThird : atomPairing D first third ≠ 0)
    (hsecondThird : atomPairing D second third ≠ 0) :
    0 < tripleRadius D first second third :=
  abs_pos.2 (mul_ne_zero (mul_ne_zero hfirstSecond hfirstThird) hsecondThird)

/-- The parity carries the radius to the oriented product -- the shipped
`Gtz.tripleParity_mul_abs_atomPairingProduct`, read in the radius vocabulary. -/
theorem tripleParity_mul_tripleRadius (D : WeightedDesign sizeIndex 3)
    (first second third : Fin sizeIndex) :
    tripleParity D first second third * tripleRadius D first second third
      = atomPairing D first second * atomPairing D first third
          * atomPairing D second third :=
  tripleParity_mul_abs_atomPairingProduct D first second third

/-- **THE SIGNED ERASE SYSTEM.**  One equation per edge, in the triple signs. -/
def SolvesSignedEraseSystem (D : WeightedDesign sizeIndex 3)
    (sign : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ) : Prop :=
  ∀ edgeFirst edgeSecond : Fin sizeIndex, edgeFirst ≠ edgeSecond →
    ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        D.weight other * (sign edgeFirst edgeSecond other
          * tripleRadius D edgeFirst edgeSecond other)
      = atomPairing D edgeFirst edgeSecond ^ 2
        * (1 - atomShare D edgeFirst - atomShare D edgeSecond)

/-- **THE SYSTEM IS INHABITED.**  The design's own parity solves it, unconditionally
and at every size: this is the edge law scaled by the edge pairing.  Every rigidity
question below is about whether anything ELSE does. -/
theorem solvesSignedEraseSystem_tripleParity (D : WeightedDesign sizeIndex 3) :
    SolvesSignedEraseSystem D (tripleParity D) := by
  intro edgeFirst edgeSecond hedge
  have hlaw := sum_erasePair_weight_mul_atomPairing D hedge
  have hterm : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      D.weight other * (tripleParity D edgeFirst edgeSecond other
          * tripleRadius D edgeFirst edgeSecond other)
        = atomPairing D edgeFirst edgeSecond
          * (D.weight other
            * (atomPairing D edgeFirst other * atomPairing D other edgeSecond)) := by
    intro other _
    rw [tripleParity_mul_tripleRadius, atomPairing_comm D other edgeSecond]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hlaw]
  ring

/-- A candidate second solution: a pattern agreeing with the design's parity up to
sign at every triple.  Every two-graph flip of the design's own two-graph is one. -/
def IsParityFlip (D : WeightedDesign sizeIndex 3)
    (sign : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ) : Prop :=
  ∀ first second third : Fin sizeIndex,
    sign first second third = tripleParity D first second third
      ∨ sign first second third = -tripleParity D first second third

/-- **COCYCLE RIGIDITY** at a design: the signed erase system pins the parity of
every nondegenerate triple, so no phantom exists. -/
def HasRigidSignedEraseSystem (D : WeightedDesign sizeIndex 3) : Prop :=
  ∀ sign : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ,
    IsParityFlip D sign → SolvesSignedEraseSystem D sign →
      ∀ first second third : Fin sizeIndex, first ≠ second → first ≠ third → second ≠ third →
        sign first second third = tripleParity D first second third

/-! ## 3. The `tau_all` locus

The one rigidity-failure component with a closed form.  Negating a solution negates
every left-hand side, so the negation solves exactly when every right-hand side is
zero -- a condition on the SHARES alone. -/

/-- **THE GLOBAL FLIP CRITERION.**  Given one solution, its negation solves exactly
when every erase right-hand side vanishes.  General in the size; no cocycle, no
nondegeneracy. -/
theorem solvesSignedEraseSystem_neg_iff (D : WeightedDesign sizeIndex 3)
    (sign : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ)
    (hsolve : SolvesSignedEraseSystem D sign) :
    SolvesSignedEraseSystem D (fun first second third => -(sign first second third))
      ↔ ∀ edgeFirst edgeSecond : Fin sizeIndex, edgeFirst ≠ edgeSecond →
          atomPairing D edgeFirst edgeSecond ^ 2
            * (1 - atomShare D edgeFirst - atomShare D edgeSecond) = 0 := by
  have hrewrite : ∀ edgeFirst edgeSecond : Fin sizeIndex,
      ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
          D.weight other * (-(sign edgeFirst edgeSecond other)
            * tripleRadius D edgeFirst edgeSecond other)
        = -∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
            D.weight other * (sign edgeFirst edgeSecond other
              * tripleRadius D edgeFirst edgeSecond other) := by
    intro edgeFirst edgeSecond
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun other _ => by ring)
  constructor
  · intro hflip edgeFirst edgeSecond hedge
    have hbase := hsolve edgeFirst edgeSecond hedge
    have hneg := hflip edgeFirst edgeSecond hedge
    rw [hrewrite, hbase] at hneg
    linarith
  · intro hzero edgeFirst edgeSecond hedge
    have hbase := hsolve edgeFirst edgeSecond hedge
    have hvanish := hzero edgeFirst edgeSecond hedge
    rw [hrewrite, hbase, hvanish]
    linarith

/-- **THE CRITERION HAS CONTENT ON BOTH SIDES.**  At the tetrahedron the global flip
does NOT solve: every share is `3/4` (`Gtz.atomShare_tetraDesign`), so the edge `(0,1)`
right-hand side is `-1/2` against a squared pairing of `1`.

Landed as an anti-vacuity guard on `Gtz.solvesSignedEraseSystem_neg_iff`: paired with
`Gtz.solvesSignedEraseSystem_neg_tripleParity_icosaDesign` it shows the criterion is
satisfied at one shipped design and violated at another, so neither direction is
empty.  Note `tetraDesign : WeightedDesign 4 3` has `4 ≠ 2 * 3`, which is exactly the
`tau_all`-absence predicted below. -/
theorem not_solvesSignedEraseSystem_neg_tripleParity_tetraDesign :
    ¬ SolvesSignedEraseSystem tetraDesign
        (fun first second third => -(tripleParity tetraDesign first second third)) := by
  intro hflip
  have hzero := (solvesSignedEraseSystem_neg_iff tetraDesign (tripleParity tetraDesign)
    (solvesSignedEraseSystem_tripleParity tetraDesign)).1 hflip 0 1 (by decide)
  rw [tetraDesign_atomPairing_zeroOne, atomShare_tetraDesign, atomShare_tetraDesign] at hzero
  norm_num at hzero

/-- From three labels up, pairwise share sums equal to one force every share to
`1/2`.  Design-free: a statement about a function on `Fin size`. -/
theorem forall_eq_half_of_forall_pair_add_eq_one {size : ℕ} (hsize : 3 ≤ size)
    (share : Fin size → ℝ)
    (hpair : ∀ first second : Fin size, first ≠ second → share first + share second = 1) :
    ∀ index : Fin size, share index = 1 / 2 := by
  intro index
  have hcard : 1 < (Finset.univ.erase index).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ index), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨other, hother, another, hanother, hne⟩ := Finset.one_lt_card.mp hcard
  have hindexOther : index ≠ other := ((Finset.mem_erase.1 hother).1).symm
  have hindexAnother : index ≠ another := ((Finset.mem_erase.1 hanother).1).symm
  have hone := hpair index other hindexOther
  have htwo := hpair index another hindexAnother
  have hthree := hpair other another hne
  linarith

/-- **THE RANK-STRUCTURAL COROLLARY.**  All shares `1/2` forces `size = 2 * rank`.
The shares sum to the rank (`Gtz.sum_atomShare_eq_rank`), so the count is pinned.

This is why the self-dual cells are the hard ones: the `tau_all` degeneracy
component EXISTS at `(6,3)`, where `6 = 2 * 3`, and CANNOT exist at the rank-four
Veronese top `(10,4)`, where `10 ≠ 8`. -/
theorem size_eq_two_mul_rank_of_forall_atomShare_eq_half {m k : ℕ} (D : WeightedDesign m k)
    (hhalf : ∀ index : Fin m, atomShare D index = 1 / 2) : m = 2 * k := by
  have hsum := sum_atomShare_eq_rank D
  rw [Finset.sum_congr rfl (fun index _ => hhalf index), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hreal : (m : ℝ) = 2 * (k : ℝ) := by linarith
  exact_mod_cast hreal

/-- The share of the third atom of the shipped `Gtz.orthoSplitDesign`: weight `2/5`
against leverage `2`. -/
theorem atomShare_orthoSplitDesign_two : atomShare orthoSplitDesign 2 = 4 / 5 := by
  rw [atomShare, orthoSplitDesign_leverage 2]
  simp [orthoSplitDesign_weight]
  norm_num

/-- **THE CONVERSE IS FALSE.**  `size = 2 * rank` does NOT force the shares to
`1/2`.  Witness: the shipped `Gtz.orthoSplitDesign`, a `WeightedDesign 6 3` with
`6 = 2 * 3` whose shares are `1/2, 1/2, 4/5, 1/5, 1/2, 1/2`.

So the `tau_all` locus `{all shares 1/2}` is a PROPER subset of the `size = 2 * rank`
cells, and only the forward implication
`Gtz.size_eq_two_mul_rank_of_forall_atomShare_eq_half` is available. -/
theorem not_forall_atomShare_eq_half_of_size_eq_two_mul_rank :
    ¬ ∀ (m k : ℕ) (D : WeightedDesign m k), m = 2 * k →
        ∀ index : Fin m, atomShare D index = 1 / 2 := by
  intro hall
  have hhalf := hall 6 3 orthoSplitDesign (by norm_num) 2
  rw [atomShare_orthoSplitDesign_two] at hhalf
  norm_num at hhalf

/-! ## 4. The census of flip patterns

A flip pattern is a two-graph, and the tree already encodes two-graphs on six labels
as a `link : Nat` below `1024`, gauge-fixed at atom `0`, with `Gtz.sectorIncoherent`
decoding an arbitrary triple and `Gtz.sectorIncoherent_linkWordOf` bridging to a
design.  Everything below is that shipped encoding; nothing re-derives it. -/

/-- The four triples of an edge's star that the flip pattern touches. -/
def flipStar (link : Nat) (edgeFirst edgeSecond : Fin 6) : Finset (Fin 6) :=
  ((Finset.univ.erase edgeFirst).erase edgeSecond).filter
    (fun other => sectorIncoherent link edgeFirst edgeSecond other = true)

/-- Does some edge star meet the flip support in EXACTLY one triple?  Such a link
dies at every design with nonvanishing pairings, by the size-one kill. -/
def hasSingletonStar (link : Nat) : Bool :=
  decide (∃ edgeFirst : Fin 6, ∃ edgeSecond : Fin 6,
    edgeFirst ≠ edgeSecond ∧ (flipStar link edgeFirst edgeSecond).card = 1)

/-- The triples the flip pattern touches, as unordered triples. -/
def flipSupport (link : Nat) : Finset (Fin 6 × Fin 6 × Fin 6) :=
  Finset.univ.filter (fun triple => triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 ∧
    sectorIncoherent link triple.1 triple.2.1 triple.2.2 = true)

/-- The edges on which the flip pattern imposes an exact relation. -/
def liveEdges (link : Nat) : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun edge => edge.1 < edge.2 ∧ (flipStar link edge.1 edge.2).Nonempty)

/-- **THE KILL CENSUS.**  Every nontrivial two-graph that escapes the size-one kill
flips at least EIGHT of the twenty triples AND imposes an exact relation on at least
TWELVE of the fifteen edges.

Stated survivor-conditionally on purpose.  The disjunctive phrasing "killed, or at
least eight flips" is nearly vacuous -- `825` of the `900` killed links also carry
eight or more flipped triples -- so it would report a property of the killed set
rather than of the survivors. -/
theorem killCensus : ∀ link < 1024, (flipSupport link).Nonempty →
    hasSingletonStar link = false →
    8 ≤ (flipSupport link).card ∧ 12 ≤ (liveEdges link).card := by
  decide +kernel

/-- The `123` links the size-one kill does not reach. -/
def IsSurvivorLink (link : Nat) : Bool :=
  decide (flipSupport link).Nonempty && !hasSingletonStar link

theorem card_survivorLinks : sectorCount IsSurvivorLink = 123 := by decide +kernel

theorem card_killedLinks :
    sectorCount (fun link => decide (flipSupport link).Nonempty && hasSingletonStar link)
      = 900 := by decide +kernel

/-- Sharpness of the support bound: a survivor attains eight. -/
theorem killCensus_sharp_support :
    ∃ link < 1024, IsSurvivorLink link = true ∧ (flipSupport link).card = 8 := by
  decide +kernel

/-- Sharpness of the edge bound: a survivor attains twelve. -/
theorem killCensus_sharp_liveEdges :
    ∃ link < 1024, IsSurvivorLink link = true ∧ (liveEdges link).card = 12 := by
  decide +kernel

/-! ## 5. Rigidity off the survivor locus

A phantom is the design's parity multiplied by a flip pattern.  Its disagreement set
at an edge IS that edge's flip star, so the size-one kill applies verbatim. -/

/-- The design's parity, flipped by the two-graph `link`. -/
noncomputable def flippedParity (D : WeightedDesign 6 3) (link : Nat)
    (first second third : Fin 6) : ℝ :=
  tripleParity D first second third
    * (if sectorIncoherent link first second third then -1 else 1)

theorem flippedParity_eq_or_eq_neg (D : WeightedDesign 6 3) (link : Nat)
    (first second third : Fin 6) :
    flippedParity D link first second third = tripleParity D first second third
      ∨ flippedParity D link first second third = -tripleParity D first second third := by
  rw [flippedParity]
  split
  · exact Or.inr (by ring)
  · exact Or.inl (by ring)

theorem isParityFlip_flippedParity (D : WeightedDesign 6 3) (link : Nat) :
    IsParityFlip D (flippedParity D link) :=
  fun first second third => flippedParity_eq_or_eq_neg D link first second third

/-- **THE DISAGREEMENT SET IS THE FLIP STAR.**  The bridge between the real-valued
system and the Boolean census: the atoms at which a phantom differs from the design
along an edge are exactly the flipped triples of that edge's star. -/
theorem disagreement_flippedParity (D : WeightedDesign 6 3) (link : Nat)
    (edgeFirst edgeSecond : Fin 6) :
    ((Finset.univ.erase edgeFirst).erase edgeSecond).filter
        (fun other => flippedParity D link edgeFirst edgeSecond other
          ≠ tripleParity D edgeFirst edgeSecond other)
      = flipStar link edgeFirst edgeSecond := by
  rw [flipStar]
  refine Finset.filter_congr ?_
  intro other _
  rw [flippedParity]
  constructor
  · intro hne
    by_contra hfalse
    rw [Bool.not_eq_true] at hfalse
    exact hne (by rw [hfalse]; norm_num)
  · intro htrue hequal
    rw [htrue, if_pos rfl] at hequal
    have hzero : tripleParity D edgeFirst edgeSecond other = 0 := by linarith
    exact tripleParity_ne_zero D edgeFirst edgeSecond other hzero

/-- **THE KILL AT A DESIGN.**  A flip pattern whose star meets one edge exactly once
cannot solve the signed erase system, at any design with nonvanishing pairings. -/
theorem not_solvesSignedEraseSystem_flippedParity_of_flipStar_card_eq_one
    (D : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing D first second ≠ 0)
    {link : Nat} {edgeFirst edgeSecond witness : Fin 6} (hedge : edgeFirst ≠ edgeSecond)
    (hsingle : flipStar link edgeFirst edgeSecond = {witness})
    (hsolve : SolvesSignedEraseSystem D (flippedParity D link)) : False := by
  have hmem : witness ∈ flipStar link edgeFirst edgeSecond := by
    rw [hsingle]; exact Finset.mem_singleton_self witness
  rw [flipStar, Finset.mem_filter, Finset.mem_erase, Finset.mem_erase] at hmem
  obtain ⟨⟨hwitnessSecond, hwitnessFirst, _⟩, _⟩ := hmem
  have hcoeff : 0 < D.weight witness * tripleRadius D edgeFirst edgeSecond witness :=
    mul_pos (D.weight_pos witness) (tripleRadius_pos D (hnonzero _ _ hedge)
      (hnonzero _ _ (Ne.symm hwitnessFirst)) (hnonzero _ _ (Ne.symm hwitnessSecond)))
  have hreshape : ∀ sign : Fin 6 → Fin 6 → Fin 6 → ℝ,
      ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
          D.weight other * (sign edgeFirst edgeSecond other
            * tripleRadius D edgeFirst edgeSecond other)
        = ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
            (D.weight other * tripleRadius D edgeFirst edgeSecond other)
              * sign edgeFirst edgeSecond other :=
    fun sign => Finset.sum_congr rfl (fun other _ => by ring)
  have hfirst := solvesSignedEraseSystem_tripleParity D edgeFirst edgeSecond hedge
  have hsecond := hsolve edgeFirst edgeSecond hedge
  rw [hreshape] at hfirst hsecond
  refine disagreement_ne_singleton_of_pos ((Finset.univ.erase edgeFirst).erase edgeSecond)
    (fun other => D.weight other * tripleRadius D edgeFirst edgeSecond other)
    (fun other => tripleParity D edgeFirst edgeSecond other)
    (fun other => flippedParity D link edgeFirst edgeSecond other)
    (atomPairing D edgeFirst edgeSecond ^ 2
      * (1 - atomShare D edgeFirst - atomShare D edgeSecond))
    witness (fun other _ => flippedParity_eq_or_eq_neg D link edgeFirst edgeSecond other)
    hfirst hsecond hcoeff
    (tripleParity_eq_one_or_neg_one D edgeFirst edgeSecond witness) ?_
  rw [← hsingle]
  exact disagreement_flippedParity D link edgeFirst edgeSecond

/-- **RIGIDITY OFF THE SURVIVOR LOCUS.**  At a design with nonvanishing pairings,
every phantom's flip pattern is one of the `123` survivors -- so it flips at least
eight triples and imposes exact relations on at least twelve of the fifteen edges.

A phantom is therefore never cheap: it costs a dozen simultaneous exact cancellations
in the field-blind data, which is what makes the degeneracy locus thin. -/
theorem flipSupport_card_ge_of_solvesSignedEraseSystem (D : WeightedDesign 6 3)
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomPairing D first second ≠ 0)
    {link : Nat} (hlink : link < 1024) (hnontrivial : (flipSupport link).Nonempty)
    (hsolve : SolvesSignedEraseSystem D (flippedParity D link)) :
    8 ≤ (flipSupport link).card ∧ 12 ≤ (liveEdges link).card := by
  refine killCensus link hlink hnontrivial ?_
  by_contra hsingleton
  rw [Bool.not_eq_false, hasSingletonStar, decide_eq_true_eq] at hsingleton
  obtain ⟨edgeFirst, edgeSecond, hedge, hcard⟩ := hsingleton
  obtain ⟨witness, hwitness⟩ := Finset.card_eq_one.mp hcard
  exact not_solvesSignedEraseSystem_flippedParity_of_flipStar_card_eq_one D hnonzero hedge
    hwitness hsolve

/-! ## 6. The icosahedron: global rigidity is false

`Gtz.atomShare_icosaDesign` puts every icosahedral share at `1/2`, so every erase
right-hand side vanishes and the global flip solves.  The failure is not an artefact
of a degenerate datum: the icosahedral design is the calibrated hard case of the
cell, all of its pairings are nonzero, and its two-graph is the unique nontrivial
regular two-graph on six points. -/

/-- The global flip as a link: `1023` sets all ten gauge bits, and its sector decode
is `true` at every nondegenerate triple. -/
theorem sectorIncoherent_globalFlipLink {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    sectorIncoherent 1023 first second third = true := by
  revert hfirstSecond hfirstThird hsecondThird
  revert first second third
  decide

/-- The `tau_all` pattern SURVIVES the size-one kill -- which is precisely why the
icosahedral failure below is possible.  It is the unique survivor flipping all
twenty triples, and it constrains all fifteen edges. -/
theorem isSurvivorLink_globalFlipLink : IsSurvivorLink 1023 = true := by decide +kernel

theorem flipSupport_card_globalFlipLink : (flipSupport 1023).card = 20 := by decide +kernel

theorem liveEdges_card_globalFlipLink : (liveEdges 1023).card = 15 := by decide +kernel

/-- **THE GLOBAL FLIP SOLVES AT THE ICOSAHEDRON.** -/
theorem solvesSignedEraseSystem_neg_tripleParity_icosaDesign :
    SolvesSignedEraseSystem icosaDesign
      (fun first second third => -(tripleParity icosaDesign first second third)) := by
  refine (solvesSignedEraseSystem_neg_iff icosaDesign (tripleParity icosaDesign)
    (solvesSignedEraseSystem_tripleParity icosaDesign)).2 ?_
  intro edgeFirst edgeSecond _
  rw [atomShare_icosaDesign, atomShare_icosaDesign]
  ring

/-- **COCYCLE RIGIDITY IS FALSE AS A GLOBAL STATEMENT.**  The icosahedral design
admits a second solution of its signed erase system, namely the global flip.  So no
argument may assume that the field-blind datum determines the two-graph. -/
theorem not_hasRigidSignedEraseSystem_icosaDesign :
    ¬ HasRigidSignedEraseSystem icosaDesign := by
  intro hrigid
  have hpin := hrigid (fun first second third => -(tripleParity icosaDesign first second third))
    (fun first second third => Or.inr rfl)
    solvesSignedEraseSystem_neg_tripleParity_icosaDesign 0 1 2 (by decide) (by decide) (by decide)
  have hzero : tripleParity icosaDesign 0 1 2 = 0 := by linarith
  exact tripleParity_ne_zero icosaDesign 0 1 2 hzero

/-! ### The icosahedral two-graph, computed

`Gtz.icosahedralLink_mem_residualSectors` records that link `220` is the icosahedral
class as an ATTRIBUTION rather than a theorem.  The overlap-sign table closes that
gap: every off-diagonal icosahedral overlap is `±icosaRadius`, and the sign pattern
is the table below. -/

/-- The sign of every off-diagonal icosahedral overlap. -/
def icosaOverlapSign : Fin 6 → Fin 6 → ℝ :=
  ![![0, 1, 1, -1, 1, 1],
    ![1, 0, 1, -1, -1, -1],
    ![1, 1, 0, 1, 1, -1],
    ![-1, -1, 1, 0, 1, -1],
    ![1, -1, 1, 1, 0, 1],
    ![1, -1, -1, -1, 1, 0]]

set_option maxHeartbeats 1000000 in
/-- **THE SIGNED OVERLAP TABLE.**  Refines the shipped `Gtz.icosaAtom_dot_sq_of_ne`,
which sees only the square, to the sign.  Each of the thirty ordered pairs closes by
one of two certificates: the overlap is `icosaLong ^ 2 - icosaShort ^ 2` or
`± icosaShort * icosaLong`, and both equal `± icosaRadius`. -/
theorem icosaAtom_dot_of_ne {first second : Fin 6} (hne : first ≠ second) :
    icosaAtom first ⬝ᵥ icosaAtom second = icosaOverlapSign first second * icosaRadius := by
  have hshort := icosaShort_sq
  have hlong := icosaLong_sq
  have hmul := icosaShort_mul_icosaLong
  fin_cases first <;> fin_cases second <;>
    simp [icosaAtom, icosaOverlapSign, dotProduct, Fin.sum_univ_three] at hne ⊢ <;>
    first
      | linear_combination hmul
      | linear_combination -hmul
      | linear_combination hshort - hlong
      | linear_combination hlong - hshort

theorem atomPairing_icosaDesign_of_ne {first second : Fin 6} (hne : first ≠ second) :
    atomPairing icosaDesign first second = icosaOverlapSign first second * icosaRadius :=
  icosaAtom_dot_of_ne hne

theorem icosaOverlapSign_eq_one_or_neg_one {first second : Fin 6} (hne : first ≠ second) :
    icosaOverlapSign first second = 1 ∨ icosaOverlapSign first second = -1 := by
  fin_cases first <;> fin_cases second <;> simp [icosaOverlapSign] at hne ⊢

theorem edgeSign_icosaDesign {first second : Fin 6} (hne : first ≠ second) :
    edgeSign icosaDesign first second = icosaOverlapSign first second := by
  rw [edgeSign, atomPairing_icosaDesign_of_ne hne]
  rcases icosaOverlapSign_eq_one_or_neg_one hne with hplus | hminus
  · rw [hplus, if_pos (by nlinarith [icosaRadius_pos])]
  · rw [hminus, if_neg (by nlinarith [icosaRadius_pos])]

theorem tripleParity_icosaDesign {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleParity icosaDesign first second third
      = icosaOverlapSign first second * icosaOverlapSign first third
        * icosaOverlapSign second third := by
  rw [tripleParity, edgeSign_icosaDesign hfirstSecond, edgeSign_icosaDesign hfirstThird,
    edgeSign_icosaDesign hsecondThird]

/-- **THE ICOSAHEDRAL LINK IS `220`.**  The identification that
`Gtz.icosahedralLink_mem_residualSectors` states in prose as "an ATTRIBUTION, not
proved here", now a theorem: the two-graph of `Gtz.icosaDesign` is exactly the link
whose survival that theorem certifies. -/
theorem linkWordOf_icosaDesign : linkWordOf icosaDesign = 220 := by
  have hbit12 : decide (tripleParity icosaDesign 0 1 2 = -1) = false := by
    rw [show tripleParity icosaDesign 0 1 2 = 1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_false (by norm_num)
  have hbit13 : decide (tripleParity icosaDesign 0 1 3 = -1) = false := by
    rw [show tripleParity icosaDesign 0 1 3 = 1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_false (by norm_num)
  have hbit14 : decide (tripleParity icosaDesign 0 1 4 = -1) = true := by
    rw [show tripleParity icosaDesign 0 1 4 = -1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_true rfl
  have hbit15 : decide (tripleParity icosaDesign 0 1 5 = -1) = true := by
    rw [show tripleParity icosaDesign 0 1 5 = -1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_true rfl
  have hbit23 : decide (tripleParity icosaDesign 0 2 3 = -1) = true := by
    rw [show tripleParity icosaDesign 0 2 3 = -1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_true rfl
  have hbit24 : decide (tripleParity icosaDesign 0 2 4 = -1) = false := by
    rw [show tripleParity icosaDesign 0 2 4 = 1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_false (by norm_num)
  have hbit25 : decide (tripleParity icosaDesign 0 2 5 = -1) = true := by
    rw [show tripleParity icosaDesign 0 2 5 = -1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_true rfl
  have hbit34 : decide (tripleParity icosaDesign 0 3 4 = -1) = true := by
    rw [show tripleParity icosaDesign 0 3 4 = -1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_true rfl
  have hbit35 : decide (tripleParity icosaDesign 0 3 5 = -1) = false := by
    rw [show tripleParity icosaDesign 0 3 5 = 1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_false (by norm_num)
  have hbit45 : decide (tripleParity icosaDesign 0 4 5 = -1) = false := by
    rw [show tripleParity icosaDesign 0 4 5 = 1 from by
      rw [tripleParity_icosaDesign (by decide) (by decide) (by decide)]
      simp [icosaOverlapSign]]
    exact decide_eq_false (by norm_num)
  rw [linkWordOf, hbit12, hbit13, hbit14, hbit15, hbit23, hbit24, hbit25, hbit34, hbit35,
    hbit45]
  rfl

/-- **THE ICOSAHEDRAL TWO-GRAPH IS SELF-COMPLEMENTARY.**  Relabelling by
`0, 1, 4, 5, 3, 2` sends every parity to its negative.  So the phantom of
`Gtz.solvesSignedEraseSystem_neg_tripleParity_icosaDesign` is not a mere sign
pattern: it is the two-graph of an ISOMORPHIC COPY of the icosahedral design, which
is why the second solution is realised rather than formal.

The relabelling fixes atom `0`, so it acts on the gauge-fixed encoding directly. -/
theorem sectorIncoherent_icosahedralLink_relabelled :
    ∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
      sectorIncoherent 220 (![0, 1, 4, 5, 3, 2] first) (![0, 1, 4, 5, 3, 2] second)
          (![0, 1, 4, 5, 3, 2] third)
        = ! sectorIncoherent 220 first second third := by
  decide

/-! ### The phantom, realised

The shipped `Gtz.relabelDesign` permutes atoms and weights together, so a relabelling
of a design IS a design -- Parseval comes for free.  Applying the complementing
relabelling above to the icosahedron therefore produces a SECOND REAL DESIGN over the
SAME field-blind datum whose two-graph is the global flip of the first's.

That upgrades the failure from a formal sign pattern to a genuine second solution
realised by an actual weighted design, which is what makes the seam load-bearing. -/

/-- The relabelling that complements the icosahedral two-graph. -/
def icosaComplementPerm : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 3, 2]
  invFun := ![0, 1, 5, 4, 2, 3]
  left_inv := by decide
  right_inv := by decide

theorem icosaComplementPerm_apply (index : Fin 6) :
    icosaComplementPerm index = ![0, 1, 4, 5, 3, 2] index := rfl

/-- **THE SECOND ICOSAHEDRAL DESIGN.** -/
noncomputable def icosaComplementDesign : WeightedDesign 6 3 :=
  relabelDesign icosaDesign icosaComplementPerm

/-- The sector decode of link `220` IS the icosahedral parity, by
`Gtz.linkWordOf_icosaDesign` and the shipped bridge. -/
theorem sectorIncoherent_eq_decide_tripleParity_icosaDesign (first second third : Fin 6) :
    sectorIncoherent 220 first second third
      = decide (tripleParity icosaDesign first second third = -1) := by
  rw [← linkWordOf_icosaDesign]
  exact sectorIncoherent_linkWordOf icosaDesign first second third

/-- **THE SECOND DESIGN CARRIES THE FLIPPED TWO-GRAPH.**  Every nondegenerate parity
of `Gtz.icosaComplementDesign` is the negative of the corresponding icosahedral one. -/
theorem tripleParity_icosaComplementDesign {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tripleParity icosaComplementDesign first second third
      = -tripleParity icosaDesign first second third := by
  have hboolNeNot : ∀ flag : Bool, flag ≠ !flag := by decide
  have hrel := sectorIncoherent_icosahedralLink_relabelled first second third
    hfirstSecond hfirstThird hsecondThird
  rw [sectorIncoherent_eq_decide_tripleParity_icosaDesign,
    sectorIncoherent_eq_decide_tripleParity_icosaDesign] at hrel
  rw [icosaComplementDesign, tripleParity_relabelDesign, icosaComplementPerm_apply,
    icosaComplementPerm_apply, icosaComplementPerm_apply]
  rcases tripleParity_eq_one_or_neg_one icosaDesign
      (![0, 1, 4, 5, 3, 2] first) (![0, 1, 4, 5, 3, 2] second) (![0, 1, 4, 5, 3, 2] third)
      with hleft | hleft <;>
    rcases tripleParity_eq_one_or_neg_one icosaDesign first second third with hright | hright <;>
    rw [hleft, hright] at hrel <;> rw [hleft, hright] <;>
    first
      | exact absurd hrel (hboolNeNot _)
      | norm_num

/-- Same weights as the icosahedron. -/
theorem weight_icosaComplementDesign (atomIndex : Fin 6) :
    icosaComplementDesign.weight atomIndex = 1 / 6 := rfl

/-- Same leverages as the icosahedron. -/
theorem leverageOf_icosaComplementDesign (atomIndex : Fin 6) :
    leverageOf (icosaComplementDesign.atom atomIndex) = 3 := by
  rw [icosaComplementDesign, leverageOf_relabelDesign]
  exact icosaAtom_leverageOf _

/-- Same squared pairings as the icosahedron: the second design is equiangular at the
same angle, so the two are indistinguishable by the field-blind datum. -/
theorem atomPairing_sq_icosaComplementDesign {first second : Fin 6} (hne : first ≠ second) :
    atomPairing icosaComplementDesign first second ^ 2 = 9 / 5 := by
  rw [icosaComplementDesign, atomPairing_relabelDesign]
  exact icosaDesign_atomPairing_sq_of_ne (fun heq => hne (icosaComplementPerm.injective heq))

/-- **THE PHANTOM IS A REAL DESIGN.**  The two-graph of `Gtz.icosaComplementDesign`
solves the signed erase system OF `Gtz.icosaDesign`.

Together with `Gtz.weight_icosaComplementDesign`,
`Gtz.leverageOf_icosaComplementDesign` and
`Gtz.atomPairing_sq_icosaComplementDesign` -- same weights, same leverages, same
squared pairings -- this says the two designs share every field-blind invariant the
erase system can see, yet carry OPPOSITE two-graphs.  So no argument may recover the
two-graph from the moduli, and `Gtz.not_hasRigidSignedEraseSystem_icosaDesign` is
witnessed by an actual weighted design rather than by a bare sign pattern. -/
theorem solvesSignedEraseSystem_tripleParity_icosaComplementDesign :
    SolvesSignedEraseSystem icosaDesign (tripleParity icosaComplementDesign) := by
  intro edgeFirst edgeSecond hedge
  have hneg := solvesSignedEraseSystem_neg_tripleParity_icosaDesign edgeFirst edgeSecond hedge
  rw [← hneg]
  refine Finset.sum_congr rfl ?_
  intro other hother
  rw [Finset.mem_erase, Finset.mem_erase] at hother
  obtain ⟨hotherSecond, hotherFirst, _⟩ := hother
  rw [tripleParity_icosaComplementDesign hedge (Ne.symm hotherFirst) (Ne.symm hotherSecond)]

end Gtz

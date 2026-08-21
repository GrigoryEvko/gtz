/-
# The complement of a pair, its determinant, and the volume it must carry

Parseval says the weighted atoms of a design total the identity.  Split that sum
at a PAIR and the two halves are a rank-two correction of the identity on one
side and the whole rest of the design on the other.  This module proves the
determinant of that correction in closed form, expands the other side by
Cauchy-Binet at sizes two, three and four, and reads eleven consequences off the
resulting identities — at `(4,3)`, at `(5,3)` and at `(6,3)`.

## The three determinant laws

All three are `Matrix.det_fin_three` followed by `ring`, and all three are new.

  **`Gtz.det_one_sub_pairAtomCombo`**
  `det(1 − α g gᵀ − β h hᵀ) = 1 − α·l_g − β·l_h + α·β·w_gh` ,

with `w_gh = l_g·l_h − ⟨g,h⟩²` the squared area of the pair.

  **`Gtz.det_tripleAtomCombo`**
  `det(α g gᵀ + β h hᵀ + γ e eᵀ) = α·β·γ·[g,h,e]²` ,

  **`Gtz.det_fourAtomCombo`**
  `det(∑ of four scaled atoms) = ∑ over the four triples of (∏ scale)·[·]²` .

The last two are Cauchy-Binet written out, and they are what turns a complement
into a VOLUME.

## The complement laws

Parseval splits at a pair (`Gtz.weightedComplement_pair_eq`), so at every size

  **`Gtz.det_weightedComplement_pair`:**
  `det(∑_{c ∉ {p,q}} t_c g_c g_cᵀ) = 1 − t_p·l_p − t_q·l_q + t_p·t_q·w_pq` .

At `(4,3)` the complement of a pair is a PAIR, whose determinant vanishes, so the
identity becomes an equation (`Gtz.pair_share_sum_eq_of_size_four`).  At `(5,3)`
the complement is a TRIPLE and the identity reads

  **`Gtz.complement_triple_volume_law`:**
  `t_c·t_d·t_e·[g_c,g_d,g_e]² = 1 − t_p·l_p − t_q·l_q + t_p·t_q·w_pq` .

At `(6,3)` the complement is a FOUR-SET and the identity reads

  **`Gtz.complement_fourSet_volume_law`:** the four complementary triples'
  weighted squared volumes total `1 − t_p·l_p − t_q·l_q + t_p·t_q·w_pq` .

So at every one of the three live sizes a pair's two shares and its squared area
determine a determinant of the rest of the design exactly.

## What comes out

* **The wedge floor** (`Gtz.share_add_share_le_one_add_weight_mul_crossNormSq`).
  The complement is positive semidefinite, so

  `t_p·l_p + t_q·l_q − 1 ≤ t_p·t_q·w_pq`   at EVERY `(m,3)` design.

* **A PARALLEL PAIR IS LIGHT** (`Gtz.share_add_share_le_one_of_crossNormSq_eq_zero`).
  A parallel pair has `w = 0`, so its two shares total at most one.  This is the
  first bound the campaign has that separates a parallel pair by its WEIGHTS
  rather than by its geometry, and it localises the hinge's target: at a `(6,3)`
  tie the parallel pair the hinge hunts must lie among the pairs whose shares
  total at most one.  At `(5,3)` the sharper
  `Gtz.parallel_pair_share_deficit_eq_complement_volume` says the deficit
  `1 − t_p·l_p − t_q·l_q` IS the complementary triple's weighted squared volume,
  so a parallel pair with shares totalling exactly one has a coplanar complement.

* **The inadmissible cap** (`Gtz.inadmissible_share_cap`).  Feeding
  `w_pq ≤ l_p + l_q − 1` into the wedge floor eliminates the squared area:

  `t_p·l_p·(1 − t_q) + t_q·l_q·(1 − t_p) ≤ 1 − t_p·t_q` .

* **The wedge row law** (`Gtz.sum_weight_mul_crossNormSq`):
  **`∑_b t_b·w_ab = 2·l_a`** at every `(m,3)` design.  It is not a rescaling of
  the landed pair-minor budget: that budget is quadratic in the weights and
  totals a constant, this one is linear and totals a leverage.

* **THE HEAVINESS HYPOTHESIS IS LOAD-BEARING**
  (`Gtz.exists_inadmissible_nonparallel_of_leverage_le_one`).  Question 7.5(b) of
  the survey asks whether a pair with `q_ab ≤ 0` in a boundary system is
  parallel.  If ONE atom has leverage at most one — and nonzero — the answer is
  NO at every `(m,3)` design, tie or not: the row law names a partner with
  positive squared area, and against a heavy partner a light atom is
  automatically inadmissible.  The landed
  `Gtz.leverage_one_le_of_isTie_fiveThree` gives `1 ≤ l_c` at a `(5,3)` tie for
  free; this theorem shows the STRICT form `1 < l_c` is exactly what the question
  needs and exactly what is not free.

* **The rescaled complement rung** (`Gtz.one_sub_weight_cap_le_complement_share`).
  Running the weight-rescaling trick on the COMPLEMENT rather than the subset: at
  a design with no strict `k`-subset dominator, for every `k`-subset `T` and every
  cap `τ` on its members' weights,

  **`1 − τ ≤ ∑_{e ∉ T} t_e·l_e`** ,   equivalently   `∑_{c∈T} t_c·l_c ≤ k − 1 + τ` .

  SHARP.  Split one atom of the regular tetrahedron into two parallel copies of
  half weight: the resulting `(5,3)` tie has `t = (1/8, 1/8, 1/4, 1/4, 1/4)`,
  `l ≡ 3`, `t·l = (3/8, 3/8, 3/4, 3/4, 3/4)`, and at the triple of unsplit atoms
  `τ = 1/4` and both sides read `3/4`.  At `(6,3)` the same law caps every
  triple's share total by `2 + τ`, which is a new necessary condition on a
  `(6,3)` tie (`Gtz.triple_share_cap_of_no_strict_dominator`).

* **The rank-zero exclusion** (`Gtz.subsetSum_ne_one_of_corank_two`).  At
  `m = k + 2` no `k`-subset has `S_C = 1`, because the complement pair is
  singular while the members' complement is bounded below by `(1 − τ)·1`.  So the
  gap of a weak dominator of a `(5,3)` tie has rank one or two, never zero, and
  the survey's rank split of the tie is exhaustive.

* **The complement case, priced** (`Gtz.inadmissible_complement_volume_bound`).
  Any lower bound on the complement triple's determinant caps the inadmissible
  pair's two shares.

* **THE PRICE OF QUESTION 7.5(b)** (`Gtz.pairGapMinor_pos_inside_dominator_of_q75b`).
  A pair inside a weak dominator is admissible non-strictly
  (`Gtz.pairGapMinor_nonneg_of_dominates_triple`, proved here from the Gram
  criterion rather than assumed).  If it were inadmissible it would have
  `q = 0`, hence squared area `l_a + l_b − 1 > 1 > 0`, hence NOT parallel — so
  Question 7.5(b) would fail on it.  Therefore the question, at a design whose
  atoms are strictly heavy, IMPLIES that no weak dominator carries a vanishing
  pair minor: every weak dominator has gap rank two with no vanishing reading.
  That is the standing hypothesis of the survey's rank-two section, here shown to
  be a consequence of the question rather than an aid to it.

## What this does NOT do

It does not prove Question 7.5(b) at `(5,3)`, and it does not close the hinge.
`Gtz.pair_dominator_trichotomy` records the three positions an inadmissible pair
can take relative to a weak dominator of a `(5,3)` tie; this module prices the
inside case and supplies the complement case with an exact volume law, and the
mixed case is untouched.

[MEASURED, exact rational arithmetic on the named fixture FIRST.  The `(5,3)`
diamond `K4 − e` with conductances `(2,3,3,3,3)` and uniform weight `1/5` has
leverages `(2, 13/4, 13/4, 13/4, 13/4)`, weighted shares `(2/5, 13/20, 13/20,
13/20, 13/20)` totalling three, eight weak dominators, no strict one, all ten
pair minors positive (minimum `3/4`) and all ten squared areas positive (minimum
`5`).  This reproduces the survey's example on the nose, and it makes Question
7.5(b) VACUOUS at the diamond.  The split tetrahedron makes it non-vacuous: its
parallel pair has `q = 1 − 2·3 = −5 < 0` and squared area zero.

MEASURED, the search for a counterexample.  Minimise the pair minor `q_01` over
`(5,3)` designs subject to no triple dominating strictly, all leverages at least
`1.02`, all weights at least `τ`, and the normalised squared area
`w_01/(l_0+l_1−1)` at least `0.15`.  Nelder-Mead from random starts on the
Stiefel-times-simplex chart, `64` threads, `192` to `384` starts, three descent
passes per start.  Results: `τ = 0.12` gives `min q_01 = +0.2887` at tie residual
`5.4e-6`; `τ = 0.05` gives `+0.0901` at tie residual `1.6e-9`; `τ = 0.01` gives
`+0.0218` at tie residual `5.2e-8`.  The minimum never reaches zero and shrinks
about linearly in the weight floor, `min q_01 ≈ 2·τ`.  Dually, minimising the tie
residual subject to `q_01 ≤ 0` and a squared-area floor gives residual `6.3e-3`
at `τ = 0.10`, `3.5e-3` at `τ = 0.05`, `1.5e-3` at `τ = 0.02` and `3.9e-4` at
`τ = 0.01`.  With NO weight floor the search reaches tie residual `1.4e-7`
carrying `q_01 = −0.12` and squared area `2.49`, at weights
`(0.189, 0.665, 4e-7, 0.147, 3e-7)`.  So the counterexample exists only in the
limit where a weight vanishes: Question 7.5(b) at `(5,3)` looks TRUE under strict
heaviness, and any certificate for it carries a margin proportional to the
smallest weight.  That is the campaign's universal obstruction, measured here
from the counterexample side rather than from the certificate side.]
-/
import Gtz.Wave.InadmissiblePairSeparation
import Gtz.Design.DirectionBudget
import Gtz.Design.StressFreeNormalizer
import Gtz.Wave.CrossFrameRowLaw
import Gtz.Design.PrimitiveTightClassification
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. Reading a design against a probe

Every statement below is one quadratic form evaluated at one probe, so this
section carries the module. -/

/-- One scaled atom, read at a probe. -/
theorem scaledAtom_reading (D : WeightedDesign m k) (c : Fin m) (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((D.weight c • atomMatrix (D.atom c)) *ᵥ probe)
      = D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  have hvec : (D.weight c • atomMatrix (D.atom c)) *ᵥ probe
      = (D.weight c * (D.atom c ⬝ᵥ probe)) • D.atom c := by
    funext coord
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hvec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-! The Parseval reading `Gtz.sum_weight_mul_sq_reading` and the gap symmetry
`Gtz.isHermitian_subsetSum_sub_one` are landed in `Gtz.Design.DirectionBudget`
and `Gtz.Design.StressFreeNormalizer` respectively, and are imported rather than
restated. -/

/-- A weighted subsum of atoms, read at a probe. -/
theorem dotProduct_weightedSubsum_mulVec (D : WeightedDesign m k) (C : Finset (Fin m))
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((∑ c ∈ C, D.weight c • atomMatrix (D.atom c)) *ᵥ probe)
      = ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  classical
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => scaledAtom_reading D c probe

/-- A weighted subsum of atoms is positive semidefinite. -/
theorem posSemidef_weightedSubsum (D : WeightedDesign m k) (C : Finset (Fin m)) :
    (∑ c ∈ C, D.weight c • atomMatrix (D.atom c)).PosSemidef := by
  classical
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero ?_
  intro c _
  exact (posSemidef_atomMatrix (D.atom c)).smul (D.weight_pos c).le

/-! ## 2. Three determinant laws

Each is `Matrix.det_fin_three` followed by `ring`, and each says that a sum of
rank-one matrices in rank three has a determinant with a name: zero at two
atoms, a weighted squared volume at three, and a sum of four of those at
four. -/

/-- **TWO ATOMS ARE SINGULAR IN RANK THREE.** -/
theorem det_pairAtomCombo (leftScale rightScale : ℝ) (leftVec rightVec : Fin 3 → ℝ) :
    (leftScale • atomMatrix leftVec + rightScale • atomMatrix rightVec).det = 0 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- **THREE ATOMS MAKE A VOLUME.**  Cauchy-Binet at the smallest interesting
shape: the determinant of three scaled atoms is the product of the scales times
the squared bracket. -/
theorem det_tripleAtomCombo (firstScale secondScale thirdScale : ℝ)
    (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    (firstScale • atomMatrix firstVec + secondScale • atomMatrix secondVec
        + thirdScale • atomMatrix thirdVec).det
      = firstScale * secondScale * thirdScale
        * tripleBracket firstVec secondVec thirdVec ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, tripleBracket, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **FOUR ATOMS MAKE FOUR VOLUMES.**  Cauchy-Binet at four atoms in rank three:
the determinant is the sum over the four triples of the scale product times the
squared bracket. -/
theorem det_fourAtomCombo (firstScale secondScale thirdScale fourthScale : ℝ)
    (firstVec secondVec thirdVec fourthVec : Fin 3 → ℝ) :
    (firstScale • atomMatrix firstVec + secondScale • atomMatrix secondVec
        + thirdScale • atomMatrix thirdVec + fourthScale • atomMatrix fourthVec).det
      = firstScale * secondScale * thirdScale
          * tripleBracket firstVec secondVec thirdVec ^ 2
        + firstScale * secondScale * fourthScale
          * tripleBracket firstVec secondVec fourthVec ^ 2
        + firstScale * thirdScale * fourthScale
          * tripleBracket firstVec thirdVec fourthVec ^ 2
        + secondScale * thirdScale * fourthScale
          * tripleBracket secondVec thirdVec fourthVec ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    atomMatrix, Matrix.vecMulVec_apply, tripleBracket, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **THE RANK-TWO UPDATE OF THE IDENTITY.**  Subtracting two scaled atoms from
the identity leaves a determinant in the pair's own vocabulary: the two leverages
and the squared area.  Nothing else survives. -/
theorem det_one_sub_pairAtomCombo (leftScale rightScale : ℝ) (leftVec rightVec : Fin 3 → ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - leftScale • atomMatrix leftVec
        - rightScale • atomMatrix rightVec).det
      = 1 - leftScale * leverageOf leftVec - rightScale * leverageOf rightVec
        + leftScale * rightScale * crossNormSq leftVec rightVec := by
  rw [crossNormSq_eq_leverage_mul_sub_sq]
  norm_num +decide [Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply, leverageOf, dotProduct,
    Fin.sum_univ_three]
  ring

/-! ## 3. Parseval splits at a pair

At every size the weighted atoms outside a pair total `1` less the pair's own
weighted atoms.  At `m = k + 2` the complement is a `k`-subset, which is why this
is the corank-two chart. -/

/-- The weighted atom sum of the two members of a pair. -/
noncomputable def weightedPairSum (D : WeightedDesign m k) (first second : Fin m) :
    Matrix (Fin k) (Fin k) ℝ :=
  D.weight first • atomMatrix (D.atom first) + D.weight second • atomMatrix (D.atom second)

/-- **PARSEVAL AT A PAIR.**  The complement of a pair carries exactly what the
pair does not. -/
theorem weightedComplement_pair_eq (D : WeightedDesign m k) {first second : Fin m}
    (hne : first ≠ second) :
    ∑ c ∈ ({first, second} : Finset (Fin m))ᶜ, D.weight c • atomMatrix (D.atom c)
      = 1 - weightedPairSum D first second := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({first, second} : Finset (Fin m))
    (fun c => D.weight c • atomMatrix (D.atom c))
  rw [D.isParseval, Finset.sum_pair hne] at hsplit
  rw [weightedPairSum]
  linear_combination (norm := module) hsplit

/-- **THE COMPLEMENT OF A PAIR, EVALUATED.**  At rank three the determinant of a
pair's complement is a polynomial in the pair alone. -/
theorem det_weightedComplement_pair (D : WeightedDesign m 3) {first second : Fin m}
    (hne : first ≠ second) :
    (∑ c ∈ ({first, second} : Finset (Fin m))ᶜ, D.weight c • atomMatrix (D.atom c)).det
      = 1 - D.weight first * leverageOf (D.atom first)
        - D.weight second * leverageOf (D.atom second)
        + D.weight first * D.weight second
          * crossNormSq (D.atom first) (D.atom second) := by
  rw [weightedComplement_pair_eq D hne, weightedPairSum, sub_add_eq_sub_sub,
    det_one_sub_pairAtomCombo]

/-! ## 4. The wedge floor and what it costs a pair -/

/-- **THE WEDGE FLOOR.**  The complement of a pair is positive semidefinite, so
its determinant is nonnegative, and the determinant law turns that into a floor
on the pair's weighted squared area.  No tie, no dominator, no size restriction:
this holds at every `(m,3)` design. -/
theorem share_add_share_le_one_add_weight_mul_crossNormSq (D : WeightedDesign m 3)
    {first second : Fin m} (hne : first ≠ second) :
    D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second)
      ≤ 1 + D.weight first * D.weight second
          * crossNormSq (D.atom first) (D.atom second) := by
  have hdet := (posSemidef_weightedSubsum D
    (({first, second} : Finset (Fin m))ᶜ)).det_nonneg
  rw [det_weightedComplement_pair D hne] at hdet
  linarith

/-- **A PARALLEL PAIR IS LIGHT IN THE WEIGHTS.**  When the squared area vanishes
the floor becomes a cap on the two shares.  This is the first bound in the
campaign that separates a parallel pair by its weights rather than by its
geometry, and it localises the hinge's target at `(6,3)`. -/
theorem share_add_share_le_one_of_crossNormSq_eq_zero (D : WeightedDesign m 3)
    {first second : Fin m} (hne : first ≠ second)
    (hflat : crossNormSq (D.atom first) (D.atom second) = 0) :
    D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second) ≤ 1 := by
  have hfloor := share_add_share_le_one_add_weight_mul_crossNormSq D hne
  rw [hflat] at hfloor
  linarith

/-- **THE INADMISSIBLE CAP.**  An inadmissible pair has `w ≤ l_p + l_q − 1`, and
feeding that into the wedge floor eliminates the squared area, leaving one
inequality in the two leverages and the two weights. -/
theorem inadmissible_share_cap (D : WeightedDesign m 3) {first second : Fin m}
    (hne : first ≠ second)
    (hinadm : pairGapMinor (D.atom first) (D.atom second) ≤ 0) :
    D.weight first * leverageOf (D.atom first) * (1 - D.weight second)
        + D.weight second * leverageOf (D.atom second) * (1 - D.weight first)
      ≤ 1 - D.weight first * D.weight second := by
  have hfloor := share_add_share_le_one_add_weight_mul_crossNormSq D hne
  have hcap := crossNormSq_le_of_pairGapMinor_nonpos (D.atom first) (D.atom second) hinadm
  have hwpos : 0 < D.weight first * D.weight second :=
    mul_pos (D.weight_pos first) (D.weight_pos second)
  nlinarith [hfloor, hcap, hwpos]

/-! ## 5. The wedge row law, and the price of a light atom -/

/-- **THE WEDGE ROW LAW.**  Parseval read at one atom says the weighted squared
pairings against the whole design total that atom's leverage.  Against the trace
identity this turns into a budget for the SQUARED AREAS:

  `∑_b t_b · w_ab = 2 · l_a` .

It is the squared-area sibling of the landed pair-minor budget, and it is a
different statement: that budget is quadratic in the weights and totals a
constant, this one is linear and totals a leverage. -/
theorem sum_weight_mul_crossNormSq (D : WeightedDesign m 3) (center : Fin m) :
    ∑ b, D.weight b * crossNormSq (D.atom center) (D.atom b)
      = 2 * leverageOf (D.atom center) := by
  have hreading := sum_weight_mul_sq_reading D (D.atom center)
  have hself : D.atom center ⬝ᵥ D.atom center = leverageOf (D.atom center) := frameDotSelf _
  have htrace := sum_weight_mul_leverage D
  have hexpand : ∑ b, D.weight b * crossNormSq (D.atom center) (D.atom b)
      = leverageOf (D.atom center) * (∑ b, D.weight b * leverageOf (D.atom b))
        - ∑ b, D.weight b * (D.atom b ⬝ᵥ D.atom center) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [crossNormSq_eq_leverage_mul_sub_sq, dotProduct_comm (D.atom b) (D.atom center)]
    ring
  rw [hexpand, htrace, hreading, hself]
  push_cast
  ring

/-- The squared area is never negative: Cauchy-Schwarz on the two atoms. -/
theorem crossNormSq_nonneg (leftVec rightVec : Fin 3 → ℝ) :
    0 ≤ crossNormSq leftVec rightVec := by
  rw [crossNormSq_eq_leverage_mul_sub_sq]
  have hcs := dotProduct_sq_le_mul leftVec rightVec
  rw [frameDotSelf, frameDotSelf] at hcs
  linarith

/-- The squared area of an atom with itself vanishes. -/
theorem crossNormSq_self (vec : Fin 3 → ℝ) : crossNormSq vec vec = 0 := by
  rw [crossNormSq_eq_leverage_mul_sub_sq, frameDotSelf]
  ring

/-- **HEAVINESS IS LOAD-BEARING IN QUESTION 7.5(b).**  If one atom has leverage at
most one — and nonzero — then the design carries a pair that is inadmissible and
NOT parallel, so the question's conclusion fails.  The proof is the row law: the
light partners carry at most `l_a` of the squared-area budget `2·l_a`, so the
heavy partners carry more than `l_a > 0`, and one of them has a positive squared
area with the light atom.  Against a heavy partner a light atom is automatically
inadmissible.

This holds at every `(m,3)` design, tie or not.  The strict heaviness `1 < l_c`
of the survey's remaining questions cannot be dropped. -/
theorem exists_inadmissible_nonparallel_of_leverage_le_one (D : WeightedDesign m 3)
    {center : Fin m} (hpos : 0 < leverageOf (D.atom center))
    (hlight : leverageOf (D.atom center) ≤ 1) :
    ∃ partner : Fin m, partner ≠ center
      ∧ pairGapMinor (D.atom center) (D.atom partner) ≤ 0
      ∧ 0 < crossNormSq (D.atom center) (D.atom partner) := by
  classical
  set heavySet : Finset (Fin m) := {b | 1 ≤ leverageOf (D.atom b)} with hheavySet
  have hlightBound : ∑ b ∈ heavySetᶜ, D.weight b * crossNormSq (D.atom center) (D.atom b)
      ≤ leverageOf (D.atom center) := by
    have hstep : ∀ b ∈ heavySetᶜ, D.weight b * crossNormSq (D.atom center) (D.atom b)
        ≤ D.weight b * leverageOf (D.atom center) := by
      intro b hb
      have hbl : leverageOf (D.atom b) < 1 := by
        by_contra hcon
        exact (Finset.mem_compl.mp hb) (by simpa [hheavySet] using (not_lt.mp hcon))
      have hinner : crossNormSq (D.atom center) (D.atom b) ≤ leverageOf (D.atom center) := by
        rw [crossNormSq_eq_leverage_mul_sub_sq]
        nlinarith [hpos, hbl, sq_nonneg (D.atom center ⬝ᵥ D.atom b)]
      exact mul_le_mul_of_nonneg_left hinner (D.weight_pos b).le
    calc ∑ b ∈ heavySetᶜ, D.weight b * crossNormSq (D.atom center) (D.atom b)
        ≤ ∑ b ∈ heavySetᶜ, D.weight b * leverageOf (D.atom center) :=
          Finset.sum_le_sum hstep
      _ = (∑ b ∈ heavySetᶜ, D.weight b) * leverageOf (D.atom center) := by rw [Finset.sum_mul]
      _ ≤ 1 * leverageOf (D.atom center) := by
          have hsub : ∑ b ∈ heavySetᶜ, D.weight b ≤ ∑ b, D.weight b :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun b _ _ => (D.weight_pos b).le)
          rw [D.weight_sum_one] at hsub
          exact mul_le_mul_of_nonneg_right hsub hpos.le
      _ = leverageOf (D.atom center) := one_mul _
  have htotal := sum_weight_mul_crossNormSq D center
  have hsplit := Finset.sum_add_sum_compl heavySet
    (fun b => D.weight b * crossNormSq (D.atom center) (D.atom b))
  rw [htotal] at hsplit
  have hheavyBound : 0 < ∑ b ∈ heavySet, D.weight b * crossNormSq (D.atom center) (D.atom b) := by
    linarith
  obtain ⟨partner, hmem, hterm⟩ :
      ∃ b ∈ heavySet, 0 < D.weight b * crossNormSq (D.atom center) (D.atom b) := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.sum_nonpos fun b hb => hcon b hb) (not_le.mpr hheavyBound)
  have hwedgePos : 0 < crossNormSq (D.atom center) (D.atom partner) := by
    by_contra hcon
    push Not at hcon
    nlinarith [hterm, D.weight_pos partner, hcon]
  refine ⟨partner, ?_, ?_, hwedgePos⟩
  · rintro rfl
    rw [crossNormSq_self] at hwedgePos
    exact absurd hwedgePos (lt_irrefl 0)
  · have hheavy : 1 ≤ leverageOf (D.atom partner) := by simpa [hheavySet] using hmem
    rw [pairGapMinor]
    nlinarith [hheavy, hlight, sq_nonneg (D.atom center ⬝ᵥ D.atom partner)]

/-! ## 6. The rescaled complement rung

The landed weight-rescaled rung compares `τ·S_T` with the weighted sum over `T`.
Parseval turns that weighted sum into `1` less the complement's weighted sum, so
the rung becomes a statement about the COMPLEMENT — and at `m = k + 2` the
complement is a pair. -/

/-- **A SMALL COMPLEMENT MAKES A STRICT DOMINATOR.**  If every member of `T`
carries weight at most `τ` and the complement's total share falls below `1 − τ`,
then `S_T ≻ 1`.  The proof reads the two quadratic forms at one probe and uses
Cauchy-Schwarz on the complement's readings. -/
theorem posDef_subsetSum_sub_one_of_complement_share_lt (D : WeightedDesign m k)
    {T : Finset (Fin m)} {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ T, D.weight c ≤ cap)
    (hsmall : ∑ c ∈ Tᶜ, D.weight c * leverageOf (D.atom c) < 1 - cap) :
    (subsetSum D T - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_subsetSum_sub_one D T, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  have hform : probe ⬝ᵥ ((subsetSum D T - 1) *ᵥ probe)
      = (∑ c ∈ T, (D.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    congr 1
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [frameAtomMulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    ring
  have hcomplBound : ∑ c ∈ Tᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      < (1 - cap) * (probe ⬝ᵥ probe) := by
    have hstep : ∀ c ∈ Tᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
        ≤ D.weight c * leverageOf (D.atom c) * (probe ⬝ᵥ probe) := by
      intro c _
      have hcs := dotProduct_sq_le_mul (D.atom c) probe
      rw [frameDotSelf] at hcs
      nlinarith [hcs, (D.weight_pos c).le]
    calc ∑ c ∈ Tᶜ, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
        ≤ ∑ c ∈ Tᶜ, D.weight c * leverageOf (D.atom c) * (probe ⬝ᵥ probe) :=
          Finset.sum_le_sum hstep
      _ = (∑ c ∈ Tᶜ, D.weight c * leverageOf (D.atom c)) * (probe ⬝ᵥ probe) := by
          rw [Finset.sum_mul]
      _ < (1 - cap) * (probe ⬝ᵥ probe) := mul_lt_mul_of_pos_right hsmall hprobePos
  have hall := sum_weight_mul_sq_reading D probe
  have hsplit := Finset.sum_add_sum_compl T
    (fun c => D.weight c * (D.atom c ⬝ᵥ probe) ^ 2)
  rw [hall] at hsplit
  have hinner : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      ≤ cap * (∑ c ∈ T, (D.atom c ⬝ᵥ probe) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c hc =>
      mul_le_mul_of_nonneg_right (hcap c hc) (sq_nonneg _)
  have hkey : cap * (probe ⬝ᵥ probe) < cap * (∑ c ∈ T, (D.atom c ⬝ᵥ probe) ^ 2) := by
    nlinarith [hinner, hcomplBound, hsplit]
  have hstrict : probe ⬝ᵥ probe < ∑ c ∈ T, (D.atom c ⬝ᵥ probe) ^ 2 :=
    lt_of_mul_lt_mul_left hkey hcapPos.le
  rw [hform]
  linarith

/-- **THE COMPLEMENT SHARE FLOOR.**  A design with no strict `k`-subset dominator
gives every `k`-subset a complement whose total share is at least `1 − τ`, for
every cap `τ` on the members' weights.

SHARP.  Split one atom of the regular tetrahedron into two parallel copies of
half weight.  That `(5,3)` tie has `t = (1/8, 1/8, 1/4, 1/4, 1/4)` and `l ≡ 3`;
at the triple of unsplit atoms `τ = 1/4` and the complement's share is
`3/8 + 3/8 = 3/4 = 1 − τ`. -/
theorem one_sub_weight_cap_le_complement_share (D : WeightedDesign m k)
    (hnostrict : ∀ C : Finset (Fin m), C.card = k → ¬ (subsetSum D C - 1).PosDef)
    {T : Finset (Fin m)} (hcard : T.card = k) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ T, D.weight c ≤ cap) :
    1 - cap ≤ ∑ c ∈ Tᶜ, D.weight c * leverageOf (D.atom c) := by
  by_contra hcon
  exact hnostrict T hcard
    (posDef_subsetSum_sub_one_of_complement_share_lt D hcapPos hcap (lt_of_not_ge hcon))

/-- **THE SHARE CAP ON A SELECTION.**  The complement floor, read on the other
side of the trace identity: a `k`-subset of a design with no strict dominator
carries at most `k − 1 + τ` of the total share `k`. -/
theorem selection_share_cap_of_no_strict_dominator (D : WeightedDesign m k)
    (hnostrict : ∀ C : Finset (Fin m), C.card = k → ¬ (subsetSum D C - 1).PosDef)
    {T : Finset (Fin m)} (hcard : T.card = k) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ T, D.weight c ≤ cap) :
    ∑ c ∈ T, D.weight c * leverageOf (D.atom c) ≤ (k : ℝ) - 1 + cap := by
  classical
  have hfloor := one_sub_weight_cap_le_complement_share D hnostrict hcard hcapPos hcap
  have hsplit := Finset.sum_add_sum_compl T
    (fun c => D.weight c * leverageOf (D.atom c))
  rw [sum_weight_mul_leverage D] at hsplit
  linarith

/-- **THE TRIPLE SHARE CAP AT `(6,3)`.**  A `(6,3)` design with no strict triple
dominator gives every triple a share total of at most `2 + τ`.  This is a new
necessary condition on a `(6,3)` tie, and it is the size-six instance of the
complement rung whose `(5,3)` instance the split tetrahedron makes sharp. -/
theorem triple_share_cap_of_no_strict_dominator (D : WeightedDesign 6 3)
    (hnostrict : ∀ C : Finset (Fin 6), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    {T : Finset (Fin 6)} (hcard : T.card = 3) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ T, D.weight c ≤ cap) :
    ∑ c ∈ T, D.weight c * leverageOf (D.atom c) ≤ 2 + cap := by
  have hcapT := selection_share_cap_of_no_strict_dominator D hnostrict hcard hcapPos hcap
  norm_num at hcapT
  linarith

/-- **THE PAIR FORM OF THE FLOOR.**  At `m = k + 2` the complement of a
`k`-subset is a pair, so the floor is a law about two atoms. -/
theorem one_sub_weight_cap_le_pair_share (D : WeightedDesign m k)
    (hnostrict : ∀ C : Finset (Fin m), C.card = k → ¬ (subsetSum D C - 1).PosDef)
    {first second : Fin m} (hne : first ≠ second)
    (hcard : ({first, second} : Finset (Fin m))ᶜ.card = k) {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : ∀ c ∈ ({first, second} : Finset (Fin m))ᶜ, D.weight c ≤ cap) :
    1 - cap ≤ D.weight first * leverageOf (D.atom first)
      + D.weight second * leverageOf (D.atom second) := by
  classical
  have hfloor := one_sub_weight_cap_le_complement_share D hnostrict hcard hcapPos hcap
  rwa [compl_compl, Finset.sum_pair hne] at hfloor

/-! ## 7. The rank-zero exclusion at corank two -/

/-- **NO `k`-SUBSET RESOLVES THE IDENTITY AT CORANK TWO.**  If `S_C = 1` then the
members' weighted atoms are dominated by `τ · 1` with `τ < 1`, so the complement
PAIR's weighted sum is positive definite — impossible, because two rank-one
matrices cannot fill rank three.  Hence the gap of a weak dominator of a `(5,3)`
tie has rank one or rank two, never zero. -/
theorem subsetSum_ne_one_of_corank_two (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {outsideFirst outsideSecond : Fin m} (hne : outsideFirst ≠ outsideSecond)
    (hcompl : Cᶜ = {outsideFirst, outsideSecond}) {cap : ℝ} (hcapLt : cap < 1)
    (hcap : ∀ c ∈ C, D.weight c ≤ cap) :
    subsetSum D C ≠ 1 := by
  classical
  intro hone
  have hCsum : ∑ c ∈ C, D.weight c • atomMatrix (D.atom c)
      = 1 - weightedPairSum D outsideFirst outsideSecond := by
    rw [← weightedComplement_pair_eq D hne, ← hcompl, compl_compl]
  have hdetPair : (weightedPairSum D outsideFirst outsideSecond).det = 0 := by
    rw [weightedPairSum]; exact det_pairAtomCombo _ _ _ _
  have hpairLower : ∀ probe : Fin 3 → ℝ,
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ probe ⬝ᵥ (weightedPairSum D outsideFirst outsideSecond *ᵥ probe) := by
    intro probe
    have hmembers : probe ⬝ᵥ ((∑ c ∈ C, D.weight c • atomMatrix (D.atom c)) *ᵥ probe)
        ≤ cap * (probe ⬝ᵥ probe) := by
      rw [dotProduct_weightedSubsum_mulVec]
      have hcapSum : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
          ≤ ∑ c ∈ C, cap * (D.atom c ⬝ᵥ probe) ^ 2 :=
        Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_right (hcap c hc) (sq_nonneg _)
      have hunw : ∑ c ∈ C, cap * (D.atom c ⬝ᵥ probe) ^ 2
          = cap * (probe ⬝ᵥ (subsetSum D C *ᵥ probe)) := by
        rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [frameAtomMulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
        ring
      rw [hunw, hone, Matrix.one_mulVec] at hcapSum
      exact hcapSum
    rw [hCsum, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hmembers
    linarith
  have hsymm : (weightedPairSum D outsideFirst outsideSecond)ᵀ
      = weightedPairSum D outsideFirst outsideSecond := by
    ext i j
    simp only [weightedPairSum, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply]
    ring
  have hposDef : (weightedPairSum D outsideFirst outsideSecond).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
    rw [star_trivial]
    have hlower := hpairLower probe
    have hpos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
    nlinarith [hlower, hpos, hcapLt]
  exact absurd hdetPair (ne_of_gt hposDef.det_pos)

/-! ## 8. The complement volume laws at the three live sizes -/

/-- **`(4,3)`: THE COMPLEMENT OF A PAIR IS A PAIR.**  Its determinant vanishes, so
the pair law becomes an equation and every pair of a `(4,3)` design has its
squared area pinned by its two shares. -/
theorem pair_share_sum_eq_of_size_four (D : WeightedDesign 4 3) {first second : Fin 4}
    (hne : first ≠ second) {outFirst outSecond : Fin 4} (houtne : outFirst ≠ outSecond)
    (hcompl : ({first, second} : Finset (Fin 4))ᶜ = {outFirst, outSecond}) :
    D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second)
      = 1 + D.weight first * D.weight second
          * crossNormSq (D.atom first) (D.atom second) := by
  have hdet := det_weightedComplement_pair D hne
  rw [hcompl, Finset.sum_pair houtne] at hdet
  rw [det_pairAtomCombo] at hdet
  linarith

/-- **`(5,3)`: THE COMPLEMENT TRIPLE VOLUME LAW.**  The complement of a pair is a
triple, and its weighted squared volume equals the pair's share deficit plus its
weighted squared area. -/
theorem complement_triple_volume_law (D : WeightedDesign 5 3) {first second : Fin 5}
    (hne : first ≠ second) {outFirst outMid outLast : Fin 5}
    (hfm : outFirst ≠ outMid) (hfl : outFirst ≠ outLast) (hml : outMid ≠ outLast)
    (hcompl : ({first, second} : Finset (Fin 5))ᶜ = {outFirst, outMid, outLast}) :
    D.weight outFirst * D.weight outMid * D.weight outLast
        * tripleBracket (D.atom outFirst) (D.atom outMid) (D.atom outLast) ^ 2
      = 1 - D.weight first * leverageOf (D.atom first)
        - D.weight second * leverageOf (D.atom second)
        + D.weight first * D.weight second
          * crossNormSq (D.atom first) (D.atom second) := by
  have hdet := det_weightedComplement_pair D hne
  rw [hcompl, Finset.sum_insert (by simp [hfm, hfl]), Finset.sum_insert (by simp [hml]),
    Finset.sum_singleton, ← add_assoc, det_tripleAtomCombo] at hdet
  exact hdet

/-- **`(5,3)`: A PARALLEL PAIR'S SHARE DEFICIT IS THE COMPLEMENT'S VOLUME.**  So a
parallel pair whose shares total exactly one has a COPLANAR complement, and a
parallel pair with a non-degenerate complement has shares totalling strictly less
than one. -/
theorem parallel_pair_share_deficit_eq_complement_volume (D : WeightedDesign 5 3)
    {first second : Fin 5} (hne : first ≠ second) {outFirst outMid outLast : Fin 5}
    (hfm : outFirst ≠ outMid) (hfl : outFirst ≠ outLast) (hml : outMid ≠ outLast)
    (hcompl : ({first, second} : Finset (Fin 5))ᶜ = {outFirst, outMid, outLast})
    (hflat : crossNormSq (D.atom first) (D.atom second) = 0) :
    D.weight outFirst * D.weight outMid * D.weight outLast
        * tripleBracket (D.atom outFirst) (D.atom outMid) (D.atom outLast) ^ 2
      = 1 - D.weight first * leverageOf (D.atom first)
        - D.weight second * leverageOf (D.atom second) := by
  have hlaw := complement_triple_volume_law D hne hfm hfl hml hcompl
  rw [hflat] at hlaw
  linarith

/-- **`(6,3)`: THE COMPLEMENT FOUR-SET VOLUME LAW.**  The four complementary
triples' weighted squared volumes total the pair's share deficit plus its
weighted squared area.  This is the size-six instance of the complement law, and
it converts a statement about a pair into a statement about four volumes of the
remaining design. -/
theorem complement_fourSet_volume_law (D : WeightedDesign 6 3) {first second : Fin 6}
    (hne : first ≠ second) {outOne outTwo outThree outFour : Fin 6}
    (h12 : outOne ≠ outTwo) (h13 : outOne ≠ outThree) (h14 : outOne ≠ outFour)
    (h23 : outTwo ≠ outThree) (h24 : outTwo ≠ outFour) (h34 : outThree ≠ outFour)
    (hcompl : ({first, second} : Finset (Fin 6))ᶜ = {outOne, outTwo, outThree, outFour}) :
    D.weight outOne * D.weight outTwo * D.weight outThree
          * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outThree) ^ 2
        + D.weight outOne * D.weight outTwo * D.weight outFour
          * tripleBracket (D.atom outOne) (D.atom outTwo) (D.atom outFour) ^ 2
        + D.weight outOne * D.weight outThree * D.weight outFour
          * tripleBracket (D.atom outOne) (D.atom outThree) (D.atom outFour) ^ 2
        + D.weight outTwo * D.weight outThree * D.weight outFour
          * tripleBracket (D.atom outTwo) (D.atom outThree) (D.atom outFour) ^ 2
      = 1 - D.weight first * leverageOf (D.atom first)
        - D.weight second * leverageOf (D.atom second)
        + D.weight first * D.weight second
          * crossNormSq (D.atom first) (D.atom second) := by
  have hdet := det_weightedComplement_pair D hne
  rw [hcompl, Finset.sum_insert (by simp [h12, h13, h14]),
    Finset.sum_insert (by simp [h23, h24]), Finset.sum_insert (by simp [h34]),
    Finset.sum_singleton] at hdet
  rw [show D.weight outOne • atomMatrix (D.atom outOne)
        + (D.weight outTwo • atomMatrix (D.atom outTwo)
          + (D.weight outThree • atomMatrix (D.atom outThree)
            + D.weight outFour • atomMatrix (D.atom outFour)))
      = D.weight outOne • atomMatrix (D.atom outOne)
        + D.weight outTwo • atomMatrix (D.atom outTwo)
        + D.weight outThree • atomMatrix (D.atom outThree)
        + D.weight outFour • atomMatrix (D.atom outFour) by abel,
    det_fourAtomCombo] at hdet
  exact hdet

/-! ## 9. What Question 7.5(b) costs at `(5,3)` -/

/-- **THE GRAM CRITERION, WEAK FORM.**  Weak domination by a triple is positive
semidefiniteness of the selected atoms' Gram matrix minus the identity.  The
landed `Gtz.subsetSum_posDef_iff_tripleGram` is the strict version and needs
positive definiteness, which a tie never supplies. -/
theorem dominates_triple_iff_tripleGram_posSemidef (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Dominates D ({x, y, z} : Finset (Fin m))
      ↔ (tripleGram (D.atom x) (D.atom y) (D.atom z) - 1).PosSemidef := by
  rw [Dominates, subsetSum_triple_eq_mul_transpose D x y z hxy hxz hyz, tripleGram]
  exact (posSemidef_transpose_mul_sub_one_comm _).symm

/-- **EVERY PAIR INSIDE A WEAK DOMINATOR IS ADMISSIBLE.**  The two-by-two
principal minor of a positive semidefinite Gram gap is nonnegative, and at a pair
of members that minor is exactly the pair minor. -/
theorem pairGapMinor_nonneg_of_dominates_triple (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    0 ≤ pairGapMinor (D.atom x) (D.atom y) := by
  have hpsd := (dominates_triple_iff_tripleGram_posSemidef D x y z hxy hxz hyz).mp hdom
  have hsub := hpsd.submatrix (![0, 1] : Fin 2 → Fin 3)
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  rw [gap_zero_zero, gap_one_one, gap_zero_one, gap_one_zero] at hdet
  rw [pairGapMinor]
  nlinarith [hdet]

/-- **A VANISHING PAIR MINOR IS NEVER PARALLEL WHEN BOTH ATOMS ARE HEAVY.**  With
`q_ab = 0` the squared area is `l_a + l_b − 1`, which exceeds one. -/
theorem crossNormSq_pos_of_pairGapMinor_eq_zero_of_heavy (leftVec rightVec : Fin 3 → ℝ)
    (hleft : 1 < leverageOf leftVec) (hright : 1 < leverageOf rightVec)
    (hzero : pairGapMinor leftVec rightVec = 0) :
    1 < crossNormSq leftVec rightVec := by
  rw [pairGapMinor_eq_crossNormSq] at hzero
  linarith

/-- **THE PRICE OF QUESTION 7.5(b).**  Suppose the question's conclusion holds at
a design whose atoms are strictly heavy: every inadmissible pair has vanishing
squared area.  Then NO weak dominator carries a vanishing pair minor.  By the
survey's adjugate corollary that is exactly the statement that every weak
dominator has gap rank two with no vanishing reading — the standing hypothesis of
the survey's rank-two section, here shown to be a CONSEQUENCE of the question
rather than an aid to it. -/
theorem pairGapMinor_pos_inside_dominator_of_q75b (D : WeightedDesign m 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hq75b : ∀ x y : Fin m, x ≠ y → pairGapMinor (D.atom x) (D.atom y) ≤ 0 →
      crossNormSq (D.atom x) (D.atom y) = 0)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    0 < pairGapMinor (D.atom x) (D.atom y) := by
  rcases lt_or_eq_of_le (pairGapMinor_nonneg_of_dominates_triple D x y z hxy hxz hyz hdom)
    with hpos | hzero
  · exact hpos
  · exact absurd (hq75b x y hxy (le_of_eq hzero.symm))
      (ne_of_gt (lt_trans zero_lt_one
        (crossNormSq_pos_of_pairGapMinor_eq_zero_of_heavy (D.atom x) (D.atom y)
          (hheavy x) (hheavy y) hzero.symm)))

/-- **THE THREE-WAY SPLIT AT `(5,3)`.**  A weak dominator has three members and a
complement pair, so a pair of a `(5,3)` design meets a dominator in two, one or
none of its members, and the last case is exactly `{a,b} = Cᶜ`. -/
theorem pair_dominator_trichotomy {C : Finset (Fin 5)} (hcard : C.card = 3)
    (first second : Fin 5) (hne : first ≠ second) :
    (first ∈ C ∧ second ∈ C)
      ∨ (first ∈ C ∧ second ∉ C) ∨ (first ∉ C ∧ second ∈ C)
      ∨ ({first, second} : Finset (Fin 5)) = Cᶜ := by
  classical
  by_cases hfirst : first ∈ C
  · by_cases hsecond : second ∈ C
    · exact Or.inl ⟨hfirst, hsecond⟩
    · exact Or.inr (Or.inl ⟨hfirst, hsecond⟩)
  · by_cases hsecond : second ∈ C
    · exact Or.inr (Or.inr (Or.inl ⟨hfirst, hsecond⟩))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hsub : ({first, second} : Finset (Fin 5)) ⊆ Cᶜ := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact Finset.mem_compl.mpr hfirst
        · rw [Finset.mem_singleton] at hz'
          subst hz'
          exact Finset.mem_compl.mpr hsecond
      have hcards : ({first, second} : Finset (Fin 5)).card = Cᶜ.card := by
        rw [Finset.card_pair hne, Finset.card_compl, hcard]
        simp
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcards.symm)

/-- **THE COMPLEMENT CASE AT `(5,3)`, PRICED BY THE COMPLEMENT'S VOLUME.**  When
the inadmissible pair is the complement of a triple, the complement volume law
and the inadmissible cap combine: any lower bound on the complement's
determinant is a cap on the two shares.  The landed
`Gtz.one_le_sq_tripleBracket_of_dominates` supplies the bound
`volume = t_c·t_d·t_e` whenever that complement triple weakly dominates. -/
theorem inadmissible_complement_volume_bound (D : WeightedDesign 5 3)
    {first second : Fin 5} (hne : first ≠ second)
    (hinadm : pairGapMinor (D.atom first) (D.atom second) ≤ 0)
    {volume : ℝ}
    (hvolume : volume ≤ (∑ c ∈ ({first, second} : Finset (Fin 5))ᶜ,
      D.weight c • atomMatrix (D.atom c)).det) :
    volume + D.weight first * D.weight second
      ≤ 1 - D.weight first * leverageOf (D.atom first) * (1 - D.weight second)
        - D.weight second * leverageOf (D.atom second) * (1 - D.weight first) := by
  rw [det_weightedComplement_pair D hne] at hvolume
  have hcap := crossNormSq_le_of_pairGapMinor_nonpos (D.atom first) (D.atom second) hinadm
  have hproductPos : 0 < D.weight first * D.weight second :=
    mul_pos (D.weight_pos first) (D.weight_pos second)
  have hcapScaled : D.weight first * D.weight second
        * crossNormSq (D.atom first) (D.atom second)
      ≤ D.weight first * D.weight second
        * (leverageOf (D.atom first) + leverageOf (D.atom second) - 1) :=
    mul_le_mul_of_nonneg_left hcap hproductPos.le
  linarith [hvolume, hcapScaled]

end Gtz

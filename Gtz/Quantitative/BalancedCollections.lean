/-
# Balanced collections on the `rank`-subset layer, and the fractional relaxation

A multiplier on the `rank`-subsets of `[size]` is BALANCED when it is nonnegative
and the multipliers of the subsets through any one atom sum to one -- the
Bondareva--Shapley balance condition, restricted to the uniform layer the selection
problem lives on.  This module lands that layer at general `(size, rank)`, together
with the reason it cannot reach GTZ.

## The shape of the layer

Everything runs on ONE double count.  Writing `deg(c)` for the total mass a
multiplier puts on the subsets through atom `c`,

    sum_C mu_C * S_C  =  sum_c deg(c) * A_c                (the MASTER IDENTITY)

for an ARBITRARY real multiplier on an arbitrary layer -- no balance, no
nonnegativity, no design axiom.  Balance is `deg == 1`, and then the right-hand
side collapses to the full atom sum, the multiplier having vanished entirely:

    sum_C mu_C * (S_C - 1)  =  S_univ - (size/rank) * 1 .

So the whole combinatorial freedom in `mu` is invisible to the averaged gap; only
the SUPPORT of `mu` carries information, which is what the vertex census of the
balanced polytope is about.

## Why the layer cannot reach GTZ, in one theorem

`not_isBalancedSubsetMultiplier_indicator`: the indicator of a SINGLE subset is
never balanced (as soon as one atom lies outside it, its degree there is zero, not
one).  GTZ asks for a single subset; a balanced average structurally cannot express
one.  Correspondingly `posSemidef_hypersimplexRelaxation` exhibits an EXPLICIT point
of the hypersimplex `Delta(size, rank)` that dominates, at every design and over
every field, so the fractional relaxation of the conjecture is unconditionally true
and carries no content.  The entire conjecture is the INTEGRALITY GAP -- whether the
explicit fractional certificate can be rounded to a 0/1 point.  That is a structural
explanation of the campaign's measured walls on design-blind aggregates (B6, B10),
not a new one of them.

## R6 disclosures -- read these before extending

* **The "sharpened full excess" is NOT landed, because it is already shipped.**  The
  statement `weight <= rank/size` implies `rank * S_univ >= size * 1` is EQUIVALENT,
  by a positive rescale in both directions, to the shipped
  `Gtz.posSemidef_bound_smul_subsetSum_sub_one`
  (`Gtz/Quantitative/DesignQuadraticFloors.lean:162`) at `bound = rank/size`.  What
  this module lands instead is the SHIFT reparametrisation
  `posSemidef_subsetSum_univ_sub_smul_one`, which is the form the balanced identity
  produces and which is PROVED BY CONSUMING that shipped lemma rather than by
  reproving it.

* **`T - I` positive semidefinite is NOT restated.**  It is shipped strictly
  stronger as `Gtz.posDef_fullExcess` (positive DEFINITE, from `2 <= size`) together
  with `Gtz.fullExcess_eq_coParseval`, both in `Gtz/Reduction/DescentLadder.lean`.
  `subsetSum_univ_sub_smul_one_eq` below is the arbitrary-shift generalisation of the
  latter and is landed only because the balanced identity needs shift `size/rank`.

* **The incidence swap generalises two shipped lemmas.**
  `Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum`
  (`Gtz/Quantitative/CauchyBinetValueFloor.lean:408`) is the case of a summand
  depending on the atom alone, and `Gtz.sum_powersetCard_sum_mem_mul_eq`
  (`Gtz/Quantitative/ElementaryValueFloor.lean:571`) the case of a real product.
  Neither covers a MATRIX-valued summand depending on both the subset and the atom,
  which is what the master identity needs, so `sum_powersetCard_sum_mem_comm` is
  stated over an arbitrary `AddCommMonoid`.

* **The fractional certificate composes with the domination cone rather than
  duplicating it.**  `posSemidef_hypersimplexRelaxation` is proved by CONSUMING
  `Gtz.mem_dominationCone_of_nonneg` (`Gtz/Quantitative/HarmonicCircuit.lean`): the
  displacement from the weights to the certificate is coordinatewise nonnegative.
  `gtzWeighted_iff_forall_exists_zeroOne_relaxation` is landed alongside the shipped
  `Gtz.gtzWeighted_iff_forall_exists_vertexDirection_mem_dominationCone` because the
  0/1 form shares its literal expression `(sum_c w_c A_c - 1).PosSemidef` with the
  relaxation theorem, which is exactly what makes the fractional-versus-integral
  contrast a comparison of two instances of one formula rather than of two
  formalisms.

* **Balanced multipliers are NOT the product weightings of
  `Gtz.gapMinorAggregate`** (`Gtz/Quantitative/MixtureAggregates.lean`).  Balance is
  a per-atom DEGREE condition; that one is a per-subset PRODUCT.  The two objects
  are unrelated and the master identity applies to both only because it assumes
  neither.  Nor is the hypersimplex here the `Gtz.invariantLeverageHypersimplex` of
  `Gtz/Quantitative/SixThreeNuCovering.lean`, which is `sum nu = 2` in the inverse-
  leverage coordinate.

## Measured scope (measurements, not theorems; recorded for calibration)

The balanced polytope `B(size, rank)` -- nonnegative multipliers with all degrees
one -- has exactly 70 vertices at `(6,3)`, in 3 orbits with support-size histogram
`{2:10, 4:30, 6:30}` and multiplier values `1`, `1/2`, `1/3`; 33395 at `(7,3)` with
histogram `{5:1085, 6:4620, 7:27690}`; 3634897 at `(8,3)`; 2029615 at `(8,4)`.  At
`(m,2)` the vertices are Balinski's fractional perfect matchings: 3, 22, 25, 717 at
`m = 4,5,6,7`.  TWO CORRECTIONS to an earlier reading, both from the `(7,3)` count.
First, "every vertex has a CONSTANT multiplier" is a `(6,3)` accident and is FALSE at
`(7,3)`: a constant multiplier on a `d`-regular support forces `|S| = (m/rank) d`,
hence `|S| = 7` at `(7,3)`, so the 5705 vertices of support 5 and 6 are non-constant.
Second, the finite-certificate-basis reading of B6 -- every design-blind nonnegative
aggregation of the domination gaps is a nonnegative combination of finitely many
explicit ones -- blows up 477-fold from 70 generators to 33395 in one step, so its
sharpness is an accident of size and not a structural fact.

The layer is FIELD-BLIND: every statement here is linear in the atoms and transports
verbatim to Hermitian atoms, so by boundary condition B1 no closing route can be
built on it.  It also has no contact with the equality locus B2 demands: at the exact
`Q(sqrt 5)` `(6,3)` tie the balanced pigeonhole over all 70 vertices is slack by
`10/3` at its tightest, and by `48/5` at `Gtz.icosaDesign`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.CollaredCompact
import Gtz.Reduction.DescentLadder
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Quantitative.ExcessGapCensus
import Gtz.Quantitative.HarmonicCircuit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The incidence swap -/

/-- **THE INCIDENCE SWAP.**  Summing a quantity indexed by (subset, member) pairs
subset-outermost equals summing it atom-outermost over the subsets through that atom.
This is the double count every statement below runs on.  It is stated over an
arbitrary `AddCommMonoid` with the summand depending on BOTH indices, because the
master identity needs a matrix-valued summand; the two shipped specialisations are
named in the module header. -/
theorem sum_powersetCard_sum_mem_comm {carrier : Type*} [AddCommMonoid carrier]
    (level : ℕ) (summand : Finset (Fin size) → Fin size → carrier) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        ∑ atomIndex ∈ selected, summand selected atomIndex
      = ∑ atomIndex : Fin size,
          ∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
              (fun candidate => atomIndex ∈ candidate),
            summand selected atomIndex := by
  classical
  refine Finset.sum_comm' ?_
  intro selected atomIndex
  simp only [Finset.mem_filter, Finset.mem_univ, and_true]

/-! ## The multiplier degree and the master identity -/

/-- The multiplier's DEGREE at an atom: the total mass it puts on the subsets of the
given layer through that atom.  Balance is `multiplierDegree = 1` everywhere. -/
def multiplierDegree (level : ℕ) (multiplier : Finset (Fin size) → ℝ)
    (atomIndex : Fin size) : ℝ :=
  ∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
    (fun candidate => atomIndex ∈ candidate), multiplier selected

/-- **THE MASTER IDENTITY.**  Aggregating the unweighted atom sums against any
multiplier on any layer is the same as reweighting each atom by that multiplier's
degree.  No balance, no nonnegativity, no design axiom is used -- this is a pure
exchange of summation order, and every identity below is a corollary of it. -/
theorem sum_smul_subsetSum_eq_sum_multiplierDegree_smul
    (design : WeightedDesign size rank) (level : ℕ)
    (multiplier : Finset (Fin size) → ℝ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected • subsetSum design selected
      = ∑ atomIndex, multiplierDegree level multiplier atomIndex
          • atomMatrix (design.atom atomIndex) := by
  classical
  have hinner : ∀ selected : Finset (Fin size),
      multiplier selected • subsetSum design selected
        = ∑ atomIndex ∈ selected,
            multiplier selected • atomMatrix (design.atom atomIndex) :=
    fun selected => by rw [subsetSum, Finset.smul_sum]
  simp only [hinner]
  rw [sum_powersetCard_sum_mem_comm level
    fun selected atomIndex => multiplier selected • atomMatrix (design.atom atomIndex)]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [multiplierDegree, Finset.sum_smul]

/-- **THE MASS LAW.**  Summing the degrees counts each subset `level` times, so the
total mass and the total degree determine one another. -/
theorem level_mul_sum_eq_sum_multiplierDegree (level : ℕ)
    (multiplier : Finset (Fin size) → ℝ) :
    (level : ℝ) * ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected
      = ∑ atomIndex : Fin size, multiplierDegree level multiplier atomIndex := by
  classical
  have hexpand : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      ∑ _atomIndex ∈ selected, multiplier selected
      = (level : ℝ) * ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
          multiplier selected := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun selected hselected => by
      rw [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hselected).2]
  rw [← hexpand, sum_powersetCard_sum_mem_comm level fun selected _ => multiplier selected]
  exact Finset.sum_congr rfl fun atomIndex _ => by rw [multiplierDegree]

/-! ## Balanced multipliers -/

/-- **A BALANCED MULTIPLIER** on the `level`-subsets: nonnegative, and the multipliers
of the subsets through any one atom sum to one. -/
def IsBalancedSubsetMultiplier (level : ℕ) (multiplier : Finset (Fin size) → ℝ) : Prop :=
  (∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level, 0 ≤ multiplier selected)
    ∧ ∀ atomIndex : Fin size, multiplierDegree level multiplier atomIndex = 1

theorem multiplierDegree_eq_one_of_isBalancedSubsetMultiplier {level : ℕ}
    {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier) (atomIndex : Fin size) :
    multiplierDegree level multiplier atomIndex = 1 :=
  hbalanced.2 atomIndex

/-- The uniform family `1 / C(size - 1, level - 1)` is balanced: the number of
`level`-subsets through a fixed atom is that binomial. -/
theorem isBalancedSubsetMultiplier_uniform (level : ℕ) (hlevel : 0 < level)
    (hle : level ≤ size) :
    IsBalancedSubsetMultiplier (size := size) level
      (fun _ => ((((size - 1).choose (level - 1) : ℕ) : ℝ))⁻¹) := by
  classical
  have hchoose : 0 < (size - 1).choose (level - 1) := Nat.choose_pos (by omega)
  refine ⟨fun _ _ => by positivity, fun atomIndex => ?_⟩
  rw [multiplierDegree, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.univ : Finset (Fin size)).powersetCard level).filter
      (fun candidate => atomIndex ∈ candidate)).card = (size - 1).choose (level - 1) := by
    have hrewrite : ((Finset.univ : Finset (Fin size)).powersetCard level).filter
        (fun candidate => atomIndex ∈ candidate)
        = ((Finset.univ : Finset (Fin size)).powersetCard level).filter
            (fun candidate => {atomIndex} ⊆ candidate) := by
      refine Finset.filter_congr fun candidate _ => ?_
      simp [Finset.singleton_subset_iff]
    rw [hrewrite, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
      (by simp only [Finset.card_singleton]; omega)]
    simp
  rw [hcard]
  field_simp

/-- **THE OBSTRUCTION, in one line.**  The indicator of a SINGLE subset is never
balanced: at any atom outside that subset the degree is zero, not one.  GTZ asks for
a single subset, so no balanced average can express what the conjecture asks for --
this is the structural reason the whole layer is a fractional statement. -/
theorem not_isBalancedSubsetMultiplier_indicator (level : ℕ) (chosen : Finset (Fin size))
    {outside : Fin size} (houtside : outside ∉ chosen) :
    ¬ IsBalancedSubsetMultiplier level
        (fun candidate => if candidate = chosen then (1 : ℝ) else 0) := by
  classical
  intro hbalanced
  have hdegree := hbalanced.2 outside
  rw [multiplierDegree] at hdegree
  have hzero : ∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
      (fun candidate => outside ∈ candidate),
      (if selected = chosen then (1 : ℝ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun selected hselected => ?_
    have hmem : outside ∈ selected := (Finset.mem_filter.mp hselected).2
    have hne : selected ≠ chosen := fun hEq => houtside (hEq ▸ hmem)
    rw [if_neg hne]
  rw [hzero] at hdegree
  exact zero_ne_one hdegree

/-! ## The two halves of C5 -/

/-- **C5(a), THE MASS.**  Every balanced family has total mass `size / level`. -/
theorem sum_isBalancedSubsetMultiplier {level : ℕ} (hlevel : 0 < level)
    {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level, multiplier selected
      = (size : ℝ) / level := by
  have hscaled := level_mul_sum_eq_sum_multiplierDegree (size := size) level multiplier
  rw [Finset.sum_congr rfl (fun atomIndex _ => hbalanced.2 atomIndex), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hscaled
  have hlevelne : (level : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hlevel.ne'
  field_simp
  linarith [hscaled]

/-- **C5(b), THE MATRIX IDENTITY.**  Every balanced average of the subset sums is the
FULL atom sum -- the multiplier has disappeared.  Immediate from the master identity
at degree one. -/
theorem sum_smul_subsetSum_isBalancedSubsetMultiplier (design : WeightedDesign size rank)
    {level : ℕ} {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected • subsetSum design selected
      = subsetSum design Finset.univ := by
  rw [sum_smul_subsetSum_eq_sum_multiplierDegree_smul design level multiplier,
    Finset.sum_congr rfl (fun atomIndex _ =>
      by rw [hbalanced.2 atomIndex, one_smul] : ∀ atomIndex ∈ Finset.univ,
        multiplierDegree level multiplier atomIndex • atomMatrix (design.atom atomIndex)
          = atomMatrix (design.atom atomIndex)),
    subsetSum]

/-- **THE SHIFTED CO-PARSEVAL FORM**, at every real shift.  The shift `1` is the
shipped `Gtz.fullExcess_eq_coParseval`; the shift the balanced identity produces is
`size / rank`. -/
theorem subsetSum_univ_sub_smul_one_eq (design : WeightedDesign size rank) (shift : ℝ) :
    subsetSum design Finset.univ - shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)
      = ∑ atomIndex, (1 - shift * design.weight atomIndex)
          • atomMatrix (design.atom atomIndex) := by
  have hterm : ∀ atomIndex : Fin size,
      (1 - shift * design.weight atomIndex) • atomMatrix (design.atom atomIndex)
        = atomMatrix (design.atom atomIndex)
            - shift • (design.weight atomIndex • atomMatrix (design.atom atomIndex)) :=
    fun atomIndex => by rw [sub_smul, one_smul, smul_smul]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, design.isParseval, subsetSum]

/-- **C5(b) IN GAP FORM.**  The balanced average of the DOMINATION GAPS is a matrix
that does not see the multiplier at all. -/
theorem sum_smul_gap_isBalancedSubsetMultiplier (design : WeightedDesign size rank)
    {level : ℕ} (hlevel : 0 < level) {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected • (subsetSum design selected - 1)
      = ∑ atomIndex, (1 - ((size : ℝ) / level) * design.weight atomIndex)
          • atomMatrix (design.atom atomIndex) := by
  have hsplit : ∀ selected : Finset (Fin size),
      multiplier selected • (subsetSum design selected - (1 : Matrix (Fin rank) (Fin rank) ℝ))
        = multiplier selected • subsetSum design selected
            - multiplier selected • (1 : Matrix (Fin rank) (Fin rank) ℝ) :=
    fun selected => smul_sub _ _ _
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, sum_smul_subsetSum_isBalancedSubsetMultiplier design hbalanced,
    ← Finset.sum_smul, sum_isBalancedSubsetMultiplier hlevel hbalanced,
    ← subsetSum_univ_sub_smul_one_eq design ((size : ℝ) / level)]

/-! ## When the averaged gap is positive semidefinite -/

/-- The shifted full excess is positive semidefinite as soon as the shift never
scales a weight past one.  PROVED BY CONSUMING the shipped
`Gtz.posSemidef_bound_smul_subsetSum_sub_one` at `bound = 1/shift`: the two are the
same statement up to a positive rescale, so this is a reparametrisation into the form
the balanced identity produces, not a second proof. -/
theorem posSemidef_subsetSum_univ_sub_smul_one (design : WeightedDesign size rank)
    {shift : ℝ} (hshift : ∀ atomIndex, shift * design.weight atomIndex ≤ 1) :
    (subsetSum design Finset.univ - shift • (1 : Matrix (Fin rank) (Fin rank) ℝ)).PosSemidef := by
  rcases le_or_gt shift 0 with hle | hpos
  · rw [subsetSum_univ_sub_smul_one_eq design shift]
    refine Matrix.posSemidef_sum _ fun atomIndex _ => ?_
    refine (posSemidef_atomMatrix (design.atom atomIndex)).smul ?_
    nlinarith [(design.weight_pos atomIndex).le]
  · have hbound : ∀ atomIndex, design.weight atomIndex ≤ shift⁻¹ := fun atomIndex =>
      calc design.weight atomIndex
          = shift⁻¹ * (shift * design.weight atomIndex) := by field_simp
        _ ≤ shift⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hshift atomIndex) (inv_pos.mpr hpos).le
        _ = shift⁻¹ := mul_one _
    have hshipped : (shift⁻¹ • subsetSum design Finset.univ - 1).PosSemidef :=
      posSemidef_bound_smul_subsetSum_sub_one design hbound
    have hscale := hshipped.smul hpos.le
    have hrewrite : shift • (shift⁻¹ • subsetSum design Finset.univ - 1)
        = subsetSum design Finset.univ
          - shift • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rwa [hrewrite] at hscale

/-- The balanced instance: whenever no weight exceeds `level / size`, EVERY balanced
average of the domination gaps is positive semidefinite. -/
theorem posSemidef_sum_smul_gap_isBalancedSubsetMultiplier (design : WeightedDesign size rank)
    {level : ℕ} (hlevel : 0 < level) {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier)
    (hweight : ∀ atomIndex, ((size : ℝ) / level) * design.weight atomIndex ≤ 1) :
    (∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected • (subsetSum design selected - 1)).PosSemidef := by
  rw [sum_smul_gap_isBalancedSubsetMultiplier design hlevel hbalanced,
    ← subsetSum_univ_sub_smul_one_eq design ((size : ℝ) / level)]
  exact posSemidef_subsetSum_univ_sub_smul_one design hweight

/-- **THE PSD AGGREGATION LEMMA**, for an arbitrary multiplier.  As soon as every
degree dominates the corresponding weight scaled by the total mass, the aggregated
gap is a nonnegative combination of the rank-one atoms, hence positive semidefinite.
The hypothesis fails at every single-subset multiplier -- `1_C` has degree zero off
`C` while `mass * weight` is strictly positive there -- which is
`not_isBalancedSubsetMultiplier_indicator` seen from the quantitative side, and is
exactly why this lemma cannot reach GTZ. -/
theorem posSemidef_sum_smul_gap_of_le_multiplierDegree (design : WeightedDesign size rank)
    (level : ℕ) (multiplier : Finset (Fin size) → ℝ)
    (hdominates : ∀ atomIndex,
      (∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
          multiplier selected) * design.weight atomIndex
        ≤ multiplierDegree level multiplier atomIndex) :
    (∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected • (subsetSum design selected - 1)).PosSemidef := by
  have hsplit : ∀ selected : Finset (Fin size),
      multiplier selected • (subsetSum design selected - (1 : Matrix (Fin rank) (Fin rank) ℝ))
        = multiplier selected • subsetSum design selected
          - multiplier selected • (1 : Matrix (Fin rank) (Fin rank) ℝ) :=
    fun selected => smul_sub _ _ _
  simp only [hsplit]
  rw [Finset.sum_sub_distrib,
    sum_smul_subsetSum_eq_sum_multiplierDegree_smul design level multiplier,
    ← Finset.sum_smul, ← design.isParseval, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Matrix.posSemidef_sum _ fun atomIndex _ => ?_
  rw [smul_smul, ← sub_smul]
  exact (posSemidef_atomMatrix (design.atom atomIndex)).smul (by linarith [hdominates atomIndex])

/-! ## The support pigeonhole -/

/-- **THE WEIGHTED PIGEONHOLE**, as a standalone scalar fact: some index carrying
POSITIVE weight has value at least the weighted mean. -/
theorem exists_pos_weight_mean_le {index : Type*} [DecidableEq index]
    (support : Finset index) (weight value : index → ℝ)
    (hnonneg : ∀ i ∈ support, 0 ≤ weight i) (hmass : 0 < ∑ i ∈ support, weight i) :
    ∃ i ∈ support, 0 < weight i ∧
      (∑ i ∈ support, weight i * value i) / (∑ i ∈ support, weight i) ≤ value i := by
  classical
  set total := ∑ i ∈ support, weight i with htotal
  set paired := ∑ i ∈ support, weight i * value i with hpaired
  set active := support.filter (fun i => 0 < weight i) with hactive
  have hzero : ∀ i ∈ support, i ∉ active → weight i = 0 := by
    intro i hmem hnot
    have hnotpos : ¬ (0 < weight i) := fun hpos => hnot (Finset.mem_filter.mpr ⟨hmem, hpos⟩)
    linarith [hnonneg i hmem, not_lt.mp hnotpos]
  have hactivemass : ∑ i ∈ active, weight i = total := by
    rw [htotal]
    exact Finset.sum_subset (Finset.filter_subset (fun i => 0 < weight i) support) hzero
  have hactivepaired : ∑ i ∈ active, weight i * value i = paired := by
    rw [hpaired]
    refine Finset.sum_subset (Finset.filter_subset (fun i => 0 < weight i) support) ?_
    intro i hmem hnot
    rw [hzero i hmem hnot, zero_mul]
  have hne : active.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hactivemass
    exact absurd hactivemass.symm hmass.ne'
  have hcompare : ∑ i ∈ active, weight i * (paired / total)
      ≤ ∑ i ∈ active, weight i * value i := by
    have hcancel : total * (paired / total) = paired := by field_simp
    rw [hactivepaired, ← Finset.sum_mul, hactivemass]
    exact le_of_eq hcancel
  obtain ⟨i, hmem, hle⟩ := Finset.exists_le_of_sum_le hne hcompare
  exact ⟨i, (Finset.filter_subset (fun i => 0 < weight i) support) hmem,
    (Finset.mem_filter.mp hmem).2,
    le_of_mul_le_mul_left hle (Finset.mem_filter.mp hmem).2⟩

/-- **THE BALANCED PIGEONHOLE.**  Against ANY probe, some subset IN THE SUPPORT of a
balanced family pairs at least the `level / size` fraction of the averaged gap.  The
gain over the plain average over all `C(size, level)` subsets is that the witness is
confined to the support -- which for a VERTEX of the balanced polytope has at most
`size` members. -/
theorem exists_mem_support_le_trace_gap (design : WeightedDesign size rank)
    {level : ℕ} (hlevel : 0 < level) (hsize : 0 < size)
    {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier)
    (probe : Matrix (Fin rank) (Fin rank) ℝ) :
    ∃ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      0 < multiplier selected ∧
      ((level : ℝ) / size)
          * Matrix.trace (probe * ∑ atomIndex,
              (1 - ((size : ℝ) / level) * design.weight atomIndex)
                • atomMatrix (design.atom atomIndex))
        ≤ Matrix.trace (probe * (subsetSum design selected - 1)) := by
  classical
  have hmass : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      multiplier selected = (size : ℝ) / level :=
    sum_isBalancedSubsetMultiplier hlevel hbalanced
  have hmasspos : (0 : ℝ) < (size : ℝ) / level := by
    have hsizepos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
    have hlevelpos : (0 : ℝ) < (level : ℝ) := by exact_mod_cast hlevel
    positivity
  have hpairedsum : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      multiplier selected * Matrix.trace (probe * (subsetSum design selected - 1))
      = Matrix.trace (probe * ∑ atomIndex,
          (1 - ((size : ℝ) / level) * design.weight atomIndex)
            • atomMatrix (design.atom atomIndex)) := by
    rw [← sum_smul_gap_isBalancedSubsetMultiplier design hlevel hbalanced, Finset.mul_sum,
      Matrix.trace_sum]
    exact Finset.sum_congr rfl fun selected _ => by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  obtain ⟨selected, hmem, hpos, hle⟩ :=
    exists_pos_weight_mean_le ((Finset.univ : Finset (Fin size)).powersetCard level) multiplier
      (fun selected => Matrix.trace (probe * (subsetSum design selected - 1)))
      hbalanced.1 (by rw [hmass]; exact hmasspos)
  refine ⟨selected, hmem, hpos, le_trans ?_ hle⟩
  rw [hmass, hpairedsum]
  have hsizene : (size : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hsize.ne'
  have hlevelne : (level : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hlevel.ne'
  field_simp
  exact le_refl _

/-! ## Complementation duality -/

/-- **THE COMPLEMENTATION DUALITY.**  Complementing every subset and rescaling by
`level / (size - level)` carries balanced families on the `level`-layer to balanced
families on the `(size - level)`-layer, so the two balanced polytopes are linearly
isomorphic.  At `size = 2 * level` the scale is one and the layer is carried to
itself -- which at a Veronese top happens only at rank three, so nothing downstream
may lean on it (B7). -/
theorem isBalancedSubsetMultiplier_compl {level : ℕ} (hlevel : 0 < level) (hlt : level < size)
    {multiplier : Finset (Fin size) → ℝ}
    (hbalanced : IsBalancedSubsetMultiplier level multiplier) :
    IsBalancedSubsetMultiplier (size - level)
      (fun selected => ((level : ℝ) / ((size : ℝ) - level)) * multiplier selectedᶜ) := by
  classical
  have hgap : (0 : ℝ) < (size : ℝ) - level := by
    have : (level : ℝ) < (size : ℝ) := Nat.cast_lt.mpr hlt
    linarith
  have hcompl : ∀ candidate : Finset (Fin size),
      candidate ∈ (Finset.univ : Finset (Fin size)).powersetCard (size - level) →
        candidateᶜ ∈ (Finset.univ : Finset (Fin size)).powersetCard level := by
    intro candidate hmem
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_compl, (Finset.mem_powersetCard.mp hmem).2]
    simp; omega
  refine ⟨fun candidate hmem => mul_nonneg (by positivity) (hbalanced.1 _ (hcompl _ hmem)), ?_⟩
  intro atomIndex
  rw [multiplierDegree]
  have hbij : ∑ candidate ∈ ((Finset.univ : Finset (Fin size)).powersetCard (size - level)).filter
        (fun candidate => atomIndex ∈ candidate), multiplier candidateᶜ
      = ∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
        (fun selected => atomIndex ∉ selected), multiplier selected := by
    refine Finset.sum_nbij' (fun candidate => candidateᶜ) (fun selected => selectedᶜ)
      ?_ ?_ ?_ ?_ ?_
    · intro candidate hmem
      rw [Finset.mem_filter] at hmem ⊢
      exact ⟨hcompl _ hmem.1, by simpa using hmem.2⟩
    · intro selected hmem
      rw [Finset.mem_filter] at hmem ⊢
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, by simpa using hmem.2⟩
      rw [Finset.card_compl, (Finset.mem_powersetCard.mp hmem.1).2]
      simp
    · intro candidate _; simp
    · intro selected _; simp
    · intro candidate _; rfl
  rw [← Finset.mul_sum, hbij]
  have hsplit : ∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
        (fun selected => atomIndex ∉ selected), multiplier selected
      = (size : ℝ) / level - 1 := by
    have hpartition : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        multiplier selected
        = (∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
            (fun selected => atomIndex ∈ selected), multiplier selected)
          + ∑ selected ∈ ((Finset.univ : Finset (Fin size)).powersetCard level).filter
            (fun selected => atomIndex ∉ selected), multiplier selected :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hdeg := hbalanced.2 atomIndex
    rw [multiplierDegree] at hdeg
    rw [sum_isBalancedSubsetMultiplier hlevel hbalanced, hdeg] at hpartition
    linarith
  rw [hsplit]
  have hlevelne : (level : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hlevel.ne'
  field_simp

/-! ## The fractional relaxation, and GTZ as an integrality gap -/

/-- The canonical fractional certificate: the design's own weight pushed toward the
all-ones vector by the ratio `(rank - 1) / (size - 1)`. -/
noncomputable def hypersimplexRelaxationWeight (design : WeightedDesign size rank)
    (atomIndex : Fin size) : ℝ :=
  design.weight atomIndex
    + (((rank : ℝ) - 1) / ((size : ℝ) - 1)) * (1 - design.weight atomIndex)

/-- Every weight of a design is at most one.  This is the DESIGN INSTANCE of the
shipped `Gtz.weight_le_one_of_sum_one` (`Gtz/Design/CollaredCompact.lean:108`), which
states the same fact for a raw nonnegative function summing to one; it is named here
only because the tree currently re-derives it inline at
`Gtz/Reduction/Reductions.lean:103` and `Gtz/Quantitative/InteriorExclusion.lean:772`,
and the balanced layer needs it twice more.  It is a one-line consumption, not a
second proof.  (The field-generic analogue is `Gtz.fieldWeight_le_one`, which lives on
`FieldWeightedDesign` and so does not apply here.) -/
theorem weight_le_one (design : WeightedDesign size rank) (atomIndex : Fin size) :
    design.weight atomIndex ≤ 1 :=
  weight_le_one_of_sum_one design.weight_sum_one
    (fun other => (design.weight_pos other).le) atomIndex

/-- The displacement from the weights to the certificate is coordinatewise
nonnegative -- which is exactly the hypothesis of `Gtz.mem_dominationCone_of_nonneg`,
and is what makes the certificate a corollary of the landed cone layer rather than a
new argument. -/
theorem hypersimplexRelaxationWeight_sub_weight_nonneg (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (hrank : 1 ≤ rank) (atomIndex : Fin size) :
    0 ≤ hypersimplexRelaxationWeight design atomIndex - design.weight atomIndex := by
  have hsizegap : (0 : ℝ) < (size : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
    linarith
  have hratio : (0 : ℝ) ≤ ((rank : ℝ) - 1) / ((size : ℝ) - 1) := by
    have : (1 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
    positivity
  have hgap : (0 : ℝ) ≤ 1 - design.weight atomIndex := by
    linarith [weight_le_one design atomIndex]
  rw [hypersimplexRelaxationWeight]
  nlinarith [mul_nonneg hratio hgap]

/-- The certificate is a point of the hypersimplex `Delta(size, rank)`. -/
theorem hypersimplexRelaxationWeight_mem (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (hrank : 1 ≤ rank) (hle : rank ≤ size) :
    (∀ atomIndex, 0 ≤ hypersimplexRelaxationWeight design atomIndex)
      ∧ (∀ atomIndex, hypersimplexRelaxationWeight design atomIndex ≤ 1)
      ∧ ∑ atomIndex, hypersimplexRelaxationWeight design atomIndex = (rank : ℝ) := by
  have hsizegap : (0 : ℝ) < (size : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
    linarith
  have hratiole : ((rank : ℝ) - 1) / ((size : ℝ) - 1) ≤ 1 := by
    have : (rank : ℝ) ≤ (size : ℝ) := by exact_mod_cast hle
    rw [div_le_one hsizegap]; linarith
  refine ⟨fun atomIndex => ?_, fun atomIndex => ?_, ?_⟩
  · have := hypersimplexRelaxationWeight_sub_weight_nonneg design hsize hrank atomIndex
    linarith [(design.weight_pos atomIndex).le]
  · have hgap : (0 : ℝ) ≤ 1 - design.weight atomIndex := by
      linarith [weight_le_one design atomIndex]
    have hbound : ((rank : ℝ) - 1) / ((size : ℝ) - 1) * (1 - design.weight atomIndex)
        ≤ 1 * (1 - design.weight atomIndex) := mul_le_mul_of_nonneg_right hratiole hgap
    rw [hypersimplexRelaxationWeight]; linarith
  · simp only [hypersimplexRelaxationWeight]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      design.weight_sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp
    ring

/-- **THE FRACTIONAL CERTIFICATE.**  The hypersimplex point above dominates, at every
design and over every field, and the proof CONSUMES the landed
`Gtz.mem_dominationCone_of_nonneg`: the displacement from the weights is
coordinatewise nonnegative, so it lies in the domination cone, and Parseval turns
that into domination by the certificate. -/
theorem posSemidef_hypersimplexRelaxation (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (hrank : 1 ≤ rank) :
    ((∑ atomIndex, hypersimplexRelaxationWeight design atomIndex
        • atomMatrix (design.atom atomIndex)) - 1).PosSemidef := by
  have hcone : (fun atomIndex =>
      hypersimplexRelaxationWeight design atomIndex - design.weight atomIndex)
        ∈ dominationCone design :=
    mem_dominationCone_of_nonneg design
      (hypersimplexRelaxationWeight_sub_weight_nonneg design hsize hrank)
  rw [mem_dominationCone_iff] at hcone
  have hrewrite : ∑ atomIndex,
      (hypersimplexRelaxationWeight design atomIndex - design.weight atomIndex)
        • atomMatrix (design.atom atomIndex)
      = (∑ atomIndex, hypersimplexRelaxationWeight design atomIndex
          • atomMatrix (design.atom atomIndex)) - 1 := by
    rw [← design.isParseval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by rw [sub_smul]
  rwa [hrewrite] at hcone

/-- The certificate written against the full atom sum: it is the identity displaced
along the shipped positive-definite co-Parseval operator. -/
theorem hypersimplexRelaxation_eq_one_add_smul_fullExcess (design : WeightedDesign size rank) :
    (∑ atomIndex, hypersimplexRelaxationWeight design atomIndex
        • atomMatrix (design.atom atomIndex))
      = 1 + (((rank : ℝ) - 1) / ((size : ℝ) - 1)) • (subsetSum design Finset.univ - 1) := by
  have hterm : ∀ atomIndex : Fin size,
      hypersimplexRelaxationWeight design atomIndex • atomMatrix (design.atom atomIndex)
        = design.weight atomIndex • atomMatrix (design.atom atomIndex)
          + (((rank : ℝ) - 1) / ((size : ℝ) - 1))
              • ((1 - design.weight atomIndex) • atomMatrix (design.atom atomIndex)) :=
    fun atomIndex => by rw [hypersimplexRelaxationWeight, add_smul, smul_smul]
  simp only [hterm]
  rw [Finset.sum_add_distrib, design.isParseval, ← Finset.smul_sum,
    ← fullExcess_eq_coParseval design]

/-- **GTZ, AS AN INTEGRALITY STATEMENT.**  Domination by a `rank`-subset is exactly the
existence of a 0/1 point of the hypersimplex whose atom combination dominates.  Read
against `posSemidef_hypersimplexRelaxation` -- which supplies such a point in the
RELAXED polytope unconditionally -- this says the whole conjecture is the rounding
step.  The two statements share the literal expression `(sum_c w_c A_c - 1).PosSemidef`,
which is what makes the comparison a comparison of two instances of one formula; the
shipped `Gtz.gtzWeighted_iff_forall_exists_vertexDirection_mem_dominationCone` is the
same fact in displaced coordinates. -/
theorem gtzWeighted_iff_forall_exists_zeroOne_relaxation :
    GtzWeighted size rank ↔ ∀ design : WeightedDesign size rank, ∃ w : Fin size → ℝ,
      (∀ atomIndex, w atomIndex = 0 ∨ w atomIndex = 1)
        ∧ (∑ atomIndex, w atomIndex = (rank : ℝ))
        ∧ ((∑ atomIndex, w atomIndex • atomMatrix (design.atom atomIndex)) - 1).PosSemidef := by
  classical
  constructor
  · intro hgtz design
    obtain ⟨selected, hcard, hdominates⟩ := hgtz design
    refine ⟨fun atomIndex => if atomIndex ∈ selected then 1 else 0, fun atomIndex => ?_, ?_, ?_⟩
    · by_cases hmem : atomIndex ∈ selected <;> simp [hmem]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    · have hrewrite : (∑ atomIndex, (if atomIndex ∈ selected then (1 : ℝ) else 0)
          • atomMatrix (design.atom atomIndex)) = subsetSum design selected := by
        rw [subsetSum]
        simp only [ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hrewrite]; exact hdominates
  · intro hround design
    obtain ⟨w, hzeroone, hsum, hpsd⟩ := hround design
    refine ⟨Finset.univ.filter (fun atomIndex => w atomIndex = 1), ?_, ?_⟩
    · have hcast : ((Finset.univ.filter (fun atomIndex => w atomIndex = 1)).card : ℝ)
          = (rank : ℝ) := by
        rw [← hsum, Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rcases hzeroone atomIndex with hzero | hone
        · simp [hzero]
        · simp [hone]
      exact_mod_cast hcast
    · have hrewrite : subsetSum design (Finset.univ.filter (fun atomIndex => w atomIndex = 1))
          = ∑ atomIndex, w atomIndex • atomMatrix (design.atom atomIndex) := by
        rw [subsetSum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun atomIndex => w atomIndex = 1)
          (fun atomIndex => w atomIndex • atomMatrix (design.atom atomIndex))]
        have hone : ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => w atomIndex = 1),
            w atomIndex • atomMatrix (design.atom atomIndex)
            = ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => w atomIndex = 1),
              atomMatrix (design.atom atomIndex) :=
          Finset.sum_congr rfl fun atomIndex hmem => by
            rw [(Finset.mem_filter.mp hmem).2, one_smul]
        have hzero : ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => ¬ w atomIndex = 1),
            w atomIndex • atomMatrix (design.atom atomIndex) = 0 :=
          Finset.sum_eq_zero fun atomIndex hmem => by
            rcases hzeroone atomIndex with hz | ho
            · rw [hz, zero_smul]
            · exact absurd ho (Finset.mem_filter.mp hmem).2
        rw [hone, hzero, add_zero]
      rw [Dominates, hrewrite]; exact hpsd

/-! ## The bridge to the product mixtures

`Gtz/Quantitative/MixtureAggregates.lean` weights the `rank`-subsets by a PRODUCT
`prod_{c in C} v_c`.  That is a multiplier, so the master identity applies to it, and
the three statements below are the exact junction between the two layers.  They also
make precise why the families are different: a product multiplier is balanced only on
the solution set of `v_c * e_{level-1}(v off c) = 1`, which is a genuine system of
`size` equations and not a normalisation. -/

/-- **THE DEGREE OF A PRODUCT MULTIPLIER** is the atom's own weight times the
elementary symmetric function of the others.  This is the dictionary entry between
the per-subset PRODUCT weighting of `Gtz.productMixture` / `Gtz.gapMinorAggregate`
and the per-atom DEGREE condition that defines balance. -/
theorem multiplierDegree_weightProduct (level : ℕ) (hlevel : 0 < level)
    (weight : Fin size → ℝ) (atomIndex : Fin size) :
    multiplierDegree level (fun selected => ∏ index ∈ selected, weight index) atomIndex
      = weight atomIndex
        * ∑ rest ∈ (Finset.univ.erase atomIndex).powersetCard (level - 1),
            ∏ index ∈ rest, weight index := by
  classical
  rw [multiplierDegree, Finset.mul_sum]
  refine Finset.sum_nbij' (fun selected => selected.erase atomIndex)
    (fun rest => insert atomIndex rest) ?_ ?_ ?_ ?_ ?_
  · intro selected hselected
    rw [Finset.mem_filter] at hselected
    obtain ⟨hmem, hin⟩ := hselected
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem hin, (Finset.mem_powersetCard.mp hmem).2]
  · intro rest hrest
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hrest
    have hnotmem : atomIndex ∉ rest := fun hc => (Finset.mem_erase.mp (hsub hc)).1 rfl
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hnotmem, hcard]
    omega
  · intro selected hselected
    rw [Finset.mem_filter] at hselected
    exact Finset.insert_erase hselected.2
  · intro rest hrest
    obtain ⟨hsub, _⟩ := Finset.mem_powersetCard.mp hrest
    have hnotmem : atomIndex ∉ rest := fun hc => (Finset.mem_erase.mp (hsub hc)).1 rfl
    exact Finset.erase_insert hnotmem
  · intro selected hselected
    rw [Finset.mem_filter] at hselected
    rw [← Finset.mul_prod_erase _ _ hselected.2]

/-- **THE MATRIX AGGREGATE OF A PRODUCT MIXTURE COLLAPSES.**  The master identity at
the product multiplier: however the mixture weights the subsets, the resulting
combination of atom sums is a per-atom reweighting whose coefficients are the
elementary symmetric functions above.  The determinant-level aggregates of
`Gtz.gapMinorAggregate` do NOT collapse this way -- that is the whole difference
between the matrix layer and the coefficient layer. -/
theorem sum_weightProduct_smul_subsetSum_eq (design : WeightedDesign size rank) (level : ℕ)
    (hlevel : 0 < level) (weight : Fin size → ℝ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
        (∏ index ∈ selected, weight index) • subsetSum design selected
      = ∑ atomIndex, (weight atomIndex
          * ∑ rest ∈ (Finset.univ.erase atomIndex).powersetCard (level - 1),
              ∏ index ∈ rest, weight index)
          • atomMatrix (design.atom atomIndex) := by
  rw [sum_smul_subsetSum_eq_sum_multiplierDegree_smul design level
    (fun selected => ∏ index ∈ selected, weight index)]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [multiplierDegree_weightProduct level hlevel weight atomIndex]

/-- **WHERE THE TWO FAMILIES MEET.**  A nonnegative product multiplier is balanced
exactly on the solution set of `v_c * e_{level-1}(v off c) = 1` -- one equation per
atom.  So "product" and "balanced" are transverse conditions, not reparametrisations
of each other, and no product mixture is balanced by construction. -/
theorem isBalancedSubsetMultiplier_weightProduct_iff (level : ℕ) (hlevel : 0 < level)
    {weight : Fin size → ℝ} (hnonneg : ∀ atomIndex, 0 ≤ weight atomIndex) :
    IsBalancedSubsetMultiplier level (fun selected => ∏ index ∈ selected, weight index)
      ↔ ∀ atomIndex, weight atomIndex
          * ∑ rest ∈ (Finset.univ.erase atomIndex).powersetCard (level - 1),
              ∏ index ∈ rest, weight index = 1 := by
  constructor
  · intro hbalanced atomIndex
    rw [← multiplierDegree_weightProduct level hlevel weight atomIndex]
    exact hbalanced.2 atomIndex
  · intro hdegree
    refine ⟨fun selected _ => Finset.prod_nonneg fun index _ => hnonneg index, fun atomIndex => ?_⟩
    rw [multiplierDegree_weightProduct level hlevel weight atomIndex]
    exact hdegree atomIndex

/-! ## Non-vacuity firing controls -/

/-- **FIRING CONTROL** for `posSemidef_sum_smul_gap_of_le_multiplierDegree` (precedent
P4: vacuous hypotheses compile).  At `(6,3)` the CONSTANT multiplier satisfies the
hypothesis on every design whose weights are at most `1/2`: its degree is `10 * level`
by the shipped `Gtz.card_powersetCard_three_through_atom` and its mass is `20 * level`
by `Gtz.card_powersetCard_three_sixThree`, so the hypothesis reads `20 t <= 10`.  The
PSD lemma therefore has a nonzero non-degenerate instance. -/
theorem le_multiplierDegree_constant_sixThree (design : WeightedDesign 6 3) (level : ℝ)
    (hlevel : 0 ≤ level) (hweight : ∀ atomIndex, design.weight atomIndex ≤ 1 / 2) :
    ∀ atomIndex,
      (∑ _selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, level)
          * design.weight atomIndex
        ≤ multiplierDegree 3 (fun _ => level) atomIndex := by
  intro atomIndex
  have hmass : (∑ _selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, level)
      = 20 * level := by
    rw [Finset.sum_const, card_powersetCard_three_sixThree, nsmul_eq_mul]
    norm_num
  have hdegree : multiplierDegree 3 (fun _ => level) atomIndex = 10 * level := by
    rw [multiplierDegree, Finset.sum_const, card_powersetCard_three_through_atom,
      nsmul_eq_mul]
    norm_num
  rw [hmass, hdegree]
  nlinarith [hweight atomIndex, (design.weight_pos atomIndex).le, hlevel]

/-- **FIRING CONTROL** for the balanced predicate itself: the uniform family at `(6,3)`
is balanced with the explicit value `1/10`, so `IsBalancedSubsetMultiplier` is
inhabited at the cell and every balanced statement above has a witness there. -/
theorem isBalancedSubsetMultiplier_uniform_sixThree :
    IsBalancedSubsetMultiplier (size := 6) 3 (fun _ => (10 : ℝ)⁻¹) := by
  have huniform := isBalancedSubsetMultiplier_uniform (size := 6) 3 (by norm_num) (by norm_num)
  norm_num at huniform
  exact huniform

end Gtz

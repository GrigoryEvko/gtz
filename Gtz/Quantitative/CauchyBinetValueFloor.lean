/-
# FLOOR-CB — the Cauchy–Binet floor on the chart value

The shipped floor on the value of an admissible chart stationarity datum is
`Gtz.neg_inv_size_le_value_of_isChartStationaryData`, namely `-1/size ≤ value`,
obtained by summing the weight floor `-value ≤ t_c` against `Σ t_c = 1`.  This file
replaces it by

    `value ≥ -(1/size) (1 - 1/C(size - 1, rank - 1))` ,

which is `-3/20` at `(6,3)`, `-2/15` at `(7,3)`, `-5/42` at `(8,3)`, `-3/28` at
`(9,3)`, `-3/20` at `(6,4)` and `-19/140` at `(7,4)`.  The improvement over `-1/size`
is EXACTLY `1/(size · C(size - 1, rank - 1))` — recorded as an identity in
`cauchyBinetValueFloor_sub_neg_inv_size_eq` — hence strictly positive at every
`1 ≤ rank ≤ size`, with no cell excluded and no strictness side condition.

## The argument, in the order the file mechanizes it

Everything rests on ONE per-subset inequality, and everything after it is a sum.

1.  **The block is a contraction.**  A design's chart `P = V Vᵀ` and its complement
    `1 - P` are both symmetric idempotents, hence both positive semidefinite, and
    both stay so after restriction to a subset.  So the block `P[C]` satisfies
    `0 ⪯ P[C] ⪯ 1` (`posSemidef_projectionOfDesign`,
    `posSemidef_one_sub_projectionOfDesign`).
2.  **A contraction's determinant sits below every Rayleigh quotient**
    (`det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub`): all eigenvalues
    lie in `[0,1]`, so `det = λ_min · (the rest) ≤ λ_min`, and `λ_min ≤ ⟨u, A u⟩` at a
    unit probe.  The Loewner shift `A - (det A)·1 ⪰ 0` does the second half, so the
    only spectral input is the shipped dictionary of
    `Gtz.Reduction.ExchangeInvariant` — no diagonalization is touched here.
3.  **C1-A, the per-subset cap** (`shadowDeterminant_le_of_isChartArgmaxValue`):
    admissibility hands every `rank`-subset a unit probe supported there with
    `⟨u, W u⟩ ≤ value`, and `⟨u, P u⟩ = ⟨u, W u⟩ + Σ_c t_c u_c²`, so

        `det P[C] ≤ Σ_{c ∈ C} (t_c + value) u_c² ≤ max_{c ∈ C} (t_c + value)` .

    This step needs NEITHER the weight floor NOR any sign condition: it is stated
    against an arbitrary cap on `t_c + value` over the subset, which is the max in
    universal-property form, and `sup'` is recovered in
    `shadowDeterminant_le_sup'_weight_add_value_of_isChartArgmaxValue`.
4.  **The sum** (`cauchyBinetValueFloor_le_value_of_isChartArgmaxValue`): with the
    weight floor `τ_c := t_c + value ≥ 0` the cap may be taken to be `Σ_{c ∈ C} τ_c`,
    and Cauchy–Binet `Σ_C det P[C] = 1` (`Gtz.sum_shadowDeterminant_eq_one`) against
    the double count `Σ_C Σ_{c ∈ C} τ_c = C(size-1, rank-1) · Σ_c τ_c` gives
    `1 ≤ C(size-1, rank-1) · (1 + size · value)`.

## The exact hypotheses, so the reach is not overstated

`cauchyBinetValueFloor_le_value_of_isChartArgmaxValue`, which is the floor proper,
consumes exactly three things: the DESIGN behind the chart (because Cauchy–Binet is
imported, not re-derived — the same reason
`Gtz.not_isChartStationaryData_of_value_eq_neg_inv_size` carries one), the shipped
admissibility field `Gtz.IsChartArgmaxValue`, and TWO raw inequalities on the weights,
`-value ≤ t_c` and `Σ t_c = 1`, taken as hypotheses rather than read off a bundle.  It
does not assume uniform weights, general position or strict positivity, and it does
not assume the rank is positive — admissibility is unsatisfiable at `rank = 0`, which
is `rank_pos_of_isChartArgmaxValue`.  Only the derived
`cauchyBinetValueFloor_le_value_of_isChartStationaryData` mentions the stationarity
bundle at all, and it mentions it in exactly two places: the shipped
`Gtz.weight_ge_neg_value_of_isChartStationaryData` for the first inequality (which is
where the bundle's own fields are spent, inside that lemma and not here) and
`weight_sum_one` for the second.  Nothing in the argument is specific to `ℝ` beyond
the ambient formalization; the Hermitian reading is verbatim.

## Why this is load-bearing, and exactly how much it buys

`Gtz.Quantitative.ChartEmptinessCertificate` closes the negative-value half of the
repeated-weight branch of the two-block partition class — the class of two
complementary triples, the one the paper's third-symmetric-function corollary sets
aside — and its payoff theorem
`Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_flooredNegativeValue`
carries TWO undischarged hypotheses: the numeric floor `-(3/20) ≤ value`, and
`Gtz.EliminatesChartTwoBlockValue`.  The floor here discharges the FIRST of the two
(`not_isChartStationaryData_of_isChartTwoBlockFamily_of_negativeValue`), and that is
the whole of the increment.  The elimination step remains an assumption this
development does not discharge, so the class closure remains conditional; the claim
"unconditional" is not made anywhere below and would be false.

That the floor is load-bearing at all is a theorem of that file:
`Gtz.not_flooredWindow_neg_inv_six` says `-1/6 < -3/20`, and the eliminant VANISHES at
`-1/6`, so the shipped `-1/size` window admits a root and the Handelman certificate
cannot be run on it.  The window at `(6,3)` narrows from `(-1/6, 0)` to `[-3/20, 0)`.

## What this does NOT do

* It closes no covering class.  A floor is class-independent — it constrains every
  datum equally and excludes no family — so it shrinks the window in which all the
  classes of the covering census must still be examined and does nothing else.
* It reaches nothing at `value ≥ 0`.  `GTZ(6,3)` and `GTZ(7,3)` are exactly as open
  after this file as before it.
* It is not the sharp constant of its own method.  Replacing "the other eigenvalues
  are at most one" by "their product is one term of `e_{rank-1}`" gives
  `value ≥ -(1/size)(1 - 1/((size-rank)(rank-1) + rank))`, i.e. `-4/27` at `(6,3)` and
  `-10/77` at `(7,3)`, and the crossover between the two counts falls exactly on
  `(6,3)`.  That sharpening needs the per-index marginal `Σ_{C ∋ c} det P[C] = P_cc`
  at subset size `rank - 1` — `Gtz.IsProjectionOnePointMarginal`, which this
  development still carries as a hypothesis — and is deliberately NOT attempted here.
  Outside Lean, three independent tightenings of this family all stop at the same
  concentrated corner (all the mass `τ` on one atom, at leverage one), which satisfies
  each of them with EQUALITY; so `-4/27` reads as the sharp constant of the
  first-moment method rather than as a way station.  That is quoted arithmetic, not a
  theorem of this development, and nothing below depends on it.
-/
import Mathlib
import Gtz.Quantitative.ChartEmptinessCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Support bookkeeping

Two collapses used throughout: a sum over all atoms restricts to the support of the
probe, and a sum over a subset is a sum along any injective enumeration of it. -/

section Support

variable {size rank : ℕ}

/-- A sum of a summand that vanishes off a subset is the sum over that subset. -/
theorem sum_eq_sum_of_vanishes_offSubset {selected : Finset (Fin size)}
    (summand : Fin size → ℝ)
    (hvanishes : ∀ atomIndex : Fin size, atomIndex ∉ selected → summand atomIndex = 0) :
    ∑ atomIndex : Fin size, summand atomIndex = ∑ atomIndex ∈ selected, summand atomIndex :=
  (Finset.sum_subset (Finset.subset_univ selected)
    fun atomIndex _ hnotMem => hvanishes atomIndex hnotMem).symm

/-- A sum over a subset is the sum along any injective enumeration of it. -/
theorem sum_selected_eq_sum_pick {selected : Finset (Fin size)} (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected) (summand : Fin size → ℝ) :
    ∑ atomIndex ∈ selected, summand atomIndex
      = ∑ selectedIndex : Fin rank, summand (pick selectedIndex) := by
  classical
  rw [← himage, Finset.sum_image fun first _ second _ hpair => hinjective hpair]

end Support

/-! ## A contraction's determinant sits below every Rayleigh quotient

The one spectral step of the file.  Both halves are read off the shipped Loewner /
spectrum dictionary of `Gtz.Reduction.ExchangeInvariant`; no diagonalization appears. -/

section Contraction

variable {dim : ℕ}

/-- **The eigenvalue ceiling.**  If `1 - A` is positive semidefinite then every
eigenvalue of `A` is at most one — read off the eigenvector itself, exactly as
`Gtz.eigenvalue_ge_of_posSemidef_sub_smul_one` reads off the floor: the shifted
matrix sends it to `(1 - lambda)` times itself, the quadratic form there is
nonnegative, and the eigenvector has positive length. -/
theorem eigenvalue_le_one_of_posSemidef_one_sub {form : Matrix (Fin dim) (Fin dim) ℝ}
    (hHermitian : form.IsHermitian)
    (hcontraction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef)
    (eigenIndex : Fin dim) : hHermitian.eigenvalues eigenIndex ≤ 1 := by
  set eigenVector : Fin dim → ℝ := ⇑(hHermitian.eigenvectorBasis eigenIndex) with heigenVector
  have hnonzero : eigenVector ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 (hHermitian.eigenvectorBasis.orthonormal.ne_zero eigenIndex)
  have haction : form *ᵥ eigenVector = (hHermitian.eigenvalues eigenIndex) • eigenVector :=
    hHermitian.mulVec_eigenvectorBasis eigenIndex
  have hshiftAction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form) *ᵥ eigenVector
      = (1 - hHermitian.eigenvalues eigenIndex) • eigenVector := by
    rw [Matrix.sub_mulVec, haction, Matrix.one_mulVec, sub_smul, one_smul]
  have hquadratic := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hcontraction).2 eigenVector
  rw [star_trivial, hshiftAction, dotProduct_smul, smul_eq_mul] at hquadratic
  have hlengthPos : 0 < eigenVector ⬝ᵥ eigenVector := dotProduct_self_pos hnonzero
  nlinarith [hquadratic, hlengthPos]

/-- **The determinant is below every eigenvalue** of a contraction: the determinant
is the product of the eigenvalues, all of which lie in `[0,1]`, so factoring out any
one of them leaves a product of numbers in `[0,1]`. -/
theorem det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hpsd : form.PosSemidef)
    (hcontraction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef)
    (eigenIndex : Fin dim) : form.det ≤ hpsd.1.eigenvalues eigenIndex := by
  have hdet : form.det = ∏ otherIndex : Fin dim, hpsd.1.eigenvalues otherIndex := by
    simpa using hpsd.1.det_eq_prod_eigenvalues
  have hrestNonneg : 0 ≤ ∏ otherIndex ∈ Finset.univ.erase eigenIndex,
      hpsd.1.eigenvalues otherIndex :=
    Finset.prod_nonneg fun otherIndex _ => hpsd.eigenvalues_nonneg otherIndex
  have hrestLeOne : ∏ otherIndex ∈ Finset.univ.erase eigenIndex,
      hpsd.1.eigenvalues otherIndex ≤ 1 :=
    Finset.prod_le_one (fun otherIndex _ => hpsd.eigenvalues_nonneg otherIndex)
      fun otherIndex _ => eigenvalue_le_one_of_posSemidef_one_sub hpsd.1 hcontraction otherIndex
  rw [hdet, ← Finset.mul_prod_erase _ _ (Finset.mem_univ eigenIndex)]
  nlinarith [hpsd.eigenvalues_nonneg eigenIndex]

/-- **THE SPECTRAL STEP.**  For `0 ⪯ A ⪯ 1` and a unit probe, `det A ≤ ⟨u, A u⟩`.

The determinant is below every eigenvalue, so the Loewner shift `A - (det A)·1` is
positive semidefinite by the shipped eigenvalue criterion, and its quadratic form at
a unit probe is `⟨u, A u⟩ - det A ≥ 0`. -/
theorem det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hpsd : form.PosSemidef)
    (hcontraction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef)
    {probe : Fin dim → ℝ} (hunit : probe ⬝ᵥ probe = 1) :
    form.det ≤ probe ⬝ᵥ (form *ᵥ probe) := by
  have hshift := posSemidef_sub_smul_one_of_eigenvalue_ge hpsd.1 form.det
    fun eigenIndex =>
      det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub hpsd hcontraction eigenIndex
  have hquadratic := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hshift).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul, hunit, mul_one] at hquadratic
  linarith

end Contraction

/-! ## The chart and its complement are positive semidefinite -/

section ChartBlock

variable {size rank : ℕ}

/-- The chart of a design is positive semidefinite: it is `V Vᵀ`. -/
theorem posSemidef_projectionOfDesign (design : WeightedDesign size rank) :
    (projectionOfDesign design).PosSemidef := by
  have hgram := Matrix.posSemidef_self_mul_conjTranspose (scaledAtomRows design)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, ← projectionOfDesign] at hgram

/-- The complementary chart `1 - P` is positive semidefinite: it is again a symmetric
idempotent, so it factors as `(1 - P)(1 - P)ᵀ`. -/
theorem posSemidef_one_sub_projectionOfDesign (design : WeightedDesign size rank) :
    ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design).PosSemidef := by
  have hsymmetric : ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design)ᵀ
      = 1 - projectionOfDesign design := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, projectionOfDesign_transpose]
  have hidempotent :
      ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design)
          * ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design)
        = 1 - projectionOfDesign design := by
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, projectionOfDesign_mul_self, sub_self,
      sub_zero]
  have hgram := Matrix.posSemidef_self_mul_conjTranspose
    ((1 : Matrix (Fin size) (Fin size) ℝ) - projectionOfDesign design)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hsymmetric, hidempotent] at hgram

/-- **The shadow determinant is below every Rayleigh quotient of the chart at a unit
probe supported on the subset.**  The block `P[C]` is a contraction, so the spectral
step applies to it, and both sides transport along an injective enumeration of the
subset because the probe vanishes off it. -/
theorem shadowDeterminant_le_dotProduct_mulVec_of_pick (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = selected)
    {probe : Fin size → ℝ} (hunit : probe ⬝ᵥ probe = 1)
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ selected → probe atomIndex = 0) :
    shadowDeterminant design selected ≤ probe ⬝ᵥ (projectionOfDesign design *ᵥ probe) := by
  classical
  have hblockPsd : ((projectionOfDesign design).submatrix pick pick).PosSemidef :=
    (posSemidef_projectionOfDesign design).submatrix pick
  have hblockContraction : ((1 : Matrix (Fin rank) (Fin rank) ℝ)
      - (projectionOfDesign design).submatrix pick pick).PosSemidef := by
    have hcomplement := (posSemidef_one_sub_projectionOfDesign design).submatrix pick
    have hsplit : ((1 : Matrix (Fin size) (Fin size) ℝ)
          - projectionOfDesign design).submatrix pick pick
        = (1 : Matrix (Fin size) (Fin size) ℝ).submatrix pick pick
          - (projectionOfDesign design).submatrix pick pick := rfl
    rwa [hsplit, Matrix.submatrix_one pick hinjective] at hcomplement
  have hblockUnit : (fun selectedIndex : Fin rank => probe (pick selectedIndex))
      ⬝ᵥ (fun selectedIndex : Fin rank => probe (pick selectedIndex)) = 1 := by
    rw [dotProduct, ← sum_selected_eq_sum_pick pick hinjective himage
        fun atomIndex => probe atomIndex * probe atomIndex,
      ← sum_eq_sum_of_vanishes_offSubset (fun atomIndex => probe atomIndex * probe atomIndex)
        fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem, mul_zero]]
    exact hunit
  have hrow : ∀ selectedIndex : Fin rank,
      ((projectionOfDesign design).submatrix pick pick
          *ᵥ fun otherIndex : Fin rank => probe (pick otherIndex)) selectedIndex
        = (projectionOfDesign design *ᵥ probe) (pick selectedIndex) := by
    intro selectedIndex
    have hcollapse := (sum_eq_sum_of_vanishes_offSubset
      (fun atomIndex => projectionOfDesign design (pick selectedIndex) atomIndex * probe atomIndex)
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem, mul_zero]).trans
      (sum_selected_eq_sum_pick pick hinjective himage _)
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] using hcollapse.symm
  have hrayleigh : (fun selectedIndex : Fin rank => probe (pick selectedIndex))
        ⬝ᵥ ((projectionOfDesign design).submatrix pick pick
          *ᵥ fun selectedIndex : Fin rank => probe (pick selectedIndex))
      = probe ⬝ᵥ (projectionOfDesign design *ᵥ probe) := by
    rw [dotProduct, Finset.sum_congr rfl fun selectedIndex _ => by rw [hrow selectedIndex],
      ← sum_selected_eq_sum_pick pick hinjective himage
        fun atomIndex => probe atomIndex * (projectionOfDesign design *ᵥ probe) atomIndex,
      ← sum_eq_sum_of_vanishes_offSubset
        (fun atomIndex => probe atomIndex * (projectionOfDesign design *ᵥ probe) atomIndex)
        fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem, zero_mul]]
    rfl
  rw [shadowDeterminant_eq_det_submatrix design pick hinjective himage, ← hrayleigh]
  exact det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub hblockPsd hblockContraction
    hblockUnit

/-- The same, indexed by the subset itself through its order embedding. -/
theorem shadowDeterminant_le_dotProduct_mulVec_of_support (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {probe : Fin size → ℝ} (hunit : probe ⬝ᵥ probe = 1)
    (hsupport : ∀ atomIndex : Fin size, atomIndex ∉ selected → probe atomIndex = 0) :
    shadowDeterminant design selected ≤ probe ⬝ᵥ (projectionOfDesign design *ᵥ probe) :=
  shadowDeterminant_le_dotProduct_mulVec_of_pick design _
    (selected.orderEmbOfFin hcard).injective (image_orderEmbOfFin hcard) hunit hsupport

end ChartBlock

/-! ## C1-A: the per-subset cap -/

section PerSubset

variable {size rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ}

/-- **Admissibility is unsatisfiable at rank zero**, so no positivity hypothesis on
the rank is needed anywhere below: the empty subset would have to carry a unit probe
supported inside it. -/
theorem rank_pos_of_isChartArgmaxValue
    (hargmax : IsChartArgmaxValue rank projection weight value) : 0 < rank := by
  rcases Nat.eq_zero_or_pos rank with hzero | hpos
  · exfalso
    obtain ⟨probe, hunit, hsupport, -⟩ := hargmax ∅ (by rw [Finset.card_empty, hzero])
    have hvanishes : probe = 0 :=
      funext fun atomIndex => hsupport atomIndex (Finset.notMem_empty atomIndex)
    rw [hvanishes, zero_dotProduct] at hunit
    exact absurd hunit (by norm_num)
  · exact hpos

/-- **C1-A, THE PER-SUBSET CAP.**  At an admissible value, the shadow determinant of
every `rank`-subset is at most any upper bound of `t_c + value` over that subset:

    `det P[C] ≤ max_{c ∈ C} (t_c + value)` ,

stated against an arbitrary cap so that the maximum is not needed as a gadget and the
degenerate subset is not a special case.

Neither the weight floor nor any sign condition enters, and neither does any field of
`Gtz.IsChartStationaryData`.  The only inputs are the design behind the chart (through
`0 ⪯ P[C] ⪯ 1`) and admissibility.  Everything else in this file is a sum over this
inequality. -/
theorem shadowDeterminant_le_of_isChartArgmaxValue (design : WeightedDesign size rank)
    (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) {capValue : ℝ}
    (hcap : ∀ atomIndex ∈ selected, weight atomIndex + value ≤ capValue) :
    shadowDeterminant design selected ≤ capValue := by
  obtain ⟨probe, hunit, hsupport, hquotient⟩ := hargmax selected hcard
  have hprobeMass : ∑ atomIndex ∈ selected, probe atomIndex ^ 2 = 1 := by
    rw [← sum_eq_sum_of_vanishes_offSubset (fun atomIndex => probe atomIndex ^ 2)
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem]; ring,
      ← dotProduct_self_eq_sum_sq]
    exact hunit
  have hsplit : probe ⬝ᵥ (projection *ᵥ probe)
      = probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
        + ∑ atomIndex : Fin size, weight atomIndex * probe atomIndex ^ 2 := by
    have hdiagonal : probe ⬝ᵥ (Matrix.diagonal weight *ᵥ probe)
        = ∑ atomIndex : Fin size, weight atomIndex * probe atomIndex ^ 2 :=
      Finset.sum_congr rfl fun atomIndex _ => by rw [Matrix.mulVec_diagonal]; ring
    rw [chartStationaryGap, Matrix.sub_mulVec, dotProduct_sub, hdiagonal]
    ring
  have hweightMass : ∑ atomIndex : Fin size, weight atomIndex * probe atomIndex ^ 2
      = ∑ atomIndex ∈ selected, weight atomIndex * probe atomIndex ^ 2 :=
    sum_eq_sum_of_vanishes_offSubset _
      fun atomIndex hnotMem => by rw [hsupport atomIndex hnotMem]; ring
  have hweighted : probe ⬝ᵥ (projection *ᵥ probe)
      ≤ ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2 := by
    have hexpand : ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2
        = (∑ atomIndex ∈ selected, weight atomIndex * probe atomIndex ^ 2)
          + value * ∑ atomIndex ∈ selected, probe atomIndex ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, hweightMass, hexpand, hprobeMass, mul_one]
    linarith
  have hcapped : ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2
      ≤ capValue := by
    have hterms : ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2
        ≤ ∑ atomIndex ∈ selected, capValue * probe atomIndex ^ 2 :=
      Finset.sum_le_sum fun atomIndex hmem =>
        mul_le_mul_of_nonneg_right (hcap atomIndex hmem) (sq_nonneg _)
    rwa [← Finset.mul_sum, hprobeMass, mul_one] at hterms
  calc shadowDeterminant design selected
      ≤ probe ⬝ᵥ (projectionOfDesign design *ᵥ probe) :=
        shadowDeterminant_le_dotProduct_mulVec_of_support design hcard hunit hsupport
    _ = probe ⬝ᵥ (projection *ᵥ probe) := by rw [hchart]
    _ ≤ ∑ atomIndex ∈ selected, (weight atomIndex + value) * probe atomIndex ^ 2 := hweighted
    _ ≤ capValue := hcapped

/-- **C1-A with the maximum spelled out.**  On a nonempty subset the cap may be taken
to be the maximum itself. -/
theorem shadowDeterminant_le_sup'_weight_add_value_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hnonempty : selected.Nonempty) :
    shadowDeterminant design selected
      ≤ selected.sup' hnonempty fun atomIndex => weight atomIndex + value :=
  shadowDeterminant_le_of_isChartArgmaxValue design hchart hargmax hcard
    fun _atomIndex hmem =>
      Finset.le_sup' (fun otherIndex => weight otherIndex + value) hmem

end PerSubset

/-! ## The double count -/

/-- **Every atom lies in `C(size - 1, rank - 1)` of the `rank`-subsets**, so summing a
per-atom quantity over the atoms of each subset and then over the subsets multiplies
the total by that binomial.  Positive rank is genuinely needed: at `rank = 0` the left
side is empty and the right side is not. -/
theorem sum_powersetCard_sum_mem_eq_choose_mul_sum {size : ℕ} (rank : ℕ) (hrank : 0 < rank)
    (summand : Fin size → ℝ) :
    ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
        ∑ atomIndex ∈ selected, summand atomIndex
      = (((size - 1).choose (rank - 1) : ℕ) : ℝ) * ∑ atomIndex : Fin size, summand atomIndex := by
  classical
  have hrestrict : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      ∑ atomIndex ∈ selected, summand atomIndex
        = ∑ atomIndex : Fin size, if atomIndex ∈ selected then summand atomIndex else 0 := by
    intro selected _
    rw [← Finset.sum_filter, Finset.filter_univ_mem]
  have hcount : ∀ atomIndex : Fin size,
      ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
          (if atomIndex ∈ selected then summand atomIndex else 0)
        = (((size - 1).choose (rank - 1) : ℕ) : ℝ) * summand atomIndex := by
    intro atomIndex
    have hfilterEq : ((Finset.univ : Finset (Fin size)).powersetCard rank).filter
          (fun selected => atomIndex ∈ selected)
        = ((Finset.univ : Finset (Fin size)).powersetCard rank).filter
          (fun selected => ({atomIndex} : Finset (Fin size)) ⊆ selected) :=
      Finset.filter_congr fun selected _ => by simp
    have hcardFilter : (((Finset.univ : Finset (Fin size)).powersetCard rank).filter
        (fun selected => atomIndex ∈ selected)).card = (size - 1).choose (rank - 1) := by
      rw [hfilterEq, Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
        (by rw [Finset.card_singleton]; omega), Finset.card_singleton, Finset.card_univ,
        Fintype.card_fin]
    rw [← Finset.sum_filter, Finset.sum_const, hcardFilter, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hrestrict, Finset.sum_comm,
    Finset.sum_congr rfl fun atomIndex _ => hcount atomIndex, ← Finset.mul_sum]

/-! ## C1-B: the floor -/

section Floor

variable {size rank : ℕ} {activeIndex : Type*} {projection : Matrix (Fin size) (Fin size) ℝ}
  {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE CAUCHY–BINET FLOOR** `-(1/size)(1 - 1/C(size - 1, rank - 1))`, as a
definition of a rational number.  That it IS a floor on the chart value is
`cauchyBinetValueFloor_le_value_of_isChartArgmaxValue` below. -/
noncomputable def cauchyBinetValueFloor (size rank : ℕ) : ℝ :=
  -((size : ℝ))⁻¹ * (1 - (((size - 1).choose (rank - 1) : ℕ) : ℝ)⁻¹)

/-- **The mass inequality**, which is the floor before it is solved for the value:
Cauchy–Binet against the per-subset cap and the double count. -/
theorem one_le_choose_mul_one_add_size_mul_value_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hweightFloor : ∀ atomIndex : Fin size, -value ≤ weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    1 ≤ (((size - 1).choose (rank - 1) : ℕ) : ℝ) * (1 + (size : ℝ) * value) := by
  have hrankPos := rank_pos_of_isChartArgmaxValue hargmax
  have hperSubset : ∀ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      shadowDeterminant design selected
        ≤ ∑ atomIndex ∈ selected, (weight atomIndex + value) := by
    intro selected hmemFamily
    refine shadowDeterminant_le_of_isChartArgmaxValue design hchart hargmax
      (Finset.mem_powersetCard.mp hmemFamily).2 fun atomIndex hmemSelected => ?_
    exact Finset.single_le_sum (f := fun otherIndex => weight otherIndex + value)
      (fun otherIndex _ => by linarith [hweightFloor otherIndex]) hmemSelected
  have hmass : (1 : ℝ) ≤ ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      ∑ atomIndex ∈ selected, (weight atomIndex + value) := by
    rw [← sum_shadowDeterminant_eq_one design]
    exact Finset.sum_le_sum hperSubset
  rw [sum_powersetCard_sum_mem_eq_choose_mul_sum rank hrankPos] at hmass
  have htotal : ∑ atomIndex : Fin size, (weight atomIndex + value) = 1 + (size : ℝ) * value := by
    rw [Finset.sum_add_distrib, hweightSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rwa [htotal] at hmass

/-- **FLOOR-CB.**  An admissible chart value whose chart is a design's, and whose
weights obey the floor `-value ≤ t_c` and sum to one, satisfies

    `-(1/size)(1 - 1/C(size - 1, rank - 1)) ≤ value` .

The weight floor is exactly what
`Gtz.weight_ge_neg_value_of_isChartStationaryData` supplies; no other field of the
stationarity bundle is consumed, and no hypothesis on the cell is imposed. -/
theorem cauchyBinetValueFloor_le_value_of_isChartArgmaxValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hweightFloor : ∀ atomIndex : Fin size, -value ≤ weight atomIndex)
    (hweightSum : ∑ atomIndex : Fin size, weight atomIndex = 1) :
    cauchyBinetValueFloor size rank ≤ value := by
  have hrankPos := rank_pos_of_isChartArgmaxValue hargmax
  have hrankLe := rank_le_of_design design
  have hsizeCast : (0 : ℝ) < (size : ℝ) := by
    have hsizePos : 0 < size := lt_of_lt_of_le hrankPos hrankLe
    exact_mod_cast hsizePos
  have hchooseCast : (0 : ℝ) < (((size - 1).choose (rank - 1) : ℕ) : ℝ) := by
    have hchoosePos : 0 < (size - 1).choose (rank - 1) := Nat.choose_pos (by omega)
    exact_mod_cast hchoosePos
  have hmass := one_le_choose_mul_one_add_size_mul_value_of_isChartArgmaxValue design hchart
    hargmax hweightFloor hweightSum
  have hdivideChoose : (((size - 1).choose (rank - 1) : ℕ) : ℝ)⁻¹ ≤ 1 + (size : ℝ) * value := by
    have hscaled := mul_le_mul_of_nonneg_left hmass (inv_pos.mpr hchooseCast).le
    rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hchooseCast.ne', one_mul] at hscaled
  have hdivideSize := mul_le_mul_of_nonneg_left
    (show (((size - 1).choose (rank - 1) : ℕ) : ℝ)⁻¹ - 1 ≤ (size : ℝ) * value by
      linarith) (inv_pos.mpr hsizeCast).le
  rw [← mul_assoc, inv_mul_cancel₀ hsizeCast.ne', one_mul] at hdivideSize
  have hrewrite : cauchyBinetValueFloor size rank
      = ((size : ℝ))⁻¹ * ((((size - 1).choose (rank - 1) : ℕ) : ℝ)⁻¹ - 1) := by
    rw [cauchyBinetValueFloor]; ring
  rw [hrewrite]
  exact hdivideSize

/-- **FLOOR-CB against the stationarity bundle**, which is how every consumer meets
it.  The bundle enters only through the weight floor and the weight sum. -/
theorem cauchyBinetValueFloor_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    cauchyBinetValueFloor size rank ≤ value :=
  cauchyBinetValueFloor_le_value_of_isChartArgmaxValue design hchart hargmax
    (weight_ge_neg_value_of_isChartStationaryData hdata) hdata.weight_sum_one

end Floor

/-! ## The supersession, measured exactly -/

/-- **THE IMPROVEMENT, AS AN IDENTITY**: the new floor exceeds the shipped `-1/size`
by exactly `1/(size · C(size - 1, rank - 1))`.  Pure arithmetic about the two
numerals; no hypothesis at all. -/
theorem cauchyBinetValueFloor_sub_neg_inv_size_eq (size rank : ℕ) :
    cauchyBinetValueFloor size rank - -((size : ℝ))⁻¹
      = ((size : ℝ))⁻¹ * (((size - 1).choose (rank - 1) : ℕ) : ℝ)⁻¹ := by
  rw [cauchyBinetValueFloor]; ring

/-- **The improvement is strict at every cell** with `1 ≤ rank ≤ size` — including
both endpoints, where the floor is `0` rather than `-1/size`.  There is no cell at
which the Cauchy–Binet floor merely reproduces the shipped one. -/
theorem neg_inv_size_lt_cauchyBinetValueFloor {size rank : ℕ} (hrank : 0 < rank)
    (hle : rank ≤ size) : -((size : ℝ))⁻¹ < cauchyBinetValueFloor size rank := by
  have hsizeCast : (0 : ℝ) < (size : ℝ) := by
    have hsizePos : 0 < size := lt_of_lt_of_le hrank hle
    exact_mod_cast hsizePos
  have hchooseCast : (0 : ℝ) < (((size - 1).choose (rank - 1) : ℕ) : ℝ) := by
    have hchoosePos : 0 < (size - 1).choose (rank - 1) := Nat.choose_pos (by omega)
    exact_mod_cast hchoosePos
  have hgap := cauchyBinetValueFloor_sub_neg_inv_size_eq size rank
  have hpositive : 0 < ((size : ℝ))⁻¹ * (((size - 1).choose (rank - 1) : ℕ) : ℝ)⁻¹ :=
    mul_pos (inv_pos.mpr hsizeCast) (inv_pos.mpr hchooseCast)
  linarith

/-! ## The floor at the cells where it has been asked for -/

theorem cauchyBinetValueFloor_sixThree : cauchyBinetValueFloor 6 3 = -(3 / 20) := by
  have hchoose : (6 - 1).choose (3 - 1) = 10 := by decide
  rw [cauchyBinetValueFloor, hchoose]
  norm_num

theorem cauchyBinetValueFloor_sevenThree : cauchyBinetValueFloor 7 3 = -(2 / 15) := by
  have hchoose : (7 - 1).choose (3 - 1) = 15 := by decide
  rw [cauchyBinetValueFloor, hchoose]
  norm_num

theorem cauchyBinetValueFloor_eightThree : cauchyBinetValueFloor 8 3 = -(5 / 42) := by
  have hchoose : (8 - 1).choose (3 - 1) = 21 := by decide
  rw [cauchyBinetValueFloor, hchoose]
  norm_num

theorem cauchyBinetValueFloor_nineThree : cauchyBinetValueFloor 9 3 = -(3 / 28) := by
  have hchoose : (9 - 1).choose (3 - 1) = 28 := by decide
  rw [cauchyBinetValueFloor, hchoose]
  norm_num

theorem cauchyBinetValueFloor_sixFour : cauchyBinetValueFloor 6 4 = -(3 / 20) := by
  have hchoose : (6 - 1).choose (4 - 1) = 10 := by decide
  rw [cauchyBinetValueFloor, hchoose]
  norm_num

theorem cauchyBinetValueFloor_sevenFour : cauchyBinetValueFloor 7 4 = -(19 / 140) := by
  have hchoose : (7 - 1).choose (4 - 1) = 20 := by decide
  rw [cauchyBinetValueFloor, hchoose]
  norm_num

section Cells

variable {size rank : ℕ} {activeIndex : Type*} {projection : Matrix (Fin size) (Fin size) ℝ}
  {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)}

/-- **The floor at `(6,3)`**, which is the numeral
`Gtz.Quantitative.ChartEmptinessCertificate` consumes as a hypothesis. -/
theorem neg_three_div_twenty_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 6) (hrank : rank = 3) :
    -(3 / 20 : ℝ) ≤ value := by
  have hfloor := cauchyBinetValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, cauchyBinetValueFloor_sixThree] at hfloor

/-- **The floor at `(7,3)`**, the other open cell. -/
theorem neg_two_div_fifteen_le_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hsize : size = 7) (hrank : rank = 3) :
    -(2 / 15 : ℝ) ≤ value := by
  have hfloor := cauchyBinetValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata
  rwa [hsize, hrank, cauchyBinetValueFloor_sevenThree] at hfloor

end Cells

/-! ## THE DISCHARGE

`Gtz.Quantitative.ChartEmptinessCertificate` closes the negative-value half of the
repeated-weight branch of the two-block partition class under TWO hypotheses it does
not discharge: the numeral `-(3/20) ≤ value`, and `Gtz.EliminatesChartTwoBlockValue`.
The floor above discharges the first.  The second remains, so what follows is the
same class closure with one hypothesis fewer — not an unconditional one.

The rank is pinned to three because that is where the eliminant is asserted; the SIZE
is not a hypothesis, since a two-block family with both blocks occupied forces
`size = 2 · rank` (`Gtz.size_eq_two_mul_rank_of_isChartTwoBlockFamily`). -/

section Discharge

variable {size rank : ℕ} {activeIndex : Type*} {projection : Matrix (Fin size) (Fin size) ℝ}
  {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)} {chosenSubset : Finset (Fin size)}

/-- **THE TWO-BLOCK CLASS AT A NEGATIVE VALUE IS EMPTY, WITHOUT THE FLOOR
HYPOTHESIS.**  An admissible chart stationarity datum of rank three whose chart is a
design's and whose active family is two occupied complementary blocks has a
NONNEGATIVE value, given the elimination step.

This is `Gtz.zero_le_value_of_isChartTwoBlockFamily_of_eliminates` with its numeric
hypothesis `-(3/20) ≤ value` replaced by the design behind the chart, which is what
the Cauchy–Binet floor needs and what Cauchy–Binet needs anyway.  The elimination step
is still assumed. -/
theorem zero_le_value_of_isChartTwoBlockFamily_of_eliminates_of_design
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hrank : rank = 3)
    (heliminates : EliminatesChartTwoBlockValue (size := size) (activeIndex := activeIndex) rank)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnonempty : chosenSubset.Nonempty) (hnonemptyCompl : chosenSubsetᶜ.Nonempty) :
    0 ≤ value := by
  have hsize : size = 6 := by
    have hdouble :=
      size_eq_two_mul_rank_of_isChartTwoBlockFamily hdata hfamily hnonempty hnonemptyCompl
    omega
  exact zero_le_value_of_isChartTwoBlockFamily_of_eliminates heliminates hdata hargmax hfamily
    hnonempty hnonemptyCompl
    (neg_three_div_twenty_le_value_of_isChartStationaryData design hchart hargmax hdata hsize hrank)

/-- **THE EMPTINESS OF THE TWO-BLOCK CLASS ON THE WHOLE NEGATIVE AXIS.**  Given the
elimination step, there is NO admissible chart stationarity datum of rank three whose
chart is a design's, whose active family is two occupied complementary blocks, and
whose value is negative.

The shipped
`Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_flooredNegativeValue`
excludes the window `[-3/20, 0)`; the floor closes the rest of the negative axis, so
the window disappears from the statement.  What does NOT disappear is
`Gtz.EliminatesChartTwoBlockValue`: one of two hypotheses is discharged here, and the
class closure stays conditional on the other.  It also stays one class of the covering
census, and a floor excludes no further class — it only narrows the window in which
every class must still be examined. -/
theorem not_isChartStationaryData_of_isChartTwoBlockFamily_of_negativeValue
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hrank : rank = 3)
    (heliminates : EliminatesChartTwoBlockValue (size := size) (activeIndex := activeIndex) rank)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfamily : IsChartTwoBlockFamily activeSet activeSubset chosenSubset)
    (hnonempty : chosenSubset.Nonempty) (hnonemptyCompl : chosenSubsetᶜ.Nonempty)
    (hnegative : value < 0) :
    ¬ IsChartStationaryData rank projection weight value activeSet activeSubset activeWeight
        tightDir := by
  intro hdata
  exact absurd
    (zero_le_value_of_isChartTwoBlockFamily_of_eliminates_of_design design hchart hrank heliminates
      hdata hargmax hfamily hnonempty hnonemptyCompl)
    (not_le.mpr hnegative)

end Discharge

end Gtz

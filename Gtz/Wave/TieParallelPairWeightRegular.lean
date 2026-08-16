/-
# A weight-regular domination engine, and three laws the tree did not carry

## Section 1 and 2: the engine

`Gtz.dominates_iff_posSemidef_projectionBlock` decides domination by the Loewner
inequality `P_C ⪰ diag t_C` on the projection form.  Section 1 lands its STRICT
twin.  Section 2 replaces the weight diagonal on the right by ONE scalar cap:

    P_C ⪰ cap • 1  and  every selected weight is at most cap  ⟹  C dominates
    P_C ≻ cap • 1  and  the same                             ⟹  C dominates strictly

The strict form is a tie exclusion, `Gtz.not_isTie_of_projectionBlock_gt_weightCap`.

## Why the cap form earns its place

Every number the cap form reads lies in `[0, 1]`.  The tree already proves
`0 ⪯ P ⪯ 1`, and section 3 adds that a firing cap is at most the diagonal of the
block, hence at most one.  `Dominates` itself unfolds to `Σ_{c ∈ C} g_c g_cᵀ ⪰ I`
over the atoms `g_c = h_c / √t_c`, which have no bound as a weight goes to zero.
The engine is therefore regular exactly where the weight-scaled reading is not.

The cap costs only the spread of the selected weights:
`Gtz.posDef_gap_iff_projectionBlock_gt_weightCap_of_constant` is an equivalence
whenever the selected weights agree.

## Section 4: the two-sided stress reading

`Gtz.neg_side_orthogonal_of_pos_side` reads a stress in one direction only.
Section 4 lands the two-sided form: a probe kills the positive side exactly when
it kills the negative side, and exactly when it kills the whole support.

## Section 5: the small-support law

A nonzero stress whose support holds at most three labels forces a parallel pair.
No uniqueness hypothesis, no tie hypothesis, every size and every rank.  The tree
carried this only for support one and two, and only inside a `(7,3)` taxonomy
that assumes the stress space is a line.

## Section 6: three identities in atom coordinates

The tree carries the moment ladder through principal minors of the projection
form.  Section 6 states the level-one and level-two members over the atoms
themselves, and fuses the rank-level member into one determinant identity.
-/
import Mathlib
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.PsdKit
import Gtz.Certificates.ResidueDissolution
import Gtz.Corner.CornerFiber
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressSignSplit
import Gtz.Reduction.StressSupportTaxonomy
import Gtz.Reduction.ConnectednessRoute
import Gtz.Reduction.CoplanarStress
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.MixedCharPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The strict projection-block criterion

The positive-diagonal congruence of `Gtz.projectionBlock_sub_weightDiagonal` is an
equality of matrices, so it transports strict definiteness exactly as it
transports semidefiniteness. -/

/-- **The strict twin of `Gtz.posSemidef_projectionBlock_iff`**, at every selection
size.  The congruence basis is a positive diagonal, so `Gtz.posDef_congr_right`
applies unchanged. -/
theorem posDef_projectionBlock_iff (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    ((projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosDef
      ↔ (selectedAtomRows D pick * (selectedAtomRows D pick)ᵀ - 1).PosDef := by
  rw [projectionBlock_sub_weightDiagonal]
  exact (posDef_congr_right (selectedGramGap_transpose D pick)
    (isUnit_det_sqrtWeightDiagonal D pick)).symm

/-- **Strict domination is a strict projection-block inequality.**  At selection
size exactly the rank the selected-row matrix is square, so the transpose flip
`Gtz.posDef_transpose_mul_sub_one_comm` carries the gap across. -/
theorem posDef_gap_iff_posDef_projectionBlock (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ((projectionOfDesign D).submatrix pick pick
          - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosDef := by
  rw [posDef_projectionBlock_iff, ← transpose_mul_selectedAtomRows D pick hinj]
  exact posDef_transpose_mul_sub_one_comm (selectedAtomRows D pick)

/-! ## 2. The weight cap

One scalar replaces the weight diagonal.  The slack is a diagonal matrix with
nonnegative entries, so it costs one addition of a positive semidefinite matrix. -/

/-- The slack between a scalar cap and a weight diagonal is one diagonal matrix. -/
theorem smul_one_sub_weightDiagonal {size : ℕ} (cap : ℝ) (weightOf : Fin size → ℝ) :
    cap • (1 : Matrix (Fin size) (Fin size) ℝ) - Matrix.diagonal weightOf
      = Matrix.diagonal fun selectedIndex => cap - weightOf selectedIndex := by
  ext leftIndex rightIndex
  by_cases hEq : leftIndex = rightIndex
  · subst hEq; simp
  · simp [Matrix.one_apply_ne hEq, Matrix.diagonal_apply_ne _ hEq]

/-- The slack is positive semidefinite exactly when the cap bounds every selected
weight. -/
theorem posSemidef_smul_one_sub_weightDiagonal {size : ℕ} {cap : ℝ}
    {weightOf : Fin size → ℝ} (hcap : ∀ selectedIndex, weightOf selectedIndex ≤ cap) :
    (cap • (1 : Matrix (Fin size) (Fin size) ℝ) - Matrix.diagonal weightOf).PosSemidef := by
  rw [smul_one_sub_weightDiagonal]
  exact Matrix.posSemidef_diagonal_iff.mpr fun selectedIndex =>
    sub_nonneg.mpr (hcap selectedIndex)

/-- The projection block splits as the cap gap plus the cap slack. -/
theorem projectionBlock_sub_weightDiagonal_split (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (cap : ℝ) :
    (projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))
      = ((projectionOfDesign D).submatrix pick pick
          - cap • (1 : Matrix (Fin size) (Fin size) ℝ))
        + (cap • (1 : Matrix (Fin size) (Fin size) ℝ)
            - Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex)) :=
  (sub_add_sub_cancel _ _ _).symm

/-- **THE ENGINE, weak form.**  A scalar Loewner floor on the projection block,
together with a cap on the selected weights, produces domination.  No reciprocal
of a weight occurs in the hypothesis. -/
theorem dominates_of_projectionBlock_ge_weightCap (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) (cap : ℝ)
    (hcap : ∀ selectedIndex, D.weight (pick selectedIndex) ≤ cap)
    (hfloor : ((projectionOfDesign D).submatrix pick pick
        - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef) :
    Dominates D (Finset.image pick Finset.univ) := by
  rw [dominates_iff_posSemidef_projectionBlock D pick hinj,
    projectionBlock_sub_weightDiagonal_split D pick cap]
  exact hfloor.add (posSemidef_smul_one_sub_weightDiagonal hcap)

/-- **THE ENGINE, strict form.**  A strict scalar floor produces a strictly
dominating subset. -/
theorem posDef_gap_of_projectionBlock_gt_weightCap (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) (cap : ℝ)
    (hcap : ∀ selectedIndex, D.weight (pick selectedIndex) ≤ cap)
    (hfloor : ((projectionOfDesign D).submatrix pick pick
        - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
  rw [posDef_gap_iff_posDef_projectionBlock D pick hinj,
    projectionBlock_sub_weightDiagonal_split D pick cap]
  exact hfloor.add_posSemidef (posSemidef_smul_one_sub_weightDiagonal hcap)

/-- The selected image holds exactly `k` labels when the selection is injective. -/
theorem card_image_of_injective_univ (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (Finset.image pick Finset.univ).card = k := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **THE TIE EXCLUSION.**  One selection with a strict scalar floor above the
weight cap already refutes `Gtz.IsTie`.  Every ingredient stays inside the
projection form, which is bounded. -/
theorem not_isTie_of_projectionBlock_gt_weightCap (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) (cap : ℝ)
    (hcap : ∀ selectedIndex, D.weight (pick selectedIndex) ≤ cap)
    (hfloor : ((projectionOfDesign D).submatrix pick pick
        - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef) :
    ¬ IsTie D := fun htie =>
  htie.2 (Finset.image pick Finset.univ) (card_image_of_injective_univ pick hinj)
    (posDef_gap_of_projectionBlock_gt_weightCap D pick hinj cap hcap hfloor)

/-- **The engine loses nothing on the constant-weight locus.**  When every selected
weight equals the cap, the weight diagonal IS the scalar matrix, so the sufficient
condition becomes an equivalence.  The cap costs exactly the spread of the
selected weights, and nothing else. -/
theorem posDef_gap_iff_projectionBlock_gt_weightCap_of_constant (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) (cap : ℝ)
    (hconstant : ∀ selectedIndex, D.weight (pick selectedIndex) = cap) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ((projectionOfDesign D).submatrix pick pick
          - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  rw [posDef_gap_iff_posDef_projectionBlock D pick hinj]
  have hdiag : Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))
      = cap • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext leftIndex rightIndex
    by_cases hEq : leftIndex = rightIndex
    · subst hEq; simp [hconstant]
    · simp [Matrix.diagonal_apply_ne _ hEq, Matrix.one_apply_ne hEq]
  rw [hdiag]

/-! ## 3. The cap is bounded, the atoms are not

The projection form obeys `0 ⪯ P ⪯ 1` in the tree.  A firing cap therefore sits
below one, whatever the weights do. -/

/-- **A firing cap never exceeds one.**  The cap sits below a diagonal entry of the
projection block, and that entry is a leverage score, which the complement bounds
by one.  So the engine reads only numbers in `[0, 1]`. -/
theorem weightCap_le_one_of_projectionBlock_ge (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) (cap : ℝ)
    (selectedIndex : Fin size)
    (hfloor : ((projectionOfDesign D).submatrix pick pick
        - cap • (1 : Matrix (Fin size) (Fin size) ℝ)).PosSemidef) :
    cap ≤ 1 := by
  have hgap := hfloor.diag_nonneg (i := selectedIndex)
  have hcomplement := (posSemidef_one_sub_projectionOfDesign D).submatrix pick
  have hsplit : ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D).submatrix pick pick
      = (1 : Matrix (Fin m) (Fin m) ℝ).submatrix pick pick
        - (projectionOfDesign D).submatrix pick pick := rfl
  rw [hsplit, Matrix.submatrix_one pick hinj] at hcomplement
  have hupper := hcomplement.diag_nonneg (i := selectedIndex)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at hgap hupper
  linarith

/-! ### The engine is not vacuous

On the uniform-weight locus the cap equals every selected weight, so the
equivalence of the previous theorem turns any strictly dominating subset into a
firing of the engine. -/

/-- **A uniform-weight design with a strict dominator fires the engine.**  The
cap is the shared weight, and the equivalence supplies the strict floor. -/
theorem exists_projectionBlock_gt_weightCap_of_uniform (D : WeightedDesign m k) (cap : ℝ)
    (huniform : ∀ atomIndex, D.weight atomIndex = cap)
    (hstrict : HasStrictlyDominatingSubset D) :
    ∃ pick : Fin k → Fin m, Function.Injective pick ∧
      ((projectionOfDesign D).submatrix pick pick
        - cap • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  obtain ⟨selected, hcard, hposDef⟩ := hstrict
  refine ⟨selected.orderEmbOfFin hcard, (selected.orderEmbOfFin hcard).injective, ?_⟩
  have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  refine (posDef_gap_iff_projectionBlock_gt_weightCap_of_constant D _
    (selected.orderEmbOfFin hcard).injective cap fun selectedIndex => huniform _).mp ?_
  rw [himage]
  exact hposDef

/-- **THE ENGINE FIRES AT THE ICOSAHEDRON.**  The tree's `(6,3)` anchor carries
weight `1/6` at every label and a strictly dominating triple, so the cap form is
inhabited at the exact cell the rank-three frontier lives in. -/
theorem exists_projectionBlock_gt_weightCap_icosaDesign :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      ((projectionOfDesign icosaDesign).submatrix pick pick
        - (1 / 6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef :=
  exists_projectionBlock_gt_weightCap_of_uniform icosaDesign (1 / 6) (fun _ => rfl)
    icosaDesign_hasStrictlyDominatingSubset

/-! ## 4. The two-sided stress reading

The tree proves that a probe killing the positive side kills the negative side.
The converse is the same theorem at the negated stress, and the two together give
the whole support. -/

variable {n rank : ℕ}

/-- A negated stress is a stress. -/
theorem neg_stress {atomFamily : Fin n → Fin rank → ℝ} {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    ∑ c, (-stressCoeff) c • atomMatrix (atomFamily c) = 0 := by
  simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hstress, neg_zero]

/-- **THE TWO-SIDED READING.**  A probe annihilates every atom on the positive side
of a stress exactly when it annihilates every atom on the negative side. -/
theorem stress_pos_side_orthogonal_iff_neg_side {atomFamily : Fin n → Fin rank → ℝ}
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) (probe : Fin rank → ℝ) :
    (∀ c, 0 < stressCoeff c → atomFamily c ⬝ᵥ probe = 0)
      ↔ (∀ c, stressCoeff c < 0 → atomFamily c ⬝ᵥ probe = 0) := by
  constructor
  · exact fun hpos => neg_side_orthogonal_of_pos_side hstress hpos
  · intro hneg
    have hflip : ∀ c, (0 : ℝ) < (-stressCoeff) c → atomFamily c ⬝ᵥ probe = 0 := by
      intro c hc
      exact hneg c (by simpa using neg_pos.mp (by simpa using hc))
    intro c hc
    exact neg_side_orthogonal_of_pos_side (neg_stress hstress) hflip c (by simpa using hc)

/-- **The support reading.**  A probe that annihilates the positive side of a stress
annihilates every supported atom.  This is the exact hypothesis shape that branch
(iii) of `Gtz.sixThree_stress_trichotomy` consumes. -/
theorem stress_support_orthogonal_iff_pos_side {atomFamily : Fin n → Fin rank → ℝ}
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) (probe : Fin rank → ℝ) :
    (∀ c, 0 < stressCoeff c → atomFamily c ⬝ᵥ probe = 0)
      ↔ (∀ c, stressCoeff c ≠ 0 → atomFamily c ⬝ᵥ probe = 0) := by
  constructor
  · intro hpos c hc
    rcases lt_trichotomy (stressCoeff c) 0 with hlt | heq | hgt
    · exact (stress_pos_side_orthogonal_iff_neg_side hstress probe).mp hpos c hlt
    · exact absurd heq hc
    · exact hpos c hgt
  · exact fun hall c hc => hall c (ne_of_gt hc)

/-! ## 5. The small-support law

A stress with at most three live labels forces a parallel pair. -/

/-- **A one-signed stress hits a zero atom.**  If no coefficient is negative, every
supported atom is annihilated by every probe, so it is the zero vector. -/
theorem exists_zero_atom_of_nonneg_stress {atomFamily : Fin n → Fin rank → ℝ}
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hnonneg : ∀ c, 0 ≤ stressCoeff c) {live : Fin n} (hlive : stressCoeff live ≠ 0) :
    atomFamily live = 0 := by
  have hprobe : ∀ probe : Fin rank → ℝ, atomFamily live ⬝ᵥ probe = 0 := by
    intro probe
    have hsum := stress_kills_weighted_squares hstress probe
    have hterm : ∀ c ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ stressCoeff c * (atomFamily c ⬝ᵥ probe) ^ 2 :=
      fun c _ => mul_nonneg (hnonneg c) (sq_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum live (Finset.mem_univ live)
    rcases mul_eq_zero.mp hzero with hcoeff | hsq
    · exact absurd hcoeff hlive
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  exact eq_zero_of_dotProduct_self_eq_zero (hprobe (atomFamily live))

/-- A zero atom gives a parallel pair with ratio zero, as soon as two labels exist. -/
theorem hasParallelAtomPair_of_atom_eq_zero {atomFamily : Fin n → Fin rank → ℝ}
    (hsize : 1 < n) {dead : Fin n} (hdead : atomFamily dead = 0) :
    hasParallelAtomPair atomFamily := by
  have hne : NeZero n := ⟨by omega⟩
  obtain ⟨other, hother⟩ : ∃ other : Fin n, other ≠ dead := by
    have hcard : 1 < Fintype.card (Fin n) := by simpa using hsize
    exact Fintype.exists_ne_of_one_lt_card hcard dead
  exact ⟨other, dead, 0, hother, by rw [hdead, zero_smul]⟩

/-- The support splits into the two sign sides. -/
theorem card_stressSupport_eq_add (stressCoeff : Fin n → ℝ) :
    (stressSupport stressCoeff).card
      = (Finset.univ.filter fun c => 0 < stressCoeff c).card
        + (Finset.univ.filter fun c => stressCoeff c < 0).card := by
  classical
  have hunion : stressSupport stressCoeff
      = (Finset.univ.filter fun c => 0 < stressCoeff c)
        ∪ (Finset.univ.filter fun c => stressCoeff c < 0) := by
    ext c
    simp only [mem_stressSupport_iff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun hc => (lt_or_gt_of_ne hc).symm.imp id id, fun hc => by
      rcases hc with hpos | hneg
      · exact ne_of_gt hpos
      · exact ne_of_lt hneg⟩
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hleft hright
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hleft hright
    linarith
  rw [hunion, Finset.card_union_of_disjoint hdisjoint]

/-- **THE SMALL-SUPPORT LAW.**  A nonzero stress whose support holds at most three
labels forces a parallel pair.  No uniqueness hypothesis, no tie hypothesis, every
size and every rank.

Three cases.  A one-signed stress kills an atom outright.  Otherwise both signs
occur, the two sides have at least one label each, and a support of size at most
three leaves one side a singleton.  A singleton side caps the support span at one
dimension, and the tree turns that into a parallel pair. -/
theorem hasParallelAtomPair_of_card_stressSupport_le_three {atomFamily : Fin n → Fin rank → ℝ}
    {stressCoeff : Fin n → ℝ} (hsize : 1 < n) (hnonzero : stressCoeff ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hsupport : (stressSupport stressCoeff).card ≤ 3) :
    hasParallelAtomPair atomFamily := by
  classical
  obtain ⟨live, hlive⟩ := Function.ne_iff.mp hnonzero
  simp only [Pi.zero_apply] at hlive
  by_cases hnonneg : ∀ c, 0 ≤ stressCoeff c
  · exact hasParallelAtomPair_of_atom_eq_zero hsize
      (exists_zero_atom_of_nonneg_stress hstress hnonneg hlive)
  by_cases hnonpos : ∀ c, stressCoeff c ≤ 0
  · have hnegNonneg : ∀ c, 0 ≤ (-stressCoeff) c := fun c => by
      simpa using neg_nonneg.mpr (hnonpos c)
    have hnegLive : (-stressCoeff) live ≠ 0 := by simpa using hlive
    exact hasParallelAtomPair_of_atom_eq_zero hsize
      (exists_zero_atom_of_nonneg_stress (neg_stress hstress) hnegNonneg hnegLive)
  push Not at hnonneg hnonpos
  obtain ⟨negLabel, hnegLabel⟩ := hnonneg
  obtain ⟨posLabel, hposLabel⟩ := hnonpos
  have hposCard : 1 ≤ (Finset.univ.filter fun c => 0 < stressCoeff c).card :=
    Finset.card_pos.mpr ⟨posLabel, by simp [hposLabel]⟩
  have hnegCard : 1 ≤ (Finset.univ.filter fun c => stressCoeff c < 0).card :=
    Finset.card_pos.mpr ⟨negLabel, by simp [hnegLabel]⟩
  have hsplit := card_stressSupport_eq_add stressCoeff
  have hsmall : (Finset.univ.filter fun c => 0 < stressCoeff c).card ≤ 1
      ∨ (Finset.univ.filter fun c => stressCoeff c < 0).card ≤ 1 := by omega
  refine hasParallelAtomPair_of_supportSpan_le_one atomFamily hnonzero hsize hstress ?_
  rcases hsmall with hposSmall | hnegSmall
  · exact le_trans (finrank_supportSpan_le_card_positiveSide atomFamily hstress) hposSmall
  · have hnegSide : (Finset.univ.filter fun c => 0 < (-stressCoeff) c).card
        = (Finset.univ.filter fun c => stressCoeff c < 0).card := by
      congr 1
      ext c
      simp
    have hbound := finrank_supportSpan_le_card_positiveSide atomFamily (neg_stress hstress)
    rw [supportSpan_neg, hnegSide] at hbound
    exact le_trans hbound hnegSmall

/-- The design form of the small-support law. -/
theorem hasParallelPair_of_card_stressSupport_le_three {size : ℕ}
    (design : WeightedDesign size rank) (hsize : 1 < size) {stressCoeff : Fin size → ℝ}
    (hnonzero : stressCoeff ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hsupport : (stressSupport stressCoeff).card ≤ 3) :
    HasParallelPair design :=
  (hasParallelPair_iff_hasParallelAtomPair design).mpr
    (hasParallelAtomPair_of_card_stressSupport_le_three hsize hnonzero hstress hsupport)

/-- **Branch (iii) of `Gtz.sixThree_stress_trichotomy`, sharpened on small
supports.**  At `(6,3)` a nonzero stress with at most three live labels gives a
parallel pair with NO tie hypothesis and no selection machinery.  The tree's
coplanar branch reaches the same conclusion only through `Gtz.IsTie` and
`Gtz.twoPoleStratumSelection_six_unconditional`. -/
theorem hasParallelPair_sixThree_of_card_stressSupport_le_three
    (design : WeightedDesign 6 3) {stressCoeff : Fin 6 → ℝ} (hnonzero : stressCoeff ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hsupport : (stressSupport stressCoeff).card ≤ 3) :
    HasParallelPair design :=
  hasParallelPair_of_card_stressSupport_le_three design (by norm_num) hnonzero hstress hsupport

/-! ## 6. Three identities in atom coordinates -/

/-- The trace of a product of two atoms is the squared inner product. -/
theorem trace_atomMatrix_mul_atomMatrix (leftAtom rightAtom : Fin rank → ℝ) :
    Matrix.trace (atomMatrix leftAtom * atomMatrix rightAtom)
      = (leftAtom ⬝ᵥ rightAtom) ^ 2 := by
  rw [atomMatrix_mul_atomMatrix, Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul, sq]

/-- **THE SECOND MOMENT, in atom coordinates.**  Parseval squared, read by the
trace: the weighted double sum of squared inner products is the rank.  The tree
had this only as the level-two principal-minor member of the shadow ladder. -/
theorem sum_pair_weight_mul_sq_dotProduct (D : WeightedDesign m k) :
    ∑ leftLabel, ∑ rightLabel,
        D.weight leftLabel * D.weight rightLabel
          * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 = (k : ℝ) := by
  have hsquare : (∑ c, D.weight c • atomMatrix (D.atom c))
      * (∑ c, D.weight c • atomMatrix (D.atom c)) = 1 := by
    rw [D.isParseval, Matrix.one_mul]
  have hexpand : Matrix.trace ((∑ c, D.weight c • atomMatrix (D.atom c))
      * (∑ c, D.weight c • atomMatrix (D.atom c)))
      = ∑ leftLabel, ∑ rightLabel,
          D.weight leftLabel * D.weight rightLabel
            * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := by
    rw [Matrix.sum_mul]
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun rightLabel _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
      trace_atomMatrix_mul_atomMatrix, smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [← hexpand, hsquare, Matrix.trace_one, Fintype.card_fin]

/-- **THE PAIR-AREA IDENTITY.**  The weighted double sum of the two-atom Gram
determinants is `k² − k`.  The diagonal terms vanish, so the sum runs over ordered
pairs of distinct labels, and the unordered form is half of it. -/
theorem sum_pair_weight_mul_pairGram (D : WeightedDesign m k) :
    ∑ leftLabel, ∑ rightLabel,
        D.weight leftLabel * D.weight rightLabel
          * (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel)
              - (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)
      = (k : ℝ) ^ 2 - (k : ℝ) := by
  have hfirst : ∑ leftLabel, ∑ rightLabel,
      D.weight leftLabel * D.weight rightLabel
        * (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel))
      = (k : ℝ) ^ 2 := by
    have hsplit : ∀ leftLabel : Fin m, ∑ rightLabel,
        D.weight leftLabel * D.weight rightLabel
          * (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel))
        = (D.weight leftLabel * leverageOf (D.atom leftLabel))
          * ∑ rightLabel, D.weight rightLabel * leverageOf (D.atom rightLabel) := by
      intro leftLabel
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun rightLabel _ => by ring
    rw [Finset.sum_congr rfl fun leftLabel _ => hsplit leftLabel, ← Finset.sum_mul,
      sum_weight_mul_leverage, sq]
  have hsecond := sum_pair_weight_mul_sq_dotProduct D
  have hcombine : ∑ leftLabel, ∑ rightLabel,
      D.weight leftLabel * D.weight rightLabel
        * (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel)
            - (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)
      = (∑ leftLabel, ∑ rightLabel,
          D.weight leftLabel * D.weight rightLabel
            * (leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel)))
        - ∑ leftLabel, ∑ rightLabel,
            D.weight leftLabel * D.weight rightLabel
              * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  rw [hcombine, hfirst, hsecond]

/-- **THE VOLUME-SAMPLING IDENTITY, fused.**  The weight products against the
subset determinants sum to one.  The tree carried the two halves separately, the
shadow measure and the shadow evaluation, and never the composed statement. -/
theorem sum_weightProduct_mul_det_subsetSum (D : WeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (∏ atomIndex ∈ selected, D.weight atomIndex) * (subsetSum D selected).det = 1 := by
  rw [← sum_shadowDeterminant_eq_one D]
  refine Finset.sum_congr rfl fun selected hselected => ?_
  exact (shadowDeterminant_eq_weightProduct_mul_detSubsetSum D
    (Finset.mem_powersetCard.mp hselected).2).symm

end Gtz

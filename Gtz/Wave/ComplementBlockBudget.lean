/-
# The anisotropy criterion on the projection block, and its complementary budget

`Gtz.posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt` decides strict
domination from two invariants of the GAP matrix `S_C - 1`.  The gap matrix reads
the raw Gram entries, which grow without bound as a weight vanishes.  This module
lands the same criterion on the PROJECTION BLOCK `P_C - diag t_C`, whose entries
all lie in `[-1, 1]`.

## What is new here

* `Gtz.projectionGap` — the shifted projection block, together with its trace and
  its squared Frobenius norm in weight-and-Gram coordinates.  No square root of a
  weight survives: the diagonal is `t_c * leverage`, the off-diagonal appears only
  squared, and `Gtz.sq_projectionOfDesign_apply` clears both roots.
* `Gtz.not_isTie_of_projectionGap_isotropy` — the engine.  One selection whose
  block trace is nonnegative and whose block Frobenius mass is under half the
  squared block trace already refutes `Gtz.IsTie`.
* `Gtz.blockSquareMass_add_crossBlockMass` — the COMPLEMENTARY reading.  The
  squared entries of the block, plus the squared entries of the block against its
  complement, total the block diagonal.  This is idempotency of the projection cut
  along the selection, and it turns the criterion into a statement in which the
  complementary labels appear with a favourable sign.
* `Gtz.crossBlockMass_le_of_isTie` — the budget.  At a tie every selection obeys
  an upper bound on its cross mass, in numbers from `[0, 1]`.
* `Gtz.blockSquareMass_compl` — the complementary Frobenius law.  A block and the
  block on the complementary labels differ by the rank minus twice the block
  diagonal.  The cross mass cancels between the two cuts, so no eigenvalue and no
  size hypothesis enters.
* `Gtz.projectionGap_isotropy_signFlipDesign_iff` — the criterion is SIGN-BLIND,
  in the tree's established sense of that term.
  `Gtz.atomMatrix` does not read the sign of an atom, so `Gtz.IsTie` is invariant
  when each atom is multiplied by its own scalar of square one
  (`Gtz.isTie_signFlipDesign_iff`).  The criterion reads the weights, the leverage
  shares and the SQUARED Gram entries, and all three are invariant too.  So the
  engine cannot separate two designs that `Gtz.IsTie` cannot separate.

## The two readings are incomparable, at the campaign's own foil

`Gtz.capFoilDesign` is the landed stress-free `(6,3)` design at which no scalar
weight cap fires.  On it:

* the triple `{0, 3, 5}` has block trace `47/42` and block Frobenius mass
  `1081/1764`, so the BLOCK criterion fires, while the gap matrix has trace `13`
  and Frobenius mass `91`, so the GAP criterion does NOT
  (`Gtz.capFoil_projectionGap_isotropy_middle`,
  `Gtz.capFoil_gap_not_isotropy_middle`);
* the triple `{1, 3, 5}` has block trace `8/7` and block Frobenius mass `2/3`, so
  the BLOCK criterion does NOT fire, while the gap matrix has trace `9` and
  Frobenius mass `39`, so the GAP criterion does
  (`Gtz.capFoil_gap_isotropy_right`,
  `Gtz.capFoil_projectionGap_not_isotropy_right`).

Both directions are collected in `Gtz.capFoil_isotropy_tests_incomparable`.

So neither criterion contains the other, and the two witnesses are exact
rationals at a design already in the tree.

## The threshold is sharp at the tetrahedron

At `Gtz.tetraDesign`, the `(4,3)` tie, every triple has block trace `3/2` and
block Frobenius mass `9/8`, so `(tr)^2 = 2 * F` exactly
(`Gtz.tetraDesign_projectionGap_boundary`).  The engine misses size four by
exactly zero margin.  Nothing here reaches `(4,3)` or `(5,3)`, and that is not an
accident of the proof: the threshold IS attained there.

## Honest scope

The criterion is SUFFICIENT and not necessary.  It reads two of the three
invariants of a `3 x 3` spectrum, so it is blind to the anisotropic positive
definite blocks, exactly as its gap twin is.  It does not close the stress-free
branch of `Gtz.sixThree_stress_trichotomy` and no claim to that effect is made
here.  Its margin still falls to zero at the tie boundary, because every
sufficient condition with a margin does.  What changes is the CHANNEL: the block
reading stays finite when a weight vanishes, and the gap reading does not.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.ChartHadamard
import Gtz.Design.StressFreeStratum
import Gtz.Design.StressCertificate
import Gtz.Certificates.ResidueDissolution
import Gtz.Wave.TieParallelPairWeightRegular
import Gtz.Wave.StressFreeCapRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The shifted projection block -/

/-- **The projection gap of a selection**: the principal block of the projection
form along `pick`, minus the diagonal of the selected weights.  This is the matrix
whose positive definiteness IS strict domination
(`Gtz.posDef_gap_iff_posDef_projectionBlock`). -/
noncomputable def projectionGap (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) : Matrix (Fin size) (Fin size) ℝ :=
  (projectionOfDesign D).submatrix pick pick
    - Matrix.diagonal fun selectedIndex => D.weight (pick selectedIndex)

/-- The entries of the projection gap. -/
theorem projectionGap_apply (D : WeightedDesign m k) {size : ℕ} (pick : Fin size → Fin m)
    (leftIndex rightIndex : Fin size) :
    projectionGap D pick leftIndex rightIndex
      = projectionOfDesign D (pick leftIndex) (pick rightIndex)
        - (if leftIndex = rightIndex then D.weight (pick leftIndex) else 0) := by
  rw [projectionGap]
  by_cases hsame : leftIndex = rightIndex
  · subst hsame
    simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ hsame, hsame]

/-- The projection gap is symmetric. -/
theorem projectionGap_transpose (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) : (projectionGap D pick)ᵀ = projectionGap D pick := by
  ext leftIndex rightIndex
  rw [Matrix.transpose_apply, projectionGap_apply, projectionGap_apply]
  have hsymm : projectionOfDesign D (pick rightIndex) (pick leftIndex)
      = projectionOfDesign D (pick leftIndex) (pick rightIndex) := by
    conv_rhs => rw [← projectionOfDesign_transpose D]
    rfl
  rw [hsymm]
  by_cases hsame : leftIndex = rightIndex
  · subst hsame; simp
  · rw [if_neg hsame, if_neg (Ne.symm hsame)]

/-- **The block trace, in weight coordinates.**  Every summand is a leverage share
minus a weight, and the leverage share is a diagonal entry of a projection. -/
theorem trace_projectionGap (D : WeightedDesign m k) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix.trace (projectionGap D pick)
      = ∑ selectedIndex, (D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex)) - D.weight (pick selectedIndex)) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun selectedIndex _ => ?_
  rw [Matrix.diag_apply, projectionGap_apply, if_pos rfl, projectionOfDesign_diagonal]

/-- **The block Frobenius mass, split off the diagonal.**  The cross term of the
square touches only the diagonal, so the off-diagonal entries enter squared and
the weights enter linearly. -/
theorem frobeniusNormSq_projectionGap (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    frobeniusNormSq (projectionGap D pick)
      = (∑ leftIndex, ∑ rightIndex,
            projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2)
        - 2 * ∑ selectedIndex, D.weight (pick selectedIndex)
            * projectionOfDesign D (pick selectedIndex) (pick selectedIndex)
        + ∑ selectedIndex, D.weight (pick selectedIndex) ^ 2 := by
  classical
  have hrow : ∀ leftIndex : Fin size,
      ∑ rightIndex, projectionGap D pick leftIndex rightIndex
          * projectionGap D pick leftIndex rightIndex
        = (∑ rightIndex, projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2)
          - 2 * (D.weight (pick leftIndex)
              * projectionOfDesign D (pick leftIndex) (pick leftIndex))
          + D.weight (pick leftIndex) ^ 2 := by
    intro leftIndex
    have hterm : ∀ rightIndex : Fin size,
        projectionGap D pick leftIndex rightIndex * projectionGap D pick leftIndex rightIndex
          = projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2
            - 2 * (projectionOfDesign D (pick leftIndex) (pick rightIndex)
                * (if leftIndex = rightIndex then D.weight (pick leftIndex) else 0))
            + (if leftIndex = rightIndex then D.weight (pick leftIndex) else 0) ^ 2 := by
      intro rightIndex
      rw [projectionGap_apply]
      ring
    rw [Finset.sum_congr rfl fun rightIndex _ => hterm rightIndex]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hcross : ∑ rightIndex, projectionOfDesign D (pick leftIndex) (pick rightIndex)
          * (if leftIndex = rightIndex then D.weight (pick leftIndex) else 0)
        = D.weight (pick leftIndex)
          * projectionOfDesign D (pick leftIndex) (pick leftIndex) := by
      rw [Finset.sum_eq_single leftIndex]
      · rw [if_pos rfl]; ring
      · intro rightIndex _ hne
        rw [if_neg (Ne.symm hne), mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ leftIndex) hmem
    have hsquare : ∑ rightIndex,
        (if leftIndex = rightIndex then D.weight (pick leftIndex) else 0) ^ 2
        = D.weight (pick leftIndex) ^ 2 := by
      rw [Finset.sum_eq_single leftIndex]
      · rw [if_pos rfl]
      · intro rightIndex _ hne
        rw [if_neg (Ne.symm hne)]; ring
      · intro hmem; exact absurd (Finset.mem_univ leftIndex) hmem
    rw [hcross, hsquare]
  rw [frobeniusNormSq, frobeniusInner,
    Finset.sum_congr rfl fun leftIndex _ => hrow leftIndex,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- **The block Frobenius mass, with every square root cleared.**  The squared
projection entry is `t_a t_b (g_a . g_b)^2` and the diagonal share is
`t_c * leverage`, so the whole quantity is a polynomial in weights and Gram
entries. -/
theorem frobeniusNormSq_projectionGap_gramForm (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) :
    frobeniusNormSq (projectionGap D pick)
      = (∑ leftIndex, ∑ rightIndex,
            D.weight (pick leftIndex) * D.weight (pick rightIndex)
              * (D.atom (pick leftIndex) ⬝ᵥ D.atom (pick rightIndex)) ^ 2)
        - 2 * ∑ selectedIndex, D.weight (pick selectedIndex) ^ 2
            * leverageOf (D.atom (pick selectedIndex))
        + ∑ selectedIndex, D.weight (pick selectedIndex) ^ 2 := by
  rw [frobeniusNormSq_projectionGap]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun leftIndex _ =>
        Finset.sum_congr rfl fun rightIndex _ => sq_projectionOfDesign_apply D _ _
    · congr 1
      refine Finset.sum_congr rfl fun selectedIndex _ => ?_
      rw [projectionOfDesign_diagonal]
      ring

/-! ## 2. The engine

The landed isotropy test is applied to the block rather than to the gap.  The
bridge back to domination is the landed strict projection-block equivalence, so
the selection size has to be the rank. -/

/-- **THE BLOCK ISOTROPY TEST.**  A selection of three labels whose projection
gap has nonnegative trace and squared Frobenius mass under half the squared trace
carries a positive definite projection gap. -/
theorem posDef_projectionGap_of_isotropy (D : WeightedDesign m k) (pick : Fin 3 → Fin m)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick))
    (hisotropy : 2 * frobeniusNormSq (projectionGap D pick)
      < Matrix.trace (projectionGap D pick) ^ 2) :
    (projectionGap D pick).PosDef :=
  posDef_three_of_trace_nonneg_of_two_mul_frobeniusNormSq_lt
    (projectionGap_transpose D pick) htrace hisotropy

/-- **THE BLOCK ISOTROPY TEST PRODUCES A STRICTLY DOMINATING TRIPLE.**  At rank
three the selected scaled rows are square, so the landed strict flip carries the
block gap onto the atom gap. -/
theorem posDef_gap_of_projectionGap_isotropy (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick))
    (hisotropy : 2 * frobeniusNormSq (projectionGap D pick)
      < Matrix.trace (projectionGap D pick) ^ 2) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
  rw [posDef_gap_iff_posDef_projectionBlock D pick hinj]
  exact posDef_projectionGap_of_isotropy D pick htrace hisotropy

/-- **THE ENGINE.**  One selection passing the block isotropy test already refutes
`Gtz.IsTie`.  Every number the hypothesis reads is a weight, a leverage share or a
squared projection entry, and all three families live inside `[0, 1]`. -/
theorem not_isTie_of_projectionGap_isotropy (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick))
    (hisotropy : 2 * frobeniusNormSq (projectionGap D pick)
      < Matrix.trace (projectionGap D pick) ^ 2) :
    ¬ IsTie D := fun htie =>
  htie.2 (Finset.image pick Finset.univ) (card_image_of_injective_univ pick hinj)
    (posDef_gap_of_projectionGap_isotropy D pick hinj htrace hisotropy)

/-- **THE ANISOTROPY LAW ON THE BLOCK.**  Contrapositive of the engine: at a tie,
every injective selection of three labels has squared block trace at most twice
the block Frobenius mass.  This is the bounded twin of
`Gtz.two_mul_frobeniusNormSq_gap_of_isTie_sixThree`. -/
theorem sq_trace_projectionGap_le_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick)) :
    Matrix.trace (projectionGap D pick) ^ 2
      ≤ 2 * frobeniusNormSq (projectionGap D pick) := by
  by_contra hisotropy
  push Not at hisotropy
  exact not_isTie_of_projectionGap_isotropy D pick hinj htrace hisotropy htie

/-! ## 3. The criterion is bounded

The projection form obeys `0 ⪯ P ⪯ 1`, so its diagonal lies in `[0, 1]` and the
squared entries total the rank.  Both quantities the engine reads inherit this. -/

/-- Every leverage share of a design lies in `[0, 1]`: it is a diagonal entry of a
symmetric idempotent. -/
theorem weight_mul_leverage_mem_unitInterval (D : WeightedDesign m k) (atomLabel : Fin m) :
    0 ≤ D.weight atomLabel * leverageOf (D.atom atomLabel)
      ∧ D.weight atomLabel * leverageOf (D.atom atomLabel) ≤ 1 := by
  constructor
  · exact mul_nonneg (D.weight_pos atomLabel).le
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hdiag := diagonal_le_one_of_symmetricIdempotent
      (projectionOfDesign_transpose D) (projectionOfDesign_mul_self D) atomLabel
    rwa [projectionOfDesign_diagonal] at hdiag

/-- **The block trace never exceeds the rank.**  The selected leverage shares are
part of the projection diagonal, whose total is the rank. -/
theorem trace_projectionGap_le_rank (D : WeightedDesign m k) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick) :
    Matrix.trace (projectionGap D pick) ≤ (k : ℝ) := by
  classical
  rw [trace_projectionGap]
  have hbound : ∑ selectedIndex, (D.weight (pick selectedIndex)
        * leverageOf (D.atom (pick selectedIndex)) - D.weight (pick selectedIndex))
      ≤ ∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex)) := by
    refine Finset.sum_le_sum fun selectedIndex _ => ?_
    have := (D.weight_pos (pick selectedIndex)).le
    linarith
  have himage : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        D.weight atomLabel * leverageOf (D.atom atomLabel)
      = ∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex)) :=
    Finset.sum_image fun left _ right _ hlr => hinj hlr
  have hpart : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        D.weight atomLabel * leverageOf (D.atom atomLabel)
      ≤ ∑ atomLabel, D.weight atomLabel * leverageOf (D.atom atomLabel) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomLabel _ _ => (weight_mul_leverage_mem_unitInterval D atomLabel).1
  rw [sum_weight_mul_leverage D, himage] at hpart
  linarith [hbound, hpart]

/-- **The squared block entries never exceed the rank.**  They are part of the
total squared mass of the projection, which is the rank. -/
theorem sum_sq_projectionBlock_le_rank (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    ∑ leftIndex, ∑ rightIndex,
        projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2 ≤ (k : ℝ) := by
  classical
  have himage : ∀ leftIndex : Fin size,
      ∑ atomLabel ∈ Finset.image pick Finset.univ,
          projectionOfDesign D (pick leftIndex) atomLabel ^ 2
        = ∑ rightIndex, projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2 :=
    fun leftIndex => Finset.sum_image fun left _ right _ hlr => hinj hlr
  have hrow : ∀ leftIndex : Fin size,
      ∑ rightIndex, projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2
        ≤ D.weight (pick leftIndex) * leverageOf (D.atom (pick leftIndex)) := by
    intro leftIndex
    rw [← himage leftIndex,
      ← sum_sq_projectionOfDesign_row_eq_weight_mul_leverage D (pick leftIndex)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => sq_nonneg _
  have hstep : ∑ leftIndex, ∑ rightIndex,
        projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2
      ≤ ∑ leftIndex, D.weight (pick leftIndex) * leverageOf (D.atom (pick leftIndex)) :=
    Finset.sum_le_sum fun leftIndex _ => hrow leftIndex
  have hsel : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        D.weight atomLabel * leverageOf (D.atom atomLabel)
      = ∑ leftIndex, D.weight (pick leftIndex) * leverageOf (D.atom (pick leftIndex)) :=
    Finset.sum_image fun left _ right _ hlr => hinj hlr
  have hpart : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        D.weight atomLabel * leverageOf (D.atom atomLabel)
      ≤ ∑ atomLabel, D.weight atomLabel * leverageOf (D.atom atomLabel) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomLabel _ _ => (weight_mul_leverage_mem_unitInterval D atomLabel).1
  rw [sum_weight_mul_leverage D, hsel] at hpart
  linarith [hstep, hpart]

/-! ## 4. The complementary reading

Idempotency of the projection says the squared entries of a row total the diagonal
entry of that row.  Cutting the row at the selection turns that into a law with
the complementary labels on the other side. -/

/-- **The cross mass of a selection**: the squared projection entries pairing a
selected label with an unselected one. -/
noncomputable def crossBlockMass (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) : ℝ :=
  ∑ selectedIndex, ∑ otherLabel ∈ (Finset.image pick Finset.univ)ᶜ,
    projectionOfDesign D (pick selectedIndex) otherLabel ^ 2

/-- The cross mass is nonnegative. -/
theorem crossBlockMass_nonneg (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) : 0 ≤ crossBlockMass D pick :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **THE CROSS-BLOCK LAW.**  For an injective selection, the squared entries of
the block plus the cross mass total the block diagonal.  This is the row law of
`Gtz.sum_sq_projectionOfDesign_row_eq_weight_mul_leverage` cut along the
selection, and it is the exact sense in which the complementary labels carry the
deficit of the block. -/
theorem blockSquareMass_add_crossBlockMass (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    (∑ leftIndex, ∑ rightIndex,
        projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2)
      + crossBlockMass D pick
      = ∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex)) := by
  classical
  rw [crossBlockMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun leftIndex _ => ?_
  have himage : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        projectionOfDesign D (pick leftIndex) atomLabel ^ 2
      = ∑ rightIndex, projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2 :=
    Finset.sum_image fun left _ right _ hlr => hinj hlr
  rw [← himage, Finset.sum_add_sum_compl,
    sum_sq_projectionOfDesign_row_eq_weight_mul_leverage D (pick leftIndex)]

/-- **THE BLOCK FROBENIUS MASS, READ THROUGH THE COMPLEMENT.**  The cross mass
enters with a MINUS sign, so a selection strongly coupled to its complement has a
small block Frobenius mass and passes the isotropy test more easily. -/
theorem frobeniusNormSq_projectionGap_complementForm (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    frobeniusNormSq (projectionGap D pick)
      = (∑ selectedIndex, D.weight (pick selectedIndex)
            * leverageOf (D.atom (pick selectedIndex))
              * (1 - 2 * D.weight (pick selectedIndex)))
        + (∑ selectedIndex, D.weight (pick selectedIndex) ^ 2)
        - crossBlockMass D pick := by
  have hmass := blockSquareMass_add_crossBlockMass D pick hinj
  rw [frobeniusNormSq_projectionGap]
  have hsplit : (∑ leftIndex, ∑ rightIndex,
        projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2)
      = (∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex))) - crossBlockMass D pick := by
    linarith [hmass]
  rw [hsplit]
  have hdiag : ∑ selectedIndex, D.weight (pick selectedIndex)
        * projectionOfDesign D (pick selectedIndex) (pick selectedIndex)
      = ∑ selectedIndex, D.weight (pick selectedIndex)
          * (D.weight (pick selectedIndex) * leverageOf (D.atom (pick selectedIndex))) :=
    Finset.sum_congr rfl fun selectedIndex _ => by rw [projectionOfDesign_diagonal]
  rw [hdiag]
  have hcombine : (∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex)))
        - 2 * ∑ selectedIndex, D.weight (pick selectedIndex)
            * (D.weight (pick selectedIndex) * leverageOf (D.atom (pick selectedIndex)))
      = ∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex))
            * (1 - 2 * D.weight (pick selectedIndex)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun selectedIndex _ => by ring
  linarith [hcombine]

/-- **THE ENGINE, IN COMPLEMENT FORM.**  A large cross mass fires the criterion.
Every term is a weight, a leverage share or a squared projection entry. -/
theorem not_isTie_of_crossBlockMass (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick))
    (hcross : 2 * ((∑ selectedIndex, D.weight (pick selectedIndex)
            * leverageOf (D.atom (pick selectedIndex))
              * (1 - 2 * D.weight (pick selectedIndex)))
          + (∑ selectedIndex, D.weight (pick selectedIndex) ^ 2)
          - crossBlockMass D pick)
        < Matrix.trace (projectionGap D pick) ^ 2) :
    ¬ IsTie D := by
  refine not_isTie_of_projectionGap_isotropy D pick hinj htrace ?_
  rwa [frobeniusNormSq_projectionGap_complementForm D pick hinj]

/-- **THE CROSS-MASS BUDGET AT A TIE.**  At a tie the cross mass of every
injective selection of three labels is bounded above by data on the selection
alone.  All the numbers are weights and leverage shares, hence in `[0, 1]`. -/
theorem crossBlockMass_le_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    (pick : Fin 3 → Fin m) (hinj : Function.Injective pick)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick)) :
    crossBlockMass D pick
      ≤ (∑ selectedIndex, D.weight (pick selectedIndex)
            * leverageOf (D.atom (pick selectedIndex))
              * (1 - 2 * D.weight (pick selectedIndex)))
        + (∑ selectedIndex, D.weight (pick selectedIndex) ^ 2)
        - Matrix.trace (projectionGap D pick) ^ 2 / 2 := by
  have haniso := sq_trace_projectionGap_le_of_isTie D htie pick hinj htrace
  rw [frobeniusNormSq_projectionGap_complementForm D pick hinj] at haniso
  linarith

/-- **THE GLOBAL CROSS BUDGET.**  Summed over all ordered pairs of labels, the
squared off-diagonal projection entries total the rank minus the squared leverage
shares.  This is the ceiling every selection's cross mass sits under. -/
theorem sum_sq_offDiagonal_projection (D : WeightedDesign m k) :
    ∑ leftLabel, ∑ rightLabel ∈ Finset.univ.erase leftLabel,
        projectionOfDesign D leftLabel rightLabel ^ 2
      = (k : ℝ) - ∑ atomLabel, (D.weight atomLabel * leverageOf (D.atom atomLabel)) ^ 2 := by
  classical
  have hrow : ∀ leftLabel : Fin m,
      ∑ rightLabel ∈ Finset.univ.erase leftLabel,
          projectionOfDesign D leftLabel rightLabel ^ 2
        = D.weight leftLabel * leverageOf (D.atom leftLabel)
          - (D.weight leftLabel * leverageOf (D.atom leftLabel)) ^ 2 := by
    intro leftLabel
    have hfull := sum_sq_projectionOfDesign_row_eq_weight_mul_leverage D leftLabel
    have hsplit : ∑ rightLabel, projectionOfDesign D leftLabel rightLabel ^ 2
        = projectionOfDesign D leftLabel leftLabel ^ 2
          + ∑ rightLabel ∈ Finset.univ.erase leftLabel,
              projectionOfDesign D leftLabel rightLabel ^ 2 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ leftLabel)).symm
    rw [projectionOfDesign_diagonal] at hsplit
    linarith [hfull, hsplit]
  rw [Finset.sum_congr rfl fun leftLabel _ => hrow leftLabel, Finset.sum_sub_distrib,
    sum_weight_mul_leverage D]

/-! ## 4b. The complementary block

Read along a subset rather than along a selection map, the same cut gives a law
that compares a block with the block on the COMPLEMENTARY labels.  The cross mass
is shared by the two sides, so it cancels and leaves a statement about the two
diagonals alone. -/

/-- The squared projection entries inside a subset of labels. -/
noncomputable def blockSquareMass (D : WeightedDesign m k) (selected : Finset (Fin m)) : ℝ :=
  ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
    projectionOfDesign D leftLabel rightLabel ^ 2

/-- The squared projection entries pairing a subset with its complement. -/
noncomputable def crossMass (D : WeightedDesign m k) (selected : Finset (Fin m)) : ℝ :=
  ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selectedᶜ,
    projectionOfDesign D leftLabel rightLabel ^ 2

/-- **THE CUT, ON SUBSETS.**  Block mass plus cross mass is the block diagonal. -/
theorem blockSquareMass_add_crossMass (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    blockSquareMass D selected + crossMass D selected
      = ∑ atomLabel ∈ selected, D.weight atomLabel * leverageOf (D.atom atomLabel) := by
  classical
  rw [blockSquareMass, crossMass, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun leftLabel _ => ?_
  rw [Finset.sum_add_sum_compl,
    sum_sq_projectionOfDesign_row_eq_weight_mul_leverage D leftLabel]

/-- **THE CROSS MASS IS SHARED.**  A subset and its complement read the same cross
pairs, because the projection form is symmetric. -/
theorem crossMass_compl (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    crossMass D selectedᶜ = crossMass D selected := by
  classical
  have hsymm : ∀ leftLabel rightLabel : Fin m,
      projectionOfDesign D leftLabel rightLabel = projectionOfDesign D rightLabel leftLabel := by
    intro leftLabel rightLabel
    conv_lhs => rw [← projectionOfDesign_transpose D]
    rfl
  rw [crossMass, crossMass, compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun leftLabel _ =>
    Finset.sum_congr rfl fun rightLabel _ => by rw [hsymm rightLabel leftLabel]

/-- The projection diagonal on a complement is the rank minus the diagonal on the
subset. -/
theorem sum_diagonal_compl (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    ∑ atomLabel ∈ selectedᶜ, D.weight atomLabel * leverageOf (D.atom atomLabel)
      = (k : ℝ) - ∑ atomLabel ∈ selected, D.weight atomLabel * leverageOf (D.atom atomLabel) := by
  classical
  have hsplit := Finset.sum_add_sum_compl selected
    (fun atomLabel => D.weight atomLabel * leverageOf (D.atom atomLabel))
  rw [sum_weight_mul_leverage D] at hsplit
  linarith

/-- **THE COMPLEMENTARY FROBENIUS LAW.**  The squared mass of a block and the
squared mass of the complementary block differ by the rank minus twice the block
diagonal.  Nothing here needs the size to be twice the rank, and nothing needs
eigenvalues: the cross mass cancels between the two cuts.

This is the exact sense in which the block criterion can be read on the OTHER
labels.  A complementary block with small squared mass makes the block criterion
easier to satisfy. -/
theorem blockSquareMass_compl (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    blockSquareMass D selectedᶜ
      = blockSquareMass D selected + (k : ℝ)
        - 2 * ∑ atomLabel ∈ selected, D.weight atomLabel * leverageOf (D.atom atomLabel) := by
  have hblock := blockSquareMass_add_crossMass D selected
  have hcompl := blockSquareMass_add_crossMass D selectedᶜ
  rw [crossMass_compl D selected, sum_diagonal_compl D selected] at hcompl
  linarith

/-- The selection-indexed cross mass is the subset-indexed one. -/
theorem crossBlockMass_eq_crossMass (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    crossBlockMass D pick = crossMass D (Finset.image pick Finset.univ) := by
  classical
  have houter : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        (∑ otherLabel ∈ (Finset.image pick Finset.univ)ᶜ,
          projectionOfDesign D atomLabel otherLabel ^ 2)
      = ∑ selectedIndex, ∑ otherLabel ∈ (Finset.image pick Finset.univ)ᶜ,
          projectionOfDesign D (pick selectedIndex) otherLabel ^ 2 :=
    Finset.sum_image fun left _ right _ hlr => hinj hlr
  rw [crossBlockMass, crossMass, houter]

/-- The selection-indexed block mass is the subset-indexed one. -/
theorem blockSquareMass_eq_of_injective (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    (∑ leftIndex, ∑ rightIndex,
        projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2)
      = blockSquareMass D (Finset.image pick Finset.univ) := by
  classical
  have houter : ∑ leftLabel ∈ Finset.image pick Finset.univ,
        (∑ rightLabel ∈ Finset.image pick Finset.univ,
          projectionOfDesign D leftLabel rightLabel ^ 2)
      = ∑ leftIndex, ∑ rightLabel ∈ Finset.image pick Finset.univ,
          projectionOfDesign D (pick leftIndex) rightLabel ^ 2 :=
    Finset.sum_image fun left _ right _ hlr => hinj hlr
  have hinner : ∀ leftIndex : Fin size,
      ∑ rightLabel ∈ Finset.image pick Finset.univ,
          projectionOfDesign D (pick leftIndex) rightLabel ^ 2
        = ∑ rightIndex, projectionOfDesign D (pick leftIndex) (pick rightIndex) ^ 2 :=
    fun leftIndex => Finset.sum_image fun left _ right _ hlr => hinj hlr
  rw [blockSquareMass, houter]
  exact (Finset.sum_congr rfl fun leftIndex _ => hinner leftIndex).symm

/-- **THE BLOCK FROBENIUS MASS, READ ON THE COMPLEMENTARY BLOCK.**  Substituting
the complementary Frobenius law into the split form leaves the criterion depending
on the complementary labels only through their own squared mass. -/
theorem frobeniusNormSq_projectionGap_complementBlockForm (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    frobeniusNormSq (projectionGap D pick)
      = blockSquareMass D (Finset.image pick Finset.univ)ᶜ - (k : ℝ)
        + 2 * (∑ selectedIndex, D.weight (pick selectedIndex)
            * leverageOf (D.atom (pick selectedIndex))
              * (1 - D.weight (pick selectedIndex)))
        + ∑ selectedIndex, D.weight (pick selectedIndex) ^ 2 := by
  classical
  have hcompl := blockSquareMass_compl D (Finset.image pick Finset.univ)
  have hdiag : ∑ atomLabel ∈ Finset.image pick Finset.univ,
        D.weight atomLabel * leverageOf (D.atom atomLabel)
      = ∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex)) :=
    Finset.sum_image fun left _ right _ hlr => hinj hlr
  rw [hdiag] at hcompl
  rw [frobeniusNormSq_projectionGap, blockSquareMass_eq_of_injective D pick hinj]
  have hdiagEntry : ∑ selectedIndex, D.weight (pick selectedIndex)
        * projectionOfDesign D (pick selectedIndex) (pick selectedIndex)
      = ∑ selectedIndex, D.weight (pick selectedIndex)
          * (D.weight (pick selectedIndex) * leverageOf (D.atom (pick selectedIndex))) :=
    Finset.sum_congr rfl fun selectedIndex _ => by rw [projectionOfDesign_diagonal]
  have hcombine : ∑ selectedIndex, D.weight (pick selectedIndex)
          * leverageOf (D.atom (pick selectedIndex))
            * (1 - D.weight (pick selectedIndex))
      = (∑ selectedIndex, D.weight (pick selectedIndex)
            * leverageOf (D.atom (pick selectedIndex)))
        - ∑ selectedIndex, D.weight (pick selectedIndex)
            * (D.weight (pick selectedIndex) * leverageOf (D.atom (pick selectedIndex))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun selectedIndex _ => by ring
  rw [hdiagEntry]
  linarith [hcompl, hcombine]

/-- **THE ENGINE, ON THE COMPLEMENTARY BLOCK.**  A complementary block whose
squared mass is small enough refutes `Gtz.IsTie`. -/
theorem not_isTie_of_complementBlockSquareMass (D : WeightedDesign m 3) (pick : Fin 3 → Fin m)
    (hinj : Function.Injective pick)
    (htrace : 0 ≤ Matrix.trace (projectionGap D pick))
    (hcomplement : 2 * (blockSquareMass D (Finset.image pick Finset.univ)ᶜ - 3
          + 2 * (∑ selectedIndex, D.weight (pick selectedIndex)
              * leverageOf (D.atom (pick selectedIndex))
                * (1 - D.weight (pick selectedIndex)))
          + ∑ selectedIndex, D.weight (pick selectedIndex) ^ 2)
        < Matrix.trace (projectionGap D pick) ^ 2) :
    ¬ IsTie D := by
  refine not_isTie_of_projectionGap_isotropy D pick hinj htrace ?_
  rw [frobeniusNormSq_projectionGap_complementBlockForm D pick hinj]
  exact_mod_cast hcomplement

/-! ## 4c. The sign-flip group

`Gtz.atomMatrix` is `Matrix.vecMulVec g g`, so it does not read the sign of `g`.
Every statement that follows from `Gtz.IsTie` must therefore be invariant when
each atom is multiplied by its own sign.  The block criterion is: it reads the
weights, the leverage shares and the SQUARED Gram entries, and all three are
invariant.  Nothing below assumes the signs are `1` or `-1` beyond the square
being one. -/

/-- **The sign flip of a design.**  Each atom is multiplied by a scalar of square
one.  Parseval survives because `Gtz.atomMatrix_smul` squares the scalar. -/
noncomputable def signFlipDesign (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) : WeightedDesign m k where
  atom := fun atomLabel => sign atomLabel • D.atom atomLabel
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    rw [← D.isParseval]
    exact Finset.sum_congr rfl fun atomLabel _ => by
      rw [atomMatrix_smul, hsign atomLabel, one_smul]

@[simp] theorem signFlipDesign_weight (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) :
    (signFlipDesign D sign hsign).weight = D.weight := rfl

/-- The atom matrices are untouched by a sign flip. -/
theorem atomMatrix_signFlipDesign (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) (atomLabel : Fin m) :
    atomMatrix ((signFlipDesign D sign hsign).atom atomLabel)
      = atomMatrix (D.atom atomLabel) := by
  show atomMatrix (sign atomLabel • D.atom atomLabel) = atomMatrix (D.atom atomLabel)
  rw [atomMatrix_smul, hsign atomLabel, one_smul]

/-- Every subset sum, and hence every domination question, is untouched. -/
theorem subsetSum_signFlipDesign (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) (selected : Finset (Fin m)) :
    subsetSum (signFlipDesign D sign hsign) selected = subsetSum D selected :=
  Finset.sum_congr rfl fun atomLabel _ => atomMatrix_signFlipDesign D sign hsign atomLabel

/-- **`Gtz.IsTie` IS INVARIANT UNDER THE SIGN-FLIP GROUP.** -/
theorem isTie_signFlipDesign_iff (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) :
    IsTie (signFlipDesign D sign hsign) ↔ IsTie D := by
  constructor
  · rintro ⟨⟨selected, hcard, hdom⟩, hnostrict⟩
    refine ⟨⟨selected, hcard, ?_⟩, fun other hother => ?_⟩
    · rwa [Dominates, ← subsetSum_signFlipDesign D sign hsign selected]
    · rw [← subsetSum_signFlipDesign D sign hsign other]
      exact hnostrict other hother
  · rintro ⟨⟨selected, hcard, hdom⟩, hnostrict⟩
    refine ⟨⟨selected, hcard, ?_⟩, fun other hother => ?_⟩
    · rwa [Dominates, subsetSum_signFlipDesign D sign hsign selected]
    · rw [subsetSum_signFlipDesign D sign hsign other]
      exact hnostrict other hother

/-- The leverage of an atom is untouched by a sign flip. -/
theorem leverageOf_signFlipDesign (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) (atomLabel : Fin m) :
    leverageOf ((signFlipDesign D sign hsign).atom atomLabel)
      = leverageOf (D.atom atomLabel) := by
  show leverageOf (sign atomLabel • D.atom atomLabel) = leverageOf (D.atom atomLabel)
  rw [leverageOf_smul, hsign atomLabel, one_mul]

/-- The SQUARED Gram entries are untouched by a sign flip. -/
theorem sq_dotProduct_signFlipDesign (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) (leftLabel rightLabel : Fin m) :
    ((signFlipDesign D sign hsign).atom leftLabel
        ⬝ᵥ (signFlipDesign D sign hsign).atom rightLabel) ^ 2
      = (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := by
  show ((sign leftLabel • D.atom leftLabel) ⬝ᵥ (sign rightLabel • D.atom rightLabel)) ^ 2
    = (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_pow, mul_pow,
    hsign leftLabel, hsign rightLabel, one_mul, one_mul]

/-- **THE BLOCK TRACE IS SIGN-BLIND.** -/
theorem trace_projectionGap_signFlipDesign (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix.trace (projectionGap (signFlipDesign D sign hsign) pick)
      = Matrix.trace (projectionGap D pick) := by
  rw [trace_projectionGap, trace_projectionGap]
  exact Finset.sum_congr rfl fun selectedIndex _ => by
    rw [leverageOf_signFlipDesign D sign hsign (pick selectedIndex)]
    rfl

/-- **THE BLOCK FROBENIUS MASS IS SIGN-BLIND.**  The criterion reads only the
squared Gram entries, which the flip conjugates away. -/
theorem frobeniusNormSq_projectionGap_signFlipDesign (D : WeightedDesign m k)
    (sign : Fin m → ℝ) (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) {size : ℕ}
    (pick : Fin size → Fin m) :
    frobeniusNormSq (projectionGap (signFlipDesign D sign hsign) pick)
      = frobeniusNormSq (projectionGap D pick) := by
  rw [frobeniusNormSq_projectionGap_gramForm, frobeniusNormSq_projectionGap_gramForm]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun leftIndex _ => Finset.sum_congr rfl fun rightIndex _ => ?_
      rw [sq_dotProduct_signFlipDesign D sign hsign (pick leftIndex) (pick rightIndex)]
      rfl
    · congr 1
      exact Finset.sum_congr rfl fun selectedIndex _ => by
        rw [leverageOf_signFlipDesign D sign hsign (pick selectedIndex)]
        rfl

/-- **THE ENGINE RESPECTS THE SIGN-FLIP GROUP.**  A selection that fires on a
design fires on every sign flip of it, and the two designs are ties together.  So
the engine cannot separate points that `Gtz.IsTie` cannot separate. -/
theorem projectionGap_isotropy_signFlipDesign_iff (D : WeightedDesign m k) (sign : Fin m → ℝ)
    (hsign : ∀ atomLabel, sign atomLabel ^ 2 = 1) {size : ℕ} (pick : Fin size → Fin m) :
    (2 * frobeniusNormSq (projectionGap (signFlipDesign D sign hsign) pick)
        < Matrix.trace (projectionGap (signFlipDesign D sign hsign) pick) ^ 2)
      ↔ (2 * frobeniusNormSq (projectionGap D pick)
        < Matrix.trace (projectionGap D pick) ^ 2) := by
  rw [frobeniusNormSq_projectionGap_signFlipDesign D sign hsign pick,
    trace_projectionGap_signFlipDesign D sign hsign pick]

/-! ## 5. The foil

`Gtz.capFoilDesign` is the landed stress-free `(6,3)` design at which no selection
and no admissible scalar cap fires
(`Gtz.capFoilDesign_not_posDef_projectionBlock`).  The block isotropy test fires
at it, on three of the twenty triples. -/

/-- The three selections of the foil that this module reads. -/
def foilPickLeft : Fin 3 → Fin 6 := ![0, 1, 5]

/-- The selection at which the block test fires and the gap test does not. -/
def foilPickMiddle : Fin 3 → Fin 6 := ![0, 3, 5]

/-- The selection at which the gap test fires and the block test does not. -/
def foilPickRight : Fin 3 → Fin 6 := ![1, 3, 5]

theorem foilPickLeft_injective : Function.Injective foilPickLeft := by decide
theorem foilPickMiddle_injective : Function.Injective foilPickMiddle := by decide
theorem foilPickRight_injective : Function.Injective foilPickRight := by decide

/-- A six-entry vector read at index three.  The tree carries the reduction only
up to index four, and the foil needs index five. -/
@[simp] theorem consSix_apply_three {Entry : Type*} (first second third fourth fifth sixth : Entry) :
    ![first, second, third, fourth, fifth, sixth] 3 = fourth := rfl

/-- A six-entry vector read at index four. -/
@[simp] theorem consSix_apply_four {Entry : Type*} (first second third fourth fifth sixth : Entry) :
    ![first, second, third, fourth, fifth, sixth] 4 = fifth := rfl

/-- A six-entry vector read at index five. -/
@[simp] theorem consSix_apply_five {Entry : Type*} (first second third fourth fifth sixth : Entry) :
    ![first, second, third, fourth, fifth, sixth] 5 = sixth := rfl

@[simp] theorem foilPickLeft_zero : foilPickLeft 0 = 0 := rfl
@[simp] theorem foilPickLeft_one : foilPickLeft 1 = 1 := rfl
@[simp] theorem foilPickLeft_two : foilPickLeft 2 = 5 := rfl
@[simp] theorem foilPickMiddle_zero : foilPickMiddle 0 = 0 := rfl
@[simp] theorem foilPickMiddle_one : foilPickMiddle 1 = 3 := rfl
@[simp] theorem foilPickMiddle_two : foilPickMiddle 2 = 5 := rfl
@[simp] theorem foilPickRight_zero : foilPickRight 0 = 1 := rfl
@[simp] theorem foilPickRight_one : foilPickRight 1 = 3 := rfl
@[simp] theorem foilPickRight_two : foilPickRight 2 = 5 := rfl

/-- The foil data that the three selections read, unfolded to explicit vectors.
The per-label equations of `Gtz.foilAtom` and `Gtz.foilWeight` are already in the
tree, so nothing here recomputes the design. -/
theorem capFoil_atom_weight_unfold :
    capFoilDesign.atom = foilAtom ∧ capFoilDesign.weight = foilWeight := ⟨rfl, rfl⟩

/-- The block trace at the left selection. -/
theorem trace_projectionGap_capFoil_left :
    Matrix.trace (projectionGap capFoilDesign foilPickLeft) = 55 / 42 := by
  rw [trace_projectionGap, Fin.sum_univ_three]
  norm_num [foilPickLeft_zero, foilPickLeft_one, foilPickLeft_two, capFoilDesign_atom,
    capFoilDesign_weight, foilAtom_zero, foilAtom_one, foilAtom_five, foilWeight_zero,
    foilWeight_one, foilWeight_five, leverageOf, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The block Frobenius mass at the left selection. -/
theorem frobeniusNormSq_projectionGap_capFoil_left :
    frobeniusNormSq (projectionGap capFoilDesign foilPickLeft) = 1345 / 1764 := by
  rw [frobeniusNormSq_projectionGap_gramForm, Fin.sum_univ_three]
  norm_num [Fin.sum_univ_three, foilPickLeft_zero, foilPickLeft_one, foilPickLeft_two,
    capFoilDesign_atom, capFoilDesign_weight, foilAtom_zero, foilAtom_one, foilAtom_five,
    foilWeight_zero, foilWeight_one, foilWeight_five, leverageOf, dotProduct,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- **THE BLOCK ISOTROPY TEST FIRES AT THE FOIL.**  The left selection has squared
block trace `3025/1764` against twice the block Frobenius mass `2690/1764`. -/
theorem capFoil_projectionGap_isotropy_left :
    2 * frobeniusNormSq (projectionGap capFoilDesign foilPickLeft)
      < Matrix.trace (projectionGap capFoilDesign foilPickLeft) ^ 2 := by
  rw [trace_projectionGap_capFoil_left, frobeniusNormSq_projectionGap_capFoil_left]
  norm_num

/-- **THE FOIL IS NOT A TIE, BY THE BOUNDED ENGINE.**  Every number the proof reads
lies in `[0, 1]`, and no scalar cap fires anywhere on this design. -/
theorem capFoil_not_isTie_of_projectionGap :
    ¬ IsTie capFoilDesign :=
  not_isTie_of_projectionGap_isotropy capFoilDesign foilPickLeft foilPickLeft_injective
    (by rw [trace_projectionGap_capFoil_left]; norm_num)
    capFoil_projectionGap_isotropy_left

/-! ### The two readings are incomparable

The gap matrix and the projection block are congruent, not similar, so the two
isotropy tests are different tests.  Both directions of the separation occur on
this one design. -/

/-- The block trace at the middle selection. -/
theorem trace_projectionGap_capFoil_middle :
    Matrix.trace (projectionGap capFoilDesign foilPickMiddle) = 47 / 42 := by
  rw [trace_projectionGap, Fin.sum_univ_three]
  norm_num [foilPickMiddle_zero, foilPickMiddle_one, foilPickMiddle_two, capFoilDesign_atom,
    capFoilDesign_weight, foilAtom_zero, foilAtom_three, foilAtom_five, foilWeight_zero,
    foilWeight_three, foilWeight_five, leverageOf, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The block Frobenius mass at the middle selection. -/
theorem frobeniusNormSq_projectionGap_capFoil_middle :
    frobeniusNormSq (projectionGap capFoilDesign foilPickMiddle) = 1081 / 1764 := by
  rw [frobeniusNormSq_projectionGap_gramForm, Fin.sum_univ_three]
  norm_num [Fin.sum_univ_three, foilPickMiddle_zero, foilPickMiddle_one, foilPickMiddle_two,
    capFoilDesign_atom, capFoilDesign_weight, foilAtom_zero, foilAtom_three, foilAtom_five,
    foilWeight_zero, foilWeight_three, foilWeight_five, leverageOf, dotProduct,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- **THE BLOCK TEST FIRES AT THE MIDDLE SELECTION.** -/
theorem capFoil_projectionGap_isotropy_middle :
    2 * frobeniusNormSq (projectionGap capFoilDesign foilPickMiddle)
      < Matrix.trace (projectionGap capFoilDesign foilPickMiddle) ^ 2 := by
  rw [trace_projectionGap_capFoil_middle, frobeniusNormSq_projectionGap_capFoil_middle]
  norm_num

/-- The gap matrix of the middle selection, in closed form. -/
theorem capFoil_gapMatrix_middle :
    subsetSum capFoilDesign {0, 3, 5} - 1 = !![4, 1, 4; 1, 4, 0; 4, 0, 5] := by
  have hsum : subsetSum capFoilDesign {0, 3, 5}
      = atomMatrix (capFoilDesign.atom 0) + atomMatrix (capFoilDesign.atom 3)
        + atomMatrix (capFoilDesign.atom 5) := by
    simp only [subsetSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      add_assoc]
  rw [hsum]
  ext rowIndex columnIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    capFoilDesign_atom, foilAtom_zero, foilAtom_one, foilAtom_three, foilAtom_five,
    Matrix.one_apply]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- **THE GAP TEST DOES NOT FIRE AT THE MIDDLE SELECTION.**  Trace `13`, Frobenius
mass `91`, and `2 * 91 = 182` is more than `13 ^ 2 = 169`. -/
theorem capFoil_gap_not_isotropy_middle :
    ¬ (2 * frobeniusNormSq (subsetSum capFoilDesign {0, 3, 5} - 1)
      < Matrix.trace (subsetSum capFoilDesign {0, 3, 5} - 1) ^ 2) := by
  rw [capFoil_gapMatrix_middle]
  simp only [frobeniusNormSq, frobeniusInner, Fin.sum_univ_three, Matrix.trace_fin_three,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val', Matrix.of_apply]
  norm_num

/-- The block trace at the right selection. -/
theorem trace_projectionGap_capFoil_right :
    Matrix.trace (projectionGap capFoilDesign foilPickRight) = 8 / 7 := by
  rw [trace_projectionGap, Fin.sum_univ_three]
  norm_num [foilPickRight_zero, foilPickRight_one, foilPickRight_two, capFoilDesign_atom,
    capFoilDesign_weight, foilAtom_one, foilAtom_three, foilAtom_five, foilWeight_one,
    foilWeight_three, foilWeight_five, leverageOf, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The block Frobenius mass at the right selection. -/
theorem frobeniusNormSq_projectionGap_capFoil_right :
    frobeniusNormSq (projectionGap capFoilDesign foilPickRight) = 2 / 3 := by
  rw [frobeniusNormSq_projectionGap_gramForm, Fin.sum_univ_three]
  norm_num [Fin.sum_univ_three, foilPickRight_zero, foilPickRight_one, foilPickRight_two,
    capFoilDesign_atom, capFoilDesign_weight, foilAtom_one, foilAtom_three, foilAtom_five,
    foilWeight_one, foilWeight_three, foilWeight_five, leverageOf, dotProduct,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- **THE BLOCK TEST DOES NOT FIRE AT THE RIGHT SELECTION.**  Squared block trace
`64/49`, twice the block Frobenius mass `4/3`. -/
theorem capFoil_projectionGap_not_isotropy_right :
    ¬ (2 * frobeniusNormSq (projectionGap capFoilDesign foilPickRight)
      < Matrix.trace (projectionGap capFoilDesign foilPickRight) ^ 2) := by
  rw [trace_projectionGap_capFoil_right, frobeniusNormSq_projectionGap_capFoil_right]
  norm_num

/-- The gap matrix of the right selection, in closed form. -/
theorem capFoil_gapMatrix_right :
    subsetSum capFoilDesign {1, 3, 5} - 1 = !![4, 0, 1; 0, 3, -2; 1, -2, 2] := by
  have hsum : subsetSum capFoilDesign {1, 3, 5}
      = atomMatrix (capFoilDesign.atom 1) + atomMatrix (capFoilDesign.atom 3)
        + atomMatrix (capFoilDesign.atom 5) := by
    simp only [subsetSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      add_assoc]
  rw [hsum]
  ext rowIndex columnIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    capFoilDesign_atom, foilAtom_zero, foilAtom_one, foilAtom_three, foilAtom_five,
    Matrix.one_apply]
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- **THE GAP TEST FIRES AT THE RIGHT SELECTION.**  Trace `9`, Frobenius mass `39`,
and `2 * 39 = 78` is under `9 ^ 2 = 81`. -/
theorem capFoil_gap_isotropy_right :
    2 * frobeniusNormSq (subsetSum capFoilDesign {1, 3, 5} - 1)
      < Matrix.trace (subsetSum capFoilDesign {1, 3, 5} - 1) ^ 2 := by
  rw [capFoil_gapMatrix_right]
  simp only [frobeniusNormSq, frobeniusInner, Fin.sum_univ_three, Matrix.trace_fin_three,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val', Matrix.of_apply]
  norm_num

/-- **NEITHER ISOTROPY TEST CONTAINS THE OTHER.**  On one landed design, one triple
passes the block test and fails the gap test, and another triple does the
opposite.  The two readings of the same criterion are genuinely different
instruments. -/
theorem capFoil_isotropy_tests_incomparable :
    (2 * frobeniusNormSq (projectionGap capFoilDesign foilPickMiddle)
        < Matrix.trace (projectionGap capFoilDesign foilPickMiddle) ^ 2
      ∧ ¬ (2 * frobeniusNormSq (subsetSum capFoilDesign {0, 3, 5} - 1)
        < Matrix.trace (subsetSum capFoilDesign {0, 3, 5} - 1) ^ 2))
    ∧ (2 * frobeniusNormSq (subsetSum capFoilDesign {1, 3, 5} - 1)
        < Matrix.trace (subsetSum capFoilDesign {1, 3, 5} - 1) ^ 2
      ∧ ¬ (2 * frobeniusNormSq (projectionGap capFoilDesign foilPickRight)
        < Matrix.trace (projectionGap capFoilDesign foilPickRight) ^ 2)) :=
  ⟨⟨capFoil_projectionGap_isotropy_middle, capFoil_gap_not_isotropy_middle⟩,
    ⟨capFoil_gap_isotropy_right, capFoil_projectionGap_not_isotropy_right⟩⟩

/-! ## 6. The threshold is attained at the tetrahedron

`Gtz.tetraDesign` is the `(4,3)` tie.  Its blocks sit exactly on the criterion's
boundary, so the engine misses size four by zero margin.  Nothing in this module
can reach `(4,3)`, and the reason is not a weakness of the proof. -/

/-- Every tetrahedron atom has leverage three. -/
theorem tetraDesign_leverageOf (dirIndex : Fin 4) :
    leverageOf (tetraDesign.atom dirIndex) = 3 := by
  rw [← dotProduct_self_eq_leverageOf]
  exact tetraAtom_dot_self dirIndex

/-- **THE BLOCK TRACE AT THE TETRAHEDRON IS THREE HALVES**, at every selection. -/
theorem trace_projectionGap_tetraDesign (pick : Fin 3 → Fin 4) :
    Matrix.trace (projectionGap tetraDesign pick) = 3 / 2 := by
  rw [trace_projectionGap, Fin.sum_univ_three]
  simp only [tetraDesign_leverageOf]
  show (1 : ℝ) / 4 * 3 - 1 / 4 + (1 / 4 * 3 - 1 / 4) + (1 / 4 * 3 - 1 / 4) = 3 / 2
  norm_num

/-- **THE BLOCK FROBENIUS MASS AT THE TETRAHEDRON IS NINE EIGHTHS**, at every
injective selection.  The off-diagonal Gram entries are all `-1`, so the block is
the same up to relabelling whichever three directions are chosen. -/
theorem frobeniusNormSq_projectionGap_tetraDesign (pick : Fin 3 → Fin 4)
    (hinj : Function.Injective pick) :
    frobeniusNormSq (projectionGap tetraDesign pick) = 9 / 8 := by
  have hpair : ∀ leftIndex rightIndex : Fin 3, leftIndex ≠ rightIndex →
      (tetraDesign.atom (pick leftIndex) ⬝ᵥ tetraDesign.atom (pick rightIndex)) ^ 2 = 1 := by
    intro leftIndex rightIndex hne
    have hlabel : pick leftIndex ≠ pick rightIndex := fun heq => hne (hinj heq)
    rw [show tetraDesign.atom = tetraAtom from rfl, tetraAtom_dot_of_ne hlabel]
    norm_num
  have hself : ∀ selectedIndex : Fin 3,
      (tetraDesign.atom (pick selectedIndex) ⬝ᵥ tetraDesign.atom (pick selectedIndex)) ^ 2
        = 9 := by
    intro selectedIndex
    rw [show tetraDesign.atom = tetraAtom from rfl, tetraAtom_dot_self]
    norm_num
  rw [frobeniusNormSq_projectionGap_gramForm, Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, tetraDesign_leverageOf]
  rw [hself 0, hself 1, hself 2, hpair 0 1 (by decide), hpair 0 2 (by decide),
    hpair 1 0 (by decide), hpair 1 2 (by decide), hpair 2 0 (by decide),
    hpair 2 1 (by decide)]
  show (1 : ℝ) / 4 * (1 / 4) * 9 + 1 / 4 * (1 / 4) * 1 + 1 / 4 * (1 / 4) * 1
      + (1 / 4 * (1 / 4) * 1 + 1 / 4 * (1 / 4) * 9 + 1 / 4 * (1 / 4) * 1)
      + (1 / 4 * (1 / 4) * 1 + 1 / 4 * (1 / 4) * 1 + 1 / 4 * (1 / 4) * 9)
      - 2 * ((1 / 4) ^ 2 * 3 + (1 / 4) ^ 2 * 3 + (1 / 4) ^ 2 * 3)
      + ((1 / 4) ^ 2 + (1 / 4) ^ 2 + (1 / 4) ^ 2) = 9 / 8
  norm_num

/-- **THE THRESHOLD IS ATTAINED AT THE `(4,3)` TIE.**  Every injective selection of
the tetrahedron has squared block trace exactly twice its block Frobenius mass, so
the strict inequality of the engine fails by exactly zero.  The engine therefore
does not reach size four, and no relaxation of the constant would let it. -/
theorem tetraDesign_projectionGap_boundary (pick : Fin 3 → Fin 4)
    (hinj : Function.Injective pick) :
    Matrix.trace (projectionGap tetraDesign pick) ^ 2
      = 2 * frobeniusNormSq (projectionGap tetraDesign pick) := by
  rw [trace_projectionGap_tetraDesign, frobeniusNormSq_projectionGap_tetraDesign pick hinj]
  norm_num

end Gtz

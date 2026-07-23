/-
# The deflation engine: coisometries push weighted designs forward

The all-k induction (the Lifting-Lemma route) deflates dimension: fix a
pivot atom, project the others onto its orthocomplement, and the
projections satisfy the SAME-weight Parseval identity in dimension `k−1`.
The engine underneath is coordinate-free and unconditional: ANY coisometry
`B` (`B·Bᵀ = 1`) pushes a weighted design forward to a weighted design —
same weights, atoms `B·g_c`. The orthocomplement projection is the
instance where `B`'s rows are an orthonormal completion basis.

This is the first kernel footprint of the all-k frontier: the induction's
Parseval step is now a theorem, independent of the (open) pivot-selection
content of the Lifting Lemma itself.
-/
import Mathlib
import Gtz.Basic
import Gtz.Completion
import Gtz.PsdKit
import Gtz.MarginTransfer
import Gtz.TraceIdentity
import Gtz.Reductions

namespace Gtz

open Matrix Finset

variable {m k j : ℕ}

/-- **Rectangular conjugation of a rank-one square**:
`(B·g)(B·g)ᵀ = B·(g gᵀ)·Bᵀ` for any rectangular `B`. -/
theorem atomMatrix_mulVec_conj (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (direction : Fin k → ℝ) :
    atomMatrix (rectangular *ᵥ direction)
      = rectangular * atomMatrix direction * rectangularᵀ := by
  ext row col
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec,
    Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  conv_rhs => simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun innerLeft _ => ?_
  refine Finset.sum_congr rfl fun innerRight _ => ?_
  ring

/-- **The coisometry pushforward**: a weighted design in dimension `k`
pushes forward along any coisometry `B : ℝᵏ → ℝʲ` (`B·Bᵀ = 1`) to a
weighted design in dimension `j` with the SAME weights — the deflation
induction's Parseval step, unconditional. -/
def coisometryPushforward (D : WeightedDesign m k)
    (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (hcoisometry : rectangular * rectangularᵀ = 1) : WeightedDesign m j where
  atom index := rectangular *ᵥ D.atom index
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    have hconjugated : ∑ index, D.weight index
        • atomMatrix (rectangular *ᵥ D.atom index)
        = rectangular * (∑ index, D.weight index
            • atomMatrix (D.atom index)) * rectangularᵀ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun index _ => ?_
      rw [atomMatrix_mulVec_conj, Matrix.mul_smul, Matrix.smul_mul]
    rw [hconjugated, D.isParseval, Matrix.mul_one, hcoisometry]

/-- The pushforward keeps every weight (definitional reading). -/
theorem coisometryPushforward_weight (D : WeightedDesign m k)
    (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (hcoisometry : rectangular * rectangularᵀ = 1) (index : Fin m) :
    (coisometryPushforward D rectangular hcoisometry).weight index
      = D.weight index := rfl

/-- The pushforward's atoms are the projected atoms (definitional
reading). -/
theorem coisometryPushforward_atom (D : WeightedDesign m k)
    (rectangular : Matrix (Fin j) (Fin k) ℝ)
    (hcoisometry : rectangular * rectangularᵀ = 1) (index : Fin m) :
    (coisometryPushforward D rectangular hcoisometry).atom index
      = rectangular *ᵥ D.atom index := rfl

/-- **The deflation coisometry exists**: every unit pivot direction in
`ℝ^(k+1)` admits a coisometry `B : ℝ^(k+1) → ℝᵏ` whose rows are orthonormal
and orthogonal to the pivot, with the completeness split
`Bᵀ·B + u·uᵀ = 1` — the orthonormal basis of `u^⊥` packaged as the matrix
the pushforward consumes. Instantiates `exists_orthonormal_completion` at
one column and transposes. -/
theorem exists_deflation_coisometry {k : ℕ} {pivotDir : Fin (k + 1) → ℝ}
    (hpivotUnit : pivotDir ⬝ᵥ pivotDir = 1) :
    ∃ deflator : Matrix (Fin k) (Fin (k + 1)) ℝ,
      deflator * deflatorᵀ = 1
        ∧ deflator *ᵥ pivotDir = 0
        ∧ deflatorᵀ * deflator + atomMatrix pivotDir = 1 := by
  set pivotColumn : Matrix (Fin (k + 1)) (Fin 1) ℝ :=
    fun rowIndex _ => pivotDir rowIndex with hpivotColumn
  have hcolumnOrtho : pivotColumnᵀ * pivotColumn = 1 := by
    ext firstIndex secondIndex
    fin_cases firstIndex
    fin_cases secondIndex
    simpa [hpivotColumn, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, dotProduct] using hpivotUnit
  obtain ⟨completion, hcompletionOrtho, hcrossZero, hcomplete⟩ :=
    exists_orthonormal_completion pivotColumn hcolumnOrtho
  refine ⟨completionᵀ, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]
    exact hcompletionOrtho
  · funext rowIndex
    have hcrossEntry := congrFun (congrFun hcrossZero 0) rowIndex
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      hpivotColumn] at hcrossEntry
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.zero_apply]
    rw [Finset.sum_congr rfl fun index _ =>
      mul_comm (completion index rowIndex) (pivotDir index)]
    exact hcrossEntry
  · have hpivotSquare : pivotColumn * pivotColumnᵀ = atomMatrix pivotDir := by
      ext firstIndex secondIndex
      simp [hpivotColumn, Matrix.mul_apply, Matrix.transpose_apply,
        atomMatrix, Matrix.vecMulVec_apply]
    rw [Matrix.transpose_transpose]
    rw [hpivotSquare] at hcomplete
    rw [← hcomplete]
    exact add_comm (completion * completionᵀ) (atomMatrix pivotDir)

/-- **Pivot deflation, end-to-end**: every NONZERO atom of a weighted design
in dimension `k+1` yields a positive normalizing scale and a deflation
coisometry — rows orthonormal, annihilating the atom itself, with the
completeness split at the normalized direction. Feeding `deflator` to
`coisometryPushforward` gives the projected design of the SS15 induction
step; no unit-norm hypothesis survives, only `atom ≠ 0`. -/
theorem exists_pivot_deflation {m k : ℕ} (D : WeightedDesign m (k + 1))
    (pivot : Fin m) (hpivotNonzero : D.atom pivot ≠ 0) :
    ∃ (scale : ℝ) (deflator : Matrix (Fin k) (Fin (k + 1)) ℝ),
      0 < scale
        ∧ deflator * deflatorᵀ = 1
        ∧ deflator *ᵥ D.atom pivot = 0
        ∧ deflatorᵀ * deflator + atomMatrix (scale • D.atom pivot) = 1 := by
  set lev := D.atom pivot ⬝ᵥ D.atom pivot with hlev
  have hlevNonneg : 0 ≤ lev := by
    rw [hlev]
    simp only [dotProduct]
    exact Finset.sum_nonneg fun index _ => mul_self_nonneg _
  have hlevPos : 0 < lev := by
    rcases eq_or_lt_of_le hlevNonneg with hzero | hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hpivotNonzero
    · exact hpos
  have hsqrtPos : 0 < Real.sqrt lev := Real.sqrt_pos.mpr hlevPos
  have hunit : ((Real.sqrt lev)⁻¹ • D.atom pivot)
      ⬝ᵥ ((Real.sqrt lev)⁻¹ • D.atom pivot) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hlevPos.le]
    exact inv_mul_cancel₀ (ne_of_gt hlevPos)
  obtain ⟨deflator, hcoisometry, hkillScaled, hsplit⟩ :=
    exists_deflation_coisometry hunit
  refine ⟨(Real.sqrt lev)⁻¹, deflator, inv_pos.mpr hsqrtPos, hcoisometry,
    ?_, hsplit⟩
  have hkillSmul : (Real.sqrt lev)⁻¹ • (deflator *ᵥ D.atom pivot) = 0 := by
    rw [← Matrix.mulVec_smul]
    exact hkillScaled
  rcases smul_eq_zero.mp hkillSmul with hscaleZero | hvecZero
  · exact absurd hscaleZero (inv_ne_zero (ne_of_gt hsqrtPos))
  · exact hvecZero

/-- The rank-one square acts as projection onto the pivot line:
`(u uᵀ)·v = ⟨u,v⟩·u`. -/
theorem atomMatrix_mulVec_eq_dot_smul {k : ℕ} (pivotDir anyVec : Fin k → ℝ) :
    atomMatrix pivotDir *ᵥ anyVec = (pivotDir ⬝ᵥ anyVec) • pivotDir := by
  funext index
  simp only [atomMatrix, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

/-- **Orthogonal decomposition along a deflation**: the completeness split
`Bᵀ·B + u·uᵀ = 1` decomposes EVERY vector into its orthocomplement part
(pulled back through the deflator) plus its pivot component — the
coordinate engine behind the cross-vector `r` and the projected Gram `G′`
of the Schur lift condition. -/
theorem decompose_along_deflation {k : ℕ} {pivotDir : Fin (k + 1) → ℝ}
    {deflator : Matrix (Fin k) (Fin (k + 1)) ℝ}
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotDir = 1)
    (anyVec : Fin (k + 1) → ℝ) :
    deflatorᵀ *ᵥ (deflator *ᵥ anyVec)
      + (pivotDir ⬝ᵥ anyVec) • pivotDir = anyVec := by
  have happlied : (deflatorᵀ * deflator) *ᵥ anyVec
      + atomMatrix pivotDir *ᵥ anyVec = anyVec := by
    have happly := congrArg (fun matrixValue => matrixValue *ᵥ anyVec) hsplit
    simpa [Matrix.add_mulVec] using happly
  rw [← Matrix.mulVec_mulVec, atomMatrix_mulVec_eq_dot_smul] at happlied
  exact happlied

/-- **Parseval split of inner products along a deflation**: the adapted
basis `{orthocomplement} ⊕ {pivot line}` preserves every inner product —
`⟨l,r⟩ = ⟨Bl,Br⟩ + ⟨u,l⟩⟨u,r⟩`. Both the cross-vector `r_c = ⟨u,g_c⟩` and
the projected Gram of the Schur lift condition read off this identity. -/
theorem dotProduct_split_along_deflation {k : ℕ}
    {pivotUnit : Fin (k + 1) → ℝ}
    {deflator : Matrix (Fin k) (Fin (k + 1)) ℝ}
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (leftVec rightVec : Fin (k + 1) → ℝ) :
    leftVec ⬝ᵥ rightVec
      = (deflator *ᵥ leftVec) ⬝ᵥ (deflator *ᵥ rightVec)
        + (pivotUnit ⬝ᵥ leftVec) * (pivotUnit ⬝ᵥ rightVec) := by
  conv_lhs => rw [← decompose_along_deflation hsplit leftVec]
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul,
    dotProduct_mulVec_transpose]

/-- A quadratic with nonnegative leading and constant coefficients and a
dominated discriminant is globally nonnegative — the scalar heart of the
bordered Schur sufficiency, boundary-robust (no inverse, no division). -/
theorem quadratic_nonneg_of_discriminant {leading crossTerm constantTerm : ℝ}
    (hleading : 0 ≤ leading) (hconstant : 0 ≤ constantTerm)
    (hdiscriminant : crossTerm ^ 2 ≤ leading * constantTerm)
    (coordinate : ℝ) :
    0 ≤ leading * coordinate ^ 2 + 2 * coordinate * crossTerm
      + constantTerm := by
  rcases eq_or_lt_of_le hleading with hleadingZero | hleadingPos
  · have hcrossSq : crossTerm ^ 2 ≤ 0 := by
      calc crossTerm ^ 2 ≤ leading * constantTerm := hdiscriminant
        _ = 0 := by rw [← hleadingZero, zero_mul]
    have hcrossZero : crossTerm = 0 :=
      pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp
        (le_antisymm hcrossSq (sq_nonneg _))
    rw [← hleadingZero, hcrossZero]
    simpa using hconstant
  · nlinarith [sq_nonneg (leading * coordinate + crossTerm), hdiscriminant,
      hleadingPos]

/-- **The Schur lift condition, sufficiency half, inverse-free** (SS15
gtz.md:631-634 without the `(G′−I)⁻¹`): if the projected subset dominates
in the orthocomplement and the leverage/cross data satisfy the
DISCRIMINANT condition — the boundary-robust reading of
`|g_{c*}|² ≥ 1 + rᵀ(G′−I)⁻¹r` — then the bordered `(k+1)`-subset
`{pivot} ∪ C′` dominates outright. Pure quadratic-form algebra: every test
vector splits along the deflation, the pivot contributes only through its
`u`-component (its projection is killed), and the mixed terms are absorbed
by the discriminant bound. -/
theorem dominates_insert_of_projection_certificates {m k : ℕ}
    (D : WeightedDesign m (k + 1)) (pivot : Fin m)
    {pivotUnit : Fin (k + 1) → ℝ}
    {deflator : Matrix (Fin k) (Fin (k + 1)) ℝ}
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (hprojectedDominates : ∀ testVec : Fin k → ℝ,
      testVec ⬝ᵥ testVec
        ≤ ∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
    (hleverageFloor : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
        + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
    (hdiscriminant : ∀ testVec : Fin k → ℝ,
      (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
          * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
        ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
              + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
            * ((∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
              - testVec ⬝ᵥ testVec)) :
    Dominates D (insert pivot subset) := by
  show (subsetSum D (insert pivot subset) - 1).PosSemidef
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun anyW => ?_⟩
  · have htranspose : (subsetSum D (insert pivot subset)
        - (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))ᵀ
        = subsetSum D (insert pivot subset) - 1 := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum]
      rw [Matrix.transpose_sum]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      ext rowIdx colIdx
      simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply,
        mul_comm]
    exact isHermitian_of_transpose_eq htranspose
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    have hformExpand : anyW ⬝ᵥ (subsetSum D (insert pivot subset) *ᵥ anyW)
        = ∑ c ∈ insert pivot subset, (D.atom c ⬝ᵥ anyW) ^ 2 := by
      rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
      exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (D.atom c) anyW
    rw [hformExpand, Finset.sum_insert hnotMem]
    have hpivotDot : D.atom pivot ⬝ᵥ anyW
        = (pivotUnit ⬝ᵥ D.atom pivot) * (pivotUnit ⬝ᵥ anyW) := by
      rw [dotProduct_split_along_deflation hsplit (D.atom pivot) anyW, hkill,
        zero_dotProduct, zero_add]
    have hmemberDot : ∀ c ∈ subset, (D.atom c ⬝ᵥ anyW) ^ 2
        = ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)
            + (pivotUnit ⬝ᵥ D.atom c) * (pivotUnit ⬝ᵥ anyW)) ^ 2 :=
      fun c _ => by
        rw [dotProduct_split_along_deflation hsplit (D.atom c) anyW]
    have hnormSplit : anyW ⬝ᵥ anyW
        = (deflator *ᵥ anyW) ⬝ᵥ (deflator *ᵥ anyW)
          + (pivotUnit ⬝ᵥ anyW) * (pivotUnit ⬝ᵥ anyW) :=
      dotProduct_split_along_deflation hsplit anyW anyW
    rw [hpivotDot, Finset.sum_congr rfl hmemberDot, hnormSplit]
    have hsumExpand : ∑ c ∈ subset,
        ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)
          + (pivotUnit ⬝ᵥ D.atom c) * (pivotUnit ⬝ᵥ anyW)) ^ 2
        = (∑ c ∈ subset,
            ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)) ^ 2)
          + 2 * (pivotUnit ⬝ᵥ anyW)
            * (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
                * ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)))
          + (pivotUnit ⬝ᵥ anyW) ^ 2
            * (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hsumExpand]
    have hconstantNonneg :
        0 ≤ (∑ c ∈ subset,
            ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)) ^ 2)
          - (deflator *ᵥ anyW) ⬝ᵥ (deflator *ᵥ anyW) :=
      sub_nonneg.mpr (hprojectedDominates (deflator *ᵥ anyW))
    have hquadratic := quadratic_nonneg_of_discriminant hleverageFloor
      hconstantNonneg (hdiscriminant (deflator *ᵥ anyW)) (pivotUnit ⬝ᵥ anyW)
    nlinarith [hquadratic]

/-- **THE LIFTING LEMMA** (SS15/SS39: the 18th wall, the single named open
Prop the whole problem now reduces to). For every weighted design in
dimension `k+1` there exist a pivot atom, a unit normal with its deflation
coisometry killing the pivot, and a `k`-subset that (i) dominates in the
projection and (ii) satisfies the boundary-robust DISCRIMINANT form of the
leverage floor `|g_{c*}|² ≥ 1 + rᵀ(G′−I)⁻¹r` — inverse-free, so the
statement is honest on the tight boundary (`G′ = I` directions force the
cross-sum to vanish there instead of dividing by zero). Adversarially
tight over ℝ (the `(k+1)`-cycle attains equality) and FALSE over ℂ (the
SIC `(4,2)` minimizer breaks it) — the realness of the entire problem is
concentrated in this Prop. The pivot/subset SELECTION is the open
content: every deterministic rule is refuted; selection is global. -/
def LiftingLemma (k : ℕ) : Prop :=
  ∀ (m : ℕ) (D : WeightedDesign m (k + 1)),
    ∃ (pivot : Fin m) (pivotUnit : Fin (k + 1) → ℝ)
      (deflator : Matrix (Fin k) (Fin (k + 1)) ℝ)
      (subset : Finset (Fin m)),
      deflatorᵀ * deflator + atomMatrix pivotUnit = 1
      ∧ deflator *ᵥ D.atom pivot = 0
      ∧ pivot ∉ subset
      ∧ subset.card = k
      ∧ (∀ testVec : Fin k → ℝ, testVec ⬝ᵥ testVec
          ≤ ∑ c ∈ subset, ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
      ∧ 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
          + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1
      ∧ ∀ testVec : Fin k → ℝ,
          (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
            ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
                  + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
                * ((∑ c ∈ subset,
                    ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
                  - testVec ⬝ᵥ testVec)

/-- **The glue**: the Lifting Lemma at rank `k` closes weighted GTZ in
dimension `k+1` outright — the bordered Schur sufficiency consumes the
lemma's certificates. -/
theorem gtzWeighted_succ_of_liftingLemma {k : ℕ}
    (hlifting : LiftingLemma k) (m : ℕ) : GtzWeighted m (k + 1) := by
  intro D
  obtain ⟨pivot, pivotUnit, deflator, subset, hsplit, hkill, hnotMem, hcard,
    hprojected, hfloor, hdiscriminant⟩ := hlifting m D
  refine ⟨insert pivot subset, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnotMem, hcard]
  · exact dominates_insert_of_projection_certificates D pivot hsplit hkill
      subset hnotMem hprojected hfloor hdiscriminant

/-- Dimension zero is vacuous: the empty subset dominates. -/
theorem gtzWeighted_dim_zero (m : ℕ) : GtzWeighted m 0 := by
  intro D
  refine ⟨∅, Finset.card_empty, ?_⟩
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun testVec => ?_⟩
  · have hentries : (subsetSum D (∅ : Finset (Fin m))
        - (1 : Matrix (Fin 0) (Fin 0) ℝ))ᴴ = subsetSum D ∅ - 1 := by
      ext rowIdx colIdx
      exact rowIdx.elim0
    exact hentries
  · simp [dotProduct]

/-- **The all-k collapse**: the Lifting Lemma at every rank closes
weighted GTZ at every rank — the deflation induction, with the projected
domination absorbed into the lemma's own certificates. -/
theorem gtzWeightedAll_of_liftingLemma
    (hlifting : ∀ k, LiftingLemma k) : ∀ k, GtzWeightedAll k := by
  intro k
  cases k with
  | zero => exact fun m => gtzWeighted_dim_zero m
  | succ predDim =>
      exact fun m => gtzWeighted_succ_of_liftingLemma (hlifting predDim) m

/-- **THE WHOLE PROBLEM, COLLAPSED**: the original 1997
Goreinov–Tyrtyshnikov–Zamarashkin statement holds for EVERY `(n, k)` with
`0 < n`, given only the Lifting Lemma at every rank. Every other
ingredient — crystallization, Naimark duality, the weighted bridge, the
bordered Schur sufficiency — is now a kernel-checked theorem; the single
named Prop `LiftingLemma` is all that separates the campaign from
unconditional `(n, k)` closure on the all-k frontier. -/
theorem gtz_original_all_of_liftingLemma
    (hlifting : ∀ k, LiftingLemma k) :
    ∀ n k, 0 < n → GtzOriginal n k := fun n k hn =>
  original_of_weighted k (gtzWeightedAll_of_liftingLemma hlifting k) n hn

end Gtz

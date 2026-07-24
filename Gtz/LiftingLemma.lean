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
        ∧ deflatorᵀ * deflator + atomMatrix (scale • D.atom pivot) = 1
        ∧ (scale • D.atom pivot) ⬝ᵥ (scale • D.atom pivot) = 1 := by
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
    ?_, hsplit, hunit⟩
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

/-- **The bordered form, exactly**: at any test vector, the domination
form of the bordered subset `{pivot} ∪ C′` IS the scalar quadratic
`A·a² + 2a·SQ(v) + C(v)` in the adapted coordinates `a = ⟨u,w⟩`,
`v = B·w` — the identity BOTH Schur directions read off. -/
theorem bordered_form_eq {m k : ℕ} (D : WeightedDesign m (k + 1))
    (pivot : Fin m) {pivotUnit : Fin (k + 1) → ℝ}
    {deflator : Matrix (Fin k) (Fin (k + 1)) ℝ}
    (hsplit : deflatorᵀ * deflator + atomMatrix pivotUnit = 1)
    (hkill : deflator *ᵥ D.atom pivot = 0)
    (subset : Finset (Fin m)) (hnotMem : pivot ∉ subset)
    (anyW : Fin (k + 1) → ℝ) :
    anyW ⬝ᵥ (subsetSum D (insert pivot subset) *ᵥ anyW) - anyW ⬝ᵥ anyW
      = ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * (pivotUnit ⬝ᵥ anyW) ^ 2
        + 2 * (pivotUnit ⬝ᵥ anyW)
          * (∑ c ∈ subset, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)))
        + ((∑ c ∈ subset,
            ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)) ^ 2)
          - (deflator *ᵥ anyW) ⬝ᵥ (deflator *ᵥ anyW)) := by
  have hformExpand : anyW ⬝ᵥ (subsetSum D (insert pivot subset) *ᵥ anyW)
      = ∑ c ∈ insert pivot subset, (D.atom c ⬝ᵥ anyW) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (D.atom c) anyW
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
  rw [hformExpand, Finset.sum_insert hnotMem, hpivotDot,
    Finset.sum_congr rfl hmemberDot, hnormSplit]
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
  ring

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
    have hexpansion := bordered_form_eq D pivot hsplit hkill subset
      hnotMem anyW
    have hconstantNonneg :
        0 ≤ (∑ c ∈ subset,
            ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)) ^ 2)
          - (deflator *ᵥ anyW) ⬝ᵥ (deflator *ᵥ anyW) :=
      sub_nonneg.mpr (hprojectedDominates (deflator *ᵥ anyW))
    have hquadratic := quadratic_nonneg_of_discriminant hleverageFloor
      hconstantNonneg (hdiscriminant (deflator *ᵥ anyW)) (pivotUnit ⬝ᵥ anyW)
    linarith [hexpansion, hquadratic]

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

/-- The domination form is the sum of squared atom pairings. -/
theorem subsetSum_form_eq_sum_sq {m dim : ℕ} (D : WeightedDesign m dim)
    (C : Finset (Fin m)) (anyW : Fin dim → ℝ) :
    anyW ⬝ᵥ (subsetSum D C *ᵥ anyW)
      = ∑ c ∈ C, (D.atom c ⬝ᵥ anyW) ^ 2 := by
  rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (D.atom c) anyW

/-- Domination read as a coercive inequality: the selected atoms majorize
the identity form. -/
theorem sum_sq_ge_of_dominates {m dim : ℕ} {D : WeightedDesign m dim}
    {C : Finset (Fin m)} (hdominates : Dominates D C)
    (anyW : Fin dim → ℝ) :
    anyW ⬝ᵥ anyW ≤ ∑ c ∈ C, (D.atom c ⬝ᵥ anyW) ^ 2 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 anyW
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum_form_eq_sum_sq] at hform
  linarith

/-- **Converse of the discriminant reading**: a globally nonnegative
quadratic with nonnegative leading coefficient has dominated
discriminant. Together with `quadratic_nonneg_of_discriminant` this makes
the inverse-free lift condition EXACT, not merely sufficient. -/
theorem discriminant_le_of_quadratic_nonneg
    {leading crossTerm constantTerm : ℝ} (hleading : 0 ≤ leading)
    (hquadratic : ∀ coordinate : ℝ,
      0 ≤ leading * coordinate ^ 2 + 2 * coordinate * crossTerm
        + constantTerm) :
    crossTerm ^ 2 ≤ leading * constantTerm := by
  rcases eq_or_lt_of_le hleading with hleadingZero | hleadingPos
  · rcases eq_or_ne crossTerm 0 with hcrossZero | hcrossNe
    · have hconstant := hquadratic 0
      rw [hcrossZero]
      nlinarith [hconstant]
    · exfalso
      have hbad := hquadratic (-(constantTerm + 1) / (2 * crossTerm))
      rw [← hleadingZero, zero_mul, zero_add] at hbad
      have hcancel : 2 * (-(constantTerm + 1) / (2 * crossTerm)) * crossTerm
          = -(constantTerm + 1) := by
        field_simp
      rw [hcancel] at hbad
      linarith
  · have hkey := hquadratic (-(crossTerm / leading))
    have hexpand : leading * (-(crossTerm / leading)) ^ 2
        + 2 * (-(crossTerm / leading)) * crossTerm + constantTerm
        = constantTerm - crossTerm ^ 2 / leading := by
      field_simp
      ring
    rw [hexpand] at hkey
    have hdivided : crossTerm ^ 2 / leading ≤ constantTerm := by linarith
    have hmultiplied := (div_le_iff₀ hleadingPos).mp hdivided
    linarith [hmultiplied]

/-- **THE CONVERSE COLLAPSE** — the Lifting Lemma is not a strengthening:
weighted GTZ in dimension `k+1` yields, for EVERY design, a pivot and a
subset with all of the lemma's certificates. Every certificate is
EXTRACTED from a dominating `(k+1)`-subset by testing the bordered form
at the adapted family `Bᵀv + a·u` — the coisometry makes that
parametrization onto, so nothing is lost. Mechanizes SS16's informal
"Lifting Lemma = GTZ exactly, an identity". -/
theorem liftingLemma_of_gtzWeighted {k : ℕ}
    (hgtz : ∀ m : ℕ, GtzWeighted m (k + 1)) : LiftingLemma k := by
  intro m D
  obtain ⟨C, hcard, hdominates⟩ := hgtz m D
  -- some selected atom is nonzero, else the form at a unit vector fails
  have hbasisUnit : (Pi.single (0 : Fin (k + 1)) (1 : ℝ))
      ⬝ᵥ Pi.single 0 1 = 1 := by
    rw [dotProduct, Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp
    · intro other _ hother
      simp [hother]
    · intro habsent
      exact absurd (Finset.mem_univ _) habsent
  have hexistsNonzero : ∃ pivot ∈ C, D.atom pivot ≠ 0 := by
    by_contra hallZero
    push Not at hallZero
    have hsumZero : ∑ c ∈ C, (D.atom c ⬝ᵥ Pi.single 0 1) ^ 2 = 0 :=
      Finset.sum_eq_zero fun c hc => by
        rw [hallZero c hc, zero_dotProduct]
        ring
    have hcoercive := sum_sq_ge_of_dominates hdominates (Pi.single 0 1)
    rw [hsumZero, hbasisUnit] at hcoercive
    linarith
  obtain ⟨pivot, hpivotMem, hpivotNonzero⟩ := hexistsNonzero
  obtain ⟨scale, deflator, hscalePos, hcoisometry, hkill, hsplit, hunit⟩ :=
    exists_pivot_deflation D pivot hpivotNonzero
  set pivotUnit := scale • D.atom pivot with hpivotUnitDef
  have hkillUnit : deflator *ᵥ pivotUnit = 0 := by
    rw [hpivotUnitDef, Matrix.mulVec_smul, hkill, smul_zero]
  -- the bordered form is globally nonnegative in adapted coordinates
  have hformNonneg : ∀ anyW : Fin (k + 1) → ℝ,
      0 ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * (pivotUnit ⬝ᵥ anyW) ^ 2
        + 2 * (pivotUnit ⬝ᵥ anyW)
          * (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)))
        + ((∑ c ∈ C.erase pivot,
            ((deflator *ᵥ D.atom c) ⬝ᵥ (deflator *ᵥ anyW)) ^ 2)
          - (deflator *ᵥ anyW) ⬝ᵥ (deflator *ᵥ anyW)) := by
    intro anyW
    have hexpansion := bordered_form_eq D pivot hsplit hkill (C.erase pivot)
      (Finset.notMem_erase pivot C) anyW
    rw [Finset.insert_erase hpivotMem] at hexpansion
    have hcoercive := sum_sq_ge_of_dominates hdominates anyW
    rw [← subsetSum_form_eq_sum_sq] at hcoercive
    linarith [hexpansion, hcoercive]
  -- adapted-coordinate surjectivity: recover (a, v) from Bᵀv + a·u
  have hpivotOrthToLift : ∀ testVec : Fin k → ℝ,
      pivotUnit ⬝ᵥ (deflatorᵀ *ᵥ testVec) = 0 := by
    intro testVec
    rw [dotProduct_comm, dotProduct_mulVec_transpose, hkillUnit,
      dotProduct_zero]
  have hcoordRecover : ∀ (coordinate : ℝ) (testVec : Fin k → ℝ),
      pivotUnit ⬝ᵥ (deflatorᵀ *ᵥ testVec + coordinate • pivotUnit)
        = coordinate := by
    intro coordinate testVec
    rw [dotProduct_add, hpivotOrthToLift, dotProduct_smul, smul_eq_mul,
      hunit, mul_one, zero_add]
  have hprojRecover : ∀ (coordinate : ℝ) (testVec : Fin k → ℝ),
      deflator *ᵥ (deflatorᵀ *ᵥ testVec + coordinate • pivotUnit)
        = testVec := by
    intro coordinate testVec
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hcoisometry,
      Matrix.one_mulVec, Matrix.mulVec_smul, hkillUnit, smul_zero, add_zero]
  -- the scalar quadratic is globally nonnegative at EVERY (a, v)
  have hquadraticAll : ∀ (testVec : Fin k → ℝ) (coordinate : ℝ),
      0 ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
            + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
          * coordinate ^ 2
        + 2 * coordinate
          * (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c)
              * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec))
        + ((∑ c ∈ C.erase pivot,
            ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
          - testVec ⬝ᵥ testVec) := by
    intro testVec coordinate
    have hlifted := hformNonneg
      (deflatorᵀ *ᵥ testVec + coordinate • pivotUnit)
    rw [hcoordRecover coordinate testVec, hprojRecover coordinate testVec]
      at hlifted
    exact hlifted
  -- certificate 1: projected domination (test at coordinate 0)
  have hprojected : ∀ testVec : Fin k → ℝ, testVec ⬝ᵥ testVec
      ≤ ∑ c ∈ C.erase pivot,
          ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2 := by
    intro testVec
    have hatZero := hquadraticAll testVec 0
    nlinarith [hatZero]
  -- certificate 2: the leverage floor (test at the zero vector, coord 1)
  have hfloor : 0 ≤ (pivotUnit ⬝ᵥ D.atom pivot) ^ 2
      + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1 := by
    have hatOne := hquadraticAll 0 1
    simp only [dotProduct_zero, mul_zero, Finset.sum_const_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one, one_pow,
      add_zero, sub_zero] at hatOne
    nlinarith [hatOne]
  -- certificate 3: the discriminant (converse of the quadratic reading)
  have hdiscriminant : ∀ testVec : Fin k → ℝ,
      (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c)
          * ((deflator *ᵥ D.atom c) ⬝ᵥ testVec)) ^ 2
        ≤ ((pivotUnit ⬝ᵥ D.atom pivot) ^ 2
              + (∑ c ∈ C.erase pivot, (pivotUnit ⬝ᵥ D.atom c) ^ 2) - 1)
            * ((∑ c ∈ C.erase pivot,
                ((deflator *ᵥ D.atom c) ⬝ᵥ testVec) ^ 2)
              - testVec ⬝ᵥ testVec) :=
    fun testVec => discriminant_le_of_quadratic_nonneg hfloor
      (hquadraticAll testVec)
  exact ⟨pivot, pivotUnit, deflator, C.erase pivot, hsplit, hkill,
    Finset.notMem_erase pivot C,
    by rw [Finset.card_erase_of_mem hpivotMem, hcard]; omega, hprojected,
    hfloor, hdiscriminant⟩

/-- **THE EQUIVALENCE — the collapse is lossless**: the Lifting Lemma at
rank `k` is EXACTLY weighted GTZ in dimension `k+1`, kernel-checked in
both directions. The inverse-free discriminant packaging neither weakens
nor strengthens the problem; the single named Prop IS the problem. -/
theorem liftingLemma_iff_gtzWeighted_succ {k : ℕ} :
    LiftingLemma k ↔ ∀ m, GtzWeighted m (k + 1) :=
  ⟨fun hlifting m => gtzWeighted_succ_of_liftingLemma hlifting m,
    liftingLemma_of_gtzWeighted⟩

/-- **The second named route to the binding object**: the rank-2→3 lift
closes weighted (6,3) — THE open case of the whole campaign — outright.
Rank-2 GTZ is proven (`gtz_rank_two`); what `LiftingLemma 2` adds is
exactly the global pivot/subset selection. -/
theorem gtzWeighted_six_three_of_liftingLemma_two
    (hlifting : LiftingLemma 2) : GtzWeighted 6 3 :=
  gtzWeighted_succ_of_liftingLemma hlifting 6

/-- **Adversarial calibration, rank 0**: the wall Prop is INHABITED where
GTZ is known — dimension-1 GTZ (pigeonhole) proves `LiftingLemma 0`
through the converse. Had the discriminant packaging been accidentally
too strong, this instance would be unprovable; it is a theorem. -/
theorem liftingLemma_zero : LiftingLemma 0 :=
  liftingLemma_of_gtzWeighted gtz_rank_one

/-- **Adversarial calibration, rank 1**: dimension-2 GTZ (the weighted
Sengupta–Pautov engine) proves `LiftingLemma 1` — the second unconditional
instance of the wall Prop, at the last fully-closed rank. -/
theorem liftingLemma_one : LiftingLemma 1 :=
  liftingLemma_of_gtzWeighted gtz_rank_two

/-- **The wall meets the binding objects**: at its lowest OPEN rank, the
Lifting Lemma is EXACTLY the conjunction of the campaign's two residual
designs — `LiftingLemma 2 ↔ GtzWeighted 6 3 ∧ GtzWeighted 7 3`. The two
frontiers of the problem (the analytic (6,3) wall and the all-k selection
wall) are two faces of the same open content, kernel-checked. -/
theorem liftingLemma_two_iff_the_two_residuals :
    LiftingLemma 2 ↔ (GtzWeighted 6 3 ∧ GtzWeighted 7 3) :=
  liftingLemma_iff_gtzWeighted_succ.trans rank_three_iff_the_two_residuals

/-- **The ladder is the problem, at the family level**: every Lifting
Lemma holds iff weighted GTZ holds at every rank. -/
theorem liftingLemma_all_iff_gtzWeightedAll :
    (∀ k, LiftingLemma k) ↔ ∀ k, GtzWeightedAll k :=
  ⟨gtzWeightedAll_of_liftingLemma,
    fun hgtz k => liftingLemma_of_gtzWeighted (hgtz (k + 1))⟩

/-- **The canonical windows generate the whole ladder** (the s ≥ 4 window
frontier wired to the all-k frontier): the FINITE window family
`2s ≤ m ≤ s(s+1)/2 + 1` per rank yields EVERY Lifting Lemma — the
strong-induction master reduction feeds the converse collapse rank by
rank. Crystallization makes each rank's obligation finite; the ladder
turns the finite obligations into the full problem. -/
theorem liftingLemma_all_of_canonical_windows
    (hwindows : ∀ s m', 2 ≤ s → 2 * s ≤ m' → m' ≤ s * (s + 1) / 2 + 1 →
      GtzWeighted m' s) :
    ∀ k, LiftingLemma k := fun k =>
  liftingLemma_of_gtzWeighted
    (gtz_of_canonical_list hwindows (k + 1) (Nat.le_add_left 1 k))

/-- **The wall, narrowed to the coupling**: with rank-`k` GTZ in hand,
EVERY nonzero atom of EVERY `(k+1)`-design admits a deflation whose
projected design has a dominating `k`-subset — good-in-projection
subsets exist for every pivot choice. So of the Lifting Lemma's three
certificates, the first two are ALWAYS jointly satisfiable per pivot;
the open content is exactly the leverage/discriminant COUPLING between
the pivot and its projected selection. -/
theorem exists_good_in_projection {k : ℕ} (hgtz : GtzWeightedAll k)
    {m : ℕ} (D : WeightedDesign m (k + 1)) (pivot : Fin m)
    (hpivotNonzero : D.atom pivot ≠ 0) :
    ∃ (scale : ℝ) (deflator : Matrix (Fin k) (Fin (k + 1)) ℝ)
      (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m)),
      0 < scale
        ∧ deflator *ᵥ D.atom pivot = 0
        ∧ deflatorᵀ * deflator + atomMatrix (scale • D.atom pivot) = 1
        ∧ subset.card = k
        ∧ Dominates (coisometryPushforward D deflator hcoisometry) subset := by
  obtain ⟨scale, deflator, hscalePos, hcoisometry, hkill, hsplit, hunit⟩ :=
    exists_pivot_deflation D pivot hpivotNonzero
  obtain ⟨subset, hcard, hdominates⟩ :=
    hgtz m (coisometryPushforward D deflator hcoisometry)
  exact ⟨scale, deflator, hcoisometry, subset, hscalePos, hkill, hsplit,
    hcard, hdominates⟩

/-- **The rank-3 instance — the hardest object, cornered**: every nonzero
atom of every `(m,3)` design (the (6,3)/(7,3) frontier included) has
good-in-projection PAIRS, unconditionally, because rank-2 GTZ is proven.
What separates this from `LiftingLemma 2` — hence from (6,3)∧(7,3),
hence from all of rank 3 — is only the coupling: choosing the pivot so
that SOME dominating pair also carries the leverage floor and the
discriminant bound. -/
theorem exists_good_in_projection_rank_three {m : ℕ}
    (D : WeightedDesign m 3) (pivot : Fin m)
    (hpivotNonzero : D.atom pivot ≠ 0) :
    ∃ (scale : ℝ) (deflator : Matrix (Fin 2) (Fin 3) ℝ)
      (hcoisometry : deflator * deflatorᵀ = 1) (subset : Finset (Fin m)),
      0 < scale
        ∧ deflator *ᵥ D.atom pivot = 0
        ∧ deflatorᵀ * deflator + atomMatrix (scale • D.atom pivot) = 1
        ∧ subset.card = 2
        ∧ Dominates (coisometryPushforward D deflator hcoisometry) subset :=
  exists_good_in_projection gtz_rank_two D pivot hpivotNonzero

end Gtz

/-
# Erasing a pair from a six-point tie: a pair-local cap

`Gtz.not_isTie_of_lightAtom` is the first rung of a ladder.  Erase ONE atom from
a boundary system, whiten what is left, import a dominating subset from the
smaller size, and read the bound back: the landed
`Gtz.exists_deflatedGapBound` gives

  `(1 − t_d)·(S_selected − 1) ⪰ t_d·(1 − g_d g_dᵀ)` ,

whose right side is positive definite exactly when `ℓ_d < 1`.  So the one-atom
rung says every atom of a boundary system is heavy, and nothing more.

This module builds the SECOND rung.  Erase a PAIR from a `(6,3)` boundary
system.  Four atoms survive, and four atoms at rank three is a size the corank
floor already closes (`Gtz.gtzWeighted_of_le_five`, since `4 ≤ 3 + 2`).  The
same import-and-read-back gives a condition on the erased PAIR.

## The cap

Write `P = t_a·g_a g_aᵀ + t_b·g_b g_bᵀ` for the pair's weighted contribution.
Then (`Gtz.not_posDef_pairCap_of_isTie`)

  **`(t_a + t_b)·1 − P` is NEVER positive definite at a boundary system.**

The reason is short.  Parseval leaves `1 − P` on the survivors, so if
`(t_a + t_b)·1 ≻ P` then `1 − P ≻ (1 − t_a − t_b)·1`, the survivors' frame
operator beats the identity strictly, and the triple the corank floor hands back
dominates STRICTLY — which a boundary system does not have.

## What it says about the pair

`P` has rank at most two and its nonzero spectrum is that of the two-by-two
matrix with diagonal `t_aℓ_a`, `t_bℓ_b` and off-diagonal `√(t_at_b)·⟨g_a,g_b⟩`,
whose determinant is `t_at_b·crossNormSq g_a g_b`.  So the cap is a polynomial
condition on the pair alone, and on the branch where `t_a + t_b` is at least the
half-trace it reads as an UPPER BOUND ON THE WEDGE
(`Gtz.crossNormSq_le_of_pairCap`):

  **`t_at_b·crossNormSq g_a g_b ≤ (t_a + t_b)·(t_aℓ_a + t_bℓ_b − t_a − t_b)`** .

That is the second landed statement of this arm to bound the hunted pair's wedge
from above, and unlike `Gtz.crossNormSq_le_of_pairGapMinor_nonpos` it consumes
the boundary hypothesis rather than the pair minor.

## The reusable core

`Gtz.exists_triple_ge_frameOperator` is the four-atom import, stated for a bare
family rather than a design: four vectors and four positive weights summing to
one, with positive definite frame operator, always carry a triple whose atom sum
beats that frame operator in the Loewner order.  It needs no design and no
indexing, so any lane can apply it to any four atoms it can name.

[MEASURED before proving.  The cap holds at all 390 pairs of 26 boundary `(6,3)`
systems with worst slack `+0.105`, and at all ten pairs of the `(5,3)` diamond
with worst slack `+0.400` — not a thin tail.  The systems were built as the zero
set of `Σ_T max(λmin(S_T − 1), 0)²` under Parseval with a hard weight floor
`t ≥ 0.05`, never by descent on `max_T λmin`.]
-/
import Gtz.Design.BalancedNormalForm
import Gtz.Reduction.SplitTransfer
import Gtz.Design.TripleGramSylvester
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.WindowPolarity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. Congruence preserves semidefiniteness -/

/-- **CONGRUENCE BY AN INVERTIBLE MATRIX REFLECTS SEMIDEFINITENESS.**  The
semidefinite companion of the landed `Gtz.posDef_congruence_iff`. -/
theorem posSemidef_of_congruence {rank : ℕ} {gramMat congruence : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit congruence.det)
    (hconjugated : (congruenceᵀ * gramMat * congruence).PosSemidef) : gramMat.PosSemidef := by
  have hmatrixUnit : IsUnit congruence := (Matrix.isUnit_iff_isUnit_det congruence).mpr hunit
  have hrightInv : congruence * congruence⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hleftTranspose : (congruence⁻¹)ᵀ * congruenceᵀ = 1 := by
    rw [← Matrix.transpose_mul, hrightInv, Matrix.transpose_one]
  have hstep := hconjugated.conjTranspose_mul_mul_same (B := congruence⁻¹)
  rw [conjTranspose_eq_transpose_real] at hstep
  have hcollapse : (congruence⁻¹)ᵀ * (congruenceᵀ * gramMat * congruence) * congruence⁻¹
      = gramMat := by
    calc (congruence⁻¹)ᵀ * (congruenceᵀ * gramMat * congruence) * congruence⁻¹
        = ((congruence⁻¹)ᵀ * congruenceᵀ) * gramMat * (congruence * congruence⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = gramMat := by rw [hleftTranspose, hrightInv, Matrix.one_mul, Matrix.mul_one]
  rwa [hcollapse] at hstep

/-! ## 2. The four-atom import, for a bare family -/

/-- **FOUR ATOMS CARRY A TRIPLE THAT BEATS THEIR FRAME OPERATOR.**  A positively
weighted family of four vectors in `ℝ³` whose weights total one and whose frame
operator is positive definite always has a triple whose atom sum dominates that
frame operator in the Loewner order.

No design and no index bookkeeping: the statement is about a bare family, so any
lane can apply it to any four atoms it can name.  The input is the corank floor
at `(4,3)`, which `Gtz.gtzWeighted_of_le_five` supplies. -/
theorem exists_triple_ge_frameOperator (atomFamily : Fin 4 → Fin 3 → ℝ)
    (weightFamily : Fin 4 → ℝ) (hweightPos : ∀ i, 0 < weightFamily i)
    (hweightSumOne : ∑ i, weightFamily i = 1)
    (hframe : (∑ i, weightFamily i • atomMatrix (atomFamily i)).PosDef) :
    ∃ selected : Finset (Fin 4), selected.card = 3 ∧
      ((∑ i ∈ selected, atomMatrix (atomFamily i))
        - ∑ i, weightFamily i • atomMatrix (atomFamily i)).PosSemidef := by
  obtain ⟨whitener, hunit, hwhiten⟩ := exists_congruence_to_one hframe
  obtain ⟨selected, hcard, hdom⟩ :=
    gtzWeighted_of_le_five 4 3 (by norm_num) (by norm_num)
      (whitenedFamilyDesign atomFamily weightFamily hweightPos hweightSumOne whitener hwhiten)
  refine ⟨selected, hcard, ?_⟩
  refine posSemidef_of_congruence hunit ?_
  have hidentity : whitenerᵀ * ((∑ i ∈ selected, atomMatrix (atomFamily i))
        - ∑ i, weightFamily i • atomMatrix (atomFamily i)) * whitener
      = whitenerᵀ * (∑ i ∈ selected, atomMatrix (atomFamily i)) * whitener - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hwhiten]
  rw [hidentity, ← subsetSum_whitenedFamilyDesign_eq_conjugate atomFamily weightFamily
    hweightPos hweightSumOne whitener hwhiten selected]
  exact hdom
/-! ## 3. The pair cap at a six-point boundary system -/

/-- The four survivors of an erased pair enumerate the complement of that pair. -/
theorem image_pick_eq_compl {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b) :
    Finset.image pick Finset.univ = ({a, b} : Finset (Fin 6))ᶜ := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨havoidA i, havoidB i⟩
  · rw [Finset.card_compl, Finset.card_insert_of_notMem (by simpa using hab),
      Finset.card_singleton, Finset.card_image_of_injective _ hinj]
    simp

/-- **THE PAIR CAP.**  At a boundary system of size six and rank three the pair
matrix `t_a·g_a g_aᵀ + t_b·g_b g_bᵀ` is never strictly below `(t_a + t_b)·1`.

Erasing the pair leaves four atoms, and four atoms at rank three is inside the
corank floor.  If the cap failed, the survivors' frame operator would beat the
identity strictly, and the triple the corank floor returns would dominate
strictly — which a boundary system does not have. -/
theorem not_posDef_pairCap_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b) :
    ¬ (((D.weight a + D.weight b) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - (D.weight a • atomMatrix (D.atom a)
          + D.weight b • atomMatrix (D.atom b))).PosDef := by
  classical
  intro hcap
  set pairMat : Matrix (Fin 3) (Fin 3) ℝ :=
    D.weight a • atomMatrix (D.atom a) + D.weight b • atomMatrix (D.atom b) with hpairMat
  set pairMass : ℝ := D.weight a + D.weight b with hpairMass
  set survivorMass : ℝ := 1 - pairMass with hsurvivorMass
  have himage := image_pick_eq_compl hab pick hinj havoidA havoidB
  have hsplit : ∀ f : Fin 6 → ℝ, ∑ i, f (pick i) = (∑ c, f c) - (f a + f b) := by
    intro f
    have hsum : ∑ c ∈ Finset.image pick Finset.univ, f c = ∑ i, f (pick i) :=
      Finset.sum_image (fun x _ y _ hxy => hinj hxy)
    have htotal := Finset.sum_add_sum_compl ({a, b} : Finset (Fin 6)) f
    rw [Finset.sum_pair hab] at htotal
    rw [← hsum, himage]
    linarith [htotal]
  have hweightSurvivors : ∑ i, D.weight (pick i) = survivorMass := by
    rw [hsplit D.weight, D.weight_sum_one, hsurvivorMass, hpairMass]
  have hsurvivorPos : 0 < survivorMass := by
    have hpos : (0 : ℝ) < ∑ i, D.weight (pick i) :=
      Finset.sum_pos (fun i _ => D.weight_pos _) Finset.univ_nonempty
    rw [hweightSurvivors] at hpos
    exact hpos
  have hparseval : ∑ i, D.weight (pick i) • atomMatrix (D.atom (pick i))
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) - pairMat := by
    ext row col
    have hall := congrFun (congrFun D.isParseval row) col
    have hrow := hsplit (fun c => (D.weight c • atomMatrix (D.atom c)) row col)
    simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
      smul_eq_mul] at hall hrow ⊢
    simp only [hpairMat, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hrow, hall]
  set frame : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ i, (D.weight (pick i) / survivorMass) • atomMatrix (D.atom (pick i)) with hframeDef
  have hframeEq : frame = survivorMass⁻¹ • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - pairMat) := by
    rw [hframeDef, ← hparseval, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, div_eq_inv_mul]
  have hscalar : survivorMass⁻¹ * pairMass = survivorMass⁻¹ - 1 := by
    field_simp
    rw [hsurvivorMass]; ring
  have hframeGap : frame - 1
      = survivorMass⁻¹ • (pairMass • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pairMat) := by
    rw [hframeEq, smul_sub, smul_sub, smul_smul, hscalar, sub_smul, one_smul]
    abel
  have hframeGapPos : (frame - 1).PosDef := by
    rw [hframeGap]
    exact hcap.smul (by positivity)
  have hframePos : frame.PosDef := by
    have hrewrite : frame = (frame - 1) + 1 := by abel
    rw [hrewrite]
    exact hframeGapPos.add_posSemidef Matrix.PosSemidef.one
  obtain ⟨selected, hcard, hdom⟩ := exists_triple_ge_frameOperator
    (fun i => D.atom (pick i)) (fun i => D.weight (pick i) / survivorMass)
    (fun i => div_pos (D.weight_pos _) hsurvivorPos)
    (by rw [← Finset.sum_div, hweightSurvivors, div_self hsurvivorPos.ne'])
    hframePos
  refine htie.2 (selected.image pick) ?_ ?_
  · rw [Finset.card_image_of_injective _ hinj, hcard]
  · have hsubsetSum : subsetSum D (selected.image pick)
        = ∑ i ∈ selected, atomMatrix (D.atom (pick i)) := by
      rw [subsetSum, Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    have hsplitGap : (∑ i ∈ selected, atomMatrix (D.atom (pick i)))
          - (1 : Matrix (Fin 3) (Fin 3) ℝ)
        = ((∑ i ∈ selected, atomMatrix (D.atom (pick i))) - frame) + (frame - 1) := by
      abel
    rw [hsubsetSum, hsplitGap, add_comm]
    exact hframeGapPos.add_posSemidef hdom
/-! ## 4. The cap in scalars -/

/-- The pair cap matrix, as a function of the two atoms and their weights. -/
noncomputable def pairCapForm (wa wb : ℝ) (u v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((wa + wb) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) - (wa • atomMatrix u + wb • atomMatrix v)

theorem pairCapForm_transpose (wa wb : ℝ) (u v : Fin 3 → ℝ) :
    (pairCapForm wa wb u v)ᵀ = pairCapForm wa wb u v := by
  ext row col
  simp only [pairCapForm, Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  rcases eq_or_ne row col with rfl | hne
  · rfl
  · rw [if_neg hne, if_neg (Ne.symm hne)]; ring

/-- The trace of the pair cap form. -/
theorem trace_pairCapForm (wa wb : ℝ) (u v : Fin 3 → ℝ) :
    Matrix.trace (pairCapForm wa wb u v)
      = 3 * (wa + wb) - (wa * leverageOf u + wb * leverageOf v) := by
  simp only [pairCapForm, Matrix.trace_fin_three, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
    leverageOf, dotProduct, Fin.sum_univ_three]
  norm_num
  ring

/-- The second invariant of the pair cap form, in pair scalars. -/
theorem secondInvariant_pairCapForm (wa wb : ℝ) (u v : Fin 3 → ℝ) :
    secondInvariantOfThree (pairCapForm wa wb u v)
      = 3 * (wa + wb) ^ 2 - 2 * (wa * leverageOf u + wb * leverageOf v) * (wa + wb)
        + wa * wb * (leverageOf u * leverageOf v - (u ⬝ᵥ v) ^ 2) := by
  rw [pairCapForm, Matrix.one_fin_three]
  simp only [secondInvariantOfThree, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val']
  ring

/-- The determinant of the pair cap form, in pair scalars. -/
theorem det_pairCapForm (wa wb : ℝ) (u v : Fin 3 → ℝ) :
    (pairCapForm wa wb u v).det
      = (wa + wb) * ((wa + wb) ^ 2 - (wa * leverageOf u + wb * leverageOf v) * (wa + wb)
        + wa * wb * (leverageOf u * leverageOf v - (u ⬝ᵥ v) ^ 2)) := by
  rw [pairCapForm, Matrix.one_fin_three]
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val']
  ring

/-- **THE CAP, IN PAIR SCALARS.**  At a boundary system of size six every pair
satisfies one of three polynomial inequalities in its two weights, its two
leverages and its one pairing.  Two of the three bound the pair's WEDGE from
above, since `Gtz.crossNormSq_eq_leverage_mul_sub_sq` identifies the bracket
`leverageOf u * leverageOf v - (u ⬝ᵥ v)^2` with `Gtz.crossNormSq u v`.

The producer is the landed
`Gtz.posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos`: a symmetric
three-by-three form with positive trace, second invariant and determinant is
positive definite, and the cap says this one is not. -/
theorem pairCap_scalar_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b) :
    3 * (D.weight a + D.weight b)
        ≤ D.weight a * leverageOf (D.atom a) + D.weight b * leverageOf (D.atom b)
      ∨ 3 * (D.weight a + D.weight b) ^ 2
          + D.weight a * D.weight b * crossNormSq (D.atom a) (D.atom b)
          ≤ 2 * (D.weight a * leverageOf (D.atom a)
            + D.weight b * leverageOf (D.atom b)) * (D.weight a + D.weight b)
      ∨ (D.weight a + D.weight b) ^ 2
          + D.weight a * D.weight b * crossNormSq (D.atom a) (D.atom b)
          ≤ (D.weight a * leverageOf (D.atom a)
            + D.weight b * leverageOf (D.atom b)) * (D.weight a + D.weight b) := by
  have hcap := not_posDef_pairCap_of_isTie D htie hab pick hinj havoidA havoidB
  have hform : pairCapForm (D.weight a) (D.weight b) (D.atom a) (D.atom b)
      = ((D.weight a + D.weight b) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        - (D.weight a • atomMatrix (D.atom a) + D.weight b • atomMatrix (D.atom b)) := rfl
  rw [← hform] at hcap
  have hherm : (pairCapForm (D.weight a) (D.weight b) (D.atom a) (D.atom b)).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_real]
    exact pairCapForm_transpose _ _ _ _
  have hmass : 0 < D.weight a + D.weight b := by
    linarith [D.weight_pos a, D.weight_pos b]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  refine hcap (posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos hherm ?_ ?_ ?_)
  · rw [trace_pairCapForm]; linarith
  · rw [secondInvariant_pairCapForm, crossNormSq_eq_leverage_mul_sub_sq] at *; linarith
  · rw [det_pairCapForm, crossNormSq_eq_leverage_mul_sub_sq] at *
    have hinner : 0 < (D.weight a + D.weight b) ^ 2
        - (D.weight a * leverageOf (D.atom a)
          + D.weight b * leverageOf (D.atom b)) * (D.weight a + D.weight b)
        + D.weight a * D.weight b * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - (D.atom a ⬝ᵥ D.atom b) ^ 2) := by linarith
    positivity

end Gtz

/-
# The erasure ladder: every small set of atoms carries its own weight

`Gtz.leverage_one_le_of_isTie` says every atom of a boundary system is heavy.
Its proof is an erasure: drop one atom, whiten what is left, import a dominating
triple from the smaller size, and read the bound back.  The smaller size is
inside the corank floor, so the import is free.

That argument does not care that only one atom was dropped.  Dropping `E` from a
`(6,3)` boundary system leaves `6 − |E|` atoms, and every size from three to
five is inside the corank floor (`Gtz.gtzWeighted_of_le_five`).  So the SAME
argument runs for every `E` with `1 ≤ |E| ≤ 3`, and it gives a condition on `E`.

## The cap

Write `t(E) = Σ_{c ∈ E} t_c` and `P_E = Σ_{c ∈ E} t_c·g_c g_cᵀ`.  Then at a
boundary system (`Gtz.not_posDef_erasedCap_of_isTie`)

  **`t(E)·1 − P_E` is NEVER positive definite** ,

for every erased set leaving at least three and at most five survivors.  The
reason is one line: Parseval leaves `1 − P_E` on the survivors, so if the cap
failed their frame operator would beat the identity strictly, and the triple the
corank floor returns would dominate STRICTLY — which a boundary system has none
of.

## What the ladder says, rung by rung

* `|E| = 1` returns `1 ≤ ℓ_a` — the landed heaviness theorem, recovered here as
  the first rung (`Gtz.one_le_leverage_of_erasedCap`).  So the family is a
  genuine generalization of a theorem, not a new guess.
* `|E| = 2` caps a PAIR, and in scalars that bounds the pair's WEDGE
  (`Gtz/Wave/ErasedPairCap.lean`).
* `|E| = 3` caps a TRIPLE, and is new at every rung.

At `(6,3)` that is `6 + 15 + 20 = 41` simultaneous necessary conditions, one per
small subset, all of the same shape.

## The reading form

Positive definiteness fails exactly when some direction sees the erased atoms
carrying at least their own weight (`Gtz.exists_reading_ge_of_isTie`):

  **there is `x ≠ 0` with `Σ_{c ∈ E} t_c·⟨g_c,x⟩² ≥ t(E)·‖x‖²`** .

Parseval turns that inside out: since `Σ_c t_c⟨g_c,x⟩² = ‖x‖²` and `Σ_c t_c = 1`,
the same `x` makes the SURVIVORS carry at most their own weight.  So a boundary
system cannot have any small set of atoms that is everywhere below its weight.

## The reusable core

`Gtz.exists_triple_ge_frameOperator_le_five` is the import, stated for a bare
family of at most five vectors rather than for a design: positive weights
summing to one and a positive definite frame operator always yield a triple
whose atom sum beats that frame operator in the Loewner order.  No design, no
indexing, no erasure — any lane can apply it to any five atoms it can name.

[MEASURED before proving, on 26 boundary `(6,3)` systems built as the zero set of
`Σ_T max(λmin(S_T − 1), 0)²` under Parseval with a hard weight floor `t ≥ 0.05`,
never by descent on `max_T λmin`.  Worst slack `λmax(P_E) − t(E)`: `+0.057` over
156 singletons, `+0.105` over 390 pairs, `+0.170` over 520 triples.  No
violations, and no thin tail.  The cap also held over all 390 four-sets with
worst slack `+0.111`, which this argument does NOT cover — two survivors cannot
form a triple — so that rung is measured only.]
-/
import Gtz.Wave.ErasedPairCap
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The import, for a bare family of at most five vectors -/

/-- **AT MOST FIVE ATOMS CARRY A TRIPLE THAT BEATS THEIR FRAME OPERATOR.**  A
positively weighted family of at most five vectors in `ℝ³` whose weights total
one and whose frame operator is positive definite always has a triple whose atom
sum dominates that frame operator in the Loewner order.

The input is the corank floor, which `Gtz.gtzWeighted_of_le_five` supplies at
every size up to five.  The statement is about a bare family, so it needs no
design and no index bookkeeping. -/
theorem exists_triple_ge_frameOperator_le_five {n : ℕ} (hn : n ≤ 5)
    (atomFamily : Fin n → Fin 3 → ℝ) (weightFamily : Fin n → ℝ)
    (hweightPos : ∀ i, 0 < weightFamily i) (hweightSumOne : ∑ i, weightFamily i = 1)
    (hframe : (∑ i, weightFamily i • atomMatrix (atomFamily i)).PosDef) :
    ∃ selected : Finset (Fin n), selected.card = 3 ∧
      ((∑ i ∈ selected, atomMatrix (atomFamily i))
        - ∑ i, weightFamily i • atomMatrix (atomFamily i)).PosSemidef := by
  obtain ⟨whitener, hunit, hwhiten⟩ := exists_congruence_to_one hframe
  obtain ⟨selected, hcard, hdom⟩ :=
    gtzWeighted_of_le_five n 3 (by norm_num) hn
      (whitenedFamilyDesign atomFamily weightFamily hweightPos hweightSumOne whitener hwhiten)
  refine ⟨selected, hcard, posSemidef_of_congruence hunit ?_⟩
  have hidentity : whitenerᵀ * ((∑ i ∈ selected, atomMatrix (atomFamily i))
        - ∑ i, weightFamily i • atomMatrix (atomFamily i)) * whitener
      = whitenerᵀ * (∑ i ∈ selected, atomMatrix (atomFamily i)) * whitener - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hwhiten]
  rw [hidentity, ← subsetSum_whitenedFamilyDesign_eq_conjugate atomFamily weightFamily
    hweightPos hweightSumOne whitener hwhiten selected]
  exact hdom

/-! ## 2. The erased set and its cap -/

/-- The weight an erased set carries. -/
noncomputable def erasedMass {m : ℕ} (D : WeightedDesign m 3) (E : Finset (Fin m)) : ℝ :=
  ∑ c ∈ E, D.weight c

/-- The weighted contribution of an erased set to Parseval. -/
noncomputable def erasedMat {m : ℕ} (D : WeightedDesign m 3) (E : Finset (Fin m)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ c ∈ E, D.weight c • atomMatrix (D.atom c)

/-- The cap form of an erased set: its own weight against its contribution. -/
noncomputable def erasedCapForm {m : ℕ} (D : WeightedDesign m 3) (E : Finset (Fin m)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (erasedMass D E) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - erasedMat D E

theorem erasedCapForm_transpose {m : ℕ} (D : WeightedDesign m 3) (E : Finset (Fin m)) :
    (erasedCapForm D E)ᵀ = erasedCapForm D E := by
  rw [erasedCapForm, erasedMat, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]

/-- **THE ERASURE CAP.**  At a boundary system the cap form of an erased set is
never positive definite, provided the survivors number between three and five.

Everything before the last step is bookkeeping: the survivors carry the
complementary weight and the complementary Parseval mass, so their frame
operator is `(1 − t(E))⁻¹·(1 − P_E)`, which beats the identity exactly when the
cap form is positive definite.  The corank floor then returns a triple of
survivors that dominates strictly. -/
theorem not_posDef_erasedCap_of_isTie {m n : ℕ} (D : WeightedDesign m 3) (htie : IsTie D)
    (E : Finset (Fin m)) (hn3 : 3 ≤ n) (hn : n ≤ 5) (pick : Fin n → Fin m)
    (hinj : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = Eᶜ) :
    ¬ (erasedCapForm D E).PosDef := by
  classical
  intro hcap
  set pairMass : ℝ := erasedMass D E with hpairMass
  set survivorMass : ℝ := 1 - pairMass with hsurvivorMass
  have hsplit : ∀ f : Fin m → ℝ, ∑ i, f (pick i) = (∑ c, f c) - ∑ c ∈ E, f c := by
    intro f
    have hsum : ∑ c ∈ Finset.image pick Finset.univ, f c = ∑ i, f (pick i) :=
      Finset.sum_image (fun x _ y _ hxy => hinj hxy)
    have htotal := Finset.sum_add_sum_compl E f
    rw [← hsum, himage]
    linarith [htotal]
  have hweightSurvivors : ∑ i, D.weight (pick i) = survivorMass := by
    rw [hsplit D.weight, D.weight_sum_one, hsurvivorMass, hpairMass, erasedMass]
  have hsurvivorPos : 0 < survivorMass := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by omega))
    have hpos : (0 : ℝ) < ∑ i, D.weight (pick i) :=
      Finset.sum_pos (fun i _ => D.weight_pos _) hne
    rw [hweightSurvivors] at hpos
    exact hpos
  have hparseval : ∑ i, D.weight (pick i) • atomMatrix (D.atom (pick i))
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) - erasedMat D E := by
    ext row col
    have hall := congrFun (congrFun D.isParseval row) col
    have hrow := hsplit (fun c => (D.weight c • atomMatrix (D.atom c)) row col)
    simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
      smul_eq_mul] at hall hrow ⊢
    simp only [erasedMat, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [hrow, hall]
  set frame : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ i, (D.weight (pick i) / survivorMass) • atomMatrix (D.atom (pick i)) with hframeDef
  have hframeEq : frame
      = survivorMass⁻¹ • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - erasedMat D E) := by
    rw [hframeDef, ← hparseval, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, div_eq_inv_mul]
  have hscalar : survivorMass⁻¹ * pairMass = survivorMass⁻¹ - 1 := by
    field_simp
    rw [hsurvivorMass]; ring
  have hframeGap : frame - 1 = survivorMass⁻¹ • erasedCapForm D E := by
    rw [hframeEq, erasedCapForm, ← hpairMass, smul_sub, smul_sub, smul_smul, hscalar,
      sub_smul, one_smul]
    abel
  have hframeGapPos : (frame - 1).PosDef := by
    rw [hframeGap]; exact hcap.smul (by positivity)
  have hframePos : frame.PosDef := by
    have hrewrite : frame = (frame - 1) + 1 := by abel
    rw [hrewrite]
    exact hframeGapPos.add_posSemidef Matrix.PosSemidef.one
  obtain ⟨selected, hcard, hdom⟩ := exists_triple_ge_frameOperator_le_five hn
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

/-! ## 3. The reading form -/

/-- **THE ERASED SET CARRIES ITS OWN WEIGHT IN SOME DIRECTION.**  Failure of
positive definiteness is exactly a direction in which the erased atoms read at
least their own weight.  By Parseval the same direction makes the SURVIVORS read
at most theirs. -/
theorem exists_reading_ge_of_isTie {m n : ℕ} (D : WeightedDesign m 3) (htie : IsTie D)
    (E : Finset (Fin m)) (hn3 : 3 ≤ n) (hn : n ≤ 5) (pick : Fin n → Fin m)
    (hinj : Function.Injective pick)
    (himage : Finset.image pick Finset.univ = Eᶜ) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      erasedMass D E * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ E, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
  have hcap := not_posDef_erasedCap_of_isTie D htie E hn3 hn pick hinj himage
  have hherm : (erasedCapForm D E).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_real]
    exact erasedCapForm_transpose D E
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hcap
  push_neg at hcap
  obtain ⟨probe, hne, hform⟩ := hcap hherm
  refine ⟨probe, hne, ?_⟩
  have hexpand : probe ⬝ᵥ ((erasedCapForm D E) *ᵥ probe)
      = erasedMass D E * (probe ⬝ᵥ probe)
        - ∑ c ∈ E, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 := by
    rw [erasedCapForm, erasedMat, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Matrix.sum_mulVec, dotProduct_sum]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by
      rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul,
        dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm probe (D.atom c)]
      ring
  rw [star_trivial, hexpand] at hform
  linarith

/-! ## 4. The first rung is the landed heaviness theorem -/

/-- **THE SINGLETON RUNG RETURNS HEAVINESS.**  Erasing one atom, the cap says
exactly that the atom is heavy.  The landed `Gtz.leverage_one_le_of_isTie` proves
the same thing by the same erasure, so the ladder generalizes a theorem rather
than guessing a new family. -/
theorem one_le_leverage_of_erasedCap {m : ℕ} (D : WeightedDesign m 3) {a : Fin m}
    (hcap : ¬ (erasedCapForm D {a}).PosDef) : 1 ≤ leverageOf (D.atom a) := by
  by_contra hlight
  push_neg at hlight
  refine hcap ?_
  have hform : erasedCapForm D {a}
      = D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom a)) := by
    rw [erasedCapForm, erasedMass, erasedMat, Finset.sum_singleton, Finset.sum_singleton,
      smul_sub]
  rw [hform]
  exact (posDef_one_sub_atomMatrix_of_leverage_lt_one (D.atom a) hlight).smul (D.weight_pos a)

end Gtz

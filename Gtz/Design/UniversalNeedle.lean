import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The universal needle of a weighted design

The A1 residual carries a PER-TRIPLE needle: every three-slot selection owns
one probe on which its gap form reaches `(1 - 2*cap)/cap`.  This module proves
the matching statement for the FULL selection, and it holds at EVERY probe:

    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ cap * (probe ⬝ᵥ ((subsetSum design univ - 1) *ᵥ probe)).

The proof is Parseval and one scalar comparison, with no eigenvalue, no square
root and no determinant.  The full gap expands as the `(1 - weight)`-combination
of the atoms, Parseval reads the `weight`-combination as the probe energy, and
`weight ≤ cap` compares the two term by term.

Three consequences land here.  `posDef_subsetSum_univ_sub_one_of_cap` sharpens
the landed qualitative statement: the cap replaces the atom count, which is the
honest hypothesis, because a one-atom design carries `cap = 1` and its full gap
vanishes.  `sum_compl_sq_ge_of_tight` is the A1 reading: at a direction that a
selection holds tight, the COMPLEMENT atoms carry all the universal energy, so
their squared readings are bounded below.  `sum_compl_sq_ge_of_tight_baseTriple`
is the same statement at the pinned base triple.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Parseval as a quadratic form -/

/-- **Parseval, read at a probe.**  The weight-combination of the squared atom
readings is the probe energy. -/
theorem sum_weight_mul_sq_dotProduct (design : WeightedDesign size rank)
    (probe : Fin rank → ℝ) :
    (∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
      = probe ⬝ᵥ probe := by
  have hexpand : probe ⬝ᵥ
        ((∑ label, design.weight label • atomMatrix (design.atom label)) *ᵥ probe)
      = ∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, dotProduct_atomMatrix_mulVec, smul_eq_mul]
  rw [← hexpand, design.isParseval, Matrix.one_mulVec]

/-- **The full gap is the `(1 - weight)`-combination.**  Parseval subtracts the
identity inside the atom sum. -/
theorem quadForm_subsetSum_univ_sub_one (design : WeightedDesign size rank)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe)
      = ∑ label, (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, ← sum_weight_mul_sq_dotProduct design probe,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun label _ => by ring

/-! ## The needle -/

/-- **THE UNIVERSAL NEEDLE.**  A cap on the weights is a floor on the full gap
form, at EVERY probe.  Division-free, and the constant `1 - cap` beats the
per-triple constant `1 - 2*cap` of the A1 residual.

The scalar core is `weight ≤ cap ⟺ (1 - cap) * weight ≤ cap * (1 - weight)`. -/
theorem universal_needle (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap) (probe : Fin rank → ℝ) :
    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ cap * (probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe)) := by
  rw [quadForm_subsetSum_univ_sub_one, ← sum_weight_mul_sq_dotProduct design probe,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun label _ => ?_
  have hsq : (0 : ℝ) ≤ (design.atom label ⬝ᵥ probe) ^ 2 := sq_nonneg _
  nlinarith [hcap label]

/-- The cap of a nonempty design is positive. -/
theorem pos_of_weight_le (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap) (label : Fin size) : 0 < cap :=
  lt_of_lt_of_le (design.weight_pos label) (hcap label)

/-- **THE QUANTITATIVE FULL-SET FLOOR.**  A cap strictly below one makes the
full gap form strictly positive at every nonzero probe, with the explicit floor
`(1 - cap) / cap` carried in division-free form by the needle above.

This sharpens the landed qualitative statement in two ways.  The floor is
explicit, and the hypothesis is the honest one: a single-atom design carries
`cap = 1` and its full gap is exactly zero, so `cap < 1` is what the conclusion
actually needs, not the atom count. -/
theorem quadForm_subsetSum_univ_sub_one_pos (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap) (hcapLt : cap < 1)
    (label : Fin size) {probe : Fin rank → ℝ} (hprobe : probe ≠ 0) :
    0 < probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe) := by
  have hcapPos : 0 < cap := pos_of_weight_le design hcap label
  have hpos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  have hneedle := universal_needle design hcap probe
  have hleft : 0 < (1 - cap) * (probe ⬝ᵥ probe) := by
    have hgap : (0 : ℝ) < 1 - cap := by linarith
    positivity
  nlinarith [lt_of_lt_of_le hleft hneedle]

/-! ## The heavy label is free -/

/-- **SOME LABEL CARRIES THE RECIPROCAL COUNT.**  Positive weights summing to one
cannot all sit below `1 / size`. -/
theorem exists_weight_ge_inv_card (design : WeightedDesign size rank)
    (hsize : 0 < size) :
    ∃ label, (1 : ℝ) / size ≤ design.weight label := by
  by_contra hnone
  push Not at hnone
  have hstrict : (∑ label, design.weight label) < ∑ _label : Fin size, (1 : ℝ) / size := by
    refine Finset.sum_lt_sum_of_nonempty ?_ fun label _ => hnone label
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsize)
  rw [design.weight_sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hstrict
  have hsizePos : (0 : ℝ) < size := by exact_mod_cast hsize
  rw [mul_one_div, div_self (ne_of_gt hsizePos)] at hstrict
  exact lt_irrefl _ hstrict

/-- **THE A1 HEAVY HYPOTHESIS IS FREE.**  Every `(6,3)` design carries a label of
weight at least `1 / 6`, hence at least `1 / 10`.

So the tenth-heavy narrowing of the A1 residual — both the existential heavy
label and the `1 / 10` floor under the pinned base/complement cap — adds no
hypothesis a prover may spend: it holds at every design in the class.  The
light-region theorem earns its keep upstream of A1, not inside it. -/
theorem exists_weight_ge_tenth (design : WeightedDesign 6 3) :
    ∃ label, (1 : ℝ) / 10 ≤ design.weight label := by
  obtain ⟨label, hlabel⟩ := exists_weight_ge_inv_card design (by norm_num)
  exact ⟨label, by norm_num at hlabel ⊢; linarith⟩

/-! ## The A1 reading: tight directions push their energy to the complement -/

/-- **THE COMPLEMENT CARRIES THE NEEDLE.**  At a direction on which a selection
holds its gap form tight, the full gap form is exactly the complement's squared
readings, so the universal needle prices them from below.

This is the A1 shape: the residual hands a weak base triple with a tight
direction, and this theorem turns the cap into a lower bound on the complement's
energy at that very direction — no eigenvalue, no positivity of the gap. -/
theorem sum_compl_sq_ge_of_tight (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0) :
    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ cap * ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hsplit : probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe)
      = probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
        + ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sub_mulVec, dotProduct_sub,
      dotProduct_subsetSum_mulVec_of_finset, dotProduct_subsetSum_mulVec_of_finset]
    have hunion : (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
        + ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2
        = ∑ label, (design.atom label ⬝ᵥ probe) ^ 2 :=
      Finset.sum_add_sum_compl selected _
    linarith [hunion]
  have hneedle := universal_needle design hcap probe
  rw [hsplit, htight, zero_add] at hneedle
  exact hneedle

/-- The A1 instance at the pinned base triple: its complement is the three
remaining slots, and a tight direction prices their squared readings. -/
theorem sum_compl_sq_ge_of_tight_baseTriple (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap) (probe : Fin 3 → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe) = 0) :
    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ cap * ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
          (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hcompl : ({0, 1, 2} : Finset (Fin 6))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have := sum_compl_sq_ge_of_tight design hcap ({0, 1, 2} : Finset (Fin 6)) probe htight
  rwa [hcompl] at this

end Gtz

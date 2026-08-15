import Gtz.Design.UniversalNeedle
import Gtz.Design.TwoMeetingLinesTransversal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The two-meeting-lines transversals price their complements

The two-meeting-lines residual asks that one of the four transversals `{1,3,5}`,
`{1,4,5}`, `{2,3,5}`, `{2,4,5}` dominates strictly.  Each of the four
complements is `{0, i', j'}`: the SHARED atom together with the two unused
private atoms, one from each line.

This module prices a failure.  The landed universal needle turns a weight cap
into a floor on the full gap form, and the landed complement law spends that
floor at a direction where a selection holds its gap TIGHT.  A failing selection
supplies less: a direction where the gap form is merely NONPOSITIVE.  The first
theorem here weakens the tight hypothesis to that, which is exactly what
`Matrix.PosDef` failure delivers, and the class instances then read the price on
the complement of each transversal.

The shared atom carries every one of the four prices, because it lies in every
one of the four complements.
-/

variable {size rank : ℕ}

/-! ## The needle at a nonpositive direction -/

/-- **THE COMPLEMENT CARRIES THE NEEDLE AT A NONPOSITIVE DIRECTION.**  A
selection whose gap form is nonpositive at a probe prices its complement's
squared readings there.  This weakens the tight hypothesis of
`Gtz.sum_compl_sq_ge_of_tight` to an inequality, which is what a failure of
`Matrix.PosDef` supplies. -/
theorem sum_compl_sq_ge_of_nonpos (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (hnonpos : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) ≤ 0) :
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
  have hne : Nonempty (Fin size) := by
    rcases isEmpty_or_nonempty (Fin size) with hemp | hne
    · exact absurd (by
        rw [← design.weight_sum_one, Finset.univ_eq_empty, Finset.sum_empty]) one_ne_zero
    · exact hne
  have hcappos : 0 < cap := pos_of_weight_le design hcap hne.some
  have hneedle := universal_needle design hcap probe
  rw [hsplit] at hneedle
  nlinarith [hneedle, hnonpos, hcappos]

/-- A selection whose gap fails to be positive definite has a nonzero direction
on which the gap form is nonpositive. -/
theorem exists_probe_nonpos_of_not_posDef (design : WeightedDesign size rank)
    (selected : Finset (Fin size))
    (hfail : ¬ (subsetSum design selected - 1).PosDef) :
    ∃ probe : Fin rank → ℝ, probe ≠ 0 ∧
      probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) ≤ 0 := by
  by_contra hnone
  push Not at hnone
  refine hfail (Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design selected),
      fun probe hprobe => ?_⟩)
  rw [star_trivial]
  exact hnone probe hprobe

/-- **A FAILING SELECTION PRICES ITS COMPLEMENT.**  If a selection does not
dominate strictly, some nonzero direction hands the universal needle to the
complement's squared readings. -/
theorem sum_compl_sq_ge_of_not_posDef (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size))
    (hfail : ¬ (subsetSum design selected - 1).PosDef) :
    ∃ probe : Fin rank → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hprobe, hnonpos⟩ :=
    exists_probe_nonpos_of_not_posDef design selected hfail
  exact ⟨probe, hprobe, sum_compl_sq_ge_of_nonpos design hcap selected probe hnonpos⟩

/-! ## The four transversal complements -/

/-- The complement of the transversal `{1,3,5}` is the shared atom together with
the two unused private atoms. -/
theorem compl_transversal_oneThreeFive :
    ({1, 3, 5} : Finset (Fin 6))ᶜ = ({0, 2, 4} : Finset (Fin 6)) := by decide

/-- The complement of the transversal `{1,4,5}`. -/
theorem compl_transversal_oneFourFive :
    ({1, 4, 5} : Finset (Fin 6))ᶜ = ({0, 2, 3} : Finset (Fin 6)) := by decide

/-- The complement of the transversal `{2,3,5}`. -/
theorem compl_transversal_twoThreeFive :
    ({2, 3, 5} : Finset (Fin 6))ᶜ = ({0, 1, 4} : Finset (Fin 6)) := by decide

/-- The complement of the transversal `{2,4,5}`. -/
theorem compl_transversal_twoFourFive :
    ({2, 4, 5} : Finset (Fin 6))ᶜ = ({0, 1, 3} : Finset (Fin 6)) := by decide

/-- **THE SHARED ATOM LIES IN EVERY TRANSVERSAL COMPLEMENT.**  This is the
finite reason the shared atom carries every price below. -/
theorem sharedAtom_mem_every_transversal_compl :
    (0 : Fin 6) ∈ ({1, 3, 5} : Finset (Fin 6))ᶜ ∧
      (0 : Fin 6) ∈ ({1, 4, 5} : Finset (Fin 6))ᶜ ∧
      (0 : Fin 6) ∈ ({2, 3, 5} : Finset (Fin 6))ᶜ ∧
      (0 : Fin 6) ∈ ({2, 4, 5} : Finset (Fin 6))ᶜ := by decide

/-! ## The class instances -/

/-- **A FAILING TRANSVERSAL PRICES THE SHARED ATOM AND TWO PRIVATE ATOMS.**  The
instance of the needle at the transversal `{1,3,5}`. -/
theorem transversalFailure_prices_oneThreeFive (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (hfail : ¬ (subsetSum design ({1, 3, 5} : Finset (Fin 6)) - 1).PosDef) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 2, 4} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hprobe, hprice⟩ :=
    sum_compl_sq_ge_of_not_posDef design hcap ({1, 3, 5} : Finset (Fin 6)) hfail
  exact ⟨probe, hprobe, by rwa [compl_transversal_oneThreeFive] at hprice⟩

/-- The instance at the transversal `{1,4,5}`. -/
theorem transversalFailure_prices_oneFourFive (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (hfail : ¬ (subsetSum design ({1, 4, 5} : Finset (Fin 6)) - 1).PosDef) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 2, 3} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hprobe, hprice⟩ :=
    sum_compl_sq_ge_of_not_posDef design hcap ({1, 4, 5} : Finset (Fin 6)) hfail
  exact ⟨probe, hprobe, by rwa [compl_transversal_oneFourFive] at hprice⟩

/-- The instance at the transversal `{2,3,5}`. -/
theorem transversalFailure_prices_twoThreeFive (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (hfail : ¬ (subsetSum design ({2, 3, 5} : Finset (Fin 6)) - 1).PosDef) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 1, 4} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hprobe, hprice⟩ :=
    sum_compl_sq_ge_of_not_posDef design hcap ({2, 3, 5} : Finset (Fin 6)) hfail
  exact ⟨probe, hprobe, by rwa [compl_transversal_twoThreeFive] at hprice⟩

/-- The instance at the transversal `{2,4,5}`. -/
theorem transversalFailure_prices_twoFourFive (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (hfail : ¬ (subsetSum design ({2, 4, 5} : Finset (Fin 6)) - 1).PosDef) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 1, 3} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hprobe, hprice⟩ :=
    sum_compl_sq_ge_of_not_posDef design hcap ({2, 4, 5} : Finset (Fin 6)) hfail
  exact ⟨probe, hprobe, by rwa [compl_transversal_twoFourFive] at hprice⟩

/-- **THE FOUR-FOLD PRICE.**  If the two-meeting-lines conclusion fails outright
— no transversal dominates strictly — then all four complements are priced, each
at its own direction, and the shared atom appears in every one of them.  This is
the exact quantitative content a proof of the residual has to contradict. -/
theorem allTransversalsFail_prices_four (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (hfail : ¬ TwoMeetingLinesTransversalStrict design) :
    (∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧ (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 2, 4} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2) ∧
      (∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧ (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 2, 3} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2) ∧
      (∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧ (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 1, 4} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2) ∧
      (∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧ (1 - cap) * (probe ⬝ᵥ probe)
        ≤ cap * ∑ label ∈ ({0, 1, 3} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ probe) ^ 2) := by
  simp only [TwoMeetingLinesTransversalStrict, not_or] at hfail
  obtain ⟨h135, h145, h235, h245⟩ := hfail
  exact ⟨transversalFailure_prices_oneThreeFive design hcap h135,
    transversalFailure_prices_oneFourFive design hcap h145,
    transversalFailure_prices_twoThreeFive design hcap h235,
    transversalFailure_prices_twoFourFive design hcap h245⟩

end Gtz

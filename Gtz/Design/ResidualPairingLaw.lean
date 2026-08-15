/-
# The residual pairing law: every selection decided by ONE inverse

`Gtz.posDef_directionChartGap_iff_complementForm` decides a selection by the
complement form at the coefficient vectors supported on the labels the
selection OMITS.  At the trivial chart of a design every mass ratio is one, so
that form collapses to a fixed symmetric `6 x 6` pairing read off the FULL
selection alone:

  `residualPairing design c d = (if c = d then 1 else 0) - crossPivot design c d`

with `crossPivot design c d = a_c . (S_univ - 1)⁻¹ a_d`.

The consequence is a change of cost.  Deciding the fifteen card-four selections
and the twenty card-three selections no longer needs thirty-five inverses of
`3 x 3` gaps.  It needs ONE inverse, `(S_univ - 1)⁻¹`, and the principal minors
of the pairing it produces:

  `(subsetSum design S - 1).PosDef  <->  residualPairing is positive on Sᶜ`

A card-four selection omits a PAIR, so its test is a binary quadratic form and
`binaryForm_pos_iff` turns it into two scalar inequalities.  A card-three
selection omits a TRIPLE, so the no-strict ledger of the A1 residual says
exactly that NO principal `3 x 3` minor of the pairing is positive definite.

The diagonal is the full-selection pivot gap, `1 - pivot design univ c`, and
`Gtz.pivot_sum_eq_rank_add_trace_inv` prices the whole diagonal at
`3 - trace ((S_univ - 1)⁻¹)`.
-/
import Mathlib
import Gtz.Design.ComplementFormLaw
import Gtz.Design.DesignDescentPort
import Gtz.Design.TieStallReduction
import Gtz.Design.TraceIdentity
import Gtz.Design.InverseTraceEscape

namespace Gtz

open Matrix Finset

/-! ## 1. A binary quadratic form -/

/-- **The binary form criterion.**  A symmetric binary quadratic form is
positive on every nonzero coefficient pair exactly when its first diagonal
entry is positive and its determinant is positive.  Sqrt-free and division-free
in both directions: the forward direction evaluates at `(1,0)` and at
`(-b, a)`, and the converse completes the square. -/
theorem binaryForm_pos_iff {a b c : ℝ} :
    (∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) → 0 < a * x * x + 2 * b * x * y + c * y * y)
      ↔ (0 < a ∧ b * b < a * c) := by
  constructor
  · intro hform
    have hone : 0 < a := by
      have := hform 1 0 (Or.inl one_ne_zero)
      linarith [this]
    refine ⟨hone, ?_⟩
    by_cases hb : b = 0
    · have := hform 0 1 (Or.inr one_ne_zero)
      have hc : 0 < c := by linarith [this]
      nlinarith [hb, hone, hc]
    · have hne : (-b) ≠ 0 ∨ a ≠ 0 := Or.inr (ne_of_gt hone)
      have hval := hform (-b) a hne
      nlinarith [hval, hone]
  · rintro ⟨hpos, hdet⟩ x y hne
    have key : a * (a * x * x + 2 * b * x * y + c * y * y)
        = (a * x + b * y) ^ 2 + (a * c - b * b) * (y * y) := by ring
    rcases eq_or_ne y 0 with rfl | hy0
    · have hx : x ≠ 0 := by
        rcases hne with h | h
        · exact h
        · exact absurd rfl h
      nlinarith [mul_pos hpos (mul_self_pos.mpr hx)]
    · have hy2 : 0 < y * y := mul_self_pos.mpr hy0
      have hprod : 0 < (a * c - b * b) * (y * y) := mul_pos (by linarith) hy2
      nlinarith [sq_nonneg (a * x + b * y), key, hprod, hpos]

/-! ## 2. The pairing -/

variable (design : WeightedDesign 6 3)

/-- The gap of the full selection.  Positive definite at every design. -/
noncomputable def fullGap : Matrix (Fin 3) (Fin 3) ℝ :=
  subsetSum design Finset.univ - 1

theorem posDef_fullGap : (fullGap design).PosDef :=
  posDef_subsetSum_univ_sub_one design (by norm_num)

/-- The inverse reading of one atom against another. -/
noncomputable def crossPivot (c d : Fin 6) : ℝ :=
  design.atom c ⬝ᵥ ((fullGap design)⁻¹ *ᵥ design.atom d)

/-- **The residual pairing.**  The identity less the inverse Gram of the atoms
against the full gap. -/
noncomputable def residualPairing (c d : Fin 6) : ℝ :=
  (if c = d then (1 : ℝ) else 0) - crossPivot design c d

/-- The full gap is symmetric. -/
theorem fullGap_transpose : (fullGap design)ᵀ = fullGap design := by
  have hsym : (subsetSum design Finset.univ)ᵀ = subsetSum design Finset.univ := by
    rw [subsetSum, Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ => by
      rw [atomMatrix, Matrix.transpose_vecMulVec]
  rw [fullGap, Matrix.transpose_sub, hsym, Matrix.transpose_one]

/-- The inverse of the full gap is symmetric. -/
theorem fullGap_inv_transpose : ((fullGap design)⁻¹)ᵀ = (fullGap design)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, fullGap_transpose]

/-- A symmetric matrix reads the same on a swapped pair of probes.  Proved by
the double sum, so it needs no adjoint lemma. -/
theorem dotProduct_mulVec_comm_of_transpose {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) (x y : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have hqp : M q p = M p q := congrFun (congrFun hM p) q
  rw [hqp]
  ring

theorem crossPivot_comm (c d : Fin 6) :
    crossPivot design c d = crossPivot design d c :=
  dotProduct_mulVec_comm_of_transpose (fullGap_inv_transpose design)
    (design.atom c) (design.atom d)

theorem residualPairing_comm (c d : Fin 6) :
    residualPairing design c d = residualPairing design d c := by
  rw [residualPairing, residualPairing, crossPivot_comm]
  by_cases h : c = d
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- **The diagonal is the full-selection pivot gap.**  This ties the pairing to
the campaign's landed pivot vocabulary. -/
theorem residualPairing_diag (c : Fin 6) :
    residualPairing design c c = 1 - pivot design Finset.univ c := by
  rw [residualPairing, if_pos rfl, crossPivot, pivot_eq_dot, fullGap]

/-- **The diagonal trace law.**  Summing the diagonal against the inverse-trace
law prices the whole pairing diagonal by the inverse of the full gap alone. -/
theorem sum_residualPairing_diag :
    ∑ c, residualPairing design c c
      = 3 - Matrix.trace ((fullGap design)⁻¹) := by
  have hlaw := pivot_sum_eq_rank_add_trace_inv design Finset.univ (posDef_fullGap design)
  have hcard : ∑ _c : Fin 6, (1 : ℝ) = 6 := by simp
  calc ∑ c, residualPairing design c c
      = ∑ c, (1 - pivot design Finset.univ c) := by
        exact Finset.sum_congr rfl fun c _ => residualPairing_diag design c
    _ = (∑ _c : Fin 6, (1 : ℝ)) - ∑ c, pivot design Finset.univ c := by
        rw [Finset.sum_sub_distrib]
    _ = 3 - Matrix.trace ((fullGap design)⁻¹) := by
        rw [hcard]
        rw [show (Finset.univ : Finset (Fin 6)) = Finset.univ from rfl] at hlaw
        rw [fullGap]
        push_cast at hlaw ⊢
        linarith [hlaw]

/-! ## 3. The complement form collapses onto the pairing -/

/-- At the trivial chart every mass ratio is one. -/
theorem designChartPoint_ratio (label : Fin 6) :
    (designChartPoint design).mass label / (designChartPoint design).weight label = 1 :=
  div_self (design.weight_pos label).ne'

/-- The chart gap of the full selection is the design's own full gap. -/
theorem directionChartGap_univ_designChartPoint :
    directionChartGap design.atom (designChartPoint design).mass
        (designChartPoint design).weight Finset.univ
      = fullGap design :=
  directionChartGap_designChartPoint design Finset.univ

/-- The omitted combination at the trivial chart is the plain coefficient
combination of the omitted atoms. -/
theorem omittedCombination_designChartPoint (omitted : Finset (Fin 6))
    (coeff : Fin 6 → ℝ) :
    omittedCombination design.atom (designChartPoint design).mass
        (designChartPoint design).weight omitted coeff
      = ∑ c ∈ omitted, coeff c • design.atom c := by
  rw [omittedCombination]
  exact Finset.sum_congr rfl fun c _ => by
    rw [designChartPoint_ratio design c, one_mul]

/-- **THE COLLAPSE.**  At the trivial chart the complement form is the
quadratic form of the residual pairing, restricted to the omitted labels.  No
mass ratio and no chart survive. -/
theorem complementForm_designChartPoint (omitted : Finset (Fin 6))
    (coeff : Fin 6 → ℝ) :
    complementForm design.atom (designChartPoint design).mass
        (designChartPoint design).weight omitted coeff
      = ∑ c ∈ omitted, ∑ d ∈ omitted,
          coeff c * coeff d * residualPairing design c d := by
  have hsquare : ∑ c ∈ omitted,
      (designChartPoint design).mass c / (designChartPoint design).weight c
        * coeff c * coeff c
      = ∑ c ∈ omitted, coeff c * coeff c :=
    Finset.sum_congr rfl fun c _ => by rw [designChartPoint_ratio design c, one_mul]
  have hbilinear : omittedCombination design.atom (designChartPoint design).mass
        (designChartPoint design).weight omitted coeff ⬝ᵥ
        ((directionChartGap design.atom (designChartPoint design).mass
          (designChartPoint design).weight Finset.univ)⁻¹ *ᵥ
          omittedCombination design.atom (designChartPoint design).mass
            (designChartPoint design).weight omitted coeff)
      = ∑ c ∈ omitted, ∑ d ∈ omitted,
          coeff c * coeff d * crossPivot design c d := by
    rw [omittedCombination_designChartPoint design omitted coeff,
      directionChartGap_univ_designChartPoint design]
    rw [Matrix.mulVec_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, crossPivot]
    ring
  have hdiag : ∑ c ∈ omitted, ∑ d ∈ omitted,
      coeff c * coeff d * (if c = d then (1 : ℝ) else 0)
      = ∑ c ∈ omitted, coeff c * coeff c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.sum_eq_single c]
    · rw [if_pos rfl, mul_one]
    · intro d _ hdc
      rw [if_neg (Ne.symm hdc), mul_zero]
    · intro hnot
      exact absurd hc hnot
  rw [complementForm, hsquare, hbilinear, ← hdiag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [residualPairing]
  ring

/-! ## 4. The law at every design -/

/-- **THE RESIDUAL PAIRING LAW.**  A selection's gap is positive definite
exactly when the residual pairing is positive at every coefficient vector that
is nonzero somewhere on the labels the selection OMITS.  One inverse decides
every selection. -/
theorem posDef_subsetSum_iff_residualPairing (selected : Finset (Fin 6)) :
    (subsetSum design selected - 1).PosDef
      ↔ ∀ coeff : Fin 6 → ℝ, (∃ label ∈ selectedᶜ, coeff label ≠ 0) →
          0 < ∑ c ∈ selectedᶜ, ∑ d ∈ selectedᶜ,
              coeff c * coeff d * residualPairing design c d := by
  have hboost : ∀ label ∈ selectedᶜ,
      0 < (designChartPoint design).mass label / (designChartPoint design).weight label := by
    intro label _
    rw [designChartPoint_ratio design label]
    norm_num
  have hstep := posDef_directionChartGap_iff_complementForm design.atom
    (designChartPoint design).mass (designChartPoint design).weight selected hboost
    (posDef_directionChartGap_univ_designChartPoint design)
  rw [directionChartGap_designChartPoint design selected] at hstep
  rw [hstep]
  constructor
  · intro hform coeff hne
    rw [← complementForm_designChartPoint design selectedᶜ coeff]
    exact hform coeff hne
  · intro hform coeff hne
    rw [complementForm_designChartPoint design selectedᶜ coeff]
    exact hform coeff hne

/-! ## 5. The card-four test is two scalars -/

/-- **THE PAIR MINOR LAW AT A DESIGN.**  A card-four selection omits a pair, so
its gap is positive definite exactly when the pairing's first diagonal entry is
positive and its `2 x 2` determinant is positive.  Two scalar inequalities in
one inverse, for each of the fifteen card-four selections. -/
theorem posDef_subsetSum_cardFour_iff_pairMinor (selected : Finset (Fin 6))
    (i j : Fin 6) (hij : i ≠ j) (hcompl : selectedᶜ = {i, j}) :
    (subsetSum design selected - 1).PosDef
      ↔ (0 < residualPairing design i i
          ∧ residualPairing design i j * residualPairing design i j
              < residualPairing design i i * residualPairing design j j) := by
  rw [posDef_subsetSum_iff_residualPairing design selected, hcompl]
  constructor
  · intro hform
    refine (binaryForm_pos_iff (a := residualPairing design i i)
      (b := residualPairing design i j) (c := residualPairing design j j)).mp ?_
    intro x y hne
    have hii : (if i = i then x else y) = x := if_pos rfl
    have hji : (if j = i then x else y) = y := if_neg (Ne.symm hij)
    have hcoeff := hform (fun label => if label = i then x else y) ?_
    · rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij,
        hii, hji, residualPairing_comm design j i] at hcoeff
      nlinarith [hcoeff]
    · rcases hne with hx | hy
      · exact ⟨i, Finset.mem_insert_self _ _, by rw [hii]; exact hx⟩
      · exact ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          by rw [hji]; exact hy⟩
  · rintro ⟨hpos, hdet⟩ coeff hne
    have hbin := (binaryForm_pos_iff (a := residualPairing design i i)
      (b := residualPairing design i j) (c := residualPairing design j j)).mpr ⟨hpos, hdet⟩
    rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij]
    rw [residualPairing_comm design j i]
    have hne' : coeff i ≠ 0 ∨ coeff j ≠ 0 := by
      obtain ⟨label, hmem, hlabel⟩ := hne
      rcases Finset.mem_insert.mp hmem with rfl | hsingle
      · exact Or.inl hlabel
      · exact Or.inr (by rwa [Finset.mem_singleton.mp hsingle] at hlabel)
    nlinarith [hbin (coeff i) (coeff j) hne']

/-! ## 6. The A1 ledger reads as a minor statement -/

/-- **THE NO-STRICT LEDGER IS A MINOR STATEMENT.**  No card-three selection
dominates strictly exactly when NO principal `3 x 3` minor of the residual
pairing is positive definite.  This is the exact hypothesis carried by
`Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` at line 107 of the
registry, rewritten with no design left in it. -/
theorem noStrict_iff_no_tripleMinor :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef)
      ↔ ∀ selected : Finset (Fin 6), selected.card = 3 →
          ∃ coeff : Fin 6 → ℝ, (∃ label ∈ selectedᶜ, coeff label ≠ 0) ∧
            ∑ c ∈ selectedᶜ, ∑ d ∈ selectedᶜ,
              coeff c * coeff d * residualPairing design c d ≤ 0 := by
  constructor
  · intro hledger selected hcard
    by_contra hnone
    push Not at hnone
    exact hledger selected hcard
      ((posDef_subsetSum_iff_residualPairing design selected).mpr
        fun coeff hne => hnone coeff hne)
  · intro hminor selected hcard hposDef
    obtain ⟨coeff, hne, hle⟩ := hminor selected hcard
    exact absurd ((posDef_subsetSum_iff_residualPairing design selected).mp hposDef
      coeff hne) (not_lt.mpr hle)

/-- **The A1 consumer.**  A design whose card-four selections all move carries
no no-strict ledger, so every counterexample residual that lists the ledger --
`Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` among them -- closes
from the stall escape alone.  The pairing law supplies the escape hypothesis in
minor form. -/
theorem false_of_noStrict_of_pairingEscape
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef)
    (hescape : DesignCardFourStallEscape design) : False :=
  false_of_noStrict_of_stallEscape design hnoStrict hescape

end Gtz

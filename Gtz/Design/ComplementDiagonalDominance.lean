/-
# The diagonal-dominance kill: strict domination without a determinant

`Gtz.posDef_directionChartGap_iff_complementForm` reduces strict domination of a
selection to positivity of ONE quadratic form on the labels the selection omits,
and `Gtz.complementForm_eq_sum` writes that form as the quadratic form of the
symmetric matrix `Gtz.complementMatrixEntry`.  Every existing route from there
runs through leading minors, so a card-three selection costs a three-by-three
determinant and a card-four one costs a four-by-four.

This file supplies the other classical route.  A symmetric matrix whose every
diagonal entry beats the sum of the absolute values of its own row off the
diagonal is positive definite, and the proof is a two-line completion of squares
rather than an expansion.  The criterion is therefore **`k` scalar inequalities
at omitted cardinality `k`**, and each one names only pivots and cross pivots.

## PROVED here, kernel-checked, unconditional

* `Gtz.complementRowSlack` — the row margin of one omitted label, and
  `Gtz.complementRowSlack_eq_boost_mul` reading it as the boost times a
  pivot-and-cross-pivot expression.
* `Gtz.complementForm_pos_of_rowSlack_pos` — **THE KILL.**  Positive row slack at
  every omitted label makes the complement form strictly positive.  Generic in
  the size, the direction family and the omitted set, with no cardinality
  hypothesis at all.
* `Gtz.posDef_directionChartGap_of_rowSlack_pos` — the same statement with the
  conclusion moved onto the chart gap.
* `Gtz.posDef_directionChartGap_of_crossPivotSlack` — the usable phrasing.  A
  selection is strictly dominating when every omitted label `a` satisfies
  `∑ ρ_b |F_ab| < 1 - π_a`, the sum over the other omitted labels.
* `Gtz.dominates_of_crossPivotSlack` — the design reading, where every boost is
  one and the criterion is `∑ |fullPivotGram a b| < 1 - pivot a`.
* `Gtz.complementForm_pos_of_scaledRowSlack_pos` — **THE SCALED KILL.**  The
  same completion of squares carries a free positive scale at every label,
  because the arithmetic-geometric bound holds at every positive parameter.  This
  is the classical H-matrix criterion, strictly weaker than plain dominance.
* `Gtz.posDef_directionChartGap_of_pairCriterion` — **exactness at omitted count
  two.**  A scale exists exactly when the landed pair inequality holds, so the
  scaled criterion loses nothing there.  The witnessing scale is explicit and
  needs no square root, so the two-by-two determinant is never expanded.
* Card-one, card-two and card-three specializations, and
  `Gtz.pairCriterion_of_rowSlack_pos`, which shows plain dominance is strictly
  stronger than the exact pair law and therefore a proper sub-cell of it.

## Why the criterion is worth having

It is one-sided: it proves strict domination and never refutes it.  In exchange
it is cheap, it is monotone in the omitted set, and it degrades gracefully.  At
omitted cardinality one it IS the landed pivot law `π_a < 1`.  At cardinality
two the plain form implies the landed exact pair inequality
`ρ_a ρ_b F_ab ^ 2 < (1 - π_a) (1 - π_b)`, and the SCALED form is equivalent to
it, so nothing is lost at all.  At cardinality three, where the exact law is a
cubic determinant, it is three linear inequalities in the absolute cross
pivots.
-/
import Gtz.Design.ComplementPairCriterion
import Gtz.Design.PivotGramIdempotent
import Gtz.Design.DesignDescentPort
import Gtz.Wave.GaugeWallTriangleTreeReduction

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## The row margin -/

/-- **The off-diagonal row weight of an omitted label.**  The sum, over the other
omitted labels, of the absolute complement-matrix entries in the row of `a`. -/
noncomputable def complementRowOff (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (a : Fin size) : ℝ :=
  ∑ b ∈ omitted, (if b = a then 0 else |complementMatrixEntry direction mass weight a b|)

/-- **The row margin of an omitted label.**  Its diagonal complement-matrix entry
minus its off-diagonal row weight.  Positivity at every omitted label is the
criterion this file proves. -/
noncomputable def complementRowSlack (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (a : Fin size) : ℝ :=
  complementMatrixEntry direction mass weight a a
    - complementRowOff direction mass weight omitted a

/-- The diagonal complement-matrix entry is the boost times the pivot defect. -/
theorem complementMatrixEntry_diag (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a : Fin size) :
    complementMatrixEntry direction mass weight a a
      = (mass a / weight a) * (1 - fullPivot direction mass weight a) := by
  simp only [complementMatrixEntry, fullPivot, eq_self_iff_true, if_true]
  ring

/-- The off-diagonal complement-matrix entry is minus the product of the two
boosts with the inverse form. -/
theorem complementMatrixEntry_off (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {a b : Fin size} (hne : a ≠ b) :
    complementMatrixEntry direction mass weight a b
      = -((mass a / weight a) * (mass b / weight b)
          * fullInverseForm direction mass weight a b) := by
  rw [complementMatrixEntry, if_neg hne]
  ring

/-- **The row margin in pivot coordinates.**  With a positive boost at `a` the
margin is that boost times `(1 - π_a) - ∑ ρ_b |F_ab|`, so the sign of the margin
is the sign of the bracket. -/
theorem complementRowSlack_eq_boost_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (a : Fin size)
    (hboost : 0 ≤ mass a / weight a) :
    complementRowSlack direction mass weight omitted a
      = (mass a / weight a)
        * ((1 - fullPivot direction mass weight a)
            - ∑ b ∈ omitted, (if b = a then 0 else
                |mass b / weight b| * |fullInverseForm direction mass weight a b|)) := by
  have hsum : ∑ b ∈ omitted, (if b = a then 0 else
        |complementMatrixEntry direction mass weight a b|)
      = (mass a / weight a) * ∑ b ∈ omitted, (if b = a then 0 else
        |mass b / weight b| * |fullInverseForm direction mass weight a b|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hba : b = a
    · simp [hba]
    · have hne : a ≠ b := fun h => hba h.symm
      rw [if_neg hba, if_neg hba, complementMatrixEntry_off direction mass weight hne,
        abs_neg, abs_mul, abs_mul, abs_of_nonneg hboost]
      ring
  rw [complementRowSlack, complementMatrixEntry_diag, complementRowOff, hsum]
  ring

/-! ## The kill

The proof is the classical completion of squares.  Off the diagonal the term
`N a b * c a * c b` is at least `- |N a b| * ((c a) ^ 2 + (c b) ^ 2) / 2`, and
summing that bound twice — once along rows and once along columns, which agree
because the matrix is symmetric — leaves exactly the row margins.
-/

/-- **THE DIAGONAL-DOMINANCE KILL.**  If every omitted label has a strictly
positive row margin, the complement form is strictly positive at every
coefficient vector that is nonzero somewhere on the omitted set.

No cardinality hypothesis, no determinant, no rank condition.  The only inputs
are the symmetry of the complement matrix and the margins. -/
theorem complementForm_pos_of_rowSlack_pos (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size))
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ a ∈ omitted, 0 < complementRowSlack direction mass weight omitted a)
    (coeff : Fin size → ℝ) (hne : ∃ label ∈ omitted, coeff label ≠ 0) :
    0 < complementForm direction mass weight omitted coeff := by
  classical
  set N : Fin size → Fin size → ℝ := complementMatrixEntry direction mass weight with hN
  have hsymm : ∀ a b, N a b = N b a := fun a b =>
    complementMatrixEntry_symm direction mass weight huniv a b
  -- The minorant: the diagonal exactly, and the arithmetic-geometric bound off it.
  have hpoint : ∀ a ∈ omitted, ∀ b ∈ omitted,
      N a a * coeff a ^ 2 * (if b = a then 1 else 0)
          - (if b = a then 0 else |N a b| * (coeff a ^ 2 + coeff b ^ 2) / 2)
        ≤ N a b * coeff a * coeff b := by
    intro a _ b _
    by_cases hba : b = a
    · subst hba
      have hone : (if b = b then (1 : ℝ) else 0) = 1 := if_pos rfl
      have hzero : (if b = b then (0 : ℝ)
          else |N b b| * (coeff b ^ 2 + coeff b ^ 2) / 2) = 0 := if_pos rfl
      rw [hone, hzero]
      exact le_of_eq (by ring)
    · rw [if_neg hba, if_neg hba]
      have habs : |N a b * coeff a * coeff b| ≤ |N a b| * (coeff a ^ 2 + coeff b ^ 2) / 2 := by
        rw [abs_mul, abs_mul]
        have hsq : |coeff a| * |coeff b| ≤ (coeff a ^ 2 + coeff b ^ 2) / 2 := by
          nlinarith [sq_nonneg (|coeff a| - |coeff b|), sq_abs (coeff a), sq_abs (coeff b)]
        have : (0 : ℝ) ≤ |N a b| := abs_nonneg _
        nlinarith [abs_nonneg (coeff a), abs_nonneg (coeff b)]
      linarith [neg_abs_le (N a b * coeff a * coeff b)]
  -- Sum the minorant.  The two off-diagonal halves add up to the row weights.
  have hrow : ∑ a ∈ omitted, ∑ b ∈ omitted,
      (if b = a then 0 else |N a b| * coeff a ^ 2 / 2)
        = ∑ a ∈ omitted, coeff a ^ 2 / 2 * complementRowOff direction mass weight omitted a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [complementRowOff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hba : b = a <;> simp [hba] <;> ring
  have hcol : ∑ a ∈ omitted, ∑ b ∈ omitted,
      (if b = a then 0 else |N a b| * coeff b ^ 2 / 2)
        = ∑ b ∈ omitted, coeff b ^ 2 / 2 * complementRowOff direction mass weight omitted b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [complementRowOff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hab : a = b
    · simp [hab]
    · have hba : b ≠ a := fun h => hab h.symm
      rw [if_neg hab, if_neg hba, hsymm a b]
      ring
  have hdiag : ∑ a ∈ omitted, ∑ b ∈ omitted, N a a * coeff a ^ 2 * (if b = a then 1 else 0)
      = ∑ a ∈ omitted, N a a * coeff a ^ 2 := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum, Finset.sum_ite_eq' omitted a (fun _ => (1 : ℝ))]
    simp [ha]
  have hminor : ∑ a ∈ omitted, coeff a ^ 2 * complementRowSlack direction mass weight omitted a
      ≤ complementForm direction mass weight omitted coeff := by
    rw [complementForm_eq_sum]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun a ha =>
      Finset.sum_le_sum fun b hb => hpoint a ha b hb)
    have hsplit : ∀ a b : Fin size,
        N a a * coeff a ^ 2 * (if b = a then 1 else 0)
            - (if b = a then 0 else |N a b| * (coeff a ^ 2 + coeff b ^ 2) / 2)
          = N a a * coeff a ^ 2 * (if b = a then 1 else 0)
              - (if b = a then 0 else |N a b| * coeff a ^ 2 / 2)
              - (if b = a then 0 else |N a b| * coeff b ^ 2 / 2) := by
      intro a b
      by_cases hba : b = a <;> simp [hba] <;> ring
    simp only [hsplit, Finset.sum_sub_distrib]
    rw [hdiag, hrow, hcol]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [complementRowSlack]
    ring
  -- Every summand is nonnegative and the witnessing one is strictly positive.
  obtain ⟨label, hlabel, hcoeff⟩ := hne
  refine lt_of_lt_of_le ?_ hminor
  refine Finset.sum_pos' (fun a ha => mul_nonneg (sq_nonneg _) (hslack a ha).le)
    ⟨label, hlabel, ?_⟩
  exact mul_pos (by positivity) (hslack label hlabel)

/-- **The kill, with the conclusion on the chart gap.**  A selection whose
omitted labels all have a strictly positive row margin is strictly dominating. -/
theorem posDef_directionChartGap_of_rowSlack_pos (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size))
    (hboost : ∀ label ∈ selectedᶜ, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ a ∈ selectedᶜ, 0 < complementRowSlack direction mass weight selectedᶜ a) :
    (directionChartGap direction mass weight selected).PosDef :=
  (posDef_directionChartGap_iff_complementForm direction mass weight selected hboost
    huniv).mpr
    (complementForm_pos_of_rowSlack_pos direction mass weight selectedᶜ huniv hslack)


/-! ## The scaled kill

Plain diagonal dominance compares each diagonal entry with its own row.  The
completion of squares below carries a free positive scale at every label,
because the arithmetic-geometric bound `2 |x| |y| ≤ γ x ^ 2 + γ⁻¹ y ^ 2` holds
at every positive `γ`.  Choosing `γ` as the ratio of the two scales turns the
criterion into the classical H-matrix condition, which is strictly weaker than
plain dominance and, at omitted count two, is **exact**.
-/

/-- **The scaled off-diagonal row weight.**  The row of `a`, with each entry
weighted by the scale of the label it points at. -/
noncomputable def complementScaledRowOff (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size))
    (scale : Fin size → ℝ) (a : Fin size) : ℝ :=
  ∑ b ∈ omitted, (if b = a then 0
    else scale b * |complementMatrixEntry direction mass weight a b|)

/-- **THE SCALED DIAGONAL-DOMINANCE KILL.**  A positive scale that makes every
omitted label beat its own scaled row makes the complement form strictly
positive.

Taking every scale equal to one recovers plain diagonal dominance.  A stratum
that knows one label is strong and another weak may trade them off, which plain
dominance cannot do. -/
theorem complementForm_pos_of_scaledRowSlack_pos (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size))
    (scale : Fin size → ℝ) (hscale : ∀ a ∈ omitted, 0 < scale a)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ a ∈ omitted, complementScaledRowOff direction mass weight omitted scale a
      < scale a * complementMatrixEntry direction mass weight a a)
    (coeff : Fin size → ℝ) (hne : ∃ label ∈ omitted, coeff label ≠ 0) :
    0 < complementForm direction mass weight omitted coeff := by
  classical
  set N : Fin size → Fin size → ℝ := complementMatrixEntry direction mass weight with hN
  have hsymm : ∀ a b, N a b = N b a := fun a b =>
    complementMatrixEntry_symm direction mass weight huniv a b
  -- The minorant, with the arithmetic-geometric parameter set to the scale ratio.
  have hpoint : ∀ a ∈ omitted, ∀ b ∈ omitted,
      N a a * coeff a ^ 2 * (if b = a then 1 else 0)
          - (if b = a then 0 else
              scale b / scale a * |N a b| * coeff a ^ 2 / 2
                + scale a / scale b * |N a b| * coeff b ^ 2 / 2)
        ≤ N a b * coeff a * coeff b := by
    intro a ha b hb
    by_cases hba : b = a
    · subst hba
      have hone : (if b = b then (1 : ℝ) else 0) = 1 := if_pos rfl
      have hzero : (if b = b then (0 : ℝ)
          else scale b / scale b * |N b b| * coeff b ^ 2 / 2
            + scale b / scale b * |N b b| * coeff b ^ 2 / 2) = 0 := if_pos rfl
      rw [hone, hzero]
      exact le_of_eq (by ring)
    · rw [if_neg hba, if_neg hba]
      have hsa := hscale a ha
      have hsb := hscale b hb
      -- `2 |c a| |c b| ≤ (scale b / scale a) (c a) ^ 2 + (scale a / scale b) (c b) ^ 2`
      have hamgm : 2 * (|coeff a| * |coeff b|)
          ≤ scale b / scale a * coeff a ^ 2 + scale a / scale b * coeff b ^ 2 := by
        have hleft : scale b / scale a * coeff a ^ 2 = scale b * |coeff a| ^ 2 / scale a := by
          rw [sq_abs]; ring
        have hright : scale a / scale b * coeff b ^ 2 = scale a * |coeff b| ^ 2 / scale b := by
          rw [sq_abs]; ring
        rw [hleft, hright, div_add_div _ _ (ne_of_gt hsa) (ne_of_gt hsb),
          le_div_iff₀ (mul_pos hsa hsb)]
        nlinarith [sq_nonneg (scale b * |coeff a| - scale a * |coeff b|), hsa, hsb,
          abs_nonneg (coeff a), abs_nonneg (coeff b)]
      have habs : |N a b * coeff a * coeff b|
          ≤ scale b / scale a * |N a b| * coeff a ^ 2 / 2
            + scale a / scale b * |N a b| * coeff b ^ 2 / 2 := by
        rw [abs_mul, abs_mul]
        nlinarith [abs_nonneg (N a b), hamgm, abs_nonneg (coeff a), abs_nonneg (coeff b)]
      linarith [neg_abs_le (N a b * coeff a * coeff b)]
  -- The two off-diagonal halves reassemble into the scaled rows.
  have hrow : ∑ a ∈ omitted, ∑ b ∈ omitted,
      (if b = a then 0 else scale b / scale a * |N a b| * coeff a ^ 2 / 2)
        = ∑ a ∈ omitted, coeff a ^ 2 / (2 * scale a)
            * complementScaledRowOff direction mass weight omitted scale a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [complementScaledRowOff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hba : b = a
    · simp [hba]
    · rw [if_neg hba, if_neg hba]
      field_simp
      ring
  have hcol : ∑ a ∈ omitted, ∑ b ∈ omitted,
      (if b = a then 0 else scale a / scale b * |N a b| * coeff b ^ 2 / 2)
        = ∑ b ∈ omitted, coeff b ^ 2 / (2 * scale b)
            * complementScaledRowOff direction mass weight omitted scale b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [complementScaledRowOff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hab : a = b
    · simp [hab]
    · have hba : b ≠ a := fun h => hab h.symm
      rw [if_neg hab, if_neg hba, hsymm a b]
      field_simp
      ring
  have hdiag : ∑ a ∈ omitted, ∑ b ∈ omitted, N a a * coeff a ^ 2 * (if b = a then 1 else 0)
      = ∑ a ∈ omitted, N a a * coeff a ^ 2 := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum, Finset.sum_ite_eq' omitted a (fun _ => (1 : ℝ))]
    simp [ha]
  have hminor : ∑ a ∈ omitted, coeff a ^ 2 / scale a
        * (scale a * N a a - complementScaledRowOff direction mass weight omitted scale a)
      ≤ complementForm direction mass weight omitted coeff := by
    rw [complementForm_eq_sum]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun a ha =>
      Finset.sum_le_sum fun b hb => hpoint a ha b hb)
    have hsplit : ∀ a b : Fin size,
        N a a * coeff a ^ 2 * (if b = a then 1 else 0)
            - (if b = a then 0 else
                scale b / scale a * |N a b| * coeff a ^ 2 / 2
                  + scale a / scale b * |N a b| * coeff b ^ 2 / 2)
          = N a a * coeff a ^ 2 * (if b = a then 1 else 0)
              - (if b = a then 0 else scale b / scale a * |N a b| * coeff a ^ 2 / 2)
              - (if b = a then 0 else scale a / scale b * |N a b| * coeff b ^ 2 / 2) := by
      intro a b
      by_cases hba : b = a
      · simp [hba]
      · simp only [if_neg hba]
        ring
    simp only [hsplit, Finset.sum_sub_distrib]
    rw [hdiag, hrow, hcol]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hsa := hscale a ha
    field_simp
    ring
  obtain ⟨label, hlabel, hcoeff⟩ := hne
  refine lt_of_lt_of_le ?_ hminor
  refine Finset.sum_pos' (fun a ha => ?_) ⟨label, hlabel, ?_⟩
  · exact mul_nonneg (div_nonneg (sq_nonneg _) (hscale a ha).le)
      (sub_nonneg.mpr (hslack a ha).le)
  · have hs := hscale label hlabel
    exact mul_pos (by positivity) (sub_pos.mpr (hslack label hlabel))

/-- **The scaled kill on the chart gap.** -/
theorem posDef_directionChartGap_of_scaledRowSlack_pos (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size))
    (scale : Fin size → ℝ) (hscale : ∀ a ∈ selectedᶜ, 0 < scale a)
    (hboost : ∀ label ∈ selectedᶜ, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ a ∈ selectedᶜ,
      complementScaledRowOff direction mass weight selectedᶜ scale a
        < scale a * complementMatrixEntry direction mass weight a a) :
    (directionChartGap direction mass weight selected).PosDef :=
  (posDef_directionChartGap_iff_complementForm direction mass weight selected hboost
    huniv).mpr
    (complementForm_pos_of_scaledRowSlack_pos direction mass weight selectedᶜ scale hscale
      huniv hslack)

/-- Plain diagonal dominance is the scaled criterion at every scale equal to
one. -/
theorem complementScaledRowOff_one (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (omitted : Finset (Fin size)) (a : Fin size) :
    complementScaledRowOff direction mass weight omitted (fun _ => 1) a
      = complementRowOff direction mass weight omitted a := by
  rw [complementScaledRowOff, complementRowOff]
  exact Finset.sum_congr rfl fun b _ => by by_cases hba : b = a <;> simp [hba]

/-! ## Exactness at omitted count two

At two omitted labels the scaled criterion is not merely sufficient.  A scale
exists exactly when the landed pair inequality `N a b ^ 2 < N a a * N b b`
holds, so nothing is lost.  The witness is explicit and needs no square root.
-/

/-- **The scale that certifies a pair.**  Given the landed pair inequality, this
scale makes both rows dominate.  It is `1` at `a` and, at `b`, the ratio
`|N a b| / N b b` pushed up by a margin that the inequality pays for. -/
noncomputable def pairScale (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) (label : Fin size) : ℝ :=
  if label = a then 1
  else
    let cross := |complementMatrixEntry direction mass weight a b|
    let diagA := complementMatrixEntry direction mass weight a a
    let diagB := complementMatrixEntry direction mass weight b b
    cross / diagB + (diagA - cross ^ 2 / diagB) / (2 * (cross + 1))

/-- **THE EXACT PAIR LAW, FROM DIAGONAL DOMINANCE.**  Two omitted labels whose
diagonal entries are positive and whose cross entry obeys the landed inequality
leave a strictly dominating selection.  The proof exhibits a scale and spends the
scaled kill, so no two-by-two determinant is expanded anywhere. -/
theorem posDef_directionChartGap_of_pairCriterion (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) {a b : Fin size}
    (hne : a ≠ b) (hcompl : selectedᶜ = {a, b})
    (hboost : ∀ label ∈ selectedᶜ, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hdiagA : 0 < complementMatrixEntry direction mass weight a a)
    (hdiagB : 0 < complementMatrixEntry direction mass weight b b)
    (hcross : complementMatrixEntry direction mass weight a b ^ 2
      < complementMatrixEntry direction mass weight a a
        * complementMatrixEntry direction mass weight b b) :
    (directionChartGap direction mass weight selected).PosDef := by
  classical
  set cross := |complementMatrixEntry direction mass weight a b| with hcrossDef
  set diagA := complementMatrixEntry direction mass weight a a with hdiagADef
  set diagB := complementMatrixEntry direction mass weight b b with hdiagBDef
  have hcrossNonneg : 0 ≤ cross := abs_nonneg _
  have hcrossSq : cross ^ 2 < diagA * diagB := by
    rw [hcrossDef, sq_abs]; exact hcross
  have hdefect : 0 < diagA - cross ^ 2 / diagB := by
    rw [sub_pos, div_lt_iff₀ hdiagB]
    linarith
  set margin := (diagA - cross ^ 2 / diagB) / (2 * (cross + 1)) with hmargin
  have hmarginPos : 0 < margin := div_pos hdefect (by linarith)
  set t := cross / diagB + margin with ht
  have htPos : 0 < t := by positivity
  -- The scale is one at `a` and `t` at `b`.
  have hscaleA : pairScale direction mass weight a b a = 1 := by
    rw [pairScale, if_pos rfl]
  have hscaleB : pairScale direction mass weight a b b = t := by
    rw [pairScale, if_neg (Ne.symm hne), ht, hmargin]
  have hscalePos : ∀ label ∈ selectedᶜ, 0 < pairScale direction mass weight a b label := by
    intro label hlabel
    rw [hcompl] at hlabel
    rcases Finset.mem_insert.mp hlabel with h | h
    · rw [h, hscaleA]; norm_num
    · rw [Finset.mem_singleton.mp h, hscaleB]; exact htPos
  -- The two row inequalities the scale was built for.
  have hrowA : t * cross < diagA := by
    have h1 : cross / diagB * cross = cross ^ 2 / diagB := by
      field_simp
    have h2 : margin * cross ≤ (diagA - cross ^ 2 / diagB) / 2 := by
      rw [hmargin, div_mul_eq_mul_div,
        div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (cross + 1)) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hdefect, hcrossNonneg]
    have h3 : cross ^ 2 / diagB < diagA := by linarith
    rw [ht, add_mul, h1]
    linarith
  have hrowB : cross < t * diagB := by
    have h1 : cross / diagB * diagB = cross := by
      field_simp
    rw [ht, add_mul, h1]
    linarith [mul_pos hmarginPos hdiagB]
  refine posDef_directionChartGap_of_scaledRowSlack_pos direction mass weight selected
    (pairScale direction mass weight a b) hscalePos hboost huniv fun label hlabel => ?_
  rw [hcompl] at hlabel ⊢
  have hsymmEntry := complementMatrixEntry_symm direction mass weight huniv a b
  rcases Finset.mem_insert.mp hlabel with h | h
  · subst h
    rw [complementScaledRowOff, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
      if_pos rfl, if_neg (Ne.symm hne), hscaleA, hscaleB, one_mul]
    simpa [← hcrossDef, ← hdiagADef] using hrowA
  · rw [Finset.mem_singleton.mp h]
    rw [complementScaledRowOff, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
      if_neg hne, if_pos rfl, hscaleA, hscaleB, one_mul, add_zero, ← hsymmEntry]
    simpa [← hcrossDef, ← hdiagBDef] using hrowB

/-! ## The usable phrasing

The margin is the boost times a bracket, and the boost is positive at every
omitted label of a chart point.  So the criterion is the bracket alone: the
absolute cross pivots of an omitted label, weighted by the other boosts, must
stay strictly below its pivot defect.
-/

/-- **THE CROSS-PIVOT CRITERION.**  A selection is strictly dominating as soon as
every omitted label keeps its weighted absolute cross pivots strictly below its
pivot defect.

At omitted cardinality `k` this is `k` scalar inequalities.  Each one names the
pivot of a single label and the inverse-form entries between omitted labels, and
none of them is a determinant. -/
theorem posDef_directionChartGap_of_crossPivotSlack (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size))
    (hboost : ∀ label ∈ selectedᶜ, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hcross : ∀ a ∈ selectedᶜ,
      ∑ b ∈ selectedᶜ, (if b = a then 0 else
          |mass b / weight b| * |fullInverseForm direction mass weight a b|)
        < 1 - fullPivot direction mass weight a) :
    (directionChartGap direction mass weight selected).PosDef := by
  refine posDef_directionChartGap_of_rowSlack_pos direction mass weight selected hboost huniv
    fun a ha => ?_
  rw [complementRowSlack_eq_boost_mul direction mass weight selectedᶜ a (hboost a ha).le]
  exact mul_pos (hboost a ha) (sub_pos.mpr (hcross a ha))

/-! ## The three small cardinalities

At omitted cardinality one the criterion is the landed pivot law on the nose.  At
cardinality two it is a pair of linear inequalities that together imply the
landed exact pair law, so it is a proper sub-cell of it.  At cardinality three it
replaces a cubic determinant by three linear inequalities.
-/

/-- **Cardinality one.**  The empty off-diagonal row weight makes the criterion
`π_a < 1`, which is the landed single-label law. -/
theorem complementRowOff_singleton (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a : Fin size) :
    complementRowOff direction mass weight {a} a = 0 := by
  simp [complementRowOff]

/-- **Cardinality two, the row weights.**  Each of the two omitted labels sees
exactly the other. -/
theorem complementRowOff_pair (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {a b : Fin size} (hne : a ≠ b) :
    complementRowOff direction mass weight {a, b} a
      = |complementMatrixEntry direction mass weight a b| := by
  rw [complementRowOff, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  simp [Ne.symm hne]

/-- **Cardinality two is a proper sub-cell of the exact pair law.**  Two positive
row margins multiply to the landed pair inequality
`(N a b) ^ 2 < N a a * N b b`, so diagonal dominance implies the exact criterion
and never the other way. -/
theorem pairCriterion_of_rowSlack_pos (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {a b : Fin size} (hne : a ≠ b)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslackA : 0 < complementRowSlack direction mass weight {a, b} a)
    (hslackB : 0 < complementRowSlack direction mass weight {a, b} b) :
    complementMatrixEntry direction mass weight a b ^ 2
      < complementMatrixEntry direction mass weight a a
        * complementMatrixEntry direction mass weight b b := by
  have hpairA := complementRowOff_pair direction mass weight hne
  have hpairB : complementRowOff direction mass weight {a, b} b
      = |complementMatrixEntry direction mass weight a b| := by
    have hswap : ({a, b} : Finset (Fin size)) = {b, a} := Finset.pair_comm a b
    rw [hswap, complementRowOff_pair direction mass weight (Ne.symm hne),
      complementMatrixEntry_symm direction mass weight huniv b a]
  rw [complementRowSlack, hpairA] at hslackA
  rw [complementRowSlack, hpairB] at hslackB
  have habs : |complementMatrixEntry direction mass weight a b| ^ 2
      = complementMatrixEntry direction mass weight a b ^ 2 := sq_abs _
  nlinarith [abs_nonneg (complementMatrixEntry direction mass weight a b)]

/-! ## The design reading

At a design the mass equals the weight, so every boost is one and the criterion
loses its weights.  The inverse form becomes the landed pivot Gram and the pivot
becomes the landed full-selection pivot.
-/

/-- **The design gap dictionary at its own weights.**  The landed dictionary is
stated at `Gtz.designChartPoint`, whose mass and weight are the design's weight.
This is the same equality written so that a rewrite matches syntactically. -/
theorem directionChartGap_design (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) :
    directionChartGap design.atom design.weight design.weight selected
      = subsetSum design selected - 1 :=
  directionChartGap_designChartPoint design selected

/-- The chart gap of a design at the full selection is the design's own gap. -/
theorem directionChartGap_univ_design (design : WeightedDesign size 3) :
    directionChartGap design.atom design.weight design.weight Finset.univ
      = subsetSum design Finset.univ - 1 :=
  directionChartGap_design design Finset.univ

/-- The inverse form of a design is its landed pivot Gram. -/
theorem fullInverseForm_design (design : WeightedDesign size 3) (i j : Fin size) :
    fullInverseForm design.atom design.weight design.weight i j
      = fullPivotGram design i j := by
  rw [fullInverseForm, fullPivotGram, directionChartGap_univ_design]

/-- The full pivot of a design is its landed full-selection pivot. -/
theorem fullPivot_design (design : WeightedDesign size 3) (i : Fin size) :
    fullPivot design.atom design.weight design.weight i = fullPivotGram design i i := by
  rw [fullPivot, fullInverseForm_design, div_self (design.weight_pos i).ne', one_mul]

/-- **THE DESIGN CRITERION.**  A card-`k` complement of small absolute cross
pivots is strictly dominating.  Every boost is one, so the inequality at an
omitted label `a` reads: the sum of the absolute pivot-Gram entries to the other
omitted labels stays strictly below `1` minus the pivot of `a`. -/
theorem posDef_subsetSum_of_crossPivotSlack (design : WeightedDesign size 3)
    (selected : Finset (Fin size))
    (huniv : (subsetSum design Finset.univ - 1).PosDef)
    (hcross : ∀ a ∈ selectedᶜ,
      ∑ b ∈ selectedᶜ, (if b = a then 0 else |fullPivotGram design a b|)
        < 1 - fullPivotGram design a a) :
    (subsetSum design selected - 1).PosDef := by
  have hgap := directionChartGap_design design selected
  have hboost : ∀ label ∈ selectedᶜ,
      0 < design.weight label / design.weight label := fun label _ => by
    rw [div_self (design.weight_pos label).ne']; norm_num
  have huniv' : (directionChartGap design.atom design.weight design.weight
      Finset.univ).PosDef := by rwa [directionChartGap_univ_design]
  have hcross' : ∀ a ∈ selectedᶜ,
      ∑ b ∈ selectedᶜ, (if b = a then 0 else
          |design.weight b / design.weight b|
            * |fullInverseForm design.atom design.weight design.weight a b|)
        < 1 - fullPivot design.atom design.weight design.weight a := by
    intro a ha
    rw [fullPivot_design]
    refine lt_of_le_of_lt (le_of_eq ?_) (hcross a ha)
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hba : b = a
    · simp [hba]
    · rw [if_neg hba, if_neg hba, fullInverseForm_design,
        div_self (design.weight_pos b).ne', abs_one, one_mul]
  have := posDef_directionChartGap_of_crossPivotSlack design.atom design.weight design.weight
    selected hboost huniv' hcross'
  rwa [hgap] at this

/-- **The consumable design form.**  Small absolute cross pivots on the omitted
labels make the selection dominate, in the weak sense the campaign's target
`Gtz.GtzWeighted` asks for. -/
theorem dominates_of_crossPivotSlack (design : WeightedDesign size 3)
    (selected : Finset (Fin size))
    (huniv : (subsetSum design Finset.univ - 1).PosDef)
    (hcross : ∀ a ∈ selectedᶜ,
      ∑ b ∈ selectedᶜ, (if b = a then 0 else |fullPivotGram design a b|)
        < 1 - fullPivotGram design a a) :
    Dominates design selected :=
  (posDef_subsetSum_of_crossPivotSlack design selected huniv hcross).posSemidef

end Gtz

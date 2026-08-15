import Gtz.Wave.PlanePairSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The exact pair criterion, the strictness engine, and the isotropy spread

The plane base of the rank-three descent.  This module lands three new laws of
a plane frame, on the vocabulary of `Gtz.PlanePairDominates`.

## 1. The exact pair criterion

`Gtz.PlanePairDominatesStrict` is the strict pair test: every nonzero probe
reads a strict gap.  It is the division-free reading of `(P - 1).PosDef` for
the pair operator `P = b b^T / t + c c^T / s`.  The criterion is an EXACT
equivalence: the pair dominates strictly when the two shifted masses are
positive and the squared reading sits strictly below their product.  In budget
coordinates the same statement reads: the two budgets `1 - scale / mass` are
positive and the squared alignment is below their product.  Three probes read
the forward direction, and the strict scalar core reads the backward
direction.  The weak test gets the same two-gap form.

## 2. The strictness engine

`Gtz.planeActiveSet` holds the slots whose mass exceeds the scale.  When the
active budget `scale * (2 * mass - scale)` totals more than the active mass
total minus one, some active pair dominates STRICTLY
(`Gtz.exists_strictDominatingPlanePair`).  The proof squares the active gap
total against the row energy law.  No strict pair puts every squared reading
above the product of the two gaps.  The double sum of the readings is capped
by the active mass total, the square of the gap total sits above the gap
total, and the two bounds cancel into the budget inequality.  The engine works
at scale total EXACTLY one, where the landed selection theorem is weak.

## 3. The isotropy spread

`Gtz.PlaneParseval.exists_spread_pair` is the sixty-degree law: every plane
frame with positive masses carries a pair with four times the squared reading
at most the product of the two masses.  The landed separated partner gives
forty-five degrees at EVERY slot; the spread pair reaches sixty at SOME pair,
and sixty is sharp at the trine (`Gtz.planeTrine_spread_tight`).

The proof replaces the classical angle-sorting argument by pure algebra.  The
doubled unit readings balance to zero by the wrap law.  The MINIMAL pair of
doubled readings opens the widest doubled angle.  The plane Gram law — three
plane vectors are dependent, one polynomial identity — pins every other
doubled unit above the level `1 + cross` against that pair
(`Gtz.planeSpread_kernel`).  A zero balance refuses a positive level.

## 4. The consumers

* The HALF-MASS PAIR: every plane frame with positive masses carries a pair
  that dominates at half its masses, with no scale hypothesis at all.
* The SUB-HALF STRICT PAIR: the same pair dominates strictly at every pair of
  scales strictly below half the masses.
* The UNIFORM corollaries: an equal-mass frame at a uniform scale of total at
  most one carries a dominating pair, strictly below total one a strict pair.
  The criterion closes exactly: budgets one half against alignment one quarter.

## The field

The spread rests on the dimension count TWO of the doubled plane.  At doubled
dimension three the law FAILS: the four normalized Bloch readings of the
regular tetrahedron are units, they balance with positive weights, and every
pair reads minus one third, above the wide level minus one half
(`Gtz.blochTetra_no_widePair`).  The spread, and every consumer built on it,
is REAL-ONLY.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.PlanePairDominatesStrict`, `.symm`, `.dominates`, `.lt_div` — the strict
  pair test and its three faces.
* `Gtz.planeProbe_ne_zero_of_first`, `Gtz.planeProbe_ne_zero_of_second`,
  `Gtz.planeProbe_energy_pos` — the probe bookkeeping.
* `Gtz.planeForm_pos`, `Gtz.planeForm_pos_converse` — the strict scalar core,
  in both directions.
* `Gtz.planePairDominatesStrict_of_certificate`,
  `Gtz.planePair_strictGaps_of_dominates`,
  `Gtz.planePairDominatesStrict_iff` — **THE EXACT PAIR CRITERION.**
* `Gtz.planePairDominatesStrict_iff_budget` — the criterion in budget
  coordinates.
* `Gtz.planePairDominates_of_gaps`, `Gtz.planePairDominates_iff_gaps` — the
  weak test in two-gap form.
* `Gtz.planeActiveSet`, `Gtz.mem_planeActiveSet`,
  `Gtz.PlaneParseval.one_le_sum_active_gap` — the active set and its gap
  floor.
* `Gtz.exists_strictDominatingPlanePair`,
  `Gtz.exists_strictDominatingPlanePair_of_active` — **THE STRICTNESS
  ENGINE.**
* `Gtz.planeTripleGram_eq` — the plane Gram law.
* `Gtz.planeSpread_kernel` — **THE SPREAD KERNEL.**
* `Gtz.exists_wide_unit_pair` — **THE BALANCED UNITS SPREAD.**
* `Gtz.PlaneParseval.exists_spread_pair` — **THE ISOTROPY SPREAD.**
* `Gtz.planeTrine_spread_tight`, `Gtz.planeTrine_energy`,
  `Gtz.planeTrine_no_strictPair` — the spread and the strict engine are sharp
  at the trine.
* `Gtz.planeTrine_pair_tied`, `Gtz.planeTrine_not_parallel` — **THE LEGALITY
  FILTER.**  The trine is a genuine mass-one tie with NO parallel pair, so
  rank-two ties do not force parallel pairs: every proof of the rank-three
  hinge must consume rank-three structure.
* `Gtz.PlaneParseval.strict_or_tied_pair_uniform` — **THE TIE ALTERNATIVE.**
  At the uniform mass-one scale an equal-mass frame carries a strict pair or a
  pair tied at exactly sixty degrees.
* `Gtz.blochTetraUnit_dot_self`, `Gtz.blochTetraUnit_balance`,
  `Gtz.blochTetra_no_widePair` — the spread is real.
* `Gtz.PlaneParseval.exists_halfMass_pair`,
  `Gtz.PlaneParseval.exists_subHalf_strictPair`,
  `Gtz.PlaneParseval.exists_halfMass_strictPair` — the unconditional pairs,
  and the sharp energy threshold `4/3` of the strict half-mass pair.
* `Gtz.PlaneParseval.mass_eq_of_equal`,
  `Gtz.exists_dominatingPlanePair_uniform`,
  `Gtz.exists_strictDominatingPlanePair_uniform` — the uniform corollaries.
-/

namespace Gtz

open scoped BigOperators Matrix

/-! ## Layer 1 — the strict pair test -/

/-- **THE STRICT PAIR TEST.**  The two scaled outer products dominate the
identity of the plane STRICTLY: every nonzero probe reads a strict gap.  This
is the division-free reading of `(P - 1).PosDef` for the pair operator. -/
def PlanePairDominatesStrict (atomOne atomTwo : Fin 2 → ℝ) (scaleOne scaleTwo : ℝ) : Prop :=
  ∀ probe : Fin 2 → ℝ, probe ≠ 0 →
    scaleOne * scaleTwo * (probe ⬝ᵥ probe)
      < scaleTwo * (atomOne ⬝ᵥ probe) ^ 2 + scaleOne * (atomTwo ⬝ᵥ probe) ^ 2

/-- A plane probe with a nonzero first entry is not the zero probe. -/
theorem planeProbe_ne_zero_of_first {first second : ℝ} (hfirst : first ≠ 0) :
    (![first, second] : Fin 2 → ℝ) ≠ 0 := by
  intro hzero
  exact hfirst (by simpa using congrFun hzero 0)

/-- A plane probe with a nonzero second entry is not the zero probe. -/
theorem planeProbe_ne_zero_of_second {first second : ℝ} (hsecond : second ≠ 0) :
    (![first, second] : Fin 2 → ℝ) ≠ 0 := by
  intro hzero
  exact hsecond (by simpa using congrFun hzero 1)

/-- A nonzero plane probe carries positive energy, in coordinates. -/
theorem planeProbe_energy_pos {probe : Fin 2 → ℝ} (hprobe : probe ≠ 0) :
    0 < probe 0 ^ 2 + probe 1 ^ 2 := by
  rcases eq_or_ne (probe 0) 0 with hfirst | hfirst
  · rcases eq_or_ne (probe 1) 0 with hsecond | hsecond
    · refine absurd (funext fun index => ?_) hprobe
      fin_cases index
      · simpa using hfirst
      · simpa using hsecond
    · have hpos : 0 < probe 1 ^ 2 :=
        (sq_nonneg (probe 1)).lt_of_ne fun heq => hsecond (sq_eq_zero_iff.mp heq.symm)
      nlinarith [sq_nonneg (probe 0)]
  · have hpos : 0 < probe 0 ^ 2 :=
      (sq_nonneg (probe 0)).lt_of_ne fun heq => hfirst (sq_eq_zero_iff.mp heq.symm)
    nlinarith [sq_nonneg (probe 1)]

/-- The strict pair test does not depend on the order of the two slots. -/
theorem PlanePairDominatesStrict.symm {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hdom : PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo) :
    PlanePairDominatesStrict atomTwo atomOne scaleTwo scaleOne := by
  intro probe hprobe
  have hkey := hdom probe hprobe
  have hcomm : scaleTwo * scaleOne * (probe ⬝ᵥ probe)
      = scaleOne * scaleTwo * (probe ⬝ᵥ probe) := by ring
  rw [hcomm]
  linarith [hkey]

/-- A strictly dominating pair dominates. -/
theorem PlanePairDominatesStrict.dominates {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ}
    (hdom : PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo) :
    PlanePairDominates atomOne atomTwo scaleOne scaleTwo := by
  intro probe
  by_cases hzero : probe = 0
  · subst hzero
    simp
  · exact le_of_lt (hdom probe hzero)

/-- **THE DIVISION FORM OF THE STRICT PAIR TEST.** -/
theorem PlanePairDominatesStrict.lt_div {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hdom : PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo)
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo) {probe : Fin 2 → ℝ}
    (hprobe : probe ≠ 0) :
    probe ⬝ᵥ probe
      < (atomOne ⬝ᵥ probe) ^ 2 / scaleOne + (atomTwo ⬝ᵥ probe) ^ 2 / scaleTwo := by
  have hkey := hdom probe hprobe
  rw [div_add_div _ _ (ne_of_gt hposOne) (ne_of_gt hposTwo), lt_div_iff₀ (by positivity)]
  nlinarith [hkey]

/-! ## Layer 2 — the strict certificate, and the exact criterion -/

/-- **THE STRICT SCALAR CORE.**  A binary quadratic form of positive trace and
positive discriminant is positive away from the origin.  No eigenvalue, no
square root, no dimension. -/
theorem planeForm_pos {formA formB formC first second : ℝ}
    (htrace : 0 < formA + formC) (hdisc : formB ^ 2 < formA * formC)
    (hpoint : 0 < first ^ 2 + second ^ 2) :
    0 < formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2 := by
  have hkey : (formA + formC)
      * (formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2)
      = (formA * first + formB * second) ^ 2 + (formB * first + formC * second) ^ 2
        + (formA * formC - formB ^ 2) * (first ^ 2 + second ^ 2) := by
    ring
  have hrest : 0 < (formA * formC - formB ^ 2) * (first ^ 2 + second ^ 2) :=
    mul_pos (by linarith) hpoint
  have hprod : 0 < (formA + formC)
      * (formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2) := by
    rw [hkey]
    have hone : (0 : ℝ) ≤ (formA * first + formB * second) ^ 2 := sq_nonneg _
    have htwo : (0 : ℝ) ≤ (formB * first + formC * second) ^ 2 := sq_nonneg _
    linarith
  by_contra hneg
  rw [not_lt] at hneg
  nlinarith [hprod, htrace, hneg]

/-- **THE STRICT SCALAR CONVERSE.**  A binary quadratic form positive away from
the origin has a positive trace and a positive discriminant.  Three points
read it: the two frame points and the adjugate point. -/
theorem planeForm_pos_converse {formA formB formC : ℝ}
    (hform : ∀ first second : ℝ, 0 < first ^ 2 + second ^ 2 →
      0 < formA * first ^ 2 + 2 * formB * (first * second) + formC * second ^ 2) :
    0 < formA + formC ∧ formB ^ 2 < formA * formC := by
  have hA : 0 < formA := by
    have hread := hform 1 0 (by norm_num)
    nlinarith [hread]
  have hC : 0 < formC := by
    have hread := hform 0 1 (by norm_num)
    nlinarith [hread]
  have hdisc : 0 < formA * formC - formB ^ 2 := by
    have hpoint : 0 < (-formB) ^ 2 + formA ^ 2 := by
      nlinarith [sq_nonneg formB, mul_pos hA hA]
    have hread := hform (-formB) formA hpoint
    have hkey : formA * (-formB) ^ 2 + 2 * formB * (-formB * formA) + formC * formA ^ 2
        = formA * (formA * formC - formB ^ 2) := by
      ring
    rw [hkey] at hread
    nlinarith [hread, hA]
  exact ⟨by linarith, by linarith⟩

/-- **THE STRICT PAIR CERTIFICATE.**  Two positive shifted masses and a strict
determinant reading give the strict domination. -/
theorem planePairDominatesStrict_of_certificate {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ} (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hgapOne : scaleOne < atomOne ⬝ᵥ atomOne) (hgapTwo : scaleTwo < atomTwo ⬝ᵥ atomTwo)
    (hdet : (atomOne ⬝ᵥ atomTwo) ^ 2
      < (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) :
    PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo := by
  intro probe hprobe
  have hpoint := planeProbe_energy_pos hprobe
  simp only [dot_fin_two] at hgapOne hgapTwo hdet ⊢
  have htraceForm : 0 < (scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2
      - scaleOne * scaleTwo)
      + (scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2 - scaleOne * scaleTwo) := by
    nlinarith [mul_pos hposTwo (sub_pos.mpr hgapOne), mul_pos hposOne (sub_pos.mpr hgapTwo)]
  have hdiscForm : (scaleTwo * (atomOne 0 * atomOne 1) + scaleOne * (atomTwo 0 * atomTwo 1)) ^ 2
      < (scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2 - scaleOne * scaleTwo)
        * (scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2 - scaleOne * scaleTwo) := by
    nlinarith [mul_pos (mul_pos hposOne hposTwo) (sub_pos.mpr hdet)]
  have hcore := planeForm_pos htraceForm hdiscForm hpoint
  nlinarith [hcore]

/-- **THE THREE PROBES OF A STRICTLY DOMINATING PAIR.**  A strictly dominating
pair carries positive shifted masses and a strict determinant reading. -/
theorem planePair_strictGaps_of_dominates {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ} (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hdom : PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo) :
    scaleOne < atomOne ⬝ᵥ atomOne ∧ scaleTwo < atomTwo ⬝ᵥ atomTwo
      ∧ (atomOne ⬝ᵥ atomTwo) ^ 2
        < (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo) := by
  have hform : ∀ first second : ℝ, 0 < first ^ 2 + second ^ 2 →
      0 < (scaleTwo * atomOne 0 ^ 2 + scaleOne * atomTwo 0 ^ 2 - scaleOne * scaleTwo)
            * first ^ 2
          + 2 * (scaleTwo * (atomOne 0 * atomOne 1) + scaleOne * (atomTwo 0 * atomTwo 1))
            * (first * second)
          + (scaleTwo * atomOne 1 ^ 2 + scaleOne * atomTwo 1 ^ 2 - scaleOne * scaleTwo)
            * second ^ 2 := by
    intro first second hpoint
    have hne : (![first, second] : Fin 2 → ℝ) ≠ 0 := by
      intro hzero
      have hfirst : first = 0 := by simpa using congrFun hzero 0
      have hsecond : second = 0 := by simpa using congrFun hzero 1
      rw [hfirst, hsecond] at hpoint
      norm_num at hpoint
    have hprobe := hdom ![first, second] hne
    simp only [dot_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hprobe
    nlinarith [hprobe]
  obtain ⟨htrace, hdisc⟩ := planeForm_pos_converse hform
  have hdetDot : (atomOne ⬝ᵥ atomTwo) ^ 2
      < (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo) := by
    simp only [dot_fin_two]
    nlinarith [hdisc, mul_pos hposOne hposTwo]
  have hprodPos : 0 < (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo) :=
    lt_of_le_of_lt (sq_nonneg _) hdetDot
  rcases mul_pos_iff.mp hprodPos with ⟨honePos, htwoPos⟩ | ⟨honeNeg, htwoNeg⟩
  · exact ⟨sub_pos.mp honePos, sub_pos.mp htwoPos, hdetDot⟩
  · exfalso
    have hone := mul_neg_of_pos_of_neg hposTwo honeNeg
    have htwo := mul_neg_of_pos_of_neg hposOne htwoNeg
    simp only [dot_fin_two] at hone htwo
    nlinarith [htrace, hone, htwo]

/-- **THE EXACT PAIR CRITERION.**  At positive scales the strict domination and
the two-gap strict certificate are the same statement. -/
theorem planePairDominatesStrict_iff {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo) :
    PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo
      ↔ (scaleOne < atomOne ⬝ᵥ atomOne ∧ scaleTwo < atomTwo ⬝ᵥ atomTwo
          ∧ (atomOne ⬝ᵥ atomTwo) ^ 2
            < (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) := by
  constructor
  · exact fun hdom => planePair_strictGaps_of_dominates hposOne hposTwo hdom
  · intro hcert
    exact planePairDominatesStrict_of_certificate hposOne hposTwo hcert.1 hcert.2.1 hcert.2.2

/-- **THE EXACT PAIR CRITERION IN BUDGET COORDINATES.**  With the budget
`1 - scale / mass` of each slot, the strict pair test says: the two budgets are
positive and the squared alignment sits strictly below their product. -/
theorem planePairDominatesStrict_iff_budget {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ} (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hmassOne : 0 < atomOne ⬝ᵥ atomOne) (hmassTwo : 0 < atomTwo ⬝ᵥ atomTwo) :
    PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo
      ↔ (0 < 1 - scaleOne / (atomOne ⬝ᵥ atomOne)
          ∧ 0 < 1 - scaleTwo / (atomTwo ⬝ᵥ atomTwo)
          ∧ (atomOne ⬝ᵥ atomTwo) ^ 2 / ((atomOne ⬝ᵥ atomOne) * (atomTwo ⬝ᵥ atomTwo))
            < (1 - scaleOne / (atomOne ⬝ᵥ atomOne))
              * (1 - scaleTwo / (atomTwo ⬝ᵥ atomTwo))) := by
  rw [planePairDominatesStrict_iff hposOne hposTwo]
  have hmassMul : 0 < (atomOne ⬝ᵥ atomOne) * (atomTwo ⬝ᵥ atomTwo) :=
    mul_pos hmassOne hmassTwo
  have hexpand : (1 - scaleOne / (atomOne ⬝ᵥ atomOne))
      * (1 - scaleTwo / (atomTwo ⬝ᵥ atomTwo))
      * ((atomOne ⬝ᵥ atomOne) * (atomTwo ⬝ᵥ atomTwo))
      = (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo) := by
    field_simp
  constructor
  · rintro ⟨hone, htwo, hdet⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [sub_pos, div_lt_one hmassOne]
      exact hone
    · rw [sub_pos, div_lt_one hmassTwo]
      exact htwo
    · rw [div_lt_iff₀ hmassMul, hexpand]
      exact hdet
  · rintro ⟨hone, htwo, hdet⟩
    rw [sub_pos, div_lt_one hmassOne] at hone
    rw [sub_pos, div_lt_one hmassTwo] at htwo
    rw [div_lt_iff₀ hmassMul, hexpand] at hdet
    exact ⟨hone, htwo, hdet⟩

/-- **THE WEAK PAIR TEST FROM THE TWO GAPS.**  Nonnegative shifted masses and a
determinant reading give the domination.  This is the weak half of the exact
criterion, in the shape the budget engines consume. -/
theorem planePairDominates_of_gaps {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hgapOne : scaleOne ≤ atomOne ⬝ᵥ atomOne) (hgapTwo : scaleTwo ≤ atomTwo ⬝ᵥ atomTwo)
    (hdet : (atomOne ⬝ᵥ atomTwo) ^ 2
      ≤ (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) :
    PlanePairDominates atomOne atomTwo scaleOne scaleTwo := by
  refine planePairDominates_of_certificate hposOne hposTwo ?_ hdet
  nlinarith [mul_nonneg (le_of_lt hposTwo) (sub_nonneg.mpr hgapOne),
    mul_nonneg (le_of_lt hposOne) (sub_nonneg.mpr hgapTwo)]

/-- **THE WEAK PAIR TEST IS THE TWO-GAP CERTIFICATE.**  The landed trace
condition upgrades to the two individual gaps for free: the determinant reading
carries the product sign, and the trace refuses two negative gaps. -/
theorem planePairDominates_iff_gaps {atomOne atomTwo : Fin 2 → ℝ} {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo) :
    PlanePairDominates atomOne atomTwo scaleOne scaleTwo
      ↔ (scaleOne ≤ atomOne ⬝ᵥ atomOne ∧ scaleTwo ≤ atomTwo ⬝ᵥ atomTwo
          ∧ (atomOne ⬝ᵥ atomTwo) ^ 2
            ≤ (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) := by
  constructor
  · intro hdom
    have htrace := planePair_trace_of_dominates hdom
    have hdet := planePair_certificate_of_dominates hposOne hposTwo hdom
    have hgapOne : scaleOne ≤ atomOne ⬝ᵥ atomOne := by
      by_contra hlt
      rw [not_le] at hlt
      have hother : atomTwo ⬝ᵥ atomTwo - scaleTwo ≤ 0 := by
        by_contra hpos
        rw [not_le] at hpos
        have hneg := mul_neg_of_neg_of_pos
          (show atomOne ⬝ᵥ atomOne - scaleOne < 0 by linarith) hpos
        linarith [hdet, sq_nonneg (atomOne ⬝ᵥ atomTwo)]
      nlinarith [htrace, hlt, hother, hposOne, hposTwo]
    have hgapTwo : scaleTwo ≤ atomTwo ⬝ᵥ atomTwo := by
      by_contra hlt
      rw [not_le] at hlt
      have hother : atomOne ⬝ᵥ atomOne - scaleOne ≤ 0 := by
        by_contra hpos
        rw [not_le] at hpos
        have hneg := mul_neg_of_pos_of_neg hpos
          (show atomTwo ⬝ᵥ atomTwo - scaleTwo < 0 by linarith)
        linarith [hdet, sq_nonneg (atomOne ⬝ᵥ atomTwo)]
      nlinarith [htrace, hlt, hother, hposOne, hposTwo]
    exact ⟨hgapOne, hgapTwo, hdet⟩
  · rintro ⟨hone, htwo, hdet⟩
    exact planePairDominates_of_gaps hposOne hposTwo hone htwo hdet

/-! ## Layer 3 — the active set and the strictness engine -/

/-- **THE ACTIVE SET.**  The slots whose mass exceeds the scale: the slots with
a positive shifted gap, the slots a strict pair can use. -/
noncomputable def planeActiveSet {slotCount : ℕ} (atom : Fin slotCount → (Fin 2 → ℝ))
    (scale : Fin slotCount → ℝ) : Finset (Fin slotCount) :=
  Finset.univ.filter fun slot => scale slot < atom slot ⬝ᵥ atom slot

theorem mem_planeActiveSet {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    {scale : Fin slotCount → ℝ} {slot : Fin slotCount} :
    slot ∈ planeActiveSet atom scale ↔ scale slot < atom slot ⬝ᵥ atom slot := by
  simp [planeActiveSet]

/-- **THE ACTIVE GAP FLOOR.**  Under a scale total of at most one, the shifted
gaps of the active slots total at least one.  The mass law supplies two, the
scale total spends at most one, and the slots off the active set only give
mass back. -/
theorem PlaneParseval.one_le_sum_active_gap {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (scale : Fin slotCount → ℝ) (hsmall : (∑ slot, scale slot) ≤ 1) :
    1 ≤ ∑ slot ∈ planeActiveSet atom scale, (atom slot ⬝ᵥ atom slot - scale slot) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun slot => scale slot < atom slot ⬝ᵥ atom slot)
    (fun slot => atom slot ⬝ᵥ atom slot - scale slot)
  have htotal : (∑ slot, (atom slot ⬝ᵥ atom slot - scale slot))
      = 2 - ∑ slot, scale slot := by
    rw [Finset.sum_sub_distrib, hframe.sum_mass]
  have hrest : (∑ slot ∈ Finset.univ.filter
      (fun slot => ¬ scale slot < atom slot ⬝ᵥ atom slot),
        (atom slot ⬝ᵥ atom slot - scale slot)) ≤ 0 :=
    Finset.sum_nonpos fun slot hslot => by
      rw [Finset.mem_filter, not_lt] at hslot
      linarith [hslot.2]
  have hActive : planeActiveSet atom scale
      = Finset.univ.filter (fun slot => scale slot < atom slot ⬝ᵥ atom slot) := rfl
  rw [hActive]
  linarith [hsplit, htotal, hrest, hsmall]

/-- **THE STRICTNESS ENGINE.**  A plane frame with a scale total of at most one
carries a STRICTLY dominating pair of active slots, when the active budget
`scale * (2 * mass - scale)` totals more than the active mass total minus one.

The proof squares the active gap total against the row energy law.  No strict
pair means every active pair reads its squared alignment at or above the
product of its two gaps.  The double sum of these readings is capped by the
active mass total.  The square of the gap total sits above the gap total,
because the gap total is at least one.  The two bounds cancel into the budget
inequality, which the hypothesis refuses. -/
theorem exists_strictDominatingPlanePair {slotCount : ℕ}
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 1)
    (hbudget : (∑ slot ∈ planeActiveSet atom scale, atom slot ⬝ᵥ atom slot)
      < 1 + ∑ slot ∈ planeActiveSet atom scale,
          scale slot * (2 * (atom slot ⬝ᵥ atom slot) - scale slot)) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ slotOne ∈ planeActiveSet atom scale ∧ slotTwo ∈ planeActiveSet atom scale
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (scale slotOne) (scale slotTwo) := by
  classical
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  have hfail : ∀ slotOne ∈ planeActiveSet atom scale,
      ∀ slotTwo ∈ planeActiveSet atom scale, slotOne ≠ slotTwo →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    intro slotOne hone slotTwo htwo hne
    by_contra hbig
    rw [not_le] at hbig
    exact hnone slotOne slotTwo hne hone htwo
      (planePairDominatesStrict_of_certificate (hpos slotOne) (hpos slotTwo)
        (mem_planeActiveSet.mp hone) (mem_planeActiveSet.mp htwo) hbig)
  have hrow : ∀ slotOne ∈ planeActiveSet atom scale,
      (∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        ≤ atom slotOne ⬝ᵥ atom slotOne := by
    intro slotOne _
    have hsub : (∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        ≤ ∑ slotTwo, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun slotTwo _ _ => sq_nonneg _)
    have hfull : (∑ slotTwo, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        = atom slotOne ⬝ᵥ atom slotOne := by
      rw [← hframe.rowEnergy slotOne]
      exact Finset.sum_congr rfl fun slotTwo _ => by
        rw [dotProduct_comm (atom slotOne) (atom slotTwo), pow_two]
    rw [← hfull]
    exact hsub
  have hdouble : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
      ≤ ∑ slotOne ∈ planeActiveSet atom scale, atom slotOne ⬝ᵥ atom slotOne :=
    Finset.sum_le_sum hrow
  have hsplitAlign : ∀ slotOne ∈ planeActiveSet atom scale,
      (∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
        = (atom slotOne ⬝ᵥ atom slotOne) ^ 2
          + ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := fun slotOne hone =>
    (Finset.add_sum_erase _ (fun slotTwo => (atom slotOne ⬝ᵥ atom slotTwo) ^ 2) hone).symm
  have hsplitGap : ∀ slotOne ∈ planeActiveSet atom scale,
      (∑ slotTwo ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
        = (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          + ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
                * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := fun slotOne hone =>
    (Finset.add_sum_erase _
      (fun slotTwo => (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
        * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)) hone).symm
  have hoff : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
      ≤ ∑ slotOne ∈ planeActiveSet atom scale,
          ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
            (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 :=
    Finset.sum_le_sum fun slotOne hone =>
      Finset.sum_le_sum fun slotTwo htwo =>
        hfail slotOne hone slotTwo (Finset.mem_of_mem_erase htwo)
          (Finset.ne_of_mem_erase htwo).symm
  have hsquare : (∑ slotOne ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
      * (∑ slotTwo ∈ planeActiveSet atom scale,
          (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
      = ∑ slotOne ∈ planeActiveSet atom scale,
          ∑ slotTwo ∈ planeActiveSet atom scale,
            (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
              * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) :=
    Finset.sum_mul_sum _ _ _ _
  have htotalAlign : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotTwo) ^ 2)
      = (∑ slotOne ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotOne) ^ 2)
        + ∑ slotOne ∈ planeActiveSet atom scale,
            ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplitAlign
  have htotalGap : (∑ slotOne ∈ planeActiveSet atom scale,
      ∑ slotTwo ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo))
      = (∑ slotOne ∈ planeActiveSet atom scale,
          (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
        + ∑ slotOne ∈ planeActiveSet atom scale,
            ∑ slotTwo ∈ (planeActiveSet atom scale).erase slotOne,
              (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
                * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplitGap
  have hgapFloor := hframe.one_le_sum_active_gap scale hsmall
  have hgapSq : (∑ slotOne ∈ planeActiveSet atom scale,
        (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
      ≤ (∑ slotOne ∈ planeActiveSet atom scale,
          (atom slotOne ⬝ᵥ atom slotOne - scale slotOne))
        * (∑ slotTwo ∈ planeActiveSet atom scale,
            (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)) := by
    nlinarith [hgapFloor]
  have hpoint : (∑ slotOne ∈ planeActiveSet atom scale, (atom slotOne ⬝ᵥ atom slotOne) ^ 2)
      - ∑ slotOne ∈ planeActiveSet atom scale,
          (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
            * (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
      = ∑ slotOne ∈ planeActiveSet atom scale,
          scale slotOne * (2 * (atom slotOne ⬝ᵥ atom slotOne) - scale slotOne) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun slotOne _ => by ring
  linarith [hdouble, htotalAlign, hoff, htotalGap, hsquare, hgapSq, hgapFloor,
    hpoint, hbudget]

/-- **THE ALL-ACTIVE STRICTNESS ENGINE.**  When every slot is active the mass
law pins the active mass total at two, and the budget hypothesis collapses to
`1 < total budget`. -/
theorem exists_strictDominatingPlanePair_of_active {slotCount : ℕ}
    (atom : Fin slotCount → (Fin 2 → ℝ)) (scale : Fin slotCount → ℝ)
    (hframe : PlaneParseval atom) (hpos : ∀ slot, 0 < scale slot)
    (hsmall : (∑ slot, scale slot) ≤ 1)
    (hactive : ∀ slot, scale slot < atom slot ⬝ᵥ atom slot)
    (hbudget : 1 < ∑ slot, scale slot * (2 * (atom slot ⬝ᵥ atom slot) - scale slot)) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (scale slotOne) (scale slotTwo) := by
  have hall : planeActiveSet atom scale = Finset.univ :=
    Finset.eq_univ_of_forall fun slot => mem_planeActiveSet.mpr (hactive slot)
  obtain ⟨slotOne, slotTwo, hne, -, -, hdom⟩ :=
    exists_strictDominatingPlanePair atom scale hframe hpos hsmall (by
      rw [hall]
      have hmass := hframe.sum_mass
      linarith [hbudget, hmass])
  exact ⟨slotOne, slotTwo, hne, hdom⟩

/-! ## Layer 4 — the isotropy spread -/

/-- **THE PLANE GRAM LAW.**  Three vectors of the plane are dependent: the Gram
determinant vanishes, as one polynomial identity of the six readings. -/
theorem planeTripleGram_eq (vecOne vecTwo vecThree : Fin 2 → ℝ) :
    (vecOne ⬝ᵥ vecOne) * ((vecTwo ⬝ᵥ vecTwo) * (vecThree ⬝ᵥ vecThree))
      + 2 * ((vecOne ⬝ᵥ vecTwo) * ((vecTwo ⬝ᵥ vecThree) * (vecOne ⬝ᵥ vecThree)))
      = (vecOne ⬝ᵥ vecOne) * (vecTwo ⬝ᵥ vecThree) ^ 2
        + (vecTwo ⬝ᵥ vecTwo) * (vecOne ⬝ᵥ vecThree) ^ 2
        + (vecThree ⬝ᵥ vecThree) * (vecOne ⬝ᵥ vecTwo) ^ 2 := by
  simp only [dot_fin_two]
  ring

/-- **THE SPREAD KERNEL.**  Three numbers that obey the plane Gram law of a
unit triple, with the cross reading minimal and above minus one half, keep the
two alignments at or above the level `1 + cross`.  The factored dichotomy
`(sum - (1 + cross)) * (sum - (1 + cross) * (2 * cross - 1)) ≥ 0` carries the
whole geometry, and the low branch dies against `sum ≥ 2 * cross`. -/
theorem planeSpread_kernel {alignOne alignTwo cross : ℝ}
    (hrel : alignOne ^ 2 + alignTwo ^ 2 + cross ^ 2
      = 1 + 2 * cross * (alignOne * alignTwo))
    (hwide : -(1 / 2) < cross)
    (hone : cross ≤ alignOne) (htwo : cross ≤ alignTwo) :
    1 + cross ≤ alignOne + alignTwo := by
  have hfactor : (alignOne + alignTwo - (1 + cross))
      * (alignOne + alignTwo - (1 + cross) * (2 * cross - 1))
      = 2 * (1 + cross) * ((alignOne - cross) * (alignTwo - cross)) := by
    linear_combination hrel
  have hnonneg : 0 ≤ (alignOne + alignTwo - (1 + cross))
      * (alignOne + alignTwo - (1 + cross) * (2 * cross - 1)) := by
    rw [hfactor]
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (sub_nonneg.mpr htwo), hwide]
  rcases le_or_gt (1 + cross) (alignOne + alignTwo) with hdone | hless
  · exact hdone
  · exfalso
    have hsecond : alignOne + alignTwo - (1 + cross) * (2 * cross - 1) ≤ 0 := by
      nlinarith [hnonneg, hless]
    have hcorner : 0 ≤ (2 * cross + 1) * (cross - 1) := by
      nlinarith [hsecond, hone, htwo]
    have hcrossGe : 1 ≤ cross := by
      nlinarith [hcorner, hwide]
    linarith [hone, htwo, hless, hcrossGe]

/-- **THE BALANCED UNITS SPREAD.**  Unit vectors of the plane with positive
weights that balance to zero always hold a pair reading minus one half or
lower.  The minimal pair opens the widest angle, the spread kernel reads every
slot at or above the level `1 + cross` against that pair, and a zero balance
refuses a positive level. -/
theorem exists_wide_unit_pair {slotCount : ℕ} (hcount : 2 ≤ slotCount)
    (unit : Fin slotCount → (Fin 2 → ℝ)) (weight : Fin slotCount → ℝ)
    (hunit : ∀ slot, unit slot ⬝ᵥ unit slot = 1) (hweight : ∀ slot, 0 < weight slot)
    (hbalance : ∀ point : Fin 2 → ℝ, (∑ slot, weight slot * (unit slot ⬝ᵥ point)) = 0) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ unit slotOne ⬝ᵥ unit slotTwo ≤ -(1 / 2) := by
  classical
  by_contra hnone
  simp only [not_exists, not_and, not_le] at hnone
  haveI : Nonempty (Fin slotCount) := Fin.pos_iff_nonempty.mp (by omega)
  have hne : ((Finset.univ : Finset (Fin slotCount)).offDiag).Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩⟩
    intro heq
    exact absurd (congrArg Fin.val heq) (by norm_num)
  obtain ⟨pair, hpairMem, hpairMin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin slotCount)).offDiag
      (fun pair => unit pair.1 ⬝ᵥ unit pair.2) hne
  obtain ⟨-, -, hpairNe⟩ := Finset.mem_offDiag.mp hpairMem
  have hwide : -(1 / 2) < unit pair.1 ⬝ᵥ unit pair.2 := hnone pair.1 pair.2 hpairNe
  have hcap : unit pair.1 ⬝ᵥ unit pair.2 ≤ 1 := by
    have hcs := plane_dot_sq_le (unit pair.1) (unit pair.2)
    rw [hunit pair.1, hunit pair.2] at hcs
    nlinarith [hcs]
  have hminOne : ∀ slot, unit pair.1 ⬝ᵥ unit pair.2 ≤ unit slot ⬝ᵥ unit pair.1 := by
    intro slot
    by_cases hsame : slot = pair.1
    · rw [hsame, hunit pair.1]
      exact hcap
    · exact hpairMin (slot, pair.1) (Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, hsame⟩)
  have hminTwo : ∀ slot, unit pair.1 ⬝ᵥ unit pair.2 ≤ unit slot ⬝ᵥ unit pair.2 := by
    intro slot
    by_cases hsame : slot = pair.2
    · rw [hsame, hunit pair.2]
      exact hcap
    · exact hpairMin (slot, pair.2) (Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, hsame⟩)
  have hlevel : ∀ slot, 1 + unit pair.1 ⬝ᵥ unit pair.2
      ≤ unit slot ⬝ᵥ unit pair.1 + unit slot ⬝ᵥ unit pair.2 := by
    intro slot
    have hgram := planeTripleGram_eq (unit pair.1) (unit pair.2) (unit slot)
    rw [hunit pair.1, hunit pair.2, hunit slot,
      dotProduct_comm (unit pair.1) (unit slot),
      dotProduct_comm (unit pair.2) (unit slot)] at hgram
    have hrel : (unit slot ⬝ᵥ unit pair.1) ^ 2 + (unit slot ⬝ᵥ unit pair.2) ^ 2
        + (unit pair.1 ⬝ᵥ unit pair.2) ^ 2
        = 1 + 2 * (unit pair.1 ⬝ᵥ unit pair.2)
            * ((unit slot ⬝ᵥ unit pair.1) * (unit slot ⬝ᵥ unit pair.2)) := by
      linear_combination (-1 : ℝ) * hgram
    exact planeSpread_kernel hrel hwide (hminOne slot) (hminTwo slot)
  have hbal := hbalance (unit pair.1 + unit pair.2)
  have hlow : (∑ slot, weight slot * (1 + unit pair.1 ⬝ᵥ unit pair.2))
      ≤ ∑ slot, weight slot * (unit slot ⬝ᵥ (unit pair.1 + unit pair.2)) := by
    refine Finset.sum_le_sum fun slot _ => ?_
    rw [dotProduct_add]
    exact mul_le_mul_of_nonneg_left (hlevel slot) (le_of_lt (hweight slot))
  rw [hbal, ← Finset.sum_mul] at hlow
  have hweightPos : 0 < ∑ slot, weight slot :=
    Finset.sum_pos (fun slot _ => hweight slot) Finset.univ_nonempty
  have hposLevel : (0 : ℝ) < 1 + unit pair.1 ⬝ᵥ unit pair.2 := by linarith [hwide]
  linarith [hlow, mul_pos hweightPos hposLevel]

/-- **THE ISOTROPY SPREAD.**  A plane frame with positive masses carries a pair
of slots at sixty degrees or wider: four times the squared reading is at most
the product of the two masses.  The doubled atoms, normalized to units, balance
under the mass weights by the wrap law, and the wide pair of that balance is
the spread pair of the frame. -/
theorem PlaneParseval.exists_spread_pair {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hcount : 2 ≤ slotCount) (hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ 4 * (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
        ≤ (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo) := by
  have hunit : ∀ slot, ((atom slot ⬝ᵥ atom slot)⁻¹ • planeDouble (atom slot)) ⬝ᵥ
      ((atom slot ⬝ᵥ atom slot)⁻¹ • planeDouble (atom slot)) = 1 := by
    intro slot
    have hne : atom slot ⬝ᵥ atom slot ≠ 0 := (hmass slot).ne'
    rw [smul_dotProduct, dotProduct_smul, planeDouble_dot_self, smul_eq_mul, smul_eq_mul]
    field_simp
  have hbalance : ∀ point : Fin 2 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ atom slot)
        * (((atom slot ⬝ᵥ atom slot)⁻¹ • planeDouble (atom slot)) ⬝ᵥ point)) = 0 := by
    intro point
    have hcollapse : ∀ slot : Fin slotCount, (atom slot ⬝ᵥ atom slot)
        * (((atom slot ⬝ᵥ atom slot)⁻¹ • planeDouble (atom slot)) ⬝ᵥ point)
        = planeDouble (atom slot) ⬝ᵥ point := by
      intro slot
      rw [smul_dotProduct, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (hmass slot).ne', one_mul]
    calc (∑ slot, (atom slot ⬝ᵥ atom slot)
          * (((atom slot ⬝ᵥ atom slot)⁻¹ • planeDouble (atom slot)) ⬝ᵥ point))
        = ∑ slot, planeDouble (atom slot) ⬝ᵥ point :=
          Finset.sum_congr rfl fun slot _ => hcollapse slot
      _ = ∑ slot, point ⬝ᵥ planeDouble (atom slot) :=
          Finset.sum_congr rfl fun slot _ => dotProduct_comm _ _
      _ = 0 := hframe.sum_dot_planeDouble point
  obtain ⟨slotOne, slotTwo, hne, hwide⟩ :=
    exists_wide_unit_pair hcount
      (fun slot => (atom slot ⬝ᵥ atom slot)⁻¹ • planeDouble (atom slot))
      (fun slot => atom slot ⬝ᵥ atom slot) hunit hmass hbalance
  refine ⟨slotOne, slotTwo, hne, ?_⟩
  have hcollapse : ((atom slotOne ⬝ᵥ atom slotOne)⁻¹ • planeDouble (atom slotOne)) ⬝ᵥ
      ((atom slotTwo ⬝ᵥ atom slotTwo)⁻¹ • planeDouble (atom slotTwo))
      = (atom slotOne ⬝ᵥ atom slotOne)⁻¹ * ((atom slotTwo ⬝ᵥ atom slotTwo)⁻¹
          * (planeDouble (atom slotOne) ⬝ᵥ planeDouble (atom slotTwo))) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hcollapse, planeDouble_dot] at hwide
  have hmul := mul_le_mul_of_nonneg_left hwide
    (le_of_lt (mul_pos (hmass slotOne) (hmass slotTwo)))
  have hclear : (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo)
      * ((atom slotOne ⬝ᵥ atom slotOne)⁻¹ * ((atom slotTwo ⬝ᵥ atom slotTwo)⁻¹
        * (2 * (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          - (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo))))
      = 2 * (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
        - (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo) := by
    have hneOne : atom slotOne ⬝ᵥ atom slotOne ≠ 0 := (hmass slotOne).ne'
    have hneTwo : atom slotTwo ⬝ᵥ atom slotTwo ≠ 0 := (hmass slotTwo).ne'
    field_simp
  rw [hclear] at hmul
  nlinarith [hmul]

/-- **THE SPREAD IS SHARP.**  Every distinct pair of the trine reads exactly
the sixty-degree boundary: four times the squared reading EQUALS the product
of the two masses. -/
theorem planeTrine_spread_tight {slotOne slotTwo : Fin 3} (hne : slotOne ≠ slotTwo) :
    4 * (planeTrineAtom slotOne ⬝ᵥ planeTrineAtom slotTwo) ^ 2
      = (planeTrineAtom slotOne ⬝ᵥ planeTrineAtom slotOne)
        * (planeTrineAtom slotTwo ⬝ᵥ planeTrineAtom slotTwo) := by
  rw [planeTrineAtom_dot hne, planeTrineAtom_mass, planeTrineAtom_mass]
  norm_num

/-- The trine carries mass energy exactly four thirds, the boundary of the
strict energy engine. -/
theorem planeTrine_energy :
    (∑ slot : Fin 3, (planeTrineAtom slot ⬝ᵥ planeTrineAtom slot) ^ 2) = 4 / 3 := by
  rw [Fin.sum_univ_three, planeTrineAtom_mass, planeTrineAtom_mass, planeTrineAtom_mass]
  norm_num

/-- **THE STRICTNESS ENGINE IS SHARP.**  At the trine no pair dominates
STRICTLY at the half-mass scales one third: the alignment reads the gap
product exactly.  The active budget of the trine totals exactly one, so the
strict budget inequality of the engine cannot be weakened. -/
theorem planeTrine_no_strictPair {slotOne slotTwo : Fin 3} (hne : slotOne ≠ slotTwo) :
    ¬ PlanePairDominatesStrict (planeTrineAtom slotOne) (planeTrineAtom slotTwo)
        (1 / 3) (1 / 3) := by
  intro hdom
  obtain ⟨-, -, hdet⟩ :=
    planePair_strictGaps_of_dominates (by norm_num) (by norm_num) hdom
  rw [planeTrineAtom_dot hne, planeTrineAtom_mass, planeTrineAtom_mass] at hdet
  norm_num at hdet

/-- **THE MERCEDES TIE, POSITIVE HALF.**  Every distinct pair of the trine
weakly dominates at the uniform mass-one scales one third.  With
`Gtz.planeTrine_no_strictPair` the trine is a genuine mass-one tie. -/
theorem planeTrine_pair_tied {slotOne slotTwo : Fin 3} (hne : slotOne ≠ slotTwo) :
    PlanePairDominates (planeTrineAtom slotOne) (planeTrineAtom slotTwo)
      (1 / 3) (1 / 3) := by
  refine planePairDominates_of_gaps (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [planeTrineAtom_mass]
    norm_num
  · rw [planeTrineAtom_mass]
    norm_num
  · rw [planeTrineAtom_dot hne, planeTrineAtom_mass, planeTrineAtom_mass]
    norm_num

/-- **THE LEGALITY FILTER.**  No pair of the trine is parallel: every squared
reading sits strictly below the product of the two masses.  With
`Gtz.planeTrine_pair_tied` and `Gtz.planeTrine_no_strictPair` the trine is a
mass-one tie with NO parallel pair.  A tie-confinement argument that is blind
to the rank would prove "tie forces a parallel pair" at rank two, and the
trine refutes that statement.  Every proof of the rank-three hinge must
consume rank-three structure. -/
theorem planeTrine_not_parallel {slotOne slotTwo : Fin 3} (hne : slotOne ≠ slotTwo) :
    (planeTrineAtom slotOne ⬝ᵥ planeTrineAtom slotTwo) ^ 2
      < (planeTrineAtom slotOne ⬝ᵥ planeTrineAtom slotOne)
        * (planeTrineAtom slotTwo ⬝ᵥ planeTrineAtom slotTwo) := by
  rw [planeTrineAtom_dot hne, planeTrineAtom_mass, planeTrineAtom_mass]
  norm_num

/-- The normalized Bloch tetrahedron readings are units. -/
theorem blochTetraUnit_dot_self (slot : Fin 4) :
    ((2 : ℝ) • blochTetraRead slot) ⬝ᵥ ((2 : ℝ) • blochTetraRead slot) = 1 := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    blochTetraRead_dot_self]
  norm_num

/-- The normalized Bloch tetrahedron readings balance under the weights one
half. -/
theorem blochTetraUnit_balance (point : Fin 3 → ℝ) :
    (∑ slot, (1 / 2 : ℝ) * (((2 : ℝ) • blochTetraRead slot) ⬝ᵥ point)) = 0 := by
  have hcollapse : ∀ slot : Fin 4, (1 / 2 : ℝ)
      * (((2 : ℝ) • blochTetraRead slot) ⬝ᵥ point)
      = blochTetraRead slot ⬝ᵥ point := by
    intro slot
    rw [smul_dotProduct, smul_eq_mul, ← mul_assoc]
    norm_num
  rw [Finset.sum_congr rfl fun slot _ => hcollapse slot]
  simp only [dot_fin_three]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul, blochTetraRead_sum 0, blochTetraRead_sum 1, blochTetraRead_sum 2]
  ring

/-- **THE SPREAD IS REAL.**  At doubled dimension three the balanced units
spread FAILS: the four normalized Bloch tetrahedron readings balance with
positive weights, and every distinct pair reads minus one third, strictly
above the wide level minus one half.  The dimension count two of the doubled
plane is the whole reason the spread lemma holds. -/
theorem blochTetra_no_widePair {slotOne slotTwo : Fin 4} (hne : slotOne ≠ slotTwo) :
    -(1 / 2) < ((2 : ℝ) • blochTetraRead slotOne) ⬝ᵥ ((2 : ℝ) • blochTetraRead slotTwo) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    blochTetraRead_dot hne]
  norm_num

/-! ## Layer 5 — the half-mass pair and the uniform corollaries -/

/-- **THE HALF-MASS PAIR.**  Every plane frame with positive masses carries a
pair that dominates the identity at HALF ITS MASSES, with no scale hypothesis.
The spread pair has alignment at most one quarter, and the half-mass budget is
exactly one half at every slot, so the two-gap certificate closes exactly. -/
theorem PlaneParseval.exists_halfMass_pair {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hcount : 2 ≤ slotCount) (hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo)
          ((atom slotOne ⬝ᵥ atom slotOne) / 2) ((atom slotTwo ⬝ᵥ atom slotTwo) / 2) := by
  obtain ⟨slotOne, slotTwo, hne, hspread⟩ := hframe.exists_spread_pair hcount hmass
  refine ⟨slotOne, slotTwo, hne, planePairDominates_of_gaps
    (div_pos (hmass slotOne) two_pos) (div_pos (hmass slotTwo) two_pos)
    (by linarith [hmass slotOne]) (by linarith [hmass slotTwo]) ?_⟩
  have hgap : (atom slotOne ⬝ᵥ atom slotOne - (atom slotOne ⬝ᵥ atom slotOne) / 2)
      * (atom slotTwo ⬝ᵥ atom slotTwo - (atom slotTwo ⬝ᵥ atom slotTwo) / 2)
      = (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo) / 4 := by
    ring
  rw [hgap]
  linarith [hspread]

/-- **THE SUB-HALF STRICT PAIR.**  The spread pair dominates STRICTLY at every
pair of scales strictly below half the masses.  The pair depends only on the
frame, so one selection serves all such scales at once. -/
theorem PlaneParseval.exists_subHalf_strictPair {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hcount : 2 ≤ slotCount) (hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ ∀ scaleOne scaleTwo : ℝ, 0 < scaleOne → 0 < scaleTwo →
          2 * scaleOne < atom slotOne ⬝ᵥ atom slotOne →
          2 * scaleTwo < atom slotTwo ⬝ᵥ atom slotTwo →
          PlanePairDominatesStrict (atom slotOne) (atom slotTwo) scaleOne scaleTwo := by
  obtain ⟨slotOne, slotTwo, hne, hspread⟩ := hframe.exists_spread_pair hcount hmass
  refine ⟨slotOne, slotTwo, hne,
    fun scaleOne scaleTwo hposOne hposTwo hhalfOne hhalfTwo => ?_⟩
  refine planePairDominatesStrict_of_certificate hposOne hposTwo
    (by linarith) (by linarith) ?_
  have hgapOne : (atom slotOne ⬝ᵥ atom slotOne) / 2
      < atom slotOne ⬝ᵥ atom slotOne - scaleOne := by linarith
  have hgapTwo : (atom slotTwo ⬝ᵥ atom slotTwo) / 2
      < atom slotTwo ⬝ᵥ atom slotTwo - scaleTwo := by linarith
  have hhalfPosOne : 0 < (atom slotOne ⬝ᵥ atom slotOne) / 2 := by linarith [hmass slotOne]
  have hhalfPosTwo : 0 < (atom slotTwo ⬝ᵥ atom slotTwo) / 2 := by linarith [hmass slotTwo]
  have hquarter := mul_lt_mul'' hgapOne hgapTwo (le_of_lt hhalfPosOne) (le_of_lt hhalfPosTwo)
  nlinarith [hspread, hquarter]

/-- **THE ENERGY THRESHOLD.**  A plane frame whose mass energy passes four
thirds carries a STRICT pair at the half-mass scales.  At the half-mass scales
the scale total is exactly one, every slot is active, and the budget reads
three quarters of the energy, so the engine fires exactly above four thirds.
The trine sits at energy exactly four thirds and refuses every strict pair:
the threshold is sharp. -/
theorem PlaneParseval.exists_halfMass_strictPair {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot)
    (henergy : 4 / 3 < ∑ slot, (atom slot ⬝ᵥ atom slot) ^ 2) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          ((atom slotOne ⬝ᵥ atom slotOne) / 2) ((atom slotTwo ⬝ᵥ atom slotTwo) / 2) :=
  exists_strictDominatingPlanePair_of_active atom
    (fun slot => (atom slot ⬝ᵥ atom slot) / 2) hframe
    (fun slot => div_pos (hmass slot) two_pos)
    (by
      rw [← Finset.sum_div, hframe.sum_mass]
      norm_num)
    (fun slot => by linarith [hmass slot])
    (by
      have hpoint : (∑ slot, (atom slot ⬝ᵥ atom slot) / 2
          * (2 * (atom slot ⬝ᵥ atom slot) - (atom slot ⬝ᵥ atom slot) / 2))
          = ∑ slot, 3 / 4 * (atom slot ⬝ᵥ atom slot) ^ 2 :=
        Finset.sum_congr rfl fun slot _ => by ring
      rw [hpoint, ← Finset.mul_sum]
      linarith [henergy])

/-- Equal masses in a plane frame read exactly `2 / slotCount` each. -/
theorem PlaneParseval.mass_eq_of_equal {slotCount : ℕ}
    {atom : Fin slotCount → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hcount : 0 < slotCount)
    (hequal : ∀ slotOne slotTwo, atom slotOne ⬝ᵥ atom slotOne
      = atom slotTwo ⬝ᵥ atom slotTwo) (slot : Fin slotCount) :
    atom slot ⬝ᵥ atom slot = 2 / slotCount := by
  have hsum : (∑ other, atom other ⬝ᵥ atom other) = 2 := hframe.sum_mass
  have hconst : (∑ other, atom other ⬝ᵥ atom other)
      = ∑ _other : Fin slotCount, atom slot ⬝ᵥ atom slot :=
    Finset.sum_congr rfl fun other _ => hequal other slot
  rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hcast : (0 : ℝ) < slotCount := by exact_mod_cast hcount
  rw [eq_div_iff (ne_of_gt hcast)]
  linarith [hsum]

/-- **THE UNIFORM SELECTION AT EQUAL MASSES.**  An equal-mass plane frame at a
uniform scale of total at most one carries a dominating pair.  The spread pair
reads alignment at most one quarter, the two budgets read at least one half,
and one half squared is one quarter: the criterion closes exactly. -/
theorem exists_dominatingPlanePair_uniform {slotCount : ℕ} (hcount : 2 ≤ slotCount)
    (atom : Fin slotCount → (Fin 2 → ℝ)) (hframe : PlaneParseval atom)
    (hequal : ∀ slotOne slotTwo, atom slotOne ⬝ᵥ atom slotOne
      = atom slotTwo ⬝ᵥ atom slotTwo)
    {scaleValue : ℝ} (hpos : 0 < scaleValue) (hsmall : slotCount * scaleValue ≤ 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo) scaleValue scaleValue := by
  have hcountPos : (0 : ℝ) < slotCount := by
    have hcast : (2 : ℝ) ≤ slotCount := by exact_mod_cast hcount
    linarith
  have hmassval : ∀ slot, atom slot ⬝ᵥ atom slot = 2 / slotCount :=
    hframe.mass_eq_of_equal (by omega) hequal
  have hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot := fun slot => by
    rw [hmassval slot]
    positivity
  obtain ⟨slotOne, slotTwo, hne, hspread⟩ := hframe.exists_spread_pair hcount hmass
  have hunitPos : (0 : ℝ) < 1 / slotCount := div_pos one_pos hcountPos
  have htwoDiv : (2 : ℝ) / slotCount = 2 * (1 / slotCount) := by ring
  have hscale : scaleValue ≤ 1 / slotCount := by
    rw [le_div_iff₀ hcountPos]
    linarith [hsmall]
  rw [hmassval slotOne, hmassval slotTwo, htwoDiv] at hspread
  refine ⟨slotOne, slotTwo, hne, planePairDominates_of_gaps hpos hpos ?_ ?_ ?_⟩
  · rw [hmassval slotOne, htwoDiv]
    linarith [hscale, hunitPos]
  · rw [hmassval slotTwo, htwoDiv]
    linarith [hscale, hunitPos]
  · rw [hmassval slotOne, hmassval slotTwo, htwoDiv]
    have hgapFloor : (1 : ℝ) / slotCount ≤ 2 * (1 / slotCount) - scaleValue := by
      linarith [hscale]
    nlinarith [hspread, hgapFloor, hunitPos]

/-- **THE TIE ALTERNATIVE.**  An equal-mass plane frame at the uniform
mass-one scale carries a STRICT pair, or a pair TIED at exactly sixty degrees:
four times the squared reading equals the product of the two masses, and the
pair still dominates weakly.  This is the first rung of the mass-one tie
classification: at the boundary, failure of strictness pins the spread pair to
the exact Mercedes angle. -/
theorem PlaneParseval.strict_or_tied_pair_uniform {slotCount : ℕ}
    (hcount : 2 ≤ slotCount) {atom : Fin slotCount → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom)
    (hequal : ∀ slotOne slotTwo, atom slotOne ⬝ᵥ atom slotOne
      = atom slotTwo ⬝ᵥ atom slotTwo) :
    (∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo)
          (1 / slotCount) (1 / slotCount))
    ∨ (∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ 4 * (atom slotOne ⬝ᵥ atom slotTwo) ^ 2
          = (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo)
      ∧ PlanePairDominates (atom slotOne) (atom slotTwo)
          (1 / slotCount) (1 / slotCount)) := by
  have hcountPos : (0 : ℝ) < slotCount := by
    have hcast : (2 : ℝ) ≤ slotCount := by exact_mod_cast hcount
    linarith
  have hmassval : ∀ slot, atom slot ⬝ᵥ atom slot = 2 / slotCount :=
    hframe.mass_eq_of_equal (by omega) hequal
  have hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot := fun slot => by
    rw [hmassval slot]
    positivity
  have hunitPos : (0 : ℝ) < 1 / slotCount := div_pos one_pos hcountPos
  have htwoDiv : (2 : ℝ) / slotCount = 2 * (1 / slotCount) := by ring
  obtain ⟨slotOne, slotTwo, hne, hspread⟩ := hframe.exists_spread_pair hcount hmass
  rcases eq_or_lt_of_le hspread with htie | hstrict
  · refine Or.inr ⟨slotOne, slotTwo, hne, htie, ?_⟩
    refine planePairDominates_of_gaps hunitPos hunitPos ?_ ?_ ?_
    · rw [hmassval slotOne, htwoDiv]
      linarith [hunitPos]
    · rw [hmassval slotTwo, htwoDiv]
      linarith [hunitPos]
    · rw [hmassval slotOne, hmassval slotTwo, htwoDiv]
      rw [hmassval slotOne, hmassval slotTwo, htwoDiv] at htie
      nlinarith [htie.le, htie.ge]
  · refine Or.inl ⟨slotOne, slotTwo, hne,
      planePairDominatesStrict_of_certificate hunitPos hunitPos ?_ ?_ ?_⟩
    · rw [hmassval slotOne, htwoDiv]
      linarith [hunitPos]
    · rw [hmassval slotTwo, htwoDiv]
      linarith [hunitPos]
    · rw [hmassval slotOne, hmassval slotTwo, htwoDiv]
      rw [hmassval slotOne, hmassval slotTwo, htwoDiv] at hstrict
      nlinarith [hstrict]

/-- **THE UNIFORM STRICT SELECTION AT EQUAL MASSES.**  Strictly below scale
total one the equal-mass frame carries a STRICT pair: the budgets pass one
half strictly, and the alignment quarter loses. -/
theorem exists_strictDominatingPlanePair_uniform {slotCount : ℕ} (hcount : 2 ≤ slotCount)
    (atom : Fin slotCount → (Fin 2 → ℝ)) (hframe : PlaneParseval atom)
    (hequal : ∀ slotOne slotTwo, atom slotOne ⬝ᵥ atom slotOne
      = atom slotTwo ⬝ᵥ atom slotTwo)
    {scaleValue : ℝ} (hpos : 0 < scaleValue) (hsmall : slotCount * scaleValue < 1) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo
      ∧ PlanePairDominatesStrict (atom slotOne) (atom slotTwo) scaleValue scaleValue := by
  have hcountPos : (0 : ℝ) < slotCount := by
    have hcast : (2 : ℝ) ≤ slotCount := by exact_mod_cast hcount
    linarith
  have hmassval : ∀ slot, atom slot ⬝ᵥ atom slot = 2 / slotCount :=
    hframe.mass_eq_of_equal (by omega) hequal
  have hmass : ∀ slot, 0 < atom slot ⬝ᵥ atom slot := fun slot => by
    rw [hmassval slot]
    positivity
  obtain ⟨slotOne, slotTwo, hne, hspread⟩ := hframe.exists_spread_pair hcount hmass
  have hunitPos : (0 : ℝ) < 1 / slotCount := div_pos one_pos hcountPos
  have htwoDiv : (2 : ℝ) / slotCount = 2 * (1 / slotCount) := by ring
  have hscale : scaleValue < 1 / slotCount := by
    rw [lt_div_iff₀ hcountPos]
    linarith [hsmall]
  rw [hmassval slotOne, hmassval slotTwo, htwoDiv] at hspread
  refine ⟨slotOne, slotTwo, hne,
    planePairDominatesStrict_of_certificate hpos hpos ?_ ?_ ?_⟩
  · rw [hmassval slotOne, htwoDiv]
    linarith [hscale, hunitPos]
  · rw [hmassval slotTwo, htwoDiv]
    linarith [hscale, hunitPos]
  · rw [hmassval slotOne, hmassval slotTwo, htwoDiv]
    have hgapFloor : (1 : ℝ) / slotCount < 2 * (1 / slotCount) - scaleValue := by
      linarith [hscale]
    nlinarith [hspread, hgapFloor, hunitPos]

end Gtz

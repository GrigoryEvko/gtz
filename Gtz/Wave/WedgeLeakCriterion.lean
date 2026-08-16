/-
# The wedge-leak criterion: the plane cover, collapsed

`Gtz.posDef_of_normalSurplus_planeCover` asks for two things at a unit normal
`n` and a selected subset `S`: a NORMAL SURPLUS, and a PLANE COVER at every
in-plane probe.  Both read UNWEIGHTED sums.  The design data are WEIGHTED.
This file removes the plane cover entirely on the stratum where it is the only
thing left, and replaces it by a single scalar comparison.

The stratum is `S`'s complement BLIND: every atom outside `S` reads zero
against `n`.  At rank three and card three that happens exactly when the
complement is a line, so this is the one-line class, read from the free side.

Write `u c = a c ⬝ᵥ n`, `v c = a c ⬝ᵥ p` and `d c = 1 - w c` for the WEIGHT
DEFICIT.  Weighted Parseval, restricted by blindness, gives three facts:

  `∑ over S, w u²  = n ⬝ᵥ n`,   `∑ over S, w u v = n ⬝ᵥ p`,
  `∑ over S, w v²  = p ⬝ᵥ p - (leak of the complement at p)`.

The first two say the WEIGHTED normal energy and the WEIGHTED cross term are
pinned by the ambient geometry and see no design freedom at all.  So the
unweighted surplus and the unweighted cross are carried ENTIRELY by the
deficit:

  `∑ over S, u² - n ⬝ᵥ n = ∑ over S, d u²`,
  `∑ over S, u v - n ⬝ᵥ p = ∑ over S, d u v`.

The plane cover compares a square of the cross against a product of the two
surpluses.  That is a Cauchy-Schwarz shape in the DEFICIT measure, and the
Lagrange identity turns the comparison into an identity plus a remainder.  The
remainder is a WEDGE sum over pairs, and what it must beat is the complement's
LEAK.  The result is an equivalence, not a sufficient condition:

  plane cover at `p`  ↔  deficit wedge at `p`  >  normal surplus × leak at `p`.

Every quantity is a polynomial in the design.  No eigenvalue, no compactness,
no normalization, and no rank-three input: sections 1 thru 5 are rank-generic.

## What this does NOT claim

`Gtz.not_freeTripleSelectorRule` refutes the free triple as a RULE.  The
criterion below is therefore not universally satisfied, and this file does not
say it is.  It says the plane cover IS the criterion, and it gives two
division-free sufficient conditions for it.

The direction also matters, and it runs against the landed
`Gtz.oneLine_lineEnergy_ge_of_sandwich`.  That floor bounds the line's weighted
in-plane energy FROM BELOW, and the line is exactly the complement here, so the
floor lower-bounds the LEAK.  A lower bound on the leak is an OBSTRUCTION to
this criterion, never a producer for it.  Section 7 records that as a theorem.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.RealVolumeFloor
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Design.ChartlessKill
import Gtz.Design.LineClassObstructions
import Gtz.Design.LiftCriterion
import Gtz.LinAlg.PsdKit
import Gtz.Wave.WeightedHalfPlane
import Gtz.Wave.ConsolidatedStrictTriple
import Gtz.Wave.ChartDesignGauge
import Gtz.Reduction.Deflation

namespace Gtz

open Finset Matrix

/-! ## 1. The Lagrange identity, in double-sum form

Stated for an arbitrary index type and an arbitrary real measure.  The
unordered-pair form needs a linear order on the index and a halving; the
double sum needs neither, and it is what the `Finset` layer consumes. -/

/-- **THE LAGRANGE IDENTITY, TWO SUPPORTS AND TWO MEASURES.**  The general form.
Nothing is assumed of either support, either measure, or either family, and the
two supports may overlap, be disjoint, or be equal. -/
theorem sum_sum_wedgeSq_eq_lagrange_pair {index : Type*}
    (leftSupport rightSupport : Finset index)
    (leftMeasure rightMeasure valueNormal valueProbe : index → ℝ) :
    ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
        leftMeasure leftLabel * rightMeasure rightLabel
          * (valueNormal leftLabel * valueProbe rightLabel
              - valueNormal rightLabel * valueProbe leftLabel) ^ 2
      = (∑ label ∈ leftSupport, leftMeasure label * valueNormal label ^ 2)
            * (∑ label ∈ rightSupport, rightMeasure label * valueProbe label ^ 2)
          + (∑ label ∈ leftSupport, leftMeasure label * valueProbe label ^ 2)
            * (∑ label ∈ rightSupport, rightMeasure label * valueNormal label ^ 2)
        - 2 * ((∑ label ∈ leftSupport, leftMeasure label
              * (valueNormal label * valueProbe label))
            * ∑ label ∈ rightSupport, rightMeasure label
                * (valueNormal label * valueProbe label)) := by
  have hsplit : ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
      leftMeasure leftLabel * rightMeasure rightLabel
        * (valueNormal leftLabel * valueProbe rightLabel
            - valueNormal rightLabel * valueProbe leftLabel) ^ 2
      = ((∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
            (leftMeasure leftLabel * valueNormal leftLabel ^ 2)
              * (rightMeasure rightLabel * valueProbe rightLabel ^ 2))
          + ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
              (leftMeasure leftLabel * valueProbe leftLabel ^ 2)
                * (rightMeasure rightLabel * valueNormal rightLabel ^ 2))
        - ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
            2 * ((leftMeasure leftLabel * (valueNormal leftLabel * valueProbe leftLabel))
              * (rightMeasure rightLabel
                  * (valueNormal rightLabel * valueProbe rightLabel))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun leftLabel _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun rightLabel _ => by ring
  have hcross : ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
      2 * ((leftMeasure leftLabel * (valueNormal leftLabel * valueProbe leftLabel))
        * (rightMeasure rightLabel * (valueNormal rightLabel * valueProbe rightLabel)))
      = 2 * ∑ leftLabel ∈ leftSupport, ∑ rightLabel ∈ rightSupport,
          (leftMeasure leftLabel * (valueNormal leftLabel * valueProbe leftLabel))
            * (rightMeasure rightLabel
                * (valueNormal rightLabel * valueProbe rightLabel)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun leftLabel _ => by rw [Finset.mul_sum]
  rw [hsplit, hcross, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]

/-- **THE LAGRANGE IDENTITY, DOUBLE-SUM FORM.**  For any finite support, any
real measure, and any two families, the Cauchy-Schwarz defect is exactly half
the double sum of measure-weighted wedge squares.  No positivity anywhere. -/
theorem sum_sum_wedgeSq_eq_lagrange {index : Type*} (support : Finset index)
    (measure valueNormal valueProbe : index → ℝ) :
    ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
        measure leftLabel * measure rightLabel
          * (valueNormal leftLabel * valueProbe rightLabel
              - valueNormal rightLabel * valueProbe leftLabel) ^ 2
      = 2 * ((∑ label ∈ support, measure label * valueNormal label ^ 2)
              * ∑ label ∈ support, measure label * valueProbe label ^ 2)
        - 2 * (∑ label ∈ support, measure label
                * (valueNormal label * valueProbe label)) ^ 2 := by
  rw [sum_sum_wedgeSq_eq_lagrange_pair support support measure measure valueNormal valueProbe]
  ring

/-! ## 2. The wedge total, and the leak -/

/-- The wedge of two atoms read against a normal and a probe.  Antisymmetric in
the two labels, and it vanishes on the diagonal. -/
noncomputable def wedgeShadow {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) (leftLabel rightLabel : Fin size) : ℝ :=
  (design.atom leftLabel ⬝ᵥ normalVec) * (design.atom rightLabel ⬝ᵥ probeVec)
    - (design.atom rightLabel ⬝ᵥ normalVec) * (design.atom leftLabel ⬝ᵥ probeVec)

theorem wedgeShadow_self {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) (label : Fin size) :
    wedgeShadow design normalVec probeVec label label = 0 := by
  unfold wedgeShadow; ring

theorem wedgeShadow_swap {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeVec : Fin rank → ℝ) (leftLabel rightLabel : Fin size) :
    wedgeShadow design normalVec probeVec rightLabel leftLabel
      = -wedgeShadow design normalVec probeVec leftLabel rightLabel := by
  unfold wedgeShadow; ring

/-- The measure-weighted wedge total over a selected subset.  Half a double sum,
so it counts each unordered pair once. -/
noncomputable def wedgeTotal {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) : ℝ :=
  (∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
      measure leftLabel * measure rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2) / 2

/-- **THE WEDGE TOTAL IS THE CAUCHY-SCHWARZ DEFECT.**  Lagrange, read on the
design's own shadows.  No hypothesis on the measure. -/
theorem wedgeTotal_eq_defect {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design measure selected normalVec probeVec
      = (∑ label ∈ selected, measure label * (design.atom label ⬝ᵥ normalVec) ^ 2)
          * (∑ label ∈ selected, measure label * (design.atom label ⬝ᵥ probeVec) ^ 2)
        - (∑ label ∈ selected, measure label
            * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))) ^ 2 := by
  unfold wedgeTotal wedgeShadow
  rw [sum_sum_wedgeSq_eq_lagrange selected measure
    (fun label => design.atom label ⬝ᵥ normalVec)
    (fun label => design.atom label ⬝ᵥ probeVec)]
  ring

theorem wedgeTotal_nonneg {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ)
    (hnonneg : ∀ label ∈ selected, 0 ≤ measure label) :
    0 ≤ wedgeTotal design measure selected normalVec probeVec := by
  unfold wedgeTotal
  have hsum : 0 ≤ ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
      measure leftLabel * measure rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2 :=
    Finset.sum_nonneg fun leftLabel hleft => Finset.sum_nonneg fun rightLabel hright =>
      mul_nonneg (mul_nonneg (hnonneg leftLabel hleft) (hnonneg rightLabel hright))
        (sq_nonneg _)
  linarith

/-- **THE WEDGE TOTAL IS MONOTONE IN THE MEASURE, WITH A RATIO.**  A pointwise
bound on the products of the two measures transfers to the totals. -/
theorem ratio_mul_wedgeTotal_le {size rank : ℕ} (design : WeightedDesign size rank)
    (measureLow measureHigh : Fin size → ℝ) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) (ratio : ℝ)
    (hbound : ∀ leftLabel ∈ selected, ∀ rightLabel ∈ selected,
      ratio * (measureLow leftLabel * measureLow rightLabel)
        ≤ measureHigh leftLabel * measureHigh rightLabel) :
    ratio * wedgeTotal design measureLow selected normalVec probeVec
      ≤ wedgeTotal design measureHigh selected normalVec probeVec := by
  have hscaled : ratio * ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
      measureLow leftLabel * measureLow rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2
      = ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
          ratio * (measureLow leftLabel * measureLow rightLabel)
            * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun leftLabel _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun rightLabel _ => by ring
  have hstep : ratio * ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
      measureLow leftLabel * measureLow rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2
      ≤ ∑ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
          measureHigh leftLabel * measureHigh rightLabel
            * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2 := by
    rw [hscaled]
    exact Finset.sum_le_sum fun leftLabel hleft => Finset.sum_le_sum fun rightLabel hright =>
      mul_le_mul_of_nonneg_right (hbound leftLabel hleft rightLabel hright) (sq_nonneg _)
  unfold wedgeTotal
  linarith

/-- The weight the complement of the selected subset spends on a probe.  This is
the quantity the landed line-energy floor bounds FROM BELOW. -/
noncomputable def complementLeak {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probeVec : Fin rank → ℝ) : ℝ :=
  ∑ outLabel ∈ selectedᶜ, design.weight outLabel * (design.atom outLabel ⬝ᵥ probeVec) ^ 2

theorem complementLeak_nonneg {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    0 ≤ complementLeak design selected probeVec :=
  Finset.sum_nonneg fun outLabel _ =>
    mul_nonneg (design.weight_pos outLabel).le (sq_nonneg _)

/-- The weight deficit `1 - w`.  Positive at every label of a design on two or
more atoms, because the weights are positive and sum to one. -/
noncomputable def weightDeficit {size rank : ℕ} (design : WeightedDesign size rank)
    (label : Fin size) : ℝ :=
  1 - design.weight label

theorem weightDeficit_pos {size rank : ℕ} (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (label : Fin size) : 0 < weightDeficit design label := by
  classical
  unfold weightDeficit
  have hcard : 1 < Fintype.card (Fin size) := by rw [Fintype.card_fin]; omega
  obtain ⟨otherLabel, hother⟩ := Fintype.exists_ne_of_one_lt_card hcard label
  have hsplit : design.weight label + ∑ rest ∈ Finset.univ.erase label, design.weight rest = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ label), design.weight_sum_one]
  have hrest : 0 < ∑ rest ∈ Finset.univ.erase label, design.weight rest :=
    Finset.sum_pos (fun rest _ => design.weight_pos rest)
      ⟨otherLabel, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ otherLabel⟩⟩
  linarith

/-! ## 3. Blindness pins the weighted readings

The complement is BLIND at `normalVec` when every atom outside `selected` reads
zero against it.  Parseval then places the whole weighted normal energy and the
whole weighted cross term inside `selected`, where the ambient geometry fixes
their values.  Nothing about the design survives in either. -/

/-- **BLINDNESS PINS THE WEIGHTED NORMAL ENERGY.**  It equals `n ⬝ᵥ n`, with no
design freedom left in it. -/
theorem sum_weight_normalSq_of_blind {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0) :
    ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2
      = normalVec ⬝ᵥ normalVec := by
  classical
  have htotal := dotProduct_self_eq_sum_weight_mul_sq design normalVec
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2)
  have houtside : ∑ outLabel ∈ selectedᶜ,
      design.weight outLabel * (design.atom outLabel ⬝ᵥ normalVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun outLabel hmem => by rw [hblind outLabel hmem]; ring
  linarith [htotal, hsplit, houtside]

/-- **BLINDNESS PINS THE WEIGHTED CROSS TERM.**  It equals `n ⬝ᵥ p`, again with
no design freedom. -/
theorem sum_weight_cross_of_blind {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0) :
    ∑ label ∈ selected, design.weight label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
      = normalVec ⬝ᵥ probeVec := by
  classical
  have htotal := dotProduct_eq_sum_weight_mul_dotProduct design normalVec probeVec
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ normalVec)
      * (design.atom label ⬝ᵥ probeVec))
  have houtside : ∑ outLabel ∈ selectedᶜ, design.weight outLabel
      * (design.atom outLabel ⬝ᵥ normalVec) * (design.atom outLabel ⬝ᵥ probeVec) = 0 :=
    Finset.sum_eq_zero fun outLabel hmem => by rw [hblind outLabel hmem]; ring
  have hreassoc : ∑ label ∈ selected, design.weight label
      * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
      = ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ normalVec)
        * (design.atom label ⬝ᵥ probeVec) :=
    Finset.sum_congr rfl fun label _ => by ring
  rw [hreassoc]
  linarith [htotal, hsplit, houtside]

/-- **PARSEVAL SPLITS THE PROBE ENERGY.**  Selected weighted energy plus leak is
the probe energy.  No blindness is used here. -/
theorem sum_weight_probeSq_add_leak {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    (∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
        + complementLeak design selected probeVec
      = probeVec ⬝ᵥ probeVec := by
  classical
  have htotal := dotProduct_self_eq_sum_weight_mul_sq design probeVec
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
  unfold complementLeak
  linarith [htotal, hsplit]

/-- **THE UNWEIGHTED NORMAL SURPLUS IS THE DEFICIT ENERGY.**  This is the exact
statement that the surplus a strict dominator needs is paid entirely out of the
weight deficit, and never out of the ambient norm. -/
theorem normalSurplus_eq_deficitEnergy {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0) :
    (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec
      = ∑ label ∈ selected, weightDeficit design label * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  have hpinned := sum_weight_normalSq_of_blind design selected normalVec hblind
  have hdeficit : ∑ label ∈ selected,
      weightDeficit design label * (design.atom label ⬝ᵥ normalVec) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
        - ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by unfold weightDeficit; ring
  rw [hdeficit, hpinned]

/-- **THE UNWEIGHTED CROSS TERM IS THE DEFICIT CROSS TERM**, once the ambient
pairing is subtracted.  At an in-plane probe the subtraction is zero. -/
theorem cross_eq_deficitCross {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0) :
    (∑ label ∈ selected,
        (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ normalVec))
        - normalVec ⬝ᵥ probeVec
      = ∑ label ∈ selected, weightDeficit design label
          * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) := by
  have hpinned := sum_weight_cross_of_blind design selected normalVec probeVec hblind
  have hdeficit : ∑ label ∈ selected, weightDeficit design label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
      = (∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ normalVec))
        - ∑ label ∈ selected, design.weight label
            * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by unfold weightDeficit; ring
  rw [hdeficit, hpinned]

/-- **THE UNWEIGHTED PLANE SURPLUS IS THE DEFICIT ENERGY MINUS THE LEAK.**  No
blindness is used, and no normalization. -/
theorem probeSurplus_eq_deficitEnergy_sub_leak {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (probeVec : Fin rank → ℝ) :
    (∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec
      = (∑ label ∈ selected, weightDeficit design label
          * (design.atom label ⬝ᵥ probeVec) ^ 2)
        - complementLeak design selected probeVec := by
  have hsplit := sum_weight_probeSq_add_leak design selected probeVec
  have hdeficit : ∑ label ∈ selected,
      weightDeficit design label * (design.atom label ⬝ᵥ probeVec) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
        - ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by unfold weightDeficit; ring
  rw [hdeficit]
  linarith

/-! ## 4. The collapse

The plane cover is a Cauchy-Schwarz comparison in the deficit measure.  Section
3 replaced all three of its ingredients by deficit quantities, and Lagrange
turns the comparison into an identity.  What survives is one scalar inequality
between the deficit wedge and the leak. -/

/-- **THE PLANE COVER, COLLAPSED.**  An EQUIVALENCE, at any rank, at any
normalization, at an arbitrary selected subset with a blind complement and an
arbitrary probe orthogonal to the normal.  The left side is the hypothesis
`Gtz.posDef_of_normalSurplus_planeCover` consumes at a unit normal.  The right
side names the whole content: the DEFICIT WEDGE of the selected atoms must beat
the NORMAL SURPLUS times the complement's LEAK. -/
theorem planeCover_iff_wedgeTotal_gt_surplus_mul_leak {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0)
    (horthogonal : normalVec ⬝ᵥ probeVec = 0) :
    (∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ normalVec)) ^ 2
        < ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec)
      ↔ (∑ label ∈ selected, weightDeficit design label
              * (design.atom label ⬝ᵥ normalVec) ^ 2)
            * complementLeak design selected probeVec
          < wedgeTotal design (weightDeficit design) selected normalVec probeVec := by
  have hcross := cross_eq_deficitCross design selected normalVec probeVec hblind
  rw [horthogonal, sub_zero] at hcross
  have hlagrange := wedgeTotal_eq_defect design (weightDeficit design) selected normalVec probeVec
  have hcrossOrder : ∑ label ∈ selected, weightDeficit design label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
      = ∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ normalVec) := hcross.symm
  rw [normalSurplus_eq_deficitEnergy design selected normalVec hblind,
    probeSurplus_eq_deficitEnergy_sub_leak design selected probeVec]
  rw [hcrossOrder] at hlagrange
  constructor
  · intro hcover; nlinarith [hlagrange, hcover]
  · intro hbeats; nlinarith [hlagrange, hbeats]

/-! ## 5. The producers

Two division-free sufficient conditions for the collapsed inequality.  The first
compares the deficit measure to the weight measure by a single ratio and asks
the leak to be light.  The second removes the probe quantifier entirely by
paying the leverage of the complement. -/

/-- **THE WEIGHTED WEDGE IS PINNED TOO.**  Under blindness and orthogonality the
weight-measure wedge total is the ambient normal energy times the probe energy
that the selected atoms carry.  It is a design invariant only through the
leak. -/
theorem weightWedgeTotal_eq_of_blind {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0)
    (horthogonal : normalVec ⬝ᵥ probeVec = 0) :
    wedgeTotal design design.weight selected normalVec probeVec
      = (normalVec ⬝ᵥ normalVec)
        * (probeVec ⬝ᵥ probeVec - complementLeak design selected probeVec) := by
  rw [wedgeTotal_eq_defect design design.weight selected normalVec probeVec,
    sum_weight_normalSq_of_blind design selected normalVec hblind,
    sum_weight_cross_of_blind design selected normalVec probeVec hblind, horthogonal]
  have hsplit := sum_weight_probeSq_add_leak design selected probeVec
  have hprobe : ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2
      = probeVec ⬝ᵥ probeVec - complementLeak design selected probeVec := by linarith
  rw [hprobe]
  ring

/-- **THE LIGHT-LEAK PRODUCER.**  A single scalar `rootRatio` comparing deficit
to weight at every selected label, plus a light leak, gives the collapsed
inequality.  Both hypotheses are division-free.

At equal selected weights the threshold is exactly `1 - w`, so this is not a
lossy packaging of the criterion: it is the criterion with the pairwise wedge
data replaced by its worst pair. -/
theorem wedgeTotal_gt_surplus_mul_leak_of_weightSlack {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) (rootRatio : ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0)
    (horthogonal : normalVec ⬝ᵥ probeVec = 0)
    (hrootNonneg : 0 ≤ rootRatio)
    (hslack : ∀ label ∈ selected,
      rootRatio * design.weight label ≤ weightDeficit design label)
    (hlight : ((∑ label ∈ selected, weightDeficit design label
          * (design.atom label ⬝ᵥ normalVec) ^ 2)
        + rootRatio ^ 2 * (normalVec ⬝ᵥ normalVec))
        * complementLeak design selected probeVec
      < rootRatio ^ 2 * (normalVec ⬝ᵥ normalVec) * (probeVec ⬝ᵥ probeVec)) :
    (∑ label ∈ selected, weightDeficit design label
          * (design.atom label ⬝ᵥ normalVec) ^ 2)
        * complementLeak design selected probeVec
      < wedgeTotal design (weightDeficit design) selected normalVec probeVec := by
  have hbound : ∀ leftLabel ∈ selected, ∀ rightLabel ∈ selected,
      rootRatio ^ 2 * (design.weight leftLabel * design.weight rightLabel)
        ≤ weightDeficit design leftLabel * weightDeficit design rightLabel := by
    intro leftLabel hleft rightLabel hright
    have hleftBound := hslack leftLabel hleft
    have hrightBound := hslack rightLabel hright
    have hleftNonneg : 0 ≤ rootRatio * design.weight leftLabel :=
      mul_nonneg hrootNonneg (design.weight_pos leftLabel).le
    have hrightNonneg : 0 ≤ rootRatio * design.weight rightLabel :=
      mul_nonneg hrootNonneg (design.weight_pos rightLabel).le
    have hproduct : (rootRatio * design.weight leftLabel) * (rootRatio * design.weight rightLabel)
        ≤ weightDeficit design leftLabel * weightDeficit design rightLabel :=
      mul_le_mul hleftBound hrightBound hrightNonneg
        (le_trans hleftNonneg hleftBound)
    nlinarith [hproduct]
  have hmono := ratio_mul_wedgeTotal_le design design.weight (weightDeficit design)
    selected normalVec probeVec (rootRatio ^ 2) hbound
  rw [weightWedgeTotal_eq_of_blind design selected normalVec probeVec hblind horthogonal] at hmono
  nlinarith [hmono, hlight]

/-- **THE PROBE-FREE PRODUCER.**  Every leak is at most the complement's weighted
leverage times the probe energy, so a leverage budget removes the probe
quantifier from the light-leak hypothesis. -/
theorem complementLeak_le_leverageBudget {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probeVec : Fin rank → ℝ) :
    complementLeak design selected probeVec
      ≤ (∑ outLabel ∈ selectedᶜ, design.weight outLabel * leverageOf (design.atom outLabel))
        * (probeVec ⬝ᵥ probeVec) := by
  classical
  unfold complementLeak
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun outLabel _ => ?_
  have hcauchy : (design.atom outLabel ⬝ᵥ probeVec) ^ 2
      ≤ leverageOf (design.atom outLabel) * (probeVec ⬝ᵥ probeVec) := by
    have hkey := dotProduct_sq_le_mul (design.atom outLabel) probeVec
    have hleverage : leverageOf (design.atom outLabel)
        = design.atom outLabel ⬝ᵥ design.atom outLabel := by
      unfold leverageOf dotProduct
      exact Finset.sum_congr rfl fun coord _ => by ring
    rw [hleverage]
    exact hkey
  linarith [mul_le_mul_of_nonneg_left hcauchy (design.weight_pos outLabel).le]

/-! ## 6. Strict domination at rank three

Rank three enters only here, through `Gtz.posDef_of_normalSurplus_planeCover`.
Sections 1 thru 5 are stated at general rank and prove nothing of rank three. -/

/-- **THE STRICT DOMINATOR, FROM THE COLLAPSED CRITERION.**  A blind complement
and the wedge inequality at every in-plane probe give a POSITIVE DEFINITE gap.
The normal surplus half of `Gtz.posDef_of_normalSurplus_planeCover` is free: it
is the landed `Gtz.dotProduct_subsetSum_sub_one_mulVec_pos_of_outsideFlat` read
through section 3. -/
theorem posDef_of_blindComplement_of_wedgeBeatsLeak {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ unitNormal = 0)
    (hwedge : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      (∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2)
          * complementLeak design selected probeVec
        < wedgeTotal design (weightDeficit design) selected unitNormal probeVec) :
    (subsetSum design selected - 1).PosDef := by
  have hnormalNe : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  have hsurplusForm : (0 : ℝ)
      < unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal) :=
    dotProduct_subsetSum_sub_one_mulVec_pos_of_outsideFlat design hsize selected
      hnormalNe hblind
  have hsplit := dotProduct_subsetSum_sub_one_mulVec design selected unitNormal
  have houtside : ∑ outLabel ∈ selectedᶜ,
      design.weight outLabel * (design.atom outLabel ⬝ᵥ unitNormal) ^ 2 = 0 :=
    Finset.sum_eq_zero fun outLabel hmem => by rw [hblind outLabel hmem]; ring
  have hdeficitPos : (0 : ℝ) < ∑ label ∈ selected,
      weightDeficit design label * (design.atom label ⬝ᵥ unitNormal) ^ 2 := by
    have hrewrite : ∑ label ∈ selected,
        weightDeficit design label * (design.atom label ⬝ᵥ unitNormal) ^ 2
        = ∑ label ∈ selected, (1 - design.weight label)
            * (design.atom label ⬝ᵥ unitNormal) ^ 2 :=
      Finset.sum_congr rfl fun label _ => by unfold weightDeficit; rfl
    rw [hrewrite]
    linarith [hsurplusForm, hsplit, houtside]
  have hsurplus : (1 : ℝ) < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2 := by
    have hidentity := normalSurplus_eq_deficitEnergy design selected unitNormal hblind
    rw [hunit] at hidentity
    linarith [hidentity, hdeficitPos]
  refine posDef_of_normalSurplus_planeCover design selected unitNormal hunit hsurplus
    fun probeVec horthogonal hprobeNe => ?_
  have hnormalOrth : unitNormal ⬝ᵥ probeVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  have hiff := planeCover_iff_wedgeTotal_gt_surplus_mul_leak design selected unitNormal probeVec
    hblind hnormalOrth
  rw [hunit] at hiff
  exact hiff.mpr (hwedge probeVec horthogonal hprobeNe)

/-- **THE LIGHT-LEAK STRICT DOMINATOR.**  The same conclusion from the scalar
weight-slack hypothesis and a light leak at every in-plane probe. -/
theorem posDef_of_blindComplement_of_weightSlack {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (rootRatio : ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ unitNormal = 0)
    (hrootNonneg : 0 ≤ rootRatio)
    (hslack : ∀ label ∈ selected,
      rootRatio * design.weight label ≤ weightDeficit design label)
    (hlight : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      ((∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2) + rootRatio ^ 2)
          * complementLeak design selected probeVec
        < rootRatio ^ 2 * (probeVec ⬝ᵥ probeVec)) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_of_blindComplement_of_wedgeBeatsLeak design hsize selected unitNormal hunit
    hblind fun probeVec horthogonal hprobeNe => ?_
  have hnormalOrth : unitNormal ⬝ᵥ probeVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  refine wedgeTotal_gt_surplus_mul_leak_of_weightSlack design selected unitNormal probeVec
    rootRatio hblind hnormalOrth hrootNonneg hslack ?_
  have hstep := hlight probeVec horthogonal hprobeNe
  rw [hunit]
  linarith [hstep]

/-- **THE PROBE-FREE STRICT DOMINATOR.**  A leverage budget on the complement
removes the probe quantifier.  Every hypothesis is now a scalar inequality in
the design's own weights, leverages and normal shadows. -/
theorem posDef_of_blindComplement_of_leverageBudget {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (rootRatio : ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ unitNormal = 0)
    (hrootPos : 0 < rootRatio)
    (hslack : ∀ label ∈ selected,
      rootRatio * design.weight label ≤ weightDeficit design label)
    (hbudget : ((∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2) + rootRatio ^ 2)
          * ∑ outLabel ∈ selectedᶜ, design.weight outLabel * leverageOf (design.atom outLabel)
        < rootRatio ^ 2) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_of_blindComplement_of_weightSlack design hsize selected unitNormal rootRatio
    hunit hblind hrootPos.le hslack fun probeVec horthogonal hprobeNe => ?_
  have hprobePos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hprobeNe
  have hleak := complementLeak_le_leverageBudget design selected probeVec
  have hsurplusNonneg : (0 : ℝ) ≤ ∑ label ∈ selected,
      weightDeficit design label * (design.atom label ⬝ᵥ unitNormal) ^ 2 :=
    Finset.sum_nonneg fun label _ =>
      mul_nonneg (weightDeficit_pos design hsize label).le (sq_nonneg _)
  have hfactorPos : (0 : ℝ) < (∑ label ∈ selected, weightDeficit design label
      * (design.atom label ⬝ᵥ unitNormal) ^ 2) + rootRatio ^ 2 := by
    nlinarith [hsurplusNonneg, hrootPos]
  nlinarith [hleak, hbudget, hprobePos, hfactorPos]

/-! ## 6b. The characterisation, and the exact refusal

`Gtz.normalSurplus_planeCover_of_posDef` is the exact converse of
`Gtz.posDef_of_normalSurplus_planeCover`.  Composing it with the collapse of
section 4 turns strict domination — a three-dimensional positivity over a
matrix — into ONE scalar inequality per in-plane direction, with every weight
explicit and no eigenvalue anywhere. -/

/-- **STRICT DOMINATION IS THE WEDGE-LEAK INEQUALITY.**  At a blind complement
and a unit normal, the gap of the selected subset is positive definite EXACTLY
when the deficit wedge beats the normal surplus times the leak, at every
in-plane probe.  This is the quantifier reduction for the stratum: the input is
a `PosDef` on `Fin 3`, the output is a polynomial comparison on a plane. -/
theorem posDef_iff_wedgeBeatsLeak {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ unitNormal = 0) :
    (subsetSum design selected - 1).PosDef
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
          (∑ label ∈ selected, weightDeficit design label
                * (design.atom label ⬝ᵥ unitNormal) ^ 2)
              * complementLeak design selected probeVec
            < wedgeTotal design (weightDeficit design) selected unitNormal probeVec := by
  constructor
  · intro hposDef probeVec horthogonal hprobeNe
    have hcover := (normalSurplus_planeCover_of_posDef design selected unitNormal hunit
      hposDef).2 probeVec horthogonal hprobeNe
    have hnormalOrth : unitNormal ⬝ᵥ probeVec = 0 := by
      rw [dotProduct_comm]; exact horthogonal
    have hiff := planeCover_iff_wedgeTotal_gt_surplus_mul_leak design selected unitNormal
      probeVec hblind hnormalOrth
    rw [hunit] at hiff
    exact hiff.mp hcover
  · exact posDef_of_blindComplement_of_wedgeBeatsLeak design hsize selected unitNormal hunit
      hblind

/-- **THE EXACT REFUSAL.**  A subset with a blind complement that fails to
dominate strictly hands back one in-plane direction and one inequality, with
the leak eliminated.  The two wedge totals carry the SAME pairwise shadows and
differ only in the measure, so this is a comparison of the deficit measure
against the weight measure, tilted by the normal surplus.  Nothing else about
the design survives. -/
theorem wedgeRefusal_of_not_posDef {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ unitNormal = 0)
    (hnotPosDef : ¬ (subsetSum design selected - 1).PosDef) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 ∧ probeVec ≠ 0 ∧
      wedgeTotal design (weightDeficit design) selected unitNormal probeVec
          + (∑ label ∈ selected, weightDeficit design label
              * (design.atom label ⬝ᵥ unitNormal) ^ 2)
            * wedgeTotal design design.weight selected unitNormal probeVec
        ≤ (∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2) * (probeVec ⬝ᵥ probeVec) := by
  have hcharacterised := posDef_iff_wedgeBeatsLeak design hsize selected unitNormal hunit hblind
  have hfails : ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      (∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2)
          * complementLeak design selected probeVec
        < wedgeTotal design (weightDeficit design) selected unitNormal probeVec :=
    fun hall => hnotPosDef (hcharacterised.mpr hall)
  push Not at hfails
  obtain ⟨probeVec, horthogonal, hprobeNe, hrefusal⟩ := hfails
  refine ⟨probeVec, horthogonal, hprobeNe, ?_⟩
  have hnormalOrth : unitNormal ⬝ᵥ probeVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  have hweighted := weightWedgeTotal_eq_of_blind design selected unitNormal probeVec
    hblind hnormalOrth
  rw [hunit, one_mul] at hweighted
  rw [hweighted]
  nlinarith [hrefusal]

/-! ## 7. The direction of the landed floor

`Gtz.oneLine_lineEnergy_ge_of_sandwich` bounds the line's weighted in-plane
energy FROM BELOW.  On this stratum the line IS the complement, so that floor
is a floor on the LEAK.  The criterion of section 4 needs the leak SMALL.  The
two therefore point in opposite directions, and the floor cannot be converted
into a plane cover.  The theorem below is that statement, proved: a floor on
the leak transports to an UPPER bound on the deficit wedge that the criterion
must beat, in the light-leak regime where the deficit is comparable. -/

/-- **THE LEAK FLOOR IS AN OBSTRUCTION, NOT A PRODUCER.**  If the complement's
leak at some in-plane probe is at least the whole probe energy, then the
selected atoms carry no weighted probe energy there, the weighted wedge total
vanishes, and no positive normal surplus can satisfy the criterion. -/
theorem not_wedgeBeatsLeak_of_full_leak {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hblind : ∀ outLabel ∈ selectedᶜ, design.atom outLabel ⬝ᵥ normalVec = 0)
    (horthogonal : normalVec ⬝ᵥ probeVec = 0)
    (hfull : probeVec ⬝ᵥ probeVec ≤ complementLeak design selected probeVec)
    (hsurplusPos : 0 < ∑ label ∈ selected, weightDeficit design label
      * (design.atom label ⬝ᵥ normalVec) ^ 2)
    (hprobeNe : probeVec ≠ 0) :
    ¬ ((∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ normalVec) ^ 2)
          * complementLeak design selected probeVec
        < wedgeTotal design (weightDeficit design) selected normalVec probeVec) := by
  have hweighted := weightWedgeTotal_eq_of_blind design selected normalVec probeVec
    hblind horthogonal
  have hweightNonneg : 0 ≤ wedgeTotal design design.weight selected normalVec probeVec :=
    wedgeTotal_nonneg design design.weight selected normalVec probeVec
      fun label _ => (design.weight_pos label).le
  have hprobePos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hprobeNe
  have hleakEq : complementLeak design selected probeVec = probeVec ⬝ᵥ probeVec := by
    have hsplit := sum_weight_probeSq_add_leak design selected probeVec
    have hselNonneg : (0 : ℝ) ≤ ∑ label ∈ selected,
        design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 :=
      Finset.sum_nonneg fun label _ =>
        mul_nonneg (design.weight_pos label).le (sq_nonneg _)
    linarith
  have hselZero : ∑ label ∈ selected,
      design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 = 0 := by
    have hsplit := sum_weight_probeSq_add_leak design selected probeVec
    linarith
  have hshadowZero : ∀ label ∈ selected, design.atom label ⬝ᵥ probeVec = 0 := by
    intro label hlabel
    have hterm : design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun other _ => mul_nonneg (design.weight_pos other).le (sq_nonneg _))).mp
        hselZero label hlabel
    have hsq : (design.atom label ⬝ᵥ probeVec) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with hzero | hzero
      · exact absurd hzero (design.weight_pos label).ne'
      · exact hzero
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  have hwedgeZero : wedgeTotal design (weightDeficit design) selected normalVec probeVec = 0 := by
    unfold wedgeTotal
    have hinner : ∀ leftLabel ∈ selected, ∑ rightLabel ∈ selected,
        weightDeficit design leftLabel * weightDeficit design rightLabel
          * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2 = 0 := by
      intro leftLabel hleft
      refine Finset.sum_eq_zero fun rightLabel hright => ?_
      have hwedgeZeroPair : wedgeShadow design normalVec probeVec leftLabel rightLabel = 0 := by
        unfold wedgeShadow
        rw [hshadowZero leftLabel hleft, hshadowZero rightLabel hright]
        ring
      rw [hwedgeZeroPair]
      ring
    rw [Finset.sum_congr rfl hinner]
    simp
  rw [hwedgeZero, hleakEq]
  push Not
  nlinarith [hsurplusPos, hprobePos]

/-! ## 8. The one-line class at size six

The line `{0, 1, 2}` has a normal, and the complement `{3, 4, 5}` is exactly
the set of atoms the normal does not blind.  So the free triple is the ONLY
card-three subset of a one-line design whose complement is blind, and the
criterion of section 4 is an exact reading of its strict domination. -/

theorem oneLine_compl_freeTriple : ({3, 4, 5} : Finset (Fin 6))ᶜ = ({0, 1, 2} : Finset (Fin 6)) := by
  decide

/-- **THE FREE TRIPLE OF A ONE-LINE DESIGN, DECIDED.**  Strict domination by
`{3, 4, 5}` at a unit line normal follows from the light-leak hypothesis alone.
`Gtz.not_freeTripleSelectorRule` refutes the free triple as a RULE, so the
hypothesis genuinely carries content and is not always satisfied. -/
theorem oneLine_freeTriple_posDef_of_lightLine (design : WeightedDesign 6 3)
    (unitNormal : Fin 3 → ℝ) (rootRatio : ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hrootNonneg : 0 ≤ rootRatio)
    (hslack : ∀ label ∈ ({3, 4, 5} : Finset (Fin 6)),
      rootRatio * design.weight label ≤ weightDeficit design label)
    (hlight : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      ((∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2) + rootRatio ^ 2)
          * complementLeak design {3, 4, 5} probeVec
        < rootRatio ^ 2 * (probeVec ⬝ᵥ probeVec)) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine posDef_of_blindComplement_of_weightSlack design (by norm_num) {3, 4, 5} unitNormal
    rootRatio hunit ?_ hrootNonneg hslack hlight
  rw [oneLine_compl_freeTriple]
  exact hlineFlat

/-- **THE PROBE-FREE READING AT THE ONE-LINE CLASS.**  The leak budget is the
LINE's weighted leverage, and the whole hypothesis is scalar. -/
theorem oneLine_freeTriple_posDef_of_lineLeverageBudget (design : WeightedDesign 6 3)
    (unitNormal : Fin 3 → ℝ) (rootRatio : ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hrootPos : 0 < rootRatio)
    (hslack : ∀ label ∈ ({3, 4, 5} : Finset (Fin 6)),
      rootRatio * design.weight label ≤ weightDeficit design label)
    (hbudget : ((∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2) + rootRatio ^ 2)
          * ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
              design.weight lineLabel * leverageOf (design.atom lineLabel)
        < rootRatio ^ 2) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine posDef_of_blindComplement_of_leverageBudget design (by norm_num) {3, 4, 5} unitNormal
    rootRatio hunit ?_ hrootPos hslack ?_
  · rw [oneLine_compl_freeTriple]; exact hlineFlat
  · rw [oneLine_compl_freeTriple]; exact hbudget

/-- The free triple has card three, so a strict gap there is a strict card-three
witness. -/
theorem oneLine_freeTriple_card : ({3, 4, 5} : Finset (Fin 6)).card = 3 := by decide

/-- **A ONE-LINE DESIGN WITH A LIGHT LINE IS NOT A TIE.**  This is the consumer
shape: `Gtz.IsTie` forbids every card-three subset from dominating strictly, and
the free triple does. -/
theorem oneLine_not_isTie_of_lineLeverageBudget (design : WeightedDesign 6 3)
    (unitNormal : Fin 3 → ℝ) (rootRatio : ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hrootPos : 0 < rootRatio)
    (hslack : ∀ label ∈ ({3, 4, 5} : Finset (Fin 6)),
      rootRatio * design.weight label ≤ weightDeficit design label)
    (hbudget : ((∑ label ∈ ({3, 4, 5} : Finset (Fin 6)), weightDeficit design label
            * (design.atom label ⬝ᵥ unitNormal) ^ 2) + rootRatio ^ 2)
          * ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
              design.weight lineLabel * leverageOf (design.atom lineLabel)
        < rootRatio ^ 2) :
    ¬ IsTie design := by
  intro htie
  exact htie.2 {3, 4, 5} oneLine_freeTriple_card
    (oneLine_freeTriple_posDef_of_lineLeverageBudget design unitNormal rootRatio hunit
      hlineFlat hrootPos hslack hbudget)

/-- **THE NORMAL IS FREE AT THE ONE-LINE PATTERN.**  The pattern supplies a unit
line normal, so the criterion needs no normal as input. -/
theorem oneLine_exists_unitNormal (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1
      ∧ ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ unitNormal = 0 := by
  obtain ⟨normalVec, hnormalNe, horthogonal⟩ := oneLine_has_lineNormal design hpattern
  obtain ⟨unitNormal, scale, hunit, hscale⟩ := exists_unitNormal_parallel_of_ne_zero hnormalNe
  refine ⟨unitNormal, hunit, fun lineLabel hmem => ?_⟩
  rw [hscale, dotProduct_smul, smul_eq_mul, horthogonal lineLabel hmem, mul_zero]

/-! ## 9. The master identity: the collapse with no blindness

Blindness was never needed.  Dropping it, the complement contributes its own
wedge total and a CROSSING wedge total between the selected atoms and the
outside ones.  What comes out is an identity for the Schur discriminant of the
gap of an ARBITRARY subset against an ARBITRARY pair of vectors:

  `(gap at n) * (gap at p) - (gap cross)²
     = inside wedge + outside wedge - crossing wedge`

with the inside carrying the DEFICIT measure, the outside the WEIGHT measure,
and the crossing one of each.  Section 4 is the case where the complement is
blind: there the outside wedge vanishes and the crossing wedge is the normal
surplus times the leak. -/

/-- The weighted cross term the complement spends on the two vectors. -/
noncomputable def complementCross {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) : ℝ :=
  ∑ outLabel ∈ selectedᶜ, design.weight outLabel
    * ((design.atom outLabel ⬝ᵥ normalVec) * (design.atom outLabel ⬝ᵥ probeVec))

/-- The CROSSING wedge: one leg inside the selected subset at deficit measure,
one leg outside at weight measure.  Not halved, because the two legs run over
different supports and each pair is met once. -/
noncomputable def mixedWedgeTotal {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) : ℝ :=
  ∑ inLabel ∈ selected, ∑ outLabel ∈ selectedᶜ,
    weightDeficit design inLabel * design.weight outLabel
      * wedgeShadow design normalVec probeVec inLabel outLabel ^ 2

theorem mixedWedgeTotal_nonneg {size rank : ℕ} (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) :
    0 ≤ mixedWedgeTotal design selected normalVec probeVec :=
  Finset.sum_nonneg fun inLabel _ => Finset.sum_nonneg fun outLabel _ =>
    mul_nonneg (mul_nonneg (weightDeficit_pos design hsize inLabel).le
      (design.weight_pos outLabel).le) (sq_nonneg _)

theorem mixedWedgeTotal_eq_defect {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) :
    mixedWedgeTotal design selected normalVec probeVec
      = (∑ label ∈ selected, weightDeficit design label
            * (design.atom label ⬝ᵥ normalVec) ^ 2)
          * complementLeak design selected probeVec
        + (∑ label ∈ selected, weightDeficit design label
              * (design.atom label ⬝ᵥ probeVec) ^ 2)
          * complementLeak design selected normalVec
        - 2 * ((∑ label ∈ selected, weightDeficit design label
              * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)))
            * complementCross design selected normalVec probeVec) := by
  unfold mixedWedgeTotal wedgeShadow complementLeak complementCross
  exact sum_sum_wedgeSq_eq_lagrange_pair selected selectedᶜ (weightDeficit design)
    design.weight (fun label => design.atom label ⬝ᵥ normalVec)
    (fun label => design.atom label ⬝ᵥ probeVec)

/-- **THE CROSS GAP IS THE DEFICIT CROSS MINUS THE COMPLEMENT CROSS.**  The
polarized companion of `Gtz.probeSurplus_eq_deficitEnergy_sub_leak`, with no
blindness and no orthogonality. -/
theorem crossGap_eq_deficitCross_sub_complementCross {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    (∑ label ∈ selected,
        (design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
        - normalVec ⬝ᵥ probeVec
      = (∑ label ∈ selected, weightDeficit design label
          * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)))
        - complementCross design selected normalVec probeVec := by
  classical
  have htotal := dotProduct_eq_sum_weight_mul_dotProduct design normalVec probeVec
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ normalVec)
      * (design.atom label ⬝ᵥ probeVec))
  have hselected : ∑ label ∈ selected, design.weight label
      * (design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)
      = ∑ label ∈ selected, design.weight label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) :=
    Finset.sum_congr rfl fun label _ => by ring
  have houtside : ∑ outLabel ∈ selectedᶜ, design.weight outLabel
      * (design.atom outLabel ⬝ᵥ normalVec) * (design.atom outLabel ⬝ᵥ probeVec)
      = complementCross design selected normalVec probeVec := by
    unfold complementCross
    exact Finset.sum_congr rfl fun outLabel _ => by ring
  have hdeficit : ∑ label ∈ selected, weightDeficit design label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
      = (∑ label ∈ selected,
          (design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
        - ∑ label ∈ selected, design.weight label
            * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by unfold weightDeficit; ring
  rw [hselected] at hsplit
  rw [houtside] at hsplit
  rw [hdeficit]
  linarith

/-- **THE MASTER IDENTITY.**  The Schur discriminant of any subset's gap, at any
two vectors, at any rank, equals INSIDE WEDGE plus OUTSIDE WEDGE minus CROSSING
WEDGE.  All three are sums of squared pairwise wedge shadows.  The inside runs
on the weight deficit, the outside on the weight, and the crossing on one of
each.  No hypothesis at all. -/
theorem gapDiscriminant_eq_wedgeBalance {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) :
    ((∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec)
        * ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec)
      - ((∑ label ∈ selected,
            (design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
          - normalVec ⬝ᵥ probeVec) ^ 2
      = (wedgeTotal design (weightDeficit design) selected normalVec probeVec
          + wedgeTotal design design.weight selectedᶜ normalVec probeVec)
        - mixedWedgeTotal design selected normalVec probeVec := by
  rw [probeSurplus_eq_deficitEnergy_sub_leak design selected normalVec,
    probeSurplus_eq_deficitEnergy_sub_leak design selected probeVec,
    crossGap_eq_deficitCross_sub_complementCross design selected normalVec probeVec,
    wedgeTotal_eq_defect design (weightDeficit design) selected normalVec probeVec,
    wedgeTotal_eq_defect design design.weight selectedᶜ normalVec probeVec,
    mixedWedgeTotal_eq_defect design selected normalVec probeVec]
  unfold complementLeak complementCross
  ring

/-! ## 10. The border criterion, at EVERY rank

`Gtz.posDef_of_normalSurplus_planeCover` and its converse
`Gtz.normalSurplus_planeCover_of_posDef` are stated at rank three.  Nothing in
the argument is rank three.  Splitting a test vector into its component along a
unit pivot and its residual, the gap form becomes a quadratic in the component
whose discriminant is exactly the border minor, so the criterion is an
EQUIVALENCE at every rank.

This is the rank-uniform positive-definiteness test the general-rank lane has
been missing.  It is not diagonal dominance, and unlike Sylvester it names no
coordinate: the pivot is any unit vector, and it may be chosen to suit the
design.  Sylvester needs `rank` nested leading minors in a fixed basis, and it
does not lift across the split hinge.  The border criterion needs ONE pivot and
one two-dimensional inequality per residual direction. -/

/-- The gap form of a subset, read as a sum of squares.  Any rank. -/
theorem dotProduct_subsetSum_sub_one_mulVec_eq_sumSq {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (probeVec : Fin rank → ℝ) :
    probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec := by
  rw [dotProduct_subsetSum_sub_one_mulVec design selected probeVec,
    probeSurplus_eq_deficitEnergy_sub_leak design selected probeVec]
  unfold weightDeficit complementLeak
  rfl

/-- The gap form expanded along a unit pivot.  The residual is orthogonal to the
pivot, so the pivot's own norm contributes exactly the square of the
component. -/
theorem gapForm_pivot_expansion {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (unitPivot residualVec : Fin rank → ℝ) (component : ℝ)
    (hunit : unitPivot ⬝ᵥ unitPivot = 1) (horthogonal : residualVec ⬝ᵥ unitPivot = 0) :
    (residualVec + component • unitPivot)
        ⬝ᵥ ((subsetSum design selected - 1) *ᵥ (residualVec + component • unitPivot))
      = ((∑ label ∈ selected, (design.atom label ⬝ᵥ residualVec) ^ 2)
            - residualVec ⬝ᵥ residualVec)
        + 2 * component * (∑ label ∈ selected, (design.atom label ⬝ᵥ residualVec)
            * (design.atom label ⬝ᵥ unitPivot))
        + component ^ 2
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2) - 1) := by
  rw [dotProduct_subsetSum_sub_one_mulVec_eq_sumSq design selected]
  have hatomSplit : ∀ label : Fin size,
      design.atom label ⬝ᵥ (residualVec + component • unitPivot)
        = (design.atom label ⬝ᵥ residualVec)
          + component * (design.atom label ⬝ᵥ unitPivot) := by
    intro label
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hpivotOrth : unitPivot ⬝ᵥ residualVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  have hself : (residualVec + component • unitPivot)
      ⬝ᵥ (residualVec + component • unitPivot)
      = residualVec ⬝ᵥ residualVec + component ^ 2 := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hunit, horthogonal, hpivotOrth]
    ring
  have hsum : ∑ label ∈ selected,
      (design.atom label ⬝ᵥ (residualVec + component • unitPivot)) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ residualVec) ^ 2)
        + 2 * component * (∑ label ∈ selected, (design.atom label ⬝ᵥ residualVec)
            * (design.atom label ⬝ᵥ unitPivot))
        + component ^ 2 * ∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun label _ => by rw [hatomSplit label]; ring
  rw [hsum, hself]
  ring

/-- **THE BORDER CRITERION, AT EVERY RANK.**  A positive surplus at one unit
pivot plus a strict border minor at every residual direction gives a positive
definite gap.  This generalizes the landed rank-three
`Gtz.posDef_of_normalSurplus_planeCover` to all ranks. -/
theorem posDef_of_normalSurplus_borderMinors {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (unitPivot : Fin rank → ℝ)
    (hunit : unitPivot ⬝ᵥ unitPivot = 1)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2)
    (hborder : ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitPivot = 0 → probeVec ≠ 0 →
      (∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec)
          * (design.atom label ⬝ᵥ unitPivot)) ^ 2
        < ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2) - 1)
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
              - probeVec ⬝ᵥ probeVec)) :
    (subsetSum design selected - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design selected),
      fun testVec htestNe => ?_⟩
  rw [star_trivial]
  have hresidualOrth : (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot) ⬝ᵥ unitPivot = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, sub_self]
  have hrebuild : testVec
      = (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot) + (testVec ⬝ᵥ unitPivot) • unitPivot := by
    abel
  have hexpansion := gapForm_pivot_expansion design selected unitPivot
    (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot) (testVec ⬝ᵥ unitPivot) hunit hresidualOrth
  rw [← hrebuild] at hexpansion
  rw [hexpansion]
  by_cases hresidualZero : testVec - (testVec ⬝ᵥ unitPivot) • unitPivot = 0
  · have hcomponentNe : testVec ⬝ᵥ unitPivot ≠ 0 := by
      intro hzero
      refine htestNe ?_
      rw [hrebuild, hresidualZero, hzero, zero_smul, add_zero]
    rw [hresidualZero]
    have hzeroSum : ∑ label ∈ selected, (design.atom label ⬝ᵥ (0 : Fin rank → ℝ)) ^ 2 = 0 :=
      Finset.sum_eq_zero fun label _ => by rw [dotProduct_zero]; ring
    have hzeroCross : ∑ label ∈ selected, (design.atom label ⬝ᵥ (0 : Fin rank → ℝ))
        * (design.atom label ⬝ᵥ unitPivot) = 0 :=
      Finset.sum_eq_zero fun label _ => by rw [dotProduct_zero]; ring
    rw [hzeroSum, hzeroCross, dotProduct_zero]
    have hsquarePos : 0 < (testVec ⬝ᵥ unitPivot) ^ 2 := by positivity
    nlinarith [hsurplus, hsquarePos]
  · have hborderHere := hborder (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot)
      hresidualOrth hresidualZero
    nlinarith [hborderHere, hsurplus,
      sq_nonneg ((testVec ⬝ᵥ unitPivot)
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2) - 1)
        + ∑ label ∈ selected,
            (design.atom label ⬝ᵥ (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot))
              * (design.atom label ⬝ᵥ unitPivot))]

/-- **THE BORDER CRITERION IS NECESSARY TOO, AT EVERY RANK.**  Generalizes the
landed rank-three `Gtz.normalSurplus_planeCover_of_posDef`. -/
theorem normalSurplus_borderMinors_of_posDef {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (unitPivot : Fin rank → ℝ)
    (hunit : unitPivot ⬝ᵥ unitPivot = 1)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2)
      ∧ ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitPivot = 0 → probeVec ≠ 0 →
          (∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec)
              * (design.atom label ⬝ᵥ unitPivot)) ^ 2
            < ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2) - 1)
              * ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
                  - probeVec ⬝ᵥ probeVec) := by
  have hgap : ∀ vec : Fin rank → ℝ, vec ≠ 0 →
      0 < (∑ label ∈ selected, (design.atom label ⬝ᵥ vec) ^ 2) - vec ⬝ᵥ vec := by
    intro vec hvecNe
    have hvalue := hposDef.dotProduct_mulVec_pos hvecNe
    rw [star_trivial, dotProduct_subsetSum_sub_one_mulVec_eq_sumSq design selected vec] at hvalue
    exact hvalue
  have hpivotNe : unitPivot ≠ 0 := fun hzero => by simp [hzero] at hunit
  have hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2 := by
    have hstep := hgap unitPivot hpivotNe
    rw [hunit] at hstep
    linarith
  refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
  set surplus : ℝ := (∑ label ∈ selected, (design.atom label ⬝ᵥ unitPivot) ^ 2) - 1
    with hsurplusDef
  set cross : ℝ := ∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec)
      * (design.atom label ⬝ᵥ unitPivot) with hcrossDef
  have hsurplusPos : 0 < surplus := by rw [hsurplusDef]; linarith
  have hquad : ∀ component : ℝ,
      0 < ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec)
        + 2 * component * cross + component ^ 2 * surplus := by
    intro component
    have hne : probeVec + component • unitPivot ≠ 0 := by
      intro hzero
      have hread : (probeVec + component • unitPivot) ⬝ᵥ probeVec = 0 := by
        rw [hzero, zero_dotProduct]
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm unitPivot probeVec,
        horthogonal, mul_zero, add_zero] at hread
      exact hprobeNe (dotProduct_self_eq_zero.mp hread)
    have hvalue := hgap (probeVec + component • unitPivot) hne
    have hpivotOrth : unitPivot ⬝ᵥ probeVec = 0 := by
      rw [dotProduct_comm]; exact horthogonal
    have hexpansion := gapForm_pivot_expansion design selected unitPivot probeVec component
      hunit horthogonal
    rw [dotProduct_subsetSum_sub_one_mulVec_eq_sumSq design selected] at hexpansion
    rw [hexpansion] at hvalue
    rw [hsurplusDef, hcrossDef]
    exact hvalue
  have hsurplusNe : surplus ≠ 0 := hsurplusPos.ne'
  have hoptimal := hquad (-cross / surplus)
  have hclear : ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
        - probeVec ⬝ᵥ probeVec)
      + 2 * (-cross / surplus) * cross + (-cross / surplus) ^ 2 * surplus
      = ((((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
            - probeVec ⬝ᵥ probeVec) * surplus) - cross ^ 2) / surplus := by
    field_simp
    ring
  rw [hclear] at hoptimal
  have hmul : 0 < ((((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2)
        - probeVec ⬝ᵥ probeVec) * surplus) - cross ^ 2) := by
    have hstep := mul_pos hoptimal hsurplusPos
    rwa [div_mul_cancel₀ _ hsurplusNe] at hstep
  nlinarith [hmul]

/-! ## 11. Strict domination, characterised at every subset and every rank

The master identity replaces the border minor by the wedge balance, at EVERY
subset of EVERY design at EVERY rank — no line pattern, no blindness, no
anatomy, no coordinate. -/

/-- The wedge balance at a probe: inside plus outside beats crossing. -/
def WedgeBalanceAt {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) : Prop :=
  mixedWedgeTotal design selected normalVec probeVec
    < wedgeTotal design (weightDeficit design) selected normalVec probeVec
      + wedgeTotal design design.weight selectedᶜ normalVec probeVec

/-- **THE BORDER MINOR IS THE WEDGE BALANCE.**  At a unit pivot and an
orthogonal probe, with no other hypothesis and at any rank. -/
theorem planeCover_iff_wedgeBalanceAt {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (unitNormal probeVec : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horthogonal : probeVec ⬝ᵥ unitNormal = 0) :
    ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec)
          * (design.atom label ⬝ᵥ unitNormal)) ^ 2
        < ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec))
      ↔ WedgeBalanceAt design selected unitNormal probeVec := by
  have hnormalOrth : unitNormal ⬝ᵥ probeVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  have hmaster := gapDiscriminant_eq_wedgeBalance design selected unitNormal probeVec
  rw [hunit, hnormalOrth, sub_zero] at hmaster
  have horder : ∑ label ∈ selected,
      (design.atom label ⬝ᵥ unitNormal) * (design.atom label ⬝ᵥ probeVec)
      = ∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ unitNormal) :=
    Finset.sum_congr rfl fun label _ => by ring
  rw [horder] at hmaster
  unfold WedgeBalanceAt
  constructor
  · intro hcover; nlinarith [hmaster, hcover]
  · intro hbalance; nlinarith [hmaster, hbalance]

/-- **STRICT DOMINATION, CHARACTERISED.**  For any subset of any design at rank
three, and any unit normal, the gap is positive definite exactly when the
normal surplus is positive and the wedge balance holds at every in-plane probe.
The normal may be chosen freely: the right side is therefore true for one unit
normal exactly when it is true for all of them. -/
theorem posDef_iff_normalSurplus_and_wedgeBalance {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (unitNormal : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    (subsetSum design selected - 1).PosDef
      ↔ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
        ∧ ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            WedgeBalanceAt design selected unitNormal probeVec := by
  constructor
  · intro hposDef
    obtain ⟨hsurplus, hcover⟩ :=
      normalSurplus_borderMinors_of_posDef design selected unitNormal hunit hposDef
    refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
    exact (planeCover_iff_wedgeBalanceAt design selected unitNormal probeVec hunit
      horthogonal).mp (hcover probeVec horthogonal hprobeNe)
  · rintro ⟨hsurplus, hbalance⟩
    refine posDef_of_normalSurplus_borderMinors design selected unitNormal hunit hsurplus
      fun probeVec horthogonal hprobeNe => ?_
    exact (planeCover_iff_wedgeBalanceAt design selected unitNormal probeVec hunit
      horthogonal).mpr (hbalance probeVec horthogonal hprobeNe)

/-- **DOMINATION AT ANY RANK, FROM ONE PIVOT.**  The rank-uniform consumer
shape: a subset whose gap is positive definite dominates, so a design carrying
one is not a tie.  `Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp` both ask for a
`Gtz.HasParallelPair` out of `Gtz.IsTie` at general rank, and this is the
instrument that turns a wedge balance into the strict witness that contradicts
the tie. -/
theorem not_isTie_of_wedgeBalance {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (unitNormal : Fin rank → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    (hbalance : ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard
    ((posDef_iff_normalSurplus_and_wedgeBalance design selected unitNormal hunit).mpr
      ⟨hsurplus, hbalance⟩)

/-! ## 11. The door

`Gtz.ConsolidatedStrictTripleDesign` implies all five on-path obligations
through `Gtz.allFiveOnPath_of_consolidatedStrictTripleDesign`.  Section 10 makes
it EQUIVALENT to a selection statement whose payload is a normal surplus and a
wedge balance.  The equivalence certifies the antecedent: it is satisfiable
exactly when the target is, so this entrance cannot be vacuous. -/

/-- A unit vector at rank three, to instantiate the free normal. -/
theorem dotProduct_firstAxis : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] = 1 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- **THE WEDGE-BALANCE SELECTOR.**  Every primitive design at size six and rank
three carries a triple, a unit normal, a positive normal surplus and the wedge
balance at every in-plane probe. -/
def WedgeBalanceSelector : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ (selected : Finset (Fin 6)) (unitNormal : Fin 3 → ℝ),
      selected.card = 3 ∧ unitNormal ⬝ᵥ unitNormal = 1
        ∧ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
        ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            WedgeBalanceAt design selected unitNormal probeVec

/-- **THE SELECTOR IS THE CONSOLIDATED STATEMENT.**  An equivalence, so the
antecedent is exactly as strong as the target and carries no hidden vacuity. -/
theorem consolidatedStrictTripleDesign_iff_wedgeBalanceSelector :
    ConsolidatedStrictTripleDesign ↔ WedgeBalanceSelector := by
  constructor
  · intro hconsolidated design hprimitive
    obtain ⟨selected, hcard, hposDef⟩ := hconsolidated design hprimitive
    obtain ⟨hsurplus, hbalance⟩ :=
      (posDef_iff_normalSurplus_and_wedgeBalance design selected ![1, 0, 0]
        dotProduct_firstAxis).mp hposDef
    exact ⟨selected, ![1, 0, 0], hcard, dotProduct_firstAxis, hsurplus, hbalance⟩
  · intro hselector design hprimitive
    obtain ⟨selected, unitNormal, hcard, hunit, hsurplus, hbalance⟩ := hselector design hprimitive
    exact ⟨selected, hcard,
      (posDef_iff_normalSurplus_and_wedgeBalance design selected unitNormal hunit).mpr
        ⟨hsurplus, hbalance⟩⟩

/-- **THE ENTRANCE.**  The wedge-balance selector retires all five on-path
obligations. -/
theorem allFiveOnPath_of_wedgeBalanceSelector (hselector : WedgeBalanceSelector) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_consolidatedStrictTripleDesign
    (consolidatedStrictTripleDesign_iff_wedgeBalanceSelector.mpr hselector)

/-! ## 12. The general-rank hinge, on the strictly light branch

`Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp` both take the predecessor
cell `Gtz.GtzWeighted (size - 1) rank` as a HYPOTHESIS and conclude a parallel
pair out of a tie.  `Gtz.GtzWeighted` is a WEAK statement, and a tie owns a weak
dominator by definition, so the landed `Gtz.dominating_of_light_atom` returns
nothing a tie does not already have.  That is why the predecessor hypothesis has
never produced anything.

`Gtz.posDef_of_strictly_light_atom` repairs exactly that.  The pullback carries
the deleted atom's own defect `1 - g gᵀ`, which is positive DEFINITE when the
leverage is strictly below one, so weak domination one size down returns STRICT
domination here.  Both hinge obligations therefore hold on the whole strictly
light branch, and their residual is the all-heavy region. -/

/-- **THE HINGE HOLDS ON THE STRICTLY LIGHT BRANCH, AT EVERY RANK.**  A design
with one atom of leverage strictly below one is not a tie, given the predecessor
cell. -/
theorem not_isTie_of_strictly_light_atom {predSize rank : ℕ}
    (design : WeightedDesign (predSize + 1) rank) (hpred : 1 ≤ predSize)
    (hrecursion : GtzWeighted predSize rank) (lightLabel : Fin (predSize + 1))
    (hlight : leverageOf (design.atom lightLabel) < 1) :
    ¬ IsTie design := by
  obtain ⟨selected, hcard, hposDef⟩ :=
    posDef_of_strictly_light_atom design hpred hrecursion lightLabel hlight
  exact fun htie => htie.2 selected hcard hposDef

/-- **THE HINGE, ON THE STRICTLY LIGHT BRANCH.**  The exact shape both general
rank hinge obligations ask for, discharged whenever one atom is strictly light.
The conclusion is reached without ever looking for a parallel pair. -/
theorem hasParallelPair_of_isTie_of_strictly_light_atom {predSize rank : ℕ}
    (design : WeightedDesign (predSize + 1) rank) (hpred : 1 ≤ predSize)
    (hrecursion : GtzWeighted predSize rank) (lightLabel : Fin (predSize + 1))
    (hlight : leverageOf (design.atom lightLabel) < 1)
    (htie : IsTie design) : HasParallelPair design :=
  absurd htie (not_isTie_of_strictly_light_atom design hpred hrecursion lightLabel hlight)

/-- **THE RESIDUAL OF THE HINGE IS THE ALL-HEAVY REGION.**  A tie that survives
the predecessor cell has every atom at leverage at least one.  This is the exact
complement of the branch above, and it names what a general-rank producer must
still cover. -/
theorem forall_one_le_leverage_of_isTie {predSize rank : ℕ}
    (design : WeightedDesign (predSize + 1) rank) (hpred : 1 ≤ predSize)
    (hrecursion : GtzWeighted predSize rank) (htie : IsTie design) :
    ∀ label : Fin (predSize + 1), 1 ≤ leverageOf (design.atom label) := by
  intro label
  by_contra hbelow
  push Not at hbelow
  exact not_isTie_of_strictly_light_atom design hpred hrecursion label hbelow htie

/-- **THE HINGE OBLIGATION'S OWN SHAPE, ON THE STRICTLY LIGHT BRANCH.**  Stated
with the size and rank bounds and the predecessor cell exactly as
`Skeleton.obligationSubThresholdBandHinge` carries them.  The threshold bound on
the size is not used, so the same statement covers
`Skeleton.obligationThresholdCellHingeRankFourAndUp` on its own strictly light
branch.  What is left of both is a tie whose every atom has leverage at least
one. -/
theorem hinge_of_predecessor_on_strictlyLightBranch {size rank : ℕ} (hsize : 2 ≤ size)
    (hpredecessor : GtzWeighted (size - 1) rank) (design : WeightedDesign size rank)
    (hlight : ∃ lightLabel : Fin size, leverageOf (design.atom lightLabel) < 1)
    (htie : IsTie design) : HasParallelPair design := by
  obtain ⟨lightLabel, hlabel⟩ := hlight
  obtain ⟨predSize, hsplit⟩ : ∃ predSize : ℕ, size = predSize + 1 := ⟨size - 1, by omega⟩
  subst hsplit
  rw [Nat.add_sub_cancel] at hpredecessor
  exact hasParallelPair_of_isTie_of_strictly_light_atom design (by omega) hpredecessor
    lightLabel hlabel htie

end Gtz

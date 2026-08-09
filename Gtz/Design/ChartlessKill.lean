/-
# The chartless classes: one line and two meeting lines

The two chartless entries of the rank-three ledger are the SAME pattern-generic
obligation `Gtz.PatternHeavyWeakToStrict` read at

* `Gtz.lineFamilyPattern [[0, 1, 2]]`                 -- one three-point line, and
* `Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4]]`      -- two lines meeting at `0`.

`Gtz.HasLinePattern` pins the matroid EXACTLY: the listed triples are dependent
AND every unlisted distinct triple is independent.  The inequations are as
load-bearing as the equations -- they are what forbids a parallel pair, and they
are what puts every free atom strictly off its line's plane.

## What this file adds

1. **Class simplicity, instantiated.**  Both patterns forbid a parallel pair
   (`decide` against `Gtz.PatternForbidsParallelPair`), so every design of either
   stratum is primitive and the produced transversal axis of
   `Gtz.exists_unitAxis_planeStrictPair_of_not_hasParallelPair` fires on it with no
   genericity hypothesis at all.

2. **A general flat-complement positivity.**  If every atom OUTSIDE a subset is
   orthogonal to a probe, the subset's gap is STRICTLY positive there -- any rank,
   any subset, no heaviness.  Hence the uniform Schur producer's normal-surplus
   hypothesis is free at a coplanar complement.

3. **The mixed Parseval budget.**  Polarised Parseval against a direction the
   normal misses says the weighted heights are orthogonal to every in-plane
   reading.  This is the constraint the rank-two shadow lane cannot see.

4. **THE EXACT PLANE-COVER IDENTITY** and the equivalence it carries.  Writing
   `S` for the weighted normal surplus, `M` for the weighted in-plane mass of the
   atoms OUTSIDE the triple, and `L` for the weighted Lagrange (Gram) excess of
   the three heights against the three readings,

       producer discriminant  =  L  -  S * M

   identically, and therefore STRICT DOMINATION OF A FLAT-COMPLEMENT TRIPLE IS
   EXACTLY `S * M < L` AT EVERY IN-PLANE PROBE.  Both sides are explicit sums of
   products of squares: sign-only, exact, margin-free.

   The reading is sharp.  Weighted Cauchy-Schwarz on the cross term gives
   `L >= 0` and nothing more, so Cauchy-Schwarz alone can NEVER close the plane
   cover; the exact deficit it must beat is `S * M`, the outside atoms' own
   Parseval mass in the plane.  On a line stratum the outside atoms are the line
   itself, and that mass is strictly positive at every in-plane probe
   (simplicity: two line atoms cannot both be orthogonal to the same in-plane
   probe).  So the residual demands a genuinely positive Lagrange excess
   everywhere on the plane -- at least two of the three height-reading pair
   differences must be non-parallel.

5. **The reductions.**  `Gtz.PatternHeavyWeakToStrict` at either pattern follows
   from the Lagrange dominance of one flat-complement triple, stacked on top of
   the landed cap blind spot so the residual is demanded only where the pair-cap
   engine is blind.  The twin gets TWO independent reductions, one per line.

6. **Non-vacuity and non-triviality.**  The residual HOLDS on the tree's shipped
   one-line member `Gtz.oneLineSampleDesign`, and it FAILS at every tie -- so it
   is neither unreachable nor a dressed-up tautology.
-/

import Gtz.Design.LineClassObstructions
import Gtz.Design.PairCapEngine
import Gtz.Design.OneDeterminantReduction
import Gtz.Design.SphereExistence
import Gtz.Design.OneLineShadow
import Gtz.Reduction.TrichotomyLedger
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## Part 1 -- the two chartless strata are simple, and their axis is produced

`Gtz.PatternForbidsParallelPair` is decidable and both entries satisfy it, so
`Gtz.isPrimitiveDesign_of_hasLinePattern` turns the pattern's INEQUATIONS into
primitivity with no analysis.  That is the whole bridge the axis producer needs.
-/

/-- The one-line pattern leaves every pair of labels an independent witness. -/
theorem patternForbidsParallelPair_oneLinePattern :
    PatternForbidsParallelPair (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by decide

/-- The two-meeting-lines pattern leaves every pair of labels an independent
witness. -/
theorem patternForbidsParallelPair_twoMeetingLinesPattern :
    PatternForbidsParallelPair
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by decide

/-- **No design of the one-line stratum carries a parallel pair.** -/
theorem not_hasParallelPair_of_oneLinePattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ¬ HasParallelPair design :=
  (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern patternForbidsParallelPair_oneLinePattern design
      hpattern)

/-- **No design of the two-meeting-lines stratum carries a parallel pair.** -/
theorem not_hasParallelPair_of_twoMeetingLinesPattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    ¬ HasParallelPair design :=
  (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern patternForbidsParallelPair_twoMeetingLinesPattern
      design hpattern)

/-- **The transversal axis is produced on the one-line stratum.**  Pattern in,
plane-strict pair out: no frame, no genericity, no axis guessed. -/
theorem oneLine_exists_unitAxis_planeStrictPair (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∃ strongLabel otherLabel : Fin 6, strongLabel ≠ otherLabel
          ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ unitAxis = 0 → planar ≠ 0 →
              planar ⬝ᵥ planar
                < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                  + (design.atom otherLabel ⬝ᵥ planar) ^ 2 :=
  exists_unitAxis_planeStrictPair_of_not_hasParallelPair design
    (not_hasParallelPair_of_oneLinePattern design hpattern) (labelOne := 0) (labelTwo := 1)
    (labelThree := 2) (labelFour := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- **The transversal axis is produced on the two-meeting-lines stratum.** -/
theorem twoMeetingLines_exists_unitAxis_planeStrictPair (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∃ strongLabel otherLabel : Fin 6, strongLabel ≠ otherLabel
          ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ unitAxis = 0 → planar ≠ 0 →
              planar ⬝ᵥ planar
                < (design.atom strongLabel ⬝ᵥ planar) ^ 2
                  + (design.atom otherLabel ⬝ᵥ planar) ^ 2 :=
  exists_unitAxis_planeStrictPair_of_not_hasParallelPair design
    (not_hasParallelPair_of_twoMeetingLinesPattern design hpattern) (labelOne := 0)
    (labelTwo := 1) (labelThree := 2) (labelFour := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ## Part 2 -- a flat complement makes the gap strictly positive

The design-side twin of the chart-side excess split: if the atoms outside a
subset cannot see a probe, the whole Parseval budget for that probe is carried
inside, and every weight is below one, so the UNWEIGHTED reading strictly
exceeds the norm.  Any rank, any subset, no heaviness, no pattern.
-/

/-- **A probe that only the selected atoms see is strictly over-covered.** -/
theorem dotProduct_subsetSum_sub_one_mulVec_pos_of_outsideFlat {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) (selected : Finset (Fin size))
    {probeVec : Fin rank → ℝ} (hprobeNe : probeVec ≠ 0)
    (houtsideFlat : ∀ label ∈ selectedᶜ, design.atom label ⬝ᵥ probeVec = 0) :
    0 < probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec) := by
  classical
  have houtsideZero : ∑ label ∈ selectedᶜ,
      design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [houtsideFlat label hmem]; ring
  have hparseval := dotProduct_self_eq_sum_weight_mul_sq design probeVec
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
  have hnormPos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hprobeNe
  have hselectedPos : (0 : ℝ) < ∑ label ∈ selected,
      design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
    rw [houtsideZero, add_zero] at hsplit
    rw [hsplit, ← hparseval]
    exact hnormPos
  obtain ⟨witnessLabel, hwitnessMem, hwitnessPos⟩ :=
    Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hselectedPos)
  have hwitnessSqPos : 0 < (design.atom witnessLabel ⬝ᵥ probeVec) ^ 2 := by
    nlinarith [design.weight_pos witnessLabel, hwitnessPos]
  have hwitnessTermPos : 0 < (1 - design.weight witnessLabel)
      * (design.atom witnessLabel ⬝ᵥ probeVec) ^ 2 :=
    mul_pos (by linarith [weight_lt_one design hsize witnessLabel]) hwitnessSqPos
  have hselectedExcess : (1 - design.weight witnessLabel)
        * (design.atom witnessLabel ⬝ᵥ probeVec) ^ 2
      ≤ ∑ label ∈ selected,
          (1 - design.weight label) * (design.atom label ⬝ᵥ probeVec) ^ 2 :=
    Finset.single_le_sum
      (f := fun label => (1 - design.weight label) * (design.atom label ⬝ᵥ probeVec) ^ 2)
      (fun label _ => mul_nonneg (by linarith [weight_lt_one design hsize label]) (sq_nonneg _))
      hwitnessMem
  rw [dotProduct_subsetSum_sub_one_mulVec_eq_excessSplit, houtsideZero]
  linarith

/-- **The uniform Schur producer's surplus hypothesis is free at a flat
complement.** -/
theorem one_lt_sum_sq_reading_of_outsideFlat {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (selected : Finset (Fin size)) {unitNormal : Fin 3 → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (houtsideFlat : ∀ label ∈ selectedᶜ, design.atom label ⬝ᵥ unitNormal = 0) :
    1 < ∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2 := by
  have hnormalNe : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have hpos := dotProduct_subsetSum_sub_one_mulVec_pos_of_outsideFlat design hsize selected
    hnormalNe houtsideFlat
  rw [dominationGap_form, hunit] at hpos
  linarith

/-! ## Part 3 -- the mixed Parseval budget

Polarised Parseval against a direction the normal misses.  On a line stratum
the line atoms drop out, so this says the FREE heights are weighted-orthogonal
to every in-plane reading -- the second of the three split identities, and the
one the rank-two shadow design never sees.
-/

/-- **The heights are weighted-orthogonal to every direction the normal
misses.** -/
theorem sum_weight_mul_normalReading_mul_reading_eq_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (normalVec probeVec : Fin rank → ℝ)
    (horthogonal : normalVec ⬝ᵥ probeVec = 0) :
    ∑ label, design.weight label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) = 0 :=
  (dotProduct_eq_sum_weight_mul_pair design normalVec probeVec).symm.trans horthogonal

/-- The mixed budget restricted to a subset whose complement is flat. -/
theorem sum_selected_weight_mul_normalReading_mul_reading_eq_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) (horthogonal : normalVec ⬝ᵥ probeVec = 0)
    (houtsideFlat : ∀ label ∈ selectedᶜ, design.atom label ⬝ᵥ normalVec = 0) :
    ∑ label ∈ selected, design.weight label
        * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) = 0 := by
  classical
  have houtsideZero : ∑ label ∈ selectedᶜ, design.weight label
      * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)) = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [houtsideFlat label hmem]; ring
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label
      * ((design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec)))
  rw [houtsideZero, add_zero] at hsplit
  rw [hsplit]
  exact sum_weight_mul_normalReading_mul_reading_eq_zero design normalVec probeVec horthogonal

/-! ## Part 4 -- the exact plane-cover identity

Three scalars per in-plane probe.  `S` is the weighted normal surplus of the
triple, `M` the weighted in-plane mass carried by the atoms OUTSIDE it, and `L`
the weighted Lagrange excess -- the Gram determinant of heights against
readings, which is exactly the slack in weighted Cauchy-Schwarz.  The producer's
discriminant is `L - S * M` on the nose.
-/

/-- A three-label subset sums to the three readings. -/
theorem sum_over_tripleSet_eq {size : ℕ} {firstLabel secondLabel thirdLabel : Fin size}
    (hFirstSecond : firstLabel ≠ secondLabel) (hFirstThird : firstLabel ≠ thirdLabel)
    (hSecondThird : secondLabel ≠ thirdLabel) (valueOf : Fin size → ℝ) :
    ∑ label ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)), valueOf label
      = valueOf firstLabel + valueOf secondLabel + valueOf thirdLabel := by
  rw [Finset.sum_insert (by simp [hFirstSecond, hFirstThird]),
    Finset.sum_insert (by simp [hSecondThird]), Finset.sum_singleton, add_assoc]

/-- The weighted Lagrange identity on three terms: the Cauchy-Schwarz slack is a
sum of weighted squared two-by-two minors. -/
theorem weightedLagrange_three (weightFirst weightSecond weightThird
    heightFirst heightSecond heightThird readingFirst readingSecond readingThird : ℝ) :
    (weightFirst * heightFirst ^ 2 + weightSecond * heightSecond ^ 2
        + weightThird * heightThird ^ 2)
      * (weightFirst * readingFirst ^ 2 + weightSecond * readingSecond ^ 2
        + weightThird * readingThird ^ 2)
      - (weightFirst * heightFirst * readingFirst + weightSecond * heightSecond * readingSecond
        + weightThird * heightThird * readingThird) ^ 2
      = weightFirst * weightSecond
            * (heightFirst * readingSecond - heightSecond * readingFirst) ^ 2
        + weightFirst * weightThird
            * (heightFirst * readingThird - heightThird * readingFirst) ^ 2
        + weightSecond * weightThird
            * (heightSecond * readingThird - heightThird * readingSecond) ^ 2 := by
  ring

/-- The scalar heart of the plane-cover identity: the two Parseval budgets
turn the producer's discriminant into the Lagrange excess minus the drag. -/
theorem planeCoverDiscriminant_scalar_identity
    (weightFirst weightSecond weightThird heightFirst heightSecond heightThird
      readingFirst readingSecond readingThird outsideMass : ℝ)
    (hnormalBudget : weightFirst * heightFirst ^ 2 + weightSecond * heightSecond ^ 2
      + weightThird * heightThird ^ 2 = 1)
    (hmixedBudget : weightFirst * (heightFirst * readingFirst)
      + weightSecond * (heightSecond * readingSecond)
      + weightThird * (heightThird * readingThird) = 0) :
    (heightFirst ^ 2 + heightSecond ^ 2 + heightThird ^ 2 - 1)
        * (readingFirst ^ 2 + readingSecond ^ 2 + readingThird ^ 2
          - (weightFirst * readingFirst ^ 2 + weightSecond * readingSecond ^ 2
            + weightThird * readingThird ^ 2 + outsideMass))
      - (readingFirst * heightFirst + readingSecond * heightSecond
        + readingThird * heightThird) ^ 2
      = ((1 - weightFirst) * (1 - weightSecond)
            * (heightFirst * readingSecond - heightSecond * readingFirst) ^ 2
          + (1 - weightFirst) * (1 - weightThird)
            * (heightFirst * readingThird - heightThird * readingFirst) ^ 2
          + (1 - weightSecond) * (1 - weightThird)
            * (heightSecond * readingThird - heightThird * readingSecond) ^ 2)
        - ((1 - weightFirst) * heightFirst ^ 2 + (1 - weightSecond) * heightSecond ^ 2
            + (1 - weightThird) * heightThird ^ 2) * outsideMass := by
  linear_combination
    (readingFirst ^ 2 + readingSecond ^ 2 + readingThird ^ 2
        - (weightFirst * readingFirst ^ 2 + weightSecond * readingSecond ^ 2
          + weightThird * readingThird ^ 2) - outsideMass) * hnormalBudget
      + (weightFirst * (heightFirst * readingFirst)
          + weightSecond * (heightSecond * readingSecond)
          + weightThird * (heightThird * readingThird)
        - 2 * (readingFirst * heightFirst + readingSecond * heightSecond
          + readingThird * heightThird)) * hmixedBudget

/-- The weighted normal surplus of a three-label subset. -/
noncomputable def tripleNormalSurplus {size : ℕ} (design : WeightedDesign size 3)
    (freeFirst freeSecond freeThird : Fin size) (unitNormal : Fin 3 → ℝ) : ℝ :=
  (1 - design.weight freeFirst) * (design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
    + (1 - design.weight freeSecond) * (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2
    + (1 - design.weight freeThird) * (design.atom freeThird ⬝ᵥ unitNormal) ^ 2

/-- The weighted in-plane mass carried by the atoms OUTSIDE the subset -- the
drag the Lagrange excess has to beat. -/
noncomputable def outsideProbeMass {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (probeVec : Fin 3 → ℝ) : ℝ :=
  ∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2

/-- The weighted Lagrange excess of the three heights against the three
readings: the slack in weighted Cauchy-Schwarz, as a sum of squared minors. -/
noncomputable def tripleLagrangeExcess {size : ℕ} (design : WeightedDesign size 3)
    (freeFirst freeSecond freeThird : Fin size) (unitNormal probeVec : Fin 3 → ℝ) : ℝ :=
  (1 - design.weight freeFirst) * (1 - design.weight freeSecond)
      * ((design.atom freeFirst ⬝ᵥ unitNormal) * (design.atom freeSecond ⬝ᵥ probeVec)
          - (design.atom freeSecond ⬝ᵥ unitNormal) * (design.atom freeFirst ⬝ᵥ probeVec)) ^ 2
    + (1 - design.weight freeFirst) * (1 - design.weight freeThird)
      * ((design.atom freeFirst ⬝ᵥ unitNormal) * (design.atom freeThird ⬝ᵥ probeVec)
          - (design.atom freeThird ⬝ᵥ unitNormal) * (design.atom freeFirst ⬝ᵥ probeVec)) ^ 2
    + (1 - design.weight freeSecond) * (1 - design.weight freeThird)
      * ((design.atom freeSecond ⬝ᵥ unitNormal) * (design.atom freeThird ⬝ᵥ probeVec)
          - (design.atom freeThird ⬝ᵥ unitNormal) * (design.atom freeSecond ⬝ᵥ probeVec)) ^ 2

/-- The drag is never negative. -/
theorem outsideProbeMass_nonneg {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (probeVec : Fin 3 → ℝ) :
    0 ≤ outsideProbeMass design selected probeVec :=
  Finset.sum_nonneg fun label _ => mul_nonneg (design.weight_pos label).le (sq_nonneg _)

/-- **Weighted Cauchy-Schwarz, read backwards.**  The Lagrange excess is the
Cauchy-Schwarz slack, hence never negative -- and that is ALL Cauchy-Schwarz
gives.  The plane cover needs it strictly above `S * M`, so Cauchy-Schwarz alone
can never close the class. -/
theorem tripleLagrangeExcess_nonneg {size : ℕ} (design : WeightedDesign size 3)
    (hsize : 2 ≤ size) (freeFirst freeSecond freeThird : Fin size)
    (unitNormal probeVec : Fin 3 → ℝ) :
    0 ≤ tripleLagrangeExcess design freeFirst freeSecond freeThird unitNormal probeVec := by
  have hfirst : 0 ≤ 1 - design.weight freeFirst := by
    linarith [weight_lt_one design hsize freeFirst]
  have hsecond : 0 ≤ 1 - design.weight freeSecond := by
    linarith [weight_lt_one design hsize freeSecond]
  have hthird : 0 ≤ 1 - design.weight freeThird := by
    linarith [weight_lt_one design hsize freeThird]
  rw [tripleLagrangeExcess]
  have hone := mul_nonneg (mul_nonneg hfirst hsecond)
    (sq_nonneg ((design.atom freeFirst ⬝ᵥ unitNormal) * (design.atom freeSecond ⬝ᵥ probeVec)
      - (design.atom freeSecond ⬝ᵥ unitNormal) * (design.atom freeFirst ⬝ᵥ probeVec)))
  have htwo := mul_nonneg (mul_nonneg hfirst hthird)
    (sq_nonneg ((design.atom freeFirst ⬝ᵥ unitNormal) * (design.atom freeThird ⬝ᵥ probeVec)
      - (design.atom freeThird ⬝ᵥ unitNormal) * (design.atom freeFirst ⬝ᵥ probeVec)))
  have hthree := mul_nonneg (mul_nonneg hsecond hthird)
    (sq_nonneg ((design.atom freeSecond ⬝ᵥ unitNormal) * (design.atom freeThird ⬝ᵥ probeVec)
      - (design.atom freeThird ⬝ᵥ unitNormal) * (design.atom freeSecond ⬝ᵥ probeVec)))
  linarith

/-- **The Lagrange excess dies where the readings track the heights.**  A
concrete failure family for the plane cover at a flat-complement triple: at any
in-plane probe whose three free readings are one common multiple of the three
free heights, the Cauchy-Schwarz slack is exactly zero. -/
theorem tripleLagrangeExcess_eq_zero_of_readings_proportional {size : ℕ}
    (design : WeightedDesign size 3) (freeFirst freeSecond freeThird : Fin size)
    (unitNormal probeVec : Fin 3 → ℝ) (ratio : ℝ)
    (hfirst : design.atom freeFirst ⬝ᵥ probeVec
      = ratio * (design.atom freeFirst ⬝ᵥ unitNormal))
    (hsecond : design.atom freeSecond ⬝ᵥ probeVec
      = ratio * (design.atom freeSecond ⬝ᵥ unitNormal))
    (hthird : design.atom freeThird ⬝ᵥ probeVec
      = ratio * (design.atom freeThird ⬝ᵥ unitNormal)) :
    tripleLagrangeExcess design freeFirst freeSecond freeThird unitNormal probeVec = 0 := by
  rw [tripleLagrangeExcess, hfirst, hsecond, hthird]
  ring

/-- **THE EXACT PLANE-COVER IDENTITY.**  With the complement flat against the
unit normal and the probe in the plane, the uniform Schur producer's
discriminant equals the weighted Lagrange excess minus the normal surplus times
the outside drag.  No hypothesis on heaviness, primitivity or pattern. -/
theorem planeCoverDiscriminant_eq_lagrangeExcess_sub_outsideDrag {size : ℕ}
    (design : WeightedDesign size 3) {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (unitNormal probeVec : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hprobeFlat : unitNormal ⬝ᵥ probeVec = 0)
    (houtsideFlat : ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
      design.atom label ⬝ᵥ unitNormal = 0) :
    ((∑ selectedLabel ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
          (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
        * ((∑ selectedLabel ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec)
      - (∑ selectedLabel ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
          (design.atom selectedLabel ⬝ᵥ probeVec)
            * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
      = tripleLagrangeExcess design freeFirst freeSecond freeThird unitNormal probeVec
        - tripleNormalSurplus design freeFirst freeSecond freeThird unitNormal
          * outsideProbeMass design ({freeFirst, freeSecond, freeThird} : Finset (Fin size))
            probeVec := by
  classical
  have hnormalBudget : (∑ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
      design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2) = 1 := by
    have houtsideZero : ∑ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
        design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2 = 0 :=
      Finset.sum_eq_zero fun label hmem => by rw [houtsideFlat label hmem]; ring
    have hsplit := Finset.sum_add_sum_compl
      ({freeFirst, freeSecond, freeThird} : Finset (Fin size))
      (fun label => design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2)
    rw [houtsideZero, add_zero] at hsplit
    rw [hsplit, ← dotProduct_self_eq_sum_weight_mul_sq design unitNormal]
    exact hunit
  have hmixedBudget : (∑ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
      design.weight label
        * ((design.atom label ⬝ᵥ unitNormal) * (design.atom label ⬝ᵥ probeVec))) = 0 :=
    sum_selected_weight_mul_normalReading_mul_reading_eq_zero design _ unitNormal probeVec
      hprobeFlat houtsideFlat
  have hprobeSplit : probeVec ⬝ᵥ probeVec
      = (∑ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
          design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)
        + outsideProbeMass design ({freeFirst, freeSecond, freeThird} : Finset (Fin size))
          probeVec := by
    rw [outsideProbeMass, dotProduct_self_eq_sum_weight_mul_sq design probeVec]
    exact (Finset.sum_add_sum_compl ({freeFirst, freeSecond, freeThird} : Finset (Fin size))
      (fun label => design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)).symm
  rw [sum_over_tripleSet_eq hFirstSecond hFirstThird hSecondThird] at hnormalBudget hmixedBudget hprobeSplit
  rw [sum_over_tripleSet_eq hFirstSecond hFirstThird hSecondThird
      (fun label => (design.atom label ⬝ᵥ unitNormal) ^ 2),
    sum_over_tripleSet_eq hFirstSecond hFirstThird hSecondThird
      (fun label => (design.atom label ⬝ᵥ probeVec) ^ 2),
    sum_over_tripleSet_eq hFirstSecond hFirstThird hSecondThird
      (fun label => (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ unitNormal)),
    hprobeSplit, tripleLagrangeExcess, tripleNormalSurplus]
  exact planeCoverDiscriminant_scalar_identity (design.weight freeFirst)
    (design.weight freeSecond) (design.weight freeThird)
    (design.atom freeFirst ⬝ᵥ unitNormal) (design.atom freeSecond ⬝ᵥ unitNormal)
    (design.atom freeThird ⬝ᵥ unitNormal) (design.atom freeFirst ⬝ᵥ probeVec)
    (design.atom freeSecond ⬝ᵥ probeVec) (design.atom freeThird ⬝ᵥ probeVec)
    (outsideProbeMass design ({freeFirst, freeSecond, freeThird} : Finset (Fin size)) probeVec)
    hnormalBudget hmixedBudget

/-! ## Part 5 -- strict domination of a flat-complement triple, exactly

The identity turns the producer into a scalar sign test, and the landed converse
`Gtz.normalSurplus_planeCover_of_posDef` turns the test back into the producer.
So this is an EQUIVALENCE, not a weakening.
-/

/-- **The Lagrange dominance of a triple against a unit normal.** -/
def IsLagrangeDominatingTriple {size : ℕ} (design : WeightedDesign size 3)
    (freeFirst freeSecond freeThird : Fin size) (unitNormal : Fin 3 → ℝ) : Prop :=
  ∀ probeVec : Fin 3 → ℝ, unitNormal ⬝ᵥ probeVec = 0 → probeVec ≠ 0 →
    tripleNormalSurplus design freeFirst freeSecond freeThird unitNormal
        * outsideProbeMass design ({freeFirst, freeSecond, freeThird} : Finset (Fin size))
          probeVec
      < tripleLagrangeExcess design freeFirst freeSecond freeThird unitNormal probeVec

/-- **STRICT DOMINATION OF A FLAT-COMPLEMENT TRIPLE IS EXACTLY LAGRANGE
DOMINANCE.**  Sign-only, exact, margin-free: both sides of the test are explicit
sums of products of squares. -/
theorem posDef_tripleSet_iff_isLagrangeDominatingTriple {size : ℕ}
    (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (houtsideFlat : ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
      design.atom label ⬝ᵥ unitNormal = 0) :
    (subsetSum design ({freeFirst, freeSecond, freeThird} : Finset (Fin size)) - 1).PosDef
      ↔ IsLagrangeDominatingTriple design freeFirst freeSecond freeThird unitNormal := by
  constructor
  · intro hposDef probeVec hprobeFlat hprobeNe
    have hcover := (normalSurplus_planeCover_of_posDef design _ unitNormal hunit hposDef).2
      probeVec (by rw [dotProduct_comm]; exact hprobeFlat) hprobeNe
    have hidentity := planeCoverDiscriminant_eq_lagrangeExcess_sub_outsideDrag design
      hFirstSecond hFirstThird hSecondThird unitNormal probeVec hunit hprobeFlat houtsideFlat
    linarith
  · intro hdominates
    refine posDef_of_normalSurplus_planeCover design _ unitNormal hunit
      (one_lt_sum_sq_reading_of_outsideFlat design hsize _ hunit houtsideFlat)
      fun probeVec hprobeFlat hprobeNe => ?_
    have hprobeFlatSym : unitNormal ⬝ᵥ probeVec = 0 := by
      rw [dotProduct_comm]; exact hprobeFlat
    have hidentity := planeCoverDiscriminant_eq_lagrangeExcess_sub_outsideDrag design
      hFirstSecond hFirstThird hSecondThird unitNormal probeVec hunit hprobeFlatSym houtsideFlat
    linarith [hdominates probeVec hprobeFlatSym hprobeNe]

/-- The strict dominator packaged with its cardinality. -/
theorem exists_posDef_cardThree_of_isLagrangeDominatingTriple {size : ℕ}
    (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (houtsideFlat : ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
      design.atom label ⬝ᵥ unitNormal = 0)
    (hdominates : IsLagrangeDominatingTriple design freeFirst freeSecond freeThird unitNormal) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef :=
  ⟨{freeFirst, freeSecond, freeThird},
    card_labelTriple_eq_three hFirstSecond hFirstThird hSecondThird,
    (posDef_tripleSet_iff_isLagrangeDominatingTriple design hsize hFirstSecond hFirstThird
      hSecondThird unitNormal hunit houtsideFlat).mpr hdominates⟩

/-- **The residual has real content: it fails at every tie.**  So no Lagrange
dominance statement on these strata is a dressed-up tautology. -/
theorem not_isLagrangeDominatingTriple_of_isTie {size : ℕ}
    (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (houtsideFlat : ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
      design.atom label ⬝ᵥ unitNormal = 0) (htie : IsTie design) :
    ¬ IsLagrangeDominatingTriple design freeFirst freeSecond freeThird unitNormal := by
  intro hdominates
  exact htie.2 _ (card_labelTriple_eq_three hFirstSecond hFirstThird hSecondThird)
    ((posDef_tripleSet_iff_isLagrangeDominatingTriple design hsize hFirstSecond hFirstThird
      hSecondThird unitNormal hunit houtsideFlat).mpr hdominates)

/-! ## Part 6 -- the drag is strictly positive on a line stratum

`M(p)` vanishes only when EVERY outside atom misses the probe.  On a line
stratum the outside atoms are the line, and two line atoms orthogonal to the
same in-plane probe would be parallel -- the pattern forbids it.  So the
residual really does demand a positive Lagrange excess at every in-plane probe.
-/

/-- A nonzero vector orthogonal to another nonzero vector is not a multiple of
it. -/
theorem not_parallel_of_orthogonal_of_ne_zero {rank : ℕ} {firstVec secondVec : Fin rank → ℝ}
    (hfirstNe : firstVec ≠ 0) (hsecondNe : secondVec ≠ 0)
    (horthogonal : firstVec ⬝ᵥ secondVec = 0) : ∀ ratio : ℝ, secondVec ≠ ratio • firstVec := by
  intro ratio hparallel
  have hscaled : ratio * (firstVec ⬝ᵥ firstVec) = 0 := by
    have hcopy := horthogonal
    rw [hparallel, dotProduct_smul, smul_eq_mul] at hcopy
    exact hcopy
  have hnormPos : 0 < firstVec ⬝ᵥ firstVec := dotProduct_self_pos hfirstNe
  exact hsecondNe (by rw [hparallel, (mul_eq_zero.mp hscaled).resolve_right hnormPos.ne',
    zero_smul])

/-- **Two vectors orthogonal to the same independent pair of normals are
parallel**: the orthogonal complement of a two-dimensional span in three space
is a line. -/
theorem exists_smul_of_orthogonal_to_independent_normals
    {firstNormal secondNormal firstVec secondVec : Fin 3 → ℝ}
    (hfirstNormalNe : firstNormal ≠ 0)
    (hnotParallel : ∀ ratio : ℝ, secondNormal ≠ ratio • firstNormal)
    (hfirstVecNe : firstVec ≠ 0)
    (hfirstAgainstFirst : firstVec ⬝ᵥ firstNormal = 0)
    (hfirstAgainstSecond : firstVec ⬝ᵥ secondNormal = 0)
    (hsecondAgainstFirst : secondVec ⬝ᵥ firstNormal = 0)
    (hsecondAgainstSecond : secondVec ⬝ᵥ secondNormal = 0) :
    ∃ scale : ℝ, secondVec = scale • firstVec := by
  have hcrossNe : bracketNormal firstNormal secondNormal ≠ 0 :=
    bracketNormal_ne_zero_of_not_parallel firstNormal secondNormal hfirstNormalNe hnotParallel
  have hfirstCross : bracketNormal (bracketNormal firstNormal secondNormal) firstVec = 0 := by
    rw [bracketNormal_bracketNormal, dotProduct_comm firstNormal firstVec,
      dotProduct_comm secondNormal firstVec, hfirstAgainstFirst, hfirstAgainstSecond,
      zero_smul, zero_smul, sub_zero]
  have hsecondCross : bracketNormal (bracketNormal firstNormal secondNormal) secondVec = 0 := by
    rw [bracketNormal_bracketNormal, dotProduct_comm firstNormal secondVec,
      dotProduct_comm secondNormal secondVec, hsecondAgainstFirst, hsecondAgainstSecond,
      zero_smul, zero_smul, sub_zero]
  exact exists_smul_of_both_smul_of_ne_zero hfirstVecNe
    (eq_smul_of_bracketNormal_eq_zero (bracketNormal firstNormal secondNormal) firstVec
      hcrossNe hfirstCross)
    (eq_smul_of_bracketNormal_eq_zero (bracketNormal firstNormal secondNormal) secondVec
      hcrossNe hsecondCross)

/-- **Two atoms flat against the normal and blind to an in-plane probe are
parallel.** -/
theorem hasParallelPair_of_two_flat_blind {size : ℕ} (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hfirstNe : design.atom firstLabel ≠ 0)
    (normalVec probeVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (hprobeFlat : normalVec ⬝ᵥ probeVec = 0) (hprobeNe : probeVec ≠ 0)
    (hfirstFlat : design.atom firstLabel ⬝ᵥ normalVec = 0)
    (hsecondFlat : design.atom secondLabel ⬝ᵥ normalVec = 0)
    (hfirstBlind : design.atom firstLabel ⬝ᵥ probeVec = 0)
    (hsecondBlind : design.atom secondLabel ⬝ᵥ probeVec = 0) :
    HasParallelPair design := by
  obtain ⟨scale, hscale⟩ := exists_smul_of_orthogonal_to_independent_normals hnormalNe
    (not_parallel_of_orthogonal_of_ne_zero hnormalNe hprobeNe hprobeFlat) hfirstNe
    hfirstFlat hfirstBlind hsecondFlat hsecondBlind
  exact ⟨firstLabel, secondLabel, scale, hdistinct, hscale⟩

/-- **The drag is strictly positive whenever two outside atoms are flat.**  They
cannot both be blind to the same in-plane probe without being parallel, and the
pattern forbids that.  Generic in the subset, the pattern and the line. -/
theorem outsideProbeMass_pos_of_flat_outside_pair {size : ℕ} (design : WeightedDesign size 3)
    (hsimple : ¬ HasParallelPair design) (selected : Finset (Fin size))
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hfirstOutside : firstLabel ∈ selectedᶜ) (hsecondOutside : secondLabel ∈ selectedᶜ)
    (hfirstAtomNe : design.atom firstLabel ≠ 0)
    (normalVec probeVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0) (hprobeNe : probeVec ≠ 0)
    (hprobeFlat : normalVec ⬝ᵥ probeVec = 0)
    (hfirstFlat : design.atom firstLabel ⬝ᵥ normalVec = 0)
    (hsecondFlat : design.atom secondLabel ⬝ᵥ normalVec = 0) :
    0 < outsideProbeMass design selected probeVec := by
  classical
  have hnonneg : ∀ label ∈ selectedᶜ,
      0 ≤ design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 :=
    fun label _ => mul_nonneg (design.weight_pos label).le (sq_nonneg _)
  have hseen : design.atom firstLabel ⬝ᵥ probeVec ≠ 0
      ∨ design.atom secondLabel ⬝ᵥ probeVec ≠ 0 := by
    by_contra hblind
    push Not at hblind
    exact hsimple (hasParallelPair_of_two_flat_blind design hdistinct hfirstAtomNe normalVec
      probeVec hnormalNe hprobeFlat hprobeNe hfirstFlat hsecondFlat hblind.1 hblind.2)
  rw [outsideProbeMass]
  rcases hseen with hfirstSeen | hsecondSeen
  · exact lt_of_lt_of_le (mul_pos (design.weight_pos firstLabel) (by positivity))
      (Finset.single_le_sum hnonneg hfirstOutside)
  · exact lt_of_lt_of_le (mul_pos (design.weight_pos secondLabel) (by positivity))
      (Finset.single_le_sum hnonneg hsecondOutside)

/-- **The drag is strictly positive on the one-line stratum.** -/
theorem oneLine_outsideProbeMass_pos (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (normalVec probeVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0) (hprobeNe : probeVec ≠ 0)
    (hprobeFlat : normalVec ⬝ᵥ probeVec = 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    0 < outsideProbeMass design ({(3 : Fin 6), 4, 5} : Finset (Fin 6)) probeVec :=
  outsideProbeMass_pos_of_flat_outside_pair design
    (not_hasParallelPair_of_oneLinePattern design hpattern) _ (by decide : (0 : Fin 6) ≠ 1)
    (by decide) (by decide) (oneLine_atoms_ne_zero design hpattern 0) normalVec probeVec
    hnormalNe hprobeNe hprobeFlat (horthogonal 0 (by decide)) (horthogonal 1 (by decide))

/-- **The drag is strictly positive on the twin at its first line.** -/
theorem twoMeetingLines_outsideProbeMass_pos_firstLine (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec probeVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0) (hprobeNe : probeVec ≠ 0)
    (hprobeFlat : normalVec ⬝ᵥ probeVec = 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    0 < outsideProbeMass design ({(3 : Fin 6), 4, 5} : Finset (Fin 6)) probeVec :=
  outsideProbeMass_pos_of_flat_outside_pair design
    (not_hasParallelPair_of_twoMeetingLinesPattern design hpattern) _
    (by decide : (0 : Fin 6) ≠ 1) (by decide) (by decide)
    (twoMeetingLines_atoms_ne_zero design hpattern 0) normalVec probeVec hnormalNe hprobeNe
    hprobeFlat (horthogonal 0 (by decide)) (horthogonal 1 (by decide))

/-- **The drag is strictly positive on the twin at its second line.** -/
theorem twoMeetingLines_outsideProbeMass_pos_secondLine (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec probeVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0) (hprobeNe : probeVec ≠ 0)
    (hprobeFlat : normalVec ⬝ᵥ probeVec = 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0) :
    0 < outsideProbeMass design ({(1 : Fin 6), 2, 5} : Finset (Fin 6)) probeVec :=
  outsideProbeMass_pos_of_flat_outside_pair design
    (not_hasParallelPair_of_twoMeetingLinesPattern design hpattern) _
    (by decide : (0 : Fin 6) ≠ 3) (by decide) (by decide)
    (twoMeetingLines_atoms_ne_zero design hpattern 0) normalVec probeVec hnormalNe hprobeNe
    hprobeFlat (horthogonal 0 (by decide)) (horthogonal 3 (by decide))

/-- **The Lagrange excess must be strictly positive everywhere on the plane.**
An immediate but load-bearing consequence: on the one-line stratum the residual
can never be met by a probe at which all three height-reading minors vanish. -/
theorem oneLine_lagrangeExcess_pos_of_isLagrangeDominatingTriple (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hdominates : IsLagrangeDominatingTriple design 3 4 5 unitNormal)
    (probeVec : Fin 3 → ℝ) (hprobeFlat : unitNormal ⬝ᵥ probeVec = 0) (hprobeNe : probeVec ≠ 0) :
    0 < tripleLagrangeExcess design 3 4 5 unitNormal probeVec := by
  have hnormalNe : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have hdrag := oneLine_outsideProbeMass_pos design hpattern unitNormal probeVec hnormalNe
    hprobeNe hprobeFlat horthogonal
  have hsurplus : 0 < tripleNormalSurplus design 3 4 5 unitNormal := by
    have hflat : ∀ label ∈ ({(3 : Fin 6), 4, 5} : Finset (Fin 6))ᶜ,
        design.atom label ⬝ᵥ unitNormal = 0 := by
      intro label hmem
      exact horthogonal label (by rw [show ({(3 : Fin 6), 4, 5} : Finset (Fin 6))ᶜ
        = {0, 1, 2} from by decide] at hmem; exact hmem)
    have hone := one_lt_sum_sq_reading_of_outsideFlat design (by norm_num)
      ({(3 : Fin 6), 4, 5} : Finset (Fin 6)) hunit hflat
    have hbudget : (∑ label ∈ ({(3 : Fin 6), 4, 5} : Finset (Fin 6)),
        design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2) = 1 := by
      have houtsideZero : ∑ label ∈ ({(3 : Fin 6), 4, 5} : Finset (Fin 6))ᶜ,
          design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2 = 0 :=
        Finset.sum_eq_zero fun label hmem => by rw [hflat label hmem]; ring
      have hsplit := Finset.sum_add_sum_compl ({(3 : Fin 6), 4, 5} : Finset (Fin 6))
        (fun label => design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2)
      rw [houtsideZero, add_zero] at hsplit
      rw [hsplit, ← dotProduct_self_eq_sum_weight_mul_sq design unitNormal]
      exact hunit
    rw [sum_over_tripleSet_eq (by decide : (3 : Fin 6) ≠ 4) (by decide : (3 : Fin 6) ≠ 5)
      (by decide : (4 : Fin 6) ≠ 5)] at hone hbudget
    rw [tripleNormalSurplus]
    linarith
  have hstrict := hdominates probeVec hprobeFlat hprobeNe
  nlinarith [hsurplus, hdrag, hstrict]

/-! ## Part 6b -- the residual as a comparison of two sums of squares

Every minor in the Lagrange excess is the reading of ONE explicit in-plane
vector, so the residual compares two sums of squares of linear forms in the
probe: three pair-difference forms against the outside atoms' own readings.
That is the sharpest shape the class has -- a two-by-two Loewner comparison
inside the line plane, with both sides written out.
-/

/-- The in-plane pair-difference direction of two labels against a normal:
`h_i * a_j - h_j * a_i` with `h` the height against the normal. -/
noncomputable def heightPairDifference {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) (unitNormal : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (design.atom firstLabel ⬝ᵥ unitNormal) • design.atom secondLabel
    - (design.atom secondLabel ⬝ᵥ unitNormal) • design.atom firstLabel

/-- Its reading against any probe is the two-by-two minor. -/
theorem heightPairDifference_dotProduct {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) (unitNormal probeVec : Fin 3 → ℝ) :
    heightPairDifference design firstLabel secondLabel unitNormal ⬝ᵥ probeVec
      = (design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probeVec)
        - (design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probeVec) := by
  rw [heightPairDifference, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]

/-- **The pair difference lies in the plane.** -/
theorem heightPairDifference_dotProduct_unitNormal_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) (firstLabel secondLabel : Fin size)
    (unitNormal : Fin 3 → ℝ) :
    heightPairDifference design firstLabel secondLabel unitNormal ⬝ᵥ unitNormal = 0 := by
  rw [heightPairDifference_dotProduct]; ring

/-- **The pair difference is nonzero on a simple design.**  A vanishing pair
difference at a label of nonzero height exhibits a parallel pair outright. -/
theorem heightPairDifference_ne_zero_of_not_hasParallelPair {size : ℕ}
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (unitNormal : Fin 3 → ℝ)
    (hfirstHeightNe : design.atom firstLabel ⬝ᵥ unitNormal ≠ 0) :
    heightPairDifference design firstLabel secondLabel unitNormal ≠ 0 := by
  intro hzero
  have hbalanced : (design.atom firstLabel ⬝ᵥ unitNormal) • design.atom secondLabel
      = (design.atom secondLabel ⬝ᵥ unitNormal) • design.atom firstLabel :=
    sub_eq_zero.mp (by rw [← heightPairDifference]; exact hzero)
  refine hsimple ⟨firstLabel, secondLabel,
    (design.atom secondLabel ⬝ᵥ unitNormal) / (design.atom firstLabel ⬝ᵥ unitNormal),
    hdistinct, ?_⟩
  rw [div_eq_inv_mul, ← smul_smul, ← hbalanced, smul_smul,
    inv_mul_cancel₀ hfirstHeightNe, one_smul]

/-- **The Lagrange excess is a sum of three squared in-plane readings.** -/
theorem tripleLagrangeExcess_eq_sum_pairDifference_sq {size : ℕ}
    (design : WeightedDesign size 3) (freeFirst freeSecond freeThird : Fin size)
    (unitNormal probeVec : Fin 3 → ℝ) :
    tripleLagrangeExcess design freeFirst freeSecond freeThird unitNormal probeVec
      = (1 - design.weight freeFirst) * (1 - design.weight freeSecond)
            * (heightPairDifference design freeFirst freeSecond unitNormal ⬝ᵥ probeVec) ^ 2
        + (1 - design.weight freeFirst) * (1 - design.weight freeThird)
            * (heightPairDifference design freeFirst freeThird unitNormal ⬝ᵥ probeVec) ^ 2
        + (1 - design.weight freeSecond) * (1 - design.weight freeThird)
            * (heightPairDifference design freeSecond freeThird unitNormal ⬝ᵥ probeVec) ^ 2 := by
  rw [tripleLagrangeExcess, heightPairDifference_dotProduct, heightPairDifference_dotProduct,
    heightPairDifference_dotProduct]

/-- **All three pair differences of the one-line free triple are nonzero
in-plane vectors.**  Free heights never vanish on this stratum, so the
residual's right-hand side is a genuine three-term sum of squares. -/
theorem oneLine_heightPairDifference_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    {firstLabel secondLabel : Fin 6} (hdistinct : firstLabel ≠ secondLabel)
    (hfirstFree : firstLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    heightPairDifference design firstLabel secondLabel normalVec ≠ 0 :=
  heightPairDifference_ne_zero_of_not_hasParallelPair design
    (not_hasParallelPair_of_oneLinePattern design hpattern) hdistinct normalVec
    (oneLine_freeAtom_normal_dot_ne_zero design hpattern normalVec hnormalNe horthogonal
      firstLabel hfirstFree)

/-! ## Part 6bb -- a conservation law among the pair-difference readings, and
the named branch where the canonical triple cannot be the answer

The two Parseval budgets pin each free reading to the other two pair-difference
readings.  So a probe at which all three minors vanish is invisible to ALL
THREE free atoms, and there the free triple does not even weakly dominate.  That
is a branch the canonical anatomy provably cannot close, stated exactly.
-/

/-- The normal budget of a subset with a flat complement, as a sum. -/
theorem sum_selected_weight_mul_sq_reading_eq_one_of_outsideFlat {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (houtsideFlat : ∀ label ∈ selectedᶜ, design.atom label ⬝ᵥ unitNormal = 0) :
    ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2 = 1 := by
  classical
  have houtsideZero : ∑ label ∈ selectedᶜ,
      design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by rw [houtsideFlat label hmem]; ring
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ unitNormal) ^ 2)
  rw [houtsideZero, add_zero] at hsplit
  rw [hsplit, ← dotProduct_self_eq_sum_weight_mul_sq design unitNormal]
  exact hunit

/-- **The drag is the probe's norm minus the triple's own weighted mass**, so
the outside atoms' internal geometry drops out of the residual entirely. -/
theorem outsideProbeMass_eq_normSq_sub_selectedMass {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (probeVec : Fin 3 → ℝ) :
    outsideProbeMass design selected probeVec
      = probeVec ⬝ᵥ probeVec
        - ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2 := by
  classical
  rw [outsideProbeMass, dotProduct_self_eq_sum_weight_mul_sq design probeVec,
    ← Finset.sum_add_sum_compl selected
      (fun label => design.weight label * (design.atom label ⬝ᵥ probeVec) ^ 2)]
  ring

/-- **A probe no selected atom sees kills weak domination.**  Any rank, any
subset: the gap reads exactly minus the probe's norm there. -/
theorem not_dominates_of_blind_probe {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {probeVec : Fin rank → ℝ} (hprobeNe : probeVec ≠ 0)
    (hblind : ∀ label ∈ selected, design.atom label ⬝ᵥ probeVec = 0) :
    ¬ Dominates design selected := by
  intro hdominates
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probeVec
  rw [star_trivial, dominationGap_form,
    Finset.sum_eq_zero (fun label hmem => by rw [hblind label hmem]; ring)] at hform
  linarith [dotProduct_self_pos hprobeNe]

/-- **The scalar conservation law.**  With both Parseval budgets in hand, three
vanishing minors force all three readings to vanish. -/
theorem readings_eq_zero_of_minors_eq_zero
    (weightFirst weightSecond weightThird heightFirst heightSecond heightThird
      readingFirst readingSecond readingThird : ℝ)
    (hnormalBudget : weightFirst * heightFirst ^ 2 + weightSecond * heightSecond ^ 2
      + weightThird * heightThird ^ 2 = 1)
    (hmixedBudget : weightFirst * (heightFirst * readingFirst)
      + weightSecond * (heightSecond * readingSecond)
      + weightThird * (heightThird * readingThird) = 0)
    (hminorFirstSecond : heightFirst * readingSecond - heightSecond * readingFirst = 0)
    (hminorFirstThird : heightFirst * readingThird - heightThird * readingFirst = 0)
    (hminorSecondThird : heightSecond * readingThird - heightThird * readingSecond = 0) :
    readingFirst = 0 ∧ readingSecond = 0 ∧ readingThird = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination heightFirst * hmixedBudget - readingFirst * hnormalBudget
      - weightSecond * heightSecond * hminorFirstSecond
      - weightThird * heightThird * hminorFirstThird
  · linear_combination heightSecond * hmixedBudget - readingSecond * hnormalBudget
      + weightFirst * heightFirst * hminorFirstSecond
      - weightThird * heightThird * hminorSecondThird
  · linear_combination heightThird * hmixedBudget - readingThird * hnormalBudget
      + weightFirst * heightFirst * hminorFirstThird
      + weightSecond * heightSecond * hminorSecondThird

/-- **Vanishing minors blind the whole triple.**  At an in-plane probe where all
three pair differences read zero, every atom of the triple reads zero. -/
theorem tripleReadings_eq_zero_of_pairDifference_readings_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (unitNormal probeVec : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hprobeFlat : unitNormal ⬝ᵥ probeVec = 0)
    (houtsideFlat : ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
      design.atom label ⬝ᵥ unitNormal = 0)
    (hminorFirstSecond :
      heightPairDifference design freeFirst freeSecond unitNormal ⬝ᵥ probeVec = 0)
    (hminorFirstThird :
      heightPairDifference design freeFirst freeThird unitNormal ⬝ᵥ probeVec = 0)
    (hminorSecondThird :
      heightPairDifference design freeSecond freeThird unitNormal ⬝ᵥ probeVec = 0) :
    ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size)),
      design.atom label ⬝ᵥ probeVec = 0 := by
  have hnormalBudget := sum_selected_weight_mul_sq_reading_eq_one_of_outsideFlat design
    ({freeFirst, freeSecond, freeThird} : Finset (Fin size)) hunit houtsideFlat
  have hmixedBudget := sum_selected_weight_mul_normalReading_mul_reading_eq_zero design
    ({freeFirst, freeSecond, freeThird} : Finset (Fin size)) unitNormal probeVec hprobeFlat
    houtsideFlat
  rw [sum_over_tripleSet_eq hFirstSecond hFirstThird hSecondThird] at hnormalBudget hmixedBudget
  rw [heightPairDifference_dotProduct] at hminorFirstSecond hminorFirstThird hminorSecondThird
  obtain ⟨hfirstZero, hsecondZero, hthirdZero⟩ := readings_eq_zero_of_minors_eq_zero
    (design.weight freeFirst) (design.weight freeSecond) (design.weight freeThird)
    (design.atom freeFirst ⬝ᵥ unitNormal) (design.atom freeSecond ⬝ᵥ unitNormal)
    (design.atom freeThird ⬝ᵥ unitNormal) (design.atom freeFirst ⬝ᵥ probeVec)
    (design.atom freeSecond ⬝ᵥ probeVec) (design.atom freeThird ⬝ᵥ probeVec)
    hnormalBudget hmixedBudget hminorFirstSecond hminorFirstThird hminorSecondThird
  intro label hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hfirstZero
  · exact hsecondZero
  · exact hthirdZero

/-- **THE NAMED BRANCH.**  At an in-plane probe where the triple's three pair
differences all read zero, the triple does not even WEAKLY dominate -- so the
canonical flat-complement anatomy provably cannot close the class there, and a
different triple has to be produced.  This is the exact residual branch the
Lagrange form leaves open. -/
theorem not_dominates_tripleSet_of_pairDifference_readings_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (unitNormal probeVec : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hprobeFlat : unitNormal ⬝ᵥ probeVec = 0) (hprobeNe : probeVec ≠ 0)
    (houtsideFlat : ∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
      design.atom label ⬝ᵥ unitNormal = 0)
    (hminorFirstSecond :
      heightPairDifference design freeFirst freeSecond unitNormal ⬝ᵥ probeVec = 0)
    (hminorFirstThird :
      heightPairDifference design freeFirst freeThird unitNormal ⬝ᵥ probeVec = 0)
    (hminorSecondThird :
      heightPairDifference design freeSecond freeThird unitNormal ⬝ᵥ probeVec = 0) :
    ¬ Dominates design ({freeFirst, freeSecond, freeThird} : Finset (Fin size)) :=
  not_dominates_of_blind_probe design _ hprobeNe
    (tripleReadings_eq_zero_of_pairDifference_readings_eq_zero design hFirstSecond hFirstThird
      hSecondThird unitNormal probeVec hunit hprobeFlat houtsideFlat hminorFirstSecond
      hminorFirstThird hminorSecondThird)

/-! ## Part 6c -- the circle family: normals lying IN the line plane

The uniform Schur producer accepts ANY unit normal, not only the line's.  Take
one lying in the line plane: the three line atoms then project onto a SINGLE
parallel class of the new plane, because their projections are orthogonal to
both the line normal and the in-plane normal, and that intersection is a line.
So along the whole circle of in-plane directions the class's shadow has at most
four parallel classes, and every strict pair in such a shadow must involve a
free atom.  This is the one-parameter family of probes a single-normal attack
never had.
-/

/-- The component of an atom orthogonal to a unit direction. -/
noncomputable def atomShadowAgainst {size : ℕ} (design : WeightedDesign size 3)
    (label : Fin size) (unitDirection : Fin 3 → ℝ) : Fin 3 → ℝ :=
  design.atom label - (design.atom label ⬝ᵥ unitDirection) • unitDirection

/-- The shadow is orthogonal to the direction it was taken against. -/
theorem atomShadowAgainst_dotProduct_self_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    (label : Fin size) (unitDirection : Fin 3 → ℝ)
    (hunit : unitDirection ⬝ᵥ unitDirection = 1) :
    atomShadowAgainst design label unitDirection ⬝ᵥ unitDirection = 0 := by
  rw [atomShadowAgainst, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, sub_self]

/-- A flat atom's shadow against an in-plane direction stays flat. -/
theorem atomShadowAgainst_dotProduct_planeNormal_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) (label : Fin size)
    (planeNormal inPlaneDirection : Fin 3 → ℝ)
    (hinPlaneFlat : inPlaneDirection ⬝ᵥ planeNormal = 0)
    (hatomFlat : design.atom label ⬝ᵥ planeNormal = 0) :
    atomShadowAgainst design label inPlaneDirection ⬝ᵥ planeNormal = 0 := by
  rw [atomShadowAgainst, sub_dotProduct, smul_dotProduct, smul_eq_mul, hinPlaneFlat, hatomFlat,
    mul_zero, sub_zero]

/-- **THE CIRCLE FAMILY.**  Against a unit direction lying in the line plane the
shadows of any two line atoms are PARALLEL: both are orthogonal to the line
normal and to the in-plane direction, and those two span a plane. -/
theorem lineShadows_parallel_at_inPlaneDirection {size : ℕ} (design : WeightedDesign size 3)
    (planeNormal inPlaneDirection : Fin 3 → ℝ) (hplaneNormalNe : planeNormal ≠ 0)
    (hinPlaneNe : inPlaneDirection ≠ 0)
    (hunit : inPlaneDirection ⬝ᵥ inPlaneDirection = 1)
    (hinPlaneFlat : planeNormal ⬝ᵥ inPlaneDirection = 0)
    {firstLabel secondLabel : Fin size}
    (hfirstFlat : design.atom firstLabel ⬝ᵥ planeNormal = 0)
    (hsecondFlat : design.atom secondLabel ⬝ᵥ planeNormal = 0)
    (hfirstShadowNe : atomShadowAgainst design firstLabel inPlaneDirection ≠ 0) :
    ∃ scale : ℝ, atomShadowAgainst design secondLabel inPlaneDirection
      = scale • atomShadowAgainst design firstLabel inPlaneDirection := by
  have hinPlaneFlatSym : inPlaneDirection ⬝ᵥ planeNormal = 0 := by
    rw [dotProduct_comm]; exact hinPlaneFlat
  exact exists_smul_of_orthogonal_to_independent_normals hplaneNormalNe
    (not_parallel_of_orthogonal_of_ne_zero hplaneNormalNe hinPlaneNe hinPlaneFlat)
    hfirstShadowNe
    (atomShadowAgainst_dotProduct_planeNormal_eq_zero design firstLabel planeNormal
      inPlaneDirection hinPlaneFlatSym hfirstFlat)
    (atomShadowAgainst_dotProduct_self_eq_zero design firstLabel inPlaneDirection hunit)
    (atomShadowAgainst_dotProduct_planeNormal_eq_zero design secondLabel planeNormal
      inPlaneDirection hinPlaneFlatSym hsecondFlat)
    (atomShadowAgainst_dotProduct_self_eq_zero design secondLabel inPlaneDirection hunit)

/-- **The one-line reading of the circle family**: at every unit direction in
the line plane the three line atoms cast parallel shadows, so the shadow design
has at most four parallel classes and no line-line pair can dominate it. -/
theorem oneLine_lineShadows_parallel_at_inPlaneDirection (design : WeightedDesign 6 3)
    (planeNormal inPlaneDirection : Fin 3 → ℝ) (hplaneNormalNe : planeNormal ≠ 0)
    (hinPlaneNe : inPlaneDirection ≠ 0)
    (hunit : inPlaneDirection ⬝ᵥ inPlaneDirection = 1)
    (hinPlaneFlat : planeNormal ⬝ᵥ inPlaneDirection = 0)
    (horthogonal : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ planeNormal = 0)
    {firstLabel secondLabel : Fin 6}
    (hfirstLine : firstLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hsecondLine : secondLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfirstShadowNe : atomShadowAgainst design firstLabel inPlaneDirection ≠ 0) :
    ∃ scale : ℝ, atomShadowAgainst design secondLabel inPlaneDirection
      = scale • atomShadowAgainst design firstLabel inPlaneDirection :=
  lineShadows_parallel_at_inPlaneDirection design planeNormal inPlaneDirection hplaneNormalNe
    hinPlaneNe hunit hinPlaneFlat (horthogonal firstLabel hfirstLine)
    (horthogonal secondLabel hsecondLine) hfirstShadowNe

/-! ## Part 6d -- the twin's case-(ii) normal form, with its one exception named

`Gtz.oneLine_shadowColumn_injective_and_nonzero` closes case (ii) on the
one-line stratum: when the rank-two four-direction hinge fails at the line
normal, every free shadow lands on a line atom, the assignment is injective and
no ratio vanishes.  The twin is NOT a verbatim copy, because the twin pattern
DECLARES `{0,3,4}` dependent -- a collision of the free labels `3` and `4` on
the column `0` is allowed by the matroid and is therefore not a contradiction.

That single exception is the whole difference.  Every other collision is still
impossible, and the ratio-nonvanishing survives INTACT, because each free label
has a partner whose pair with it is not `{3,4}`.
-/

/-- **THE TWIN COLLISION IS FORCED TO THE MEETING PLANE.**  Two distinct free
atoms sharing one line atom's plane through the normal force that line atom to
be the meeting point `0` and the two free atoms to be `3` and `4` -- the twin
pattern's own second line. -/
theorem twoMeetingLines_shadowCollision_forced (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec : Fin 3 → ℝ) {lineLabel freeFirst freeSecond : Fin 6}
    (hlineMem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfirstMem : freeFirst ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hsecondMem : freeSecond ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hdistinct : freeFirst ≠ freeSecond)
    (hfirstInPlane : ∃ alongLine alongNormal : ℝ,
      design.atom freeFirst = alongLine • design.atom lineLabel + alongNormal • normalVec)
    (hsecondInPlane : ∃ alongLine alongNormal : ℝ,
      design.atom freeSecond = alongLine • design.atom lineLabel + alongNormal • normalVec) :
    lineLabel = 0 ∧ ({freeFirst, freeSecond} : Finset (Fin 6)) = {3, 4} := by
  have hlineFirst : lineLabel ≠ freeFirst := by
    fin_cases hlineMem <;> fin_cases hfirstMem <;> decide
  have hlineSecond : lineLabel ≠ freeSecond := by
    fin_cases hlineMem <;> fin_cases hsecondMem <;> decide
  have hbracket : atomBracket design lineLabel freeFirst freeSecond = 0 :=
    tripleBracket_eq_zero_of_spannedByPair (design.atom lineLabel) normalVec _ _ _
      (spannedByPair_self _ _) hfirstInPlane hsecondInPlane
  have hinPattern :=
    (hpattern lineLabel freeFirst freeSecond hlineFirst hlineSecond hdistinct).mp hbracket
  revert hdistinct hinPattern
  fin_cases hlineMem <;> fin_cases hfirstMem <;> fin_cases hsecondMem <;> decide

/-- **The twin's shadow columns collide only at the meeting plane.** -/
theorem twoMeetingLines_shadowColumn_collision_only_at_meetingPlane
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec : Fin 3 → ℝ) (columnOf : Fin 6 → Fin 6) (ratioOf : Fin 6 → ℝ)
    (hcolumnMem : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      columnOf freeLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hshadow : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      design.atom freeLabel - (design.atom freeLabel ⬝ᵥ normalVec) • normalVec
        = ratioOf freeLabel • design.atom (columnOf freeLabel))
    {freeFirst freeSecond : Fin 6}
    (hfirstMem : freeFirst ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hsecondMem : freeSecond ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hdistinct : freeFirst ≠ freeSecond)
    (hcolumnEq : columnOf freeFirst = columnOf freeSecond) :
    columnOf freeFirst = 0 ∧ ({freeFirst, freeSecond} : Finset (Fin 6)) = {3, 4} :=
  twoMeetingLines_shadowCollision_forced design hpattern normalVec
    (hcolumnMem freeFirst hfirstMem) hfirstMem hsecondMem hdistinct
    (spannedByPair_of_shadow_eq_smul _ _ _ _ (hshadow freeFirst hfirstMem))
    (by rw [hcolumnEq]
        exact spannedByPair_of_shadow_eq_smul _ _ _ _ (hshadow freeSecond hsecondMem))

/-- **THE TWIN RATIO NEVER VANISHES.**  Unlike the collision bound, this half of
the one-line normal form survives the twin intact: a vanishing ratio would put
the free atom in EVERY line atom's plane through the normal, and each free label
has a partner whose pair with it is not the allowed `{3,4}`. -/
theorem twoMeetingLines_shadowRatio_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalVec : Fin 3 → ℝ) (columnOf : Fin 6 → Fin 6) (ratioOf : Fin 6 → ℝ)
    (hcolumnMem : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      columnOf freeLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hshadow : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      design.atom freeLabel - (design.atom freeLabel ⬝ᵥ normalVec) • normalVec
        = ratioOf freeLabel • design.atom (columnOf freeLabel))
    {freeLabel : Fin 6} (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    ratioOf freeLabel ≠ 0 := by
  intro hratioZero
  have hflat : design.atom freeLabel
      = (design.atom freeLabel ⬝ᵥ normalVec) • normalVec := by
    have hraw := hshadow freeLabel hmem
    rw [hratioZero, zero_smul, sub_eq_zero] at hraw
    exact hraw
  have hcollision : ∀ partner ∈ ({3, 4, 5} : Finset (Fin 6)), partner ≠ freeLabel →
      ({freeLabel, partner} : Finset (Fin 6)) = {3, 4} := by
    intro partner hpartnerMem hpartnerNe
    exact (twoMeetingLines_shadowCollision_forced design hpattern normalVec
      (hcolumnMem partner hpartnerMem) hmem hpartnerMem (Ne.symm hpartnerNe)
      ⟨0, design.atom freeLabel ⬝ᵥ normalVec, by rw [zero_smul, zero_add]; exact hflat⟩
      (spannedByPair_of_shadow_eq_smul _ _ _ _ (hshadow partner hpartnerMem))).2
  fin_cases hmem
  · exact absurd (hcollision 5 (by decide) (by decide)) (by decide)
  · exact absurd (hcollision 5 (by decide) (by decide)) (by decide)
  · exact absurd (hcollision 3 (by decide) (by decide)) (by decide)

/-! ## Part 7 -- the chartless reductions

`Gtz.patternHeavyWeakToStrict_of_capBlindSpot` already reduces the whole
obligation at ANY line pattern to the pair-cap engine's blind spot.  Stacking
Part 5 on top of it leaves exactly one scalar sign test per in-plane probe.
-/

/-- **THE CHARTLESS REDUCTION, pattern-generic.**  The obligation follows from
Lagrange dominance of one flat-complement triple, demanded only on the cap blind
spot. -/
theorem patternHeavyWeakToStrict_of_lagrangeDominatingTriple {size : ℕ} (hsize : 2 ≤ size)
    (pattern : LinePattern size) {freeFirst freeSecond freeThird : Fin size}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (hresidual : ∀ design : WeightedDesign size 3, HasLinePattern design pattern →
      (∀ label : Fin size, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1
        ∧ (∀ label ∈ ({freeFirst, freeSecond, freeThird} : Finset (Fin size))ᶜ,
            design.atom label ⬝ᵥ unitNormal = 0)
        ∧ IsLagrangeDominatingTriple design freeFirst freeSecond freeThird unitNormal) :
    PatternHeavyWeakToStrict pattern := by
  refine patternHeavyWeakToStrict_of_capBlindSpot pattern
    fun design hpattern hheavy hblind hweak => ?_
  obtain ⟨unitNormal, hunit, houtsideFlat, hdominates⟩ :=
    hresidual design hpattern hheavy hblind hweak
  exact exists_posDef_cardThree_of_isLagrangeDominatingTriple design hsize hFirstSecond
    hFirstThird hSecondThird unitNormal hunit houtsideFlat hdominates

/-- A nonzero vector rescales to a unit vector along the same ray. -/
theorem exists_unitScaling_of_ne_zero {rank : ℕ} {baseVec : Fin rank → ℝ}
    (hne : baseVec ≠ 0) :
    ∃ scale : ℝ, scale ≠ 0 ∧ (scale • baseVec) ⬝ᵥ (scale • baseVec) = 1 := by
  have hnormPos : 0 < baseVec ⬝ᵥ baseVec := dotProduct_self_pos hne
  have hsqrtPos : 0 < Real.sqrt (baseVec ⬝ᵥ baseVec) := Real.sqrt_pos.mpr hnormPos
  refine ⟨(Real.sqrt (baseVec ⬝ᵥ baseVec))⁻¹, inv_ne_zero hsqrtPos.ne', ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt hnormPos.le]
  exact inv_mul_cancel₀ hnormPos.ne'

/-- **The one-line stratum carries a UNIT line normal.** -/
theorem oneLine_exists_unitLineNormal (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ∃ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1
      ∧ ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ unitNormal = 0 := by
  obtain ⟨normalVec, hnormalNe, horthogonal⟩ := oneLine_has_lineNormal design hpattern
  obtain ⟨scale, hscaleNe, hunit⟩ := exists_unitScaling_of_ne_zero hnormalNe
  refine ⟨scale • normalVec, hunit, fun lineLabel hmem => ?_⟩
  rw [dotProduct_smul, smul_eq_mul, horthogonal lineLabel hmem, mul_zero]

/-- **The two-meeting-lines stratum carries two UNIT line normals.** -/
theorem twoMeetingLines_exists_unitLineNormals (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    ∃ unitNormalFirst unitNormalSecond : Fin 3 → ℝ,
      unitNormalFirst ⬝ᵥ unitNormalFirst = 1 ∧ unitNormalSecond ⬝ᵥ unitNormalSecond = 1
        ∧ (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
            design.atom lineLabel ⬝ᵥ unitNormalFirst = 0)
        ∧ ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
            design.atom lineLabel ⬝ᵥ unitNormalSecond = 0 := by
  obtain ⟨normalFirst, normalSecond, hfirstNe, hsecondNe, horthFirst, horthSecond⟩ :=
    twoMeetingLines_have_two_normals design hpattern
  obtain ⟨scaleFirst, _, hunitFirst⟩ := exists_unitScaling_of_ne_zero hfirstNe
  obtain ⟨scaleSecond, _, hunitSecond⟩ := exists_unitScaling_of_ne_zero hsecondNe
  refine ⟨scaleFirst • normalFirst, scaleSecond • normalSecond, hunitFirst, hunitSecond,
    fun lineLabel hmem => ?_, fun lineLabel hmem => ?_⟩
  · rw [dotProduct_smul, smul_eq_mul, horthFirst lineLabel hmem, mul_zero]
  · rw [dotProduct_smul, smul_eq_mul, horthSecond lineLabel hmem, mul_zero]

/-- **THE ONE-LINE REDUCTION.**  The normal is supplied by the pattern, so all
that is left of the class obligation is the scalar sign test at the free triple
`{3,4,5}`, on the cap blind spot. -/
theorem patternHeavyWeakToStrict_oneLine_of_lagrangeDominance
    (hresidual : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
        (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ unitNormal = 0) →
        IsLagrangeDominatingTriple design 3 4 5 unitNormal) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  refine patternHeavyWeakToStrict_of_lagrangeDominatingTriple (by norm_num) _
    (by decide : (3 : Fin 6) ≠ 4) (by decide : (3 : Fin 6) ≠ 5) (by decide : (4 : Fin 6) ≠ 5)
    fun design hpattern hheavy hblind hweak => ?_
  obtain ⟨unitNormal, hunit, horthogonal⟩ := oneLine_exists_unitLineNormal design hpattern
  refine ⟨unitNormal, hunit, fun label hmem => ?_,
    hresidual design hpattern hheavy hblind hweak unitNormal hunit horthogonal⟩
  exact horthogonal label
    (by rw [show ({(3 : Fin 6), 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} from by decide] at hmem
        exact hmem)

/-- **THE TWIN REDUCTION AT THE FIRST LINE.**  Free triple `{3,4,5}`, the
complement of the line `{0,1,2}`. -/
theorem patternHeavyWeakToStrict_twoMeetingLines_of_firstLineDominance
    (hresidual : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
        (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ unitNormal = 0) →
        IsLagrangeDominatingTriple design 3 4 5 unitNormal) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  refine patternHeavyWeakToStrict_of_lagrangeDominatingTriple (by norm_num) _
    (by decide : (3 : Fin 6) ≠ 4) (by decide : (3 : Fin 6) ≠ 5) (by decide : (4 : Fin 6) ≠ 5)
    fun design hpattern hheavy hblind hweak => ?_
  obtain ⟨unitNormalFirst, _, hunitFirst, _, horthFirst, _⟩ :=
    twoMeetingLines_exists_unitLineNormals design hpattern
  refine ⟨unitNormalFirst, hunitFirst, fun label hmem => ?_,
    hresidual design hpattern hheavy hblind hweak unitNormalFirst hunitFirst horthFirst⟩
  exact horthFirst label
    (by rw [show ({(3 : Fin 6), 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} from by decide] at hmem
        exact hmem)

/-- **THE TWIN REDUCTION AT THE SECOND LINE.**  Free triple `{1,2,5}`, the
complement of the line `{0,3,4}`.  Either reduction suffices, so the twin gets
two independent scalar sign tests, sharing only the label `5`. -/
theorem patternHeavyWeakToStrict_twoMeetingLines_of_secondLineDominance
    (hresidual : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
        (∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
          design.atom lineLabel ⬝ᵥ unitNormal = 0) →
        IsLagrangeDominatingTriple design 1 2 5 unitNormal) :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  refine patternHeavyWeakToStrict_of_lagrangeDominatingTriple (by norm_num) _
    (by decide : (1 : Fin 6) ≠ 2) (by decide : (1 : Fin 6) ≠ 5) (by decide : (2 : Fin 6) ≠ 5)
    fun design hpattern hheavy hblind hweak => ?_
  obtain ⟨_, unitNormalSecond, _, hunitSecond, _, horthSecond⟩ :=
    twoMeetingLines_exists_unitLineNormals design hpattern
  refine ⟨unitNormalSecond, hunitSecond, fun label hmem => ?_,
    hresidual design hpattern hheavy hblind hweak unitNormalSecond hunitSecond horthSecond⟩
  exact horthSecond label
    (by rw [show ({(1 : Fin 6), 2, 5} : Finset (Fin 6))ᶜ = {0, 3, 4} from by decide] at hmem
        exact hmem)

/-! ## Part 8 -- non-vacuity on the tree's shipped one-line member

`Gtz.oneLineSampleDesign` realizes the one-line pattern exactly and its free
triple `{3,4,5}` is strictly dominating.  Its line lies in `z = 0`, so `![0,0,1]`
is already a unit line normal, and the equivalence of Part 5 turns the shipped
positive definiteness into the residual inequality.  The residual is therefore
SATISFIED somewhere on the stratum -- it is not an unreachable demand.
-/

/-- The sample's line atoms are flat against the third coordinate axis. -/
theorem oneLineSample_lineAtoms_flat :
    ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      oneLineSampleDesign.atom lineLabel ⬝ᵥ ![(0 : ℝ), 0, 1] = 0 := by
  intro lineLabel hmem
  fin_cases hmem <;>
    simp [oneLineSampleDesign, oneLineSampleAtom, dotProduct, Fin.sum_univ_three]

/-- **The residual FIRES on the shipped one-line member.** -/
theorem oneLineSample_isLagrangeDominatingTriple :
    IsLagrangeDominatingTriple oneLineSampleDesign 3 4 5 ![(0 : ℝ), 0, 1] := by
  refine (posDef_tripleSet_iff_isLagrangeDominatingTriple oneLineSampleDesign (by norm_num)
    (by decide : (3 : Fin 6) ≠ 4) (by decide : (3 : Fin 6) ≠ 5) (by decide : (4 : Fin 6) ≠ 5)
    ![(0 : ℝ), 0, 1] (by simp [dotProduct, Fin.sum_univ_three]) fun label hmem => ?_).mp
    oneLineSample_freeTripleGap_posDef
  exact oneLineSample_lineAtoms_flat label
    (by rw [show ({(3 : Fin 6), 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} from by decide] at hmem
        exact hmem)

/-- **The one-line stratum is inhabited and its axis producer fires there.** -/
theorem oneLineSample_exists_unitAxis_planeStrictPair :
    ∃ unitAxis : Fin 3 → ℝ, unitAxis ⬝ᵥ unitAxis = 1
      ∧ ∃ strongLabel otherLabel : Fin 6, strongLabel ≠ otherLabel
          ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ unitAxis = 0 → planar ≠ 0 →
              planar ⬝ᵥ planar
                < (oneLineSampleDesign.atom strongLabel ⬝ᵥ planar) ^ 2
                  + (oneLineSampleDesign.atom otherLabel ⬝ᵥ planar) ^ 2 :=
  oneLine_exists_unitAxis_planeStrictPair oneLineSampleDesign
    oneLineSampleDesign_hasLinePattern

end Gtz

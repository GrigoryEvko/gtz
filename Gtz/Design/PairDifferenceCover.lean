/-
# The pair-difference form: the plane cover with the probe quantifier removed

`posDef_of_normalSurplus_planeCover`'s plane-cover hypothesis at a card-three
subset is, ANATOMY-FREE, an inequality in the three PAIR-DIFFERENCE readings of
the subset -- the two-by-two minors of the reading matrix.  Flatness at a slot
simply zeroes some of them, so every anatomy is one specialization: two flat
slots collapse it to the landed in-plane excess (an Iff, so the landed
reduction loses nothing), one flat slot leaves the free pair's squared
difference, no flat slot leaves all three.  Each specialization comes with its
producer and its blind-probe kill: wherever all three pair-differences read
zero the cover is refuted outright, because the three pair-difference vectors
must SPAN the normal's plane.

Then the quantifier goes.  Against any orthonormal frame of the normal's plane
the cover is a two-by-two positivity -- one diagonal `coverForm` minor and the
frame determinant -- so strict domination is THREE scalar inequalities with no
probe left, and the unit normal transfers freely between choices.

The two-meeting-lines instance is the sharpest consequence: on that stratum the
shared atom together with the second line's private pair is pair-difference
BLIND along the second normal's in-plane component, for EVERY choice of the
first normal, so `{0,3,4}` never covers there.
-/
import Gtz.Design.LineMarginCap

set_option maxHeartbeats 4000000

namespace Gtz
open Matrix

theorem sumOverTriple {size : ℕ}
    (firstLabel secondLabel thirdLabel : Fin size)
    (hfirstSecond : firstLabel ≠ secondLabel)
    (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (valueOf : Fin size → ℝ) :
    ∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
        valueOf selectedLabel
      = valueOf firstLabel + valueOf secondLabel + valueOf thirdLabel := by
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

theorem coverIneq_iff_pairDifferenceExcess
    (normalFirst normalSecond normalThird
      probeFirst probeSecond probeThird probeNormSq : ℝ) :
    (probeFirst * normalFirst + probeSecond * normalSecond
          + probeThird * normalThird) ^ 2
        < (normalFirst ^ 2 + normalSecond ^ 2 + normalThird ^ 2 - 1)
          * (probeFirst ^ 2 + probeSecond ^ 2 + probeThird ^ 2 - probeNormSq)
      ↔ probeFirst ^ 2 + probeSecond ^ 2 + probeThird ^ 2
            + (normalFirst ^ 2 + normalSecond ^ 2 + normalThird ^ 2 - 1) * probeNormSq
          < (normalSecond * probeFirst - normalFirst * probeSecond) ^ 2
            + (normalThird * probeFirst - normalFirst * probeThird) ^ 2
            + (normalThird * probeSecond - normalSecond * probeThird) ^ 2 := by
  constructor <;> intro hyp <;> nlinarith [hyp]

/-- **The uniform pair-difference form of the plane cover at a card-three
subset.**  Anatomy-free: no flatness is assumed of any slot. -/
theorem planeCover_iff_pairDifferenceExcess {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size)
    (hfirstSecond : firstLabel ≠ secondLabel)
    (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (unitNormal probe : Fin 3 → ℝ) :
    (∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
                (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
                  (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)
      ↔ (design.atom firstLabel ⬝ᵥ probe) ^ 2 + (design.atom secondLabel ⬝ᵥ probe) ^ 2
            + (design.atom thirdLabel ⬝ᵥ probe) ^ 2
            + ((design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
                + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
                + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2 - 1) * (probe ⬝ᵥ probe)
          < ((design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
                - (design.atom firstLabel ⬝ᵥ unitNormal)
                  * (design.atom secondLabel ⬝ᵥ probe)) ^ 2
            + ((design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
                - (design.atom firstLabel ⬝ᵥ unitNormal)
                  * (design.atom thirdLabel ⬝ᵥ probe)) ^ 2
            + ((design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe)
                - (design.atom secondLabel ⬝ᵥ unitNormal)
                  * (design.atom thirdLabel ⬝ᵥ probe)) ^ 2 := by
  rw [sumOverTriple firstLabel secondLabel thirdLabel hfirstSecond hfirstThird hsecondThird
      (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ probe)
        * (design.atom selectedLabel ⬝ᵥ unitNormal)),
    sumOverTriple firstLabel secondLabel thirdLabel hfirstSecond hfirstThird hsecondThird
      (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2),
    sumOverTriple firstLabel secondLabel thirdLabel hfirstSecond hfirstThird hsecondThird
      (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ probe) ^ 2)]
  exact coverIneq_iff_pairDifferenceExcess _ _ _ _ _ _ _

/-! ## Anatomy specialisations at a line normal -/

/-- **LLF, as an equivalence.**  Two flat slots plus one free slot: the plane
cover is EXACTLY the landed in-plane excess inequality.  The landed
`oneLine_planeCover_of_inPlaneExcess` is the forward half; nothing is lost. -/
theorem twoFlat_planeCover_iff_inPlaneExcess {size : ℕ} (design : WeightedDesign size 3)
    (lineFirst lineSecond freeLabel : Fin size)
    (hdistinctFirstSecond : lineFirst ≠ lineSecond)
    (hdistinctFirstFree : lineFirst ≠ freeLabel)
    (hdistinctSecondFree : lineSecond ≠ freeLabel)
    (unitNormal probe : Fin 3 → ℝ)
    (hfirstFlat : design.atom lineFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom lineSecond ⬝ᵥ unitNormal = 0) :
    (∑ selectedLabel ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
                (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
                  (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)
      ↔ (design.atom freeLabel ⬝ᵥ probe) ^ 2
          < ((design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1)
            * ((design.atom lineFirst ⬝ᵥ probe) ^ 2
                + (design.atom lineSecond ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe) := by
  rw [planeCover_iff_pairDifferenceExcess design lineFirst lineSecond freeLabel
    hdistinctFirstSecond hdistinctFirstFree hdistinctSecondFree unitNormal probe,
    hfirstFlat, hsecondFlat]
  constructor <;> intro hyp <;> nlinarith [hyp]

/-- **LFF, as an equivalence.**  One flat slot plus two free slots.  The two
free normal components `normalFree*` no longer cancel singly; what survives is
the squared pair-difference reading of the free pair, and the flat slot's own
in-plane excess is scaled by the JOINT surplus. -/
theorem oneFlat_planeCover_iff_freePairExcess {size : ℕ} (design : WeightedDesign size 3)
    (lineLabel freeFirst freeSecond : Fin size)
    (hdistinctLineFirst : lineLabel ≠ freeFirst)
    (hdistinctLineSecond : lineLabel ≠ freeSecond)
    (hdistinctFreePair : freeFirst ≠ freeSecond)
    (unitNormal probe : Fin 3 → ℝ)
    (hlineFlat : design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    (∑ selectedLabel ∈ ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)),
                (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)),
                  (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)
      ↔ (design.atom freeFirst ⬝ᵥ probe) ^ 2 + (design.atom freeSecond ⬝ᵥ probe) ^ 2
          < ((design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
                + (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2 - 1)
              * ((design.atom lineLabel ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe)
            + ((design.atom freeSecond ⬝ᵥ unitNormal) * (design.atom freeFirst ⬝ᵥ probe)
                - (design.atom freeFirst ⬝ᵥ unitNormal)
                  * (design.atom freeSecond ⬝ᵥ probe)) ^ 2 := by
  rw [planeCover_iff_pairDifferenceExcess design lineLabel freeFirst freeSecond
    hdistinctLineFirst hdistinctLineSecond hdistinctFreePair unitNormal probe, hlineFlat]
  constructor <;> intro hyp <;> nlinarith [hyp]

/-- **The LFF producer.**  A line atom plus a free pair whose reduced in-plane
inequality holds at every in-plane probe has a POSITIVE DEFINITE gap. -/
theorem posDef_of_oneFlat_freePairExcess {size : ℕ} (design : WeightedDesign size 3)
    (lineLabel freeFirst freeSecond : Fin size)
    (hdistinctLineFirst : lineLabel ≠ freeFirst)
    (hdistinctLineSecond : lineLabel ≠ freeSecond)
    (hdistinctFreePair : freeFirst ≠ freeSecond)
    (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hsurplus : 1 < (design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
      + (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2)
    (hfreePairExcess : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
      (design.atom freeFirst ⬝ᵥ probe) ^ 2 + (design.atom freeSecond ⬝ᵥ probe) ^ 2
        < ((design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
              + (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2 - 1)
            * ((design.atom lineLabel ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe)
          + ((design.atom freeSecond ⬝ᵥ unitNormal) * (design.atom freeFirst ⬝ᵥ probe)
              - (design.atom freeFirst ⬝ᵥ unitNormal)
                * (design.atom freeSecond ⬝ᵥ probe)) ^ 2) :
    (subsetSum design ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)) - 1).PosDef := by
  refine posDef_of_normalSurplus_planeCover design _ unitNormal hunit ?_ ?_
  · rw [sumOverTriple lineLabel freeFirst freeSecond hdistinctLineFirst hdistinctLineSecond
      hdistinctFreePair (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2),
      hlineFlat]
    simpa using hsurplus
  · intro probe hprobeFlat hprobeNe
    exact (oneFlat_planeCover_iff_freePairExcess design lineLabel freeFirst freeSecond
      hdistinctLineFirst hdistinctLineSecond hdistinctFreePair unitNormal probe
      hlineFlat).mpr (hfreePairExcess probe hprobeFlat hprobeNe)

/-- **The FFF producer.**  With no flat slot there is no cancellation left: the
pair-difference form IS the reduced statement.  Three free atoms whose three
squared pair-differences outweigh their own probe readings plus the surplus
times the probe norm have a POSITIVE DEFINITE gap. -/
theorem posDef_of_pairDifferenceExcess {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size)
    (hfirstSecond : firstLabel ≠ secondLabel)
    (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hsurplus : 1 < (design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2)
    (hpairExcess : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
      (design.atom firstLabel ⬝ᵥ probe) ^ 2 + (design.atom secondLabel ⬝ᵥ probe) ^ 2
          + (design.atom thirdLabel ⬝ᵥ probe) ^ 2
          + ((design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
              + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
              + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2 - 1) * (probe ⬝ᵥ probe)
        < ((design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
              - (design.atom firstLabel ⬝ᵥ unitNormal)
                * (design.atom secondLabel ⬝ᵥ probe)) ^ 2
          + ((design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom firstLabel ⬝ᵥ probe)
              - (design.atom firstLabel ⬝ᵥ unitNormal)
                * (design.atom thirdLabel ⬝ᵥ probe)) ^ 2
          + ((design.atom thirdLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe)
              - (design.atom secondLabel ⬝ᵥ unitNormal)
                * (design.atom thirdLabel ⬝ᵥ probe)) ^ 2) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1).PosDef := by
  refine posDef_of_normalSurplus_planeCover design _ unitNormal hunit ?_ ?_
  · rw [sumOverTriple firstLabel secondLabel thirdLabel hfirstSecond hfirstThird hsecondThird
      (fun selectedLabel => (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2)]
    exact hsurplus
  · intro probe hprobeFlat hprobeNe
    exact (planeCover_iff_pairDifferenceExcess design firstLabel secondLabel thirdLabel
      hfirstSecond hfirstThird hsecondThird unitNormal probe).mpr
      (hpairExcess probe hprobeFlat hprobeNe)


/-! ## The failure side: blind probes kill a cover -/

/-- **The cover fails wherever every pair-difference reading vanishes.**  With a
strict normal surplus the right-hand side of the pair-difference form is
strictly positive, so a probe on which all three pair-differences read zero
refutes the cover outright.  Geometrically: the three pair-difference vectors
must SPAN the normal's plane. -/
theorem planeCover_fails_of_pairDifferenceReadings_vanish {size : ℕ}
    (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size)
    (hfirstSecond : firstLabel ≠ secondLabel)
    (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (unitNormal probe : Fin 3 → ℝ) (hprobeNe : probe ≠ 0)
    (hsurplus : 1 < (design.atom firstLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom secondLabel ⬝ᵥ unitNormal) ^ 2
      + (design.atom thirdLabel ⬝ᵥ unitNormal) ^ 2)
    (hfirstSecondBlind : (design.atom secondLabel ⬝ᵥ unitNormal)
        * (design.atom firstLabel ⬝ᵥ probe)
      - (design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom secondLabel ⬝ᵥ probe) = 0)
    (hfirstThirdBlind : (design.atom thirdLabel ⬝ᵥ unitNormal)
        * (design.atom firstLabel ⬝ᵥ probe)
      - (design.atom firstLabel ⬝ᵥ unitNormal) * (design.atom thirdLabel ⬝ᵥ probe) = 0)
    (hsecondThirdBlind : (design.atom thirdLabel ⬝ᵥ unitNormal)
        * (design.atom secondLabel ⬝ᵥ probe)
      - (design.atom secondLabel ⬝ᵥ unitNormal) * (design.atom thirdLabel ⬝ᵥ probe) = 0) :
    ¬ ((∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
                (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
                  (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) := by
  rw [planeCover_iff_pairDifferenceExcess design firstLabel secondLabel thirdLabel
    hfirstSecond hfirstThird hsecondThird unitNormal probe,
    hfirstSecondBlind, hfirstThirdBlind, hsecondThirdBlind]
  have hprobeNormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hreadNonneg : (0 : ℝ) ≤ (design.atom firstLabel ⬝ᵥ probe) ^ 2
      + (design.atom secondLabel ⬝ᵥ probe) ^ 2 + (design.atom thirdLabel ⬝ᵥ probe) ^ 2 := by
    positivity
  intro hcover
  nlinarith [hcover, hprobeNormPos, hreadNonneg, hsurplus]

/-- **The LFF blind-probe kill.**  A line atom blind to the probe, plus a free
pair whose pair-difference reads zero there, cannot cover: two pair-differences
vanish because the line slot is flat, the third by hypothesis. -/
theorem oneFlat_planeCover_fails_at_blindProbe {size : ℕ} (design : WeightedDesign size 3)
    (lineLabel freeFirst freeSecond : Fin size)
    (hdistinctLineFirst : lineLabel ≠ freeFirst)
    (hdistinctLineSecond : lineLabel ≠ freeSecond)
    (hdistinctFreePair : freeFirst ≠ freeSecond)
    (unitNormal probe : Fin 3 → ℝ) (hprobeNe : probe ≠ 0)
    (hlineFlat : design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hlineBlind : design.atom lineLabel ⬝ᵥ probe = 0)
    (hsurplus : 1 < (design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
      + (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2)
    (hfreePairBlind : (design.atom freeSecond ⬝ᵥ unitNormal)
        * (design.atom freeFirst ⬝ᵥ probe)
      - (design.atom freeFirst ⬝ᵥ unitNormal) * (design.atom freeSecond ⬝ᵥ probe) = 0) :
    ¬ ((∑ selectedLabel ∈ ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)),
                (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({lineLabel, freeFirst, freeSecond} : Finset (Fin size)),
                  (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) := by
  refine planeCover_fails_of_pairDifferenceReadings_vanish design lineLabel freeFirst freeSecond
    hdistinctLineFirst hdistinctLineSecond hdistinctFreePair unitNormal probe hprobeNe
    ?_ ?_ ?_ hfreePairBlind
  · rw [hlineFlat]; simpa using hsurplus
  · rw [hlineFlat, hlineBlind]; ring
  · rw [hlineFlat, hlineBlind]; ring


/-! ## The two-meeting-lines instance -/

/-- The component of a vector orthogonal to a base direction. -/
noncomputable def projectOffBase (baseVec vector : Fin 3 → ℝ) : Fin 3 → ℝ :=
  vector - ((baseVec ⬝ᵥ vector) / (baseVec ⬝ᵥ baseVec)) • baseVec

theorem projectOffBase_orthogonal (baseVec vector : Fin 3 → ℝ) (hbaseNe : baseVec ≠ 0) :
    projectOffBase baseVec vector ⬝ᵥ baseVec = 0 := by
  have hbaseNormNe : baseVec ⬝ᵥ baseVec ≠ 0 := ne_of_gt (dotProduct_self_pos hbaseNe)
  rw [projectOffBase, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    dotProduct_comm vector baseVec, div_mul_cancel₀ _ hbaseNormNe, sub_self]

theorem projectOffBase_ne_zero (baseVec vector : Fin 3 → ℝ)
    (hnotParallel : ∀ ratio : ℝ, vector ≠ ratio • baseVec) :
    projectOffBase baseVec vector ≠ 0 := by
  intro hzero
  exact hnotParallel ((baseVec ⬝ᵥ vector) / (baseVec ⬝ᵥ baseVec))
    (sub_eq_zero.mp hzero)

/-- A vector annihilating the projected direction reads the base direction,
scaled by the projection ratio. -/
theorem dotProduct_projectOffBase_of_orthogonal (baseVec vector testVec : Fin 3 → ℝ)
    (htestOrth : testVec ⬝ᵥ vector = 0) :
    testVec ⬝ᵥ projectOffBase baseVec vector
      = -((baseVec ⬝ᵥ vector) / (baseVec ⬝ᵥ baseVec)) * (testVec ⬝ᵥ baseVec) := by
  rw [projectOffBase, dotProduct_sub, dotProduct_smul, smul_eq_mul, htestOrth]
  ring

/-- **The second line's private atoms are pair-difference blind along the second
normal's in-plane component.**  Both read the first normal only through the same
projection ratio, so their pair-difference cancels exactly.  This is the
two-meeting-lines rigidity in reading form. -/
theorem twoMeetingLines_freePair_blind_at_secondNormalProjection
    (design : WeightedDesign 6 3) (normalFirst normalSecond : Fin 3 → ℝ)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    (design.atom 4 ⬝ᵥ normalFirst)
        * (design.atom 3 ⬝ᵥ projectOffBase normalFirst normalSecond)
      - (design.atom 3 ⬝ᵥ normalFirst)
        * (design.atom 4 ⬝ᵥ projectOffBase normalFirst normalSecond) = 0 := by
  rw [dotProduct_projectOffBase_of_orthogonal normalFirst normalSecond (design.atom 3)
      (horthSecond 3 (by decide)),
    dotProduct_projectOffBase_of_orthogonal normalFirst normalSecond (design.atom 4)
      (horthSecond 4 (by decide))]
  ring

/-- The shared atom is blind to the second normal's in-plane component. -/
theorem twoMeetingLines_sharedAtom_blind_at_secondNormalProjection
    (design : WeightedDesign 6 3) (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    design.atom 0 ⬝ᵥ projectOffBase normalFirst normalSecond = 0 := by
  rw [dotProduct_projectOffBase_of_orthogonal normalFirst normalSecond (design.atom 0)
      (horthSecond 0 (by decide)), horthFirst 0 (by decide)]
  ring

/-- **The second line never covers at the first normal.**  On the
two-meeting-lines stratum, the card-three subset `{0, 3, 4}` — the shared atom
with the second line's private pair — fails the plane cover at the second
normal's in-plane component, for EVERY choice of the first normal.  Every
pair-difference reading is blind there. -/
theorem twoMeetingLines_secondLine_planeCover_fails
    (design : WeightedDesign 6 3) (normalFirst normalSecond : Fin 3 → ℝ)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hfirstNe : normalFirst ≠ 0) (hsecondNe : normalSecond ≠ 0)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hsurplus : 1 < (design.atom 3 ⬝ᵥ normalFirst) ^ 2
      + (design.atom 4 ⬝ᵥ normalFirst) ^ 2) :
    ¬ ((∑ selectedLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
            (design.atom selectedLabel ⬝ᵥ projectOffBase normalFirst normalSecond)
              * (design.atom selectedLabel ⬝ᵥ normalFirst)) ^ 2
          < ((∑ selectedLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
                (design.atom selectedLabel ⬝ᵥ normalFirst) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
                  (design.atom selectedLabel
                      ⬝ᵥ projectOffBase normalFirst normalSecond) ^ 2)
                - projectOffBase normalFirst normalSecond
                    ⬝ᵥ projectOffBase normalFirst normalSecond)) :=
  oneFlat_planeCover_fails_at_blindProbe design 0 3 4 (by decide) (by decide) (by decide)
    normalFirst (projectOffBase normalFirst normalSecond)
    (projectOffBase_ne_zero normalFirst normalSecond
      (twoMeetingLines_normals_not_parallel design normalFirst normalSecond hpattern
        hfirstNe hsecondNe horthFirst horthSecond))
    (horthFirst 0 (by decide))
    (twoMeetingLines_sharedAtom_blind_at_secondNormalProjection design normalFirst
      normalSecond horthFirst horthSecond)
    hsurplus
    (twoMeetingLines_freePair_blind_at_secondNormalProjection design normalFirst
      normalSecond horthSecond)


/-- **The two-meeting-lines cover budget.**  For ANY first-line atom `lineLabel`
paired with the second line's private atoms, the plane cover at the second
normal's in-plane component collapses to a single scalar budget: the line atom
alone, scaled by the free pair's surplus, must beat the probe norm plus the
projection ratio squared times the free pair's total normal weight.  The free
pair contributes NOTHING in this direction.  At `lineLabel = 0` the left side is
zero and the budget is unsatisfiable. -/
theorem twoMeetingLines_coverBudget_at_secondNormalProjection
    (design : WeightedDesign 6 3) (lineLabel : Fin 6)
    (hlineFirstLine : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hdistinctThird : lineLabel ≠ 3) (hdistinctFourth : lineLabel ≠ 4)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ line ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom line ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ line ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom line ⬝ᵥ normalSecond = 0) :
    ((∑ selectedLabel ∈ ({lineLabel, 3, 4} : Finset (Fin 6)),
            (design.atom selectedLabel ⬝ᵥ projectOffBase normalFirst normalSecond)
              * (design.atom selectedLabel ⬝ᵥ normalFirst)) ^ 2
          < ((∑ selectedLabel ∈ ({lineLabel, 3, 4} : Finset (Fin 6)),
                (design.atom selectedLabel ⬝ᵥ normalFirst) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({lineLabel, 3, 4} : Finset (Fin 6)),
                  (design.atom selectedLabel
                      ⬝ᵥ projectOffBase normalFirst normalSecond) ^ 2)
                - projectOffBase normalFirst normalSecond
                    ⬝ᵥ projectOffBase normalFirst normalSecond))
      ↔ ((normalFirst ⬝ᵥ normalSecond) / (normalFirst ⬝ᵥ normalFirst)) ^ 2
              * ((design.atom 3 ⬝ᵥ normalFirst) ^ 2 + (design.atom 4 ⬝ᵥ normalFirst) ^ 2)
          < ((design.atom 3 ⬝ᵥ normalFirst) ^ 2
                + (design.atom 4 ⬝ᵥ normalFirst) ^ 2 - 1)
            * ((design.atom lineLabel ⬝ᵥ projectOffBase normalFirst normalSecond) ^ 2
                - projectOffBase normalFirst normalSecond
                    ⬝ᵥ projectOffBase normalFirst normalSecond) := by
  have hthirdRead := dotProduct_projectOffBase_of_orthogonal normalFirst normalSecond
    (design.atom 3) (horthSecond 3 (by decide))
  have hfourthRead := dotProduct_projectOffBase_of_orthogonal normalFirst normalSecond
    (design.atom 4) (horthSecond 4 (by decide))
  rw [oneFlat_planeCover_iff_freePairExcess design lineLabel 3 4 hdistinctThird
    hdistinctFourth (by decide) normalFirst (projectOffBase normalFirst normalSecond)
    (horthFirst lineLabel hlineFirstLine), hthirdRead, hfourthRead]
  constructor <;> intro hyp <;> nlinarith [hyp]


/-- The Lagrange identity for `bracketNormal`: the squared norm of the cross
product is the Gram determinant. -/
theorem bracketNormal_self_dotProduct (leftVec rightVec : Fin 3 → ℝ) :
    bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec
      = (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2 := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **An orthonormal frame of `ℝ³` has nonvanishing bracket.**  The normal is
forced onto the cross product of the two plane vectors, whose squared length is
one. -/
theorem tripleBracket_ne_zero_of_orthonormalFrame
    (planeFirst planeSecond unitNormal : Fin 3 → ℝ)
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hnormalUnit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstNormal : planeFirst ⬝ᵥ unitNormal = 0)
    (hsecondNormal : planeSecond ⬝ᵥ unitNormal = 0) :
    tripleBracket planeFirst planeSecond unitNormal ≠ 0 := by
  have hcrossNorm : bracketNormal planeFirst planeSecond
      ⬝ᵥ bracketNormal planeFirst planeSecond = 1 := by
    rw [bracketNormal_self_dotProduct, hfirstUnit, hsecondUnit, hfirstSecond]; ring
  have hcrossNe : bracketNormal planeFirst planeSecond ≠ 0 := by
    intro hzero
    rw [hzero] at hcrossNorm
    simp at hcrossNorm
  have hgrassmann :
      bracketNormal (bracketNormal planeFirst planeSecond) unitNormal = 0 := by
    rw [bracketNormal_bracketNormal, hfirstNormal, hsecondNormal, zero_smul, zero_smul,
      sub_zero]
  have hnormalScaled := eq_smul_of_bracketNormal_eq_zero
    (bracketNormal planeFirst planeSecond) unitNormal hcrossNe hgrassmann
  set scaleVal : ℝ := (bracketNormal planeFirst planeSecond ⬝ᵥ unitNormal)
      / (bracketNormal planeFirst planeSecond ⬝ᵥ bracketNormal planeFirst planeSecond)
    with hscaleVal
  have hnormSquare : scaleVal ^ 2 = 1 := by
    have hexpand := congrArg (fun vector : Fin 3 → ℝ => vector ⬝ᵥ vector) hnormalScaled
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at hexpand
    rw [hnormalUnit, hcrossNorm] at hexpand
    nlinarith [hexpand]
  have hbracketValue : tripleBracket planeFirst planeSecond unitNormal = scaleVal := by
    rw [tripleBracket_eq_bracketNormal_dotProduct, hnormalScaled, dotProduct_smul,
      smul_eq_mul, hcrossNorm, mul_one]
  rw [hbracketValue]
  intro hzero
  rw [hzero] at hnormSquare
  norm_num at hnormSquare

/-- **Frame completeness in the plane.**  A probe annihilating the normal is the
frame combination of its two in-plane readings. -/
theorem inPlaneProbe_eq_frameCombination
    (planeFirst planeSecond unitNormal probe : Fin 3 → ℝ)
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hnormalUnit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstNormal : planeFirst ⬝ᵥ unitNormal = 0)
    (hsecondNormal : planeSecond ⬝ᵥ unitNormal = 0)
    (hprobeFlat : probe ⬝ᵥ unitNormal = 0) :
    probe = (probe ⬝ᵥ planeFirst) • planeFirst + (probe ⬝ᵥ planeSecond) • planeSecond := by
  set residual : Fin 3 → ℝ :=
    probe - ((probe ⬝ᵥ planeFirst) • planeFirst + (probe ⬝ᵥ planeSecond) • planeSecond)
    with hresidual
  have hfirstOrth : planeFirst ⬝ᵥ residual = 0 := by
    rw [hresidual, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul,
      hfirstUnit, hfirstSecond, dotProduct_comm planeFirst probe]
    simp
  have hsecondOrth : planeSecond ⬝ᵥ residual = 0 := by
    rw [hresidual, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul,
      hsecondUnit, dotProduct_comm planeSecond planeFirst, hfirstSecond,
      dotProduct_comm planeSecond probe]
    simp
  have hnormalOrth : unitNormal ⬝ᵥ residual = 0 := by
    rw [hresidual, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_comm unitNormal planeFirst, hfirstNormal,
      dotProduct_comm unitNormal planeSecond, hsecondNormal,
      dotProduct_comm unitNormal probe, hprobeFlat]
    simp
  have hresidualZero : residual = 0 := by
    by_contra hne
    exact tripleBracket_ne_zero_of_orthonormalFrame planeFirst planeSecond unitNormal
      hfirstUnit hsecondUnit hnormalUnit hfirstSecond hfirstNormal hsecondNormal
      (tripleBracket_eq_zero_of_commonOrthogonal hne hfirstOrth hsecondOrth hnormalOrth)
  exact sub_eq_zero.mp hresidualZero


/-- **The cover form.**  The symmetric bilinear form on `ℝ³` whose positivity on
the normal's plane IS the plane-cover hypothesis of the uniform Schur producer:
the normal surplus times the coverage defect, minus the product of the two
cross-couplings. -/
noncomputable def coverForm {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal firstVec secondVec : Fin 3 → ℝ) : ℝ :=
  ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
      * ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ firstVec)
            * (design.atom selectedLabel ⬝ᵥ secondVec)) - firstVec ⬝ᵥ secondVec)
    - (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ firstVec)
          * (design.atom selectedLabel ⬝ᵥ unitNormal))
      * (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ secondVec)
          * (design.atom selectedLabel ⬝ᵥ unitNormal))

/-- The plane-cover inequality at a probe is exactly positivity of the diagonal
cover form there. -/
theorem planeCoverAt_iff_coverForm_pos {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal probe : Fin 3 → ℝ) :
    (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
          * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
        < ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe) ^ 2)
              - probe ⬝ᵥ probe)
      ↔ 0 < coverForm design selected unitNormal probe probe := by
  rw [coverForm]
  have hsquare : ∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
        * (design.atom selectedLabel ⬝ᵥ probe)
      = ∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe) ^ 2 :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [hsquare]
  constructor <;> intro hyp <;> nlinarith [hyp]

/-- **The cover form is a quadratic form on the frame.**  Its value at a
combination of two directions expands with the three frame minors as
coefficients. -/
theorem coverForm_frameCombination {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal firstVec secondVec : Fin 3 → ℝ)
    (firstCoord secondCoord : ℝ) :
    coverForm design selected unitNormal
        (firstCoord • firstVec + secondCoord • secondVec)
        (firstCoord • firstVec + secondCoord • secondVec)
      = firstCoord ^ 2 * coverForm design selected unitNormal firstVec firstVec
        + 2 * firstCoord * secondCoord
          * coverForm design selected unitNormal firstVec secondVec
        + secondCoord ^ 2 * coverForm design selected unitNormal secondVec secondVec := by
  have hread : ∀ selectedLabel : Fin size,
      design.atom selectedLabel ⬝ᵥ (firstCoord • firstVec + secondCoord • secondVec)
        = firstCoord * (design.atom selectedLabel ⬝ᵥ firstVec)
          + secondCoord * (design.atom selectedLabel ⬝ᵥ secondVec) := by
    intro selectedLabel
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp [smul_eq_mul]
  have hquad : ∑ selectedLabel ∈ selected,
        (design.atom selectedLabel ⬝ᵥ (firstCoord • firstVec + secondCoord • secondVec))
          * (design.atom selectedLabel ⬝ᵥ (firstCoord • firstVec + secondCoord • secondVec))
      = firstCoord ^ 2 * (∑ selectedLabel ∈ selected,
            (design.atom selectedLabel ⬝ᵥ firstVec) * (design.atom selectedLabel ⬝ᵥ firstVec))
        + 2 * firstCoord * secondCoord * (∑ selectedLabel ∈ selected,
            (design.atom selectedLabel ⬝ᵥ firstVec) * (design.atom selectedLabel ⬝ᵥ secondVec))
        + secondCoord ^ 2 * (∑ selectedLabel ∈ selected,
            (design.atom selectedLabel ⬝ᵥ secondVec)
              * (design.atom selectedLabel ⬝ᵥ secondVec)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun selectedLabel _ => ?_
    rw [hread selectedLabel]
    ring
  have hcross : ∑ selectedLabel ∈ selected,
        (design.atom selectedLabel ⬝ᵥ (firstCoord • firstVec + secondCoord • secondVec))
          * (design.atom selectedLabel ⬝ᵥ unitNormal)
      = firstCoord * (∑ selectedLabel ∈ selected,
            (design.atom selectedLabel ⬝ᵥ firstVec) * (design.atom selectedLabel ⬝ᵥ unitNormal))
        + secondCoord * (∑ selectedLabel ∈ selected,
            (design.atom selectedLabel ⬝ᵥ secondVec)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun selectedLabel _ => ?_
    rw [hread selectedLabel]
    ring
  have hnorm : (firstCoord • firstVec + secondCoord • secondVec)
        ⬝ᵥ (firstCoord • firstVec + secondCoord • secondVec)
      = firstCoord ^ 2 * (firstVec ⬝ᵥ firstVec)
        + 2 * firstCoord * secondCoord * (firstVec ⬝ᵥ secondVec)
        + secondCoord ^ 2 * (secondVec ⬝ᵥ secondVec) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm secondVec firstVec]
    ring
  rw [coverForm, coverForm, coverForm, coverForm, hquad, hcross, hnorm]
  ring


/-! ## The two-by-two determinant-and-trace criterion -/

/-- **The plane cover is a two-by-two positivity.**  Against ANY orthonormal
frame of the normal's plane, the cover at every nonzero in-plane probe is
EQUIVALENT to two scalar inequalities: one diagonal frame minor positive, and
the two-by-two determinant of the cover form positive.  The probe quantifier is
eliminated. -/
theorem planeCover_iff_frameMinors {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size))
    (planeFirst planeSecond unitNormal : Fin 3 → ℝ)
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hnormalUnit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstNormal : planeFirst ⬝ᵥ unitNormal = 0)
    (hsecondNormal : planeSecond ⬝ᵥ unitNormal = 0) :
    (∀ probe : Fin 3 → ℝ, probe ⬝ᵥ unitNormal = 0 → probe ≠ 0 →
        0 < coverForm design selected unitNormal probe probe)
      ↔ 0 < coverForm design selected unitNormal planeFirst planeFirst
        ∧ 0 < coverForm design selected unitNormal planeFirst planeFirst
                * coverForm design selected unitNormal planeSecond planeSecond
              - coverForm design selected unitNormal planeFirst planeSecond ^ 2 := by
  have hfirstNe : planeFirst ≠ 0 := by
    intro hzero; rw [hzero] at hfirstUnit; simp at hfirstUnit
  constructor
  · intro hcover
    have hdiagonalPos := hcover planeFirst hfirstNormal hfirstNe
    refine ⟨hdiagonalPos, ?_⟩
    set minorFirstFirst := coverForm design selected unitNormal planeFirst planeFirst
      with hminorFirstFirst
    set minorFirstSecond := coverForm design selected unitNormal planeFirst planeSecond
      with hminorFirstSecond
    set minorSecondSecond := coverForm design selected unitNormal planeSecond planeSecond
      with hminorSecondSecond
    set witnessProbe : Fin 3 → ℝ :=
      (-minorFirstSecond) • planeFirst + minorFirstFirst • planeSecond with hwitnessProbe
    have hwitnessFlat : witnessProbe ⬝ᵥ unitNormal = 0 := by
      rw [hwitnessProbe, add_dotProduct, smul_dotProduct, smul_dotProduct, hfirstNormal,
        hsecondNormal]
      simp
    have hwitnessNe : witnessProbe ≠ 0 := by
      intro hzero
      have hagainstSecond : witnessProbe ⬝ᵥ planeSecond = 0 := by rw [hzero]; simp
      rw [hwitnessProbe, add_dotProduct, smul_dotProduct, smul_dotProduct, hfirstSecond,
        hsecondUnit] at hagainstSecond
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hagainstSecond
      exact absurd hagainstSecond (ne_of_gt hdiagonalPos)
    have hwitnessValue := hcover witnessProbe hwitnessFlat hwitnessNe
    rw [hwitnessProbe, coverForm_frameCombination] at hwitnessValue
    nlinarith [hwitnessValue, hdiagonalPos]
  · rintro ⟨hdiagonalPos, hdeterminantPos⟩ probe hprobeFlat hprobeNe
    have hexpansion := inPlaneProbe_eq_frameCombination planeFirst planeSecond unitNormal probe
      hfirstUnit hsecondUnit hnormalUnit hfirstSecond hfirstNormal hsecondNormal hprobeFlat
    have hvalue := coverForm_frameCombination design selected unitNormal planeFirst planeSecond
      (probe ⬝ᵥ planeFirst) (probe ⬝ᵥ planeSecond)
    rw [← hexpansion] at hvalue
    have hnotBothZero : ¬ (probe ⬝ᵥ planeFirst = 0 ∧ probe ⬝ᵥ planeSecond = 0) := by
      rintro ⟨hfirstCoordZero, hsecondCoordZero⟩
      exact hprobeNe (by rw [hexpansion, hfirstCoordZero, hsecondCoordZero]; simp)
    rw [hvalue]
    rcases eq_or_ne (probe ⬝ᵥ planeSecond) 0 with hsecondCoordZero | hsecondCoordNe
    · have hfirstCoordNe : probe ⬝ᵥ planeFirst ≠ 0 := fun hzero =>
        hnotBothZero ⟨hzero, hsecondCoordZero⟩
      rw [hsecondCoordZero]
      have hsquarePos : 0 < (probe ⬝ᵥ planeFirst) ^ 2 := by positivity
      nlinarith [hsquarePos, hdiagonalPos]
    · have hsquarePos : 0 < (probe ⬝ᵥ planeSecond) ^ 2 := by positivity
      nlinarith [hdiagonalPos, hdeterminantPos, hsquarePos,
        sq_nonneg ((probe ⬝ᵥ planeFirst)
            * coverForm design selected unitNormal planeFirst planeFirst
          + (probe ⬝ᵥ planeSecond)
            * coverForm design selected unitNormal planeFirst planeSecond)]


/-! ## The quantifier-free decision form, and the emptiness of the normal choice -/

/-- **The gap is positive definite iff three scalar inequalities hold.**  Fix any
orthonormal frame `(planeFirst, planeSecond, unitNormal)`.  Strict domination by
a selected subset is EXACTLY: normal surplus, one positive diagonal frame minor,
and a positive two-by-two determinant.  No probe quantifier survives. -/
theorem posDef_iff_surplus_and_frameMinors {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size))
    (planeFirst planeSecond unitNormal : Fin 3 → ℝ)
    (hfirstUnit : planeFirst ⬝ᵥ planeFirst = 1)
    (hsecondUnit : planeSecond ⬝ᵥ planeSecond = 1)
    (hnormalUnit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstSecond : planeFirst ⬝ᵥ planeSecond = 0)
    (hfirstNormal : planeFirst ⬝ᵥ unitNormal = 0)
    (hsecondNormal : planeSecond ⬝ᵥ unitNormal = 0) :
    (subsetSum design selected - 1).PosDef
      ↔ (1 < ∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2)
        ∧ 0 < coverForm design selected unitNormal planeFirst planeFirst
        ∧ 0 < coverForm design selected unitNormal planeFirst planeFirst
                * coverForm design selected unitNormal planeSecond planeSecond
              - coverForm design selected unitNormal planeFirst planeSecond ^ 2 := by
  constructor
  · intro hposDef
    obtain ⟨hsurplus, hcover⟩ :=
      normalSurplus_planeCover_of_posDef design selected unitNormal hnormalUnit hposDef
    refine ⟨hsurplus, ?_⟩
    exact (planeCover_iff_frameMinors design selected planeFirst planeSecond unitNormal
      hfirstUnit hsecondUnit hnormalUnit hfirstSecond hfirstNormal hsecondNormal).mp
      (fun probe hprobeFlat hprobeNe =>
        (planeCoverAt_iff_coverForm_pos design selected unitNormal probe).mp
          (hcover probe hprobeFlat hprobeNe))
  · rintro ⟨hsurplus, hminors⟩
    refine posDef_of_normalSurplus_planeCover design selected unitNormal hnormalUnit hsurplus ?_
    intro probe hprobeFlat hprobeNe
    exact (planeCoverAt_iff_coverForm_pos design selected unitNormal probe).mpr
      ((planeCover_iff_frameMinors design selected planeFirst planeSecond unitNormal
        hfirstUnit hsecondUnit hnormalUnit hfirstSecond hfirstNormal hsecondNormal).mpr
        hminors probe hprobeFlat hprobeNe)

/-- **The normal carries no content.**  A producer pair at ONE unit normal is a
producer pair at EVERY unit normal, because both are the same statement about
the gap.  Choosing a clever normal cannot help: the only content in the reduced
cover property is the choice of the card-three subset. -/
theorem producerPair_transfers_between_normals {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (sourceNormal targetNormal : Fin 3 → ℝ)
    (hsourceUnit : sourceNormal ⬝ᵥ sourceNormal = 1)
    (htargetUnit : targetNormal ⬝ᵥ targetNormal = 1)
    (hsourceSurplus : 1 < ∑ selectedLabel ∈ selected,
      (design.atom selectedLabel ⬝ᵥ sourceNormal) ^ 2)
    (hsourceCover : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ sourceNormal = 0 → probe ≠ 0 →
      (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
          * (design.atom selectedLabel ⬝ᵥ sourceNormal)) ^ 2
        < ((∑ selectedLabel ∈ selected,
              (design.atom selectedLabel ⬝ᵥ sourceNormal) ^ 2) - 1)
          * ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe) ^ 2)
              - probe ⬝ᵥ probe)) :
    (1 < ∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ targetNormal) ^ 2)
      ∧ ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ targetNormal = 0 → probe ≠ 0 →
          (∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ targetNormal)) ^ 2
            < ((∑ selectedLabel ∈ selected,
                  (design.atom selectedLabel ⬝ᵥ targetNormal) ^ 2) - 1)
              * ((∑ selectedLabel ∈ selected, (design.atom selectedLabel ⬝ᵥ probe) ^ 2)
                  - probe ⬝ᵥ probe) :=
  normalSurplus_planeCover_of_posDef design selected targetNormal htargetUnit
    (posDef_of_normalSurplus_planeCover design selected sourceNormal hsourceUnit
      hsourceSurplus hsourceCover)

open Matrix



theorem oneLineSample_notPosDef_013 :
    ¬ (subsetSum oneLineSampleDesign ({0, 1, 3} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 0 1 3
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hpairArea

theorem oneLineSample_notPosDef_014 :
    ¬ (subsetSum oneLineSampleDesign ({0, 1, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 0 1 4
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hpairArea

theorem oneLineSample_notPosDef_015 :
    ¬ (subsetSum oneLineSampleDesign ({0, 1, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 0 1 5
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hpairArea

theorem oneLineSample_notPosDef_023 :
    ¬ (subsetSum oneLineSampleDesign ({0, 2, 3} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 0 2 3
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hpairArea

theorem oneLineSample_notPosDef_123 :
    ¬ (subsetSum oneLineSampleDesign ({1, 2, 3} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 1 2 3
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hpairArea

theorem oneLineSample_notPosDef_024 :
    ¬ (subsetSum oneLineSampleDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 0 2 4
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hdet

theorem oneLineSample_notPosDef_025 :
    ¬ (subsetSum oneLineSampleDesign ({0, 2, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 0 2 5
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hdet

theorem oneLineSample_notPosDef_124 :
    ¬ (subsetSum oneLineSampleDesign ({1, 2, 4} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 1 2 4
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hdet

theorem oneLineSample_notPosDef_125 :
    ¬ (subsetSum oneLineSampleDesign ({1, 2, 5} : Finset (Fin 6)) - 1).PosDef := by
  intro hposDef
  rw [subsetSum_sub_one_eq_gapOfDirectionTriple oneLineSampleDesign 1 2 5
    (by decide) (by decide) (by decide)] at hposDef
  obtain ⟨hleverage, hpairArea, hdet⟩ :=
    tripleInvariants_pos_of_posDef _ _ _ hposDef
  norm_num [tripleLeverageSum, triplePairAreaSum, crossNormSq, leverageOf, tripleBracket_eq,
    bracketNormal, dotProduct, Fin.sum_univ_three, oneLineSampleDesign, oneLineSampleAtom,
    Matrix.cons_val_two] at hdet


/-- **The LLF necessary condition, sharp.**  If a two-line-atom plus one-free-atom
subset covers at an in-plane probe, then the LINE PAIR ALONE strictly over-covers
the identity at that probe.  Pairwise non-parallelism does not supply this; on the
one-line sample no line pair supplies it at any probe, which is why all nine LLF
subsets there fail. -/
theorem twoFlat_linePair_overcovers_of_planeCover {size : ℕ} (design : WeightedDesign size 3)
    (lineFirst lineSecond freeLabel : Fin size)
    (hdistinctFirstSecond : lineFirst ≠ lineSecond)
    (hdistinctFirstFree : lineFirst ≠ freeLabel)
    (hdistinctSecondFree : lineSecond ≠ freeLabel)
    (unitNormal probe : Fin 3 → ℝ)
    (hfirstFlat : design.atom lineFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom lineSecond ⬝ᵥ unitNormal = 0)
    (hsurplus : 1 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2)
    (hcover : (∑ selectedLabel ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
            (design.atom selectedLabel ⬝ᵥ probe)
              * (design.atom selectedLabel ⬝ᵥ unitNormal)) ^ 2
          < ((∑ selectedLabel ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
                (design.atom selectedLabel ⬝ᵥ unitNormal) ^ 2) - 1)
            * ((∑ selectedLabel ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
                  (design.atom selectedLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) :
    probe ⬝ᵥ probe < (design.atom lineFirst ⬝ᵥ probe) ^ 2
      + (design.atom lineSecond ⬝ᵥ probe) ^ 2 := by
  have hreduced := (twoFlat_planeCover_iff_inPlaneExcess design lineFirst lineSecond freeLabel
    hdistinctFirstSecond hdistinctFirstFree hdistinctSecondFree unitNormal probe
    hfirstFlat hsecondFlat).mp hcover
  nlinarith [hreduced, hsurplus, sq_nonneg (design.atom freeLabel ⬝ᵥ probe)]

/-- **The landed LLF reduction has no instance at the sample's first line pair.**
Atoms `0` and `1` are orthonormal in the line plane, so their in-plane excess is
identically zero and the reduction's hypothesis fails at every in-plane probe --
witnessed at `![1, 0, 0]`, uniformly in the free atom. -/
theorem oneLineSample_firstLinePair_inPlaneExcess_fails (freeLabel : Fin 6) :
    ¬ ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ ![0, 0, 1] = 0 → probe ≠ 0 →
      (oneLineSampleDesign.atom freeLabel ⬝ᵥ probe) ^ 2
        < ((oneLineSampleDesign.atom freeLabel ⬝ᵥ ![0, 0, 1]) ^ 2 - 1)
          * ((oneLineSampleDesign.atom 0 ⬝ᵥ probe) ^ 2
              + (oneLineSampleDesign.atom 1 ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe) := by
  intro hexcess
  have hprobeNe : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomponent := congrFun hzero 0
    simp at hcomponent
  have hvalue := hexcess ![1, 0, 0] (by simp [dotProduct, Fin.sum_univ_three]) hprobeNe
  norm_num [oneLineSampleDesign, oneLineSampleAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two] at hvalue
  nlinarith [hvalue, sq_nonneg (oneLineSampleDesign.atom freeLabel 0)]


end Gtz

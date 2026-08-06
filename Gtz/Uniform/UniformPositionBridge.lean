/-
# The rank-two uniform-position bridge, and the route-(a)/(b) compositions

Everything new here is either uniform in the rank (the dependence dictionary)
or a base-case / cross-check instance.  Layers, in order:

1. **The uniform dependence dictionary**
   (`isDependentSelection_image_iff_det_eq_zero`): for an injectively picked
   rank-tuple of atom labels, dependence of the selection
   (`Gtz.InductionStep.IsDependentSelection`) is EXACTLY singularity of the
   picked row matrix — at every size and every rank at once.  The
   width-specific bracket forms are its determinant instances:
   `Gtz.pairBracket` at rank 2 and `Gtz.atomBracket` at rank 3, both
   converted below as two-sided iffs.

2. **NAMED GAP 4 CLOSED** (`rankTwoUniformPositionBridge_holds`): at rank 2,
   uniform position of four labels IS all six pair brackets nonzero, so
   `Gtz.rankTwoFourDirectionHinge_holds` delivers
   `Gtz.InductionStep.RankHingeUniformPosition 2` — the k = 2 base of the
   hinge tower, in kernel.  Hence H(2) in full
   (`strengthenedHypothesis_two_holds`).  Cross-check: the bridge returns the
   four-direction hinge statement shape
   (`rankTwoFourDirectionHinge_of_uniformPositionBridge`).

3. **The route-(a) composition, end to end** (`routeA_target`): with gap 4 a
   theorem, route (a) rests on exactly TWO named Props — gap 2
   (`RouteAWindowArrow`) and gap 3 (`RouteAHingeProduction`); their
   composition reaches weighted GTZ at every size and rank, and the original
   1997 statement.  Gap 2 is NOT dischargeable from the present corpus: with
   H(2) now a theorem its rank-3 instance is equivalent to
   `ClosesCanonicalWindow 3` itself
   (`closesCanonicalWindowThree_iff_routeAWindowArrowThree`), which is the
   open rank-3 content.

4. **The rank-3 hinge base slice**
   (`rankHingeUniformPositionThree_holdsAtCorankTwoCell`):
   `RankHingeUniformPosition 3` restricted to the corank-2 cell (5,3) is a
   THEOREM — uniform position forbids the shared line pair that
   `EndpointSpike.sharedLinePairAtEveryTie_holds` forces at every primitive
   tie.  What remains of the rank-3 hinge is exactly the named Prop
   `RankThreeHingeBeyondCorankTwoCell` (sizes >= 6).  Diamond control: the
   kernel-checked (5,3) tie is NOT in uniform position
   (`diamondDesign_not_isUniformPositionFamily`) — forced through the
   no-strict-dominator theorem, no bracket computation.

5. **Route (b), wired uniformly**
   (`closesCanonicalWindow_of_windowTie_of_reach`, `routeB_target`): the
   tie-reduction capstone `Gtz.gtzWeighted_of_hinge_of_reach` is fully
   generic in size and rank, so the window-cell hinge plus an anchored
   parallel-free reach close the whole canonical window by a size induction,
   the floor riding Naimark duality into the predecessor rank.
-/
import Mathlib
import Gtz.Uniform.InductionStep
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.RankTwoTieCriterion
import Gtz.Design.DiamondPrimitive
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Ties.SpikeMatroidObstruction
import Gtz.Reduction.Reductions
import Gtz.Reduction.ConnectednessRoute
import Gtz.Reduction.ParallelFreeReach

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace UniformPositionBridge

open Matrix Finset

/-! ## Layer 1: the uniform dependence dictionary

`Gtz.InductionStep.IsDependentSelection` speaks of coefficient vectors over
the whole label set; the bracket forms speak of determinants of picked rows.
The dictionary between them is one Gale-style reindexing, uniform in the
rank. -/

/-- The square row matrix of a picked rank-tuple of atoms. -/
def pickedRowMatrix {size rank : ℕ} (design : WeightedDesign size rank)
    (pick : Fin rank → Fin size) : Matrix (Fin rank) (Fin rank) ℝ :=
  Matrix.of fun rowIdx colIdx => design.atom (pick rowIdx) colIdx

@[simp] theorem pickedRowMatrix_apply {size rank : ℕ}
    (design : WeightedDesign size rank) (pick : Fin rank → Fin size)
    (rowIdx colIdx : Fin rank) :
    pickedRowMatrix design pick rowIdx colIdx = design.atom (pick rowIdx) colIdx :=
  rfl

/-- Spread a row-coefficient vector back over the whole label set along a pick:
the coefficient lands on the picked labels and vanishes everywhere else. -/
def spreadAlongPick {size rank : ℕ} (pick : Fin rank → Fin size)
    (coefficients : Fin rank → ℝ) : Fin size → ℝ :=
  fun label => ∑ rowIdx, if pick rowIdx = label then coefficients rowIdx else 0

/-- On a picked label the spread returns the row's own coefficient (injectivity
kills every other summand). -/
theorem spreadAlongPick_at_pick {size rank : ℕ} {pick : Fin rank → Fin size}
    (hinjective : Function.Injective pick) (coefficients : Fin rank → ℝ)
    (rowIdx : Fin rank) :
    spreadAlongPick pick coefficients (pick rowIdx) = coefficients rowIdx := by
  simp only [spreadAlongPick]
  rw [Finset.sum_eq_single rowIdx
    (fun otherRow _ hotherNe => if_neg fun hpickEq => hotherNe (hinjective hpickEq))
    (fun habsent => absurd (Finset.mem_univ rowIdx) habsent), if_pos rfl]

/-- Off the picked image the spread vanishes. -/
theorem spreadAlongPick_off_image {size rank : ℕ} (pick : Fin rank → Fin size)
    (coefficients : Fin rank → ℝ) {label : Fin size}
    (habsent : label ∉ Finset.image pick Finset.univ) :
    spreadAlongPick pick coefficients label = 0 := by
  simp only [spreadAlongPick]
  refine Finset.sum_eq_zero fun rowIdx _ => if_neg fun hpickEq => ?_
  exact habsent (Finset.mem_image.mpr ⟨rowIdx, Finset.mem_univ rowIdx, hpickEq⟩)

/-- **The uniform dependence dictionary.**  An injectively picked rank-tuple of
labels is a dependent selection iff its row matrix is singular — every size,
every rank.  Forward: a supported dependence restricts to a null row-mix.
Backward: a null row-mix spreads to a supported dependence.  Both directions
ride `Matrix.exists_vecMul_eq_zero_iff`. -/
theorem isDependentSelection_image_iff_det_eq_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (pick : Fin rank → Fin size)
    (hinjective : Function.Injective pick) :
    InductionStep.IsDependentSelection design (Finset.image pick Finset.univ)
      ↔ (pickedRowMatrix design pick).det = 0 := by
  constructor
  · rintro ⟨dependence, ⟨witnessLabel, hwitnessNonzero⟩, hsupport, hkill⟩
    refine Matrix.exists_vecMul_eq_zero_iff.mp
      ⟨fun rowIdx => dependence (pick rowIdx), ?_, ?_⟩
    · have hwitnessMem : witnessLabel ∈ Finset.image pick Finset.univ := by
        by_contra habsent
        exact hwitnessNonzero (hsupport witnessLabel habsent)
      obtain ⟨witnessRow, _, hpickWitness⟩ := Finset.mem_image.mp hwitnessMem
      intro hallZero
      apply hwitnessNonzero
      rw [← hpickWitness]
      exact congrFun hallZero witnessRow
    · funext colIdx
      have hkillCol : (∑ label, dependence label • design.atom label) colIdx = 0 := by
        rw [hkill]; rfl
      rw [Finset.sum_apply] at hkillCol
      simp only [Pi.smul_apply, smul_eq_mul] at hkillCol
      have hrestrict :
          ∑ label ∈ Finset.image pick Finset.univ,
              dependence label * design.atom label colIdx
            = ∑ label, dependence label * design.atom label colIdx :=
        Finset.sum_subset (Finset.subset_univ _)
          (fun label _ habsent => by rw [hsupport label habsent, zero_mul])
      have hreindex :
          ∑ label ∈ Finset.image pick Finset.univ,
              dependence label * design.atom label colIdx
            = ∑ rowIdx, dependence (pick rowIdx) * design.atom (pick rowIdx) colIdx :=
        Finset.sum_image (fun rowFirst _ rowSecond _ hpickEq => hinjective hpickEq)
      show (fun rowIdx => dependence (pick rowIdx)) ⬝ᵥ
          (fun rowIdx => pickedRowMatrix design pick rowIdx colIdx) = 0
      simp only [dotProduct, pickedRowMatrix_apply]
      rw [← hreindex, hrestrict]
      exact hkillCol
  · intro hdetZero
    obtain ⟨coefficients, hcoeffNonzero, hvecMulZero⟩ :=
      Matrix.exists_vecMul_eq_zero_iff.mpr hdetZero
    obtain ⟨witnessRow, hwitnessRowNonzero⟩ := Function.ne_iff.mp hcoeffNonzero
    have hdependenceOffPick : ∀ label : Fin size,
        label ∉ Finset.image pick Finset.univ →
        spreadAlongPick pick coefficients label = 0 :=
      fun label habsent => spreadAlongPick_off_image pick coefficients habsent
    have hpointwise : ∀ colIdx : Fin rank,
        (∑ label, spreadAlongPick pick coefficients label • design.atom label) colIdx
          = (0 : ℝ) := by
      intro colIdx
      have hvecMulCol : (coefficients ᵥ* pickedRowMatrix design pick) colIdx = 0 := by
        rw [hvecMulZero]; rfl
      simp only [Matrix.vecMul, dotProduct, pickedRowMatrix_apply] at hvecMulCol
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hrestrict :
          ∑ label ∈ Finset.image pick Finset.univ,
              spreadAlongPick pick coefficients label * design.atom label colIdx
            = ∑ label, spreadAlongPick pick coefficients label * design.atom label colIdx :=
        Finset.sum_subset (Finset.subset_univ _)
          (fun label _ habsent => by rw [hdependenceOffPick label habsent, zero_mul])
      have hreindex :
          ∑ label ∈ Finset.image pick Finset.univ,
              spreadAlongPick pick coefficients label * design.atom label colIdx
            = ∑ rowIdx, spreadAlongPick pick coefficients (pick rowIdx)
                * design.atom (pick rowIdx) colIdx :=
        Finset.sum_image (fun rowFirst _ rowSecond _ hpickEq => hinjective hpickEq)
      rw [← hrestrict, hreindex, ← hvecMulCol]
      exact Finset.sum_congr rfl fun rowIdx _ => by
        rw [spreadAlongPick_at_pick hinjective]
    refine ⟨spreadAlongPick pick coefficients, ⟨pick witnessRow, ?_⟩,
      hdependenceOffPick, ?_⟩
    · rw [spreadAlongPick_at_pick hinjective]
      simpa using hwitnessRowNonzero
    · funext colIdx
      exact hpointwise colIdx

/-! ### The rank-2 determinant instance: the `pairBracket` dictionary -/

theorem injective_pairPick {size : ℕ} {leftLabel rightLabel : Fin size}
    (hdistinct : leftLabel ≠ rightLabel) :
    Function.Injective ![leftLabel, rightLabel] := by
  intro firstIdx secondIdx hpickEq
  fin_cases firstIdx <;> fin_cases secondIdx <;> simp_all

theorem image_pairPick_eq {size : ℕ} (leftLabel rightLabel : Fin size) :
    Finset.image ![leftLabel, rightLabel] Finset.univ = {leftLabel, rightLabel} := by
  ext label
  simp [Fin.exists_fin_two, eq_comm]

theorem det_pickedRowMatrix_pair_eq_pairBracket {size : ℕ}
    (design : WeightedDesign size 2) (leftLabel rightLabel : Fin size) :
    (pickedRowMatrix design ![leftLabel, rightLabel]).det
      = pairBracket design leftLabel rightLabel := by
  rw [Matrix.det_fin_two]
  simp [pairBracket]

/-- **The rank-2 dictionary, two-sided** — the exact missing kernel content of
NAMED GAP 4: `pairBracket = 0` iff the pair is a dependent selection, at
general size. -/
theorem pairBracket_eq_zero_iff_isDependentSelection {size : ℕ}
    (design : WeightedDesign size 2) {leftLabel rightLabel : Fin size}
    (hdistinct : leftLabel ≠ rightLabel) :
    pairBracket design leftLabel rightLabel = 0
      ↔ InductionStep.IsDependentSelection design {leftLabel, rightLabel} := by
  rw [← det_pickedRowMatrix_pair_eq_pairBracket, ← image_pairPick_eq leftLabel rightLabel]
  exact (isDependentSelection_image_iff_det_eq_zero design _
    (injective_pairPick hdistinct)).symm

/-- Bracket antisymmetry transports nonzeroness across a swapped pair. -/
theorem pairBracket_ne_zero_swap {size : ℕ} (design : WeightedDesign size 2)
    {leftLabel rightLabel : Fin size}
    (hbracket : pairBracket design leftLabel rightLabel ≠ 0) :
    pairBracket design rightLabel leftLabel ≠ 0 := by
  intro hswapZero
  apply hbracket
  have hantisym : pairBracket design leftLabel rightLabel
      = -pairBracket design rightLabel leftLabel := by
    simp only [pairBracket]; ring
  rw [hantisym, hswapZero, neg_zero]

/-! ### The rank-3 determinant instance: the `atomBracket` dictionary -/

theorem injective_triplePick {size : ℕ} {leftLabel midLabel rightLabel : Fin size}
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    Function.Injective ![leftLabel, midLabel, rightLabel] := by
  intro firstIdx secondIdx hpickEq
  fin_cases firstIdx <;> fin_cases secondIdx <;> simp_all

theorem image_triplePick_eq {size : ℕ} (leftLabel midLabel rightLabel : Fin size) :
    Finset.image ![leftLabel, midLabel, rightLabel] Finset.univ
      = {leftLabel, midLabel, rightLabel} := by
  ext label
  constructor
  · intro hmem
    obtain ⟨pickIdx, _, hpickEq⟩ := Finset.mem_image.mp hmem
    fin_cases pickIdx <;> simp_all
  · intro hmem
    rcases Finset.mem_insert.mp hmem with rfl | hrest
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    rcases Finset.mem_insert.mp hrest with rfl | hlast
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    · rw [Finset.mem_singleton.mp hlast]
      exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩

theorem det_pickedRowMatrix_triple_eq_atomBracket {size : ℕ}
    (design : WeightedDesign size 3) (leftLabel midLabel rightLabel : Fin size) :
    (pickedRowMatrix design ![leftLabel, midLabel, rightLabel]).det
      = atomBracket design leftLabel midLabel rightLabel := by
  simp only [atomBracket, tripleBracket]
  congr 1
  ext rowIdx colIdx
  fin_cases rowIdx <;> simp [pickedRowMatrix]

/-- **The rank-3 dictionary, two-sided**: `atomBracket = 0` iff the triple is a
dependent selection, at general size.  The forward half is the converse of
`EndpointSpike.tripleBracket_eq_zero_of_dependence`; it is what lets uniform
position consume the shared-line-pair law below. -/
theorem atomBracket_eq_zero_iff_isDependentSelection {size : ℕ}
    (design : WeightedDesign size 3) {leftLabel midLabel rightLabel : Fin size}
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    atomBracket design leftLabel midLabel rightLabel = 0
      ↔ InductionStep.IsDependentSelection design {leftLabel, midLabel, rightLabel} := by
  rw [← det_pickedRowMatrix_triple_eq_atomBracket,
    ← image_triplePick_eq leftLabel midLabel rightLabel]
  exact (isDependentSelection_image_iff_det_eq_zero design _
    (injective_triplePick hleftMid hleftRight hmidRight)).symm

/-! ## Layer 2: NAMED GAP 4 CLOSED — the rank-2 uniform-position bridge -/

/-- **The primal-side dictionary, forward half, uniform in the chosen set**:
uniform position of any label family at rank 2 forces every pair bracket inside
it to be nonzero.  (`CorankTwo.dependence_of_completion_mix` carries the
DUAL-side halves on Naimark completions; this is the primal surface form the
hinge Prop needs.) -/
theorem pairBracket_ne_zero_of_uniformPosition {size : ℕ} (design : WeightedDesign size 2)
    {chosen : Finset (Fin size)}
    (huniform : InductionStep.IsUniformPositionFamily design chosen)
    {leftLabel rightLabel : Fin size} (hleftMem : leftLabel ∈ chosen)
    (hrightMem : rightLabel ∈ chosen) (hdistinct : leftLabel ≠ rightLabel) :
    pairBracket design leftLabel rightLabel ≠ 0 := by
  intro hbracketZero
  exact huniform {leftLabel, rightLabel}
    (Finset.insert_subset hleftMem (Finset.singleton_subset_iff.mpr hrightMem))
    (Finset.card_pair hdistinct)
    ((pairBracket_eq_zero_iff_isDependentSelection design hdistinct).mp hbracketZero)

/-- **The primal-side dictionary, backward half**: six nonzero pair brackets on
four distinct labels put them in uniform position. -/
theorem isUniformPositionFamily_of_sixBracketsNonzero {size : ℕ}
    (design : WeightedDesign size 2)
    {firstLabel secondLabel thirdLabel fourthLabel : Fin size}
    (hbracketOne : pairBracket design firstLabel secondLabel ≠ 0)
    (hbracketTwo : pairBracket design firstLabel thirdLabel ≠ 0)
    (hbracketThree : pairBracket design firstLabel fourthLabel ≠ 0)
    (hbracketFour : pairBracket design secondLabel thirdLabel ≠ 0)
    (hbracketFive : pairBracket design secondLabel fourthLabel ≠ 0)
    (hbracketSix : pairBracket design thirdLabel fourthLabel ≠ 0) :
    InductionStep.IsUniformPositionFamily design
      {firstLabel, secondLabel, thirdLabel, fourthLabel} := by
  have hswapOne := pairBracket_ne_zero_swap design hbracketOne
  have hswapTwo := pairBracket_ne_zero_swap design hbracketTwo
  have hswapThree := pairBracket_ne_zero_swap design hbracketThree
  have hswapFour := pairBracket_ne_zero_swap design hbracketFour
  have hswapFive := pairBracket_ne_zero_swap design hbracketFive
  have hswapSix := pairBracket_ne_zero_swap design hbracketSix
  intro subset hsubsetChosen hsubsetCard hdependent
  obtain ⟨leftLabel, rightLabel, hdistinct, hsubsetEq⟩ :=
    Finset.card_eq_two.mp hsubsetCard
  rw [hsubsetEq] at hdependent hsubsetChosen
  have hbracketZero : pairBracket design leftLabel rightLabel = 0 :=
    (pairBracket_eq_zero_iff_isDependentSelection design hdistinct).mpr hdependent
  have hleftChosen := hsubsetChosen (Finset.mem_insert_self _ _)
  have hrightChosen := hsubsetChosen
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hleftChosen hrightChosen
  rcases hleftChosen with rfl | rfl | rfl | rfl <;>
    rcases hrightChosen with rfl | rfl | rfl | rfl <;>
    first
      | exact hdistinct rfl
      | exact hbracketOne hbracketZero
      | exact hbracketTwo hbracketZero
      | exact hbracketThree hbracketZero
      | exact hbracketFour hbracketZero
      | exact hbracketFive hbracketZero
      | exact hbracketSix hbracketZero
      | exact hswapOne hbracketZero
      | exact hswapTwo hbracketZero
      | exact hswapThree hbracketZero
      | exact hswapFour hbracketZero
      | exact hswapFive hbracketZero
      | exact hswapSix hbracketZero

/-- **THE RANK-2 IDENTITY, VERIFIED NOT ASSERTED.**  On four distinct labels
the uniform-position premise and the four-direction hinge's
six-nonzero-brackets premise are THE SAME CONDITION — and the identity is
non-vacuous (unlike an iff between two proved Props): it is a design-local
equivalence of two hypotheses. -/
theorem isUniformPositionFamily_iff_sixBracketsNonzero {size : ℕ}
    (design : WeightedDesign size 2)
    {firstLabel secondLabel thirdLabel fourthLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hfirstFourth : firstLabel ≠ fourthLabel) (hsecondThird : secondLabel ≠ thirdLabel)
    (hsecondFourth : secondLabel ≠ fourthLabel) (hthirdFourth : thirdLabel ≠ fourthLabel) :
    InductionStep.IsUniformPositionFamily design
        {firstLabel, secondLabel, thirdLabel, fourthLabel}
      ↔ pairBracket design firstLabel secondLabel ≠ 0
        ∧ pairBracket design firstLabel thirdLabel ≠ 0
        ∧ pairBracket design firstLabel fourthLabel ≠ 0
        ∧ pairBracket design secondLabel thirdLabel ≠ 0
        ∧ pairBracket design secondLabel fourthLabel ≠ 0
        ∧ pairBracket design thirdLabel fourthLabel ≠ 0 := by
  constructor
  · intro huniform
    have hmemFirst : firstLabel ∈ ({firstLabel, secondLabel, thirdLabel, fourthLabel} :
        Finset (Fin size)) := by simp
    have hmemSecond : secondLabel ∈ ({firstLabel, secondLabel, thirdLabel, fourthLabel} :
        Finset (Fin size)) := by simp
    have hmemThird : thirdLabel ∈ ({firstLabel, secondLabel, thirdLabel, fourthLabel} :
        Finset (Fin size)) := by simp
    have hmemFourth : fourthLabel ∈ ({firstLabel, secondLabel, thirdLabel, fourthLabel} :
        Finset (Fin size)) := by simp
    exact ⟨pairBracket_ne_zero_of_uniformPosition design huniform hmemFirst hmemSecond
        hfirstSecond,
      pairBracket_ne_zero_of_uniformPosition design huniform hmemFirst hmemThird hfirstThird,
      pairBracket_ne_zero_of_uniformPosition design huniform hmemFirst hmemFourth hfirstFourth,
      pairBracket_ne_zero_of_uniformPosition design huniform hmemSecond hmemThird hsecondThird,
      pairBracket_ne_zero_of_uniformPosition design huniform hmemSecond hmemFourth
        hsecondFourth,
      pairBracket_ne_zero_of_uniformPosition design huniform hmemThird hmemFourth
        hthirdFourth⟩
  · rintro ⟨hbracketOne, hbracketTwo, hbracketThree, hbracketFour, hbracketFive,
      hbracketSix⟩
    exact isUniformPositionFamily_of_sixBracketsNonzero design hbracketOne hbracketTwo
      hbracketThree hbracketFour hbracketFive hbracketSix

/-- **NAMED GAP 4 IS A THEOREM.**  At rank 2, uniform position of four labels
is exactly "all six pair brackets nonzero" (the identity above), so
`Gtz.rankTwoFourDirectionHinge_holds` delivers the uniform-position hinge at
rank 2 — the base of the hinge tower. -/
theorem rankTwoUniformPositionBridge_holds : InductionStep.RankTwoUniformPositionBridge := by
  intro size design chosen hchosenCard huniform
  have hbracketOfChosenPair : ∀ {leftLabel rightLabel : Fin size},
      leftLabel ∈ chosen → rightLabel ∈ chosen → leftLabel ≠ rightLabel →
      pairBracket design leftLabel rightLabel ≠ 0 :=
    fun hleftMem hrightMem hdistinct =>
      pairBracket_ne_zero_of_uniformPosition design huniform hleftMem hrightMem hdistinct
  have hchosenNonempty : chosen.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨firstLabel, hfirstMem⟩ := hchosenNonempty
  have herasedCard : (chosen.erase firstLabel).card = 3 := by
    rw [Finset.card_erase_of_mem hfirstMem]
    omega
  obtain ⟨secondLabel, thirdLabel, fourthLabel, hsecondThird, hsecondFourth,
    hthirdFourth, herasedEq⟩ := Finset.card_eq_three.mp herasedCard
  have hsecondErase : secondLabel ∈ chosen.erase firstLabel := by
    rw [herasedEq]; exact Finset.mem_insert_self _ _
  have hthirdErase : thirdLabel ∈ chosen.erase firstLabel := by
    rw [herasedEq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hfourthErase : fourthLabel ∈ chosen.erase firstLabel := by
    rw [herasedEq]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨hsecondNeFirst, hsecondMem⟩ := Finset.mem_erase.mp hsecondErase
  obtain ⟨hthirdNeFirst, hthirdMem⟩ := Finset.mem_erase.mp hthirdErase
  obtain ⟨hfourthNeFirst, hfourthMem⟩ := Finset.mem_erase.mp hfourthErase
  exact rankTwoFourDirectionHinge_holds size design
    firstLabel secondLabel thirdLabel fourthLabel
    hsecondNeFirst.symm hthirdNeFirst.symm hfourthNeFirst.symm
    hsecondThird hsecondFourth hthirdFourth
    (hbracketOfChosenPair hfirstMem hsecondMem hsecondNeFirst.symm)
    (hbracketOfChosenPair hfirstMem hthirdMem hthirdNeFirst.symm)
    (hbracketOfChosenPair hfirstMem hfourthMem hfourthNeFirst.symm)
    (hbracketOfChosenPair hsecondMem hthirdMem hsecondThird)
    (hbracketOfChosenPair hsecondMem hfourthMem hsecondFourth)
    (hbracketOfChosenPair hthirdMem hfourthMem hthirdFourth)

/-- **The k = 2 base of the hinge tower, in kernel.** -/
theorem rankHingeUniformPosition_two_holds : InductionStep.RankHingeUniformPosition 2 :=
  rankTwoUniformPositionBridge_holds

/-- **H(2) in full**: both slots of the strengthened induction hypothesis at
rank 2 are theorems — the weighted theorem (`Gtz.gtz_rank_two`) and now the
uniform-position hinge. -/
theorem strengthenedHypothesis_two_holds : InductionStep.StrengthenedHypothesis 2 :=
  ⟨gtz_rank_two, rankHingeUniformPosition_two_holds⟩

/-- **Cross-check, round trip**: the bridge returns the hinge statement shape
`Gtz.RankTwoFourDirectionHinge` — proved HERE from
`rankHingeUniformPosition_two_holds`, not from
`Gtz.rankTwoFourDirectionHinge_holds`, certifying that the two Props carry
the same content. -/
theorem rankTwoFourDirectionHinge_of_uniformPositionBridge : RankTwoFourDirectionHinge := by
  intro size design firstLabel secondLabel thirdLabel fourthLabel
    hfirstSecond hfirstThird hfirstFourth hsecondThird hsecondFourth hthirdFourth
    hbracketOne hbracketTwo hbracketThree hbracketFour hbracketFive hbracketSix
  refine rankHingeUniformPosition_two_holds size design
    {firstLabel, secondLabel, thirdLabel, fourthLabel} ?_
    ((isUniformPositionFamily_iff_sixBracketsNonzero design hfirstSecond hfirstThird
      hfirstFourth hsecondThird hsecondFourth hthirdFourth).mpr
      ⟨hbracketOne, hbracketTwo, hbracketThree, hbracketFour, hbracketFive, hbracketSix⟩)
  rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird, hfirstFourth]),
    Finset.card_insert_of_notMem (by simp [hsecondThird, hsecondFourth]),
    Finset.card_pair hthirdFourth]

/-! ## Layer 3: the route-(a) composition, end to end

With gap 4 a theorem, route (a) rests on exactly TWO named Props — gap 2
(`RouteAWindowArrow`) and gap 3 (`RouteAHingeProduction`); the composition
machinery of `Gtz.Uniform.InductionStep` carries them to the full conjecture.
HONESTY: gap 2 is not dischargeable from the present corpus — with H(2) now
free, its rank-3 instance is EQUIVALENT to `ClosesCanonicalWindow 3`
(recorded below), which is the open rank-3 content (the stress-free hinge
chain).  The sharpest single-Prop form remains gap 1
(`WindowArrowFromPredecessorWeighted`). -/

/-- Route (a) with G4 discharged: the strengthened hypothesis H(rank)
propagates up the whole tower from the now-unconditional base H(2). -/
theorem forall_strengthenedHypothesis_of_twoGaps
    (harrow : InductionStep.RouteAWindowArrow)
    (hproduction : InductionStep.RouteAHingeProduction) :
    ∀ rank : ℕ, 2 ≤ rank → InductionStep.StrengthenedHypothesis rank :=
  InductionStep.forall_strengthenedHypothesis_of_routeA harrow hproduction
    rankTwoUniformPositionBridge_holds

/-- **THE ROUTE-(a) TARGET, wired end to end**: the two remaining named
productions, gaps 2 + 3, alone yield weighted GTZ at every size and every
rank. -/
theorem routeA_target
    (harrow : InductionStep.RouteAWindowArrow)
    (hproduction : InductionStep.RouteAHingeProduction) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank :=
  fun size rank hrankPos _ =>
    InductionStep.forall_gtzWeightedAll_of_routeA harrow hproduction
      rankTwoUniformPositionBridge_holds rank hrankPos size

/-- The route-(a) target in the original 1997 coordinates. -/
theorem routeA_target_original
    (harrow : InductionStep.RouteAWindowArrow)
    (hproduction : InductionStep.RouteAHingeProduction) :
    ∀ sizeParam rank : ℕ, 1 ≤ rank → 0 < sizeParam → GtzOriginal sizeParam rank :=
  fun sizeParam rank hrankPos hsizePos =>
    original_of_weighted rank
      (InductionStep.forall_gtzWeightedAll_of_routeA harrow hproduction
        rankTwoUniformPositionBridge_holds rank hrankPos) sizeParam hsizePos

/-- **Gap 2's rank-3 instance is the window closure itself**: because H(2) is
now a theorem, the premise of the route-(a) arrow at rank 3 is free, and the
instance collapses to `ClosesCanonicalWindow 3` — no weakening survives.
This is the kernel record that gap 4's closure moves the entire route-(a)
residual into the window closures. -/
theorem closesCanonicalWindowThree_iff_routeAWindowArrowThree :
    (InductionStep.StrengthenedHypothesis 2 → InductionStep.ClosesCanonicalWindow 3)
      ↔ InductionStep.ClosesCanonicalWindow 3 :=
  ⟨fun harrowThree => harrowThree strengthenedHypothesis_two_holds,
    fun hwindow _ => hwindow⟩

/-! ## Layer 4: the rank-3 hinge — the corank-2 slice is a theorem

`RankHingeUniformPosition 3` quantifies over ALL sizes; it is a sibling of,
not a consequence of, the (6,3)-specific `Gtz.StressFreeHingeHoldsSixThree`
(the uniform-position hinge speaks of 5 chosen labels at every size with a
VECTOR-matroid hypothesis and a strict-domination conclusion; the stress-free
hinge speaks of all 6 atoms of a (6,3) design with a MATRIX-independence
hypothesis and a parallel-pair conclusion — neither hypothesis implies the
other, and neither conclusion).  The size-5 slice, however, is a theorem:
uniform position of all five atoms forbids the shared line pair that every
primitive (5,3) tie must carry
(`EndpointSpike.sharedLinePairAtEveryTie_holds`), and the weak dominator is
`Gtz.gtzWeighted_of_le_five`, so no strict dominator would force a tie and
refute itself. -/

/-- Uniform position of all five atoms of a (5,3) design forces primitivity:
a parallel pair extends to a dependent triple. -/
theorem isPrimitiveDesign_of_uniformPosition_fiveThree (design : WeightedDesign 5 3)
    (huniform : InductionStep.IsUniformPositionFamily design Finset.univ) :
    IsPrimitiveDesign design := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  obtain ⟨offLabel, hoffKept, hoffDrop⟩ : ∃ offLabel : Fin 5,
      offLabel ≠ keptLabel ∧ offLabel ≠ dropLabel := by
    by_contra hnone
    push Not at hnone
    have hcover : (Finset.univ : Finset (Fin 5)) ⊆ {keptLabel, dropLabel} := by
      intro label _
      rcases eq_or_ne label keptLabel with rfl | hlabelNe
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hnone label hlabelNe))
    have hcardBound := Finset.card_le_card hcover
    have hpairCard : ({keptLabel, dropLabel} : Finset (Fin 5)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at hcardBound
    omega
  refine huniform {keptLabel, dropLabel, offLabel} (Finset.subset_univ _) ?_ ?_
  · rw [Finset.card_insert_of_notMem (by simp [hdistinct, (Ne.symm hoffKept)]),
      Finset.card_pair (Ne.symm hoffDrop)]
  · refine ⟨fun label => if label = dropLabel then -1
        else if label = keptLabel then ratio else 0, ⟨dropLabel, by simp⟩, ?_, ?_⟩
    · intro label hlabelOut
      have hlabelNeDrop : label ≠ dropLabel := fun heq =>
        hlabelOut (heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hlabelNeKept : label ≠ keptLabel := fun heq =>
        hlabelOut (heq ▸ Finset.mem_insert_self _ _)
      simp [hlabelNeDrop, hlabelNeKept]
    · have hoffSupport : ∀ label ∈ (Finset.univ : Finset (Fin 5)),
          label ∉ ({dropLabel, keptLabel} : Finset (Fin 5)) →
          (if label = dropLabel then (-1 : ℝ)
            else if label = keptLabel then ratio else 0) • design.atom label = 0 := by
        intro label _ hlabelOut
        simp only [Finset.mem_insert, Finset.mem_singleton] at hlabelOut
        push Not at hlabelOut
        simp [hlabelOut.1, hlabelOut.2]
      rw [← Finset.sum_subset (Finset.subset_univ _) hoffSupport,
        Finset.sum_pair (Ne.symm hdistinct)]
      simp only [if_neg hdistinct, if_neg (Ne.symm hdistinct)]
      rw [hparallel]
      simp

/-- **The rank-3 hinge holds at the corank-2 cell (5,3)** — the size-5 slice
of `RankHingeUniformPosition 3`: no strict dominator would make the design a
tie (`gtzWeighted_of_le_five` supplies the weak dominator), the tie is
primitive (uniform position), and every primitive (5,3) tie carries a shared
line pair — a dependent triple that uniform position forbids. -/
theorem rankHingeUniformPositionThree_holdsAtCorankTwoCell :
    ∀ (design : WeightedDesign 5 3) (chosen : Finset (Fin 5)),
      chosen.card = 5 → InductionStep.IsUniformPositionFamily design chosen →
      ∃ dominating : Finset (Fin 5),
        dominating.card = 3 ∧ (subsetSum design dominating - 1).PosDef := by
  intro design chosen hchosenCard huniformChosen
  have hchosenUniv : chosen = Finset.univ :=
    Finset.eq_univ_of_card chosen (by rw [hchosenCard, Fintype.card_fin])
  rw [hchosenUniv] at huniformChosen
  by_contra hnoStrict
  push Not at hnoStrict
  have htie : IsTie design := by
    obtain ⟨weakDominator, hweakCard, hweakDominates⟩ :=
      gtzWeighted_of_le_five 5 3 (by norm_num) (le_refl 5) design
    exact ⟨⟨weakDominator, hweakCard, hweakDominates⟩,
      fun candidate hcandidateCard => hnoStrict candidate hcandidateCard⟩
  have hprimitive := isPrimitiveDesign_of_uniformPosition_fiveThree design huniformChosen
  obtain ⟨relabel, hlineOne, _hlineTwo⟩ :=
    EndpointSpike.sharedLinePairAtEveryTie_holds design hprimitive htie
  have hzeroOne : relabel 0 ≠ relabel 1 := relabel.injective.ne (by decide)
  have hzeroTwo : relabel 0 ≠ relabel 2 := relabel.injective.ne (by decide)
  have honeTwo : relabel 1 ≠ relabel 2 := relabel.injective.ne (by decide)
  refine huniformChosen {relabel 0, relabel 1, relabel 2} (Finset.subset_univ _) ?_ ?_
  · rw [Finset.card_insert_of_notMem (by simp [hzeroOne, hzeroTwo]),
      Finset.card_pair honeTwo]
  · exact (atomBracket_eq_zero_iff_isDependentSelection design
      hzeroOne hzeroTwo honeTwo).mp hlineOne

/-- **Diamond control, forced through the theorem**: the kernel-checked
primitive (5,3) tie (`Gtz.diamondDesign_isTie`) is NOT in uniform position —
were it, the corank-2 slice above would hand it a strict dominator,
contradicting `Gtz.diamondDesign_no_strictDominator`.  So the size-5 hinge
slice excludes the diamond BY HYPOTHESIS, with no bracket computation. -/
theorem diamondDesign_not_isUniformPositionFamily :
    ¬ InductionStep.IsUniformPositionFamily diamondDesign Finset.univ := by
  intro huniform
  obtain ⟨dominating, hdominatingCard, hdominatingPosDef⟩ :=
    rankHingeUniformPositionThree_holdsAtCorankTwoCell diamondDesign Finset.univ
      (by rw [Finset.card_univ, Fintype.card_fin]) huniform
  exact diamondDesign_no_strictDominator dominating hdominatingCard hdominatingPosDef

/-- **The honest remainder of the rank-3 hinge**: sizes `>= 6`.  The size-6
instance contains the top-of-window geometry (the (6,3) cell is the window
band); nothing in the present corpus produces it — the stress-free hinge does
not (its hypothesis is matrix-level stress-freeness of all six atoms, not
vector-level uniform position of five, and its conclusion is a parallel pair,
not a strict dominator), and the tie-based route of the size-5 slice dies at
size 6 because the weak dominator there IS the open `GtzWeighted 6 3`. -/
def RankThreeHingeBeyondCorankTwoCell : Prop :=
  ∀ size : ℕ, 6 ≤ size →
    ∀ (design : WeightedDesign size 3) (chosen : Finset (Fin size)),
      chosen.card = 5 → InductionStep.IsUniformPositionFamily design chosen →
      ∃ dominating : Finset (Fin size),
        dominating.card = 3 ∧ (subsetSum design dominating - 1).PosDef

/-- The gate: the named remainder is ALL that separates the present corpus
from `RankHingeUniformPosition 3` — sizes below 5 are vacuous, size 5 is the
theorem above. -/
theorem rankHingeUniformPosition_three_of_beyondCorankTwoCell
    (hbeyond : RankThreeHingeBeyondCorankTwoCell) :
    InductionStep.RankHingeUniformPosition 3 := by
  intro size design chosen hchosenCard huniform
  have hcardLeSize : chosen.card ≤ size := by
    have hcardLe := Finset.card_le_univ chosen
    rwa [Fintype.card_fin] at hcardLe
  have hsizeFloor : 5 ≤ size := by omega
  rcases eq_or_lt_of_le hsizeFloor with hfive | hbeyondSize
  · subst hfive
    exact rankHingeUniformPositionThree_holdsAtCorankTwoCell design chosen
      (by omega) huniform
  · exact hbeyond size (by omega) design chosen (by omega) huniform

/-! ## Layer 5: route (b), wired UNIFORMLY

The tie-reduction capstone `Gtz.gtzWeighted_of_hinge_of_reach` is FULLY
GENERIC in both size and rank — the rank-3 boundness sits only in its
INPUTS, which at `(6,3)` are `Gtz.icosaDesign` (the anchor) and
`Gtz.parallelFreeReachesAnchor_six_three`.  Below, the inputs are named
uniformly and the arrow is a kernel theorem at every rank.

Two structural points:

* The hypothesis must be the hinge at EVERY window cell, not only the top
  cell.  `Gtz.gtzWeighted_of_hinge_of_reach` closes ONE cell; the window is
  closed by a SIZE induction inside it, each step consuming the previous size
  through the parallel-pair merge (`Gtz.dominating_of_parallel_pair`).
* The size induction bottoms out for free: below the window
  (`size = 2 * rank - 1`) Naimark duality descends to the dual rank
  `rank - 1`, which is the predecessor.  So route (b) consumes exactly the
  same predecessor slot route (a) does.

NOT LIFTING-SHAPED (the standing no-go, `Gtz.BorderedSlackLifting`): nothing
here lifts a downstairs selection across a RANK increment.  The recursion is
in the SIZE at fixed rank, by merging an exactly parallel pair — the
margin-free branch — with the rank only ever DESCENDING, through Naimark
duality. -/

/-- **Route (b)'s tie hypothesis, uniform in the rank.**  Every tie at every
canonical-window cell carries a parallel pair.
`InductionStep.ParallelPairAtTopCellTie rank` is its top-cell instance
(`parallelPairAtTopCellTie_of_windowTie`); the extra cells are what the size
induction needs, and at rank 3 the window is `{6, 7}` so this is exactly the
pair of statements `Gtz.HingeHoldsAtSize 6 3` / `Gtz.HingeHoldsAtSize 7 3`. -/
def ParallelPairAtWindowTie (rank : ℕ) : Prop :=
  ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank → HingeHoldsAtSize size rank

/-- **Route (b)'s topological input, uniform in the rank.**  Every window cell
carries an anchor design with a STRICTLY dominating subset whose parallel-free
locus the whole cell reaches by a parallel-free path.  At `(6,3)` both halves
are theorems: `Gtz.icosaDesign_hasStrictlyDominatingSubset` and
`Gtz.parallelFreeReachesAnchor_six_three`. -/
def WindowAnchorReach (rank : ℕ) : Prop :=
  ∀ size : ℕ, InductionStep.IsInsideCanonicalWindow size rank →
    ∃ anchor : WeightedDesign size rank,
      HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor

/-- The top-cell Prop is the top-cell instance of the window Prop. -/
theorem parallelPairAtTopCellTie_of_windowTie {rank : ℕ}
    (hwindowTie : ParallelPairAtWindowTie rank) :
    InductionStep.ParallelPairAtTopCellTie rank :=
  fun design htie =>
    hwindowTie (rank * (rank + 1) / 2 + 1)
      (InductionStep.topCell_isInsideCanonicalWindow rank) design htie

/-- **One window cell closed**, from the generic capstone: the hinge at the cell,
an anchored parallel-free reach, and the SAME rank one size down (which feeds the
parallel-pair merge). -/
theorem gtzWeighted_succ_of_hinge_of_reach {predSize rank : ℕ}
    (hhinge : HingeHoldsAtSize (predSize + 1) rank)
    (hanchor : ∃ anchor : WeightedDesign (predSize + 1) rank,
      HasStrictlyDominatingSubset anchor
        ∧ ParallelFreeReachesAnchor (predSize + 1) rank anchor)
    (hpredSize : GtzWeighted predSize rank) :
    GtzWeighted (predSize + 1) rank := by
  obtain ⟨anchor, hanchorStrict, hreach⟩ := hanchor
  refine gtzWeighted_of_hinge_of_reach hhinge hreach hanchorStrict ?_
  rintro design ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  exact dominating_of_parallel_pair design hpredSize hdistinct hparallel

/-- **The window floor is free**: one size below the window the Naimark dual has
rank `rank - 1`, so the predecessor rank supplies it. -/
theorem gtzWeighted_belowWindow_of_predecessor {rank : ℕ} (hrank : 3 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) :
    GtzWeighted (2 * rank - 1) rank := by
  refine gtzWeighted_of_dual_rank (by omega) (by omega) ?_
  have hdualRank : 2 * rank - 1 - rank = rank - 1 := by omega
  rw [hdualRank]
  exact hpredecessor (2 * rank - 1)

/-- **ROUTE (b), WIRED UNIFORMLY.**  At every rank `>= 3` the window-cell hinge,
the anchored reach and the predecessor rank close the whole canonical window —
by induction on the SIZE inside the window, each rung riding
`Gtz.gtzWeighted_of_hinge_of_reach` with the previous size feeding the
parallel-pair merge, and the floor riding Naimark duality into the predecessor.
This is route (b)'s missing arrow, and it is rank-uniform. -/
theorem closesCanonicalWindow_of_windowTie_of_reach (rank : ℕ) (hrank : 3 ≤ rank)
    (hwindowTie : ParallelPairAtWindowTie rank) (hreach : WindowAnchorReach rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) :
    InductionStep.ClosesCanonicalWindow rank := by
  have hwindowRung : ∀ offset : ℕ, 2 * rank + offset ≤ rank * (rank + 1) / 2 + 1 →
      GtzWeighted (2 * rank + offset) rank := by
    intro offset
    induction offset with
    | zero =>
        intro hoffsetTop
        have hsucc : 2 * rank + 0 = (2 * rank - 1) + 1 := by omega
        rw [hsucc]
        refine gtzWeighted_succ_of_hinge_of_reach ?_ ?_
          (gtzWeighted_belowWindow_of_predecessor hrank hpredecessor)
        · exact hwindowTie ((2 * rank - 1) + 1) ⟨by omega, by omega⟩
        · exact hreach ((2 * rank - 1) + 1) ⟨by omega, by omega⟩
    | succ prevOffset ih =>
        intro hoffsetTop
        have hsucc : 2 * rank + (prevOffset + 1) = (2 * rank + prevOffset) + 1 := by omega
        rw [hsucc]
        refine gtzWeighted_succ_of_hinge_of_reach ?_ ?_ (ih (by omega))
        · exact hwindowTie ((2 * rank + prevOffset) + 1) ⟨by omega, by omega⟩
        · exact hreach ((2 * rank + prevOffset) + 1) ⟨by omega, by omega⟩
  intro size hinside
  obtain ⟨hbelow, habove⟩ := hinside
  have hoffsetSplit : size = 2 * rank + (size - 2 * rank) := by omega
  rw [hoffsetSplit]
  exact hwindowRung (size - 2 * rank) (by omega)

/-- **Route (b) reaches the full target.**  Quantified over the ranks, the
window-cell hinge plus the anchored reach yield weighted GTZ at every size and
every rank — no hinge PRODUCTION (route (a)'s gap 3) is needed, because the
recursion is in the size, not in the hinge tower. -/
theorem routeB_target
    (hwindowTie : ∀ rank : ℕ, 3 ≤ rank → ParallelPairAtWindowTie rank)
    (hreach : ∀ rank : ℕ, 3 ≤ rank → WindowAnchorReach rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank := by
  have harrow : InductionStep.WindowArrowFromPredecessorWeighted := by
    intro rank hrank hpredecessor
    exact closesCanonicalWindow_of_windowTie_of_reach rank hrank (hwindowTie rank hrank)
      (hreach rank hrank) hpredecessor
  intro size rank hrankPos _
  exact InductionStep.forall_gtzWeightedAll_of_windowArrow harrow rank hrankPos size

/-- **Rank-3 cross-check**: at rank 3 the window is `{6, 7}`, and the reach
half at size 6 is a theorem (`Gtz.parallelFreeReachesAnchor_six_three`) with
its anchor (`Gtz.icosaDesign_hasStrictlyDominatingSubset`), so the uniform
route-(b) step at `(6,3)` reproduces `Gtz.gtzWeighted_six_three_of_hinge`
through the generic mechanism — mechanism parity certified. -/
theorem gtzWeighted_six_three_of_hinge_viaUniformRung
    (hhinge : HingeHoldsAtSize 6 3) : GtzWeighted 6 3 := by
  have hpredSize : GtzWeighted 5 3 := gtzWeighted_of_le_five 5 3 (by norm_num) (le_refl 5)
  exact gtzWeighted_succ_of_hinge_of_reach (predSize := 5) (rank := 3) hhinge
    ⟨icosaDesign, icosaDesign_hasStrictlyDominatingSubset,
      parallelFreeReachesAnchor_six_three⟩ hpredSize

end UniformPositionBridge
end Gtz

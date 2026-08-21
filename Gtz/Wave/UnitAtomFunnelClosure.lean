/-
# The funnel branch of `(6,3)` closes

A `(6,3)` tie is ALL-HEAVY or a FUNNEL: some atom has leverage exactly one, and a
dominating triple avoiding it FIXES it (`Gtz.isTie_sixThree_allHeavy_or_funnel`).
The funnel branch was closed except for one measured input — how many weakly
dominating triples a `(5,3)` tie carries.  That input is now the theorem
`Gtz.seven_le_card_dominatingFamily_of_isTie_fiveThree`, and this module spends
it.

## The route

Deflate the unit atom.  `Gtz.isTie_deflatedDesign` says the deflation of a tie at
a light atom is again a tie, so the five surviving atoms form a `(5,3)` TIE, and
the three-class law gives it SEVEN dominating triples.  Each lifts:
`Gtz.deflatedGapBoundAt_image_of_dominates_deflatedDesign` turns deflated
domination into the deflated gap bound at the lifted triple, and the landed
`Gtz.dominates_and_fixes_of_deflatedGapBound` reads that bound as domination AND
fixing.  So a funnel carries seven dominating triples, all avoiding the unit atom
and all fixing it.

Fixing is null-sharing: `(S_T - 1) g_a = 0`.  Two null-sharing dominators one
swap apart are refused — at the same exchanged member by
`Gtz.unitAtom_second_swap_absurd`, at different members by
`Gtz.unitAtom_two_mirror_swaps_absurd` — so the family has swap-degree at most
one, and `Gtz.swapDegree_le_one_card_le_three` caps it at THREE.  Seven against
three.

## What closes, and what does not

`Gtz.hasParallelPair_of_isTie_sixThree_of_unitAtom`: a `(6,3)` tie with an atom of
leverage one has a parallel pair.  With the landed split that leaves exactly one
branch of the hinge at `(6,3)`: the ALL-HEAVY one.  Recorded as
`Gtz.hingeHoldsAtSize_six_three_of_allHeavy`, which reduces
`Gtz.HingeHoldsAtSize 6 3` — and with it, through
`Gtz.gtzWeightedAll_three_of_hinge`, the whole of rank three — to all-heavy ties
alone.
-/
import Gtz.Wave.PivotFourDominatingTriples
import Gtz.Wave.FunnelSwapClosure
import Gtz.Wave.FunnelPairMinorHinge
import Gtz.Wave.AllHeavyHingeSchur
import Gtz.Wave.UnitAtomFunnel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 1. Deflated domination is the deflated gap bound upstairs -/

/-- **THE LIFT, IN THE FORM THE FUNNEL CONSUMES.**  A dominating selection of the
deflated design satisfies the deflated gap BOUND at the lifted selection, which
is strictly more than weak domination and is what
`Gtz.dominates_and_fixes_of_deflatedGapBound` reads. -/
theorem deflatedGapBoundAt_image_of_dominates_deflatedDesign {atoms rank : ℕ}
    (D : WeightedDesign (atoms + 1) rank) (light : Fin (atoms + 1))
    (R : Matrix (Fin rank) (Fin rank) ℝ) (hunit : IsUnit R.det)
    (hslack : (0 : ℝ) < 1 - D.weight light)
    (hcongruence : Rᵀ * (1 - D.weight light • atomMatrix (D.atom light)) * R = 1)
    {chosen : Finset (Fin atoms)}
    (hdominates : Dominates (deflatedDesign D light R hslack hcongruence) chosen) :
    DeflatedGapBoundAt D light (chosen.image light.succAbove) := by
  have hgap : ((((1 : ℝ) - D.weight light) • subsetSum D (chosen.image light.succAbove))
      - (1 - D.weight light • atomMatrix (D.atom light))).PosSemidef := by
    refine (posSemidef_congr_right
      (deflatedGap_transpose D light (chosen.image light.succAbove)) hunit).mpr ?_
    rw [deflatedGap_congruence D light R hslack hcongruence chosen]
    exact hdominates
  have hrewrite : ((1 : ℝ) - D.weight light) • (subsetSum D (chosen.image light.succAbove) - 1)
      - D.weight light • ((1 : Matrix (Fin rank) (Fin rank) ℝ) - atomMatrix (D.atom light))
      = (((1 : ℝ) - D.weight light) • subsetSum D (chosen.image light.succAbove))
        - (1 - D.weight light • atomMatrix (D.atom light)) := by
    module
  rw [DeflatedGapBoundAt, hrewrite]
  exact hgap

/-! ## 2. The swap normal form -/

/-- **TWO TRIPLES MEETING IN A PAIR ARE ONE SWAP APART.**  The intersection
condition names the dropped and the kept label outright: each difference is a
singleton, and the erased triple is the intersection. -/
theorem exists_swap_normalForm {ground : ℕ} {baseSet swapSet : Finset (Fin ground)}
    (hbase : baseSet.card = 3) (hswap : swapSet.card = 3)
    (hmeet : (baseSet ∩ swapSet).card = 2) :
    ∃ dropped kept : Fin ground, dropped ∈ baseSet ∧ kept ∉ baseSet
      ∧ swapSet = insert kept (baseSet.erase dropped) := by
  classical
  have hbaseDiff : (baseSet \ swapSet).card = 1 := by
    rw [Finset.card_sdiff, hbase, Finset.inter_comm, hmeet]
  have hswapDiff : (swapSet \ baseSet).card = 1 := by
    rw [Finset.card_sdiff, hswap, hmeet]
  obtain ⟨dropped, hdropped⟩ := Finset.card_eq_one.mp hbaseDiff
  obtain ⟨kept, hkept⟩ := Finset.card_eq_one.mp hswapDiff
  have hdroppedMem : dropped ∈ baseSet \ swapSet := by rw [hdropped]; exact Finset.mem_singleton_self _
  have hkeptMem : kept ∈ swapSet \ baseSet := by rw [hkept]; exact Finset.mem_singleton_self _
  refine ⟨dropped, kept, (Finset.mem_sdiff.mp hdroppedMem).1,
    (Finset.mem_sdiff.mp hkeptMem).2, ?_⟩
  have herase : baseSet.erase dropped = baseSet ∩ swapSet := by
    ext probe
    rw [Finset.mem_erase, Finset.mem_inter]
    constructor
    · rintro ⟨hne, hmember⟩
      refine ⟨hmember, ?_⟩
      by_contra hout
      have : probe ∈ baseSet \ swapSet := Finset.mem_sdiff.mpr ⟨hmember, hout⟩
      rw [hdropped, Finset.mem_singleton] at this
      exact hne this
    · rintro ⟨hleft, hright⟩
      refine ⟨?_, hleft⟩
      intro hequal
      subst hequal
      exact (Finset.mem_sdiff.mp hdroppedMem).2 hright
  rw [herase]
  ext probe
  rw [Finset.mem_insert, Finset.mem_inter]
  constructor
  · intro hmember
    by_cases hin : probe ∈ baseSet
    · exact Or.inr ⟨hin, hmember⟩
    · left
      have : probe ∈ swapSet \ baseSet := Finset.mem_sdiff.mpr ⟨hmember, hin⟩
      rw [hkept, Finset.mem_singleton] at this
      exact this
  · rintro (hequal | ⟨-, hright⟩)
    · subst hequal
      exact (Finset.mem_sdiff.mp hkeptMem).1
    · exact hright

/-- A triple containing a named label is that label together with two others. -/
theorem exists_triple_through {ground : ℕ} {baseSet : Finset (Fin ground)}
    (hcard : baseSet.card = 3) {pivot : Fin ground} (hpivot : pivot ∈ baseSet) :
    ∃ first second : Fin ground, pivot ≠ first ∧ pivot ≠ second ∧ first ≠ second
      ∧ baseSet = {pivot, first, second} := by
  classical
  have herase : (baseSet.erase pivot).card = 2 := by
    rw [Finset.card_erase_of_mem hpivot, hcard]
  obtain ⟨first, second, hne, hpair⟩ := Finset.card_eq_two.mp herase
  have hfirst : first ∈ baseSet.erase pivot := by rw [hpair]; simp
  have hsecond : second ∈ baseSet.erase pivot := by rw [hpair]; simp
  refine ⟨first, second, Ne.symm (Finset.mem_erase.mp hfirst).1,
    Ne.symm (Finset.mem_erase.mp hsecond).1, hne, ?_⟩
  rw [← Finset.insert_erase hpivot, hpair]

/-! ## 3. The ten triples of a five-element ground set -/

set_option maxRecDepth 10000 in
theorem tripleIndex_injective : Function.Injective tripleIndex := by decide

set_option maxRecDepth 10000 in
theorem card_tripleIndex (index : Fin 10) : (tripleIndex index).card = 3 := by
  revert index
  decide

set_option maxRecDepth 40000 in
theorem exists_tripleIndex_eq {selected : Finset (Fin 5)} (hcard : selected.card = 3) :
    ∃ index : Fin 10, tripleIndex index = selected := by
  revert hcard
  revert selected
  decide

/-! ## 4. A funnel has a parallel pair -/

open scoped Classical in
/-- **THE FUNNEL BRANCH OF `(6,3)`, CLOSED.**  A `(6,3)` tie with an atom of
leverage one has a parallel pair.

Deflating the unit atom leaves a `(5,3)` TIE, which the three-class law endows
with seven dominating triples.  Each lifts to a triple of the `(6,3)` design that
avoids the unit atom, dominates, and FIXES it.  A parallel-free funnel refuses
two null-sharing swaps at one dominator, so seven such triples would have
swap-degree at most one — and the decision procedure over all `1024` families of
triples of a five-element ground set caps such a family at three. -/
theorem hasParallelPair_of_isTie_sixThree_of_unitAtom (D : WeightedDesign 6 3)
    (htie : IsTie D) (unitLabel : Fin 6)
    (hunit : leverageOf (D.atom unitLabel) = 1) : HasParallelPair D := by
  by_contra hprim
  have hslack : (0 : ℝ) < 1 - D.weight unitLabel := by
    linarith [weight_lt_one D (by norm_num) unitLabel]
  obtain ⟨whitener, hwhitenerUnit, hcongruence⟩ :=
    exists_congruence_to_one
      (posDef_one_sub_weight_smul_atomMatrix D (by norm_num) unitLabel (le_of_eq hunit))
  set deflated := deflatedDesign D unitLabel whitener hslack hcongruence with hdeflated
  have hdeflatedTie : IsTie deflated :=
    isTie_deflatedDesign D (gtzWeighted_corank_two 3 (by norm_num)) htie unitLabel
      (le_of_eq hunit) whitener hwhitenerUnit hslack hcongruence
  have hseven := seven_le_card_dominatingFamily_of_isTie_fiveThree deflated hdeflatedTie
  have hembed : Function.Injective unitLabel.succAbove := Fin.succAbove_right_injective
  -- every dominating triple downstairs lifts to a dominating, fixing triple upstairs
  have hlift : ∀ chosen ∈ dominatingFamily deflated 3,
      ((chosen.image unitLabel.succAbove).card = 3
        ∧ unitLabel ∉ chosen.image unitLabel.succAbove
        ∧ subsetSum D (chosen.image unitLabel.succAbove) *ᵥ D.atom unitLabel
            = D.atom unitLabel) := by
    intro chosen hchosen
    obtain ⟨hcard, hdominates⟩ := (mem_dominatingFamily_iff deflated 3 chosen).mp hchosen
    have hcardImage : (chosen.image unitLabel.succAbove).card = 3 := by
      rw [Finset.card_image_of_injective _ hembed, hcard]
    refine ⟨hcardImage, ?_, ?_⟩
    · intro hmember
      obtain ⟨index, -, hindex⟩ := Finset.mem_image.mp hmember
      exact (Fin.succAbove_ne unitLabel index) hindex
    · exact (dominates_and_fixes_of_deflatedGapBound (m := 5) D (by norm_num) htie hunit
        hcardImage (deflatedGapBoundAt_image_of_dominates_deflatedDesign D unitLabel
          whitener hwhitenerUnit hslack hcongruence hdominates)).2
  -- index the family by the ten triples
  set family : Finset (Fin 10) :=
    Finset.univ.filter fun index => tripleIndex index ∈ dominatingFamily deflated 3
    with hfamily
  have hcardFamily : family.card = (dominatingFamily deflated 3).card := by
    refine Finset.card_bij (fun index _ => tripleIndex index) ?_ ?_ ?_
    · intro index hindex
      exact (Finset.mem_filter.mp hindex).2
    · intro first _ second _ hequal
      exact tripleIndex_injective hequal
    · intro selected hselected
      obtain ⟨hcard, -⟩ := (mem_dominatingFamily_iff deflated 3 selected).mp hselected
      obtain ⟨index, hindex⟩ := exists_tripleIndex_eq hcard
      exact ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ index, by rw [hindex]; exact hselected⟩,
        hindex⟩
  -- the null-sharing reading of a lifted triple
  have hnull : ∀ chosen ∈ dominatingFamily deflated 3,
      (subsetSum D (chosen.image unitLabel.succAbove) - 1) *ᵥ D.atom unitLabel = 0 := by
    intro chosen hchosen
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, (hlift chosen hchosen).2.2, sub_self]
  -- swap degree at most one
  have hdegree : ∀ index ∈ family,
      (family.filter fun other => other ≠ index ∧ OneSwapApart index other).card ≤ 1 := by
    intro index hindex
    by_contra hbig
    obtain ⟨firstOther, hfirstMem, secondOther, hsecondMem, hdistinct⟩ :=
      Finset.one_lt_card.mp (Nat.not_le.mp hbig)
    have hfirstFilter := Finset.mem_filter.mp hfirstMem
    have hsecondFilter := Finset.mem_filter.mp hsecondMem
    have hbaseMem : tripleIndex index ∈ dominatingFamily deflated 3 :=
      (Finset.mem_filter.mp hindex).2
    have hfirstDom : tripleIndex firstOther ∈ dominatingFamily deflated 3 :=
      (Finset.mem_filter.mp hfirstFilter.1).2
    have hsecondDom : tripleIndex secondOther ∈ dominatingFamily deflated 3 :=
      (Finset.mem_filter.mp hsecondFilter.1).2
    obtain ⟨hbaseCard, havoid, hfix⟩ := hlift _ hbaseMem
    obtain ⟨hfirstCard, -, -⟩ := hlift _ hfirstDom
    obtain ⟨hsecondCard, -, -⟩ := hlift _ hsecondDom
    have hmeetFirst : (((tripleIndex index).image unitLabel.succAbove)
        ∩ ((tripleIndex firstOther).image unitLabel.succAbove)).card = 2 := by
      rw [← Finset.image_inter _ _ hembed, Finset.card_image_of_injective _ hembed]
      exact hfirstFilter.2.2
    have hmeetSecond : (((tripleIndex index).image unitLabel.succAbove)
        ∩ ((tripleIndex secondOther).image unitLabel.succAbove)).card = 2 := by
      rw [← Finset.image_inter _ _ hembed, Finset.card_image_of_injective _ hembed]
      exact hsecondFilter.2.2
    have hsetsDistinct : (tripleIndex firstOther).image unitLabel.succAbove
        ≠ (tripleIndex secondOther).image unitLabel.succAbove := by
      intro hequal
      exact hdistinct (tripleIndex_injective (Finset.image_injective hembed hequal))
    obtain ⟨droppedFirst, keptFirst, hdroppedFirst, hkeptFirst, hfirstShape⟩ :=
      exists_swap_normalForm hbaseCard hfirstCard hmeetFirst
    obtain ⟨droppedSecond, keptSecond, hdroppedSecond, hkeptSecond, hsecondShape⟩ :=
      exists_swap_normalForm hbaseCard hsecondCard hmeetSecond
    have hnullFirst : (subsetSum D ((tripleIndex firstOther).image unitLabel.succAbove) - 1)
        *ᵥ D.atom unitLabel = 0 := hnull _ hfirstDom
    have hnullSecond : (subsetSum D ((tripleIndex secondOther).image unitLabel.succAbove) - 1)
        *ᵥ D.atom unitLabel = 0 := hnull _ hsecondDom
    by_cases hsame : droppedFirst = droppedSecond
    · subst hsame
      have hkeptDistinct : keptFirst ≠ keptSecond := by
        intro hequal
        exact hsetsDistinct (by rw [hfirstShape, hsecondShape, hequal])
      obtain ⟨firstOtherLabel, secondOtherLabel, hne1, hne2, hne3, hshape⟩ :=
        exists_triple_through hbaseCard hdroppedFirst
      rw [hshape] at havoid hfix hkeptFirst hkeptSecond hfirstShape hsecondShape
      simp only [Finset.mem_insert, Finset.mem_singleton] at havoid
      push Not at havoid
      refine unitAtom_second_swap_absurd D hprim hne1 hne2 hne3
        havoid.1 havoid.2.1 havoid.2.2 hkeptDistinct hkeptFirst hkeptSecond hunit hfix ?_ ?_
      · rw [← hfirstShape]; exact hnullFirst
      · rw [← hsecondShape]; exact hnullSecond
    · have hsecondInBase : droppedSecond
          ∈ ((tripleIndex index).image unitLabel.succAbove).erase droppedFirst :=
        Finset.mem_erase.mpr ⟨Ne.symm hsame, hdroppedSecond⟩
      have herase : (((tripleIndex index).image unitLabel.succAbove).erase droppedFirst).card
          = 2 := by rw [Finset.card_erase_of_mem hdroppedFirst, hbaseCard]
      obtain ⟨leftLabel, rightLabel, hpairNe, hpairShape⟩ := Finset.card_eq_two.mp herase
      have hthird : ∃ thirdLabel : Fin 6, droppedSecond ≠ thirdLabel
          ∧ ((tripleIndex index).image unitLabel.succAbove).erase droppedFirst
              = {droppedSecond, thirdLabel} := by
        rw [hpairShape] at hsecondInBase
        rcases Finset.mem_insert.mp hsecondInBase with hleft | hright
        · exact ⟨rightLabel, by rw [hleft]; exact hpairNe, by rw [hpairShape, hleft]⟩
        · rw [Finset.mem_singleton] at hright
          exact ⟨leftLabel, by rw [hright]; exact Ne.symm hpairNe,
            by rw [hpairShape, hright, Finset.pair_comm]⟩
      obtain ⟨thirdLabel, hthirdNe, hthirdShape⟩ := hthird
      have hthirdMem : thirdLabel
          ∈ ((tripleIndex index).image unitLabel.succAbove).erase droppedFirst := by
        rw [hthirdShape]; simp
      have hthirdNeFirst : droppedFirst ≠ thirdLabel :=
        Ne.symm (Finset.mem_erase.mp hthirdMem).1
      have hshape : (tripleIndex index).image unitLabel.succAbove
          = {droppedFirst, droppedSecond, thirdLabel} := by
        rw [← Finset.insert_erase hdroppedFirst, hthirdShape]
      rw [hshape] at havoid hfix hkeptFirst hkeptSecond hfirstShape hsecondShape
      refine unitAtom_two_mirror_swaps_absurd (m := 5) D hprim ?_ ?_ hsame hthirdNeFirst
        hthirdNe hkeptFirst hkeptSecond havoid hunit hfix ?_ ?_
      · intro hequal
        exact hkeptFirst (by rw [← hequal]; simp)
      · intro hequal
        exact hkeptSecond (by rw [← hequal]; simp)
      · rw [← hfirstShape]; exact hnullFirst
      · rw [← hsecondShape]; exact hnullSecond
  have hcap := swapDegree_le_one_card_le_three family hdegree
  omega

/-! ## 5. What remains of the hinge at `(6,3)` -/

/-- **THE HINGE AT `(6,3)` IS AN ALL-HEAVY QUESTION.**  Every `(6,3)` tie with an
atom of leverage one has a parallel pair, so if every ALL-HEAVY `(6,3)` tie has
one then the hinge holds at `(6,3)` outright — and with it, through
`Gtz.gtzWeightedAll_three_of_hinge`, the whole of weighted GTZ at rank three. -/
theorem hingeHoldsAtSize_six_three_of_allHeavy
    (hheavy : ∀ D : WeightedDesign 6 3, AllHeavy D → IsTie D → HasParallelPair D) :
    HingeHoldsAtSize 6 3 := by
  intro D htie
  rcases allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree D htie with hall | ⟨label, hlabel⟩
  · exact hheavy D hall htie
  · exact hasParallelPair_of_isTie_sixThree_of_unitAtom D htie label hlabel

/-- **RANK THREE IS AN ALL-HEAVY QUESTION.**  The unit-atom stratum of `(6,3)` is
gone. -/
theorem gtzWeightedAll_three_of_allHeavy_hinge
    (hheavy : ∀ D : WeightedDesign 6 3, AllHeavy D → IsTie D → HasParallelPair D) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_six_three_of_allHeavy hheavy)

end Gtz

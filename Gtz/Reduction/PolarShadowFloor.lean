/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarCircularOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The shadow floor of the pole plane

The circular order selects the triple.  What the wrapping kill still asks of
that triple is quantitative: the plane cover, the pole surplus and the
arithmetic test.  This file prices all three against the weights, discharges
the first one outright, and rewrites the third one in the coupling data.

## 1. The pigeonhole engine

Every moment law of the polar calculus is WEIGHTED and every hypothesis of the
kill is UNWEIGHTED.  The bridge is one Cauchy-Schwarz step together with one
cap.  `Gtz.sq_sum_weight_mul_le` is the weighted Cauchy-Schwarz, proved from the
nonnegative double sum of `weight c * weight d * (f c - f d) ^ 2`, thus division
free and with no square root.  `Gtz.sq_sum_weight_le_of_cap` adds the cap: when
every `weight c * f c` stays at or below a bound, the squared weighted total is
at most that bound times the weight total times the UNWEIGHTED total.

## 2. The Parseval caps

One term of Parseval is the whole supply.  `Gtz.weight_mul_read_sq_le` says that
`weight c * (atom c ⬝ probe) ^ 2` never exceeds `probe ⬝ probe`.  Its two
instances are the shadow cap (landed) and the pole cap.

## 3. The three floors

The engine turns each weighted moment into an unweighted floor:

* the shadow trace `2` gives `4 ≤ (1 - weight pole) * ∑ planeShadowSq`
* the pole mass `leverage` gives the pairing floor
* the plane Parseval read at a probe gives `probe ⬝ probe ≤ (1 - weight pole)
  * ∑ (atom c ⬝ probe) ^ 2`.

The third one is `Gtz.polarComplementCover`: THE COMPLEMENT OF ANY OVERSHOOTING
POLE COVERS THE POLE PLANE WITH A STRICTLY POSITIVE EXCESS, and that excess is
the weight of the pole over the weight of the rest.  No tie, no predecessor
rank, no primitivity.

## 4. The heavy triple, and the first pigeonhole discharged

`Gtz.exists_erase_pair_sum_ge` is the three-of-five averaging step: drop the two
smallest of five and the remaining three carry at least three fifths of the
total.  Applied to the shadow floor it gives `Gtz.exists_heavyShadowTriple`: at
every overshooting pole of a design of six labels some triple carries a shadow
trace of at least `12 / 5`.  That is the trace bound of the kill at the excess
`1 / 5`, thus THE FIRST OF THE TWO PIGEONHOLES IS A THEOREM.

The probes price the step.  On the 22494 poles of the 3749 real near-tie
endpoints the floor `4 ≤ (1 - weight pole) * ∑ planeShadowSq` holds with a
slack of at least `5.91`, the cap `weight c * planeShadowSq ≤ 1` holds with a
slack of at least `0.25`, and the worst of all ten triples carries a shadow
trace of at least `2.99` against the required `2`.

## 5. The second pigeonhole fails, and that is measured

The same engine applied to the pole mass gives
`leverage * (1 - weight pole * leverage) ^ 2 ≤ (1 - weight pole) * ∑ pairing ^ 2`,
and the three-of-five step then asks for
`3 * (1 - weight pole * leverage) ^ 2 > 5 * (1 - weight pole)`.  That quantity
is NEGATIVE at every one of the 22494 poles, between `-4.20` and `-2.15`.  The
pole masses are far from uniform, thus averaging cannot supply the pole
surplus, although the surplus itself is at least `1.08` at every pole.  The
second pigeonhole is priced and refuted as a free step.

## 6. The arithmetic test in coupling form

`Gtz.polarShadowAdjugate_eq_coupling`: the shadow adjugate form is the coupling
vector read against the adjugate of the survivor plane form,

  `adjugate = (trace - 1) * (V ⬝ V) - ∑ (atom c ⬝ V) ^ 2`,  `V` the coupling vector.

Under the two cover bounds the survivors read `V` at least `(1 + excess)` times
its own energy, thus `adjugate ≤ (trace - 2 - excess) * (V ⬝ V)`, while the
plane determinant is at least `excess * (trace - 2 - excess)`.  Hence
`Gtz.not_isTie_of_polarCouplingBudget`: THE ARITHMETIC TEST HOLDS AS SOON AS THE
COUPLING ENERGY STAYS BELOW THE EXCESS TIMES THE POLE SURPLUS.  The decomposition
is verified at residual `1.6e-13` and the budget form fires at 3592 of the 3749
real near-tie endpoints.

## 7. The coupling energy in the signed vocabulary

The coupling vector is the unweighted sum of the signed shadows of the triple,
thus `Gtz.polarCouplingVec_dotProduct_self_eq_signedPair` reads its energy as the
double sum of the signed pairings, and `Gtz.polarCouplingSq_triple` writes it out
as the three signed energies plus twice the three signed pairings.  At a wrapping
triple the landed vertex law makes two of those pairings strictly negative and
the landed Cauchy-Schwarz caps the third by the two signed energies it joins,
thus `Gtz.polarCouplingSq_lt_of_polarWrapping`: THE COUPLING ENERGY OF A WRAPPING
TRIPLE STAYS BELOW TWICE ITS SIGNED ENERGY.  This is where the circular order
enters the budget, and it consumes the two laws that the circular order left
unconsumed.  The identity is verified at residual `3.2e-14` and the bound holds
with a slack of at least `1.59` at every wrapping triple of every one of the
22494 poles.

## 8. The saturation law of a tie

A tie carries a dominating subset, thus `Gtz.exists_saturating_subset_polarCover_of_isTie`:
at every pole one subset of the deciding size covers the pole plane at excess
ZERO and carries the pole mass at the leverage.  The two bounds the arithmetic
kill spends are therefore a STRICTNESS statement and not an existence statement.

## 9. The three targets and the two free bundles

`Gtz.PolarHeavyShadowSelection` is the arithmetic selection target with the excess
pinned to the value the floor supplies, `Gtz.PolarShadowBudgetSelection` is the
same target with the arithmetic test replaced by the coupling budget, and
`Gtz.PolarWrapBudgetSelection` pins the triple of the budget target to a wrapping
triple of the circular order.  Each closes `Gtz.GtzWeighted 6 3` and
`Gtz.GtzWeightedAll 3` on its own and each is false at size five.
`Gtz.PolarComplementFloor` collects the three floors and the heavy triple, and
`Gtz.PolarTieSaturationBound` collects the saturation law.  Both are free, and
`Gtz.PolarTiltSelectionFloor` is the nine-bundle residual that carries them.

The probes calibrate the pinned excess.  Taking the three largest shadow
energies as the triple and `1 / 5` as the excess, the arithmetic kill fires at
20078 of the 22494 poles and at 3749 of the 3749 real near-tie endpoints, and at
the remaining poles the binding clause is the arithmetic test at 2193, the pole
surplus at 144 and the plane Gram bound at 79.  The pin costs nothing and the
arithmetic test stays the whole content.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the pigeonhole engine

A weighted total, a weight total and a cap give an unweighted floor.  The
Cauchy-Schwarz step is the nonnegative double sum of the squared differences,
thus it needs no square root and no division. -/

section Pigeonhole

variable {ι : Type*}

/-- **THE WEIGHTED CAUCHY-SCHWARZ.**  The squared weighted total is at most the
weight total times the weighted total of the squares.  The proof is the
nonnegative double sum `∑ ∑ w c * w d * (f c - f d) ^ 2`, which expands to twice
the difference of the two sides. -/
theorem sq_sum_weight_mul_le (s : Finset ι) (weight value : ι → ℝ)
    (hweight : ∀ c ∈ s, 0 ≤ weight c) :
    (∑ c ∈ s, weight c * value c) ^ 2
      ≤ (∑ c ∈ s, weight c) * (∑ c ∈ s, weight c * value c ^ 2) := by
  have hnonneg : 0 ≤ ∑ c ∈ s, ∑ d ∈ s, weight c * weight d * (value c - value d) ^ 2 :=
    Finset.sum_nonneg fun c hc => Finset.sum_nonneg fun d hd =>
      mul_nonneg (mul_nonneg (hweight c hc) (hweight d hd)) (sq_nonneg _)
  have hinner : ∀ c ∈ s, ∑ d ∈ s, weight c * weight d * (value c - value d) ^ 2
      = (weight c * value c ^ 2) * (∑ d ∈ s, weight d)
        - (weight c * value c) * (2 * ∑ d ∈ s, weight d * value d)
        + weight c * (∑ d ∈ s, weight d * value d ^ 2) := by
    intro c _
    calc ∑ d ∈ s, weight c * weight d * (value c - value d) ^ 2
        = ∑ d ∈ s, ((weight c * value c ^ 2) * weight d
            - (weight c * value c) * (2 * (weight d * value d))
            + weight c * (weight d * value d ^ 2)) :=
          Finset.sum_congr rfl fun d _ => by ring
      _ = (weight c * value c ^ 2) * (∑ d ∈ s, weight d)
            - (weight c * value c) * (2 * ∑ d ∈ s, weight d * value d)
            + weight c * (∑ d ∈ s, weight d * value d ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul] at hnonneg
  nlinarith [hnonneg]

/-- **THE CAP PIGEONHOLE.**  With a cap on every weighted term, the squared
weighted total is at most the cap times the weight total times the UNWEIGHTED
total.  This is the whole bridge from the moment laws to the kill hypotheses. -/
theorem sq_sum_weight_le_of_cap (s : Finset ι) (weight value : ι → ℝ) {cap : ℝ}
    (hweight : ∀ c ∈ s, 0 ≤ weight c) (hvalue : ∀ c ∈ s, 0 ≤ value c)
    (hcap : ∀ c ∈ s, weight c * value c ≤ cap) :
    (∑ c ∈ s, weight c * value c) ^ 2
      ≤ cap * ((∑ c ∈ s, weight c) * (∑ c ∈ s, value c)) := by
  have hcs := sq_sum_weight_mul_le s weight value hweight
  have hsq : ∑ c ∈ s, weight c * value c ^ 2 ≤ cap * ∑ c ∈ s, value c := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hrw : weight c * value c ^ 2 = (weight c * value c) * value c := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (hcap c hc) (hvalue c hc)
  have hweightSum : 0 ≤ ∑ c ∈ s, weight c := Finset.sum_nonneg hweight
  calc (∑ c ∈ s, weight c * value c) ^ 2
      ≤ (∑ c ∈ s, weight c) * (∑ c ∈ s, weight c * value c ^ 2) := hcs
    _ ≤ (∑ c ∈ s, weight c) * (cap * ∑ c ∈ s, value c) :=
        mul_le_mul_of_nonneg_left hsq hweightSum
    _ = cap * ((∑ c ∈ s, weight c) * (∑ c ∈ s, value c)) := by ring

/-- **THE THREE-OF-FIVE AVERAGING STEP.**  Drop the smallest of five and then
the smallest of the remaining four: the three that stay carry at least three
fifths of the total.  No sign hypothesis is spent, because the two dropped
labels are the two extreme ones. -/
theorem exists_erase_pair_sum_ge [DecidableEq ι] (s : Finset ι) (value : ι → ℝ)
    (hcard : s.card = 5) :
    ∃ small ∈ s, ∃ second ∈ s.erase small,
      3 * (∑ c ∈ s, value c) ≤ 5 * (∑ c ∈ (s.erase small).erase second, value c) := by
  have hne : s.Nonempty := by rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨small, hsmall, hsmallMin⟩ := Finset.exists_min_image s value hne
  have hcardSmall : (s.erase small).card = 4 := by
    rw [Finset.card_erase_of_mem hsmall, hcard]
  have hneSmall : (s.erase small).Nonempty := by
    rw [← Finset.card_pos, hcardSmall]; norm_num
  obtain ⟨second, hsecond, hsecondMin⟩ := Finset.exists_min_image (s.erase small) value hneSmall
  refine ⟨small, hsmall, second, hsecond, ?_⟩
  have hsmallBound : 5 * value small ≤ ∑ c ∈ s, value c := by
    have hstep := Finset.card_nsmul_le_sum s value (value small) fun c hc => hsmallMin c hc
    rw [hcard, nsmul_eq_mul] at hstep
    push_cast at hstep
    linarith
  have hsecondBound : 4 * value second ≤ ∑ c ∈ s.erase small, value c := by
    have hstep := Finset.card_nsmul_le_sum (s.erase small) value (value second)
      fun c hc => hsecondMin c hc
    rw [hcardSmall, nsmul_eq_mul] at hstep
    push_cast at hstep
    linarith
  rw [Finset.sum_erase_eq_sub hsecond, Finset.sum_erase_eq_sub hsmall] at *
  linarith

end Pigeonhole

/-! ## Part 2: the Parseval caps

Parseval is a sum of nonnegative terms, thus every single term is capped by the
total.  That one observation is the whole supply of the section. -/

section Caps

variable {size rank : ℕ}

/-- **THE READING CAP.**  One term of Parseval never exceeds the whole: the
weighted squared reading of any probe by any atom is at most the energy of the
probe. -/
theorem weight_mul_read_sq_le (design : WeightedDesign size rank) (label : Fin size)
    (probe : Fin rank → ℝ) :
    design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
  rw [← parseval_weighted_sum_sq design probe]
  exact Finset.single_le_sum
    (f := fun c => design.weight c * (design.atom c ⬝ᵥ probe) ^ 2)
    (fun c _ => mul_nonneg (design.weight_pos c).le (sq_nonneg _)) (Finset.mem_univ label)

/-- The weight left off a pole is one minus the weight of the pole. -/
theorem sum_erase_weight_eq (design : WeightedDesign size rank) (pole : Fin size) :
    ∑ c ∈ Finset.univ.erase pole, design.weight c = 1 - design.weight pole := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ pole), design.weight_sum_one]

/-- The complement of an overshooting pole carries a strictly positive weight. -/
theorem sum_erase_weight_pos (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    0 < 1 - design.weight pole := by
  have := weight_lt_one_of_one_lt_selfDotProduct design hlong
  linarith

end Caps

/-! ## Part 3: the three unweighted floors

Each floor is one instance of the cap pigeonhole: a landed weighted moment, a
Parseval cap, and the weight of the complement. -/

section Floors

variable {size : ℕ}

/-- **THE SHADOW FLOOR.**  The unweighted shadow trace of the complement of a
pole, scaled by the weight of that complement, is at least four.  The weighted
shadow trace is two and every weighted shadow is at most one, thus the
unweighted trace cannot collapse. -/
theorem sum_erase_planeShadowSq_ge (design : WeightedDesign size 3) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    4 ≤ (1 - design.weight pole)
      * ∑ c ∈ Finset.univ.erase pole, planeShadowSq design pole c := by
  classical
  have hcap := sq_sum_weight_le_of_cap (Finset.univ.erase pole) design.weight
    (fun c => planeShadowSq design pole c) (cap := 1)
    (fun c _ => (design.weight_pos c).le)
    (fun c _ => planeShadowSq_nonneg design pole c hpole)
    (fun c _ => weight_mul_planeShadowSq_le_one design pole c hpole)
  rw [sum_weight_planeShadowSq_erase design pole hpole, sum_erase_weight_eq design pole] at hcap
  have hfour : (4 : ℝ) ≤ 1 * ((1 - design.weight pole)
      * ∑ c ∈ Finset.univ.erase pole, planeShadowSq design pole c) := by
    calc (4 : ℝ) = (((3 : ℕ) : ℝ) - 1) ^ 2 := by norm_num
      _ ≤ _ := hcap
  linarith

/-- **THE POLE MASS FLOOR.**  The same engine on the pole readings.  The
weighted pole mass is the leverage times the saturation deficit and every
weighted reading is at most the leverage. -/
theorem sum_erase_polarPairing_sq_ge (design : WeightedDesign size 3) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    (design.atom pole ⬝ᵥ design.atom pole)
        * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) ^ 2
      ≤ (1 - design.weight pole)
        * ∑ c ∈ Finset.univ.erase pole, (design.atom c ⬝ᵥ design.atom pole) ^ 2 := by
  classical
  have hcap := sq_sum_weight_le_of_cap (Finset.univ.erase pole) design.weight
    (fun c => (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (cap := design.atom pole ⬝ᵥ design.atom pole)
    (fun c _ => (design.weight_pos c).le) (fun c _ => sq_nonneg _)
    (fun c _ => weight_mul_read_sq_le design c (design.atom pole))
  rw [sum_weight_polarPairing_sq_erase design pole, sum_erase_weight_eq design pole] at hcap
  nlinarith [hcap, hpole]

/-- **THE DIRECTIONAL FLOOR.**  The unweighted plane form of the complement of a
pole, scaled by the weight of that complement, dominates the identity of the
pole plane.  The pole reads a polar probe as zero, thus the whole plane Parseval
sits on the complement. -/
theorem sum_erase_read_sq_ge (design : WeightedDesign size 3) (pole : Fin size)
    {probe : Fin 3 → ℝ} (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    probe ⬝ᵥ probe
      ≤ (1 - design.weight pole)
        * ∑ c ∈ Finset.univ.erase pole, (design.atom c ⬝ᵥ probe) ^ 2 := by
  classical
  have hpoleRead : design.atom pole ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hprobe
  have hmoment : ∑ c ∈ Finset.univ.erase pole,
      design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ pole), parseval_weighted_sum_sq design probe,
      hpoleRead]
    ring
  have hcap := sq_sum_weight_le_of_cap (Finset.univ.erase pole) design.weight
    (fun c => (design.atom c ⬝ᵥ probe) ^ 2) (cap := probe ⬝ᵥ probe)
    (fun c _ => (design.weight_pos c).le) (fun c _ => sq_nonneg _)
    (fun c _ => weight_mul_read_sq_le design c probe)
  rw [hmoment, sum_erase_weight_eq design pole] at hcap
  have hnonneg : (0 : ℝ) ≤ probe ⬝ᵥ probe := selfDotProduct_nonneg probe
  rcases eq_or_lt_of_le hnonneg with heq | hpos
  · rw [← heq]
    have hzero : probe = 0 := eq_zero_of_dotProduct_self_eq_zero heq.symm
    rw [hzero]
    simp
  · nlinarith [hcap, hpos]

/-- **THE COMPLEMENT COVERS THE POLE PLANE.**  The labels other than an
overshooting pole cover its polar plane with the strictly positive excess
`weight pole / (1 - weight pole)`.  No tie, no predecessor rank, no
primitivity and no size guard is spent: the cover of the whole complement is a
law of Parseval alone. -/
theorem polarComplementCover (design : WeightedDesign size 3) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {probe : Fin 3 → ℝ} (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    (1 + design.weight pole / (1 - design.weight pole)) * (probe ⬝ᵥ probe)
      ≤ ∑ c ∈ Finset.univ.erase pole, (design.atom c ⬝ᵥ probe) ^ 2 := by
  have hdeficit := sum_erase_weight_pos design hlong
  have hfloor := sum_erase_read_sq_ge design pole hprobe
  have hsplit : 1 + design.weight pole / (1 - design.weight pole)
      = 1 / (1 - design.weight pole) := by
    field_simp
    ring
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ hdeficit]
  nlinarith [hfloor]

/-- The excess of the complement cover is strictly positive. -/
theorem polarComplementMargin_pos (design : WeightedDesign size 3) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    0 < design.weight pole / (1 - design.weight pole) :=
  div_pos (design.weight_pos pole) (sum_erase_weight_pos design hlong)

end Floors

/-! ## Part 4: the heavy triple

The averaging step applied to the shadow floor.  At every overshooting pole of a
design of six labels the three heaviest shadows already clear the trace bound of
the kill at the excess one fifth. -/

section HeavyTriple

variable {size : ℕ}

/-- **THE HEAVY TRIPLE.**  Three labels of the complement of the pole whose
shadow trace clears `12 / 5`.  This is the trace bound of the arithmetic kill at
the excess `1 / 5`, and it costs nothing: the shadow floor plus the three-of-five
averaging step. -/
theorem exists_heavyShadowTriple (design : WeightedDesign 6 3) {pole : Fin 6}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ pole ∉ selected
      ∧ 2 * (1 + 1 / 5) ≤ ∑ c ∈ selected, planeShadowSq design pole c := by
  classical
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  have hdeficit := sum_erase_weight_pos design hlong
  have hcardErase : (Finset.univ.erase pole).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ, Fintype.card_fin]
  obtain ⟨small, hsmall, second, hsecond, haverage⟩ :=
    exists_erase_pair_sum_ge (Finset.univ.erase pole)
      (fun c => planeShadowSq design pole c) hcardErase
  refine ⟨((Finset.univ.erase pole).erase small).erase second, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hsecond, Finset.card_erase_of_mem hsmall, hcardErase]
  · intro hmem
    exact (Finset.notMem_erase pole Finset.univ)
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
  · have hfloor := sum_erase_planeShadowSq_ge design hpole
    have hweightLe : (1 : ℝ) - design.weight pole ≤ 1 := by
      linarith [design.weight_pos pole]
    have htotal : 4 ≤ ∑ c ∈ Finset.univ.erase pole, planeShadowSq design pole c := by
      nlinarith [hfloor, hweightLe, hdeficit]
    have hsum : 0 ≤ ∑ c ∈ Finset.univ.erase pole, planeShadowSq design pole c := by
      linarith
    norm_num
    linarith [haverage, htotal]

end HeavyTriple

/-! ## Part 5: the arithmetic test in coupling form

The shadow adjugate form is the coupling vector read against the adjugate of the
survivor plane form.  The two cover bounds price the reading, and the plane
determinant is priced by the plane Gram bound alone.  The arithmetic test then
reduces to a single budget: the coupling energy against the excess times the
pole surplus. -/

section Coupling

variable {m : ℕ}

/-- **THE ADJUGATE IN COUPLING FORM.**  The shadow adjugate form is the shadow
trace minus one, times the coupling energy, minus the survivors' squared
readings of the coupling vector.  Every quantity of the arithmetic test is a
reading of one vector. -/
theorem polarShadowAdjugate_eq_coupling (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m)) :
    polarShadowAdjugate design pole selected
      = ((∑ c ∈ selected, planeShadowSq design pole c) - 1)
          * (polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected)
        - ∑ c ∈ selected,
            (design.atom c ⬝ᵥ polarCouplingVec design pole selected) ^ 2 := by
  rw [polarShadowAdjugate, polarCouplingVec_dotProduct_self design hpole selected]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by
    rw [atom_dotProduct_polarCouplingVec design pole selected c]

/-- **THE ADJUGATE IS PRICED BY THE COVER.**  Under the two cover bounds the
survivors read the coupling vector at least `1 + excess` times its own energy,
thus the shadow adjugate form stays below the shadow trace minus two minus the
excess, times the coupling energy. -/
theorem polarShadowAdjugate_le_of_cover (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (selected : Finset (Fin m))
    {excess : ℝ}
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected) :
    polarShadowAdjugate design pole selected
      ≤ ((∑ c ∈ selected, planeShadowSq design pole c) - 2 - excess)
        * (polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected) := by
  have hcover := polarPlaneCover_of_traceGramDet design hpole selected htrace hgram
  have hread := hcover (polarCouplingVec design pole selected)
    (polarCouplingVec_dotProduct_pole design hpole selected)
  rw [polarShadowAdjugate_eq_coupling design hpole selected]
  nlinarith [hread]

/-- **THE PLANE DETERMINANT IS PRICED BY THE GRAM BOUND.**  The plane
determinant is at least the excess times the shadow trace minus two minus the
excess, and at the sharp excess the two agree. -/
theorem polarPlaneDet_ge_of_traceGram {size rank : ℕ} (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) {excess : ℝ}
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected) :
    excess * ((∑ c ∈ selected, planeShadowSq design pole c) - 2 - excess)
      ≤ polarPlaneDet design pole selected := by
  rw [polarPlaneDet_eq]
  nlinarith [hgram]

/-- **THE COUPLING BUDGET IMPLIES THE ARITHMETIC TEST.**  Under the two cover
bounds and a strict pole surplus, a coupling energy below the excess times the
surplus carries the whole test.  This is the one step the two budget routes of
Part 7 and Part 8 share. -/
theorem polarShadowAdjugate_lt_of_polarCouplingBudget (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (hbudget : polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
        < excess * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole)) :
    polarShadowAdjugate design pole selected
      < polarPlaneDet design pole selected
        * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole) := by
  have hspread : 0 < (∑ c ∈ selected, planeShadowSq design pole c) - 2 - excess := by
    linarith [htrace, hexcessPos]
  have hadj := polarShadowAdjugate_le_of_cover design hpole selected htrace hgram
  have hdet := polarPlaneDet_ge_of_traceGram design pole selected hgram
  have hsurplus : 0 < (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
      - design.atom pole ⬝ᵥ design.atom pole := by linarith
  nlinarith [hadj, hdet, hbudget, hspread, hsurplus, hexcessPos]

/-- **THE COUPLING BUDGET KILL.**  A pole and a triple whose plane cover opens
with an excess, whose pole mass beats the leverage and whose COUPLING ENERGY
stays below the excess times the pole surplus, kill the tie.  The arithmetic
test disappears into one budget, and no adjugate appears in the hypotheses. -/
theorem not_isTie_of_polarCouplingBudget (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin m)} (hcard : selected.card = 3)
    {excess : ℝ} (hexcessPos : 0 < excess)
    (htrace : 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c)
    (hgram : (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
        ≤ polarPlaneGramDet design pole selected)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (hbudget : polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
        < excess * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design :=
  not_isTie_of_planeShadowSchur_rank_three design hpole hcard hexcessPos htrace hgram hz
    (polarShadowAdjugate_lt_of_polarCouplingBudget design hpole selected hexcessPos htrace
      hgram hz hbudget)

end Coupling

/-! ## Part 6: the coupling energy in the signed vocabulary

The coupling vector is the unweighted sum of the signed shadows of the triple,
thus its energy is the double sum of the signed pairings.  At a wrapping triple
at least two of those pairings are strictly negative, and the landed
Cauchy-Schwarz caps the third one by the two signed energies it joins.  Hence
the coupling energy of a wrapping triple never reaches twice the signed energy
of the triple.  This is where the circular order enters the budget. -/

section SignedCoupling

variable {m : ℕ}

/-- **THE COUPLING ENERGY IS THE SIGNED PAIRING TOTAL.**  Every quantity of the
coupling budget speaks the vocabulary of the circular order. -/
theorem polarCouplingVec_dotProduct_self_eq_signedPair (design : WeightedDesign m 3)
    {pole : Fin m} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (selected : Finset (Fin m)) :
    polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
      = ∑ c ∈ selected, ∑ d ∈ selected, polarSignedPair design pole c d := by
  rw [polarCouplingVec_dotProduct_self design hpole selected]
  exact Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => by rw [polarSignedPair]

/-- The coupling energy of a triple, written out. -/
theorem polarCouplingSq_triple (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hone : first ≠ second) (htwo : first ≠ third) (hthree : second ≠ third) :
    polarCouplingVec design pole ({first, second, third} : Finset (Fin m))
        ⬝ᵥ polarCouplingVec design pole ({first, second, third} : Finset (Fin m))
      = polarSignedSq design pole first + polarSignedSq design pole second
          + polarSignedSq design pole third
        + 2 * (polarSignedPair design pole first second
            + polarSignedPair design pole second third
            + polarSignedPair design pole third first) := by
  classical
  have hnotFirst : first ∉ ({second, third} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hone, htwo⟩
  have hnotSecond : second ∉ ({third} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]
    exact hthree
  rw [polarCouplingVec_dotProduct_self_eq_signedPair design hpole]
  simp only [Finset.sum_insert hnotFirst, Finset.sum_insert hnotSecond, Finset.sum_singleton]
  rw [polarSignedPair_self, polarSignedPair_self, polarSignedPair_self,
    polarSignedPair_comm design pole second first,
    polarSignedPair_comm design pole third second,
    polarSignedPair_comm design pole first third]
  ring

/-- A signed pairing never reaches the mean of the two signed energies it
joins.  This is the landed Cauchy-Schwarz of the signed calculus, read as a
linear bound. -/
theorem two_mul_polarSignedPair_le (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (first second : Fin m) :
    2 * polarSignedPair design pole first second
      ≤ polarSignedSq design pole first + polarSignedSq design pole second := by
  have hcs := polarSignedPair_sq_le design hpole first second
  have hfirst := polarSignedSq_nonneg design hpole first
  have hsecond := polarSignedSq_nonneg design hpole second
  nlinarith [hcs, hfirst, hsecond,
    sq_nonneg (polarSignedSq design pole first - polarSignedSq design pole second)]

/-- **THE COUPLING ENERGY OF A WRAPPING TRIPLE.**  Two of the three signed
pairings are strictly negative and the third is capped by the two signed
energies it joins, thus the coupling energy stays strictly below twice the
signed energy of the triple.  The vertex law of the circular order is the whole
input. -/
theorem polarCouplingSq_lt_of_polarWrapping (design : WeightedDesign m 3) {pole : Fin m}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {first second third : Fin m}
    (hwrap : PolarWrapping design pole first second third) :
    polarCouplingVec design pole ({first, second, third} : Finset (Fin m))
        ⬝ᵥ polarCouplingVec design pole ({first, second, third} : Finset (Fin m))
      < 2 * (polarSignedSq design pole first + polarSignedSq design pole second
        + polarSignedSq design pole third) := by
  have hone := polarWrapping_ne_first_second design hpole hwrap
  have htwo := polarWrapping_ne_first_third design hpole hwrap
  have hthree := polarWrapping_ne_second_third design hpole hwrap
  have hexpand := polarCouplingSq_triple design hpole hone htwo hthree
  have hnonnegFirst := polarSignedSq_nonneg design hpole first
  have hnonnegSecond := polarSignedSq_nonneg design hpole second
  have hnonnegThird := polarSignedSq_nonneg design hpole third
  have hcapOne := two_mul_polarSignedPair_le design hpole first second
  have hcapTwo := two_mul_polarSignedPair_le design hpole second third
  have hcapThree := two_mul_polarSignedPair_le design hpole third first
  rw [hexpand]
  rcases polarSignedPair_two_neg_of_polarWrapping design hpole hwrap with
    ⟨hnegOne, hnegTwo⟩ | ⟨hnegTwo, hnegThree⟩ | ⟨hnegThree, hnegOne⟩
  · linarith
  · linarith
  · linarith

end SignedCoupling

/-! ## Part 7: the saturation law of a tie

A tie carries a dominating subset, thus the plane cover and the pole surplus of
the kill are ALREADY achieved at that subset, non strictly, at every pole.  The
whole remaining content of the arithmetic route is strictness. -/

section TieSaturation

variable {size rank : ℕ}

/-- **THE SATURATING SUBSET OF A TIE.**  It covers every direction with excess
zero.  This is the dominating subset of the tie, read as a quadratic form. -/
theorem exists_saturating_subset_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ ∀ probe : Fin rank → ℝ,
          probe ⬝ᵥ probe ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2 := by
  obtain ⟨selected, hcard, hdominates⟩ := htie.1
  exact ⟨selected, hcard, fun probe => sum_sq_ge_of_dominates hdominates probe⟩

/-- **THE POLE SURPLUS AND THE PLANE COVER ARE BOTH ACHIEVED, NON STRICTLY.**
At every pole of a tie one subset of the deciding size carries the plane cover
at excess zero and carries the pole mass at the leverage.  The two bounds the
arithmetic kill spends are thus a strictness statement, not an existence
statement. -/
theorem exists_saturating_subset_polarCover_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) (pole : Fin size) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          probe ⬝ᵥ probe ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
      ∧ design.atom pole ⬝ᵥ design.atom pole
          ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2 := by
  obtain ⟨selected, hcard, hcover⟩ := exists_saturating_subset_of_isTie design htie
  exact ⟨selected, hcard, fun probe _ => hcover probe, hcover (design.atom pole)⟩

/-- The saturating subset of a tie is never strictly dominating, thus its own
plane determinant and pole surplus sit exactly on the boundary the arithmetic
test measures. -/
theorem not_posDef_saturating_subset_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    ¬ (subsetSum design selected - 1).PosDef := htie.2 selected hcard

/-- **THE TIE SATURATION BUNDLE.**  At the pole, one subset of the deciding size
carries the plane cover at excess zero and carries the pole mass at the
leverage.  It is a theorem at every tie, thus handing it to a prover costs
nothing. -/
def PolarTieSaturationBound (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  ∃ selected : Finset (Fin size), selected.card = rank
    ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
        probe ⬝ᵥ probe ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
    ∧ design.atom pole ⬝ᵥ design.atom pole
        ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2

/-- The tie saturation bundle is free at every tie. -/
theorem polarTieSaturationBound_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) (pole : Fin size) : PolarTieSaturationBound design pole :=
  exists_saturating_subset_polarCover_of_isTie design htie pole

end TieSaturation

/-! ## Part 8: the heavy selection target

The trace bound of the kill is a theorem at the heavy triple, and the excess it
supplies is one fifth.  The remaining content of the arithmetic route is the
plane Gram bound, the pole surplus and the arithmetic test at a triple that is
heavy. -/

section HeavySelection

variable {size : ℕ}

/-- **THE HEAVY ARITHMETIC SELECTION TARGET.**  At every primitive tie of rank
three some overshooting pole and some triple avoiding it clear the plane Gram
bound at the excess `1 / 5`, the pole surplus and the arithmetic test, while
carrying a shadow trace of at least `12 / 5`.  The last clause is free:
`Gtz.exists_heavyShadowTriple` produces a triple that carries it. -/
def PolarHeavyShadowSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ (pole : Fin size) (selected : Finset (Fin size)),
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ selected.card = 3
        ∧ pole ∉ selected
        ∧ 2 * (1 + 1 / 5) ≤ ∑ c ∈ selected, planeShadowSq design pole c
        ∧ (1 + 1 / 5) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + 1 / 5) ^ 2
            ≤ polarPlaneGramDet design pole selected
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ polarShadowAdjugate design pole selected
            < polarPlaneDet design pole selected
              * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
                - design.atom pole ⬝ᵥ design.atom pole)

/-- The heavy target is a special case of the arithmetic selection target. -/
theorem polarShadowSchurSelection_of_polarHeavyShadowSelection
    (hheavy : PolarHeavyShadowSelection size) : PolarShadowSchurSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, selected, hlong, hcard, _hnotMem, htrace, hgram, hz, htest⟩ :=
    hheavy design hprimitive htie
  exact ⟨pole, selected, 1 / 5, hlong, hcard, by norm_num, htrace, hgram, hz, htest⟩

/-- The hinge from the heavy target. -/
theorem hingeHoldsAtSize_of_polarHeavyShadowSelection
    (hheavy : PolarHeavyShadowSelection size) : HingeHoldsAtSize size 3 :=
  hingeHoldsAtSize_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarHeavyShadowSelection hheavy)

/-- The three rank-three arms from the heavy target. -/
theorem thresholdArms_rank_three_of_polarHeavyShadowSelection
    (hheavy : PolarHeavyShadowSelection 6) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 :=
  thresholdArms_rank_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarHeavyShadowSelection hheavy)

/-- **THE DECIDING CELL FROM THE HEAVY TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarHeavyShadowSelection
    (hheavy : PolarHeavyShadowSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarHeavyShadowSelection hheavy)

/-- **ALL OF RANK THREE FROM THE HEAVY TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarHeavyShadowSelection
    (hheavy : PolarHeavyShadowSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarHeavyShadowSelection hheavy)

/-- The heavy target is false at size five, thus the calibration transports. -/
theorem not_polarHeavyShadowSelection_five : ¬ PolarHeavyShadowSelection 5 :=
  fun hheavy => not_polarShadowSchurSelection_five
    (polarShadowSchurSelection_of_polarHeavyShadowSelection hheavy)

end HeavySelection

/-! ## Part 9: the coupling budget targets

The arithmetic test replaced by the coupling budget.  The probes price the
replacement: the budget form fires at 3592 of the 3749 real near-tie endpoints
and at 41 percent of the poles, against 3749 and 99.8 percent for the exact
test, thus the budget is a strictly stronger demand and a strictly simpler
statement. -/

section BudgetSelection

variable {size : ℕ}

/-- **THE COUPLING BUDGET TARGET.**  The arithmetic selection target with the
adjugate test replaced by the coupling energy budget.  Every clause is a
polynomial inequality and no adjugate appears. -/
def PolarShadowBudgetSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ (pole : Fin size) (selected : Finset (Fin size)) (excess : ℝ),
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ selected.card = 3
        ∧ 0 < excess
        ∧ 2 * (1 + excess) ≤ ∑ c ∈ selected, planeShadowSq design pole c
        ∧ (1 + excess) * (∑ c ∈ selected, planeShadowSq design pole c) - (1 + excess) ^ 2
            ≤ polarPlaneGramDet design pole selected
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
            < excess * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              - design.atom pole ⬝ᵥ design.atom pole)

/-- The budget target implies the arithmetic selection target. -/
theorem polarShadowSchurSelection_of_polarShadowBudgetSelection
    (hbudget : PolarShadowBudgetSelection size) : PolarShadowSchurSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, selected, excess, hlong, hcard, hexcess, htrace, hgram, hz, hcoupling⟩ :=
    hbudget design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  have hspread : 0 < (∑ c ∈ selected, planeShadowSq design pole c) - 2 - excess := by
    linarith [htrace, hexcess]
  have hadj := polarShadowAdjugate_le_of_cover design hpole selected htrace hgram
  have hdet := polarPlaneDet_ge_of_traceGram design pole selected hgram
  have hsurplus : 0 < (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
      - design.atom pole ⬝ᵥ design.atom pole := by linarith
  exact ⟨pole, selected, excess, hlong, hcard, hexcess, htrace, hgram, hz, by
    nlinarith [hadj, hdet, hcoupling, hspread, hsurplus, hexcess]⟩

/-- The hinge from the budget target. -/
theorem hingeHoldsAtSize_of_polarShadowBudgetSelection
    (hbudget : PolarShadowBudgetSelection size) : HingeHoldsAtSize size 3 :=
  hingeHoldsAtSize_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarShadowBudgetSelection hbudget)

/-- The three rank-three arms from the budget target. -/
theorem thresholdArms_rank_three_of_polarShadowBudgetSelection
    (hbudget : PolarShadowBudgetSelection 6) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 :=
  thresholdArms_rank_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarShadowBudgetSelection hbudget)

/-- **THE DECIDING CELL FROM THE COUPLING BUDGET TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarShadowBudgetSelection
    (hbudget : PolarShadowBudgetSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarShadowBudgetSelection hbudget)

/-- **ALL OF RANK THREE FROM THE COUPLING BUDGET TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarShadowBudgetSelection
    (hbudget : PolarShadowBudgetSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarShadowSchurSelection
    (polarShadowSchurSelection_of_polarShadowBudgetSelection hbudget)

/-- The budget target is false at size five. -/
theorem not_polarShadowBudgetSelection_five : ¬ PolarShadowBudgetSelection 5 :=
  fun hbudget => not_polarShadowSchurSelection_five
    (polarShadowSchurSelection_of_polarShadowBudgetSelection hbudget)

/-- **THE WRAPPING BUDGET TARGET.**  The coupling budget target with the triple
pinned to a WRAPPING triple of the circular order.  It is the composition of the
two real-only steps of the lane: the circular order supplies the triple and the
budget supplies the test.  Part 6 prices the composition: at a wrapping triple
the coupling energy stays strictly below twice the signed energy of the
triple. -/
def PolarWrapBudgetSelection (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design → IsTie design →
    ∃ (pole first second third : Fin size) (excess : ℝ),
      1 < design.atom pole ⬝ᵥ design.atom pole
        ∧ PolarWrapping design pole first second third
        ∧ 0 < excess
        ∧ 2 * (1 + excess)
            ≤ ∑ c ∈ ({first, second, third} : Finset (Fin size)), planeShadowSq design pole c
        ∧ (1 + excess)
              * (∑ c ∈ ({first, second, third} : Finset (Fin size)),
                  planeShadowSq design pole c)
            - (1 + excess) ^ 2
          ≤ polarPlaneGramDet design pole ({first, second, third} : Finset (Fin size))
        ∧ design.atom pole ⬝ᵥ design.atom pole
            < ∑ c ∈ ({first, second, third} : Finset (Fin size)),
                (design.atom c ⬝ᵥ design.atom pole) ^ 2
        ∧ polarCouplingVec design pole ({first, second, third} : Finset (Fin size))
              ⬝ᵥ polarCouplingVec design pole ({first, second, third} : Finset (Fin size))
            < excess * ((∑ c ∈ ({first, second, third} : Finset (Fin size)),
                  (design.atom c ⬝ᵥ design.atom pole) ^ 2)
              - design.atom pole ⬝ᵥ design.atom pole)

/-- The wrapping budget target implies the wrapping kill of the circular
order. -/
theorem polarWrapSelection_of_polarWrapBudgetSelection
    (hwrap : PolarWrapBudgetSelection size) : PolarWrapSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, first, second, third, excess, hlong, hwrapping, hexcess, htrace, hgram,
    hz, hbudget⟩ := hwrap design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  exact ⟨pole, first, second, third, excess, hlong, hwrapping, hexcess, htrace, hgram, hz,
    polarShadowAdjugate_lt_of_polarCouplingBudget design hpole
      ({first, second, third} : Finset (Fin size)) hexcess htrace hgram hz hbudget⟩

/-- The wrapping budget target implies the coupling budget target. -/
theorem polarShadowBudgetSelection_of_polarWrapBudgetSelection
    (hwrap : PolarWrapBudgetSelection size) : PolarShadowBudgetSelection size := by
  intro design hprimitive htie
  obtain ⟨pole, first, second, third, excess, hlong, hwrapping, hexcess, htrace, hgram,
    hz, hbudget⟩ := hwrap design hprimitive htie
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  exact ⟨pole, ({first, second, third} : Finset (Fin size)), excess, hlong,
    polarWrapping_card_three design hpole hwrapping, hexcess, htrace, hgram, hz, hbudget⟩

/-- **THE DECIDING CELL FROM THE WRAPPING BUDGET TARGET ALONE.** -/
theorem gtzWeighted_six_three_of_polarWrapBudgetSelection
    (hwrap : PolarWrapBudgetSelection 6) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_polarWrapSelection
    (polarWrapSelection_of_polarWrapBudgetSelection hwrap)

/-- **ALL OF RANK THREE FROM THE WRAPPING BUDGET TARGET ALONE.** -/
theorem gtzWeightedAll_three_of_polarWrapBudgetSelection
    (hwrap : PolarWrapBudgetSelection 6) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_polarWrapSelection
    (polarWrapSelection_of_polarWrapBudgetSelection hwrap)

/-- The wrapping budget target is false at size five. -/
theorem not_polarWrapBudgetSelection_five : ¬ PolarWrapBudgetSelection 5 :=
  fun hwrap => not_polarWrapSelection_five
    (polarWrapSelection_of_polarWrapBudgetSelection hwrap)

/-- **THE GUARDRAIL ON THE THREE NEW ROUTES.**  The `(6,3)` tie in the tree is
not primitive, thus it touches no target, and all three size-five instances stay
refuted. -/
theorem sixSplitDiamondDesign_spares_polarShadowFloor :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarHeavyShadowSelection 5 ∧ ¬ PolarShadowBudgetSelection 5
      ∧ ¬ PolarWrapBudgetSelection 5 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarHeavyShadowSelection_five,
    not_polarShadowBudgetSelection_five, not_polarWrapBudgetSelection_five⟩

end BudgetSelection

/-! ## Part 10: the two free bundles and the ninth narrowing

The three floors and the heavy triple are theorems at every overshooting pole,
thus handing them to the prover costs nothing.  The eight-bundle residual is the
sharpest single object of the polar lane. -/

section FloorBundle

variable {size rank : ℕ}

/-- **THE COMPLEMENT FLOOR BUNDLE.**  What Parseval alone supplies at an
overshooting pole: the complement covers the pole plane with a strictly positive
excess, the unweighted shadow trace and pole mass of the complement carry their
floors, and a heavy triple exists whenever the complement has five labels. -/
def PolarComplementFloor (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  rank = 3 → 1 < design.atom pole ⬝ᵥ design.atom pole →
    (0 < 1 - design.weight pole
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          probe ⬝ᵥ probe
            ≤ (1 - design.weight pole)
              * ∑ c ∈ Finset.univ.erase pole, (design.atom c ⬝ᵥ probe) ^ 2)
      ∧ 4 ≤ (1 - design.weight pole)
            * ∑ c ∈ Finset.univ.erase pole, planeShadowSq design pole c
      ∧ (design.atom pole ⬝ᵥ design.atom pole)
            * (1 - design.weight pole * (design.atom pole ⬝ᵥ design.atom pole)) ^ 2
          ≤ (1 - design.weight pole)
            * ∑ c ∈ Finset.univ.erase pole, (design.atom c ⬝ᵥ design.atom pole) ^ 2
      ∧ ((Finset.univ.erase pole).card = 5 →
          ∃ selected : Finset (Fin size), selected.card = 3 ∧ pole ∉ selected
            ∧ 2 * (1 + 1 / 5) ≤ ∑ c ∈ selected, planeShadowSq design pole c))

/-- **THE COMPLEMENT FLOOR BUNDLE IS FREE.**  No tie, no primitivity, no
predecessor rank and no size guard. -/
theorem polarComplementFloor_holds (design : WeightedDesign size rank) (pole : Fin size) :
    PolarComplementFloor design pole := by
  classical
  intro hrank hlong
  subst hrank
  have hpole : 0 < design.atom pole ⬝ᵥ design.atom pole := lt_trans zero_lt_one hlong
  refine ⟨sum_erase_weight_pos design hlong, fun probe hprobe =>
    sum_erase_read_sq_ge design pole hprobe, sum_erase_planeShadowSq_ge design hpole,
    sum_erase_polarPairing_sq_ge design hpole, fun hcard => ?_⟩
  have hsize : size = 6 := by
    have := Finset.card_erase_of_mem (Finset.mem_univ pole)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  subst hsize
  exact exists_heavyShadowTriple design hlong

/-- **THE NINE-BUNDLE TILT RESIDUAL.**  `Gtz.PolarTiltSelectionCircular` with the
complement floor and the tie saturation handed to the prover as well.  Every
bundle is a theorem at a tie, thus the two narrowings cost nothing
downstream. -/
def PolarTiltSelectionFloor (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    PolarDeletionHeavy design pole →
    PolarSetDeletionHeavy design pole →
    PolarSpreadSurvivorHeavy design pole →
    PolarWitnessSchurBound design pole →
    PolarPlaneShadowBound design pole →
    PolarCircularShadowBound design pole →
    PolarComplementFloor design pole →
    PolarTieSaturationBound design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The nine-bundle residual is weaker than the seven-bundle one. -/
theorem polarTiltSelectionFloor_of_polarTiltSelectionCircular
    (htilt : PolarTiltSelectionCircular size rank) : PolarTiltSelectionFloor size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread hwitness
    hplane hcircular _hfloor _hsaturation hmargin hcard hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hheavy hset hspread
      hwitness hplane hcircular hmargin hcard hnotMem hcover

/-- The nine-bundle residual is weaker than the shipped one. -/
theorem polarTiltSelectionFloor_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionFloor size rank :=
  polarTiltSelectionFloor_of_polarTiltSelectionCircular
    (polarTiltSelectionCircular_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE NINE-BUNDLE RESIDUAL.** -/
theorem hingeHoldsAtSize_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      (polarDeletionHeavy_of_isTie hrank hpredecessor design htie hlong hroom)
      (polarSetDeletionHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarSpreadSurvivorHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarWitnessSchurBound_of_isTie design htie pole)
      (polarPlaneShadowBound_of_isTie design htie pole)
      (polarCircularShadowBound_of_isTie design hprimitive htie pole)
      (polarComplementFloor_holds design pole)
      (polarTieSaturationBound_of_isTie design htie pole)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover
    hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the nine-bundle one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltFloor (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd
    (hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE NINE-BUNDLE RESIDUAL.** -/
theorem polarTiltFloor_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionFloor size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltFloor hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltFloor hrank hpredecessor hroom htilt⟩

/-! ### The registry obligations, on the nine-bundle residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltFloor
    (htilt : ∀ rank : ℕ, 4 ≤ rank → PolarTiltSelectionFloor (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltFloor (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltFloor
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionFloor size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltFloor (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one nine-bundle residual per cell. -/
theorem sharpWindowHinge_of_polarTiltFloor
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionFloor size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltFloor (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltFloor (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionFloor (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltFloor (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionFloor (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltFloor (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionFloor (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltFloor hrank hpredecessor hroom htilt

end FloorBundle

/-! ## Part 11: the deciding cell and the calibration of the ninth narrowing -/

section FloorSixThree

/-- **THE DECIDING CELL OF RANK THREE FROM THE NINE-BUNDLE RESIDUAL ALONE.** -/
theorem hingeHoldsAtSize_six_three_of_polarTiltFloor
    (htilt : PolarTiltSelectionFloor 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltFloor (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the nine-bundle residual. -/
theorem thresholdArms_rank_three_of_polarTiltFloor (htilt : PolarTiltSelectionFloor 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltFloor htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL, FROM THE NINE-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltFloor (htilt : PolarTiltSelectionFloor 6 3) :
    GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltFloor htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE, FROM THE NINE-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltFloor (htilt : PolarTiltSelectionFloor 6 3) :
    GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltFloor htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE NINE-BUNDLE RESIDUAL IS FALSE AT `(5,3)`.**  The complement floor is
free at every pole of every size and the tie saturation is free at every tie,
thus the calibration transports through both narrowings unchanged. -/
theorem not_polarTiltSelectionFloor_five_three : ¬ PolarTiltSelectionFloor 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltFloor (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it
does not touch the nine-bundle residual, and the last-stage Prop stays
refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltFloor :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionFloor 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionFloor_five_three⟩

end FloorSixThree

end Gtz

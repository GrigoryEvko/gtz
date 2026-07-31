/-
# The weight floor has exactly one usable interval, and it is `(0, 1/size]`

`Gtz/Reduction/SplitTransfer.lean` reduces rank three to four obligations —
`Gtz.DustDropCertificate` and `Gtz.SpreadFloorCertificate` at sizes six and seven,
each at a chosen weight floor (`Gtz.gtzWeightedAll_three_of_branches`).  The floor is
a free real parameter, so the first question any attempt on those four obligations
must answer is WHICH floors are worth spending effort on.

This file answers it, and the answer is a single half-open interval.

## The trichotomy

`IsLiveWeightFloor size weightFloor` is `0 < weightFloor` and
`weightFloor <= 1/size`.  Outside it the split is degenerate
(`degenerate_of_not_isLiveWeightFloor`):

* `weightFloor <= 0` — the dust region is EMPTY, because weights are positive
  (`not_hasDustAtom_of_weightFloor_nonpos`), so the dust branch is vacuously
  discharged (`dustDropCertificate_of_weightFloor_nonpos`) and buys nothing.  The
  whole problem sits in the spread branch.
* `1/size < weightFloor` — the shipped horns fire: the spread region is empty
  (`Gtz.spreadFloorCertificate_of_sizeInv_lt_floor`) and the dust branch is not a
  weakening of the goal but the goal itself
  (`Gtz.dustDropCertificate_iff_gtzWeighted_of_sizeInv_lt_floor`).  The whole problem
  sits in the dust branch.

So every floor outside `(0, 1/size]` puts the entire difficulty on one branch.  That
is not a proof that the architecture fails — it is a proof that the architecture only
has content inside the window.

## Both endpoints are justified, and the right one is INSIDE

The left endpoint is open: at `weightFloor = 0` the dust region is already empty,
since `Gtz.HasDustAtom` is a strict inequality against a positive weight.

The right endpoint is CLOSED, and that is sharp rather than conventional.
`Gtz.hasDustAtom_of_sizeInv_lt_floor` — every design carries dust above the average —
needs its STRICT hypothesis: at `weightFloor` exactly `1/size` an equal-weight design
has no dust atom (`not_hasDustAtom_of_weight_eq_sizeInv`), witnessed concretely at
`(6,3)` by the shipped uniform icosahedral design
(`not_hasDustAtom_icosaDesign_sizeInv`).  So `1/size` belongs to the window and the
shipped theorem cannot be strengthened to a non-strict hypothesis.

## What this does NOT say

It does not prove `Gtz.GtzWeighted 6 3` or `Gtz.GtzWeighted 7 3`, and it does not
show the four obligations are false or unreachable.  It bounds the parameter search:
any attempt on them may restrict attention to `0 < weightFloor <= 1/size` without
loss, and an attempt that reaches for a larger floor is provably reaching for the
whole conjecture in one branch.

Nor does it claim the window is where a proof exists.  The shipped
`Gtz.not_hingeHoldsAtSize_five_three` and the NO-GO ledger of `SplitTransfer` record
separate obstructions that live inside the window; this file is about the parameter,
not about the obligations.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.Reductions
import Gtz.Reduction.Deflation
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.EqualShareSixThree
import Gtz.Quantitative.SevenThreeNoGo
import Gtz.Quantitative.SevenThreeSyzygy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The left endpoint: below zero the dust region is empty -/

/-- **No design carries dust at a non-positive floor.**  `Gtz.HasDustAtom` asks for a
weight strictly below the floor, and every weight of a design is positive. -/
theorem not_hasDustAtom_of_weightFloor_nonpos (D : WeightedDesign m k) {weightFloor : ℝ}
    (hfloorNonpos : weightFloor ≤ 0) : ¬ HasDustAtom D weightFloor := by
  rintro ⟨dustLabel, hdust⟩
  have hweightPos := D.weight_pos dustLabel
  linarith

/-- **The dust branch is vacuous below zero**, so it discharges for free and the
whole problem sits in the spread branch. -/
theorem dustDropCertificate_of_weightFloor_nonpos {size rank : ℕ} {weightFloor : ℝ}
    (hfloorNonpos : weightFloor ≤ 0) : DustDropCertificate size rank weightFloor :=
  fun D hdust => absurd hdust (not_hasDustAtom_of_weightFloor_nonpos D hfloorNonpos)

/-! ## The right endpoint is closed, and sharply so -/

/-- **An equal-weight design carries no dust at exactly the average.**  This is what
makes the strict hypothesis of `Gtz.hasDustAtom_of_sizeInv_lt_floor` necessary. -/
theorem not_hasDustAtom_of_weight_eq_sizeInv (D : WeightedDesign m k)
    (hweightUniform : ∀ atomLabel : Fin m, D.weight atomLabel = (m : ℝ)⁻¹) :
    ¬ HasDustAtom D ((m : ℝ)⁻¹) := by
  rintro ⟨dustLabel, hdust⟩
  rw [hweightUniform dustLabel] at hdust
  exact lt_irrefl _ hdust

/-- **THE RIGHT ENDPOINT IS ATTAINED AT `(6,3)`.**  The shipped maximal real
equiangular design carries uniform weight `1/6`, so it has no dust atom at
`weightFloor = 1/6`: the average itself is a live floor, not a degenerate one. -/
theorem not_hasDustAtom_icosaDesign_sizeInv : ¬ HasDustAtom icosaDesign (((6 : ℕ) : ℝ)⁻¹) :=
  not_hasDustAtom_of_weight_eq_sizeInv icosaDesign fun _ => by norm_num [icosaDesign]

/-! ## The window, and degeneracy outside it -/

/-- **The live weight-floor window** for the four-branch split at a given size: the
floor is usable only strictly above zero and at most the average `1/size`. -/
def IsLiveWeightFloor (size : ℕ) (weightFloor : ℝ) : Prop :=
  0 < weightFloor ∧ weightFloor ≤ (size : ℝ)⁻¹

/-- The average is itself a live floor, so the window is non-empty and closed on the
right. -/
theorem isLiveWeightFloor_sizeInv {size : ℕ} (hsizePos : 0 < size) :
    IsLiveWeightFloor size ((size : ℝ)⁻¹) :=
  ⟨inv_pos.mpr (by exact_mod_cast hsizePos), le_refl _⟩

/-- **OUTSIDE THE WINDOW THE SPLIT IS DEGENERATE.**  Either the dust branch is
vacuously true (below zero), or the spread branch is vacuously true AND the dust
branch is equivalent to weighted GTZ itself (above the average).  In both cases one
branch carries the entire problem and the decomposition buys nothing. -/
theorem degenerate_of_not_isLiveWeightFloor {size rank : ℕ} (hsizePos : 0 < size)
    {weightFloor : ℝ} (hnotLive : ¬ IsLiveWeightFloor size weightFloor) :
    DustDropCertificate size rank weightFloor
      ∨ (SpreadFloorCertificate size rank weightFloor
          ∧ (DustDropCertificate size rank weightFloor ↔ GtzWeighted size rank)) := by
  rcases not_and_or.mp hnotLive with hnotPositive | hnotBelowAverage
  · exact Or.inl (dustDropCertificate_of_weightFloor_nonpos (not_lt.mp hnotPositive))
  · have haboveAverage : (size : ℝ)⁻¹ < weightFloor := not_le.mp hnotBelowAverage
    exact Or.inr ⟨spreadFloorCertificate_of_sizeInv_lt_floor hsizePos haboveAverage,
      dustDropCertificate_iff_gtzWeighted_of_sizeInv_lt_floor hsizePos haboveAverage⟩

/-- **Both certificates are NECESSARY, at every floor.**  Weighted GTZ implies each
branch trivially, so the split can never be a strengthening — its only content is
which branch is easier, which is exactly what the window bounds. -/
theorem dustDropCertificate_and_spreadFloorCertificate_of_gtzWeighted {size rank : ℕ}
    (hgtz : GtzWeighted size rank) (weightFloor : ℝ) :
    DustDropCertificate size rank weightFloor ∧ SpreadFloorCertificate size rank weightFloor :=
  ⟨fun D _ => hgtz D, fun D _ => hgtz D⟩

/-! ## At the right endpoint the spread obligation COLLAPSES to uniform weights

The window's right endpoint is not merely live — it is the one floor at which the
spread obligation shrinks from a statement about all designs to a statement about
EQUAL-WEIGHT designs.  The reason is arithmetic and has nothing to do with geometry:
`size` weights that are each at least `1/size` and sum to one are each exactly
`1/size`.  There is no room. -/

/-- **NO DUST AT THE AVERAGE FORCES UNIFORM WEIGHTS.**  A design whose every weight is
at least the average, with `size` weights summing to one, has every weight exactly the
average. -/
theorem weight_eq_sizeInv_of_not_hasDustAtom_sizeInv (D : WeightedDesign m k) (hsizePos : 0 < m)
    (hnoDust : ¬ HasDustAtom D ((m : ℝ)⁻¹)) (atomLabel : Fin m) :
    D.weight atomLabel = (m : ℝ)⁻¹ := by
  simp only [HasDustAtom, not_exists, not_lt] at hnoDust
  refine le_antisymm ?_ (hnoDust atomLabel)
  by_contra hstrictlyAbove
  rw [not_le] at hstrictlyAbove
  have hconstSum : ∑ _atomLabel : Fin m, (m : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hsizePos.ne')]
  have hstrictSum : ∑ _atomLabel : Fin m, (m : ℝ)⁻¹ < ∑ otherLabel, D.weight otherLabel :=
    Finset.sum_lt_sum (fun otherLabel _ => hnoDust otherLabel)
      ⟨atomLabel, Finset.mem_univ atomLabel, hstrictlyAbove⟩
  rw [hconstSum, D.weight_sum_one] at hstrictSum
  exact lt_irrefl 1 hstrictSum

/-- **THE RIGHT-ENDPOINT COLLAPSE.**  At `weightFloor = 1/size` the spread obligation
is EQUIVALENT to its restriction to equal-weight designs.  So obligations two and four
of `Gtz.gtzWeightedAll_three_of_branches`, taken at the right endpoint of the proved
window, are statements about uniform designs only. -/
theorem spreadFloorCertificate_sizeInv_iff_uniform {size rank : ℕ} (hsizePos : 0 < size) :
    SpreadFloorCertificate size rank ((size : ℝ)⁻¹)
      ↔ ∀ D : WeightedDesign size rank,
          (∀ atomLabel : Fin size, D.weight atomLabel = (size : ℝ)⁻¹) →
            ¬ HasParallelPair D →
              ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C := by
  refine ⟨fun hcert D huniform hnoParallel => hcert D ⟨hnoParallel, ?_⟩,
    fun huniformCert D hspread => huniformCert D ?_ hspread.1⟩
  · rintro ⟨dustLabel, hdust⟩
    rw [huniform dustLabel] at hdust
    exact lt_irrefl _ hdust
  · exact fun atomLabel =>
      weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D hsizePos hspread.2 atomLabel

/-- **THE GEOMETRIC READING.**  A uniform design is exactly a tight frame of `size`
atoms with frame constant `size`: the unweighted atom sum over all atoms is
`size` times the identity.  So the collapsed obligation is a purely geometric question
about tight frames with no parallel pair. -/
theorem subsetSum_univ_eq_size_smul_one_of_weight_eq_sizeInv (D : WeightedDesign m k)
    (hsizePos : 0 < m) (huniform : ∀ atomLabel : Fin m, D.weight atomLabel = (m : ℝ)⁻¹) :
    subsetSum D Finset.univ = (m : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hsizeNe : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hsizePos.ne'
  have hparseval : (m : ℝ)⁻¹ • ∑ atomLabel, atomMatrix (D.atom atomLabel)
      = (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Finset.smul_sum, ← D.isParseval]
    exact Finset.sum_congr rfl fun atomLabel _ => by rw [huniform atomLabel]
  rw [subsetSum]
  exact (inv_smul_eq_iff₀ hsizeNe).mp hparseval

/-! ## The endpoint meets the shipped equal-share theorem

`Gtz.IsEqualShare` has exactly two fields: every weight is `1/size`, and every leverage
is the rank.  The right-endpoint collapse above supplies the FIRST for free.  So at
`weightFloor = 1/6` the spread obligation is already discharged wherever the leverages
are all the rank, by the shipped `Gtz.exists_dominating_triple_of_isEqualShare` — and
what remains of obligation two at the right endpoint is exactly the uniform designs
carrying some leverage away from the rank. -/

/-- **OBLIGATION TWO IS DISCHARGED ON THE EQUAL-LEVERAGE LOCUS AT THE RIGHT ENDPOINT.**
No parallel-pair hypothesis is consumed: the shipped equal-share theorem does not need
one, so this covers the whole equal-leverage part of the spread region. -/
theorem exists_dominating_triple_of_isSpreadAndFloored_sizeInv_of_leverage_eq_rank
    (D : WeightedDesign 6 3) (hspread : IsSpreadAndFloored D (((6 : ℕ) : ℝ)⁻¹))
    (hleverageRank : ∀ atomLabel : Fin 6, leverageOf (D.atom atomLabel) = (3 : ℝ)) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  have hequalShare : IsEqualShare D :=
    { weight_eq := fun atomLabel =>
        weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D (by norm_num) hspread.2 atomLabel
      leverage_eq := fun atomLabel => by rw [hleverageRank atomLabel]; norm_num }
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hdominates⟩ :=
    exists_dominating_triple_of_isEqualShare D hequalShare
  exact ⟨{first, second, third},
    Finset.card_eq_three.mpr ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, rfl⟩,
    hdominates⟩

/-- **WHAT IS LEFT OF OBLIGATION TWO AT THE RIGHT ENDPOINT.**  The spread certificate at
`weightFloor = 1/6` follows from its restriction to uniform designs carrying a leverage
away from the rank.  Every other design in the region is already covered above.

This is a reduction of one of the four obligations of
`Gtz.gtzWeightedAll_three_of_branches`, not a discharge of it: the residue is real and
open. -/
theorem spreadFloorCertificate_sixThree_sizeInv_of_unequalLeverage
    (hresidue : ∀ D : WeightedDesign 6 3,
        (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
          (∃ atomLabel : Fin 6, leverageOf (D.atom atomLabel) ≠ (3 : ℝ)) →
            ¬ HasParallelPair D →
              ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) := by
  intro D hspread
  by_cases hleverageRank : ∀ atomLabel : Fin 6, leverageOf (D.atom atomLabel) = (3 : ℝ)
  · exact exists_dominating_triple_of_isSpreadAndFloored_sizeInv_of_leverage_eq_rank D hspread
      hleverageRank
  · refine hresidue D
      (fun atomLabel =>
        weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D (by norm_num) hspread.2 atomLabel)
      ?_ hspread.1
    simpa only [not_forall] using hleverageRank

/-! ## The same collapse at `(7,3)`, and the asymmetry it exposes

`spreadFloorCertificate_sizeInv_iff_uniform` is size-generic, so obligation FOUR
collapses at `weightFloor = 1/7` for free, exactly as obligation two did at `1/6`.
What does NOT transfer is the discharge: the repository has no `(7,3)` analogue of
`Gtz.exists_dominating_triple_of_isEqualShare`.  It has a single equal-share witness
(`Gtz.exists_dominating_triple_sevenThreeBasisTetrapodDesign`), not a theorem about the
stratum.  So at `(7,3)` even the equal-leverage part of the collapsed obligation is open,
and the asymmetry with `(6,3)` is stated here rather than glossed.

What the collapse DOES buy at `(7,3)` is that the shipped disjoint-triple no-go becomes
applicable: `Gtz.not_dotProduct_lt_of_disjoint_triples_sevenThree` is stated on UNIFORM
WEIGHT, not on equal share, and uniform weight is exactly what the endpoint supplies. -/

/-- Obligation four collapses at the right endpoint too — the size-generic equivalence
read at seven. -/
theorem spreadFloorCertificate_sevenThree_sizeInv_iff_uniform :
    SpreadFloorCertificate 7 3 (((7 : ℕ) : ℝ)⁻¹)
      ↔ ∀ D : WeightedDesign 7 3,
          (∀ atomLabel : Fin 7, D.weight atomLabel = ((7 : ℕ) : ℝ)⁻¹) →
            ¬ HasParallelPair D →
              ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C :=
  spreadFloorCertificate_sizeInv_iff_uniform (by norm_num)

/-- **THE ENDPOINT MAKES THE SHIPPED `(7,3)` DISJOINT-TRIPLE NO-GO FIRE.**  On the spread
region at `weightFloor = 1/7` no probe can witness two DISJOINT triples both failing to
dominate.  The uniform-weight hypothesis the shipped theorem needs is supplied by the
collapse, not assumed. -/
theorem not_dotProduct_lt_of_disjoint_triples_of_isSpreadAndFloored_sizeInv
    (D : WeightedDesign 7 3) (hspread : IsSpreadAndFloored D (((7 : ℕ) : ℝ)⁻¹))
    {tripleLeft tripleRight : Finset (Fin 7)} (hdisjoint : Disjoint tripleLeft tripleRight)
    (hleftCard : tripleLeft.card = 3) (hrightCard : tripleRight.card = 3)
    {oddIndex : Fin 7} (hodd : oddIndex ∉ tripleLeft ∪ tripleRight)
    (hoddLeverage : leverageOf (D.atom oddIndex) ≤ 3)
    {probe : Fin 3 → ℝ} (hprobe : probe ≠ 0) :
    ¬ (probe ⬝ᵥ (subsetSum D tripleLeft *ᵥ probe) < probe ⬝ᵥ probe
        ∧ probe ⬝ᵥ (subsetSum D tripleRight *ᵥ probe) < probe ⬝ᵥ probe) := by
  have huniformWeight : ∀ atomIndex : Fin 7, D.weight atomIndex = 1 / 7 := fun atomIndex => by
    rw [weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D (by norm_num) hspread.2 atomIndex]
    norm_num
  exact not_dotProduct_lt_of_disjoint_triples_sevenThree D huniformWeight hdisjoint hleftCard
    hrightCard hodd hoddLeverage hprobe

/-! ## What the `(7,3)` endpoint stratum IS, and why the `(6,3)` route cannot reach it

CORRECTION, recorded because it was got wrong once.  It is tempting to call the missing
`(7,3)` analogue of `Gtz.exists_dominating_triple_of_isEqualShare` a bounded piece of
work.  It is not.  The identification below shows the equal-leverage part of the
collapsed obligation at `weightFloor = 1/7` IS the frontier cell — seven unit directions
with atom sum `(7/3) I`, the stratum the campaign's conservation laws are written for.

And the `(6,3)` proof route provably does not transfer.  That route runs through
`Gtz.exists_triangleResidual_le_four_ninths`, an averaging statement over the twenty
triangles; its `(7,3)` counterpart is a member of the counting family, and
`Gtz.countingFamilyCeiling_sevenThree` pins that family's ceiling at `-38/315` with
`Gtz.countingFamilyCeiling_sevenThree_neg` proving it strictly negative — so no member
reaches the `0` the argument needs.  The family is field-blind, so the cap survives
every Hermitian variant.

The bridge below is therefore the deliverable, not a step toward one: it connects the
endpoint collapse to the frontier machinery and says plainly where the route ends. -/

/-- **THE ENDPOINT PUTS `(7,3)` ON THE EQUAL-SHARE STRATUM.**  Uniform weight is supplied
by the collapse; equal leverage is the only extra input, and together they are exactly
`Gtz.IsEqualShare`. -/
theorem isEqualShare_of_isSpreadAndFloored_sizeInv_of_leverage_eq_rank_sevenThree
    (D : WeightedDesign 7 3) (hspread : IsSpreadAndFloored D (((7 : ℕ) : ℝ)⁻¹))
    (hleverageRank : ∀ atomLabel : Fin 7, leverageOf (D.atom atomLabel) = (3 : ℝ)) :
    IsEqualShare D where
  weight_eq := fun atomLabel =>
    weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D (by norm_num) hspread.2 atomLabel
  leverage_eq := fun atomLabel => by rw [hleverageRank atomLabel]; norm_num

/-- **THE STRATUM, IDENTIFIED AS A TIGHT FRAME.**  On the `(7,3)` equal-share stratum the
unweighted atom sum over all seven atoms is `7 I` and every squared norm is `3`.
Dividing the atoms by `sqrt 3` gives seven UNIT directions with atom sum `(7/3) I` — the
frontier configuration, not a soft neighbourhood of it. -/
theorem subsetSum_univ_eq_and_leverage_of_isEqualShare_sevenThree (D : WeightedDesign 7 3)
    (hequal : IsEqualShare D) :
    subsetSum D Finset.univ = ((7 : ℕ) : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      ∧ ∀ atomLabel : Fin 7, leverageOf (D.atom atomLabel) = (3 : ℝ) :=
  ⟨subsetSum_univ_eq_size_smul_one_of_weight_eq_sizeInv D (by norm_num) hequal.weight_eq,
    fun atomLabel => by rw [hequal.leverage_eq atomLabel]; norm_num⟩

/-- **THE ROUTE-EXCLUSION, AS ARITHMETIC.**  The counting family's ceiling is strictly
negative at both frontier cells, so at neither size can an averaging argument of the
`(6,3)` shape reach the value the domination criterion needs.  At `(6,3)` the shipped
stratum theorem exists because its proof does not rely on the family reaching zero; at
`(7,3)` no such theorem exists, and this is the arithmetic reason to expect none of that
shape. -/
theorem countingFamilyCeiling_neg_at_both_frontier_cells :
    countingFamilyCeiling 6 3 < 0 ∧ countingFamilyCeiling 7 3 < 0 :=
  ⟨by rw [countingFamilyCeiling_sixThree]; norm_num, countingFamilyCeiling_sevenThree_neg⟩

/-! ## Carving the `(6,3)` residue down again: the light-atom branch fires

The residue left at the `(6,3)` right endpoint was "uniform weight, some leverage away
from the rank, no parallel pair".  Two further cuts apply, both from shipped material.

The leverages are not free: uniform weight forces `sum_c leverage_c = size * rank`
(`sum_leverage_eq_size_mul_rank_of_weight_eq_sizeInv`), so at `(6,3)` they sum to
exactly `18` and average the rank.  And any atom of leverage at most one is discharged
by `Gtz.dominating_of_light_atom`, whose recursion input `GtzWeighted 5 3` is supplied
by the shipped `Gtz.gtzWeighted_of_le_five` — so the light case needs no new hypothesis.

Net: the residue tightens to uniform weight, every leverage STRICTLY ABOVE ONE, not all
equal to the rank, no parallel pair — with the leverages pinned to sum to `18`. -/

/-- **UNIFORM WEIGHT PINS THE LEVERAGE SUM.**  The shares sum to the rank, so at uniform
weight the leverages sum to `size * rank` and average exactly the rank. -/
theorem sum_leverage_eq_size_mul_rank_of_weight_eq_sizeInv (D : WeightedDesign m k)
    (hsizePos : 0 < m) (huniform : ∀ atomLabel : Fin m, D.weight atomLabel = (m : ℝ)⁻¹) :
    ∑ atomLabel, leverageOf (D.atom atomLabel) = (m : ℝ) * (k : ℝ) := by
  have hsizeNe : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hsizePos.ne'
  have hshares := sum_atomShare_eq_rank D
  rw [Finset.sum_congr rfl fun atomLabel _ => by
    rw [atomShare, huniform atomLabel]] at hshares
  rw [← Finset.mul_sum] at hshares
  field_simp at hshares
  linarith [hshares]

/-- **THE LIGHT-ATOM BRANCH FIRES AT `(6,3)` WITH NO NEW INPUT.**  Its recursion
hypothesis `GtzWeighted 5 3` is shipped. -/
theorem exists_dominating_triple_of_light_atom_sixThree (D : WeightedDesign 6 3)
    {lightLabel : Fin 6} (hlight : leverageOf (D.atom lightLabel) ≤ 1) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C :=
  dominating_of_light_atom D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) lightLabel hlight

/-- **THE TIGHTENED `(6,3)` RESIDUE.**  The spread certificate at the right endpoint
follows from its restriction to uniform designs whose every leverage exceeds one and
whose leverages are not all the rank.  Everything else in the region is discharged:
equal leverage by the shipped equal-share stratum theorem, a light atom by the shipped
deflation branch.

Still a conditional, and named so it cannot be read otherwise — but the hypothesis is
strictly weaker than the previous one. -/
theorem spreadFloorCertificate_sixThree_sizeInv_of_heavyUnequalLeverage
    (hresidue : ∀ D : WeightedDesign 6 3,
        (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
          (∀ atomLabel : Fin 6, 1 < leverageOf (D.atom atomLabel)) →
            (∃ atomLabel : Fin 6, leverageOf (D.atom atomLabel) ≠ (3 : ℝ)) →
              ¬ HasParallelPair D →
                ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) := by
  intro D hspread
  by_cases hleverageRank : ∀ atomLabel : Fin 6, leverageOf (D.atom atomLabel) = (3 : ℝ)
  · exact exists_dominating_triple_of_isSpreadAndFloored_sizeInv_of_leverage_eq_rank D hspread
      hleverageRank
  by_cases hallHeavy : ∀ atomLabel : Fin 6, 1 < leverageOf (D.atom atomLabel)
  · refine hresidue D
      (fun atomLabel =>
        weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D (by norm_num) hspread.2 atomLabel)
      hallHeavy ?_ hspread.1
    simpa only [not_forall] using hleverageRank
  · obtain ⟨lightLabel, hlight⟩ := not_forall.mp hallHeavy
    exact exists_dominating_triple_of_light_atom_sixThree D (not_lt.mp hlight)

/-! ## The residue can be made CLOSED, which is what NO-GO 1 was about

`SplitTransfer`'s NO-GO 1 kills a margin on the spread-and-floored region for a
topological reason: `¬ HasParallelPair` is an OPEN condition, its closure meets the tie
locus, so the infimum of any margin over it is zero.  That objection applies to the
region as the split presents it.

It does not apply to the residue below.  The parallel-pair branch of
`Gtz.gtzWeighted_of_branches` is discharged by `Gtz.dominating_of_parallel_pair`
whose only input is `GtzWeighted 5 3`, shipped as `Gtz.gtzWeighted_of_le_five` — so at
`(6,3)` a parallel pair needs no hypothesis at all
(`exists_dominating_triple_of_hasParallelPair_sixThree`), and the residue may simply
ALLOW parallel pairs.  Dropping that one open condition leaves conditions that are all
closed: uniform weight is an equality, and the leverages sit in the closed box
`[1, size]` — the upper end from the shipped per-atom ceiling
(`leverage_le_size_of_weight_eq_sizeInv`), the lower end because leverage below one is
the light branch either way — with sum pinned to `size * rank`.

So the `(6,3)` residue at the right endpoint is a closed, bounded region.  That is a
structural improvement over the previous statement, not another case-split. -/

/-- **THE PER-ATOM LEVERAGE CEILING AT UNIFORM WEIGHT.**  The shipped
`Gtz.weighted_leverage_le_one` says every share is at most one; at uniform weight that
reads `leverage <= size`. -/
theorem leverage_le_size_of_weight_eq_sizeInv (D : WeightedDesign m k) (hsizePos : 0 < m)
    (huniform : ∀ atomLabel : Fin m, D.weight atomLabel = (m : ℝ)⁻¹) (atomLabel : Fin m) :
    leverageOf (D.atom atomLabel) ≤ (m : ℝ) := by
  have hsizePosReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsizePos
  have hsizeNe : ((m : ℝ)) ≠ 0 := ne_of_gt hsizePosReal
  have hshareBound := weighted_leverage_le_one D atomLabel
  rw [huniform atomLabel] at hshareBound
  have hscaled := mul_le_mul_of_nonneg_left hshareBound (le_of_lt hsizePosReal)
  rw [← mul_assoc, mul_inv_cancel₀ hsizeNe, one_mul, mul_one] at hscaled
  exact hscaled

/-- **A PARALLEL PAIR NEEDS NO HYPOTHESIS AT `(6,3)`.**  The merge's recursion input
`GtzWeighted 5 3` is shipped, so this branch is unconditional. -/
theorem exists_dominating_triple_of_hasParallelPair_sixThree (D : WeightedDesign 6 3)
    (hparallelPair : HasParallelPair D) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hparallelPair
  exact dominating_of_parallel_pair D
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hdistinct hparallel

/-- **THE CLOSED `(6,3)` RESIDUE.**  The spread certificate at the right endpoint follows
from its restriction to uniform designs whose leverages lie in `[1, 6]` and are not all
the rank — with NO parallel-pair condition, so every hypothesis of the residue is closed.

Still a conditional; but the region it quantifies over is now closed and bounded, and
`sum_leverage_eq_size_mul_rank_of_weight_eq_sizeInv` pins its leverages to sum to `18`. -/
theorem spreadFloorCertificate_sixThree_sizeInv_of_closedResidue
    (hresidue : ∀ D : WeightedDesign 6 3,
        (∀ atomLabel : Fin 6, D.weight atomLabel = ((6 : ℕ) : ℝ)⁻¹) →
          (∀ atomLabel : Fin 6, 1 ≤ leverageOf (D.atom atomLabel)) →
            (∃ atomLabel : Fin 6, leverageOf (D.atom atomLabel) ≠ (3 : ℝ)) →
              ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    SpreadFloorCertificate 6 3 (((6 : ℕ) : ℝ)⁻¹) := by
  intro D hspread
  by_cases hleverageRank : ∀ atomLabel : Fin 6, leverageOf (D.atom atomLabel) = (3 : ℝ)
  · exact exists_dominating_triple_of_isSpreadAndFloored_sizeInv_of_leverage_eq_rank D hspread
      hleverageRank
  by_cases hallHeavy : ∀ atomLabel : Fin 6, 1 ≤ leverageOf (D.atom atomLabel)
  · refine hresidue D
      (fun atomLabel =>
        weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D (by norm_num) hspread.2 atomLabel)
      hallHeavy ?_
    simpa only [not_forall] using hleverageRank
  · obtain ⟨lightLabel, hlight⟩ := not_forall.mp hallHeavy
    exact exists_dominating_triple_of_light_atom_sixThree D (le_of_lt (not_le.mp hlight))

/-! ## CORRECTION: the right endpoint is the DEGENERATE end of the window

Recorded because the framing above, taken alone, misleads — and did mislead the author.

The collapse at `weightFloor = 1/size` is real, but "the spread obligation shrinks to the
uniform designs" is not the good news it sounds like.  The two branches partition the
designs, so whatever leaves the spread branch ARRIVES in the dust branch.  At the right
endpoint every non-uniform design carries dust
(`hasDustAtom_of_ne_sizeInv`), so obligation ONE there is
`GtzWeighted` restricted to the non-uniform designs — everything except a
codimension-positive locus — while obligation TWO retains only the uniform locus.

That is the same degeneracy the `1/size < weightFloor` horn exhibits, arriving
continuously rather than all at once: as the floor rises to the average, the spread
region contracts onto the uniform designs and the dust region swells to the complement.
So the right endpoint is the WORST floor in the window for balancing the split, not the
best, and the collapse theorems above are simplifications of the branch that was already
becoming trivial.

Where the spread branch has content is the OTHER end.  As the floor decreases toward
zero the dust region contracts (`not_hasDustAtom_of_weightFloor_nonpos` is its limit) and
the spread region swells to carry the bulk.  Any attempt that wants obligation two to be
the substantive half should work at a SMALL floor, not at `1/size`.

This does not retract any theorem above — each is true as stated.  It retracts the
suggestion that endpoint work was progress on the hard side. -/

/-- **AT THE RIGHT ENDPOINT EVERY NON-UNIFORM DESIGN CARRIES DUST.**  So obligation one
at `weightFloor = 1/size` is weighted GTZ restricted to the non-uniform designs, and
obligation two retains only the uniform locus. -/
theorem hasDustAtom_of_ne_sizeInv (D : WeightedDesign m k) (hsizePos : 0 < m)
    {someLabel : Fin m} (hne : D.weight someLabel ≠ (m : ℝ)⁻¹) :
    HasDustAtom D ((m : ℝ)⁻¹) := by
  by_contra hnoDust
  exact hne (weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D hsizePos hnoDust someLabel)

/-- **THE SPLIT AT THE RIGHT ENDPOINT, BOTH HALVES.**  Every design is either uniform —
where obligation two lives, on the closed residue above — or carries dust, where
obligation one lives.  Stated together so the asymmetry of the two halves is visible in
one place rather than inferred. -/
theorem weight_eq_sizeInv_or_hasDustAtom (D : WeightedDesign m k) (hsizePos : 0 < m) :
    (∀ atomLabel : Fin m, D.weight atomLabel = (m : ℝ)⁻¹) ∨ HasDustAtom D ((m : ℝ)⁻¹) := by
  by_cases hnoDust : HasDustAtom D ((m : ℝ)⁻¹)
  · exact Or.inr hnoDust
  · exact Or.inl fun atomLabel =>
      weight_eq_sizeInv_of_not_hasDustAtom_sizeInv D hsizePos hnoDust atomLabel

end Gtz

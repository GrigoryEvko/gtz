/-
# Every design of rank at least three has a live pair

A **live pair** of a weighted design is two distinct labels whose two by two
principal minor of `Gram - 1` is positive definite: both gap excesses strictly
positive and the pair gap excess strictly positive.  It is the hypothesis that
the whole depth-cap / cross-axis lane runs on, and until now nothing said any
design HAS one -- liveness was always assumed, discharged only by hand at the
tetrahedron.  This file proves that the hypothesis is free.

The proof is a ledger, not a construction.  Three shipped conservation laws are
all it uses.

* The **excess budget** `sum_c t_c (l_c - 1) = rank - 1`
  (`Gtz.sum_weight_mul_leverage_sub_one`).  Call `t_c (l_c - 1)` the atom's
  *heavy mass*; light atoms contribute nonpositively, so the heavy atoms alone
  carry at least `rank - 1`, which is at least two.
* The **row law** `sum_e t_e <g_c, g_e>^2 = l_c`
  (`Gtz.sum_weight_mul_sq_atomPairing`).  Scaled by the row's own weight and
  with its diagonal term peeled off, it reads: the off-diagonal weighted squared
  pairings of a row total exactly the *share gap* `s_c - s_c^2`, where
  `s_c = t_c l_c` is the atom's share.  In particular the share gap is
  nonnegative, so `0 <= s_c <= 1`, so the share gap never exceeds `1/4`.
* The **share budget** `sum_c s_c = rank` (`Gtz.sum_atomShare_eq_rank`), which
  caps the total of the share gaps by the rank.

Suppose no heavy pair were live.  Then for two heavy labels the pair gap excess
is nonpositive, so the squared pairing dominates the product of the excesses,
and each row's share gap dominates that row's heavy mass times the heavy mass of
everything else heavy.  One row already forces every heavy mass below `1/4`:
the mass times something bigger than one cannot exceed `1/4`.  Summing the rows
then forces the heavy total `T` to satisfy `T^2 - T/4 <= rank`, while the excess
budget forces `T >= rank - 1 >= 2`.  At `rank = 3` that is `7/2 <= 3`.  The
contradiction is rational and has room to spare; it only widens with the rank.

The payoff is immediate at rank three.  A live pair is exactly a positive corner
and a positive leading two by two minor of the tree's `tripleGapMatrix`, so
Sylvester's criterion for a triple containing it collapses to its third
condition alone -- and that third condition is the determinant, which the tree
already names `discriminantTie`.  So: **every rank three design carries a pair at
which strict domination of a completing triple is decided by one determinant
sign.**  Two of the three inequalities in the domination test are free, for every
design, with no hypothesis whatsoever.

Nothing here assumes heaviness, primitivity, tightness, a bound on the number of
atoms, or any genericity.
-/
import Gtz.Design.GeneralRankAveraging
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.BranchTransferConstants
import Gtz.Design.RhoNormalForm
import Gtz.Design.KFourChartClosure
import Gtz.Design.FrameConservation
import Gtz.Certificates.CollarChartReplay
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## The heavy mass and its budget -/

/-- The **heavy mass** of an atom: its weight times its gap excess.  This is the
atom's own contribution to the excess budget. -/
def heavyMassOf (design : WeightedDesign size rank) (atomLabel : Fin size) : ℝ :=
  design.weight atomLabel * gapExcessOf design atomLabel

/-- The heavy mass is the atom's share less its weight. -/
theorem heavyMassOf_eq_atomShare_sub_weight (design : WeightedDesign size rank)
    (atomLabel : Fin size) :
    heavyMassOf design atomLabel
      = atomShare design atomLabel - design.weight atomLabel := by
  simp only [heavyMassOf, gapExcessOf, atomShare]
  ring

/-- **The excess budget**: the heavy masses total `rank - 1`. -/
theorem sum_heavyMassOf_eq_rank_sub_one (design : WeightedDesign size rank) :
    ∑ atomLabel : Fin size, heavyMassOf design atomLabel = (rank : ℝ) - 1 :=
  sum_weight_mul_leverage_sub_one design

/-! ## The row law in share-gap form -/

/-- **The row law, scaled and peeled.**  Scaling the row law by the row's own
weight and removing its diagonal term leaves exactly the share gap: the
off-diagonal weighted squared pairings of a row total `s - s^2`. -/
theorem sum_erase_weightPair_mul_sq_gapPairing (design : WeightedDesign size rank)
    (rowLabel : Fin size) :
    ∑ otherLabel ∈ Finset.univ.erase rowLabel,
        design.weight rowLabel * design.weight otherLabel
          * gapPairingOf design rowLabel otherLabel ^ 2
      = atomShare design rowLabel - atomShare design rowLabel ^ 2 := by
  have hrow := sum_weight_mul_sq_atomPairing design rowLabel
  have hscaled : ∑ otherLabel : Fin size,
      design.weight rowLabel * design.weight otherLabel
        * gapPairingOf design rowLabel otherLabel ^ 2
      = design.weight rowLabel * leverageOf (design.atom rowLabel) := by
    rw [← hrow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun otherLabel _ => by
      simp only [gapPairingOf]; ring
  have hpeel := Finset.add_sum_erase Finset.univ
    (fun otherLabel : Fin size => design.weight rowLabel * design.weight otherLabel
      * gapPairingOf design rowLabel otherLabel ^ 2) (Finset.mem_univ rowLabel)
  have hdiag : design.weight rowLabel * design.weight rowLabel
      * gapPairingOf design rowLabel rowLabel ^ 2
      = atomShare design rowLabel ^ 2 := by
    simp only [gapPairingOf, atomShare, leverageOf, dotProduct_self_eq_sum_sq]
    ring
  have hshare : design.weight rowLabel * leverageOf (design.atom rowLabel)
      = atomShare design rowLabel := rfl
  rw [hdiag, hscaled, hshare] at hpeel
  linarith [hpeel]

/-- Every share is nonnegative, at any rank. -/
theorem atomShare_nonneg_ofAnyRank (design : WeightedDesign size rank) (atomLabel : Fin size) :
    0 ≤ atomShare design atomLabel :=
  mul_nonneg (design.weight_pos atomLabel).le (leverageOf_nonneg _)

/-- **The share gap is nonnegative** -- it is a sum of weighted squares. -/
theorem atomShare_gap_nonneg (design : WeightedDesign size rank) (rowLabel : Fin size) :
    0 ≤ atomShare design rowLabel - atomShare design rowLabel ^ 2 := by
  rw [← sum_erase_weightPair_mul_sq_gapPairing design rowLabel]
  refine Finset.sum_nonneg fun otherLabel _ => ?_
  exact mul_nonneg (mul_nonneg (design.weight_pos rowLabel).le
    (design.weight_pos otherLabel).le) (sq_nonneg _)

/-- Every share is at most one, at any rank: the share gap cannot be negative. -/
theorem atomShare_le_one_ofAnyRank (design : WeightedDesign size rank) (atomLabel : Fin size) :
    atomShare design atomLabel ≤ 1 := by
  rcases eq_or_lt_of_le (atomShare_nonneg_ofAnyRank design atomLabel) with hzero | hpos
  · linarith [hzero]
  · nlinarith [atomShare_gap_nonneg design atomLabel]

/-- The share gap never exceeds a quarter. -/
theorem atomShare_gap_le_quarter (design : WeightedDesign size rank) (rowLabel : Fin size) :
    atomShare design rowLabel - atomShare design rowLabel ^ 2 ≤ 1 / 4 := by
  nlinarith [sq_nonneg (atomShare design rowLabel - 1 / 2)]

/-- Every heavy mass is strictly below one. -/
theorem heavyMassOf_lt_one (design : WeightedDesign size rank) (atomLabel : Fin size) :
    heavyMassOf design atomLabel < 1 := by
  rw [heavyMassOf_eq_atomShare_sub_weight]
  have hshare := atomShare_le_one_ofAnyRank design atomLabel
  have hweight := design.weight_pos atomLabel
  linarith

/-! ## The heavy set -/

/-- The labels whose atoms are heavy: gap excess strictly positive. -/
noncomputable def heavySet (design : WeightedDesign size rank) : Finset (Fin size) :=
  Finset.univ.filter fun atomLabel => 0 < gapExcessOf design atomLabel

theorem mem_heavySet_iff (design : WeightedDesign size rank) (atomLabel : Fin size) :
    atomLabel ∈ heavySet design ↔ 0 < gapExcessOf design atomLabel := by
  simp only [heavySet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem heavyMassOf_pos_of_mem_heavySet (design : WeightedDesign size rank)
    {atomLabel : Fin size} (hmem : atomLabel ∈ heavySet design) :
    0 < heavyMassOf design atomLabel :=
  mul_pos (design.weight_pos atomLabel) ((mem_heavySet_iff design atomLabel).mp hmem)

theorem heavyMassOf_nonpos_of_notMem_heavySet (design : WeightedDesign size rank)
    {atomLabel : Fin size} (hnotMem : atomLabel ∉ heavySet design) :
    heavyMassOf design atomLabel ≤ 0 := by
  have hexcess : gapExcessOf design atomLabel ≤ 0 := by
    by_contra hcontra
    exact hnotMem ((mem_heavySet_iff design atomLabel).mpr (lt_of_not_ge hcontra))
  exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos atomLabel).le hexcess

/-- **The heavy atoms carry the whole budget**: the light ones only subtract. -/
theorem rank_sub_one_le_sum_heavyMassOf_heavySet (design : WeightedDesign size rank) :
    (rank : ℝ) - 1 ≤ ∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel := by
  rw [← sum_heavyMassOf_eq_rank_sub_one design,
    ← Finset.sum_add_sum_compl (heavySet design) (heavyMassOf design)]
  have houtside : ∑ atomLabel ∈ (heavySet design)ᶜ, heavyMassOf design atomLabel ≤ 0 :=
    Finset.sum_nonpos fun atomLabel hmem =>
      heavyMassOf_nonpos_of_notMem_heavySet design (Finset.mem_compl.mp hmem)
  linarith

/-- **At least three atoms are heavy**, at any rank at least three.  The heavy
masses total at least `rank - 1 >= 2` and each one is strictly below one. -/
theorem three_le_card_heavySet (design : WeightedDesign size rank) (hrank : 3 ≤ rank) :
    3 ≤ (heavySet design).card := by
  have hbudget := rank_sub_one_le_sum_heavyMassOf_heavySet design
  have hrankReal : (3 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hnonempty : (heavySet design).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (heavySet design) with hempty | hne
    · rw [hempty, Finset.sum_empty] at hbudget
      linarith
    · exact hne
  have hstrict : ∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel
      < ∑ _atomLabel ∈ heavySet design, (1 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun atomLabel _ => heavyMassOf_lt_one design atomLabel
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hstrict
  by_contra hcontra
  have hcard : ((heavySet design).card : ℝ) ≤ 2 := by
    have hnat : (heavySet design).card ≤ 2 := by omega
    exact_mod_cast hnat
  linarith

/-! ## The row bound under a hypothetical absence of live pairs -/

/-- Each heavy row's share gap dominates its own mass times the mass of the rest
of the heavy set, once no heavy pair is live. -/
theorem heavyMassOf_mul_sub_le_atomShare_gap (design : WeightedDesign size rank)
    (hnolive : ∀ firstLabel ∈ heavySet design, ∀ secondLabel ∈ heavySet design,
      firstLabel ≠ secondLabel → pairGapExcessOf design firstLabel secondLabel ≤ 0)
    {rowLabel : Fin size} (hrow : rowLabel ∈ heavySet design) :
    heavyMassOf design rowLabel
        * ((∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel)
            - heavyMassOf design rowLabel)
      ≤ atomShare design rowLabel - atomShare design rowLabel ^ 2 := by
  classical
  have hsubset : (heavySet design).erase rowLabel ⊆ Finset.univ.erase rowLabel :=
    Finset.erase_subset_erase rowLabel (Finset.subset_univ _)
  have hnonneg : ∀ otherLabel ∈ Finset.univ.erase rowLabel,
      otherLabel ∉ (heavySet design).erase rowLabel →
      0 ≤ design.weight rowLabel * design.weight otherLabel
            * gapPairingOf design rowLabel otherLabel ^ 2 :=
    fun otherLabel _ _ => mul_nonneg (mul_nonneg (design.weight_pos rowLabel).le
      (design.weight_pos otherLabel).le) (sq_nonneg _)
  have hrestrict : ∑ otherLabel ∈ (heavySet design).erase rowLabel,
        design.weight rowLabel * design.weight otherLabel
          * gapPairingOf design rowLabel otherLabel ^ 2
      ≤ atomShare design rowLabel - atomShare design rowLabel ^ 2 := by
    rw [← sum_erase_weightPair_mul_sq_gapPairing design rowLabel]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have htermwise : ∀ otherLabel ∈ (heavySet design).erase rowLabel,
      heavyMassOf design rowLabel * heavyMassOf design otherLabel
        ≤ design.weight rowLabel * design.weight otherLabel
            * gapPairingOf design rowLabel otherLabel ^ 2 := by
    intro otherLabel hmem
    have hne : rowLabel ≠ otherLabel := (Finset.ne_of_mem_erase hmem).symm
    have hminor := hnolive rowLabel hrow otherLabel (Finset.mem_of_mem_erase hmem) hne
    have hweights : 0 < design.weight rowLabel * design.weight otherLabel :=
      mul_pos (design.weight_pos rowLabel) (design.weight_pos otherLabel)
    have hexpand : heavyMassOf design rowLabel * heavyMassOf design otherLabel
        = design.weight rowLabel * design.weight otherLabel
            * (gapExcessOf design rowLabel * gapExcessOf design otherLabel) := by
      simp only [heavyMassOf]; ring
    rw [hexpand]
    have hgap : gapExcessOf design rowLabel * gapExcessOf design otherLabel
        ≤ gapPairingOf design rowLabel otherLabel ^ 2 := by
      simp only [pairGapExcessOf] at hminor
      linarith
    nlinarith [hweights, hgap]
  have hsummed : heavyMassOf design rowLabel
        * ∑ otherLabel ∈ (heavySet design).erase rowLabel, heavyMassOf design otherLabel
      ≤ ∑ otherLabel ∈ (heavySet design).erase rowLabel,
          design.weight rowLabel * design.weight otherLabel
            * gapPairingOf design rowLabel otherLabel ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum htermwise
  have hsplit := Finset.add_sum_erase (heavySet design) (heavyMassOf design) hrow
  have hrewrite : ∑ otherLabel ∈ (heavySet design).erase rowLabel,
        heavyMassOf design otherLabel
      = (∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel)
          - heavyMassOf design rowLabel := by linarith [hsplit]
  rw [← hrewrite]
  linarith [hsummed, hrestrict]

/-- With no live heavy pair every heavy mass falls under a quarter: the excess
budget is at least two, so the row bound pins the mass below the fixed point of
`mass * (2 - mass) = 1/4`. -/
theorem heavyMassOf_lt_quarter_of_noLivePair (design : WeightedDesign size rank)
    (hrank : 3 ≤ rank)
    (hnolive : ∀ firstLabel ∈ heavySet design, ∀ secondLabel ∈ heavySet design,
      firstLabel ≠ secondLabel → pairGapExcessOf design firstLabel secondLabel ≤ 0)
    {rowLabel : Fin size} (hrow : rowLabel ∈ heavySet design) :
    heavyMassOf design rowLabel < 1 / 4 := by
  have hbudget := rank_sub_one_le_sum_heavyMassOf_heavySet design
  have hrankReal : (3 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hrowBound := heavyMassOf_mul_sub_le_atomShare_gap design hnolive hrow
  have hcap := atomShare_gap_le_quarter design rowLabel
  have hpos := heavyMassOf_pos_of_mem_heavySet design hrow
  have hmassLt := heavyMassOf_lt_one design rowLabel
  nlinarith [hbudget, hrowBound, hcap, hpos, hmassLt, hrankReal]

/-- The heavy masses square-sum to at most a quarter of their own total. -/
theorem sum_sq_heavyMassOf_le_quarter_mul (design : WeightedDesign size rank)
    (hrank : 3 ≤ rank)
    (hnolive : ∀ firstLabel ∈ heavySet design, ∀ secondLabel ∈ heavySet design,
      firstLabel ≠ secondLabel → pairGapExcessOf design firstLabel secondLabel ≤ 0) :
    ∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel ^ 2
      ≤ 1 / 4 * ∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun atomLabel hmem => ?_
  have hpos := heavyMassOf_pos_of_mem_heavySet design hmem
  have hquarter := heavyMassOf_lt_quarter_of_noLivePair design hrank hnolive hmem
  nlinarith [hpos, hquarter]

/-- **The share-gap ceiling**: the share gaps over the heavy set total at most
the rank, because the shares total the rank and the squares are nonnegative. -/
theorem sum_atomShare_gap_heavySet_le_rank (design : WeightedDesign size rank) :
    ∑ atomLabel ∈ heavySet design,
        (atomShare design atomLabel - atomShare design atomLabel ^ 2)
      ≤ (rank : ℝ) := by
  have hsubset : heavySet design ⊆ Finset.univ := Finset.subset_univ _
  have hnonneg : ∀ atomLabel ∈ Finset.univ, atomLabel ∉ heavySet design →
      0 ≤ atomShare design atomLabel - atomShare design atomLabel ^ 2 :=
    fun atomLabel _ _ => atomShare_gap_nonneg design atomLabel
  have hwhole : ∑ atomLabel : Fin size,
      (atomShare design atomLabel - atomShare design atomLabel ^ 2) ≤ (rank : ℝ) := by
    rw [Finset.sum_sub_distrib, sum_atomShare_eq_rank design]
    have hsquares : 0 ≤ ∑ atomLabel : Fin size, atomShare design atomLabel ^ 2 :=
      Finset.sum_nonneg fun atomLabel _ => sq_nonneg _
    linarith
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg) hwhole

/-! ## The contradiction, and the theorem -/

/-- Squaring out a total: each element times the complementary total. -/
theorem sum_mul_total_sub_self (labelSet : Finset (Fin size)) (massOf : Fin size → ℝ) :
    ∑ atomLabel ∈ labelSet,
        massOf atomLabel * ((∑ otherLabel ∈ labelSet, massOf otherLabel) - massOf atomLabel)
      = (∑ atomLabel ∈ labelSet, massOf atomLabel) ^ 2
        - ∑ atomLabel ∈ labelSet, massOf atomLabel ^ 2 := by
  have hterm : ∀ atomLabel ∈ labelSet,
      massOf atomLabel * ((∑ otherLabel ∈ labelSet, massOf otherLabel) - massOf atomLabel)
        = massOf atomLabel * (∑ otherLabel ∈ labelSet, massOf otherLabel)
            - massOf atomLabel ^ 2 :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]

/-- The closing arithmetic, with no design in sight: an excess budget of at least
`rank - 1` cannot fit inside a share-gap ceiling of the rank once the square-sum
is capped by a quarter of the total. -/
theorem false_of_heavyLedger_ceiling (rankReal heavyTotal squareTotal gapTotal : ℝ)
    (hrank : 3 ≤ rankReal)
    (hbudget : rankReal - 1 ≤ heavyTotal)
    (hrowSum : heavyTotal ^ 2 - squareTotal ≤ gapTotal)
    (hsquares : squareTotal ≤ 1 / 4 * heavyTotal)
    (hceiling : gapTotal ≤ rankReal) : False := by
  have hmonotone : 0 ≤ (heavyTotal - (rankReal - 1)) * (heavyTotal + (rankReal - 1) - 1 / 4) :=
    mul_nonneg (by linarith) (by linarith)
  have hrankGap : 0 ≤ (rankReal - 3) * (rankReal - 1 / 4) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hmonotone, hrankGap, hrowSum, hsquares, hceiling, hbudget]

/-- **EVERY DESIGN OF RANK AT LEAST THREE HAS A LIVE PAIR.**  Two distinct heavy
labels whose two by two minor of `Gram - 1` is strictly positive.  No hypothesis
on the design beyond its rank: not heaviness, not primitivity, not tightness, no
bound on the number of atoms, no genericity. -/
theorem exists_pos_pairGapExcessOf (design : WeightedDesign size rank) (hrank : 3 ≤ rank) :
    ∃ firstLabel secondLabel : Fin size, firstLabel ≠ secondLabel
      ∧ 0 < gapExcessOf design firstLabel
      ∧ 0 < gapExcessOf design secondLabel
      ∧ 0 < pairGapExcessOf design firstLabel secondLabel := by
  by_contra hcontra
  push Not at hcontra
  have hnolive : ∀ firstLabel ∈ heavySet design, ∀ secondLabel ∈ heavySet design,
      firstLabel ≠ secondLabel → pairGapExcessOf design firstLabel secondLabel ≤ 0 := by
    intro firstLabel hfirst secondLabel hsecond hne
    exact hcontra firstLabel secondLabel hne
      ((mem_heavySet_iff design firstLabel).mp hfirst)
      ((mem_heavySet_iff design secondLabel).mp hsecond)
  have hrankReal : (3 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hbudget := rank_sub_one_le_sum_heavyMassOf_heavySet design
  have hrowSum : ∑ atomLabel ∈ heavySet design,
      heavyMassOf design atomLabel
        * ((∑ otherLabel ∈ heavySet design, heavyMassOf design otherLabel)
            - heavyMassOf design atomLabel)
      ≤ ∑ atomLabel ∈ heavySet design,
          (atomShare design atomLabel - atomShare design atomLabel ^ 2) :=
    Finset.sum_le_sum fun atomLabel hmem =>
      heavyMassOf_mul_sub_le_atomShare_gap design hnolive hmem
  rw [sum_mul_total_sub_self] at hrowSum
  exact false_of_heavyLedger_ceiling (rank : ℝ)
    (∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel)
    (∑ atomLabel ∈ heavySet design, heavyMassOf design atomLabel ^ 2)
    (∑ atomLabel ∈ heavySet design,
      (atomShare design atomLabel - atomShare design atomLabel ^ 2))
    hrankReal hbudget hrowSum
    (sum_sq_heavyMassOf_le_quarter_mul design hrank hnolive)
    (sum_atomShare_gap_heavySet_le_rank design)

/-! ## Rank three: two of Sylvester's three conditions are free -/

variable {m : ℕ}

/-- The rank three reading, in the discriminant system's own vocabulary.  The three
conjuncts are exactly the unfolding of the depth-cap lane's liveness predicate. -/
theorem exists_livePair_rankThree (design : WeightedDesign m 3) :
    ∃ pivotLabel pairLabel : Fin m, pivotLabel ≠ pairLabel
      ∧ 0 < heavyExcess design pivotLabel
      ∧ 0 < heavyExcess design pairLabel
      ∧ 0 < pairGapExcessOf design pivotLabel pairLabel := by
  obtain ⟨pivotLabel, pairLabel, hne, hpivot, hpair, hminor⟩ :=
    exists_pos_pairGapExcessOf design (le_refl 3)
  exact ⟨pivotLabel, pairLabel, hne, hpivot, hpair, hminor⟩

/-- **Sylvester collapses at a live pair.**  Positive corner and positive leading
two by two minor come from liveness; the determinant leg is the tree's
`discriminantTie`.  So one sign decides the gap matrix. -/
theorem posDef_tripleGapMatrix_of_livePair (design : WeightedDesign m 3)
    (pivotLabel pairFirst pairSecond : Fin m)
    (hpivotHeavy : 0 < heavyExcess design pivotLabel)
    (hlive : 0 < pairGapExcessOf design pivotLabel pairFirst)
    (hdeterminant : 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    (tripleGapMatrix design pivotLabel pairFirst pairSecond).PosDef := by
  have hblock : 0 < heavyExcess design pivotLabel * heavyExcess design pairFirst
      - atomPairing design pivotLabel pairFirst ^ 2 := by
    simpa only [pairGapExcessOf, gapExcessOf, gapPairingOf, heavyExcess, atomPairing] using hlive
  have hdetEq : heavyExcess design pivotLabel * heavyExcess design pairFirst
        * heavyExcess design pairSecond
      - heavyExcess design pivotLabel * atomPairing design pairFirst pairSecond ^ 2
      - atomPairing design pivotLabel pairFirst ^ 2 * heavyExcess design pairSecond
      + 2 * atomPairing design pivotLabel pairFirst * atomPairing design pivotLabel pairSecond
          * atomPairing design pairFirst pairSecond
      - atomPairing design pivotLabel pairSecond ^ 2 * heavyExcess design pairFirst
      = discriminantTie design pivotLabel pairFirst pairSecond := by
    simp only [discriminantTie]
    ring
  have hdet : 0 < heavyExcess design pivotLabel * heavyExcess design pairFirst
        * heavyExcess design pairSecond
      - heavyExcess design pivotLabel * atomPairing design pairFirst pairSecond ^ 2
      - atomPairing design pivotLabel pairFirst ^ 2 * heavyExcess design pairSecond
      + 2 * atomPairing design pivotLabel pairFirst * atomPairing design pivotLabel pairSecond
          * atomPairing design pairFirst pairSecond
      - atomPairing design pivotLabel pairSecond ^ 2 * heavyExcess design pairFirst := by
    rw [hdetEq]; exact hdeterminant
  simpa only [tripleGapMatrix] using
    posDef_of_leadingMinors_fin_three (heavyExcess design pivotLabel)
      (atomPairing design pivotLabel pairFirst) (atomPairing design pivotLabel pairSecond)
      (heavyExcess design pairFirst) (atomPairing design pairFirst pairSecond)
      (heavyExcess design pairSecond) hpivotHeavy hblock hdet

/-- The same, read on the object domination is about. -/
theorem posDef_subsetSum_sub_one_of_livePair (design : WeightedDesign m 3)
    {pivotLabel pairFirst pairSecond : Fin m}
    (hpivotFirst : pivotLabel ≠ pairFirst) (hpivotSecond : pivotLabel ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 0 < heavyExcess design pivotLabel)
    (hlive : 0 < pairGapExcessOf design pivotLabel pairFirst)
    (hdeterminant : 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    (subsetSum design {pivotLabel, pairFirst, pairSecond} - 1).PosDef :=
  (posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix design hpivotFirst hpivotSecond
    hpairDistinct).mpr
    (posDef_tripleGapMatrix_of_livePair design pivotLabel pairFirst pairSecond hpivotHeavy
      hlive hdeterminant)

/-- A live pair plus one positive determinant is a dominating triple. -/
theorem dominates_of_livePair (design : WeightedDesign m 3)
    {pivotLabel pairFirst pairSecond : Fin m}
    (hpivotFirst : pivotLabel ≠ pairFirst) (hpivotSecond : pivotLabel ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 0 < heavyExcess design pivotLabel)
    (hlive : 0 < pairGapExcessOf design pivotLabel pairFirst)
    (hdeterminant : 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    Dominates design {pivotLabel, pairFirst, pairSecond} :=
  (posDef_subsetSum_sub_one_of_livePair design hpivotFirst hpivotSecond hpairDistinct
    hpivotHeavy hlive hdeterminant).posSemidef

/-- **THE DOMINATION TEST COLLAPSES TO ONE DETERMINANT, FOR EVERY DESIGN.**  Every
rank three weighted design carries a pair of labels at which strict domination of
any completing triple is decided by the sign of `discriminantTie` alone: the corner
and the leading two by two minor of Sylvester's criterion are already positive, for
free, with no hypothesis on the design. -/
theorem exists_livePair_determinantOnly (design : WeightedDesign m 3) :
    ∃ pivotLabel pairFirst : Fin m, pivotLabel ≠ pairFirst
      ∧ 0 < heavyExcess design pivotLabel
      ∧ 0 < heavyExcess design pairFirst
      ∧ 0 < pairGapExcessOf design pivotLabel pairFirst
      ∧ ∀ pairSecond : Fin m, pivotLabel ≠ pairSecond → pairFirst ≠ pairSecond →
          0 < discriminantTie design pivotLabel pairFirst pairSecond →
          (subsetSum design {pivotLabel, pairFirst, pairSecond} - 1).PosDef
            ∧ Dominates design {pivotLabel, pairFirst, pairSecond} := by
  obtain ⟨pivotLabel, pairFirst, hne, hpivot, hpair, hminor⟩ := exists_livePair_rankThree design
  refine ⟨pivotLabel, pairFirst, hne, hpivot, hpair, hminor, ?_⟩
  intro pairSecond hpivotSecond hpairDistinct hdeterminant
  exact ⟨posDef_subsetSum_sub_one_of_livePair design hne hpivotSecond hpairDistinct hpivot
      hminor hdeterminant,
    dominates_of_livePair design hne hpivotSecond hpairDistinct hpivot hminor hdeterminant⟩

/-- The unconditional theorem instantiated at the campaign's hardest small fixture:
the tetrahedron is a tie, yet it still carries a live pair. -/
theorem tetraDesign_exists_livePair :
    ∃ pivotLabel pairLabel : Fin 4, pivotLabel ≠ pairLabel
      ∧ 0 < heavyExcess tetraDesign pivotLabel
      ∧ 0 < heavyExcess tetraDesign pairLabel
      ∧ 0 < pairGapExcessOf tetraDesign pivotLabel pairLabel :=
  exists_livePair_rankThree tetraDesign

end Gtz

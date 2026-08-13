import Gtz.Wave.OuterTraceThreeInterior
import Gtz.Wave.CertificateCornerBackbone
import Gtz.Wave.CycleSeamReduction
import Gtz.Wave.SharedPairOuterReduction
import Gtz.Wave.CarriedRowReading
import Gtz.Wave.AssemblyBasisCoverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer dense corner kill — the two-carrier branch of the outer datum dies

The block-degree dispatch splits a rank-four outer datum into the pin
branch and the dense branch.  This module kills the dense branch, with
no Gram hypothesis and no interiority hypothesis.

At a two-carrier atom the coordinate row of the basis columns vanishes
off the carrier pair, thus the carried row law collapses to a corner
read of the coefficient matrix.  The corner calculus then applies to the
coefficient matrix itself: the products price the off-corner entries,
the opposite-pair dichotomy prices the complementary corners, and the
excess balance prices the six corner determinants.  The support-two
column supplies the case split: a doubled carrier pair is either
independent, and then the pair trace law plus the dichotomy break the
weight cone, or parallel, and then the difference of the two columns is
a single-atom vector whose gap row forces the gap diagonal to the value.
The remaining profile is the tetrahedron, and the K4 balance kills it.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.corner_product_of_reads_alive` — the corner product law without
  nonvanishing hypotheses.
* `Gtz.corner_dichotomy_quadruple`, `Gtz.esum_quadruple`,
  `Gtz.kfour_excess_quadruple` — the corner calculus at four abstract
  slots.
* `Gtz.false_of_quadruple_kfour_products` — **THE K4 KILL.**
* `Gtz.exists_complement_pair_of_degree` — **THE COMPLEMENT LAW.**
* `Gtz.false_of_parallel_pair_column_combination` — **THE PARALLEL
  KILL.**
* `Gtz.RankFourFrame.false_of_independent_dense_pair` — the independent
  doubled pair dies.
* `Gtz.RankFourFrame.false_of_dense_pair_column` — **THE DENSE KILL.**
* `Gtz.RankFourOuterData.false_of_dense`,
  `Gtz.RankFourOuterData.exists_block_pin` — the outer readings.
* `Gtz.rankFourOuterKilled_of_circuit_interior`,
  `Gtz.rankFourSupportTwoClosed_of_circuit_interior` — **THE RANK-FOUR
  CLOSURE-ONE REDUCTION.**

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the corner calculus at four abstract slots -/

/-- The corner product law with no nonvanishing hypothesis: one alive
coordinate is enough. -/
theorem corner_product_of_reads_alive {a b tii tjj mij mji d : ℝ}
    (halive : a ≠ 0 ∨ b ≠ 0)
    (h1 : a * tii + b * mji = d * a) (h2 : a * mij + b * tjj = d * b) :
    mij * mji = (d - tii) * (d - tjj) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := halive.resolve_left (by simp)
    have hmji : mji = 0 := by
      have hzero : b * mji = 0 := by linear_combination h1
      exact (mul_eq_zero.mp hzero).resolve_left hb
    have htjj : tjj = d := by
      have hzero : b * (tjj - d) = 0 := by linear_combination h2
      have hfac := (mul_eq_zero.mp hzero).resolve_left hb
      linarith
    rw [hmji, htjj]
    ring
  rcases eq_or_ne b 0 with rfl | hb
  · have hmij : mij = 0 := by
      have hzero : a * mij = 0 := by linear_combination h2
      exact (mul_eq_zero.mp hzero).resolve_left ha
    have htii : tii = d := by
      have hzero : a * (tii - d) = 0 := by linear_combination h1
      have hfac := (mul_eq_zero.mp hzero).resolve_left ha
      linarith
    rw [hmij, htii]
    ring
  exact corner_product_of_reads ha hb h1 h2

section Quadruple

variable {M : Matrix (Fin 4) (Fin 4) ℝ} {i j k l : Fin 4}

/-- The diagonal idempotency entry expanded over four distinct slots. -/
theorem idempotent_diagonal_quadruple (hidem : M * M = M)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    M i i * M i i + M i j * M j i + M i k * M k i + M i l * M l i = M i i := by
  have hentry := congrFun (congrFun hidem i) i
  rw [Matrix.mul_apply] at hentry
  rwa [sum_four_slots (fun slot => M i slot * M slot i) hij hik hil hjk hjl
    hkl] at hentry

/-- The trace expanded over four distinct slots. -/
theorem trace_quadruple (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Matrix.trace M = M i i + M j j + M k k + M l l := by
  rw [Matrix.trace]
  exact sum_four_slots (fun slot => M slot slot) hij hik hil hjk hjl hkl

/-- **THE OPPOSITE-PAIR DICHOTOMY AT FOUR ABSTRACT SLOTS.**  A corner
eigenvalue at one pair and a corner eigenvalue at the complementary pair
of a trace-two idempotent satisfy the product identity. -/
theorem corner_dichotomy_quadruple {x y : ℝ} (hidem : M * M = M)
    (htr : Matrix.trace M = 2)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hx : M i j * M j i = (x - M i i) * (x - M j j))
    (hy : M k l * M l k = (y - M k k) * (y - M l l)) :
    (x + y - 1) * (M i i + M j j - x + y - 1) = 0 := by
  have hi := idempotent_diagonal_quadruple hidem hij hik hil hjk hjl hkl
  have hj := idempotent_diagonal_quadruple hidem hij.symm hjk hjl hik hil hkl
  have hk := idempotent_diagonal_quadruple hidem hik.symm hjk.symm hkl hij hil
    hjl
  have hl := idempotent_diagonal_quadruple hidem hil.symm hjl.symm hkl.symm hij
    hik hjk
  have htrExp : M i i + M j j + M k k + M l l = 2 := by
    rw [← trace_quadruple hij hik hil hjk hjl hkl]
    exact htr
  linear_combination (-(1 : ℝ) / 2) * hi + (-(1 : ℝ) / 2) * hj
    + ((1 : ℝ) / 2) * hk + ((1 : ℝ) / 2) * hl + hx - hy
    + (y + (M i i + M j j) / 2 - (M k k + M l l) / 2 - 1 / 2) * htrExp

/-- The six principal two-by-two minors of a trace-two idempotent sum to
one, at four abstract slots. -/
theorem esum_quadruple (hidem : M * M = M) (htr : Matrix.trace M = 2)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (M i i * M j j - M i j * M j i) + (M i i * M k k - M i k * M k i)
      + (M i i * M l l - M i l * M l i) + (M j j * M k k - M j k * M k j)
      + (M j j * M l l - M j l * M l j) + (M k k * M l l - M k l * M l k)
      = 1 := by
  have hi := idempotent_diagonal_quadruple hidem hij hik hil hjk hjl hkl
  have hj := idempotent_diagonal_quadruple hidem hij.symm hjk hjl hik hil hkl
  have hk := idempotent_diagonal_quadruple hidem hik.symm hjk.symm hkl hij hil
    hjl
  have hl := idempotent_diagonal_quadruple hidem hil.symm hjl.symm hkl.symm hij
    hik hjk
  have htrExp : M i i + M j j + M k k + M l l = 2 := by
    rw [← trace_quadruple hij hik hil hjk hjl hkl]
    exact htr
  linear_combination ((M i i + M j j + M k k + M l l + 1) / 2) * htrExp
    - (1 / 2) * hi - (1 / 2) * hj - (1 / 2) * hk - (1 / 2) * hl

/-- **THE K4 BALANCE AT FOUR ABSTRACT SLOTS.**  Six corner products
price the corner excess sum as one. -/
theorem kfour_excess_quadruple {dij dik dil djk djl dkl : ℝ}
    (hidem : M * M = M) (htr : Matrix.trace M = 2)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (pij : M i j * M j i = (dij - M i i) * (dij - M j j))
    (pik : M i k * M k i = (dik - M i i) * (dik - M k k))
    (pil : M i l * M l i = (dil - M i i) * (dil - M l l))
    (pjk : M j k * M k j = (djk - M j j) * (djk - M k k))
    (pjl : M j l * M l j = (djl - M j j) * (djl - M l l))
    (pkl : M k l * M l k = (dkl - M k k) * (dkl - M l l)) :
    dij * (M i i + M j j - dij) + dik * (M i i + M k k - dik)
      + dil * (M i i + M l l - dil) + djk * (M j j + M k k - djk)
      + djl * (M j j + M l l - djl) + dkl * (M k k + M l l - dkl) = 1 := by
  have hesum := esum_quadruple hidem htr hij hik hil hjk hjl hkl
  linear_combination hesum + pij + pik + pil + pjk + pjl + pkl

/-- **THE K4 KILL.**  Six corner reads on the six pairs of four slots,
with positive weights summing to one and a negative value, are
contradictory.  A sum branch equates twice the value with a positive
weight sum.  The all-tau branch collapses the excess balance to the
opposite weight products against a negative right side. -/
theorem false_of_quadruple_kfour_products
    {value wij wik wil wjk wjl wkl : ℝ}
    (hidem : M * M = M) (htr : Matrix.trace M = 2)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hvalue : value < 0)
    (hwij : 0 < wij) (hwik : 0 < wik) (hwil : 0 < wil)
    (hwjk : 0 < wjk) (hwjl : 0 < wjl) (hwkl : 0 < wkl)
    (hwsum : wij + wik + wil + wjk + wjl + wkl = 1)
    (pij : M i j * M j i
      = (value + wij - M i i) * (value + wij - M j j))
    (pik : M i k * M k i
      = (value + wik - M i i) * (value + wik - M k k))
    (pil : M i l * M l i
      = (value + wil - M i i) * (value + wil - M l l))
    (pjk : M j k * M k j
      = (value + wjk - M j j) * (value + wjk - M k k))
    (pjl : M j l * M l j
      = (value + wjl - M j j) * (value + wjl - M l l))
    (pkl : M k l * M l k
      = (value + wkl - M k k) * (value + wkl - M l l)) :
    False := by
  have htrExp : M i i + M j j + M k k + M l l = 2 := by
    rw [← trace_quadruple hij hik hil hjk hjl hkl]
    exact htr
  have hD1 := corner_dichotomy_quadruple hidem htr hij hik hil hjk hjl hkl pij
    pkl
  have hD2 := corner_dichotomy_quadruple hidem htr hik hij hil hjk.symm hkl hjl
    pik pjl
  have hD3 := corner_dichotomy_quadruple hidem htr hil hij hik hjl.symm
    hkl.symm hjk pil pjk
  rcases mul_eq_zero.mp hD1 with hsum1 | htau1
  · linarith
  rcases mul_eq_zero.mp hD2 with hsum2 | htau2
  · linarith
  rcases mul_eq_zero.mp hD3 with hsum3 | htau3
  · linarith
  have hbal := kfour_excess_quadruple hidem htr hij hik hil hjk hjl hkl pij pik
    pil pjk pjl pkl
  have hkey : wij * wkl + wik * wjl + wil * wjk
      = 2 * value - 3 * value ^ 2 := by
    linear_combination (-(1 : ℝ) / 2) * hbal + ((wij - wkl) / 2) * htau1
      + ((wik - wjl) / 2) * htau2 + ((wil - wjk) / 2) * htau3
      + ((3 * value + wjk + wjl + wkl) / 2) * htrExp
      - ((2 * value - 1) / 2) * hwsum
  linarith [mul_pos hwij hwkl, mul_pos hwik hwjl, mul_pos hwil hwjk,
    sq_nonneg value]

end Quadruple

/-! ## Layer 2 — the carrier combinatorics -/

/-- A two-element set with a named member names its partner. -/
theorem exists_pair_partner {α : Type*} [DecidableEq α] {s : Finset α}
    (hcard : s.card = 2) {slot : α} (hmem : slot ∈ s) :
    ∃ other : α, other ≠ slot ∧ s = {slot, other} := by
  obtain ⟨first, second, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  rcases Finset.mem_insert.mp hmem with rfl | hmem'
  · exact ⟨second, Ne.symm hne, rfl⟩
  · rw [Finset.mem_singleton] at hmem'
    subst hmem'
    exact ⟨first, hne, Finset.pair_comm first slot⟩

/-- The two slots outside a named pair of four slots. -/
theorem exists_complement_slots {slotOne slotTwo : Fin 4}
    (hne : slotOne ≠ slotTwo) :
    ∃ slotThree slotFour : Fin 4, slotThree ≠ slotFour
      ∧ slotOne ≠ slotThree ∧ slotOne ≠ slotFour
      ∧ slotTwo ≠ slotThree ∧ slotTwo ≠ slotFour := by
  classical
  have hcard : (Finset.univ \ ({slotOne, slotTwo} : Finset (Fin 4))).card
      = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hne]),
      Finset.card_singleton]
  obtain ⟨slotThree, slotFour, h34, hset⟩ := Finset.card_eq_two.mp hcard
  have hmemThree : slotThree ∈ Finset.univ \ ({slotOne, slotTwo}
      : Finset (Fin 4)) := by
    rw [hset]
    exact Finset.mem_insert_self _ _
  have hmemFour : slotFour ∈ Finset.univ \ ({slotOne, slotTwo}
      : Finset (Fin 4)) := by
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hnotThree := (Finset.mem_sdiff.mp hmemThree).2
  have hnotFour := (Finset.mem_sdiff.mp hmemFour).2
  refine ⟨slotThree, slotFour, h34, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hnotThree (heq ▸ Finset.mem_insert_self _ _)
  · intro heq
    exact hnotFour (heq ▸ Finset.mem_insert_self _ _)
  · intro heq
    exact hnotThree (heq ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))
  · intro heq
    exact hnotFour (heq ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _))

/-- **THE COMPLEMENT LAW.**  With two carriers at every atom and three
carriers at every slot, a populated pair forces its complementary pair
to be populated.  The incidence count of the pair is six, every atom
meets the pair, and the named atom meets it twice. -/
theorem exists_complement_pair_of_degree {car : Fin 6 → Finset (Fin 4)}
    (hcard : ∀ atomIndex : Fin 6, (car atomIndex).card = 2)
    (hinc : ∀ slot : Fin 4,
      (Finset.univ.filter fun atomIndex : Fin 6 => slot ∈ car atomIndex).card
        = 3)
    {slotOne slotTwo slotThree slotFour : Fin 4}
    (h12 : slotOne ≠ slotTwo) (h13 : slotOne ≠ slotThree)
    (h14 : slotOne ≠ slotFour) (h23 : slotTwo ≠ slotThree)
    (h24 : slotTwo ≠ slotFour) (h34 : slotThree ≠ slotFour)
    {atomZero : Fin 6} (hatomZero : car atomZero = {slotOne, slotTwo}) :
    ∃ atomIndex : Fin 6, car atomIndex = {slotThree, slotFour} := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum : ∑ atomIndex : Fin 6,
      ((if slotOne ∈ car atomIndex then 1 else 0)
        + (if slotTwo ∈ car atomIndex then 1 else 0)) = 6 := by
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter,
      hinc slotOne, hinc slotTwo]
  have hone : ∀ atomIndex : Fin 6,
      1 ≤ (if slotOne ∈ car atomIndex then 1 else 0)
        + (if slotTwo ∈ car atomIndex then 1 else 0) := by
    intro atomIndex
    by_cases h1 : slotOne ∈ car atomIndex
    · rw [if_pos h1]
      omega
    by_cases h2 : slotTwo ∈ car atomIndex
    · rw [if_neg h1, if_pos h2]
    · exfalso
      have hsubset : car atomIndex ⊆ ({slotThree, slotFour}
          : Finset (Fin 4)) := by
        intro slot hslot
        have huniv : slot ∈ ({slotOne, slotTwo, slotThree, slotFour}
            : Finset (Fin 4)) := by
          rw [slot_quadruple_eq_univ h12 h13 h14 h23 h24 h34]
          exact Finset.mem_univ slot
        rcases Finset.mem_insert.mp huniv with rfl | hrest
        · exact absurd hslot h1
        rcases Finset.mem_insert.mp hrest with rfl | hrest'
        · exact absurd hslot h2
        · exact hrest'
      have hcardPair : ({slotThree, slotFour} : Finset (Fin 4)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [h34]),
          Finset.card_singleton]
      exact hnone atomIndex (Finset.eq_of_subset_of_card_le hsubset
        (by rw [hcard atomIndex, hcardPair]))
  have htwo : (if slotOne ∈ car atomZero then 1 else 0)
      + (if slotTwo ∈ car atomZero then 1 else 0) = 2 := by
    rw [hatomZero, if_pos (Finset.mem_insert_self _ _),
      if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun atomIndex : Fin 6 =>
      (if slotOne ∈ car atomIndex then 1 else 0)
        + (if slotTwo ∈ car atomIndex then 1 else 0))
    (Finset.mem_univ atomZero)
  have herase : 5 * 1 ≤ ∑ atomIndex ∈ Finset.univ.erase atomZero,
      ((if slotOne ∈ car atomIndex then 1 else 0)
        + (if slotTwo ∈ car atomIndex then 1 else 0)) := by
    have hbound := Finset.card_nsmul_le_sum (Finset.univ.erase atomZero)
      (fun atomIndex : Fin 6 =>
        (if slotOne ∈ car atomIndex then 1 else 0)
          + (if slotTwo ∈ car atomIndex then 1 else 0)) 1
      (fun atomIndex _ => hone atomIndex)
    rwa [Finset.card_erase_of_mem (Finset.mem_univ atomZero),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  omega

/-- Two atoms with different carriers are different atoms. -/
theorem atom_ne_of_carrier_mem_notMem {car : Fin 6 → Finset (Fin 4)}
    {atomOne atomTwo : Fin 6} {slot : Fin 4} (hmem : slot ∈ car atomOne)
    (hnot : slot ∉ car atomTwo) : atomOne ≠ atomTwo := by
  intro heq
  rw [heq] at hmem
  exact hnot hmem

/-! ## Layer 3 — the datum kills -/

section Datum

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- Two shifted weights summing to one break the weight cone: the other
atoms carry a positive weight, thus twice the value is positive. -/
theorem false_of_shifted_pair_sum_one
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalue : value < 0) {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo)
    (hsum : (value + weight atomOne) + (value + weight atomTwo) = 1) :
    False := by
  classical
  have hpairCard : ({atomOne, atomTwo} : Finset (Fin size)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hsplit := Finset.sum_sdiff (f := weight)
    (Finset.subset_univ ({atomOne, atomTwo} : Finset (Fin size)))
  have hpairSum : ∑ atomIndex ∈ ({atomOne, atomTwo} : Finset (Fin size)),
      weight atomIndex = weight atomOne + weight atomTwo :=
    Finset.sum_pair hne
  have hcompl : 0 < ∑ atomIndex ∈ Finset.univ
      \ ({atomOne, atomTwo} : Finset (Fin size)), weight atomIndex := by
    refine Finset.sum_pos (fun atomIndex _ => hdata.weight_pos atomIndex) ?_
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hpairCard]
    have hsize : 2 < Fintype.card (Fin size) := by
      by_contra hle
      have hcardLe : Fintype.card (Fin size) ≤ 2 := by omega
      have hcardPair : ({atomOne, atomTwo} : Finset (Fin size)).card
          ≤ Fintype.card (Fin size) := Finset.card_le_univ _
      rw [hpairCard] at hcardPair
      have hcardEq : Fintype.card (Fin size) = 2 := by omega
      have hall : ({atomOne, atomTwo} : Finset (Fin size)) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hpairCard, hcardEq])
      have hsumAll := hdata.weight_sum_one
      rw [← hall, hpairSum] at hsumAll
      linarith
    omega
  have htotal := hdata.weight_sum_one
  rw [← hsplit, hpairSum] at htotal
  linarith

/-- **THE PARALLEL KILL.**  A support-two column and a second column
proportional to it on the pair leave a single-atom difference.  The two
pair rows annihilate the gap column at the single atom, and the row of
the single atom then prices the gap diagonal at the value, against the
positive floor. -/
theorem false_of_parallel_pair_column_combination
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalue : value < 0) {labelPair labelOther : activeIndex}
    (hpairMem : labelPair ∈ activeSet) (hotherMem : labelOther ∈ activeSet)
    {atomU atomV atomS : Fin size} {scale : ℝ}
    (hUV : atomU ≠ atomV) (hSU : atomS ≠ atomU) (hSV : atomS ≠ atomV)
    (hUpair : atomU ∈ activeSubset labelPair)
    (hVpair : atomV ∈ activeSubset labelPair)
    (hpairSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir labelPair atomIndex = 0)
    (hUother : atomU ∈ activeSubset labelOther)
    (hVother : atomV ∈ activeSubset labelOther)
    (hSother : atomS ∈ activeSubset labelOther)
    (hotherSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelOther atomIndex = 0)
    (hparU : tightDir labelOther atomU = scale * tightDir labelPair atomU)
    (hparV : tightDir labelOther atomV = scale * tightDir labelPair atomV)
    (hneS : tightDir labelOther atomS ≠ 0)
    (hfloor : 0 < chartStationaryGap projection weight atomS atomS) :
    False := by
  classical
  have hsymm := chartStationaryGap_transpose hdata.isSymmetric weight
  have hentrySymm : ∀ rowIndex colIndex : Fin size,
      chartStationaryGap projection weight rowIndex colIndex
        = chartStationaryGap projection weight colIndex rowIndex := by
    intro rowIndex colIndex
    have hcongr := congrFun (congrFun hsymm colIndex) rowIndex
    rw [Matrix.transpose_apply] at hcongr
    exact hcongr
  have hcomboSupp : ∀ atomIndex, atomIndex ≠ atomS →
      (tightDir labelOther atomIndex
        - scale * tightDir labelPair atomIndex) = 0 := by
    intro atomIndex hne
    by_cases hU : atomIndex = atomU
    · rw [hU, hparU]
      ring
    by_cases hV : atomIndex = atomV
    · rw [hV, hparV]
      ring
    · rw [hotherSupp atomIndex hU hV hne, hpairSupp atomIndex hU hV]
      ring
  have hcomboS : tightDir labelOther atomS - scale * tightDir labelPair atomS
      = tightDir labelOther atomS := by
    rw [hpairSupp atomS hSU hSV]
    ring
  have haction : ∀ atomIndex : Fin size,
      (chartStationaryGap projection weight *ᵥ (fun atomOther =>
          tightDir labelOther atomOther
            - scale * tightDir labelPair atomOther)) atomIndex
        = (chartStationaryGap projection weight *ᵥ tightDir labelOther)
            atomIndex
          - scale * (chartStationaryGap projection weight
            *ᵥ tightDir labelPair) atomIndex := by
    intro atomIndex
    show (∑ atomOther, chartStationaryGap projection weight atomIndex atomOther
        * (tightDir labelOther atomOther
          - scale * tightDir labelPair atomOther)) = _
    have hterm : ∀ atomOther : Fin size,
        chartStationaryGap projection weight atomIndex atomOther
            * (tightDir labelOther atomOther
              - scale * tightDir labelPair atomOther)
          = chartStationaryGap projection weight atomIndex atomOther
              * tightDir labelOther atomOther
            - scale * (chartStationaryGap projection weight atomIndex atomOther
              * tightDir labelPair atomOther) := by
      intro atomOther
      ring
    rw [Finset.sum_congr rfl fun atomOther _ => hterm atomOther,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  have hrowU : chartStationaryGap projection weight atomU atomS = 0 := by
    have hread := haction atomU
    rw [mulVec_apply_of_single_support _ hcomboSupp atomU, hcomboS,
      hdata.tightDir_isTight labelOther hotherMem atomU hUother,
      hdata.tightDir_isTight labelPair hpairMem atomU hUpair] at hread
    have hzero : chartStationaryGap projection weight atomU atomS
        * tightDir labelOther atomS = 0 := by
      rw [hread, hparU]
      ring
    exact (mul_eq_zero.mp hzero).resolve_right hneS
  have hrowV : chartStationaryGap projection weight atomV atomS = 0 := by
    have hread := haction atomV
    rw [mulVec_apply_of_single_support _ hcomboSupp atomV, hcomboS,
      hdata.tightDir_isTight labelOther hotherMem atomV hVother,
      hdata.tightDir_isTight labelPair hpairMem atomV hVpair] at hread
    have hzero : chartStationaryGap projection weight atomV atomS
        * tightDir labelOther atomS = 0 := by
      rw [hread, hparV]
      ring
    exact (mul_eq_zero.mp hzero).resolve_right hneS
  have hpairRow : (chartStationaryGap projection weight *ᵥ tightDir labelPair)
      atomS = 0 := by
    rw [mulVec_apply_of_pair_support _ hUV hpairSupp atomS,
      hentrySymm atomS atomU, hentrySymm atomS atomV, hrowU, hrowV]
    ring
  have hreadS := haction atomS
  rw [mulVec_apply_of_single_support _ hcomboSupp atomS, hcomboS, hpairRow,
    hdata.tightDir_isTight labelOther hotherMem atomS hSother] at hreadS
  have hdiag : chartStationaryGap projection weight atomS atomS = value := by
    have hcancel : (chartStationaryGap projection weight atomS atomS - value)
        * tightDir labelOther atomS = 0 := by
      rw [sub_mul]
      linarith [hreadS]
    have hfac := (mul_eq_zero.mp hcancel).resolve_right hneS
    linarith
  rw [hdiag] at hfloor
  linarith

/-- **THE PAIR-SUPPORTED INDEPENDENCE KILL.**  Two labels supported
inside one atom pair with an independent restriction force the gap
diagonal at the left atom to the value, against the positive floor. -/
theorem false_of_pair_supported_independent
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalue : value < 0) {labelOne labelTwo : activeIndex}
    (hmemOne : labelOne ∈ activeSet) (hmemTwo : labelTwo ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hsuppOne : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir labelOne atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir labelTwo atomIndex = 0)
    (hblockOne : atomU ∈ activeSubset labelOne)
    (hblockTwo : atomU ∈ activeSubset labelTwo)
    (hdet : tightDir labelOne atomU * tightDir labelTwo atomV
      - tightDir labelOne atomV * tightDir labelTwo atomU ≠ 0)
    (hfloor : 0 < chartStationaryGap projection weight atomU atomU) :
    False := by
  have hrowOne := hdata.tightDir_isTight labelOne hmemOne atomU hblockOne
  have hrowTwo := hdata.tightDir_isTight labelTwo hmemTwo atomU hblockTwo
  rw [mulVec_apply_of_pair_support _ hUV hsuppOne atomU] at hrowOne
  rw [mulVec_apply_of_pair_support _ hUV hsuppTwo atomU] at hrowTwo
  have hcancel : (chartStationaryGap projection weight atomU atomU - value)
      * (tightDir labelOne atomU * tightDir labelTwo atomV
        - tightDir labelOne atomV * tightDir labelTwo atomU) = 0 := by
    linear_combination (tightDir labelTwo atomV) * hrowOne
      - (tightDir labelOne atomV) * hrowTwo
  have hdiag := (mul_eq_zero.mp hcancel).resolve_right hdet
  have hvalueEq : chartStationaryGap projection weight atomU atomU = value := by
    linarith
  rw [hvalueEq] at hfloor
  linarith

end Datum

/-! ## Layer 4 — the frame reads -/

section FrameReads

variable {crux : SixThreeCrux}

/-- The coordinate of a basis column vanishes off the block carrier. -/
theorem RankFourFrame.tightDir_eq_zero_of_notMem_carrier
    (frame : RankFourFrame crux) {atomIndex : Fin 6} {slot : Fin 4}
    (hslot : slot ∉ blockCarrier frame.activeSubset frame.basisLabel
      atomIndex) :
    frame.tightDir (frame.basisLabel slot) atomIndex = 0 := by
  rw [blockCarrier_mem] at hslot
  exact frame.hdata.tightDir_support (frame.basisLabel slot)
    (frame.hmemAll slot) atomIndex hslot

/-- Some carrier slot of an atom is alive: the coverage law names it. -/
theorem RankFourFrame.dense_alive (frame : RankFourFrame crux)
    {atomIndex : Fin 6} {slotOne slotTwo : Fin 4}
    (hcar : blockCarrier frame.activeSubset frame.basisLabel atomIndex
      = {slotOne, slotTwo}) :
    frame.tightDir (frame.basisLabel slotOne) atomIndex ≠ 0
      ∨ frame.tightDir (frame.basisLabel slotTwo) atomIndex ≠ 0 := by
  classical
  obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport frame.hdata
    frame.basisLabel frame.hspan frame.leftInv frame.hleft atomIndex
  have hne := mem_datumTightSupport.mp hslot
  have hmem : slot ∈ blockCarrier frame.activeSubset frame.basisLabel
      atomIndex := by
    by_contra hout
    exact hne (frame.tightDir_eq_zero_of_notMem_carrier hout)
  rw [hcar] at hmem
  rcases Finset.mem_insert.mp hmem with rfl | hmem'
  · exact Or.inl hne
  · rw [Finset.mem_singleton] at hmem'
    subst hmem'
    exact Or.inr hne

/-- **THE TWO-CARRIER READ.**  At an atom with two carriers the carried
row law collapses to the carrier pair: the coordinate row is a left
eigen row of the corner at the shifted weight. -/
theorem RankFourFrame.dense_pair_read (frame : RankFourFrame crux)
    {atomIndex : Fin 6} {slotOne slotTwo : Fin 4} (hne : slotOne ≠ slotTwo)
    (hcar : blockCarrier frame.activeSubset frame.basisLabel atomIndex
      = {slotOne, slotTwo})
    {slot : Fin 4} (hslot : slot ∈ ({slotOne, slotTwo} : Finset (Fin 4))) :
    frame.tightDir (frame.basisLabel slotOne) atomIndex
        * frame.coeff slotOne slot
      + frame.tightDir (frame.basisLabel slotTwo) atomIndex
        * frame.coeff slotTwo slot
    = (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      * frame.tightDir (frame.basisLabel slot) atomIndex := by
  classical
  have hmemBlock : atomIndex ∈ frame.activeSubset (frame.basisLabel slot) := by
    rw [← blockCarrier_mem (activeSubset := frame.activeSubset)
      (basisLabel := frame.basisLabel), hcar]
    exact hslot
  have hrow := carried_row_reading frame.hdata frame.basisLabel
    frame.hrepresentation (frame.hmemAll slot) hmemBlock
  have hsupp : ∀ slotOther : Fin 4, slotOther ≠ slotOne → slotOther ≠ slotTwo →
      frame.tightDir (frame.basisLabel slotOther) atomIndex = 0 := by
    intro slotOther h1 h2
    refine frame.tightDir_eq_zero_of_notMem_carrier ?_
    rw [hcar]
    simp [h1, h2]
  calc frame.tightDir (frame.basisLabel slotOne) atomIndex
        * frame.coeff slotOne slot
      + frame.tightDir (frame.basisLabel slotTwo) atomIndex
        * frame.coeff slotTwo slot
      = ∑ columnIndex : Fin 4,
          frame.tightDir (frame.basisLabel columnIndex) atomIndex
            * frame.coeff columnIndex slot :=
        (pair_dotProduct hne hsupp fun slotOther =>
          frame.coeff slotOther slot).symm
    _ = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * frame.tightDir (frame.basisLabel slot) atomIndex := hrow

/-- The corner product at a two-carrier atom. -/
theorem RankFourFrame.dense_corner_product (frame : RankFourFrame crux)
    {atomIndex : Fin 6} {slotOne slotTwo : Fin 4} (hne : slotOne ≠ slotTwo)
    (hcar : blockCarrier frame.activeSubset frame.basisLabel atomIndex
      = {slotOne, slotTwo}) :
    frame.coeff slotOne slotTwo * frame.coeff slotTwo slotOne
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex
          - frame.coeff slotOne slotOne)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex
          - frame.coeff slotTwo slotTwo) :=
  corner_product_of_reads_alive (frame.dense_alive hcar)
    (frame.dense_pair_read hne hcar (Finset.mem_insert_self _ _))
    (frame.dense_pair_read hne hcar
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- **THE INDEPENDENT DOUBLED PAIR.**  Two atoms on one carrier pair with
a nonzero cross determinant price the corner trace.  The complementary
pair is populated, and its dichotomy equates a shifted weight pair with
one, against the weight cone. -/
theorem RankFourFrame.false_of_independent_dense_pair
    (frame : RankFourFrame crux)
    (hdense : ∀ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 2)
    {atomOne atomTwo : Fin 6} {slotOne slotTwo : Fin 4}
    (hslots : slotOne ≠ slotTwo)
    (hcarOne : blockCarrier frame.activeSubset frame.basisLabel atomOne
      = {slotOne, slotTwo})
    (hcarTwo : blockCarrier frame.activeSubset frame.basisLabel atomTwo
      = {slotOne, slotTwo})
    (hdet : frame.tightDir (frame.basisLabel slotOne) atomOne
          * frame.tightDir (frame.basisLabel slotTwo) atomTwo
        - frame.tightDir (frame.basisLabel slotOne) atomTwo
          * frame.tightDir (frame.basisLabel slotTwo) atomOne ≠ 0) :
    False := by
  classical
  obtain ⟨slotThree, slotFour, h34, h13, h14, h23, h24⟩ :=
    exists_complement_slots hslots
  obtain ⟨atomThree, hcarThree⟩ := exists_complement_pair_of_degree hdense
    (blockCarrier_incidence frame.hdata frame.hmemAll) hslots h13 h14 h23 h24
    h34 hcarOne
  have hpairTrace := pair_trace_of_reads
    (frame.dense_pair_read hslots hcarOne (Finset.mem_insert_self _ _))
    (frame.dense_pair_read hslots hcarOne
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    (frame.dense_pair_read hslots hcarTwo (Finset.mem_insert_self _ _))
    (frame.dense_pair_read hslots hcarTwo
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    hdet
  have hDich := corner_dichotomy_quadruple frame.hidempotent frame.htrace
    hslots h13 h14 h23 h24 h34 (frame.dense_corner_product hslots hcarOne)
    (frame.dense_corner_product h34 hcarThree)
  have hmemOne : slotOne ∈ blockCarrier frame.activeSubset frame.basisLabel
      atomOne := by
    rw [hcarOne]
    exact Finset.mem_insert_self _ _
  have hmemTwo : slotOne ∈ blockCarrier frame.activeSubset frame.basisLabel
      atomTwo := by
    rw [hcarTwo]
    exact Finset.mem_insert_self _ _
  have hnotThree : slotOne ∉ blockCarrier frame.activeSubset frame.basisLabel
      atomThree := by
    rw [hcarThree]
    simp [h13, h14]
  have hneOne : atomOne ≠ atomThree :=
    atom_ne_of_carrier_mem_notMem hmemOne hnotThree
  have hneTwo : atomTwo ≠ atomThree :=
    atom_ne_of_carrier_mem_notMem hmemTwo hnotThree
  rcases mul_eq_zero.mp hDich with hsum | htau
  · exact false_of_shifted_pair_sum_one frame.hdata frame.hvalueNeg hneOne
      (by linarith)
  · exact false_of_shifted_pair_sum_one frame.hdata frame.hvalueNeg hneTwo
      (by linarith)

end FrameReads

/-! ## Layer 5 — the dense kill -/

/-- **THE DENSE KILL.**  A rank-four frame with a support-two column and
two carriers at every atom dies.  The pair column's block names a third
atom, and the three carrier partners split the profile: a doubled pair
is independent, and the corner trace closes it, or parallel, and the
single-atom difference closes it.  Three distinct partners give the
tetrahedron, and the K4 balance closes it.  No Gram hypothesis and no
interiority hypothesis appear. -/
theorem RankFourFrame.false_of_dense_pair_column {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {slotC : Fin 4} {atomU atomV : Fin 6}
    (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel slotC) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel slotC) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel slotC) atomIndex = 0)
    (hdense : ∀ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 2) :
    False := by
  classical
  have hUblock : atomU ∈ frame.activeSubset (frame.basisLabel slotC) := by
    by_contra hout
    exact hneU (frame.hdata.tightDir_support _ (frame.hmemAll slotC) atomU hout)
  have hVblock : atomV ∈ frame.activeSubset (frame.basisLabel slotC) := by
    by_contra hout
    exact hneV (frame.hdata.tightDir_support _ (frame.hmemAll slotC) atomV hout)
  -- the third atom of the pair column's block
  have hsub : ({atomU, atomV} : Finset (Fin 6))
      ⊆ frame.activeSubset (frame.basisLabel slotC) := by
    intro atomIndex hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem'
    · exact hUblock
    · rw [Finset.mem_singleton] at hmem'
      subst hmem'
      exact hVblock
  have hcardPair : ({atomU, atomV} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hUV]), Finset.card_singleton]
  have hcardSdiff : (frame.activeSubset (frame.basisLabel slotC)
      \ ({atomU, atomV} : Finset (Fin 6))).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      frame.hdata.activeSubset_card _ (frame.hmemAll slotC), hcardPair]
  obtain ⟨atomT, hTset⟩ := Finset.card_eq_one.mp hcardSdiff
  have hTmem : atomT ∈ frame.activeSubset (frame.basisLabel slotC)
      ∧ atomT ∉ ({atomU, atomV} : Finset (Fin 6)) := by
    refine Finset.mem_sdiff.mp ?_
    rw [hTset]
    exact Finset.mem_singleton_self _
  have hTU : atomT ≠ atomU := by
    intro heq
    refine hTmem.2 ?_
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hTV : atomT ≠ atomV := by
    intro heq
    refine hTmem.2 ?_
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hTzero : frame.tightDir (frame.basisLabel slotC) atomT = 0 :=
    hsupp atomT hTU hTV
  -- the three carrier partners of the pair column
  obtain ⟨slotA, hAC, hUcar⟩ := exists_pair_partner (hdense atomU)
    (blockCarrier_mem.mpr hUblock)
  obtain ⟨slotB, hBC, hVcar⟩ := exists_pair_partner (hdense atomV)
    (blockCarrier_mem.mpr hVblock)
  obtain ⟨slotK, hKC, hTcar⟩ := exists_pair_partner (hdense atomT)
    (blockCarrier_mem.mpr hTmem.1)
  by_cases hAB : slotA = slotB
  · -- the two support atoms share one carrier pair
    subst hAB
    by_cases hdet : frame.tightDir (frame.basisLabel slotC) atomU
          * frame.tightDir (frame.basisLabel slotA) atomV
        - frame.tightDir (frame.basisLabel slotC) atomV
          * frame.tightDir (frame.basisLabel slotA) atomU = 0
    · -- the parallel branch: the single-atom difference
      set scale : ℝ := frame.tightDir (frame.basisLabel slotA) atomU
        / frame.tightDir (frame.basisLabel slotC) atomU with hscale
      have hparU : frame.tightDir (frame.basisLabel slotA) atomU
          = scale * frame.tightDir (frame.basisLabel slotC) atomU := by
        rw [hscale, div_mul_cancel₀ _ hneU]
      have hparV : frame.tightDir (frame.basisLabel slotA) atomV
          = scale * frame.tightDir (frame.basisLabel slotC) atomV := by
        rw [hscale, div_mul_eq_mul_div, eq_div_iff hneU]
        linear_combination hdet
      have hUother : atomU ∈ frame.activeSubset (frame.basisLabel slotA) := by
        refine blockCarrier_mem.mp ?_
        rw [hUcar]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hVother : atomV ∈ frame.activeSubset (frame.basisLabel slotA) := by
        refine blockCarrier_mem.mp ?_
        rw [hVcar]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      -- the third atom of the partner block
      have hsubOther : ({atomU, atomV} : Finset (Fin 6))
          ⊆ frame.activeSubset (frame.basisLabel slotA) := by
        intro atomIndex hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem'
        · exact hUother
        · rw [Finset.mem_singleton] at hmem'
          subst hmem'
          exact hVother
      have hcardSdiffOther : (frame.activeSubset (frame.basisLabel slotA)
          \ ({atomU, atomV} : Finset (Fin 6))).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubOther,
          frame.hdata.activeSubset_card _ (frame.hmemAll slotA), hcardPair]
      obtain ⟨atomS, hSset⟩ := Finset.card_eq_one.mp hcardSdiffOther
      have hSmem : atomS ∈ frame.activeSubset (frame.basisLabel slotA)
          ∧ atomS ∉ ({atomU, atomV} : Finset (Fin 6)) := by
        refine Finset.mem_sdiff.mp ?_
        rw [hSset]
        exact Finset.mem_singleton_self _
      have hSU : atomS ≠ atomU := by
        intro heq
        refine hSmem.2 ?_
        rw [heq]
        exact Finset.mem_insert_self _ _
      have hSV : atomS ≠ atomV := by
        intro heq
        refine hSmem.2 ?_
        rw [heq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hotherSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
          atomIndex ≠ atomS →
          frame.tightDir (frame.basisLabel slotA) atomIndex = 0 := by
        intro atomIndex h1 h2 h3
        refine frame.hdata.tightDir_support _ (frame.hmemAll slotA) atomIndex ?_
        intro hmem
        have hsdiff : atomIndex ∈ frame.activeSubset (frame.basisLabel slotA)
            \ ({atomU, atomV} : Finset (Fin 6)) := by
          refine Finset.mem_sdiff.mpr ⟨hmem, ?_⟩
          simp [h1, h2]
        rw [hSset, Finset.mem_singleton] at hsdiff
        exact h3 hsdiff
      by_cases hSalive : frame.tightDir (frame.basisLabel slotA) atomS = 0
      · -- the two columns are proportional, against the left inverse
        have hall : frame.tightDir (frame.basisLabel slotA)
            = scale • frame.tightDir (frame.basisLabel slotC) := by
          funext atomIndex
          rw [Pi.smul_apply, smul_eq_mul]
          by_cases h1 : atomIndex = atomU
          · rw [h1, hparU]
          by_cases h2 : atomIndex = atomV
          · rw [h2, hparV]
          by_cases h3 : atomIndex = atomS
          · rw [h3, hSalive, hsupp atomS hSU hSV, mul_zero]
          · rw [hotherSupp atomIndex h1 h2 h3, hsupp atomIndex h1 h2, mul_zero]
        have hLA := leftInverse_mulVec_tightDir_basisLabel frame.basisLabel
          frame.leftInv frame.hleft slotA
        have hLC := leftInverse_mulVec_tightDir_basisLabel frame.basisLabel
          frame.leftInv frame.hleft slotC
        rw [hall, Matrix.mulVec_smul, hLC] at hLA
        have hentry := congrFun hLA slotA
        rw [Pi.smul_apply, Pi.single_eq_of_ne hAC, Pi.single_eq_same] at hentry
        simp at hentry
      · exact false_of_parallel_pair_column_combination frame.hdata
          frame.hvalueNeg (frame.hmemAll slotC) (frame.hmemAll slotA) hUV hSU
          hSV hUblock hVblock hsupp hUother hVother hSmem.1 hotherSupp hparU
          hparV hSalive (crux.gap_diagonal_pos_of_allHeavy atomS)
    · exact frame.false_of_independent_dense_pair hdense hAC.symm hUcar hVcar
        (by
          intro hzero
          exact hdet (by linear_combination hzero))
  · -- the two support atoms sit on different carrier pairs
    have hTalive : frame.tightDir (frame.basisLabel slotK) atomT ≠ 0 := by
      rcases frame.dense_alive hTcar with hC | hK
      · exact absurd hTzero hC
      · exact hK
    by_cases hKA : slotK = slotA
    · subst hKA
      refine frame.false_of_independent_dense_pair hdense hKC.symm hTcar hUcar ?_
      rw [hTzero, zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero hneU hTalive
    by_cases hKB : slotK = slotB
    · subst hKB
      refine frame.false_of_independent_dense_pair hdense hKC.symm hTcar hVcar ?_
      rw [hTzero, zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero hneV hTalive
    · -- the tetrahedron profile
      have hCA : slotC ≠ slotA := hAC.symm
      have hCB : slotC ≠ slotB := hBC.symm
      have hCK : slotC ≠ slotK := hKC.symm
      have hAK : slotA ≠ slotK := fun heq => hKA heq.symm
      have hBK : slotB ≠ slotK := fun heq => hKB heq.symm
      have hinc := blockCarrier_incidence frame.hdata frame.hmemAll
      obtain ⟨atomW1, hW1car⟩ := exists_complement_pair_of_degree hdense hinc
        hCA hCB hCK (fun heq => hAB heq) hAK hBK hUcar
      obtain ⟨atomW2, hW2car⟩ := exists_complement_pair_of_degree hdense hinc
        hCB hCA hCK (fun heq => hAB heq.symm) hBK hAK hVcar
      obtain ⟨atomW3, hW3car⟩ := exists_complement_pair_of_degree hdense hinc
        hCK hCA hCB hAK.symm hBK.symm (fun heq => hAB heq) hTcar
      -- the six atoms are distinct
      have hmemA : slotA ∈ blockCarrier frame.activeSubset frame.basisLabel
          atomU := by
        rw [hUcar]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hmemB : slotB ∈ blockCarrier frame.activeSubset frame.basisLabel
          atomV := by
        rw [hVcar]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hmemK : slotK ∈ blockCarrier frame.activeSubset frame.basisLabel
          atomT := by
        rw [hTcar]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hmemC : ∀ atomIndex : Fin 6,
          blockCarrier frame.activeSubset frame.basisLabel atomIndex
            = {slotC, slotA} ∨ blockCarrier frame.activeSubset
              frame.basisLabel atomIndex = {slotC, slotB}
            ∨ blockCarrier frame.activeSubset frame.basisLabel atomIndex
              = {slotC, slotK} →
          slotC ∈ blockCarrier frame.activeSubset frame.basisLabel
            atomIndex := by
        intro atomIndex hcase
        rcases hcase with h | h | h <;> rw [h] <;>
          exact Finset.mem_insert_self _ _
      have hABne : slotA ≠ slotB := hAB
      have hBA : slotB ≠ slotA := fun heq => hAB heq.symm
      have hnotCA : slotC ∉ blockCarrier frame.activeSubset frame.basisLabel
          atomW3 := by
        rw [hW3car]
        simp [hCA, hCB]
      have hnotCK : slotC ∉ blockCarrier frame.activeSubset frame.basisLabel
          atomW2 := by
        rw [hW2car]
        simp [hCA, hCK]
      have hnotCB : slotC ∉ blockCarrier frame.activeSubset frame.basisLabel
          atomW1 := by
        rw [hW1car]
        simp [hCB, hCK]
      have hUV' : atomU ≠ atomV :=
        atom_ne_of_carrier_mem_notMem hmemA (by rw [hVcar]; simp [hAC, hABne])
      have hUT : atomU ≠ atomT :=
        atom_ne_of_carrier_mem_notMem hmemA (by rw [hTcar]; simp [hAC, hAK])
      have hUW3 : atomU ≠ atomW3 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomU (Or.inl hUcar)) hnotCA
      have hUW2 : atomU ≠ atomW2 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomU (Or.inl hUcar)) hnotCK
      have hUW1 : atomU ≠ atomW1 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomU (Or.inl hUcar)) hnotCB
      have hVT : atomV ≠ atomT :=
        atom_ne_of_carrier_mem_notMem hmemB (by rw [hTcar]; simp [hBC, hBK])
      have hVW3 : atomV ≠ atomW3 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomV (Or.inr (Or.inl hVcar)))
          hnotCA
      have hVW2 : atomV ≠ atomW2 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomV (Or.inr (Or.inl hVcar)))
          hnotCK
      have hVW1 : atomV ≠ atomW1 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomV (Or.inr (Or.inl hVcar)))
          hnotCB
      have hTW3 : atomT ≠ atomW3 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomT (Or.inr (Or.inr hTcar)))
          hnotCA
      have hTW2 : atomT ≠ atomW2 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomT (Or.inr (Or.inr hTcar)))
          hnotCK
      have hTW1 : atomT ≠ atomW1 :=
        atom_ne_of_carrier_mem_notMem (hmemC atomT (Or.inr (Or.inr hTcar)))
          hnotCB
      have hmemBW3 : slotB ∈ blockCarrier frame.activeSubset frame.basisLabel
          atomW3 := by
        rw [hW3car]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hmemAW3 : slotA ∈ blockCarrier frame.activeSubset frame.basisLabel
          atomW3 := by
        rw [hW3car]
        exact Finset.mem_insert_self _ _
      have hmemAW2 : slotA ∈ blockCarrier frame.activeSubset frame.basisLabel
          atomW2 := by
        rw [hW2car]
        exact Finset.mem_insert_self _ _
      have hnotBW2 : slotB ∉ blockCarrier frame.activeSubset frame.basisLabel
          atomW2 := by
        rw [hW2car]
        simp [hBA, hBK]
      have hnotAW1 : slotA ∉ blockCarrier frame.activeSubset frame.basisLabel
          atomW1 := by
        rw [hW1car]
        simp [hABne, hAK]
      have hW3W2 : atomW3 ≠ atomW2 :=
        atom_ne_of_carrier_mem_notMem hmemBW3 hnotBW2
      have hW3W1 : atomW3 ≠ atomW1 :=
        atom_ne_of_carrier_mem_notMem hmemAW3 hnotAW1
      have hW2W1 : atomW2 ≠ atomW1 :=
        atom_ne_of_carrier_mem_notMem hmemAW2 hnotAW1
      have hwsum : (chartPointOfDesign crux.design).weight atomU
          + (chartPointOfDesign crux.design).weight atomV
          + (chartPointOfDesign crux.design).weight atomT
          + (chartPointOfDesign crux.design).weight atomW3
          + (chartPointOfDesign crux.design).weight atomW2
          + (chartPointOfDesign crux.design).weight atomW1 = 1 := by
        rw [← sum_six_atoms (chartPointOfDesign crux.design).weight hUV' hUT
          hUW3 hUW2 hUW1 hVT hVW3 hVW2 hVW1 hTW3 hTW2 hTW1 hW3W2 hW3W1 hW2W1]
        exact frame.hdata.weight_sum_one
      exact false_of_quadruple_kfour_products frame.hidempotent frame.htrace
        hCA hCB hCK (fun heq => hAB heq) hAK hBK frame.hvalueNeg
        (frame.hdata.weight_pos atomU) (frame.hdata.weight_pos atomV)
        (frame.hdata.weight_pos atomT) (frame.hdata.weight_pos atomW3)
        (frame.hdata.weight_pos atomW2) (frame.hdata.weight_pos atomW1)
        hwsum (frame.dense_corner_product hCA hUcar)
        (frame.dense_corner_product hCB hVcar)
        (frame.dense_corner_product hCK hTcar)
        (frame.dense_corner_product (fun heq => hAB heq) hW3car)
        (frame.dense_corner_product hAK hW2car)
        (frame.dense_corner_product hBK hW1car)

/-! ## Layer 6 — the circuit residue narrowing -/

/-- The block of a label with two named block atoms names its third
atom, and the label vanishes off the three. -/
theorem RankFourFrame.exists_block_third_atom {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {label : frame.activeIndex}
    (hmem : label ∈ frame.activeSet) {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hUblock : atomU ∈ frame.activeSubset label)
    (hVblock : atomV ∈ frame.activeSubset label) :
    ∃ atomS : Fin 6, atomS ≠ atomU ∧ atomS ≠ atomV
      ∧ atomS ∈ frame.activeSubset label
      ∧ ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        atomIndex ≠ atomS → frame.tightDir label atomIndex = 0 := by
  classical
  have hsub : ({atomU, atomV} : Finset (Fin 6)) ⊆ frame.activeSubset label := by
    intro atomIndex hmemPair
    rcases Finset.mem_insert.mp hmemPair with rfl | hmemPair'
    · exact hUblock
    · rw [Finset.mem_singleton] at hmemPair'
      subst hmemPair'
      exact hVblock
  have hcardPair : ({atomU, atomV} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hUV]), Finset.card_singleton]
  have hcardSdiff : (frame.activeSubset label
      \ ({atomU, atomV} : Finset (Fin 6))).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      frame.hdata.activeSubset_card label hmem, hcardPair]
  obtain ⟨atomS, hSset⟩ := Finset.card_eq_one.mp hcardSdiff
  have hSmem : atomS ∈ frame.activeSubset label
      ∧ atomS ∉ ({atomU, atomV} : Finset (Fin 6)) := by
    refine Finset.mem_sdiff.mp ?_
    rw [hSset]
    exact Finset.mem_singleton_self _
  refine ⟨atomS, ?_, ?_, hSmem.1, ?_⟩
  · intro heq
    refine hSmem.2 ?_
    rw [heq]
    exact Finset.mem_insert_self _ _
  · intro heq
    refine hSmem.2 ?_
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro atomIndex h1 h2 h3
    refine frame.hdata.tightDir_support label hmem atomIndex ?_
    intro hmemBlock
    have hsdiff : atomIndex ∈ frame.activeSubset label
        \ ({atomU, atomV} : Finset (Fin 6)) := by
      refine Finset.mem_sdiff.mpr ⟨hmemBlock, ?_⟩
      simp [h1, h2]
    rw [hSset, Finset.mem_singleton] at hsdiff
    exact h3 hsdiff

/-- **THE ALIGNED LABEL KILL.**  A label whose block carries the pair of
a support-two column, whose pair restriction is proportional to that
column, and whose direction is not that multiple, dies.  The difference
is a single-atom vector. -/
theorem RankFourFrame.false_of_pair_aligned_label {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {slotC : Fin 4} {atomU atomV : Fin 6}
    (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel slotC) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel slotC) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel slotC) atomIndex = 0)
    {label : frame.activeIndex} (hmem : label ∈ frame.activeSet)
    (hUblock : atomU ∈ frame.activeSubset label)
    (hVblock : atomV ∈ frame.activeSubset label) {scale : ℝ}
    (hparU : frame.tightDir label atomU
      = scale * frame.tightDir (frame.basisLabel slotC) atomU)
    (hparV : frame.tightDir label atomV
      = scale * frame.tightDir (frame.basisLabel slotC) atomV)
    (hnotParallel : frame.tightDir label
      ≠ scale • frame.tightDir (frame.basisLabel slotC)) :
    False := by
  classical
  obtain ⟨atomS, hSU, hSV, hSblock, hSsupp⟩ :=
    frame.exists_block_third_atom hmem hUV hUblock hVblock
  have hUblockC : atomU ∈ frame.activeSubset (frame.basisLabel slotC) := by
    by_contra hout
    exact hneU (frame.hdata.tightDir_support _ (frame.hmemAll slotC) atomU hout)
  have hVblockC : atomV ∈ frame.activeSubset (frame.basisLabel slotC) := by
    by_contra hout
    exact hneV (frame.hdata.tightDir_support _ (frame.hmemAll slotC) atomV hout)
  by_cases hSalive : frame.tightDir label atomS = 0
  · refine absurd ?_ hnotParallel
    funext atomIndex
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases h1 : atomIndex = atomU
    · rw [h1, hparU]
    by_cases h2 : atomIndex = atomV
    · rw [h2, hparV]
    by_cases h3 : atomIndex = atomS
    · rw [h3, hSalive, hsupp atomS hSU hSV, mul_zero]
    · rw [hSsupp atomIndex h1 h2 h3, hsupp atomIndex h1 h2, mul_zero]
  · exact false_of_parallel_pair_column_combination frame.hdata frame.hvalueNeg
      (frame.hmemAll slotC) hmem hUV hSU hSV hUblockC hVblockC hsupp hUblock
      hVblock hSblock hSsupp hparU hparV hSalive
      (crux.gap_diagonal_pos_of_allHeavy atomS)

/-- **THE CIRCUIT NARROWING.**  A label parallel to no basis column
whose block carries the pair of a support-two column is independent of
that column on the pair. -/
theorem RankFourFrame.circuit_cross_ne_zero {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {slotC : Fin 4} {atomU atomV : Fin 6}
    (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel slotC) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel slotC) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel slotC) atomIndex = 0)
    {label : frame.activeIndex} (hmem : label ∈ frame.activeSet)
    (hUblock : atomU ∈ frame.activeSubset label)
    (hVblock : atomV ∈ frame.activeSubset label)
    (hcircuit : ∀ (slot : Fin 4) (scale : ℝ),
      frame.tightDir label ≠ scale • frame.tightDir (frame.basisLabel slot)) :
    frame.tightDir label atomU * frame.tightDir (frame.basisLabel slotC) atomV
      - frame.tightDir label atomV
        * frame.tightDir (frame.basisLabel slotC) atomU ≠ 0 := by
  intro hzero
  refine frame.false_of_pair_aligned_label hUV hneU hneV hsupp hmem hUblock
    hVblock (scale := frame.tightDir label atomU
      / frame.tightDir (frame.basisLabel slotC) atomU) ?_ ?_
    (hcircuit slotC _)
  · rw [div_mul_cancel₀ _ hneU]
  · rw [div_mul_eq_mul_div, eq_div_iff hneU]
    linear_combination -hzero

/-- **THE PIN READ.**  A block-pinned atom prices the diagonal
coefficient entry at its shifted weight. -/
theorem RankFourFrame.pin_coeff_diagonal {crux : SixThreeCrux}
    (frame : RankFourFrame crux) {atomIndex : Fin 6} {slot : Fin 4}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel atomIndex
      = {slot}) :
    frame.coeff slot slot = chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex := by
  classical
  have hmemBlock : atomIndex ∈ frame.activeSubset (frame.basisLabel slot) := by
    rw [← blockCarrier_mem (activeSubset := frame.activeSubset)
      (basisLabel := frame.basisLabel), hpin]
    exact Finset.mem_singleton_self _
  have hrow := carried_row_reading frame.hdata frame.basisLabel
    frame.hrepresentation (frame.hmemAll slot) hmemBlock
  have halive : frame.tightDir (frame.basisLabel slot) atomIndex ≠ 0 := by
    obtain ⟨other, hother⟩ := exists_basisIndex_datumTightSupport frame.hdata
      frame.basisLabel frame.hspan frame.leftInv frame.hleft atomIndex
    have hne := mem_datumTightSupport.mp hother
    have hmemCar : other ∈ blockCarrier frame.activeSubset frame.basisLabel
        atomIndex := by
      by_contra hout
      exact hne (frame.tightDir_eq_zero_of_notMem_carrier hout)
    rw [hpin, Finset.mem_singleton] at hmemCar
    rw [← hmemCar]
    exact hne
  have hsuppRow : ∀ slotOther : Fin 4, slotOther ≠ slot →
      frame.tightDir (frame.basisLabel slotOther) atomIndex = 0 := by
    intro slotOther hother
    refine frame.tightDir_eq_zero_of_notMem_carrier ?_
    rw [hpin]
    simp [hother]
  have hcollapse : ∑ columnIndex : Fin 4,
      frame.tightDir (frame.basisLabel columnIndex) atomIndex
        * frame.coeff columnIndex slot
      = frame.tightDir (frame.basisLabel slot) atomIndex
        * frame.coeff slot slot := by
    rw [Finset.sum_eq_single slot]
    · intro columnIndex _ hne
      rw [hsuppRow columnIndex hne, zero_mul]
    · intro hnotMem
      exact absurd (Finset.mem_univ slot) hnotMem
  rw [hcollapse] at hrow
  have hcancel : frame.tightDir (frame.basisLabel slot) atomIndex
      * (frame.coeff slot slot
        - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) = 0 := by
    linear_combination hrow
  have hfac := (mul_eq_zero.mp hcancel).resolve_left halive
  linarith

/-! ## Layer 7 — the outer readings -/

/-- The dense branch of a rank-four outer datum is empty. -/
theorem RankFourOuterData.false_of_dense {crux : SixThreeCrux}
    (data : RankFourOuterData crux)
    (hdense : ∀ atomIndex : Fin 6,
      (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card = 2) : False :=
  data.frame.false_of_dense_pair_column data.hUV data.hneU data.hneV data.hsupp
    hdense

/-- **THE PIN LAW.**  Every rank-four outer datum carries a
block-pinned atom: the dense profile is dead. -/
theorem RankFourOuterData.exists_block_pin {crux : SixThreeCrux}
    (data : RankFourOuterData crux) :
    ∃ (pinAtom : Fin 6) (pinSlot : Fin 4),
      blockCarrier data.frame.activeSubset data.frame.basisLabel pinAtom
        = {pinSlot} := by
  rcases data.frame.blockPin_or_all_two with hpin | hdense
  · exact hpin
  · exact absurd (data.false_of_dense hdense) not_false

/-- **THE RANK-FOUR OUTER KILL.**  With the circuit residue closed and
interior shifted weights at the three-plus-carrier atoms, no rank-four
outer datum exists.  The circuit closure folds the Gram, the pin branch
dies at the refined budget, and the dense branch dies here. -/
theorem rankFourOuterKilled_of_circuit_interior
    (hcirc : RankFourOuterCircuitClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourOuterKilled := fun crux data =>
  data.false_of_dense
    (data.dense_of_circuitClosed_interior hcirc (hinterior crux data))

/-- **THE RANK-FOUR CLOSURE-ONE REDUCTION.**  The circuit residue and
the interior residue close the rank-four support-two closure. -/
theorem rankFourSupportTwoClosed_of_circuit_interior
    (hcirc : RankFourOuterCircuitClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_outer_killed
    (rankFourOuterKilled_of_circuit_interior hcirc hinterior)

end Gtz

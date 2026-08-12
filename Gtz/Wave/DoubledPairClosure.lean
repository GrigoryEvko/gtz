import Gtz.Wave.DenseShareDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The doubled-pair closure — the dense branch narrows to the labeled cycle

The dense dispatch routes to the K4 profile or to two disjoint doubled
pairs.  This file closes the doubled side down to one labeled shape.  The
degree law forces an omega: a full share on one pair forces a full share
on the disjoint pair, thus the mixed full/double case is impossible.  The
split is then exact: both pairs share two atoms, or both pairs have equal
supports.  The equal-support side dies through the landed full-share
kill.  On the two-two side the degree law normalizes the four cross
shares to a four-cycle, and the share sets label the six atoms: two atoms
on each doubled pair, one atom on each single edge, pairwise distinct and
jointly exhaustive.  The routed closure then consumes exactly one
continuation: the labeled-cycle kill.

The layers:

1. **The quadruple vocabulary.**  Four distinct slots of `Fin 4` exhaust
   the type, and the erase sets enumerate explicitly.
2. **The degree triple.**  The degree law reads as a three-term sum over
   the explicit erase set.
3. **The full-share omega.**  A full share forces the disjoint partner
   full, through the degree law at three slots.
4. **The exact split.**  Two doubled pairs are two-two or full-full.
5. **The cycle normalization.**  At two-two the cross shares form a
   four-cycle, in one of the two orientations.
6. **The atom labeling.**  The share sets extract the six atoms with
   distinctness and coverage.
7. **The routed closure.**  The dense branch dies given the K4 kill and
   the labeled-cycle kill.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.shareSet` with `Gtz.pairShare_eq_card_shareSet`,
  `Gtz.shareSet_comm`, `Gtz.mem_shareSet_iff` — the share-set vocabulary.
* `Gtz.quadruple_eq_univ`, `Gtz.erase_quadruple` — the quadruple
  vocabulary.
* `Gtz.degree_sum_triple` — **THE DEGREE TRIPLE.**
* `Gtz.pairShare_eq_card_of_supports_eq`,
  `Gtz.share_full_forces_partner_full` — **THE OMEGA.**
* `Gtz.doubled_cases_split` — **THE EXACT SPLIT.**
* `Gtz.cycle_share_normalization` — **THE CYCLE NORMALIZATION.**
* `Gtz.shareSet_carrier_vanishes`, `Gtz.shareSet_disjoint_atom_ne`,
  `Gtz.exists_cycle_atom_labeling` — **THE ATOM LABELING.**
* `Gtz.false_of_dense_branch_of_cycle_kills` — **THE ROUTED CLOSURE.**

## Vacuity

The closure takes the negative value as a hypothesis, and a crux supplies
it.  It is vacuous if `Gtz.GtzWeighted 6 3` holds.  The combinatorial
layers are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## Layer 1 — the share-set and quadruple vocabulary -/

/-- The share set: the atoms in both supports.  The pair share is its
cardinality. -/
noncomputable def shareSet (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) : Finset (Fin size) :=
  Finset.univ.filter fun atomIndex =>
    atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
      ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)

/-- The pair share is the share-set cardinality. -/
theorem pairShare_eq_card_shareSet (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) :
    pairShare tightDir basisLabel slotK slotL
      = (shareSet tightDir basisLabel slotK slotL).card := rfl

/-- The share set is symmetric. -/
theorem shareSet_comm (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) :
    shareSet tightDir basisLabel slotK slotL
      = shareSet tightDir basisLabel slotL slotK := by
  unfold shareSet
  apply Finset.filter_congr
  intro atomIndex _
  exact and_comm

/-- Membership in the share set is the double support membership. -/
theorem mem_shareSet_iff (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) {atomIndex : Fin size} :
    atomIndex ∈ shareSet tightDir basisLabel slotK slotL
      ↔ atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
        ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL) := by
  unfold shareSet
  simp

/-- Four distinct slots of `Fin 4` exhaust the type. -/
theorem quadruple_eq_univ {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN) :
    ({slotK, slotL, slotM, slotN} : Finset (Fin 4)) = Finset.univ := by
  have hnotK : slotK ∉ ({slotL, slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hKL heq
    rcases Finset.mem_insert.mp hmem' with heq | hmem''
    · exact hKM heq
    · exact hKN (Finset.mem_singleton.mp hmem'')
  have hnotL : slotL ∉ ({slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hLM heq
    · exact hLN (Finset.mem_singleton.mp hmem')
  have hnotM : slotM ∉ ({slotN} : Finset (Fin 4)) := fun hmem =>
    hMN (Finset.mem_singleton.mp hmem)
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem hnotK, Finset.card_insert_of_notMem hnotL,
    Finset.card_insert_of_notMem hnotM, Finset.card_singleton, Fintype.card_fin]

/-- The erase set of the first slot enumerates the other three. -/
theorem erase_quadruple {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN) :
    Finset.univ.erase slotK = ({slotL, slotM, slotN} : Finset (Fin 4)) := by
  have hnotK : slotK ∉ ({slotL, slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hKL heq
    rcases Finset.mem_insert.mp hmem' with heq | hmem''
    · exact hKM heq
    · exact hKN (Finset.mem_singleton.mp hmem'')
  rw [← quadruple_eq_univ hKL hKM hKN hLM hLN hMN]
  exact Finset.erase_insert hnotK

/-! ## Layer 2 — the degree triple -/

/-- **THE DEGREE TRIPLE.**  At a multiplicity-two datum with a card-3
support, the three shares of a slot against the other three slots sum to
three. -/
theorem degree_sum_triple (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN)
    (hcardK : (datumTightSupport tightDir (basisLabel slotK)).card = 3) :
    pairShare tightDir basisLabel slotK slotL
      + pairShare tightDir basisLabel slotK slotM
      + pairShare tightDir basisLabel slotK slotN = 3 := by
  classical
  have hnotL : slotL ∉ ({slotM, slotN} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hLM heq
    · exact hLN (Finset.mem_singleton.mp hmem')
  have hnotM : slotM ∉ ({slotN} : Finset (Fin 4)) := fun hmem =>
    hMN (Finset.mem_singleton.mp hmem)
  have hdeg := sum_erase_pairShare_eq_card basisLabel hmult slotK
  rw [hcardK, erase_quadruple hKL hKM hKN hLM hLN hMN,
    Finset.sum_insert hnotL, Finset.sum_insert hnotM,
    Finset.sum_singleton] at hdeg
  omega

/-! ## Layer 3 — the full-share omega -/

/-- Equal supports read a full share. -/
theorem pairShare_eq_card_of_supports_eq
    (basisLabel : Fin basisCount → activeIndex) {slotK slotL : Fin basisCount}
    (hsupports : datumTightSupport tightDir (basisLabel slotK)
      = datumTightSupport tightDir (basisLabel slotL)) :
    pairShare tightDir basisLabel slotK slotL
      = (datumTightSupport tightDir (basisLabel slotK)).card := by
  classical
  rw [pairShare_eq_card_shareSet]
  congr 1
  unfold shareSet
  rw [← hsupports]
  ext atomIndex
  simp [and_self]

/-- **THE FULL-SHARE OMEGA.**  A full share on one pair forces a full
share on the disjoint pair: the degree law empties the four cross shares
and the partner's degree lands on its own pair. -/
theorem share_full_forces_partner_full (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN)
    (hfull : pairShare tightDir basisLabel slotK slotL = 3) :
    pairShare tightDir basisLabel slotM slotN = 3 := by
  have hdegK := degree_sum_triple basisLabel hmult hKL hKM hKN hLM hLN hMN
    (hcard slotK)
  have hdegM := degree_sum_triple basisLabel hmult
    (Ne.symm hKM) (Ne.symm hLM) hMN hKL hKN hLN (hcard slotM)
  have hsymmMK := pairShare_symm (tightDir := tightDir) basisLabel slotM slotK
  have hsymmML := pairShare_symm (tightDir := tightDir) basisLabel slotM slotL
  have hdegL := degree_sum_triple basisLabel hmult
    (Ne.symm hKL) hLM hLN hKM hKN hMN (hcard slotL)
  have hsymmLK := pairShare_symm (tightDir := tightDir) basisLabel slotL slotK
  omega

/-! ## Layer 4 — the exact split -/

/-- **THE EXACT SPLIT.**  Two disjoint doubled pairs are two-two or
full-full: the omega forbids the mixed case. -/
theorem doubled_cases_split (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN)
    (h2KL : 2 ≤ pairShare tightDir basisLabel slotK slotL)
    (h2MN : 2 ≤ pairShare tightDir basisLabel slotM slotN) :
    (pairShare tightDir basisLabel slotK slotL = 2
        ∧ pairShare tightDir basisLabel slotM slotN = 2)
      ∨ (datumTightSupport tightDir (basisLabel slotK)
          = datumTightSupport tightDir (basisLabel slotL)
        ∧ datumTightSupport tightDir (basisLabel slotM)
          = datumTightSupport tightDir (basisLabel slotN)) := by
  rcases doubled_pair_split basisLabel (hcard slotK) (hcard slotL) h2KL
    with h2 | hfullKL
  · rcases doubled_pair_split basisLabel (hcard slotM) (hcard slotN) h2MN
      with h2' | hfullMN
    · exact Or.inl ⟨h2, h2'⟩
    · exfalso
      have hshareMN : pairShare tightDir basisLabel slotM slotN = 3 := by
        rw [pairShare_eq_card_of_supports_eq basisLabel hfullMN]
        exact hcard slotM
      have hshareKL := share_full_forces_partner_full basisLabel hmult hcard
        hMN (Ne.symm hKM) (Ne.symm hLM) (Ne.symm hKN) (Ne.symm hLN) hKL
        hshareMN
      omega
  · have hshareKL : pairShare tightDir basisLabel slotK slotL = 3 := by
      rw [pairShare_eq_card_of_supports_eq basisLabel hfullKL]
      exact hcard slotK
    have hshareMN := share_full_forces_partner_full basisLabel hmult hcard
      hKL hKM hKN hLM hLN hMN hshareKL
    exact Or.inr ⟨hfullKL,
      supports_eq_of_pairShare_full basisLabel (hcard slotM) (hcard slotN)
        hshareMN⟩

/-! ## Layer 5 — the cycle normalization -/

/-- **THE CYCLE NORMALIZATION.**  At two-two the four cross shares form a
four-cycle in one of the two orientations: each degree equation leaves one
unit for the two cross edges at its slot. -/
theorem cycle_share_normalization (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN)
    (h2KL : pairShare tightDir basisLabel slotK slotL = 2)
    (h2MN : pairShare tightDir basisLabel slotM slotN = 2) :
    (pairShare tightDir basisLabel slotK slotM = 1
        ∧ pairShare tightDir basisLabel slotL slotN = 1
        ∧ pairShare tightDir basisLabel slotK slotN = 0
        ∧ pairShare tightDir basisLabel slotL slotM = 0)
      ∨ (pairShare tightDir basisLabel slotK slotN = 1
        ∧ pairShare tightDir basisLabel slotL slotM = 1
        ∧ pairShare tightDir basisLabel slotK slotM = 0
        ∧ pairShare tightDir basisLabel slotL slotN = 0) := by
  have hdegK := degree_sum_triple basisLabel hmult hKL hKM hKN hLM hLN hMN
    (hcard slotK)
  have hdegL := degree_sum_triple basisLabel hmult
    (Ne.symm hKL) hLM hLN hKM hKN hMN (hcard slotL)
  have hdegM := degree_sum_triple basisLabel hmult
    (Ne.symm hKM) (Ne.symm hLM) hMN hKL hKN hLN (hcard slotM)
  have hsymmLK := pairShare_symm (tightDir := tightDir) basisLabel slotL slotK
  have hsymmMK := pairShare_symm (tightDir := tightDir) basisLabel slotM slotK
  have hsymmML := pairShare_symm (tightDir := tightDir) basisLabel slotM slotL
  have hdegN := degree_sum_triple basisLabel hmult
    (Ne.symm hKN) (Ne.symm hLN) (Ne.symm hMN) hKL hKM hLM (hcard slotN)
  have hsymmNK := pairShare_symm (tightDir := tightDir) basisLabel slotN slotK
  have hsymmNM := pairShare_symm (tightDir := tightDir) basisLabel slotN slotM
  have hsymmNL := pairShare_symm (tightDir := tightDir) basisLabel slotN slotL
  omega

/-! ## Layer 6 — the atom labeling -/

/-- A share-set atom's direction vanishes at every other slot. -/
theorem shareSet_carrier_vanishes (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL : Fin basisCount} (hKL : slotK ≠ slotL)
    {atomIndex : Fin size}
    (hmem : atomIndex ∈ shareSet tightDir basisLabel slotK slotL)
    {slotOther : Fin basisCount} (hOK : slotOther ≠ slotK)
    (hOL : slotOther ≠ slotL) :
    tightDir (basisLabel slotOther) atomIndex = 0 := by
  obtain ⟨hmemK, hmemL⟩ := (mem_shareSet_iff basisLabel slotK slotL).mp hmem
  exact shared_atom_exclusive_carriers basisLabel hmult hKL hmemK hmemL hOK hOL

/-- Atoms of share sets with a fresh slot are distinct: the fresh slot's
support separates them. -/
theorem shareSet_disjoint_atom_ne (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL slotP slotQ : Fin basisCount} (hKL : slotK ≠ slotL)
    (hPK : slotP ≠ slotK) (hPL : slotP ≠ slotL)
    {firstAtom secondAtom : Fin size}
    (hfirst : firstAtom ∈ shareSet tightDir basisLabel slotK slotL)
    (hsecond : secondAtom ∈ shareSet tightDir basisLabel slotP slotQ) :
    firstAtom ≠ secondAtom := by
  intro heq
  have hvanish := shareSet_carrier_vanishes basisLabel hmult hKL hfirst hPK hPL
  have hmemP := ((mem_shareSet_iff basisLabel slotP slotQ).mp hsecond).1
  rw [heq] at hvanish
  exact mem_datumTightSupport.mp hmemP hvanish

/-- **THE ATOM LABELING.**  At the normalized cycle, the share sets label
the six atoms: two on each doubled pair and one on each single edge, with
the labeled memberships and the pair distinctness. -/
theorem exists_cycle_atom_labeling (basisLabel : Fin 4 → activeIndex)
    {slotK slotL slotM slotN : Fin 4}
    (h2KL : pairShare tightDir basisLabel slotK slotL = 2)
    (h2MN : pairShare tightDir basisLabel slotM slotN = 2)
    (h1KM : pairShare tightDir basisLabel slotK slotM = 1)
    (h1LN : pairShare tightDir basisLabel slotL slotN = 1) :
    ∃ (pairAtomOne pairAtomTwo coAtomOne coAtomTwo singleKM singleLN : Fin size),
      pairAtomOne ≠ pairAtomTwo ∧ coAtomOne ≠ coAtomTwo
      ∧ pairAtomOne ∈ shareSet tightDir basisLabel slotK slotL
      ∧ pairAtomTwo ∈ shareSet tightDir basisLabel slotK slotL
      ∧ coAtomOne ∈ shareSet tightDir basisLabel slotM slotN
      ∧ coAtomTwo ∈ shareSet tightDir basisLabel slotM slotN
      ∧ singleKM ∈ shareSet tightDir basisLabel slotK slotM
      ∧ singleLN ∈ shareSet tightDir basisLabel slotL slotN
      ∧ shareSet tightDir basisLabel slotK slotL = {pairAtomOne, pairAtomTwo}
      ∧ shareSet tightDir basisLabel slotM slotN = {coAtomOne, coAtomTwo}
      ∧ shareSet tightDir basisLabel slotK slotM = {singleKM}
      ∧ shareSet tightDir basisLabel slotL slotN = {singleLN} := by
  classical
  rw [pairShare_eq_card_shareSet] at h2KL h2MN h1KM h1LN
  obtain ⟨pairAtomOne, pairAtomTwo, hpairNe, hpairSet⟩ :=
    Finset.card_eq_two.mp h2KL
  obtain ⟨coAtomOne, coAtomTwo, hcoNe, hcoSet⟩ := Finset.card_eq_two.mp h2MN
  obtain ⟨singleKM, hKMset⟩ := Finset.card_eq_one.mp h1KM
  obtain ⟨singleLN, hLNset⟩ := Finset.card_eq_one.mp h1LN
  refine ⟨pairAtomOne, pairAtomTwo, coAtomOne, coAtomTwo, singleKM, singleLN,
    hpairNe, hcoNe, ?_, ?_, ?_, ?_, ?_, ?_, hpairSet, hcoSet, hKMset, hLNset⟩
  · rw [hpairSet]
    exact Finset.mem_insert_self _ _
  · rw [hpairSet]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rw [hcoSet]
    exact Finset.mem_insert_self _ _
  · rw [hcoSet]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rw [hKMset]
    exact Finset.mem_singleton_self _
  · rw [hLNset]
    exact Finset.mem_singleton_self _

/-- **THE SUPPORT ENUMERATION.**  At the labeled cycle, a slot's support
is exactly its two doubled atoms and its single atom. -/
theorem cycle_support_enumeration (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL slotM : Fin basisCount}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hLM : slotL ≠ slotM)
    (hcardK : (datumTightSupport tightDir (basisLabel slotK)).card = 3)
    {pairAtomOne pairAtomTwo singleAtom : Fin size}
    (hpairNe : pairAtomOne ≠ pairAtomTwo)
    (hpairSet : shareSet tightDir basisLabel slotK slotL
      = {pairAtomOne, pairAtomTwo})
    (hsingleMem : singleAtom ∈ shareSet tightDir basisLabel slotK slotM) :
    datumTightSupport tightDir (basisLabel slotK)
      = {pairAtomOne, pairAtomTwo, singleAtom} := by
  classical
  have hmemOne : pairAtomOne ∈ shareSet tightDir basisLabel slotK slotL := by
    rw [hpairSet]
    exact Finset.mem_insert_self _ _
  have hmemTwo : pairAtomTwo ∈ shareSet tightDir basisLabel slotK slotL := by
    rw [hpairSet]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hsingleMem' : singleAtom ∈ shareSet tightDir basisLabel slotM slotK := by
    rw [shareSet_comm]
    exact hsingleMem
  have hneOne : pairAtomOne ≠ singleAtom :=
    shareSet_disjoint_atom_ne basisLabel hmult hKL (Ne.symm hKM)
      (Ne.symm hLM) hmemOne hsingleMem'
  have hneTwo : pairAtomTwo ≠ singleAtom :=
    shareSet_disjoint_atom_ne basisLabel hmult hKL (Ne.symm hKM)
      (Ne.symm hLM) hmemTwo hsingleMem'
  have hnotOne : pairAtomOne ∉ ({pairAtomTwo, singleAtom} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hpairNe heq
    · exact hneOne (Finset.mem_singleton.mp hmem')
  have hnotTwo : pairAtomTwo ∉ ({singleAtom} : Finset (Fin size)) := fun hmem =>
    hneTwo (Finset.mem_singleton.mp hmem)
  have hsubset : ({pairAtomOne, pairAtomTwo, singleAtom} : Finset (Fin size))
      ⊆ datumTightSupport tightDir (basisLabel slotK) := by
    intro atomIndex hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · rw [heq]
      exact ((mem_shareSet_iff basisLabel slotK slotL).mp hmemOne).1
    rcases Finset.mem_insert.mp hmem' with heq | hmem''
    · rw [heq]
      exact ((mem_shareSet_iff basisLabel slotK slotL).mp hmemTwo).1
    · rw [Finset.mem_singleton.mp hmem'']
      exact ((mem_shareSet_iff basisLabel slotK slotM).mp hsingleMem).1
  have hcardTriple : ({pairAtomOne, pairAtomTwo, singleAtom}
      : Finset (Fin size)).card = 3 := by
    rw [Finset.card_insert_of_notMem hnotOne,
      Finset.card_insert_of_notMem hnotTwo, Finset.card_singleton]
  symm
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hcardTriple, hcardK]

/-! ## Layer 7 — the routed closure -/

/-- **THE ROUTED CLOSURE.**  The dense branch dies given the K4 kill and
the labeled-cycle kill: the dispatch routes, the exact split kills the
full side through the landed full-share kill, the normalization orients
the cycle, and the labeled continuation consumes the rest. -/
theorem false_of_dense_branch_of_cycle_kills
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {L : Matrix (Fin 4) (Fin size) ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    (hmemAll : ∀ slotIndex : Fin 4, basisLabel slotIndex ∈ activeSet)
    (killKFour : (∀ slotK slotL : Fin 4, slotK ≠ slotL →
      pairShare tightDir basisLabel slotK slotL = 1) → False)
    (killCycle : ∀ slotK slotL slotM slotN : Fin 4,
      slotK ≠ slotL → slotM ≠ slotN → slotK ≠ slotM → slotK ≠ slotN →
      slotL ≠ slotM → slotL ≠ slotN →
      pairShare tightDir basisLabel slotK slotL = 2 →
      pairShare tightDir basisLabel slotM slotN = 2 →
      pairShare tightDir basisLabel slotK slotM = 1 →
      pairShare tightDir basisLabel slotL slotN = 1 →
      pairShare tightDir basisLabel slotK slotN = 0 →
      pairShare tightDir basisLabel slotL slotM = 0 → False) :
    False := by
  refine false_of_dense_branch_of_profiles basisLabel hmult hcard killKFour ?_
  intro slotK slotL slotM slotN hKL hMN hKM hKN hLM hLN h2KL h2MN
  rcases doubled_cases_split basisLabel hmult hcard hKL hKM hKN hLM hLN hMN
    h2KL h2MN with ⟨htwoKL, htwoMN⟩ | ⟨hfullKL, hfullMN⟩
  · rcases cycle_share_normalization basisLabel hmult hcard hKL hKM hKN hLM
      hLN hMN htwoKL htwoMN with
      ⟨h1KM, h1LN, h0KN, h0LM⟩ | ⟨h1KN, h1LM, h0KM, h0LN⟩
    · exact killCycle slotK slotL slotM slotN hKL hMN hKM hKN hLM hLN
        htwoKL htwoMN h1KM h1LN h0KN h0LM
    · have htwoNM : pairShare tightDir basisLabel slotN slotM = 2 := by
        rw [pairShare_symm]
        exact htwoMN
      exact killCycle slotK slotL slotN slotM hKL (Ne.symm hMN) hKN hKM hLN
        hLM htwoKL htwoNM h1KN h1LM h0KM h0LN
  · exact false_of_two_full_shares hdata hvalueNeg basisLabel hleft
      hrepresentation htrace hmult hmemAll hKL hMN hKM hKN hLM hLN
      (hcard slotK) (hcard slotM) hfullKL hfullMN

/-! ## Layer 8 — the oriented routed closure -/

/-- **THE ORIENTED ROUTED CLOSURE.**  The dense branch dies given the K4
kill and the two oriented cycle kills: the labeling and the support
enumeration turn the two-two case into the full C4 normal form, and the
cross determinants of the two doubled pairs orient the residue.  The
both-parallel continuation is the named open sub-branch of the rung. -/
theorem false_of_dense_branch_oriented
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {L : Matrix (Fin 4) (Fin size) ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    (hmemAll : ∀ slotIndex : Fin 4, basisLabel slotIndex ∈ activeSet)
    (killKFour : (∀ slotK slotL : Fin 4, slotK ≠ slotL →
      pairShare tightDir basisLabel slotK slotL = 1) → False)
    (killCycleIndependent : ∀ (slotK slotL slotM slotN : Fin 4)
      (pairAtomOne pairAtomTwo coAtomOne coAtomTwo singleKM singleLN : Fin size),
      slotK ≠ slotL → slotM ≠ slotN → slotK ≠ slotM → slotK ≠ slotN →
      slotL ≠ slotM → slotL ≠ slotN →
      pairAtomOne ≠ pairAtomTwo → coAtomOne ≠ coAtomTwo →
      shareSet tightDir basisLabel slotK slotL = {pairAtomOne, pairAtomTwo} →
      shareSet tightDir basisLabel slotM slotN = {coAtomOne, coAtomTwo} →
      shareSet tightDir basisLabel slotK slotM = {singleKM} →
      shareSet tightDir basisLabel slotL slotN = {singleLN} →
      datumTightSupport tightDir (basisLabel slotK)
        = {pairAtomOne, pairAtomTwo, singleKM} →
      datumTightSupport tightDir (basisLabel slotL)
        = {pairAtomOne, pairAtomTwo, singleLN} →
      datumTightSupport tightDir (basisLabel slotM)
        = {coAtomOne, coAtomTwo, singleKM} →
      datumTightSupport tightDir (basisLabel slotN)
        = {coAtomOne, coAtomTwo, singleLN} →
      (tightDir (basisLabel slotK) pairAtomOne
            * tightDir (basisLabel slotL) pairAtomTwo
          - tightDir (basisLabel slotK) pairAtomTwo
            * tightDir (basisLabel slotL) pairAtomOne ≠ 0
        ∨ tightDir (basisLabel slotM) coAtomOne
            * tightDir (basisLabel slotN) coAtomTwo
          - tightDir (basisLabel slotM) coAtomTwo
            * tightDir (basisLabel slotN) coAtomOne ≠ 0) →
      False)
    (killCycleBothParallel : ∀ (slotK slotL slotM slotN : Fin 4)
      (pairAtomOne pairAtomTwo coAtomOne coAtomTwo singleKM singleLN : Fin size),
      slotK ≠ slotL → slotM ≠ slotN → slotK ≠ slotM → slotK ≠ slotN →
      slotL ≠ slotM → slotL ≠ slotN →
      pairAtomOne ≠ pairAtomTwo → coAtomOne ≠ coAtomTwo →
      shareSet tightDir basisLabel slotK slotL = {pairAtomOne, pairAtomTwo} →
      shareSet tightDir basisLabel slotM slotN = {coAtomOne, coAtomTwo} →
      shareSet tightDir basisLabel slotK slotM = {singleKM} →
      shareSet tightDir basisLabel slotL slotN = {singleLN} →
      datumTightSupport tightDir (basisLabel slotK)
        = {pairAtomOne, pairAtomTwo, singleKM} →
      datumTightSupport tightDir (basisLabel slotL)
        = {pairAtomOne, pairAtomTwo, singleLN} →
      datumTightSupport tightDir (basisLabel slotM)
        = {coAtomOne, coAtomTwo, singleKM} →
      datumTightSupport tightDir (basisLabel slotN)
        = {coAtomOne, coAtomTwo, singleLN} →
      tightDir (basisLabel slotK) pairAtomOne
          * tightDir (basisLabel slotL) pairAtomTwo
        - tightDir (basisLabel slotK) pairAtomTwo
          * tightDir (basisLabel slotL) pairAtomOne = 0 →
      tightDir (basisLabel slotM) coAtomOne
          * tightDir (basisLabel slotN) coAtomTwo
        - tightDir (basisLabel slotM) coAtomTwo
          * tightDir (basisLabel slotN) coAtomOne = 0 →
      False) :
    False := by
  refine false_of_dense_branch_of_cycle_kills hdata hvalueNeg basisLabel hleft
    hrepresentation htrace hmult hcard hmemAll killKFour ?_
  intro slotK slotL slotM slotN hKL hMN hKM hKN hLM hLN h2KL h2MN h1KM h1LN
    _h0KN _h0LM
  obtain ⟨pairAtomOne, pairAtomTwo, coAtomOne, coAtomTwo, singleKM, singleLN,
    hpairNe, hcoNe, _hmemP1, _hmemP2, _hmemC1, _hmemC2, hmemKM, hmemLN,
    hpairSet, hcoSet, hKMset, hLNset⟩ :=
    exists_cycle_atom_labeling basisLabel h2KL h2MN h1KM h1LN
  have hpairSetLK : shareSet tightDir basisLabel slotL slotK
      = {pairAtomOne, pairAtomTwo} := by
    rw [shareSet_comm]
    exact hpairSet
  have hcoSetNM : shareSet tightDir basisLabel slotN slotM
      = {coAtomOne, coAtomTwo} := by
    rw [shareSet_comm]
    exact hcoSet
  have hmemMK : singleKM ∈ shareSet tightDir basisLabel slotM slotK := by
    rw [shareSet_comm]
    exact hmemKM
  have hmemNL : singleLN ∈ shareSet tightDir basisLabel slotN slotL := by
    rw [shareSet_comm]
    exact hmemLN
  have hsuppK := cycle_support_enumeration basisLabel hmult hKL hKM hLM
    (hcard slotK) hpairNe hpairSet hmemKM
  have hsuppL := cycle_support_enumeration basisLabel hmult (Ne.symm hKL)
    hLN hKN (hcard slotL) hpairNe hpairSetLK hmemLN
  have hsuppM := cycle_support_enumeration basisLabel hmult hMN
    (Ne.symm hKM) (Ne.symm hKN) (hcard slotM) hcoNe hcoSet hmemMK
  have hsuppN := cycle_support_enumeration basisLabel hmult (Ne.symm hMN)
    (Ne.symm hLN) (Ne.symm hLM) (hcard slotN) hcoNe hcoSetNM hmemNL
  by_cases hdetKL : tightDir (basisLabel slotK) pairAtomOne
      * tightDir (basisLabel slotL) pairAtomTwo
    - tightDir (basisLabel slotK) pairAtomTwo
      * tightDir (basisLabel slotL) pairAtomOne = 0
  · by_cases hdetMN : tightDir (basisLabel slotM) coAtomOne
        * tightDir (basisLabel slotN) coAtomTwo
      - tightDir (basisLabel slotM) coAtomTwo
        * tightDir (basisLabel slotN) coAtomOne = 0
    · exact killCycleBothParallel slotK slotL slotM slotN pairAtomOne
        pairAtomTwo coAtomOne coAtomTwo singleKM singleLN hKL hMN hKM hKN
        hLM hLN hpairNe hcoNe hpairSet hcoSet hKMset hLNset hsuppK hsuppL
        hsuppM hsuppN hdetKL hdetMN
    · exact killCycleIndependent slotK slotL slotM slotN pairAtomOne
        pairAtomTwo coAtomOne coAtomTwo singleKM singleLN hKL hMN hKM hKN
        hLM hLN hpairNe hcoNe hpairSet hcoSet hKMset hLNset hsuppK hsuppL
        hsuppM hsuppN (Or.inr hdetMN)
  · exact killCycleIndependent slotK slotL slotM slotN pairAtomOne
      pairAtomTwo coAtomOne coAtomTwo singleKM singleLN hKL hMN hKM hKN
      hLM hLN hpairNe hcoNe hpairSet hcoSet hKMset hLNset hsuppK hsuppL
      hsuppM hsuppN (Or.inl hdetKL)

end Gtz

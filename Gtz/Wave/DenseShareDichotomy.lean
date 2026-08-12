import Gtz.Wave.GapRowDictionary
import Gtz.Wave.TwoSharedPairKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense share dichotomy — the multigraph dispatch of the dense branch

At the dense census branch every atom sits in exactly two basis supports
and every support has three atoms.  The six atoms are then the six edges
of a 3-regular multigraph on the four slots, and the edge multiplicities —
the pair shares — obey the degree law: the three shares at a slot sum to
the support cardinality.  Linear arithmetic turns the degree law into a
DICHOTOMY: either every pair shares exactly one atom (the K4 shape), or
two disjoint pairs each share at least two atoms (the doubled shapes).

The dichotomy replaces the three-representative census: the two-triple
shape and the doubled-cycle shape both live in the second branch, and the
routing bridges of this file hand each side its kill interface — equal
supports at a full share, two shared atoms with exclusive carriers at a
double share.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pairShare` with `Gtz.pairShare_symm`, `Gtz.pairShare_self`,
  `Gtz.pairShare_le_card` — **THE SHARE VOCABULARY.**
* `Gtz.sum_erase_pairShare_eq_card` — **THE DEGREE LAW.**
* `Gtz.share_dichotomy_arith` — **THE ARITHMETIC CORE**, closed by
  `omega`.
* `Gtz.dense_share_dichotomy` — **THE DISPATCH.**  The K4 profile or two
  disjoint doubled pairs, at every dense datum.
* `Gtz.supports_eq_of_pairShare_full` — the full-share routing: a share
  of three makes the two supports equal.
* `Gtz.exists_two_shared_atoms_of_two_le_pairShare` — the double-share
  routing: two distinct shared atoms.
* `Gtz.shared_atom_exclusive_carriers` — a shared atom of a
  multiplicity-two datum meets no third support.

## Vacuity

The statements are unconditional over the direction family: the dense
hypotheses enter as explicit cardinality assumptions.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## The share vocabulary -/

/-- The pair share: the number of atoms in both supports. -/
noncomputable def pairShare (tightDir : activeIndex → (Fin size → ℝ))
    (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) : ℕ :=
  (Finset.univ.filter fun atomIndex =>
    atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
      ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)).card

/-- The share is symmetric. -/
theorem pairShare_symm (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) :
    pairShare tightDir basisLabel slotK slotL
      = pairShare tightDir basisLabel slotL slotK := by
  unfold pairShare
  congr 1
  apply Finset.filter_congr
  intro atomIndex _
  exact and_comm

/-- The self share is the support cardinality. -/
theorem pairShare_self (basisLabel : Fin basisCount → activeIndex)
    (slotK : Fin basisCount) :
    pairShare tightDir basisLabel slotK slotK
      = (datumTightSupport tightDir (basisLabel slotK)).card := by
  unfold pairShare
  congr 1
  ext atomIndex
  simp [and_self]

/-- The share is at most the support cardinality. -/
theorem pairShare_le_card (basisLabel : Fin basisCount → activeIndex)
    (slotK slotL : Fin basisCount) :
    pairShare tightDir basisLabel slotK slotL
      ≤ (datumTightSupport tightDir (basisLabel slotK)).card := by
  unfold pairShare
  apply Finset.card_le_card
  intro atomIndex hmem
  exact (Finset.mem_filter.mp hmem).2.1

/-! ## The degree law -/

/-- **THE DEGREE LAW.**  At a multiplicity-two datum, the shares of a slot
against the other slots sum to its support cardinality: each support atom
has exactly one other carrier. -/
theorem sum_erase_pairShare_eq_card
    (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (slotK : Fin basisCount) :
    ∑ slotL ∈ Finset.univ.erase slotK,
      pairShare tightDir basisLabel slotK slotL
      = (datumTightSupport tightDir (basisLabel slotK)).card := by
  classical
  have hstep : ∀ slotL : Fin basisCount,
      pairShare tightDir basisLabel slotK slotL
      = ∑ atomIndex ∈ datumTightSupport tightDir (basisLabel slotK),
          if atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)
            then 1 else 0 := by
    intro slotL
    unfold pairShare
    rw [Finset.card_filter]
    rw [Finset.sum_congr rfl (fun atomIndex _ => ite_and
      (atomIndex ∈ datumTightSupport tightDir (basisLabel slotK))
      (atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)) (1 : ℕ) 0)]
    rw [← Finset.sum_filter, Finset.filter_univ_mem]
  rw [Finset.sum_congr rfl fun slotL _ => hstep slotL, Finset.sum_comm]
  have hinner : ∀ atomIndex ∈ datumTightSupport tightDir (basisLabel slotK),
      (∑ slotL ∈ Finset.univ.erase slotK,
        if atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)
          then (1 : ℕ) else 0) = 1 := by
    intro atomIndex hatom
    rw [← Finset.card_filter]
    have hcommute : (Finset.univ.erase slotK).filter (fun slotL =>
        atomIndex ∈ datumTightSupport tightDir (basisLabel slotL))
        = (Finset.univ.filter fun slotL =>
            atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)).erase
          slotK := by
      rw [Finset.filter_erase]
    rw [hcommute, Finset.card_erase_of_mem]
    · have hmultAtom := hmult atomIndex
      rw [basisSupportMultiplicity] at hmultAtom
      omega
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hatom⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_one]

/-! ## The arithmetic core -/

/-- **THE ARITHMETIC CORE.**  Six shares with the four degree equations at
value three fall into the K4 profile or carry two disjoint doubled
pairs. -/
theorem share_dichotomy_arith
    (share01 share02 share03 share12 share13 share23 : ℕ)
    (hdeg0 : share01 + share02 + share03 = 3)
    (hdeg1 : share01 + share12 + share13 = 3)
    (hdeg2 : share02 + share12 + share23 = 3)
    (hdeg3 : share03 + share13 + share23 = 3) :
    (share01 = 1 ∧ share02 = 1 ∧ share03 = 1 ∧ share12 = 1 ∧ share13 = 1
        ∧ share23 = 1)
      ∨ (2 ≤ share01 ∧ 2 ≤ share23)
      ∨ (2 ≤ share02 ∧ 2 ≤ share13)
      ∨ (2 ≤ share03 ∧ 2 ≤ share12) := by
  omega

/-! ## The dispatch -/

/-- **THE DISPATCH.**  At a dense multiplicity-two datum on four slots,
either every distinct pair shares exactly one atom, or two disjoint pairs
each share at least two. -/
theorem dense_share_dichotomy
    (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3) :
    (∀ slotK slotL : Fin 4, slotK ≠ slotL →
        pairShare tightDir basisLabel slotK slotL = 1)
      ∨ ∃ slotK slotL slotM slotN : Fin 4,
        slotK ≠ slotL ∧ slotM ≠ slotN ∧ slotK ≠ slotM ∧ slotK ≠ slotN
          ∧ slotL ≠ slotM ∧ slotL ≠ slotN
          ∧ 2 ≤ pairShare tightDir basisLabel slotK slotL
          ∧ 2 ≤ pairShare tightDir basisLabel slotM slotN := by
  classical
  have hdeg : ∀ slotK : Fin 4,
      ∑ slotL ∈ Finset.univ.erase slotK,
        pairShare tightDir basisLabel slotK slotL = 3 := by
    intro slotK
    rw [sum_erase_pairShare_eq_card basisLabel hmult slotK, hcard slotK]
  have hexpand : ∀ slotK : Fin 4,
      ∑ slotL ∈ Finset.univ.erase slotK,
        pairShare tightDir basisLabel slotK slotL
      = (∑ slotL : Fin 4, pairShare tightDir basisLabel slotK slotL)
        - pairShare tightDir basisLabel slotK slotK := by
    intro slotK
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun slotL => pairShare tightDir basisLabel slotK slotL)
      (Finset.mem_univ slotK)
    omega
  have hself : ∀ slotK : Fin 4,
      pairShare tightDir basisLabel slotK slotK = 3 := by
    intro slotK
    rw [pairShare_self basisLabel slotK, hcard slotK]
  have huniv : ∀ slotK : Fin 4,
      ∑ slotL : Fin 4, pairShare tightDir basisLabel slotK slotL = 6 := by
    intro slotK
    have hval := hdeg slotK
    rw [hexpand slotK, hself slotK] at hval
    have hle : pairShare tightDir basisLabel slotK slotK
        ≤ ∑ slotL : Fin 4, pairShare tightDir basisLabel slotK slotL :=
      Finset.single_le_sum (fun slotL _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  have hrow : ∀ slotK : Fin 4,
      pairShare tightDir basisLabel slotK 0 + pairShare tightDir basisLabel slotK 1
        + pairShare tightDir basisLabel slotK 2
        + pairShare tightDir basisLabel slotK 3 = 6 := by
    intro slotK
    have hval := huniv slotK
    rw [Fin.sum_univ_four] at hval
    exact hval
  have hdegZero : pairShare tightDir basisLabel 0 1
      + pairShare tightDir basisLabel 0 2
      + pairShare tightDir basisLabel 0 3 = 3 := by
    have := hrow 0
    have := hself 0
    omega
  have hdegOne : pairShare tightDir basisLabel 0 1
      + pairShare tightDir basisLabel 1 2
      + pairShare tightDir basisLabel 1 3 = 3 := by
    have := hrow 1
    have := hself 1
    have := pairShare_symm (tightDir := tightDir) basisLabel 1 0
    omega
  have hdegTwo : pairShare tightDir basisLabel 0 2
      + pairShare tightDir basisLabel 1 2
      + pairShare tightDir basisLabel 2 3 = 3 := by
    have := hrow 2
    have := hself 2
    have := pairShare_symm (tightDir := tightDir) basisLabel 2 0
    have := pairShare_symm (tightDir := tightDir) basisLabel 2 1
    omega
  have hdegThree : pairShare tightDir basisLabel 0 3
      + pairShare tightDir basisLabel 1 3
      + pairShare tightDir basisLabel 2 3 = 3 := by
    have := hrow 3
    have := hself 3
    have := pairShare_symm (tightDir := tightDir) basisLabel 3 0
    have := pairShare_symm (tightDir := tightDir) basisLabel 3 1
    have := pairShare_symm (tightDir := tightDir) basisLabel 3 2
    omega
  have hcore := share_dichotomy_arith
    (pairShare tightDir basisLabel 0 1) (pairShare tightDir basisLabel 0 2)
    (pairShare tightDir basisLabel 0 3) (pairShare tightDir basisLabel 1 2)
    (pairShare tightDir basisLabel 1 3) (pairShare tightDir basisLabel 2 3)
    hdegZero hdegOne hdegTwo hdegThree
  rcases hcore with hK4 | hpair | hpair | hpair
  · left
    intro slotK slotL hne
    fin_cases slotK <;> fin_cases slotL
    · exact absurd rfl hne
    · exact hK4.1
    · exact hK4.2.1
    · exact hK4.2.2.1
    · exact (pairShare_symm basisLabel _ _).trans hK4.1
    · exact absurd rfl hne
    · exact hK4.2.2.2.1
    · exact hK4.2.2.2.2.1
    · exact (pairShare_symm basisLabel _ _).trans hK4.2.1
    · exact (pairShare_symm basisLabel _ _).trans hK4.2.2.2.1
    · exact absurd rfl hne
    · exact hK4.2.2.2.2.2
    · exact (pairShare_symm basisLabel _ _).trans hK4.2.2.1
    · exact (pairShare_symm basisLabel _ _).trans hK4.2.2.2.2.1
    · exact (pairShare_symm basisLabel _ _).trans hK4.2.2.2.2.2
    · exact absurd rfl hne
  · right
    exact ⟨0, 1, 2, 3, by omega, by omega, by omega, by omega, by omega,
      by omega, hpair.1, hpair.2⟩
  · right
    exact ⟨0, 2, 1, 3, by omega, by omega, by omega, by omega, by omega,
      by omega, hpair.1, hpair.2⟩
  · right
    exact ⟨0, 3, 1, 2, by omega, by omega, by omega, by omega, by omega,
      by omega, hpair.1, hpair.2⟩

/-! ## The routing bridges -/

/-- **THE FULL-SHARE ROUTING.**  A share equal to the two support
cardinalities makes the supports equal. -/
theorem supports_eq_of_pairShare_full
    (basisLabel : Fin basisCount → activeIndex) {slotK slotL : Fin basisCount}
    (hcardK : (datumTightSupport tightDir (basisLabel slotK)).card = 3)
    (hcardL : (datumTightSupport tightDir (basisLabel slotL)).card = 3)
    (hshare : pairShare tightDir basisLabel slotK slotL = 3) :
    datumTightSupport tightDir (basisLabel slotK)
      = datumTightSupport tightDir (basisLabel slotL) := by
  classical
  rw [pairShare] at hshare
  have hinter : (Finset.univ.filter fun atomIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
        ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL))
      ⊆ datumTightSupport tightDir (basisLabel slotK) := by
    intro atomIndex hmem
    exact (Finset.mem_filter.mp hmem).2.1
  have hK : (Finset.univ.filter fun atomIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
        ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL))
      = datumTightSupport tightDir (basisLabel slotK) := by
    refine Finset.eq_of_subset_of_card_le hinter ?_
    rw [hcardK, hshare]
  ext atomIndex
  constructor
  · intro hmemK
    have hmemFilter : atomIndex ∈ Finset.univ.filter fun atomIndex =>
        atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
          ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL) := by
      rw [hK]
      exact hmemK
    exact (Finset.mem_filter.mp hmemFilter).2.2
  · intro hmemL
    by_contra hnot
    have hinterL : (Finset.univ.filter fun atomIndex =>
        atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
          ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL))
        ⊆ (datumTightSupport tightDir (basisLabel slotL)).erase atomIndex := by
      intro otherIndex hmem
      obtain ⟨-, hmemK', hmemL'⟩ := Finset.mem_filter.mp hmem
      refine Finset.mem_erase.mpr ⟨?_, hmemL'⟩
      intro heq
      exact hnot (heq ▸ hmemK')
    have hcardBound := Finset.card_le_card hinterL
    rw [Finset.card_erase_of_mem hmemL, hcardL, hshare] at hcardBound
    omega

/-- **THE DOUBLE-SHARE ROUTING.**  A share of at least two yields two
distinct atoms in both supports. -/
theorem exists_two_shared_atoms_of_two_le_pairShare
    (basisLabel : Fin basisCount → activeIndex) {slotK slotL : Fin basisCount}
    (hshare : 2 ≤ pairShare tightDir basisLabel slotK slotL) :
    ∃ atomOne atomTwo : Fin size, atomOne ≠ atomTwo
      ∧ atomOne ∈ datumTightSupport tightDir (basisLabel slotK)
      ∧ atomOne ∈ datumTightSupport tightDir (basisLabel slotL)
      ∧ atomTwo ∈ datumTightSupport tightDir (basisLabel slotK)
      ∧ atomTwo ∈ datumTightSupport tightDir (basisLabel slotL) := by
  classical
  rw [pairShare] at hshare
  obtain ⟨atomOne, hmemOne, atomTwo, hmemTwo, hne⟩ :=
    Finset.one_lt_card.mp (show 1 < (Finset.univ.filter fun atomIndex =>
      atomIndex ∈ datumTightSupport tightDir (basisLabel slotK)
        ∧ atomIndex ∈ datumTightSupport tightDir (basisLabel slotL)).card
      by omega)
  obtain ⟨-, hK1, hL1⟩ := Finset.mem_filter.mp hmemOne
  obtain ⟨-, hK2, hL2⟩ := Finset.mem_filter.mp hmemTwo
  exact ⟨atomOne, atomTwo, hne, hK1, hL1, hK2, hL2⟩

/-- **THE EXCLUSIVE CARRIERS.**  At a multiplicity-two datum, an atom
inside two distinct supports meets no third: every other slot's direction
vanishes there. -/
theorem shared_atom_exclusive_carriers
    (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL : Fin basisCount} (hKL : slotK ≠ slotL)
    {atomIndex : Fin size}
    (hmemK : atomIndex ∈ datumTightSupport tightDir (basisLabel slotK))
    (hmemL : atomIndex ∈ datumTightSupport tightDir (basisLabel slotL))
    {slotOther : Fin basisCount} (hOK : slotOther ≠ slotK)
    (hOL : slotOther ≠ slotL) :
    tightDir (basisLabel slotOther) atomIndex = 0 := by
  classical
  by_contra hnonzero
  have hmultAtom := hmult atomIndex
  rw [basisSupportMultiplicity] at hmultAtom
  have hsubset : ({slotK, slotL, slotOther} : Finset (Fin basisCount))
      ⊆ Finset.univ.filter fun slotIndex =>
        atomIndex ∈ datumTightSupport tightDir (basisLabel slotIndex) := by
    intro slotIndex hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · rw [heq]
      exact hmemK
    · rcases Finset.mem_insert.mp hmem' with heq | hmem''
      · rw [heq]
        exact hmemL
      · rw [Finset.mem_singleton.mp hmem'']
        exact mem_datumTightSupport.mpr hnonzero
  have hcardTriple : ({slotK, slotL, slotOther} : Finset (Fin basisCount)).card
      = 3 :=
    card_triple_of_distinct hKL (Ne.symm hOK) (Ne.symm hOL)
  have hbound := Finset.card_le_card hsubset
  rw [hcardTriple, hmultAtom] at hbound
  omega

/-! ## The doubled-pair split and the full-share kill composition -/

variable {rank : ℕ}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}

/-- **THE DOUBLED-PAIR SPLIT.**  A doubled pair at card-3 supports shares
exactly two atoms or its supports are equal. -/
theorem doubled_pair_split
    (basisLabel : Fin basisCount → activeIndex) {slotK slotL : Fin basisCount}
    (hcardK : (datumTightSupport tightDir (basisLabel slotK)).card = 3)
    (hcardL : (datumTightSupport tightDir (basisLabel slotL)).card = 3)
    (hshare : 2 ≤ pairShare tightDir basisLabel slotK slotL) :
    pairShare tightDir basisLabel slotK slotL = 2
      ∨ datumTightSupport tightDir (basisLabel slotK)
        = datumTightSupport tightDir (basisLabel slotL) := by
  have hle := pairShare_le_card (tightDir := tightDir) basisLabel slotK slotL
  rw [hcardK] at hle
  by_cases htwo : pairShare tightDir basisLabel slotK slotL = 2
  · exact Or.inl htwo
  · refine Or.inr (supports_eq_of_pairShare_full basisLabel hcardK hcardL ?_)
    omega

/-- **THE FULL-SHARE KILL.**  Two disjoint pairs with full shares die: the
supports of each pair are equal, the shared atoms are exclusive by the
multiplicity, and the landed two-shared-pair kill closes.  This covers
the two-triple representative and every doubled shape that degenerates to
a full share. -/
theorem false_of_two_full_shares
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
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
    (hmemAll : ∀ slotIndex : Fin 4, basisLabel slotIndex ∈ activeSet)
    {slotK slotL slotM slotN : Fin 4}
    (hKL : slotK ≠ slotL) (hMN : slotM ≠ slotN) (hKM : slotK ≠ slotM)
    (hKN : slotK ≠ slotN) (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN)
    (hcardK : (datumTightSupport tightDir (basisLabel slotK)).card = 3)
    (hcardM : (datumTightSupport tightDir (basisLabel slotM)).card = 3)
    (hsharedKL : datumTightSupport tightDir (basisLabel slotK)
      = datumTightSupport tightDir (basisLabel slotL))
    (hsharedMN : datumTightSupport tightDir (basisLabel slotM)
      = datumTightSupport tightDir (basisLabel slotN)) :
    False := by
  have hnonemptyK : (datumTightSupport tightDir (basisLabel slotK)).Nonempty := by
    rw [← Finset.card_pos, hcardK]
    norm_num
  have hnonemptyM : (datumTightSupport tightDir (basisLabel slotM)).Nonempty := by
    rw [← Finset.card_pos, hcardM]
    norm_num
  have hcarriersKL : ∀ atomIndex : Fin size,
      tightDir (basisLabel slotK) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ slotK → columnIndex ≠ slotL →
        tightDir (basisLabel columnIndex) atomIndex = 0 := by
    intro atomIndex hnonzero columnIndex hcK hcL
    have hmemK := mem_datumTightSupport.mpr hnonzero
    have hmemL : atomIndex ∈ datumTightSupport tightDir (basisLabel slotL) := by
      rw [← hsharedKL]
      exact hmemK
    exact shared_atom_exclusive_carriers basisLabel hmult hKL hmemK hmemL hcK hcL
  have hcarriersMN : ∀ atomIndex : Fin size,
      tightDir (basisLabel slotM) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ slotM → columnIndex ≠ slotN →
        tightDir (basisLabel columnIndex) atomIndex = 0 := by
    intro atomIndex hnonzero columnIndex hcM hcN
    have hmemM := mem_datumTightSupport.mpr hnonzero
    have hmemN : atomIndex ∈ datumTightSupport tightDir (basisLabel slotN) := by
      rw [← hsharedMN]
      exact hmemM
    exact shared_atom_exclusive_carriers basisLabel hmult hMN hmemM hmemN hcM hcN
  exact false_of_two_shared_support_pairs hdata hvalueNeg basisLabel hleft
    hrepresentation htrace hKL hMN hKM hKN hLM hLN (hmemAll slotK)
    (hmemAll slotL) (hmemAll slotM) (hmemAll slotN) hsharedKL hsharedMN
    hnonemptyK hnonemptyM hcarriersKL hcarriersMN

/-- **THE DENSE ROUTING.**  At a dense datum with the coefficient frame,
the branch dies once the K4 profile and the double-double profile die:
the dichotomy routes, the full shares die here, and the two open profiles
enter as hypothesis-shaped continuations.  The rank-four rung consumes
this theorem with the two continuations as its named open sub-branches. -/
theorem false_of_dense_branch_of_profiles
    (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    (killKFour : (∀ slotK slotL : Fin 4, slotK ≠ slotL →
      pairShare tightDir basisLabel slotK slotL = 1) → False)
    (killDoubled : ∀ slotK slotL slotM slotN : Fin 4,
      slotK ≠ slotL → slotM ≠ slotN → slotK ≠ slotM → slotK ≠ slotN →
      slotL ≠ slotM → slotL ≠ slotN →
      2 ≤ pairShare tightDir basisLabel slotK slotL →
      2 ≤ pairShare tightDir basisLabel slotM slotN → False) :
    False := by
  rcases dense_share_dichotomy basisLabel hmult hcard with hKFour | hpair
  · exact killKFour hKFour
  obtain ⟨slotK, slotL, slotM, slotN, hKL, hMN, hKM, hKN, hLM, hLN,
    hshareKL, hshareMN⟩ := hpair
  exact killDoubled slotK slotL slotM slotN hKL hMN hKM hKN hLM hLN
    hshareKL hshareMN

end Gtz

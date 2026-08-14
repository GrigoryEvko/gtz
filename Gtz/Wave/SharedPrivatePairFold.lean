import Gtz.Wave.SharedPrivateComplementEigen
import Gtz.Wave.SharedPrivateDiagonalKill
import Gtz.Wave.SharedPrivateSlotSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The pair fold — the identical branch dies by a change of basis

The identical branch held the last hard shapes of the shared-private
lattice.  This module removes the branch without a per-label kill.

## The fold

Two basis slots with one support span a tight plane.  Any recombination
of the two columns inside that plane is again a family of tight
directions, and the Gram core transforms by congruence.  The fold picks
the recombination that kills the corner of the Gram core on the pair:
the first new column is `u_a + t u_b`, and the second is
`(g_ab - t g_aa) u_a + (g_bb - t g_ab) u_b`.  The two coefficient
vectors are conjugate for the inverse of the corner, thus the folded
corner is diagonal at EVERY `t`, and the recombination determinant is
the corner energy of `(-t, 1)`, which is positive at a positive
definite core.

The parameter `t` buys the supports.  At each atom of the pair support,
each folded column vanishes at one value of `t` at most, because a
vanishing pair of affine coefficients puts a nonzero vector in the
kernel of the corner.  Six values are bad at most, thus a good `t`
exists, and the folded columns keep the full support of three atoms.

## The dispatch

The Gram core is a mixture over the positive labels.  If some nonzero
off-diagonal entry joins two slots with DIFFERENT supports, the mixture
supplies a label with both coefficients nonzero, and the label dies
through the split and wide residues.  If every nonzero off-diagonal
entry joins two slots with ONE support, the equal-support classes are
pairs, the pairs are Gram-isolated, and the fold rebases the datum onto
a diagonal Gram core.  The landed diagonal kill then closes the datum.
Thus the identical residue leaves the lattice: the generic
shared-private kill needs the two split residues and the wide residue
only.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SharedPrivateData.gram_quadratic_pos` — the Gram core is positive
  definite.
* `Gtz.SharedPrivateData.pairedPartner` with the four partner laws — the
  equal-support classes are pairs.
* `Gtz.SharedPrivateData.foldMatrix`, `Gtz.SharedPrivateData.foldInverse`
  with `foldMatrix_mul_foldInverse` — **THE FOLD AND ITS INVERSE.**
* `Gtz.SharedPrivateData.foldGram_offDiag_eq_zero` — **THE FOLDED CORE
  IS DIAGONAL** on the isolated lattice.
* `Gtz.SharedPrivateData.exists_foldParameter` — **THE GOOD PARAMETER
  EXISTS.**
* `Gtz.SharedPrivateData.false_of_supportPaired_gram` — **THE FOLD
  KILL**: a datum whose nonzero off-diagonal Gram entries all join
  equal-support slots is dead.
* `Gtz.SharedPrivateData.exists_label_of_gram_ne_zero` — the mixture
  witness of a nonzero entry.
* `Gtz.SharedPrivateData.false_of_pair_label_of_support_ne` — the pair
  label with different supports dies through the split residues.
* `Gtz.sharedPrivateKilled_of_foldLattice` — **THE GENERIC KILL ON
  THREE RESIDUES**, with the identical residue replaced by the fold.
* `Gtz.rankFourSharedPrivateClosed_of_foldLattice`,
  `Gtz.rankFiveSharedPrivateClosed_of_foldLattice`,
  `Gtz.rankSixSharedPrivateClosed_of_foldLattice` — the three rung
  closures on the three residues.
* `Gtz.SharedPrivateData.captureGram_diagonal_eq` and
  `Gtz.SharedPrivateData.deadLeak_orthogonal` — **THE CAPTURE DIAGONAL
  LAW** of the Gram core and its dead-leak reading.

## Vacuity

Every statement quantifies over shared-private data, and no datum
exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-! ## Layer 0 — positivity and entry calculus of the Gram core -/

/-- The entry symmetry of the Gram core. -/
theorem gram_entry_symm (data : SharedPrivateData crux)
    (slotA slotB : Fin data.basisCount) :
    data.gram slotA slotB = data.gram slotB slotA := by
  have hentry := congrFun (congrFun data.hsymmH slotB) slotA
  rw [Matrix.transpose_apply] at hentry
  exact hentry

/-- **THE GRAM CORE IS POSITIVE DEFINITE.**  The core is positive
semidefinite with a trivial kernel, thus every nonzero probe has
positive energy. -/
theorem gram_quadratic_pos (data : SharedPrivateData crux)
    {probe : Fin data.basisCount → ℝ} (hne : probe ≠ 0) :
    0 < probe ⬝ᵥ (data.gram *ᵥ probe) := by
  rcases (data.hpsd.dotProduct_mulVec_nonneg probe).lt_or_eq with hpos | heq
  · simpa using hpos
  · exfalso
    have hzero : data.gram *ᵥ probe = 0 :=
      (data.hpsd.dotProduct_mulVec_zero_iff probe).mp (by simpa using heq.symm)
    exact hne (data.hker probe hzero)

/-- The two-point collapse of a Gram row read. -/
theorem twoPoint_row_read (data : SharedPrivateData crux)
    {slotA slotB : Fin data.basisCount} (hab : slotA ≠ slotB)
    (coeffA coeffB : ℝ) (rowSlot : Fin data.basisCount) :
    (data.gram *ᵥ fun slot =>
        (if slot = slotA then coeffA else 0)
          + (if slot = slotB then coeffB else 0)) rowSlot
      = data.gram rowSlot slotA * coeffA + data.gram rowSlot slotB * coeffB := by
  classical
  show (∑ slot, data.gram rowSlot slot
      * ((if slot = slotA then coeffA else 0)
        + (if slot = slotB then coeffB else 0)))
    = data.gram rowSlot slotA * coeffA + data.gram rowSlot slotB * coeffB
  rw [← Finset.sum_subset
    (Finset.subset_univ ({slotA, slotB} : Finset (Fin data.basisCount)))
    (fun slot _ hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      rw [if_neg hnot.1, if_neg hnot.2, add_zero, mul_zero]),
    Finset.sum_pair hab, if_pos rfl, if_neg hab, if_neg (Ne.symm hab), if_pos rfl]
  ring

/-- **THE PAIR ENERGY.**  The two-by-two corner energy of the Gram core
at a nonzero coefficient pair is positive. -/
theorem gram_pair_energy_pos (data : SharedPrivateData crux)
    {slotA slotB : Fin data.basisCount} (hab : slotA ≠ slotB)
    {coeffA coeffB : ℝ} (hne : coeffA ≠ 0 ∨ coeffB ≠ 0) :
    0 < coeffA * coeffA * data.gram slotA slotA
        + 2 * (coeffA * coeffB) * data.gram slotA slotB
        + coeffB * coeffB * data.gram slotB slotB := by
  classical
  set probe : Fin data.basisCount → ℝ := fun slot =>
    (if slot = slotA then coeffA else 0) + (if slot = slotB then coeffB else 0)
    with hprobe
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    rcases hne with hA | hB
    · have := congrFun hzero slotA
      rw [hprobe] at this
      simp only [if_neg hab, add_zero, Pi.zero_apply, if_true] at this
      exact hA this
    · have := congrFun hzero slotB
      rw [hprobe] at this
      simp only [if_neg (Ne.symm hab), zero_add, Pi.zero_apply, if_true] at this
      exact hB this
  have hpos := data.gram_quadratic_pos hprobeNe
  have hread : probe ⬝ᵥ (data.gram *ᵥ probe)
      = coeffA * coeffA * data.gram slotA slotA
        + 2 * (coeffA * coeffB) * data.gram slotA slotB
        + coeffB * coeffB * data.gram slotB slotB := by
    show (∑ slot, probe slot * (data.gram *ᵥ probe) slot) = _
    rw [← Finset.sum_subset
      (Finset.subset_univ ({slotA, slotB} : Finset (Fin data.basisCount)))
      (fun slot _ hnot => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        rw [hprobe]
        simp only [if_neg hnot.1, if_neg hnot.2, add_zero, zero_mul]),
      Finset.sum_pair hab]
    rw [hprobe]
    simp only [data.twoPoint_row_read hab coeffA coeffB,
      if_neg hab, if_neg (Ne.symm hab), add_zero, zero_add, if_true]
    rw [data.gram_entry_symm slotB slotA]
    ring
  rw [hread] at hpos
  exact hpos

/-! ## Layer 1 — the partner of an identical pair -/

open Classical in
/-- The equal-support partner of a basis slot, or the slot itself when no
partner exists. -/
noncomputable def pairedPartner (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) : Fin data.basisCount :=
  if h : ∃ other, other ≠ slot
      ∧ datumTightSupport data.tightDir (data.basisLabel other)
        = datumTightSupport data.tightDir (data.basisLabel slot) then
    h.choose
  else slot

/-- The partner law: a partnered slot reads its partner's support. -/
theorem pairedPartner_spec (data : SharedPrivateData crux)
    {slot : Fin data.basisCount}
    (h : ∃ other, other ≠ slot
      ∧ datumTightSupport data.tightDir (data.basisLabel other)
        = datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.pairedPartner slot ≠ slot
      ∧ datumTightSupport data.tightDir (data.basisLabel (data.pairedPartner slot))
        = datumTightSupport data.tightDir (data.basisLabel slot) := by
  rw [pairedPartner, dif_pos h]
  exact h.choose_spec

/-- The self law: an unpartnered slot folds to itself. -/
theorem pairedPartner_eq_self (data : SharedPrivateData crux)
    {slot : Fin data.basisCount}
    (h : ¬ ∃ other, other ≠ slot
      ∧ datumTightSupport data.tightDir (data.basisLabel other)
        = datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.pairedPartner slot = slot := by
  rw [pairedPartner, dif_neg h]

/-- **THE PARTNER IS UNIQUE.**  A third slot with the same support gives
three identical supports, and the landed triple kill refuses that. -/
theorem pairedPartner_eq_of (data : SharedPrivateData crux)
    {slot other : Fin data.basisCount} (hne : other ≠ slot)
    (hsame : datumTightSupport data.tightDir (data.basisLabel other)
      = datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.pairedPartner slot = other := by
  have hex : ∃ third, third ≠ slot
      ∧ datumTightSupport data.tightDir (data.basisLabel third)
        = datumTightSupport data.tightDir (data.basisLabel slot) := ⟨other, hne, hsame⟩
  obtain ⟨hpne, hpsame⟩ := data.pairedPartner_spec hex
  by_contra hcontra
  exact data.false_of_triple_identical_support (Ne.symm hne)
    (Ne.symm hpne) (fun heq => hcontra heq.symm) hsame hpsame

/-- The partnered predicate, read off the partner function. -/
theorem pairedPartner_ne_iff (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) :
    data.pairedPartner slot ≠ slot
      ↔ ∃ other, other ≠ slot
        ∧ datumTightSupport data.tightDir (data.basisLabel other)
          = datumTightSupport data.tightDir (data.basisLabel slot) := by
  constructor
  · intro hne
    by_contra hnone
    exact hne (data.pairedPartner_eq_self hnone)
  · intro h
    exact (data.pairedPartner_spec h).1

/-- The support of the partner. -/
theorem pairedPartner_support (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} (hne : data.pairedPartner slot ≠ slot) :
    datumTightSupport data.tightDir (data.basisLabel (data.pairedPartner slot))
      = datumTightSupport data.tightDir (data.basisLabel slot) :=
  (data.pairedPartner_spec ((data.pairedPartner_ne_iff slot).mp hne)).2

/-- **THE PARTNER INVOLUTION.** -/
theorem pairedPartner_involution (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} (hne : data.pairedPartner slot ≠ slot) :
    data.pairedPartner (data.pairedPartner slot) = slot :=
  data.pairedPartner_eq_of (Ne.symm hne) (data.pairedPartner_support hne).symm

/-- The private slot has no partner: a partner would give the pin atom a
second carrier. -/
theorem pairedPartner_privateSlot (data : SharedPrivateData crux) :
    data.pairedPartner data.privateSlot = data.privateSlot := by
  by_contra hne
  have hsupp := data.pairedPartner_support hne
  have hpinMem : data.pinAtom
      ∈ datumTightSupport data.tightDir (data.basisLabel data.privateSlot) :=
    mem_datumTightSupport.mpr data.hpinNe
  have hpinPartner : data.pinAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel (data.pairedPartner data.privateSlot)) := by
    rw [hsupp]; exact hpinMem
  have hsub : ({data.pairedPartner data.privateSlot, data.privateSlot}
      : Finset (Fin data.basisCount))
      ⊆ Finset.univ.filter fun columnIndex =>
        data.pinAtom ∈ datumTightSupport data.tightDir
          (data.basisLabel columnIndex) := by
    intro slot hslot
    simp only [Finset.mem_insert, Finset.mem_singleton] at hslot
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hslot with rfl | rfl
    · exact hpinPartner
    · exact hpinMem
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton] at hcard
  have hone := data.hmultOne
  rw [basisSupportMultiplicity] at hone
  omega

/-- A partner of a slot is never the private slot. -/
theorem pairedPartner_ne_privateSlot (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} (hne : data.pairedPartner slot ≠ slot) :
    data.pairedPartner slot ≠ data.privateSlot := by
  intro heq
  have hinv := data.pairedPartner_involution hne
  rw [heq, data.pairedPartner_privateSlot] at hinv
  exact hne (heq.trans hinv)

/-! ## Layer 2 — the fold matrices -/

variable (data : SharedPrivateData crux)

/-- The recombination determinant of a pair: the corner energy of
`(-t, 1)` in min-max coordinates. -/
noncomputable def foldDelta (tau : ℝ) (slot : Fin data.basisCount) : ℝ :=
  if slot < data.pairedPartner slot then
    data.gram (data.pairedPartner slot) (data.pairedPartner slot)
      - 2 * tau * data.gram slot (data.pairedPartner slot)
      + tau ^ 2 * data.gram slot slot
  else
    data.gram slot slot
      - 2 * tau * data.gram (data.pairedPartner slot) slot
      + tau ^ 2 * data.gram (data.pairedPartner slot) (data.pairedPartner slot)

/-- The determinant agrees across the pair. -/
theorem foldDelta_pair (tau : ℝ) {slot : Fin data.basisCount}
    (hne : data.pairedPartner slot ≠ slot)
    (hlt : slot < data.pairedPartner slot) :
    data.foldDelta tau (data.pairedPartner slot) = data.foldDelta tau slot := by
  have hinv := data.pairedPartner_involution hne
  rw [foldDelta, foldDelta, if_pos hlt, if_neg (by rw [hinv]; exact not_lt.mpr hlt.le),
    hinv]

/-- **THE DETERMINANT IS POSITIVE** at a partnered slot. -/
theorem foldDelta_pos (tau : ℝ) {slot : Fin data.basisCount}
    (hne : data.pairedPartner slot ≠ slot) :
    0 < data.foldDelta tau slot := by
  rcases lt_or_gt_of_ne (Ne.symm hne) with hlt | hgt
  · rw [foldDelta, if_pos hlt]
    have hpos := data.gram_pair_energy_pos (slotA := slot)
      (slotB := data.pairedPartner slot) (Ne.symm hne)
      (coeffA := -tau) (coeffB := 1) (Or.inr one_ne_zero)
    nlinarith [hpos]
  · rw [foldDelta, if_neg (not_lt.mpr hgt.le)]
    have hpos := data.gram_pair_energy_pos (slotA := data.pairedPartner slot)
      (slotB := slot) hne (coeffA := -tau) (coeffB := 1) (Or.inr one_ne_zero)
    nlinarith [hpos]

/-- **THE FOLD MATRIX.**  The identity away from the pairs; on a pair
`(a, b)` with `a < b` the column `a` becomes `e_a + t e_b` and the
column `b` becomes `(g_ab - t g_aa) e_a + (g_bb - t g_ab) e_b`. -/
noncomputable def foldMatrix (tau : ℝ) :
    Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
  fun rowSlot colSlot =>
    if data.pairedPartner colSlot = colSlot then
      (if rowSlot = colSlot then 1 else 0)
    else if colSlot < data.pairedPartner colSlot then
      (if rowSlot = colSlot then 1
       else if rowSlot = data.pairedPartner colSlot then tau else 0)
    else
      (if rowSlot = data.pairedPartner colSlot then
        data.gram (data.pairedPartner colSlot) colSlot
          - tau * data.gram (data.pairedPartner colSlot) (data.pairedPartner colSlot)
       else if rowSlot = colSlot then
        data.gram colSlot colSlot
          - tau * data.gram (data.pairedPartner colSlot) colSlot
       else 0)

/-- **THE FOLD INVERSE.**  The rows of the blockwise inverse. -/
noncomputable def foldInverse (tau : ℝ) :
    Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
  fun rowSlot colSlot =>
    if data.pairedPartner rowSlot = rowSlot then
      (if colSlot = rowSlot then 1 else 0)
    else if rowSlot < data.pairedPartner rowSlot then
      (if colSlot = rowSlot then
        (data.gram (data.pairedPartner rowSlot) (data.pairedPartner rowSlot)
          - tau * data.gram rowSlot (data.pairedPartner rowSlot))
          / data.foldDelta tau rowSlot
       else if colSlot = data.pairedPartner rowSlot then
        -(data.gram rowSlot (data.pairedPartner rowSlot)
          - tau * data.gram rowSlot rowSlot) / data.foldDelta tau rowSlot
       else 0)
    else
      (if colSlot = data.pairedPartner rowSlot then
        -tau / data.foldDelta tau rowSlot
       else if colSlot = rowSlot then 1 / data.foldDelta tau rowSlot
       else 0)

/-- The fold matrix vanishes away from the slot and its partner. -/
theorem foldMatrix_eq_zero (tau : ℝ) {rowSlot colSlot : Fin data.basisCount}
    (hrow : rowSlot ≠ colSlot) (hpartner : rowSlot ≠ data.pairedPartner colSlot) :
    data.foldMatrix tau rowSlot colSlot = 0 := by
  rw [foldMatrix]
  by_cases hself : data.pairedPartner colSlot = colSlot
  · rw [if_pos hself, if_neg hrow]
  · rw [if_neg hself]
    by_cases hlt : colSlot < data.pairedPartner colSlot
    · rw [if_pos hlt, if_neg hrow, if_neg hpartner]
    · rw [if_neg hlt, if_neg hpartner, if_neg hrow]

/-- The fold inverse vanishes away from the slot and its partner. -/
theorem foldInverse_eq_zero (tau : ℝ) {rowSlot colSlot : Fin data.basisCount}
    (hcol : colSlot ≠ rowSlot) (hpartner : colSlot ≠ data.pairedPartner rowSlot) :
    data.foldInverse tau rowSlot colSlot = 0 := by
  rw [foldInverse]
  by_cases hself : data.pairedPartner rowSlot = rowSlot
  · rw [if_pos hself, if_neg hcol]
  · rw [if_neg hself]
    by_cases hlt : rowSlot < data.pairedPartner rowSlot
    · rw [if_pos hlt, if_neg hcol, if_neg hpartner]
    · rw [if_neg hlt, if_neg hpartner, if_neg hcol]

/-- The unpartnered column of the fold matrix is the axis. -/
theorem foldMatrix_col_self (tau : ℝ) {colSlot : Fin data.basisCount}
    (hself : data.pairedPartner colSlot = colSlot) (rowSlot : Fin data.basisCount) :
    data.foldMatrix tau rowSlot colSlot = if rowSlot = colSlot then 1 else 0 := by
  rw [foldMatrix, if_pos hself]

/-- The unpartnered row of the fold inverse is the axis. -/
theorem foldInverse_row_self (tau : ℝ) {rowSlot : Fin data.basisCount}
    (hself : data.pairedPartner rowSlot = rowSlot) (colSlot : Fin data.basisCount) :
    data.foldInverse tau rowSlot colSlot = if colSlot = rowSlot then 1 else 0 := by
  rw [foldInverse, if_pos hself]

/-- A row sum against the fold matrix collapses to the slot and its
partner. -/
theorem sum_foldMatrix_mul (tau : ℝ) (rowSlot : Fin data.basisCount)
    (value : Fin data.basisCount → ℝ) :
    ∑ colSlot, data.foldMatrix tau rowSlot colSlot * value colSlot
      = if data.pairedPartner rowSlot = rowSlot then
          data.foldMatrix tau rowSlot rowSlot * value rowSlot
        else data.foldMatrix tau rowSlot rowSlot * value rowSlot
          + data.foldMatrix tau rowSlot (data.pairedPartner rowSlot)
            * value (data.pairedPartner rowSlot) := by
  classical
  have hzero : ∀ colSlot, colSlot ≠ rowSlot →
      colSlot ≠ data.pairedPartner rowSlot →
      data.foldMatrix tau rowSlot colSlot * value colSlot = 0 := by
    intro colSlot hone htwo
    have hentry : data.foldMatrix tau rowSlot colSlot = 0 := by
      refine data.foldMatrix_eq_zero tau (Ne.symm hone) ?_
      intro heq
      by_cases hself : data.pairedPartner colSlot = colSlot
      · exact hone (by rw [← hself, ← heq])
      · exact htwo (by rw [← data.pairedPartner_involution hself, ← heq])
    rw [hentry, zero_mul]
  by_cases hself : data.pairedPartner rowSlot = rowSlot
  · rw [if_pos hself]
    refine Finset.sum_eq_single rowSlot ?_ ?_
    · intro colSlot _ hne
      exact hzero colSlot hne (by rw [hself]; exact hne)
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [if_neg hself]
    have hsubset : ({rowSlot, data.pairedPartner rowSlot}
        : Finset (Fin data.basisCount)) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsubset (fun colSlot _ hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hzero colSlot hnot.1 hnot.2)]
    rw [Finset.sum_pair (Ne.symm hself)]

/-- A column sum against the fold inverse collapses to the slot and its
partner. -/
theorem sum_foldInverse_mul (tau : ℝ) (rowSlot : Fin data.basisCount)
    (value : Fin data.basisCount → ℝ) :
    ∑ colSlot, data.foldInverse tau rowSlot colSlot * value colSlot
      = if data.pairedPartner rowSlot = rowSlot then
          data.foldInverse tau rowSlot rowSlot * value rowSlot
        else data.foldInverse tau rowSlot rowSlot * value rowSlot
          + data.foldInverse tau rowSlot (data.pairedPartner rowSlot)
            * value (data.pairedPartner rowSlot) := by
  classical
  have hzero : ∀ colSlot, colSlot ≠ rowSlot →
      colSlot ≠ data.pairedPartner rowSlot →
      data.foldInverse tau rowSlot colSlot * value colSlot = 0 :=
    fun colSlot hone htwo => by
      rw [data.foldInverse_eq_zero tau hone htwo, zero_mul]
  by_cases hself : data.pairedPartner rowSlot = rowSlot
  · rw [if_pos hself]
    refine Finset.sum_eq_single rowSlot ?_ ?_
    · intro colSlot _ hne
      exact hzero colSlot hne (by rw [hself]; exact hne)
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [if_neg hself]
    rw [← Finset.sum_subset (Finset.subset_univ
      ({rowSlot, data.pairedPartner rowSlot} : Finset (Fin data.basisCount)))
      (fun colSlot _ hnot => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        exact hzero colSlot hnot.1 hnot.2)]
    rw [Finset.sum_pair (Ne.symm hself)]

/-- The minimum column of a pair. -/
theorem foldMatrix_col_min (tau : ℝ) {colSlot : Fin data.basisCount}
    (hne : data.pairedPartner colSlot ≠ colSlot)
    (hlt : colSlot < data.pairedPartner colSlot) (rowSlot : Fin data.basisCount) :
    data.foldMatrix tau rowSlot colSlot
      = if rowSlot = colSlot then 1
        else if rowSlot = data.pairedPartner colSlot then tau else 0 := by
  rw [foldMatrix, if_neg hne, if_pos hlt]

/-- The maximum column of a pair. -/
theorem foldMatrix_col_max (tau : ℝ) {colSlot : Fin data.basisCount}
    (hne : data.pairedPartner colSlot ≠ colSlot)
    (hgt : data.pairedPartner colSlot < colSlot) (rowSlot : Fin data.basisCount) :
    data.foldMatrix tau rowSlot colSlot
      = if rowSlot = data.pairedPartner colSlot then
          data.gram (data.pairedPartner colSlot) colSlot
            - tau * data.gram (data.pairedPartner colSlot)
              (data.pairedPartner colSlot)
        else if rowSlot = colSlot then
          data.gram colSlot colSlot
            - tau * data.gram (data.pairedPartner colSlot) colSlot
        else 0 := by
  rw [foldMatrix, if_neg hne, if_neg (not_lt.mpr hgt.le)]

/-- The minimum row of the fold inverse. -/
theorem foldInverse_row_min (tau : ℝ) {rowSlot : Fin data.basisCount}
    (hne : data.pairedPartner rowSlot ≠ rowSlot)
    (hlt : rowSlot < data.pairedPartner rowSlot) (colSlot : Fin data.basisCount) :
    data.foldInverse tau rowSlot colSlot
      = if colSlot = rowSlot then
          (data.gram (data.pairedPartner rowSlot) (data.pairedPartner rowSlot)
            - tau * data.gram rowSlot (data.pairedPartner rowSlot))
            / data.foldDelta tau rowSlot
        else if colSlot = data.pairedPartner rowSlot then
          -(data.gram rowSlot (data.pairedPartner rowSlot)
            - tau * data.gram rowSlot rowSlot) / data.foldDelta tau rowSlot
        else 0 := by
  rw [foldInverse, if_neg hne, if_pos hlt]

/-- The maximum row of the fold inverse, with the determinant read at the
minimum slot. -/
theorem foldInverse_row_max (tau : ℝ) {rowSlot : Fin data.basisCount}
    (hne : data.pairedPartner rowSlot ≠ rowSlot)
    (hgt : data.pairedPartner rowSlot < rowSlot) (colSlot : Fin data.basisCount) :
    data.foldInverse tau rowSlot colSlot
      = if colSlot = data.pairedPartner rowSlot then
          -tau / data.foldDelta tau (data.pairedPartner rowSlot)
        else if colSlot = rowSlot then
          1 / data.foldDelta tau (data.pairedPartner rowSlot)
        else 0 := by
  have hpp : data.pairedPartner (data.pairedPartner rowSlot) = rowSlot :=
    data.pairedPartner_involution hne
  have hdelta : data.foldDelta tau rowSlot
      = data.foldDelta tau (data.pairedPartner rowSlot) := by
    have hstep := data.foldDelta_pair tau
      (slot := data.pairedPartner rowSlot)
      (by rw [hpp]; exact Ne.symm hne) (by rw [hpp]; exact hgt)
    rw [hpp] at hstep
    exact hstep
  rw [foldInverse, if_neg hne, if_neg (not_lt.mpr hgt.le), hdelta]

/-- The determinant of the minimum slot, unfolded. -/
theorem foldDelta_min (tau : ℝ) {slot : Fin data.basisCount}
    (hlt : slot < data.pairedPartner slot) :
    data.foldDelta tau slot
      = data.gram (data.pairedPartner slot) (data.pairedPartner slot)
        - 2 * tau * data.gram slot (data.pairedPartner slot)
        + tau ^ 2 * data.gram slot slot := by
  rw [foldDelta, if_pos hlt]

set_option maxHeartbeats 6400000 in
/-- **THE INVERSE LAW.**  The fold matrix and the fold inverse multiply
to the identity. -/
theorem foldMatrix_mul_foldInverse (tau : ℝ) :
    data.foldMatrix tau * data.foldInverse tau = 1 := by
  classical
  ext rowSlot colSlot
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hzero : ∀ midSlot, midSlot ≠ rowSlot →
      midSlot ≠ data.pairedPartner rowSlot →
      data.foldMatrix tau rowSlot midSlot
        * data.foldInverse tau midSlot colSlot = 0 := by
    intro midSlot hone htwo
    have hentry : data.foldMatrix tau rowSlot midSlot = 0 := by
      refine data.foldMatrix_eq_zero tau (Ne.symm hone) ?_
      intro heq
      by_cases hmid : data.pairedPartner midSlot = midSlot
      · exact hone (by rw [← hmid, ← heq])
      · exact htwo (by rw [← data.pairedPartner_involution hmid, ← heq])
    rw [hentry, zero_mul]
  by_cases hself : data.pairedPartner rowSlot = rowSlot
  · have hsum : ∑ midSlot, data.foldMatrix tau rowSlot midSlot
        * data.foldInverse tau midSlot colSlot
        = data.foldMatrix tau rowSlot rowSlot
          * data.foldInverse tau rowSlot colSlot := by
      refine Finset.sum_eq_single rowSlot ?_ ?_
      · intro midSlot _ hne
        exact hzero midSlot hne (by rw [hself]; exact hne)
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    rw [hsum, data.foldMatrix_col_self tau hself, if_pos rfl, one_mul,
      data.foldInverse_row_self tau hself]
    by_cases heq : colSlot = rowSlot
    · rw [if_pos heq, if_pos heq.symm]
    · rw [if_neg heq, if_neg fun h => heq h.symm]
  · have hsum : ∑ midSlot, data.foldMatrix tau rowSlot midSlot
        * data.foldInverse tau midSlot colSlot
        = data.foldMatrix tau rowSlot rowSlot
            * data.foldInverse tau rowSlot colSlot
          + data.foldMatrix tau rowSlot (data.pairedPartner rowSlot)
            * data.foldInverse tau (data.pairedPartner rowSlot) colSlot := by
      rw [← Finset.sum_subset (Finset.subset_univ
        ({rowSlot, data.pairedPartner rowSlot} : Finset (Fin data.basisCount)))
        (fun midSlot _ hnot => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          exact hzero midSlot hnot.1 hnot.2)]
      rw [Finset.sum_pair (Ne.symm hself)]
    rw [hsum]
    have hinv : data.pairedPartner (data.pairedPartner rowSlot) = rowSlot :=
      data.pairedPartner_involution hself
    have hpne : data.pairedPartner (data.pairedPartner rowSlot)
        ≠ data.pairedPartner rowSlot := by
      rw [hinv]; exact fun h => hself h.symm
    rcases lt_or_gt_of_ne (Ne.symm hself) with hlt | hgt
    · -- the row slot is the minimum of its pair
      have hplt : data.pairedPartner (data.pairedPartner rowSlot)
          < data.pairedPartner rowSlot := by
        rw [hinv]; exact hlt
      have hdne : data.foldDelta tau rowSlot ≠ 0 :=
        ne_of_gt (data.foldDelta_pos tau hself)
      have hRaa : data.foldMatrix tau rowSlot rowSlot = 1 := by
        rw [data.foldMatrix_col_min tau hself hlt rowSlot, if_pos rfl]
      have hRab : data.foldMatrix tau rowSlot (data.pairedPartner rowSlot)
          = data.gram rowSlot (data.pairedPartner rowSlot)
            - tau * data.gram rowSlot rowSlot := by
        have hcol := data.foldMatrix_col_max tau hpne hplt rowSlot
        rw [hinv] at hcol
        rw [hcol, if_pos rfl]
      have hIb := data.foldInverse_row_max tau
        (rowSlot := data.pairedPartner rowSlot) hpne hplt colSlot
      rw [hinv] at hIb
      have hIa := data.foldInverse_row_min tau hself hlt colSlot
      rw [hRaa, hRab, hIa, hIb, one_mul]
      by_cases hcolRow : colSlot = rowSlot
      · rw [if_pos hcolRow, if_pos hcolRow, if_pos hcolRow.symm]
        field_simp [hdne]
        rw [data.foldDelta_min tau hlt]
        ring
      · by_cases hcolPartner : colSlot = data.pairedPartner rowSlot
        · rw [if_neg hcolRow, if_pos hcolPartner, if_neg hcolRow,
            if_pos hcolPartner,
            if_neg (fun h : rowSlot = colSlot =>
              hself ((h.trans hcolPartner).symm))]
          field_simp
          ring
        · rw [if_neg hcolRow, if_neg hcolPartner, if_neg hcolRow,
            if_neg hcolPartner, if_neg (fun h => hcolRow h.symm)]
          ring
    · -- the row slot is the maximum of its pair
      have hplt : data.pairedPartner rowSlot
          < data.pairedPartner (data.pairedPartner rowSlot) := by
        rw [hinv]; exact hgt
      have hdne : data.foldDelta tau (data.pairedPartner rowSlot) ≠ 0 :=
        ne_of_gt (data.foldDelta_pos tau hpne)
      have hRaa : data.foldMatrix tau rowSlot rowSlot
          = data.gram rowSlot rowSlot
            - tau * data.gram (data.pairedPartner rowSlot) rowSlot := by
        rw [data.foldMatrix_col_max tau hself hgt rowSlot,
          if_neg (fun h => hself h.symm), if_pos rfl]
      have hRab : data.foldMatrix tau rowSlot (data.pairedPartner rowSlot)
          = tau := by
        have hcol := data.foldMatrix_col_min tau hpne hplt rowSlot
        rw [hinv] at hcol
        rw [hcol, if_neg (fun h => hself h.symm), if_pos rfl]
      have hIa := data.foldInverse_row_max tau hself hgt colSlot
      have hIb := data.foldInverse_row_min tau
        (rowSlot := data.pairedPartner rowSlot) hpne hplt colSlot
      rw [hinv] at hIb
      have hdeltaEq : data.foldDelta tau (data.pairedPartner rowSlot)
          = data.gram rowSlot rowSlot
            - 2 * tau * data.gram (data.pairedPartner rowSlot) rowSlot
            + tau ^ 2 * data.gram (data.pairedPartner rowSlot)
              (data.pairedPartner rowSlot) := by
        have hstep := data.foldDelta_min tau (slot := data.pairedPartner rowSlot)
          hplt
        rw [hinv] at hstep
        exact hstep
      rw [hRaa, hRab, hIa, hIb]
      by_cases hcolRow : colSlot = rowSlot
      · rw [if_neg (fun h : colSlot = data.pairedPartner rowSlot =>
            hself ((hcolRow.symm.trans h).symm)),
          if_pos hcolRow,
          if_neg (fun h : colSlot = data.pairedPartner rowSlot =>
            hself ((hcolRow.symm.trans h).symm)),
          if_pos hcolRow,
          if_pos hcolRow.symm]
        field_simp [hdne]
        rw [hdeltaEq]
        ring
      · by_cases hcolPartner : colSlot = data.pairedPartner rowSlot
        · rw [if_pos hcolPartner, if_pos hcolPartner,
            if_neg (fun h : rowSlot = colSlot =>
              hself ((h.trans hcolPartner).symm))]
          field_simp
          ring
        · rw [if_neg hcolPartner, if_neg hcolRow, if_neg hcolPartner,
            if_neg hcolRow, if_neg (fun h => hcolRow h.symm)]
          ring

/-- The converse inverse law. -/
theorem foldInverse_mul_foldMatrix (tau : ℝ) :
    data.foldInverse tau * data.foldMatrix tau = 1 :=
  mul_eq_one_comm.mp (data.foldMatrix_mul_foldInverse tau)

/-! ## Layer 3 — the folded Gram core -/

/-- The support of the partner, in the general form. -/
theorem pairedPartner_support_eq (slot : Fin data.basisCount) :
    datumTightSupport data.tightDir (data.basisLabel (data.pairedPartner slot))
      = datumTightSupport data.tightDir (data.basisLabel slot) := by
  by_cases h : data.pairedPartner slot = slot
  · rw [h]
  · exact data.pairedPartner_support h

/-- The folded Gram core. -/
noncomputable def foldGram (tau : ℝ) :
    Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
  data.foldInverse tau * data.gram * (data.foldInverse tau)ᵀ

/-- The folded core is symmetric. -/
theorem foldGram_transpose (tau : ℝ) :
    (data.foldGram tau)ᵀ = data.foldGram tau := by
  rw [foldGram, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, data.hsymmH, Matrix.mul_assoc]

/-- The entry of the folded core as a probe energy of the core. -/
theorem foldGram_apply_eq_dot (tau : ℝ) (rowSlot colSlot : Fin data.basisCount) :
    data.foldGram tau rowSlot colSlot
      = (fun slot => data.foldInverse tau rowSlot slot)
        ⬝ᵥ (data.gram *ᵥ fun slot => data.foldInverse tau colSlot slot) := by
  rw [foldGram]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec]
  calc ∑ midSlot, (∑ innerSlot, data.foldInverse tau rowSlot innerSlot
          * data.gram innerSlot midSlot) * data.foldInverse tau colSlot midSlot
      = ∑ midSlot, ∑ innerSlot, data.foldInverse tau rowSlot innerSlot
          * data.gram innerSlot midSlot * data.foldInverse tau colSlot midSlot := by
        refine Finset.sum_congr rfl fun midSlot _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ innerSlot, ∑ midSlot, data.foldInverse tau rowSlot innerSlot
          * data.gram innerSlot midSlot * data.foldInverse tau colSlot midSlot :=
        Finset.sum_comm
    _ = ∑ innerSlot, data.foldInverse tau rowSlot innerSlot
          * ∑ midSlot, data.gram innerSlot midSlot
            * data.foldInverse tau colSlot midSlot := by
        refine Finset.sum_congr rfl fun innerSlot _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun midSlot _ => by ring

/-- The inverse row of an unpartnered slot is nonzero. -/
theorem foldInverse_row_ne_zero (tau : ℝ) (rowSlot : Fin data.basisCount) :
    (fun slot => data.foldInverse tau rowSlot slot) ≠ 0 := by
  intro hzero
  by_cases hself : data.pairedPartner rowSlot = rowSlot
  · have := congrFun hzero rowSlot
    rw [data.foldInverse_row_self tau hself, if_pos rfl] at this
    exact one_ne_zero this
  · have hdne : data.foldDelta tau rowSlot ≠ 0 :=
      ne_of_gt (data.foldDelta_pos tau hself)
    rcases lt_or_gt_of_ne (Ne.symm hself) with hlt | hgt
    · have hone := congrFun hzero rowSlot
      have htwo := congrFun hzero (data.pairedPartner rowSlot)
      rw [data.foldInverse_row_min tau hself hlt rowSlot, if_pos rfl] at hone
      rw [data.foldInverse_row_min tau hself hlt (data.pairedPartner rowSlot),
        if_neg hself, if_pos rfl] at htwo
      have hnumOne : data.gram (data.pairedPartner rowSlot)
          (data.pairedPartner rowSlot)
          - tau * data.gram rowSlot (data.pairedPartner rowSlot) = 0 := by
        have := div_eq_zero_iff.mp hone
        exact this.resolve_right hdne
      have hnumTwo : data.gram rowSlot (data.pairedPartner rowSlot)
          - tau * data.gram rowSlot rowSlot = 0 := by
        have hneg := div_eq_zero_iff.mp htwo
        have := hneg.resolve_right hdne
        linarith [this]
      have hdeltaZero : data.foldDelta tau rowSlot = 0 := by
        rw [data.foldDelta_min tau hlt]
        linear_combination hnumOne - tau * hnumTwo
      exact hdne hdeltaZero
    · have hpne : data.pairedPartner (data.pairedPartner rowSlot)
          ≠ data.pairedPartner rowSlot := by
        rw [data.pairedPartner_involution hself]
        exact fun h => hself h.symm
      have hdpne : data.foldDelta tau (data.pairedPartner rowSlot) ≠ 0 :=
        ne_of_gt (data.foldDelta_pos tau hpne)
      have hone := congrFun hzero rowSlot
      rw [data.foldInverse_row_max tau hself hgt rowSlot,
        if_neg (fun h => hself h.symm), if_pos rfl] at hone
      exact hdpne (by
        have := div_eq_zero_iff.mp hone
        rcases this with h | h
        · exact absurd h one_ne_zero
        · exact h)

/-- **THE FOLDED DIAGONAL IS POSITIVE.** -/
theorem foldGram_diag_pos (tau : ℝ) (slot : Fin data.basisCount) :
    0 < data.foldGram tau slot slot := by
  rw [data.foldGram_apply_eq_dot tau slot slot]
  exact data.gram_quadratic_pos (data.foldInverse_row_ne_zero tau slot)

/-- The kill of a cross entry between different classes. -/
theorem gram_eq_zero_of_class_ne
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA))
    {slotA slotB : Fin data.basisCount} (hne : slotA ≠ slotB)
    (hclass : datumTightSupport data.tightDir (data.basisLabel slotB)
      ≠ datumTightSupport data.tightDir (data.basisLabel slotA)) :
    data.gram slotA slotB = 0 := by
  by_contra hcontra
  exact hclass (hpaired slotA slotB hne hcontra)

/-- The two-point read of a dot product. -/
theorem twoPoint_dot_read {count : ℕ} {slotA slotB : Fin count} (hab : slotA ≠ slotB)
    (coeffA coeffB : ℝ) (vec : Fin count → ℝ) :
    (fun slot => (if slot = slotA then coeffA else 0)
        + (if slot = slotB then coeffB else 0)) ⬝ᵥ vec
      = coeffA * vec slotA + coeffB * vec slotB := by
  classical
  show (∑ slot, ((if slot = slotA then coeffA else 0)
      + (if slot = slotB then coeffB else 0)) * vec slot)
    = coeffA * vec slotA + coeffB * vec slotB
  rw [← Finset.sum_subset
    (Finset.subset_univ ({slotA, slotB} : Finset (Fin count)))
    (fun slot _ hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      rw [if_neg hnot.1, if_neg hnot.2, add_zero, zero_mul]),
    Finset.sum_pair hab, if_pos rfl, if_neg hab, if_neg (Ne.symm hab), if_pos rfl]
  ring

set_option maxHeartbeats 6400000 in
/-- **THE PAIR CORNER FOLDS TO ZERO.**  The two inverse rows of a pair
are conjugate directions of the corner, thus the folded corner entry
vanishes at every parameter. -/
theorem foldGram_pair_min_eq_zero (tau : ℝ) {slot : Fin data.basisCount}
    (hpair : data.pairedPartner slot ≠ slot)
    (hlt : slot < data.pairedPartner slot) :
    data.foldGram tau slot (data.pairedPartner slot) = 0 := by
  classical
  have hinv : data.pairedPartner (data.pairedPartner slot) = slot :=
    data.pairedPartner_involution hpair
  have hpne : data.pairedPartner (data.pairedPartner slot)
      ≠ data.pairedPartner slot := by
    rw [hinv]; exact fun h => hpair h.symm
  have hplt : data.pairedPartner (data.pairedPartner slot)
      < data.pairedPartner slot := by
    rw [hinv]; exact hlt
  have hdne : data.foldDelta tau slot ≠ 0 :=
    ne_of_gt (data.foldDelta_pos tau hpair)
  rw [data.foldGram_apply_eq_dot tau slot (data.pairedPartner slot)]
  have hvecA : (fun colSlot => data.foldInverse tau slot colSlot)
      = fun colSlot =>
        (if colSlot = slot then
          (data.gram (data.pairedPartner slot) (data.pairedPartner slot)
            - tau * data.gram slot (data.pairedPartner slot))
            / data.foldDelta tau slot else 0)
          + (if colSlot = data.pairedPartner slot then
            -(data.gram slot (data.pairedPartner slot)
              - tau * data.gram slot slot) / data.foldDelta tau slot else 0) := by
    funext colSlot
    rw [data.foldInverse_row_min tau hpair hlt colSlot]
    by_cases hone : colSlot = slot
    · simp only [if_pos hone,
        if_neg (show colSlot ≠ data.pairedPartner slot from
          fun h => hpair ((hone.symm.trans h).symm)), add_zero]
    · by_cases htwo : colSlot = data.pairedPartner slot
      · simp only [if_neg hone, if_pos htwo, zero_add]
      · simp only [if_neg hone, if_neg htwo, add_zero]
  have hvecB : (fun colSlot => data.foldInverse tau (data.pairedPartner slot)
        colSlot)
      = fun colSlot =>
        (if colSlot = slot then -tau / data.foldDelta tau slot else 0)
          + (if colSlot = data.pairedPartner slot then
            1 / data.foldDelta tau slot else 0) := by
    funext colSlot
    have h := data.foldInverse_row_max tau hpne hplt colSlot
    rw [hinv] at h
    rw [h]
    by_cases hone : colSlot = slot
    · simp only [if_pos hone,
        if_neg (show colSlot ≠ data.pairedPartner slot from
          fun heq => hpair ((hone.symm.trans heq).symm)), add_zero]
    · by_cases htwo : colSlot = data.pairedPartner slot
      · simp only [if_neg hone, if_pos htwo, zero_add]
      · simp only [if_neg hone, if_neg htwo, add_zero]
  rw [hvecA, hvecB, twoPoint_dot_read (Ne.symm hpair)]
  rw [data.twoPoint_row_read (Ne.symm hpair) _ _ slot,
    data.twoPoint_row_read (Ne.symm hpair) _ _ (data.pairedPartner slot),
    data.gram_entry_symm (data.pairedPartner slot) slot]
  field_simp
  ring

/-- **THE FOLDED CORE IS DIAGONAL** on the support-paired lattice. -/
theorem foldGram_offDiag_eq_zero (tau : ℝ)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA))
    {rowSlot colSlot : Fin data.basisCount} (hne : rowSlot ≠ colSlot) :
    data.foldGram tau rowSlot colSlot = 0 := by
  classical
  by_cases hpartner : colSlot = data.pairedPartner rowSlot
  · -- the pair corner
    have hpair : data.pairedPartner rowSlot ≠ rowSlot := by
      rw [← hpartner]; exact Ne.symm hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [hpartner]
      exact data.foldGram_pair_min_eq_zero tau hpair
        (by rw [← hpartner]; exact hlt)
    · have hinv : data.pairedPartner colSlot = rowSlot := by
        rw [hpartner]; exact data.pairedPartner_involution hpair
      have hcolPair : data.pairedPartner colSlot ≠ colSlot := by
        rw [hinv]; exact hne
      have hentry : data.foldGram tau colSlot (data.pairedPartner colSlot)
          = 0 :=
        data.foldGram_pair_min_eq_zero tau hcolPair
          (by rw [hinv]; exact hgt)
      rw [hinv] at hentry
      have hsymm := congrFun (congrFun (data.foldGram_transpose tau) colSlot)
        rowSlot
      rw [Matrix.transpose_apply] at hsymm
      exact hsymm.trans hentry
  · -- different classes: every surviving product carries a dead entry
    have hkill : ∀ midA midB : Fin data.basisCount,
        (midA = rowSlot ∨ midA = data.pairedPartner rowSlot) →
        (midB = colSlot ∨ midB = data.pairedPartner colSlot) →
        data.gram midA midB = 0 := by
      intro midA midB hA hB
      have hsuppA : datumTightSupport data.tightDir (data.basisLabel midA)
          = datumTightSupport data.tightDir (data.basisLabel rowSlot) := by
        rcases hA with rfl | rfl
        · rfl
        · exact data.pairedPartner_support_eq rowSlot
      have hsuppB : datumTightSupport data.tightDir (data.basisLabel midB)
          = datumTightSupport data.tightDir (data.basisLabel colSlot) := by
        rcases hB with rfl | rfl
        · rfl
        · exact data.pairedPartner_support_eq colSlot
      have hclassNe : datumTightSupport data.tightDir (data.basisLabel colSlot)
          ≠ datumTightSupport data.tightDir (data.basisLabel rowSlot) := by
        intro hsame
        exact hpartner (data.pairedPartner_eq_of (Ne.symm hne) hsame).symm
      have hmidNe : midA ≠ midB := by
        intro heq
        exact hclassNe (by rw [← hsuppB, ← heq, hsuppA])
      exact data.gram_eq_zero_of_class_ne hpaired hmidNe
        (by rw [hsuppB, hsuppA]; exact hclassNe)
    rw [data.foldGram_apply_eq_dot tau rowSlot colSlot]
    rw [dotProduct]
    refine Finset.sum_eq_zero fun midA _ => ?_
    by_cases hAmem : midA = rowSlot ∨ midA = data.pairedPartner rowSlot
    · have hzero : (data.gram *ᵥ fun slot =>
          data.foldInverse tau colSlot slot) midA = 0 := by
        show (∑ midB, data.gram midA midB
          * data.foldInverse tau colSlot midB) = 0
        refine Finset.sum_eq_zero fun midB _ => ?_
        by_cases hBmem : midB = colSlot ∨ midB = data.pairedPartner colSlot
        · rw [hkill midA midB hAmem hBmem, zero_mul]
        · push Not at hBmem
          rw [data.foldInverse_eq_zero tau hBmem.1 hBmem.2, mul_zero]
      rw [hzero, mul_zero]
    · push Not at hAmem
      rw [data.foldInverse_eq_zero tau hAmem.1 hAmem.2, zero_mul]

/-! ## Layer 4 — the folded columns and the good parameter -/

/-- The folded basis columns. -/
noncomputable def foldColumns (tau : ℝ) :
    Matrix (Fin 6) (Fin data.basisCount) ℝ :=
  tightBasisColumns data.tightDir data.basisLabel * data.foldMatrix tau

/-- The unpartnered folded column is the old column. -/
theorem foldColumns_self (tau : ℝ) {colSlot : Fin data.basisCount}
    (hself : data.pairedPartner colSlot = colSlot) (atomIndex : Fin 6) :
    data.foldColumns tau atomIndex colSlot
      = data.tightDir (data.basisLabel colSlot) atomIndex := by
  rw [foldColumns, Matrix.mul_apply]
  refine (Finset.sum_eq_single colSlot ?_ ?_).trans ?_
  · intro midSlot _ hne
    rw [data.foldMatrix_col_self tau hself midSlot, if_neg hne, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot
  · rw [data.foldMatrix_col_self tau hself colSlot, if_pos rfl, mul_one]
    rfl

/-- The minimum folded column of a pair. -/
theorem foldColumns_min (tau : ℝ) {colSlot : Fin data.basisCount}
    (hpair : data.pairedPartner colSlot ≠ colSlot)
    (hlt : colSlot < data.pairedPartner colSlot) (atomIndex : Fin 6) :
    data.foldColumns tau atomIndex colSlot
      = data.tightDir (data.basisLabel colSlot) atomIndex
        + tau * data.tightDir (data.basisLabel (data.pairedPartner colSlot))
          atomIndex := by
  rw [foldColumns, Matrix.mul_apply]
  rw [← Finset.sum_subset (Finset.subset_univ
    ({colSlot, data.pairedPartner colSlot} : Finset (Fin data.basisCount)))
    (fun midSlot _ hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      rw [data.foldMatrix_col_min tau hpair hlt midSlot, if_neg hnot.1,
        if_neg hnot.2, mul_zero])]
  rw [Finset.sum_pair (Ne.symm hpair),
    data.foldMatrix_col_min tau hpair hlt colSlot, if_pos rfl,
    data.foldMatrix_col_min tau hpair hlt (data.pairedPartner colSlot),
    if_neg hpair, if_pos rfl]
  show data.tightDir (data.basisLabel colSlot) atomIndex * 1
      + data.tightDir (data.basisLabel (data.pairedPartner colSlot)) atomIndex
        * tau = _
  ring

/-- The maximum folded column of a pair. -/
theorem foldColumns_max (tau : ℝ) {colSlot : Fin data.basisCount}
    (hpair : data.pairedPartner colSlot ≠ colSlot)
    (hgt : data.pairedPartner colSlot < colSlot) (atomIndex : Fin 6) :
    data.foldColumns tau atomIndex colSlot
      = (data.gram (data.pairedPartner colSlot) colSlot
          - tau * data.gram (data.pairedPartner colSlot)
            (data.pairedPartner colSlot))
        * data.tightDir (data.basisLabel (data.pairedPartner colSlot)) atomIndex
        + (data.gram colSlot colSlot
          - tau * data.gram (data.pairedPartner colSlot) colSlot)
          * data.tightDir (data.basisLabel colSlot) atomIndex := by
  rw [foldColumns, Matrix.mul_apply]
  rw [← Finset.sum_subset (Finset.subset_univ
    ({colSlot, data.pairedPartner colSlot} : Finset (Fin data.basisCount)))
    (fun midSlot _ hnot => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      rw [data.foldMatrix_col_max tau hpair hgt midSlot, if_neg hnot.2,
        if_neg hnot.1, mul_zero])]
  rw [Finset.sum_pair (Ne.symm hpair),
    data.foldMatrix_col_max tau hpair hgt colSlot,
    if_neg (fun h => hpair h.symm), if_pos rfl,
    data.foldMatrix_col_max tau hpair hgt (data.pairedPartner colSlot),
    if_pos rfl]
  show data.tightDir (data.basisLabel colSlot) atomIndex * _
      + data.tightDir (data.basisLabel (data.pairedPartner colSlot)) atomIndex
        * _ = _
  ring

/-- **THE GOOD PARAMETER EXISTS.**  Each folded column of a pair loses an
atom of the support at one parameter value at most, thus a parameter
avoiding the finite bad set keeps every support whole. -/
theorem exists_foldParameter (data : SharedPrivateData crux) :
    ∃ tau : ℝ, ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0 := by
  classical
  set badRoot : Fin data.basisCount × Fin 6 → ℝ := fun pair =>
    if pair.1 < data.pairedPartner pair.1 then
      -(data.tightDir (data.basisLabel pair.1) pair.2)
        / data.tightDir (data.basisLabel (data.pairedPartner pair.1)) pair.2
    else
      (data.gram (data.pairedPartner pair.1) pair.1
          * data.tightDir (data.basisLabel (data.pairedPartner pair.1)) pair.2
        + data.gram pair.1 pair.1
          * data.tightDir (data.basisLabel pair.1) pair.2)
      / (data.gram (data.pairedPartner pair.1) (data.pairedPartner pair.1)
          * data.tightDir (data.basisLabel (data.pairedPartner pair.1)) pair.2
        + data.gram (data.pairedPartner pair.1) pair.1
          * data.tightDir (data.basisLabel pair.1) pair.2)
    with hbadRoot
  obtain ⟨tau, htau⟩ :=
    Infinite.exists_notMem_finset (Finset.image badRoot Finset.univ)
  refine ⟨tau, fun slot hpair atomIndex hmem => ?_⟩
  have hliveSelf : data.tightDir (data.basisLabel slot) atomIndex ≠ 0 :=
    data.basis_live_of_mem_support hmem
  have hlivePartner : data.tightDir
      (data.basisLabel (data.pairedPartner slot)) atomIndex ≠ 0 :=
    data.basis_live_of_mem_support
      (by rw [data.pairedPartner_support_eq slot]; exact hmem)
  intro hzero
  rcases lt_or_gt_of_ne (Ne.symm hpair) with hlt | hgt
  · rw [data.foldColumns_min tau hpair hlt atomIndex] at hzero
    refine htau (Finset.mem_image.mpr ⟨(slot, atomIndex), Finset.mem_univ _, ?_⟩)
    rw [hbadRoot]
    simp only [if_pos hlt]
    rw [div_eq_iff hlivePartner]
    linarith [hzero]
  · rw [data.foldColumns_max tau hpair hgt atomIndex] at hzero
    by_cases hslope : data.gram (data.pairedPartner slot)
          (data.pairedPartner slot)
          * data.tightDir (data.basisLabel (data.pairedPartner slot)) atomIndex
        + data.gram (data.pairedPartner slot) slot
          * data.tightDir (data.basisLabel slot) atomIndex = 0
    · -- a dead slope with a dead value puts a nonzero vector in the corner
      have hconst : data.gram (data.pairedPartner slot) slot
            * data.tightDir (data.basisLabel (data.pairedPartner slot))
              atomIndex
          + data.gram slot slot
            * data.tightDir (data.basisLabel slot) atomIndex = 0 := by
        linear_combination hzero + tau * hslope
      have hpos := data.gram_pair_energy_pos
        (slotA := data.pairedPartner slot) (slotB := slot)
        hpair (coeffA := data.tightDir
          (data.basisLabel (data.pairedPartner slot)) atomIndex)
        (coeffB := data.tightDir (data.basisLabel slot) atomIndex)
        (Or.inr hliveSelf)
      have hcollapse : data.tightDir
            (data.basisLabel (data.pairedPartner slot)) atomIndex
            * data.tightDir (data.basisLabel (data.pairedPartner slot))
              atomIndex
            * data.gram (data.pairedPartner slot) (data.pairedPartner slot)
          + 2 * (data.tightDir
              (data.basisLabel (data.pairedPartner slot)) atomIndex
            * data.tightDir (data.basisLabel slot) atomIndex)
            * data.gram (data.pairedPartner slot) slot
          + data.tightDir (data.basisLabel slot) atomIndex
            * data.tightDir (data.basisLabel slot) atomIndex
            * data.gram slot slot = 0 := by
        linear_combination data.tightDir
            (data.basisLabel (data.pairedPartner slot)) atomIndex * hslope
          + data.tightDir (data.basisLabel slot) atomIndex * hconst
      linarith [hpos, hcollapse]
    · refine htau (Finset.mem_image.mpr
        ⟨(slot, atomIndex), Finset.mem_univ _, ?_⟩)
      rw [hbadRoot]
      simp only [if_neg (not_lt.mpr hgt.le)]
      rw [div_eq_iff hslope]
      linarith [hzero]

/-! ## Layer 5 — the normalized fold frame -/

/-- The squared norm of a folded column. -/
noncomputable def foldNormSq (tau : ℝ) (slot : Fin data.basisCount) : ℝ :=
  ∑ atomIndex, data.foldColumns tau atomIndex slot ^ 2

/-- The norm of a folded column. -/
noncomputable def foldScale (tau : ℝ) (slot : Fin data.basisCount) : ℝ :=
  Real.sqrt (data.foldNormSq tau slot)

/-- The normalized folded direction of a slot. -/
noncomputable def foldDir (tau : ℝ) (slot : Fin data.basisCount) :
    Fin 6 → ℝ :=
  fun atomIndex => data.foldColumns tau atomIndex slot
    / data.foldScale tau slot

/-- A folded column vanishes off the old support. -/
theorem foldColumns_eq_zero_of_notMem (tau : ℝ)
    {slot : Fin data.basisCount} {atomIndex : Fin 6}
    (hout : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.foldColumns tau atomIndex slot = 0 := by
  have hdeadSelf : data.tightDir (data.basisLabel slot) atomIndex = 0 :=
    data.basis_dead_of_notMem_support hout
  by_cases hself : data.pairedPartner slot = slot
  · rw [data.foldColumns_self tau hself atomIndex, hdeadSelf]
  · have hdeadPartner : data.tightDir
        (data.basisLabel (data.pairedPartner slot)) atomIndex = 0 :=
      data.basis_dead_of_notMem_support
        (by rw [data.pairedPartner_support_eq slot]; exact hout)
    rcases lt_or_gt_of_ne (Ne.symm hself) with hlt | hgt
    · rw [data.foldColumns_min tau hself hlt atomIndex, hdeadSelf, hdeadPartner]
      ring
    · rw [data.foldColumns_max tau hself hgt atomIndex, hdeadSelf, hdeadPartner]
      ring

/-- The squared norm of a folded column is positive at a good
parameter. -/
theorem foldNormSq_pos (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) : 0 < data.foldNormSq tau slot := by
  have hcard := data.hthree slot
  have hnonempty : (datumTightSupport data.tightDir
      (data.basisLabel slot)).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  obtain ⟨atomIndex, hmem⟩ := hnonempty
  have hne : data.foldColumns tau atomIndex slot ≠ 0 := by
    by_cases hself : data.pairedPartner slot = slot
    · rw [data.foldColumns_self tau hself atomIndex]
      exact data.basis_live_of_mem_support hmem
    · exact hgood slot hself atomIndex hmem
  have hterm : 0 < data.foldColumns tau atomIndex slot ^ 2 := by
    positivity
  refine lt_of_lt_of_le hterm ?_
  rw [foldNormSq]
  exact Finset.single_le_sum
    (f := fun probe => data.foldColumns tau probe slot ^ 2)
    (fun probe _ => sq_nonneg _) (Finset.mem_univ atomIndex)

/-- The norm of a folded column is positive at a good parameter. -/
theorem foldScale_pos (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) : 0 < data.foldScale tau slot :=
  Real.sqrt_pos.mpr (data.foldNormSq_pos tau hgood slot)

/-- The square of the norm reads the squared norm. -/
theorem foldScale_sq (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) :
    data.foldScale tau slot ^ 2 = data.foldNormSq tau slot :=
  Real.sq_sqrt (data.foldNormSq_pos tau hgood slot).le

/-- **THE FOLDED DIRECTION IS A UNIT VECTOR.** -/
theorem foldDir_unit (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) :
    data.foldDir tau slot ⬝ᵥ data.foldDir tau slot = 1 := by
  have hpos := data.foldNormSq_pos tau hgood slot
  have hsq := data.foldScale_sq tau hgood slot
  have hscaleNe : data.foldScale tau slot ≠ 0 :=
    ne_of_gt (data.foldScale_pos tau hgood slot)
  show (∑ atomIndex, data.foldDir tau slot atomIndex
    * data.foldDir tau slot atomIndex) = 1
  have hterm : ∀ atomIndex, data.foldDir tau slot atomIndex
      * data.foldDir tau slot atomIndex
      = data.foldColumns tau atomIndex slot ^ 2
        / data.foldScale tau slot ^ 2 := by
    intro atomIndex
    rw [foldDir]
    field_simp
  rw [Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex,
    ← Finset.sum_div, hsq, ← foldNormSq]
  exact div_self (ne_of_gt hpos)

/-- **THE FOLDED SUPPORT IS THE OLD SUPPORT** at a good parameter. -/
theorem foldDir_support_eq (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) :
    datumTightSupport (data.foldDir tau) slot
      = datumTightSupport data.tightDir (data.basisLabel slot) := by
  have hscaleNe : data.foldScale tau slot ≠ 0 :=
    ne_of_gt (data.foldScale_pos tau hgood slot)
  ext atomIndex
  rw [mem_datumTightSupport, mem_datumTightSupport]
  constructor
  · intro hne
    by_contra hout
    refine hne ?_
    rw [foldDir, data.foldColumns_eq_zero_of_notMem tau
      (by rw [mem_datumTightSupport]; exact not_not.mpr hout), zero_div]
  · intro hlive
    have hmem : atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel slot) := mem_datumTightSupport.mpr hlive
    have hcolNe : data.foldColumns tau atomIndex slot ≠ 0 := by
      by_cases hself : data.pairedPartner slot = slot
      · rw [data.foldColumns_self tau hself atomIndex]
        exact hlive
      · exact hgood slot hself atomIndex hmem
    rw [foldDir]
    exact div_ne_zero hcolNe hscaleNe

/-- The scale of an unpartnered slot is one. -/
theorem foldScale_self (tau : ℝ) {slot : Fin data.basisCount}
    (hself : data.pairedPartner slot = slot) :
    data.foldScale tau slot = 1 := by
  have hnorm : data.foldNormSq tau slot = 1 := by
    rw [foldNormSq]
    have hunit := data.hdata.tightDir_unit (data.basisLabel slot)
      (data.basisLabel_mem_activeSet slot)
    rw [dotProduct] at hunit
    rw [Finset.sum_congr rfl fun atomIndex _ => by
      rw [data.foldColumns_self tau hself atomIndex, sq]]
    exact hunit
  rw [foldScale, hnorm, Real.sqrt_one]

/-- The folded columns are the fold of the basis columns. -/
theorem foldColumns_eq_mul (tau : ℝ) :
    data.foldColumns tau
      = tightBasisColumns data.tightDir data.basisLabel
        * data.foldMatrix tau := rfl

/-- The normalized columns as a matrix product. -/
theorem foldDir_columns_eq (tau : ℝ) :
    tightBasisColumns (data.foldDir tau) (id : Fin data.basisCount → _)
      = data.foldColumns tau
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) := by
  ext atomIndex slot
  rw [Matrix.mul_diagonal]
  show data.foldDir tau slot atomIndex
    = data.foldColumns tau atomIndex slot * (data.foldScale tau slot)⁻¹
  rw [foldDir, div_eq_mul_inv]

/-- **THE FOLDED TIGHTNESS.**  Every folded column is tight on its
block. -/
theorem foldColumns_isTight (tau : ℝ) (slot : Fin data.basisCount)
    {atomIndex : Fin 6}
    (hblock : atomIndex ∈ data.activeSubset (data.basisLabel slot)) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ fun probe => data.foldColumns tau probe slot) atomIndex
      = chartObjective (chartPointOfDesign crux.design)
        * data.foldColumns tau atomIndex slot := by
  have htightSelf := data.hdata.tightDir_isTight (data.basisLabel slot)
    (data.basisLabel_mem_activeSet slot) atomIndex hblock
  by_cases hself : data.pairedPartner slot = slot
  · have hfun : (fun probe => data.foldColumns tau probe slot)
        = data.tightDir (data.basisLabel slot) := by
      funext probe
      exact data.foldColumns_self tau hself probe
    rw [hfun, htightSelf, data.foldColumns_self tau hself atomIndex]
  · have hblockPartner : atomIndex
        ∈ data.activeSubset (data.basisLabel (data.pairedPartner slot)) := by
      rw [data.basisBlock_eq_support, data.pairedPartner_support_eq slot,
        ← data.basisBlock_eq_support]
      exact hblock
    have htightPartner := data.hdata.tightDir_isTight
      (data.basisLabel (data.pairedPartner slot))
      (data.basisLabel_mem_activeSet (data.pairedPartner slot))
      atomIndex hblockPartner
    have hcombo : ∀ coeffSelf coeffPartner : ℝ,
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ fun probe => coeffSelf * data.tightDir (data.basisLabel slot) probe
            + coeffPartner * data.tightDir
              (data.basisLabel (data.pairedPartner slot)) probe) atomIndex
        = chartObjective (chartPointOfDesign crux.design)
          * (coeffSelf * data.tightDir (data.basisLabel slot) atomIndex
            + coeffPartner * data.tightDir
              (data.basisLabel (data.pairedPartner slot)) atomIndex) := by
      intro coeffSelf coeffPartner
      have hexpand : (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ fun probe => coeffSelf * data.tightDir (data.basisLabel slot) probe
            + coeffPartner * data.tightDir
              (data.basisLabel (data.pairedPartner slot)) probe) atomIndex
          = coeffSelf * (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
            *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
            + coeffPartner
              * (chartStationaryGap (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
              *ᵥ data.tightDir
                (data.basisLabel (data.pairedPartner slot))) atomIndex := by
        show (∑ probe, chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomIndex probe
            * (coeffSelf * data.tightDir (data.basisLabel slot) probe
              + coeffPartner * data.tightDir
                (data.basisLabel (data.pairedPartner slot)) probe)) = _
        rw [show coeffSelf * (chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
            *ᵥ data.tightDir (data.basisLabel slot)) atomIndex
            + coeffPartner * (chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
            *ᵥ data.tightDir
              (data.basisLabel (data.pairedPartner slot))) atomIndex
          = coeffSelf * ∑ probe, chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomIndex probe
              * data.tightDir (data.basisLabel slot) probe
            + coeffPartner * ∑ probe, chartStationaryGap
              (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomIndex probe
              * data.tightDir (data.basisLabel (data.pairedPartner slot)) probe
          from rfl]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun probe _ => by ring
      rw [hexpand, htightSelf, htightPartner]
      ring
    rcases lt_or_gt_of_ne (Ne.symm hself) with hlt | hgt
    · have hfun : (fun probe => data.foldColumns tau probe slot)
          = fun probe => 1 * data.tightDir (data.basisLabel slot) probe
            + tau * data.tightDir
              (data.basisLabel (data.pairedPartner slot)) probe := by
        funext probe
        rw [data.foldColumns_min tau hself hlt probe]
        ring
      rw [hfun, hcombo 1 tau, data.foldColumns_min tau hself hlt atomIndex]
      ring
    · have hfun' : (fun probe => data.foldColumns tau probe slot)
          = fun probe => (data.gram slot slot
              - tau * data.gram (data.pairedPartner slot) slot)
              * data.tightDir (data.basisLabel slot) probe
            + (data.gram (data.pairedPartner slot) slot
              - tau * data.gram (data.pairedPartner slot)
                (data.pairedPartner slot))
              * data.tightDir
                (data.basisLabel (data.pairedPartner slot)) probe := by
        funext probe
        rw [data.foldColumns_max tau hself hgt probe]
        ring
      rw [hfun', hcombo _ _, data.foldColumns_max tau hself hgt atomIndex]
      ring

end SharedPrivateData

/-! ## Layer 6 — the assembly identity of a self-indexed family -/

/-- The assembly of a family indexed by its own basis is the column
conjugate of the weight diagonal. -/
theorem chartMultiplierAssembly_univ_eq_columns_diagonal {basisCount : ℕ}
    (weightVec : Fin basisCount → ℝ) (dirs : Fin basisCount → Fin 6 → ℝ) :
    chartMultiplierAssembly Finset.univ weightVec dirs
      = tightBasisColumns dirs (id : Fin basisCount → Fin basisCount)
        * Matrix.diagonal weightVec
        * (tightBasisColumns dirs (id : Fin basisCount → Fin basisCount))ᵀ := by
  ext atomRow atomCol
  rw [chartMultiplierAssembly_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  show weightVec slot * (dirs slot atomRow * dirs slot atomCol)
    = dirs slot atomRow * weightVec slot * dirs slot atomCol
  ring

namespace SharedPrivateData

variable {crux : SixThreeCrux} (data : SharedPrivateData crux)

/-- The folded weight of a slot. -/
noncomputable def foldWeight (tau : ℝ) (slot : Fin data.basisCount) : ℝ :=
  data.foldScale tau slot ^ 2 * data.foldGram tau slot slot

/-- The folded weight is positive at a good parameter. -/
theorem foldWeight_pos (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) : 0 < data.foldWeight tau slot :=
  mul_pos (pow_pos (data.foldScale_pos tau hgood slot) 2)
    (data.foldGram_diag_pos tau slot)

/-- The weight diagonal is the scale conjugate of the folded core. -/
theorem foldWeight_diagonal_eq (tau : ℝ)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)) :
    Matrix.diagonal (data.foldWeight tau)
      = Matrix.diagonal (data.foldScale tau) * data.foldGram tau
        * Matrix.diagonal (data.foldScale tau) := by
  ext rowSlot colSlot
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases heq : rowSlot = colSlot
  · subst heq
    rw [Matrix.diagonal_apply_eq, foldWeight]
    ring
  · rw [Matrix.diagonal_apply_ne _ heq,
      data.foldGram_offDiag_eq_zero tau hpaired heq]
    ring

set_option maxHeartbeats 6400000 in
/-- **THE ASSEMBLY IS UNCHANGED BY THE FOLD.**  The folded family
assembles the same multiplier as the old datum. -/
theorem foldAssembly_eq (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)) :
    chartMultiplierAssembly Finset.univ (data.foldWeight tau)
        (data.foldDir tau)
      = chartMultiplierAssembly data.activeSet data.reducedWeight
        data.tightDir := by
  have hscaleInv : Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
      * Matrix.diagonal (data.foldScale tau) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hentry : (fun slot => (data.foldScale tau slot)⁻¹
        * data.foldScale tau slot) = fun _ => 1 := by
      funext slot
      exact inv_mul_cancel₀ (ne_of_gt (data.foldScale_pos tau hgood slot))
    rw [hentry, Matrix.diagonal_one]
  rw [chartMultiplierAssembly_univ_eq_columns_diagonal,
    data.foldWeight_diagonal_eq tau hpaired, data.foldDir_columns_eq tau]
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc data.foldColumns tau
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
        * (Matrix.diagonal (data.foldScale tau) * data.foldGram tau
          * Matrix.diagonal (data.foldScale tau))
        * (Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
          * (data.foldColumns tau)ᵀ)
      = data.foldColumns tau
        * (Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
          * Matrix.diagonal (data.foldScale tau))
        * data.foldGram tau
        * (Matrix.diagonal (data.foldScale tau)
          * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹))
        * (data.foldColumns tau)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = data.foldColumns tau * data.foldGram tau * (data.foldColumns tau)ᵀ := by
        rw [hscaleInv, mul_eq_one_comm.mp hscaleInv, Matrix.mul_one,
          Matrix.mul_one]
    _ = tightBasisColumns data.tightDir data.basisLabel * data.gram
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ := by
        rw [data.foldColumns_eq_mul tau, foldGram]
        rw [Matrix.transpose_mul]
        calc tightBasisColumns data.tightDir data.basisLabel
              * data.foldMatrix tau
              * (data.foldInverse tau * data.gram * (data.foldInverse tau)ᵀ)
              * ((data.foldMatrix tau)ᵀ
                * (tightBasisColumns data.tightDir data.basisLabel)ᵀ)
            = tightBasisColumns data.tightDir data.basisLabel
              * (data.foldMatrix tau * data.foldInverse tau)
              * data.gram
              * ((data.foldInverse tau)ᵀ * (data.foldMatrix tau)ᵀ)
              * (tightBasisColumns data.tightDir data.basisLabel)ᵀ := by
              simp only [Matrix.mul_assoc]
          _ = tightBasisColumns data.tightDir data.basisLabel * data.gram
              * (tightBasisColumns data.tightDir data.basisLabel)ᵀ := by
              rw [data.foldMatrix_mul_foldInverse tau, Matrix.mul_one,
                ← Matrix.transpose_mul, data.foldMatrix_mul_foldInverse tau,
                Matrix.transpose_one, Matrix.mul_one]
    _ = chartMultiplierAssembly data.activeSet data.reducedWeight
        data.tightDir := data.hHform

/-! ## Layer 7 — the folded frame laws -/

/-- The unpartnered folded direction is the old column. -/
theorem foldDir_eq_self (tau : ℝ) {slot : Fin data.basisCount}
    (hself : data.pairedPartner slot = slot) :
    data.foldDir tau slot = data.tightDir (data.basisLabel slot) := by
  funext atomIndex
  rw [foldDir, data.foldScale_self tau hself,
    data.foldColumns_self tau hself atomIndex, div_one]

/-- The two diagonal scale matrices are inverse. -/
theorem foldScale_diag_mul_inv (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0) :
    Matrix.diagonal (data.foldScale tau)
      * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have hentry : (fun slot => data.foldScale tau slot
      * (data.foldScale tau slot)⁻¹) = fun _ => 1 := by
    funext slot
    exact mul_inv_cancel₀ (ne_of_gt (data.foldScale_pos tau hgood slot))
  rw [hentry, Matrix.diagonal_one]

/-- The folded coefficient matrix. -/
noncomputable def foldCoeff (tau : ℝ) :
    Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ :=
  Matrix.diagonal (data.foldScale tau)
    * (data.foldInverse tau * data.coeff * data.foldMatrix tau)
    * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)

/-- The folded left inverse. -/
noncomputable def foldLeftInv (tau : ℝ) :
    Matrix (Fin data.basisCount) (Fin 6) ℝ :=
  Matrix.diagonal (data.foldScale tau)
    * (data.foldInverse tau * data.leftInv)

set_option maxHeartbeats 6400000 in
/-- The folded left inverse law. -/
theorem foldLeftInv_mul (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0) :
    data.foldLeftInv tau
      * tightBasisColumns (data.foldDir tau)
        (id : Fin data.basisCount → Fin data.basisCount) = 1 := by
  rw [foldLeftInv, data.foldDir_columns_eq tau, data.foldColumns_eq_mul tau]
  calc Matrix.diagonal (data.foldScale tau)
        * (data.foldInverse tau * data.leftInv)
        * (tightBasisColumns data.tightDir data.basisLabel
          * data.foldMatrix tau
          * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹))
      = Matrix.diagonal (data.foldScale tau)
        * (data.foldInverse tau
          * (data.leftInv * tightBasisColumns data.tightDir data.basisLabel)
          * data.foldMatrix tau)
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal (data.foldScale tau)
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) := by
        rw [data.hleft, Matrix.mul_one, data.foldInverse_mul_foldMatrix tau,
          Matrix.mul_one]
    _ = 1 := data.foldScale_diag_mul_inv tau hgood

set_option maxHeartbeats 6400000 in
/-- The folded representation law. -/
theorem foldCoeff_representation (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0) :
    (chartPointOfDesign crux.design).chart
        * tightBasisColumns (data.foldDir tau)
          (id : Fin data.basisCount → Fin data.basisCount)
      = tightBasisColumns (data.foldDir tau)
          (id : Fin data.basisCount → Fin data.basisCount)
        * data.foldCoeff tau := by
  have hinvD := mul_eq_one_comm.mp (data.foldScale_diag_mul_inv tau hgood)
  rw [data.foldDir_columns_eq tau, data.foldColumns_eq_mul tau, foldCoeff]
  calc (chartPointOfDesign crux.design).chart
        * (tightBasisColumns data.tightDir data.basisLabel
          * data.foldMatrix tau
          * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹))
      = (chartPointOfDesign crux.design).chart
          * tightBasisColumns data.tightDir data.basisLabel
        * data.foldMatrix tau
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = tightBasisColumns data.tightDir data.basisLabel * data.coeff
        * data.foldMatrix tau
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) := by
        rw [data.hrepresentation]
    _ = tightBasisColumns data.tightDir data.basisLabel
        * data.foldMatrix tau
        * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
        * (Matrix.diagonal (data.foldScale tau)
          * (data.foldInverse tau * data.coeff * data.foldMatrix tau)
          * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)) := by
        calc tightBasisColumns data.tightDir data.basisLabel * data.coeff
              * data.foldMatrix tau
              * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
            = tightBasisColumns data.tightDir data.basisLabel
              * (data.foldMatrix tau * data.foldInverse tau)
              * data.coeff * data.foldMatrix tau
              * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) := by
              rw [data.foldMatrix_mul_foldInverse tau, Matrix.mul_one]
          _ = tightBasisColumns data.tightDir data.basisLabel
              * data.foldMatrix tau
              * ((Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
                * Matrix.diagonal (data.foldScale tau))
                * (data.foldInverse tau * data.coeff * data.foldMatrix tau
                  * Matrix.diagonal
                    (fun slot => (data.foldScale tau slot)⁻¹))) := by
              rw [hinvD, Matrix.one_mul]
              simp only [Matrix.mul_assoc]
          _ = tightBasisColumns data.tightDir data.basisLabel
              * data.foldMatrix tau
              * Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
              * (Matrix.diagonal (data.foldScale tau)
                * (data.foldInverse tau * data.coeff * data.foldMatrix tau)
                * Matrix.diagonal
                  (fun slot => (data.foldScale tau slot)⁻¹)) := by
              simp only [Matrix.mul_assoc]

set_option maxHeartbeats 6400000 in
/-- The folded coefficient matrix is idempotent. -/
theorem foldCoeff_idempotent (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0) :
    data.foldCoeff tau * data.foldCoeff tau = data.foldCoeff tau := by
  have hDiD : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
        * (Matrix.diagonal (data.foldScale tau) * M) = M := fun M => by
    rw [← Matrix.mul_assoc,
      mul_eq_one_comm.mp (data.foldScale_diag_mul_inv tau hgood),
      Matrix.one_mul]
  have hRRi : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      data.foldMatrix tau * (data.foldInverse tau * M) = M := fun M => by
    rw [← Matrix.mul_assoc, data.foldMatrix_mul_foldInverse tau, Matrix.one_mul]
  have hCC : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      data.coeff * (data.coeff * M) = data.coeff * M := fun M => by
    rw [← Matrix.mul_assoc, data.hidempotent]
  rw [foldCoeff]
  simp only [Matrix.mul_assoc]
  simp only [hDiD, hRRi, hCC]

set_option maxHeartbeats 6400000 in
/-- The folded trace agrees with the old trace. -/
theorem foldCoeff_trace (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0) :
    Matrix.trace (data.foldCoeff tau) = Matrix.trace data.coeff := by
  rw [foldCoeff, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    mul_eq_one_comm.mp (data.foldScale_diag_mul_inv tau hgood),
    Matrix.one_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    data.foldMatrix_mul_foldInverse tau, Matrix.one_mul]

set_option maxHeartbeats 6400000 in
/-- The folded exchange law. -/
theorem foldCoeff_exchange (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)) :
    data.foldCoeff tau * Matrix.diagonal (data.foldWeight tau)
      = Matrix.diagonal (data.foldWeight tau) * (data.foldCoeff tau)ᵀ := by
  have hDiD : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹)
        * (Matrix.diagonal (data.foldScale tau) * M) = M := fun M => by
    rw [← Matrix.mul_assoc,
      mul_eq_one_comm.mp (data.foldScale_diag_mul_inv tau hgood),
      Matrix.one_mul]
  have hDDi : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      Matrix.diagonal (data.foldScale tau)
        * (Matrix.diagonal (fun slot => (data.foldScale tau slot)⁻¹) * M)
        = M := fun M => by
    rw [← Matrix.mul_assoc, data.foldScale_diag_mul_inv tau hgood,
      Matrix.one_mul]
  have hRRi : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      data.foldMatrix tau * (data.foldInverse tau * M) = M := fun M => by
    rw [← Matrix.mul_assoc, data.foldMatrix_mul_foldInverse tau, Matrix.one_mul]
  have hRtRt : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      (data.foldInverse tau)ᵀ * ((data.foldMatrix tau)ᵀ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul,
      data.foldMatrix_mul_foldInverse tau, Matrix.transpose_one,
      Matrix.one_mul]
  have hCG : ∀ M : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ,
      data.coeff * (data.gram * M) = data.gram * (data.coeffᵀ * M) := fun M => by
    rw [← Matrix.mul_assoc, data.hexchange, Matrix.mul_assoc]
  rw [foldCoeff, data.foldWeight_diagonal_eq tau hpaired, foldGram]
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]
  simp only [hDiD, hDDi, hRRi, hRtRt, hCG]

/-- The folded coefficient entry at an unpartnered slot. -/
theorem foldCoeff_apply_self (tau : ℝ) {slot : Fin data.basisCount}
    (hself : data.pairedPartner slot = slot) :
    data.foldCoeff tau slot slot = data.coeff slot slot := by
  classical
  have hinner : (data.foldInverse tau * data.coeff * data.foldMatrix tau)
      slot slot = data.coeff slot slot := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single slot (fun midSlot _ hne => by
      rw [data.foldMatrix_col_self tau hself midSlot, if_neg hne, mul_zero])
      (fun hnot => absurd (Finset.mem_univ _) hnot)]
    rw [data.foldMatrix_col_self tau hself slot, if_pos rfl, mul_one,
      Matrix.mul_apply]
    rw [Finset.sum_eq_single slot (fun midSlot _ hne => by
      rw [data.foldInverse_row_self tau hself midSlot,
        if_neg (fun h => hne h), zero_mul])
      (fun hnot => absurd (Finset.mem_univ _) hnot)]
    rw [data.foldInverse_row_self tau hself slot, if_pos rfl, one_mul]
  rw [foldCoeff, Matrix.mul_diagonal, Matrix.diagonal_mul, hinner,
    data.foldScale_self tau hself, inv_one, one_mul, mul_one]

/-! ## Layer 8 — the folded stationarity bundle -/

/-- The folded direction as a scaled column. -/
theorem foldDir_smul (tau : ℝ) (slot : Fin data.basisCount) :
    data.foldDir tau slot
      = (data.foldScale tau slot)⁻¹
        • fun atomIndex => data.foldColumns tau atomIndex slot := by
  funext atomIndex
  rw [Pi.smul_apply, smul_eq_mul, foldDir, div_eq_mul_inv, mul_comm]

/-- The folded direction is tight on its block. -/
theorem foldDir_isTight (tau : ℝ) (slot : Fin data.basisCount)
    {atomIndex : Fin 6}
    (hblock : atomIndex ∈ data.activeSubset (data.basisLabel slot)) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ data.foldDir tau slot) atomIndex
      = chartObjective (chartPointOfDesign crux.design)
        * data.foldDir tau slot atomIndex := by
  rw [data.foldDir_smul tau slot, Matrix.mulVec_smul, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    data.foldColumns_isTight tau slot hblock]
  ring

/-- The squared reads of a unit direction total one. -/
theorem foldDir_sq_sum (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (slot : Fin data.basisCount) :
    ∑ atomIndex, data.foldDir tau slot atomIndex ^ 2 = 1 := by
  have hunit := data.foldDir_unit tau hgood slot
  rw [dotProduct] at hunit
  rw [← hunit]
  exact Finset.sum_congr rfl fun atomIndex _ => sq (data.foldDir tau slot
    atomIndex) ▸ by rw [pow_two]

/-- **THE FOLDED WEIGHTS TOTAL ONE.** -/
theorem foldWeight_sum_one (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)) :
    ∑ slot, data.foldWeight tau slot = 1 := by
  calc ∑ slot, data.foldWeight tau slot
      = ∑ slot, ∑ atomIndex, data.foldWeight tau slot
          * data.foldDir tau slot atomIndex ^ 2 := by
        refine Finset.sum_congr rfl fun slot _ => ?_
        rw [← Finset.mul_sum, data.foldDir_sq_sum tau hgood slot, mul_one]
    _ = ∑ atomIndex, ∑ slot, data.foldWeight tau slot
          * data.foldDir tau slot atomIndex ^ 2 := Finset.sum_comm
    _ = ∑ atomIndex : Fin 6, ((6 : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [← chartMultiplierAssembly_diagonal Finset.univ
          (data.foldWeight tau) (data.foldDir tau) atomIndex]
        rw [data.foldAssembly_eq tau hgood hpaired]
        exact data.hdata.assembly_diagonal atomIndex
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        norm_num

/-- **THE FOLDED STATIONARITY BUNDLE.** -/
theorem pairFold_hdata (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)) :
    IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (Finset.univ : Finset (Fin data.basisCount))
      (fun slot => data.activeSubset (data.basisLabel slot))
      (data.foldWeight tau) (data.foldDir tau) := by
  refine ⟨data.hdata.isSymmetric, data.hdata.isIdempotent,
    data.hdata.hasTraceRank, data.hdata.weight_pos,
    data.hdata.weight_sum_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun slot _ => (data.foldWeight_pos tau hgood slot).le
  · exact data.foldWeight_sum_one tau hgood hpaired
  · exact fun slot _ => data.hdata.activeSubset_card (data.basisLabel slot)
      (data.basisLabel_mem_activeSet slot)
  · exact fun slot _ => data.foldDir_unit tau hgood slot
  · intro slot _ atomIndex hout
    have hsupp : atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel slot) := by
      rw [← data.basisBlock_eq_support slot]
      exact hout
    rw [foldDir, data.foldColumns_eq_zero_of_notMem tau hsupp, zero_div]
  · exact fun slot _ atomIndex hblock => data.foldDir_isTight tau slot hblock
  · intro atomIndex
    rw [data.foldAssembly_eq tau hgood hpaired]
    exact data.hdata.assembly_diagonal atomIndex
  · rw [data.foldAssembly_eq tau hgood hpaired]
    exact data.hdata.assembly_commutes

/-! ## Layer 9 — the span of the folded frame -/

/-- The minimum folded direction as a combination of the pair columns. -/
theorem foldDir_min_comb (tau : ℝ) {slot : Fin data.basisCount}
    (hpair : data.pairedPartner slot ≠ slot)
    (hlt : slot < data.pairedPartner slot) :
    data.foldDir tau slot
      = (data.foldScale tau slot)⁻¹ • data.tightDir (data.basisLabel slot)
        + ((data.foldScale tau slot)⁻¹ * tau)
          • data.tightDir (data.basisLabel (data.pairedPartner slot)) := by
  funext atomIndex
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    foldDir, data.foldColumns_min tau hpair hlt atomIndex, div_eq_mul_inv]
  ring

/-- The maximum folded direction as a combination of the pair columns. -/
theorem foldDir_max_comb (tau : ℝ) {slot : Fin data.basisCount}
    (hpair : data.pairedPartner slot ≠ slot)
    (hgt : data.pairedPartner slot < slot) :
    data.foldDir tau slot
      = ((data.foldScale tau slot)⁻¹
          * (data.gram (data.pairedPartner slot) slot
            - tau * data.gram (data.pairedPartner slot)
              (data.pairedPartner slot)))
          • data.tightDir (data.basisLabel (data.pairedPartner slot))
        + ((data.foldScale tau slot)⁻¹
          * (data.gram slot slot
            - tau * data.gram (data.pairedPartner slot) slot))
          • data.tightDir (data.basisLabel slot) := by
  funext atomIndex
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    foldDir, data.foldColumns_max tau hpair hgt atomIndex, div_eq_mul_inv]
  ring

set_option maxHeartbeats 6400000 in
/-- The minimum pair column as a combination of the folded directions. -/
theorem tightDir_min_comb (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    {slot : Fin data.basisCount}
    (hpair : data.pairedPartner slot ≠ slot)
    (hlt : slot < data.pairedPartner slot) :
    data.tightDir (data.basisLabel slot)
      = ((data.foldDelta tau slot)⁻¹
          * (data.gram (data.pairedPartner slot) (data.pairedPartner slot)
            - tau * data.gram slot (data.pairedPartner slot))
          * data.foldScale tau slot) • data.foldDir tau slot
        + ((data.foldDelta tau slot)⁻¹ * (-tau)
          * data.foldScale tau (data.pairedPartner slot))
          • data.foldDir tau (data.pairedPartner slot) := by
  have hinv : data.pairedPartner (data.pairedPartner slot) = slot :=
    data.pairedPartner_involution hpair
  have hpne : data.pairedPartner (data.pairedPartner slot)
      ≠ data.pairedPartner slot := by
    rw [hinv]; exact fun h => hpair h.symm
  have hplt : data.pairedPartner (data.pairedPartner slot)
      < data.pairedPartner slot := by
    rw [hinv]; exact hlt
  have hdne : data.foldDelta tau slot ≠ 0 :=
    ne_of_gt (data.foldDelta_pos tau hpair)
  have hsne : data.foldScale tau slot ≠ 0 :=
    ne_of_gt (data.foldScale_pos tau hgood slot)
  have hpne' : data.foldScale tau (data.pairedPartner slot) ≠ 0 :=
    ne_of_gt (data.foldScale_pos tau hgood (data.pairedPartner slot))
  funext atomIndex
  have hcolMax := data.foldColumns_max tau hpne hplt atomIndex
  rw [hinv] at hcolMax
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    foldDir, foldDir, data.foldColumns_min tau hpair hlt atomIndex, hcolMax]
  field_simp
  rw [data.foldDelta_min tau hlt]
  ring

set_option maxHeartbeats 6400000 in
/-- The maximum pair column as a combination of the folded directions. -/
theorem tightDir_max_comb (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0)
    {slot : Fin data.basisCount}
    (hpair : data.pairedPartner slot ≠ slot)
    (hgt : data.pairedPartner slot < slot) :
    data.tightDir (data.basisLabel slot)
      = ((data.foldDelta tau (data.pairedPartner slot))⁻¹
          * (-(data.gram (data.pairedPartner slot) slot
            - tau * data.gram (data.pairedPartner slot)
              (data.pairedPartner slot)))
          * data.foldScale tau (data.pairedPartner slot))
          • data.foldDir tau (data.pairedPartner slot)
        + ((data.foldDelta tau (data.pairedPartner slot))⁻¹
          * data.foldScale tau slot) • data.foldDir tau slot := by
  have hinv : data.pairedPartner (data.pairedPartner slot) = slot :=
    data.pairedPartner_involution hpair
  have hpne : data.pairedPartner (data.pairedPartner slot)
      ≠ data.pairedPartner slot := by
    rw [hinv]; exact fun h => hpair h.symm
  have hplt : data.pairedPartner slot
      < data.pairedPartner (data.pairedPartner slot) := by
    rw [hinv]; exact hgt
  have hdne : data.foldDelta tau (data.pairedPartner slot) ≠ 0 :=
    ne_of_gt (data.foldDelta_pos tau hpne)
  have hsne : data.foldScale tau slot ≠ 0 :=
    ne_of_gt (data.foldScale_pos tau hgood slot)
  have hpne' : data.foldScale tau (data.pairedPartner slot) ≠ 0 :=
    ne_of_gt (data.foldScale_pos tau hgood (data.pairedPartner slot))
  have hdeltaEq : data.foldDelta tau (data.pairedPartner slot)
      = data.gram slot slot
        - 2 * tau * data.gram (data.pairedPartner slot) slot
        + tau ^ 2 * data.gram (data.pairedPartner slot)
          (data.pairedPartner slot) := by
    have hstep := data.foldDelta_min tau (slot := data.pairedPartner slot) hplt
    rw [hinv] at hstep
    exact hstep
  funext atomIndex
  have hcolMin := data.foldColumns_min tau hpne hplt atomIndex
  rw [hinv] at hcolMin
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    foldDir, foldDir, data.foldColumns_max tau hpair hgt atomIndex, hcolMin]
  field_simp
  rw [hdeltaEq]
  ring

set_option maxHeartbeats 6400000 in
/-- **THE SPAN IS UNCHANGED BY THE FOLD.** -/
theorem foldSpan_eq (tau : ℝ)
    (hgood : ∀ slot : Fin data.basisCount,
      data.pairedPartner slot ≠ slot →
      ∀ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
        data.foldColumns tau atomIndex slot ≠ 0) :
    Submodule.span ℝ (Set.range (data.foldDir tau))
      = Submodule.span ℝ (Set.range fun slot =>
          data.tightDir (data.basisLabel slot)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨slot, rfl⟩
    by_cases hself : data.pairedPartner slot = slot
    · rw [data.foldDir_eq_self tau hself]
      exact Submodule.subset_span ⟨slot, rfl⟩
    rcases lt_or_gt_of_ne (Ne.symm hself) with hlt | hgt
    · rw [data.foldDir_min_comb tau hself hlt]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨slot, rfl⟩))
        (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨data.pairedPartner slot, rfl⟩))
    · rw [data.foldDir_max_comb tau hself hgt]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨data.pairedPartner slot, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨slot, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨slot, rfl⟩
    show data.tightDir (data.basisLabel slot)
      ∈ Submodule.span ℝ (Set.range (data.foldDir tau))
    by_cases hself : data.pairedPartner slot = slot
    · rw [← data.foldDir_eq_self tau hself]
      exact Submodule.subset_span ⟨slot, rfl⟩
    rcases lt_or_gt_of_ne (Ne.symm hself) with hlt | hgt
    · rw [data.tightDir_min_comb tau hgood hself hlt]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨slot, rfl⟩))
        (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨data.pairedPartner slot, rfl⟩))
    · rw [data.tightDir_max_comb tau hgood hself hgt]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨data.pairedPartner slot, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨slot, rfl⟩))

/-! ## Layer 10 — the fold kill -/

set_option maxHeartbeats 6400000 in
/-- **THE FOLD KILL.**  A shared-private datum whose nonzero off-diagonal
Gram entries all join equal-support slots rebases onto a diagonal Gram
core, and the landed diagonal kill closes it. -/
theorem false_of_supportPaired_gram (data : SharedPrivateData crux)
    (hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)) :
    False := by
  classical
  obtain ⟨tau, hgood⟩ := data.exists_foldParameter
  have hfilter : ∀ atomIndex : Fin 6,
      basisSupportMultiplicity (data.foldDir tau)
        (id : Fin data.basisCount → Fin data.basisCount) atomIndex
      = basisSupportMultiplicity data.tightDir data.basisLabel atomIndex := by
    intro atomIndex
    simp only [basisSupportMultiplicity, id_eq]
    congr 1
    refine Finset.filter_congr fun slot _ => ?_
    rw [data.foldDir_support_eq tau hgood slot]
  refine SharedPrivateData.false_of_diagonal_gram (crux := crux)
    (data :=
      { basisCount := data.basisCount
        activeIndex := Fin data.basisCount
        activeSet := Finset.univ
        activeSubset := fun slot => data.activeSubset (data.basisLabel slot)
        reducedWeight := data.foldWeight tau
        tightDir := data.foldDir tau
        basisLabel := id
        leftInv := data.foldLeftInv tau
        coeff := data.foldCoeff tau
        gram := Matrix.diagonal (data.foldWeight tau)
        hdata := data.pairFold_hdata tau hgood hpaired
        hinjective := Function.injective_id
        hmem := fun slot => by
          rw [positiveActiveSet, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, data.foldWeight_pos tau hgood slot⟩
        hspan := by
          rw [show (fun slot : Fin data.basisCount =>
              data.foldDir tau (id slot)) = data.foldDir tau from rfl,
            data.foldSpan_eq tau hgood,
            data.foldAssembly_eq tau hgood hpaired]
          exact data.hspan
        hleft := data.foldLeftInv_mul tau hgood
        hrepresentation := data.foldCoeff_representation tau hgood
        hidempotent := data.foldCoeff_idempotent tau hgood
        hHform := (chartMultiplierAssembly_univ_eq_columns_diagonal
          (data.foldWeight tau) (data.foldDir tau)).symm
        hsymmH := Matrix.diagonal_transpose (data.foldWeight tau)
        hpsd := Matrix.PosSemidef.diagonal
          (fun slot => (data.foldWeight_pos tau hgood slot).le)
        hker := fun probe hzero => by
          funext slot
          have hentry := congrFun hzero slot
          rw [Matrix.mulVec_diagonal] at hentry
          have hcases := mul_eq_zero.mp hentry
          rw [Pi.zero_apply]
          exact hcases.resolve_left
            (ne_of_gt (data.foldWeight_pos tau hgood slot))
        hexchange := data.foldCoeff_exchange tau hgood hpaired
        htrace := by
          rw [data.foldCoeff_trace tau hgood]
          exact data.htrace
        privateSlot := data.privateSlot
        pinAtom := data.pinAtom
        sharedAtom := data.sharedAtom
        hthree := fun slot => by
          rw [show datumTightSupport (data.foldDir tau) (id slot)
            = datumTightSupport (data.foldDir tau) slot from rfl,
            data.foldDir_support_eq tau hgood slot]
          exact data.hthree slot
        hmultOne := by
          rw [hfilter data.pinAtom]
          exact data.hmultOne
        hpinMem := data.hpinMem
        hpinNe := by
          show data.foldDir tau data.privateSlot data.pinAtom ≠ 0
          rw [data.foldDir_eq_self tau data.pairedPartner_privateSlot]
          exact data.hpinNe
        hprivate := fun slot hslot => by
          show data.foldDir tau slot data.pinAtom = 0
          by_contra hne
          have hmem := mem_datumTightSupport.mpr hne
          rw [data.foldDir_support_eq tau hgood slot] at hmem
          exact data.basis_live_of_mem_support hmem (data.hprivate slot hslot)
        hpin := by
          show data.foldCoeff tau data.privateSlot data.privateSlot = _
          rw [data.foldCoeff_apply_self tau data.pairedPartner_privateSlot]
          exact data.hpin
        hsharedMem := by
          show data.sharedAtom ∈ datumTightSupport (data.foldDir tau)
            data.privateSlot
          rw [data.foldDir_support_eq tau hgood data.privateSlot]
          exact data.hsharedMem
        hsharedMult := by
          rw [hfilter data.sharedAtom]
          exact data.hsharedMult })
    (gramDiag := data.foldWeight tau) rfl

/-! ## Layer 11 — the mixture witness and the split dispatch -/

/-- **THE MIXTURE WITNESS.**  A nonzero Gram entry supplies a positive
label with both coefficients alive. -/
theorem exists_label_of_gram_ne_zero (data : SharedPrivateData crux)
    {slotA slotB : Fin data.basisCount} (hne : data.gram slotA slotB ≠ 0) :
    ∃ label : data.activeIndex, label ∈ data.activeSet
      ∧ 0 < data.reducedWeight label
      ∧ data.labelCoeff label slotA ≠ 0
      ∧ data.labelCoeff label slotB ≠ 0 := by
  classical
  rw [data.gram_apply_eq_labelCoeff_sum slotA slotB] at hne
  obtain ⟨label, hmem, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [positiveActiveSet, Finset.mem_filter] at hmem
  have hcoeff : data.labelCoeff label slotA * data.labelCoeff label slotB ≠ 0 :=
    fun hzero => hterm (by rw [hzero, mul_zero])
  exact ⟨label, hmem.1, hmem.2, fun hzero => hcoeff (by rw [hzero, zero_mul]),
    fun hzero => hcoeff (by rw [hzero, mul_zero])⟩

set_option maxHeartbeats 6400000 in
/-- **THE SPLIT DISPATCH OF A PAIR LABEL.**  A pair circuit whose two
supports differ shares exactly two atoms, and the split residue kills
it. -/
theorem false_of_pair_label_of_support_ne (data : SharedPrivateData crux)
    (hsplit : SharedPrivateCircuitPairSplitClosed)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    (hdiff : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      ≠ datumTightSupport data.tightDir (data.basisLabel slotOne)) : False := by
  classical
  set supportOne := datumTightSupport data.tightDir (data.basisLabel slotOne)
    with hsupportOneDef
  set supportTwo := datumTightSupport data.tightDir (data.basisLabel slotTwo)
    with hsupportTwoDef
  have hcardOne : supportOne.card = 3 := data.hthree slotOne
  have hcardTwo : supportTwo.card = 3 := data.hthree slotTwo
  have hinterGe := data.pairCircuit_two_le_inter_card hmem hpos hne hcoeffOne
    hcoeffTwo hpair
  rw [← hsupportOneDef, ← hsupportTwoDef] at hinterGe
  have hinterLe : (supportOne ∩ supportTwo).card ≤ 3 := by
    rw [← hcardOne]
    exact Finset.card_le_card Finset.inter_subset_left
  have hcard : (supportOne ∩ supportTwo).card = 2 := by
    rcases Nat.lt_or_ge (supportOne ∩ supportTwo).card 3 with hlt | hge
    · omega
    · exfalso
      have hone : supportOne ∩ supportTwo = supportOne :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          (by rw [hcardOne]; exact hge)
      have htwo : supportOne ∩ supportTwo = supportTwo :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          (by rw [hcardTwo]; exact hge)
      exact hdiff (htwo.symm.trans hone)
  obtain ⟨atomA, atomB, hAB, hinterEq⟩ := Finset.card_eq_two.mp hcard
  have hsdiffOne : (supportOne \ supportTwo).card = 1 := by
    have hsplitOne := Finset.card_sdiff_add_card_inter supportOne supportTwo
    omega
  have hsdiffTwo : (supportTwo \ supportOne).card = 1 := by
    have hsplitTwo := Finset.card_sdiff_add_card_inter supportTwo supportOne
    have hcomm : (supportTwo ∩ supportOne).card
        = (supportOne ∩ supportTwo).card := by
      rw [Finset.inter_comm]
    omega
  obtain ⟨atomX, hXeq⟩ := Finset.card_eq_one.mp hsdiffOne
  obtain ⟨atomY, hYeq⟩ := Finset.card_eq_one.mp hsdiffTwo
  have hXmem : atomX ∈ supportOne \ supportTwo := by
    rw [hXeq]; exact Finset.mem_singleton_self _
  have hYmem : atomY ∈ supportTwo \ supportOne := by
    rw [hYeq]; exact Finset.mem_singleton_self _
  rw [Finset.mem_sdiff] at hXmem hYmem
  have hXinOne : atomX ∈ supportOne := hXmem.1
  have hXoutTwo : atomX ∉ supportTwo := hXmem.2
  have hYinTwo : atomY ∈ supportTwo := hYmem.1
  have hYoutOne : atomY ∉ supportOne := hYmem.2
  have hAinter : atomA ∈ supportOne ∩ supportTwo := by
    rw [hinterEq]; simp
  have hBinter : atomB ∈ supportOne ∩ supportTwo := by
    rw [hinterEq]; simp
  have hAX : atomA ≠ atomX := fun heq =>
    hXoutTwo (heq ▸ (Finset.mem_inter.mp hAinter).2)
  have hBX : atomB ≠ atomX := fun heq =>
    hXoutTwo (heq ▸ (Finset.mem_inter.mp hBinter).2)
  have hAY : atomA ≠ atomY := fun heq =>
    hYoutOne (heq ▸ (Finset.mem_inter.mp hAinter).1)
  have hBY : atomB ≠ atomY := fun heq =>
    hYoutOne (heq ▸ (Finset.mem_inter.mp hBinter).1)
  have hXY : atomX ≠ atomY := fun heq => hYoutOne (heq ▸ hXinOne)
  have htripleCardOne : ({atomA, atomB, atomX} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hAB, hAX]),
      Finset.card_insert_of_notMem (by simp [hBX]), Finset.card_singleton]
  have htripleCardTwo : ({atomA, atomB, atomY} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hAB, hAY]),
      Finset.card_insert_of_notMem (by simp [hBY]), Finset.card_singleton]
  have hsupportOneEq : supportOne = {atomA, atomB, atomX} := by
    refine (Finset.eq_of_subset_of_card_le ?_
      (by rw [hcardOne, htripleCardOne])).symm
    intro probe hprobe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hprobe
    rcases hprobe with heq | heq | heq
    · exact heq ▸ (Finset.mem_inter.mp hAinter).1
    · exact heq ▸ (Finset.mem_inter.mp hBinter).1
    · exact heq ▸ hXinOne
  have hsupportTwoEq : supportTwo = {atomA, atomB, atomY} := by
    refine (Finset.eq_of_subset_of_card_le ?_
      (by rw [hcardTwo, htripleCardTwo])).symm
    intro probe hprobe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hprobe
    rcases hprobe with heq | heq | heq
    · exact heq ▸ (Finset.mem_inter.mp hAinter).2
    · exact heq ▸ (Finset.mem_inter.mp hBinter).2
    · exact heq ▸ hYinTwo
  refine hsplit crux data label hmem hpos slotOne slotTwo hne hcoeffOne
    hcoeffTwo hpair atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY
    hsupportOneEq hsupportTwoEq ?_ ?_
  · have hzero := data.basis_dead_of_notMem_support (slot := slotTwo) hXoutTwo
    rw [chart_tight_row_of_capture_zero
      (data.pairCircuit_capture_eq_zero hmem hpos hne hcoeffOne hcoeffTwo hpair
        hXinOne hXoutTwo) hzero, hzero, mul_zero]
  · have hzero := data.basis_dead_of_notMem_support (slot := slotOne) hYoutOne
    rw [chart_tight_row_of_capture_zero
      (data.pairCircuit_capture_eq_zero hmem hpos (Ne.symm hne) hcoeffTwo
        hcoeffOne (fun slot htwoNe honeNe => hpair slot honeNe htwoNe)
        hYinTwo hYoutOne) hzero, hzero, mul_zero]

end SharedPrivateData

/-! ## Layer 12 — the generic kill on three residues -/

/-- **THE GENERIC KILL ON THREE RESIDUES.**  The identical residue leaves
the lattice: the fold closes the support-paired stratum, and the split
and wide residues close the rest. -/
theorem sharedPrivateKilled_of_foldLattice
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateKilled := by
  classical
  intro crux data
  have hsplitBasic : SharedPrivateCircuitPairSplitClosed :=
    sharedPrivateCircuitPairSplitClosed_of_wedge
      (sharedPrivateCircuitSplitWedgeClosed_of_slotSplit
        (sharedPrivateCircuitSplitWedgeSlotClosed_of_count
          (sharedPrivateCircuitSplitWedgeCountClosed_of_impure hwedgeLive)))
      (sharedPrivateCircuitSplitPairClosed_of_saturated hwedgeDead)
  by_cases hpaired : ∀ slotA slotB : Fin data.basisCount, slotA ≠ slotB →
      data.gram slotA slotB ≠ 0 →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = datumTightSupport data.tightDir (data.basisLabel slotA)
  · exact data.false_of_supportPaired_gram hpaired
  · push Not at hpaired
    obtain ⟨slotA, slotB, hab, hgram, hdiff⟩ := hpaired
    obtain ⟨label, hmem, hpos, hcoeffA, hcoeffB⟩ :=
      data.exists_label_of_gram_ne_zero hgram
    by_cases hthird : ∃ slotC : Fin data.basisCount,
        slotC ≠ slotA ∧ slotC ≠ slotB ∧ data.labelCoeff label slotC ≠ 0
    · obtain ⟨slotC, hCA, hCB, hcoeffC⟩ := hthird
      exact hwide crux data label hmem hpos slotA slotB slotC hab
        (Ne.symm hCA) (Ne.symm hCB) hcoeffA hcoeffB hcoeffC
        fun hsame => hdiff hsame.1
    · push Not at hthird
      exact data.false_of_pair_label_of_support_ne hsplitBasic hmem hpos hab
        hcoeffA hcoeffB (fun slot honeNe htwoNe => hthird slot honeNe htwoNe)
        hdiff

/-- Closure two of the rank-four rung on the three residues. -/
theorem rankFourSharedPrivateClosed_of_foldLattice
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_foldLattice hwedgeLive hwedgeDead hwide)

/-- The shared-private closure of the rank-five rung on the three
residues. -/
theorem rankFiveSharedPrivateClosed_of_foldLattice
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_foldLattice hwedgeLive hwedgeDead hwide)

/-- The shared-private closure of the rank-six rung on the three
residues. -/
theorem rankSixSharedPrivateClosed_of_foldLattice
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_foldLattice hwedgeLive hwedgeDead hwide)

/-! ## Layer 13 — the capture diagonal law of the Gram core -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

set_option maxHeartbeats 6400000 in
/-- **THE CAPTURE DIAGONAL LAW.**  The captured Gram core reads the
captured diagonal over six at every atom.  The assembly is a mixture of
tight support-confined directions, thus the capture diagonal is pinned —
the law the free-core probes never enforced. -/
theorem captureGram_diagonal_eq (data : SharedPrivateData crux)
    (atomIndex : Fin 6) :
    (tightBasisColumns data.tightDir data.basisLabel
        * (data.coeff * data.gram)
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ)
      atomIndex atomIndex
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * ((6 : ℝ))⁻¹ := by
  have hstep : tightBasisColumns data.tightDir data.basisLabel
        * (data.coeff * data.gram)
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ
      = (chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly data.activeSet data.reducedWeight
          data.tightDir := by
    calc tightBasisColumns data.tightDir data.basisLabel
          * (data.coeff * data.gram)
          * (tightBasisColumns data.tightDir data.basisLabel)ᵀ
        = tightBasisColumns data.tightDir data.basisLabel * data.coeff
          * data.gram
          * (tightBasisColumns data.tightDir data.basisLabel)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (chartPointOfDesign crux.design).chart
          * (tightBasisColumns data.tightDir data.basisLabel * data.gram
            * (tightBasisColumns data.tightDir data.basisLabel)ᵀ) := by
          rw [← data.hrepresentation]
          simp only [Matrix.mul_assoc]
      _ = (chartPointOfDesign crux.design).chart
          * chartMultiplierAssembly data.activeSet data.reducedWeight
            data.tightDir := by
          rw [data.hHform]
  rw [hstep]
  exact diagonal_projection_mul_multiplier_of_isChartStationaryData
    data.hdata atomIndex

set_option maxHeartbeats 6400000 in
/-- **THE DEAD-LEAK ORTHOGONALITY.**  The shadow defect of an atom is
Gram-orthogonal to the atom's own basis row: the capture diagonal law
minus the captured multiple of the assembly diagonal. -/
theorem deadLeak_orthogonal (data : SharedPrivateData crux)
    (atomIndex : Fin 6) :
    ∑ slotOut, ∑ slotIn,
      (data.rowShadow atomIndex slotOut
          - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir (data.basisLabel slotOut) atomIndex)
        * data.gram slotOut slotIn
        * data.tightDir (data.basisLabel slotIn) atomIndex = 0 := by
  classical
  have hcapture := data.captureGram_diagonal_eq atomIndex
  have hassembly : (tightBasisColumns data.tightDir data.basisLabel
        * data.gram
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ)
      atomIndex atomIndex = ((6 : ℝ))⁻¹ := by
    rw [data.hHform]
    exact data.hdata.assembly_diagonal atomIndex
  have hshadow : ∀ slotOut : Fin data.basisCount,
      (tightBasisColumns data.tightDir data.basisLabel * data.coeff)
        atomIndex slotOut = data.rowShadow atomIndex slotOut := by
    intro slotOut
    rw [Matrix.mul_apply, rowShadow]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have hcaptureSum : (tightBasisColumns data.tightDir data.basisLabel
        * (data.coeff * data.gram)
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ)
      atomIndex atomIndex
      = ∑ slotOut, ∑ slotIn, data.rowShadow atomIndex slotOut
          * data.gram slotOut slotIn
          * data.tightDir (data.basisLabel slotIn) atomIndex := by
    rw [show tightBasisColumns data.tightDir data.basisLabel
        * (data.coeff * data.gram)
      = tightBasisColumns data.tightDir data.basisLabel * data.coeff
        * data.gram from (Matrix.mul_assoc _ _ _).symm]
    rw [Matrix.mul_apply]
    calc ∑ slotIn, (tightBasisColumns data.tightDir data.basisLabel
          * data.coeff * data.gram) atomIndex slotIn
          * (tightBasisColumns data.tightDir data.basisLabel)ᵀ slotIn atomIndex
        = ∑ slotIn, ∑ slotOut, data.rowShadow atomIndex slotOut
            * data.gram slotOut slotIn
            * data.tightDir (data.basisLabel slotIn) atomIndex := by
          refine Finset.sum_congr rfl fun slotIn _ => ?_
          rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun slotOut _ => ?_
          rw [hshadow slotOut]
          rfl
      _ = ∑ slotOut, ∑ slotIn, data.rowShadow atomIndex slotOut
            * data.gram slotOut slotIn
            * data.tightDir (data.basisLabel slotIn) atomIndex :=
          Finset.sum_comm
  have hassemblySum : (tightBasisColumns data.tightDir data.basisLabel
        * data.gram
        * (tightBasisColumns data.tightDir data.basisLabel)ᵀ)
      atomIndex atomIndex
      = ∑ slotOut, ∑ slotIn,
          data.tightDir (data.basisLabel slotOut) atomIndex
            * data.gram slotOut slotIn
            * data.tightDir (data.basisLabel slotIn) atomIndex := by
    rw [Matrix.mul_apply]
    calc ∑ slotIn, (tightBasisColumns data.tightDir data.basisLabel
          * data.gram) atomIndex slotIn
          * (tightBasisColumns data.tightDir data.basisLabel)ᵀ slotIn atomIndex
        = ∑ slotIn, ∑ slotOut,
            data.tightDir (data.basisLabel slotOut) atomIndex
              * data.gram slotOut slotIn
              * data.tightDir (data.basisLabel slotIn) atomIndex := by
          refine Finset.sum_congr rfl fun slotIn _ => ?_
          rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun slotOut _ => ?_
          rfl
      _ = ∑ slotOut, ∑ slotIn,
            data.tightDir (data.basisLabel slotOut) atomIndex
              * data.gram slotOut slotIn
              * data.tightDir (data.basisLabel slotIn) atomIndex :=
          Finset.sum_comm
  have hsplit : ∑ slotOut, ∑ slotIn,
      (data.rowShadow atomIndex slotOut
          - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
            * data.tightDir (data.basisLabel slotOut) atomIndex)
        * data.gram slotOut slotIn
        * data.tightDir (data.basisLabel slotIn) atomIndex
      = (∑ slotOut, ∑ slotIn, data.rowShadow atomIndex slotOut
          * data.gram slotOut slotIn
          * data.tightDir (data.basisLabel slotIn) atomIndex)
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * ∑ slotOut, ∑ slotIn,
              data.tightDir (data.basisLabel slotOut) atomIndex
                * data.gram slotOut slotIn
                * data.tightDir (data.basisLabel slotIn) atomIndex := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun slotOut _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun slotIn _ => ?_
    ring
  rw [hsplit, ← hcaptureSum, ← hassemblySum, hcapture, hassembly]
  ring

end SharedPrivateData

end Gtz

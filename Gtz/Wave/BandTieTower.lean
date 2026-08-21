/-
# The tie tower: exact boundary systems at every cell of every rank

`Skeleton.obligationSubThresholdBandHinge` and
`Skeleton.obligationThresholdCellHingeRankFourAndUp` both say the same thing at
their own cells: an exact tie carries a parallel pair.  The band axiom's STATUS
field reads "no evidence", and its WHY OPEN field says no producer exists at any
rank.  This module supplies the two facts that a producer needs first, and both
are new at general rank.

## 1. The hinge is FALSE at size `rank + 1`, at EVERY rank

WHAT IS ALREADY IN THE TREE, AND WHAT IS NEW.  `Gtz.simplexTieDesign`
(Gtz/Ties/CorankOneTieExistence.lean) already inhabits this cell, and at EVERY
weight vector rather than only at the uniform one: `Gtz.exists_isTie_of_weights`
and `Gtz.corank_one_tie_stratum` say the corank-one tie stratum is a section over
the whole open weight simplex.  That construction runs through a Householder
reflection, and NOTHING in the tree records whether its atoms are pairwise
non-parallel.  The parallel-free half is what refutes the hinge, and it is the
new content here.  `Gtz.flatSimplexDesign` below is the uniform member written in
explicit coordinates, which is what makes the parallel-free check one line per
case.  Its `IsTie` half duplicates nothing that is stated -- the landed statement
is about a different construction -- and its existence content is superseded by
`Gtz.exists_isTie_of_weights`, which is stronger.

`Gtz.flatSimplexDesign` is an explicit weighted design of size `rank + 1` and
rank `rank`.  Its atoms are

  `g_i = p · e_i + q · 1` for `i < rank`,   `g_last = 1` ,

with `p = √(rank + 1)` and `q = (1 - p) / rank`.  Every atom has leverage
exactly `rank`, the unweighted atom total is `(rank + 1) · I`, and every
`rank`-subset is the complement of one label.  So the gap of every selection is
`rank · I - g_j g_jᵀ`, which is positive semidefinite by Cauchy-Schwarz and
singular at `g_j`.  Every selection dominates, and none dominates strictly:
the design is an exact tie, and its atoms are pairwise non-parallel.

  **`Gtz.not_hingeHoldsAtSize_succ_rank`: `¬ Gtz.HingeHoldsAtSize (rank + 1) rank`
  for every `rank ≥ 3`.**

The campaign carried this only at rank three, as `Gtz.not_hingeHoldsAtSize_four_three`
(size four) and `Gtz.not_hingeHoldsAtSize_five_three` (size five, the diamond).
Both are single cells.  The family above makes the refutation rank-uniform and
pins the band's lower guard from below: a band statement that reached down to
size `rank + 1` would be false at every rank, and `rank + 1 < 2 * rank` holds for
every `rank ≥ 2`.

## 2. The duplicate split, and the tie tower

`Gtz.duplicateSplitDesign D label share` appends a second copy of one atom and
divides that atom's weight in the ratio `share : 1 - share`.  Domination
transfers in BOTH directions and in BOTH strengths, because a selection that
takes the two copies together is rank deficient and dominates nothing:

  **`Gtz.isTie_duplicateSplitDesign_iff`: the split of a design is a tie exactly
  when the design is a tie.**

Iterating the split from the simplex tie of part 1 gives

  **`Gtz.exists_isTie_of_succ_rank_le`: at every rank `≥ 3` and every size
  `≥ rank + 1` there is an exact tie.**

So the two registry axioms quantify over an INHABITED stratum at every cell of
every rank -- the band cells `(8,4)` and `(9,4)`, the threshold cell `(10,4)`,
and every cell above.  A proof of either axiom can therefore never run through
"this cell holds no tie":

  **`Gtz.not_forall_not_isTie`: the empty-cell route is dead at every cell.**

## 3. The strict merge pullback, and descent

`Gtz.exists_dominating_of_mergedParallel_dominates` (Gtz/Reduction/SplitTransfer.lean)
lifts a WEAK dominator of the merged design.  The STRICT lift was missing, and it
is what turns the hinge into a descent law:

  **`Gtz.isTie_mergedParallelDesign`: a tie that carries a parallel pair merges to
  a tie one size down.**
  **`Gtz.exists_isTie_pred_of_hinge`: at a cell where the hinge holds, every tie
  descends to a tie at the cell below.**

## 4. What the numerics say, recorded here because it selected the targets

Searched in the projection chart at a hard collinearity floor `cos² ≤ 1 - ε`, over
800 restarts for each cell, the parallel-free tie locus is nonempty exactly below
size `2 * rank`.  Exact ties found with a parallel-free constraint: `(4,3)` and
`(5,3)` at rank three, `(5,4)`, `(6,4)` and `(7,4)` at rank four.  At `(6,3)`,
`(8,4)` and `(9,4)` the same search stalls three to four orders of magnitude above
zero while the collinearity constraint stays INACTIVE, and every one of the 876
exact ties found there without the constraint carries an exactly collinear pair.
Refer to scratchpad/NOTES-rankfour-exact.txt.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Reduction.SplitTransfer
import Gtz.Quantitative.SevenThreeNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 0. Rank deficiency kills domination

A selection whose atoms span less than the full rank has a singular atom sum, so
its gap reads one direction at `-1` and cannot be positive semidefinite.  Both
producers of a null direction below are rank-free. -/

/-- **A COMMON NULL DIRECTION REFUTES DOMINATION.**  If one nonzero direction is
orthogonal to every selected atom, the gap of that selection reads it at minus
its own square. -/
theorem not_dominates_of_exists_null (D : WeightedDesign m k) (C : Finset (Fin m))
    {probe : Fin k → ℝ} (hne : probe ≠ 0) (hnull : ∀ c ∈ C, D.atom c ⬝ᵥ probe = 0) :
    ¬ Dominates D C := by
  intro hdom
  have hvalue : probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) = -(probe ⬝ᵥ probe) := by
    have hexpand : subsetSum D C *ᵥ probe = ∑ c ∈ C, (atomMatrix (D.atom c) *ᵥ probe) := by
      funext coord
      simp only [subsetSum, Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply,
        Finset.sum_mul]
      exact Finset.sum_comm
    have hatoms : subsetSum D C *ᵥ probe = 0 := by
      rw [hexpand]
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [atomMatrix, vecMulVec_mulVec_eq, hnull c hc, zero_smul]
    rw [Matrix.sub_mulVec, hatoms, Matrix.one_mulVec, dotProduct_sub, dotProduct_zero, zero_sub]
  have hnonneg : 0 ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 probe
    rwa [star_trivial] at h
  have hpos : 0 < probe ⬝ᵥ probe := by
    rcases (dotProduct_self_nonneg probe).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (dotProduct_self_eq_zero.mp heq.symm) hne
  rw [hvalue] at hnonneg
  linarith

/-- **FEWER ATOMS THAN THE RANK LEAVE A NULL DIRECTION.**  Any family indexed by a
finset of card below the rank misses a direction.  The witness is the kernel of a
square matrix that carries a zero row. -/
theorem exists_null_of_card_lt {S : Finset (Fin m)} (vectors : Fin m → (Fin k → ℝ))
    (hsmall : S.card < k) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧ ∀ c ∈ S, vectors c ⬝ᵥ probe = 0 := by
  classical
  have hcardpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hsmall
  -- enumerate `S` by its order embedding, padded by zero rows
  set enumerate : Fin S.card → Fin m := ⇑(S.orderEmbOfFin rfl) with henumerate
  set rows : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun slot coord =>
      if hslot : (slot : ℕ) < S.card then vectors (enumerate ⟨slot, hslot⟩) coord else 0
    with hrows
  have hzeroRow : rows ⟨S.card, hsmall⟩ = 0 := by
    funext coord
    simp only [hrows, Matrix.of_apply, Matrix.zero_apply]
    exact dif_neg (lt_irrefl _)
  have hdet : rows.det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨S.card, hsmall⟩ (by
    intro coord; exact congrFun hzeroRow coord)
  obtain ⟨probe, hprobeNe, hprobeNull⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine ⟨probe, hprobeNe, ?_⟩
  intro c hc
  obtain ⟨slot, hslot⟩ : ∃ slot : Fin S.card, enumerate slot = c := by
    have hmem : c ∈ Set.range enumerate := by
      rw [henumerate, Finset.range_orderEmbOfFin]
      exact hc
    obtain ⟨slot, hslot⟩ := hmem
    exact ⟨slot, hslot⟩
  have hlift : ((⟨slot, lt_of_lt_of_le slot.isLt hsmall.le⟩ : Fin k) : ℕ) < S.card := slot.isLt
  have hrow := congrFun hprobeNull (⟨slot, lt_of_lt_of_le slot.isLt hsmall.le⟩ : Fin k)
  simp only [Matrix.mulVec, dotProduct, hrows, Matrix.of_apply, Pi.zero_apply] at hrow
  rw [← hslot]
  have hcongr : ∀ coord : Fin k,
      (if hcond : (((⟨slot, lt_of_lt_of_le slot.isLt hsmall.le⟩ : Fin k) : ℕ) < S.card) then
        vectors (enumerate ⟨(⟨slot, lt_of_lt_of_le slot.isLt hsmall.le⟩ : Fin k), hcond⟩) coord
        else 0) * probe coord
      = vectors (enumerate slot) coord * probe coord := by
    intro coord
    rw [dif_pos hlift]
  rw [dotProduct]
  rw [← hrow]
  exact (Finset.sum_congr rfl fun coord _ => (hcongr coord).symm)

/-- **A PARALLEL PAIR INSIDE A SELECTION LEAVES A NULL DIRECTION.**  The square
matrix of the selected atoms carries two proportional rows, so its determinant
vanishes and its kernel is nonzero. -/
theorem exists_null_of_parallel_within (D : WeightedDesign m k) {C : Finset (Fin m)}
    (hcard : C.card = k) {keptLabel dropLabel : Fin m} (hkept : keptLabel ∈ C)
    (hdrop : dropLabel ∈ C) (hdistinct : keptLabel ≠ dropLabel) {ratio : ℝ}
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧ ∀ c ∈ C, D.atom c ⬝ᵥ probe = 0 := by
  classical
  set enumerate : Fin k → Fin m := ⇑(C.orderEmbOfFin hcard) with henumerate
  have hinjective : Function.Injective enumerate := (C.orderEmbOfFin hcard).injective
  have hrange : ∀ c ∈ C, ∃ slot : Fin k, enumerate slot = c := by
    intro c hc
    have hmem : c ∈ Set.range enumerate := by
      rw [henumerate, Finset.range_orderEmbOfFin]; exact hc
    obtain ⟨slot, hslot⟩ := hmem
    exact ⟨slot, hslot⟩
  obtain ⟨keptSlot, hkeptSlot⟩ := hrange keptLabel hkept
  obtain ⟨dropSlot, hdropSlot⟩ := hrange dropLabel hdrop
  have hslotDistinct : keptSlot ≠ dropSlot := by
    intro hEq
    exact hdistinct (by rw [← hkeptSlot, ← hdropSlot, hEq])
  set rows : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun slot coord => D.atom (enumerate slot) coord
    with hrows
  have hrowsParallel : rows dropSlot = ratio • rows keptSlot := by
    funext coord
    simp only [hrows, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [hdropSlot, hkeptSlot]
    exact congrFun hparallel coord
  have hupdate : rows = rows.updateRow dropSlot (ratio • rows keptSlot) := by
    rw [← hrowsParallel, Matrix.updateRow_eq_self]
  have hdet : rows.det = 0 := by
    have hscaled : (rows.updateRow dropSlot (ratio • rows keptSlot)).det
        = ratio * (rows.updateRow dropSlot (rows keptSlot)).det :=
      Matrix.det_updateRow_smul _ _ _ _
    have hrepeat : (rows.updateRow dropSlot (rows keptSlot)).det = 0 := by
      refine Matrix.det_zero_of_row_eq hslotDistinct.symm ?_
      rw [Matrix.updateRow_self, Matrix.updateRow_ne hslotDistinct]
    rw [hupdate, hscaled, hrepeat, mul_zero]
  obtain ⟨probe, hprobeNe, hprobeNull⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine ⟨probe, hprobeNe, ?_⟩
  intro c hc
  obtain ⟨slot, hslot⟩ := hrange c hc
  have hrow := congrFun hprobeNull slot
  simp only [Matrix.mulVec, hrows, Matrix.of_apply, Pi.zero_apply] at hrow
  rw [← hslot, dotProduct]
  exact hrow

/-- **A SELECTION THAT REPEATS A DIRECTION DOMINATES NOTHING.**  Rank-free, at any
size and any rank: a `rank`-subset that carries a parallel pair never dominates. -/
theorem not_dominates_of_parallel_within (D : WeightedDesign m k) {C : Finset (Fin m)}
    (hcard : C.card = k) {keptLabel dropLabel : Fin m} (hkept : keptLabel ∈ C)
    (hdrop : dropLabel ∈ C) (hdistinct : keptLabel ≠ dropLabel) {ratio : ℝ}
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) :
    ¬ Dominates D C := by
  obtain ⟨probe, hne, hnull⟩ :=
    exists_null_of_parallel_within D hcard hkept hdrop hdistinct hparallel
  exact not_dominates_of_exists_null D C hne hnull

/-! ## 1. The simplex tie: an exact parallel-free boundary system at `(rank + 1, rank)`

The atoms are `g_i = p · e_i + q · 1` for `i < rank` and `g_last = 1`, with
`p = √(rank + 1)` and `q = (1 - p) / rank`.  The single scalar identity
`2 p q + rank q² + 1 = 0` drives every computation below. -/

/-- The scale of the simplex tie, `p = √(rank + 1)`. -/
noncomputable def flatSimplexScale (rank : ℕ) : ℝ := Real.sqrt ((rank : ℝ) + 1)

/-- The shift of the simplex tie, `q = (1 - p) / rank`. -/
noncomputable def flatSimplexShift (rank : ℕ) : ℝ := (1 - flatSimplexScale rank) / (rank : ℝ)

/-- The atoms of the simplex tie. -/
noncomputable def flatSimplexAtom (rank : ℕ) : Fin (rank + 1) → (Fin rank → ℝ) :=
  Fin.snoc
    (fun axis : Fin rank => fun coord : Fin rank =>
      (if coord = axis then flatSimplexScale rank else 0) + flatSimplexShift rank)
    (fun _ : Fin rank => (1 : ℝ))

theorem flatSimplexAtom_castSucc (rank : ℕ) (axis coord : Fin rank) :
    flatSimplexAtom rank (Fin.castSucc axis) coord
      = (if coord = axis then flatSimplexScale rank else 0) + flatSimplexShift rank := by
  rw [flatSimplexAtom, Fin.snoc_castSucc]

theorem flatSimplexAtom_last (rank : ℕ) (coord : Fin rank) :
    flatSimplexAtom rank (Fin.last rank) coord = 1 := by
  rw [flatSimplexAtom, Fin.snoc_last]

theorem flatSimplexScale_sq (rank : ℕ) : flatSimplexScale rank ^ 2 = (rank : ℝ) + 1 :=
  Real.sq_sqrt (by positivity)

theorem one_lt_flatSimplexScale {rank : ℕ} (hrank : 0 < rank) : 1 < flatSimplexScale rank := by
  have hcast : (1 : ℝ) < (rank : ℝ) + 1 := by
    have hpos : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
    linarith
  have hstep := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hcast
  rwa [Real.sqrt_one] at hstep

theorem flatSimplexShift_neg {rank : ℕ} (hrank : 0 < rank) : flatSimplexShift rank < 0 := by
  have hscale := one_lt_flatSimplexScale hrank
  have hcast : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
  rw [flatSimplexShift]
  exact div_neg_of_neg_of_pos (by linarith) hcast

theorem flatSimplexShift_ne_zero {rank : ℕ} (hrank : 0 < rank) : flatSimplexShift rank ≠ 0 :=
  ne_of_lt (flatSimplexShift_neg hrank)

/-- **THE SCALAR IDENTITY OF THE SIMPLEX TIE.**  Everything below is this one line
read at a different place. -/
theorem flatSimplex_key {rank : ℕ} (hrank : 0 < rank) :
    2 * flatSimplexScale rank * flatSimplexShift rank
      + (rank : ℝ) * flatSimplexShift rank ^ 2 + 1 = 0 := by
  have hcast : ((rank : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hrank.ne'
  have hsq := flatSimplexScale_sq rank
  rw [flatSimplexShift]
  field_simp
  nlinarith [hsq]

/-! ### The Gram of the simplex atoms -/

/-- **THE UNWEIGHTED GRAM IS `(rank + 1)` TIMES THE IDENTITY.**  The atoms form a
tight frame, and the scalar identity is exactly what cancels the off-diagonal. -/
theorem flatSimplexAtom_gram {rank : ℕ} (hrank : 0 < rank) (rowCoord colCoord : Fin rank) :
    ∑ label : Fin (rank + 1),
        flatSimplexAtom rank label rowCoord * flatSimplexAtom rank label colCoord
      = if rowCoord = colCoord then ((rank : ℝ) + 1) else 0 := by
  classical
  have hexpand : ∀ axis : Fin rank,
      flatSimplexAtom rank (Fin.castSucc axis) rowCoord
          * flatSimplexAtom rank (Fin.castSucc axis) colCoord
        = (if rowCoord = axis then flatSimplexScale rank else 0)
            * (if colCoord = axis then flatSimplexScale rank else 0)
          + (flatSimplexShift rank * (if rowCoord = axis then flatSimplexScale rank else 0)
            + flatSimplexShift rank * (if colCoord = axis then flatSimplexScale rank else 0))
          + flatSimplexShift rank ^ 2 := by
    intro axis
    rw [flatSimplexAtom_castSucc, flatSimplexAtom_castSucc]
    ring
  have hcross : ∑ axis : Fin rank,
      (if rowCoord = axis then flatSimplexScale rank else 0)
        * (if colCoord = axis then flatSimplexScale rank else 0)
      = if rowCoord = colCoord then flatSimplexScale rank ^ 2 else 0 := by
    by_cases hsame : rowCoord = colCoord
    · subst hsame
      have hpoint : ∀ axis : Fin rank,
          (if rowCoord = axis then flatSimplexScale rank else 0)
            * (if rowCoord = axis then flatSimplexScale rank else 0)
          = if axis = rowCoord then flatSimplexScale rank ^ 2 else 0 := by
        intro axis
        by_cases haxis : rowCoord = axis
        · simp [haxis, pow_two]
        · simp [haxis, Ne.symm haxis]
      rw [Finset.sum_congr rfl fun axis _ => hpoint axis, Finset.sum_ite_eq' Finset.univ rowCoord]
      simp
    · have hpoint : ∀ axis : Fin rank,
          (if rowCoord = axis then flatSimplexScale rank else 0)
            * (if colCoord = axis then flatSimplexScale rank else 0) = 0 := by
        intro axis
        by_cases haxis : rowCoord = axis
        · have : colCoord ≠ axis := fun hc => hsame (haxis.trans hc.symm)
          simp [haxis, this]
        · simp [haxis]
      rw [Finset.sum_congr rfl fun axis _ => hpoint axis, Finset.sum_const_zero, if_neg hsame]
  have hlinear : ∀ target : Fin rank,
      ∑ axis : Fin rank, flatSimplexShift rank * (if target = axis then flatSimplexScale rank else 0)
        = flatSimplexShift rank * flatSimplexScale rank := by
    intro target
    rw [← Finset.mul_sum]
    have hpoint : ∀ axis : Fin rank,
        (if target = axis then flatSimplexScale rank else 0)
          = if axis = target then flatSimplexScale rank else 0 := by
      intro axis; by_cases haxis : target = axis
      · simp [haxis]
      · simp [haxis, Ne.symm haxis]
    rw [Finset.sum_congr rfl fun axis _ => hpoint axis, Finset.sum_ite_eq' Finset.univ target]
    simp
  rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl fun axis _ => hexpand axis,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hcross, hlinear rowCoord, hlinear colCoord, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, flatSimplexAtom_last, flatSimplexAtom_last]
  have hkey := flatSimplex_key hrank
  by_cases hsame : rowCoord = colCoord
  · rw [if_pos hsame, if_pos hsame, flatSimplexScale_sq]
    linarith
  · rw [if_neg hsame, if_neg hsame]
    linarith

/-! ### The design -/

/-- **THE SIMPLEX TIE**, an exact weighted design of size `rank + 1` and rank
`rank` at uniform weight. -/
noncomputable def flatSimplexDesign (rank : ℕ) (hrank : 0 < rank) :
    WeightedDesign (rank + 1) rank where
  atom := flatSimplexAtom rank
  weight := fun _ => 1 / ((rank : ℝ) + 1)
  weight_pos := fun _ => by positivity
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  isParseval := by
    ext rowCoord colCoord
    rw [Matrix.sum_apply]
    have hpoint : ∀ label : Fin (rank + 1),
        ((1 / ((rank : ℝ) + 1)) • atomMatrix (flatSimplexAtom rank label)) rowCoord colCoord
          = (1 / ((rank : ℝ) + 1))
            * (flatSimplexAtom rank label rowCoord * flatSimplexAtom rank label colCoord) := by
      intro label
      rw [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun label _ => hpoint label, ← Finset.mul_sum,
      flatSimplexAtom_gram hrank]
    have hne : ((rank : ℝ) + 1) ≠ 0 := by positivity
    by_cases hsame : rowCoord = colCoord
    · rw [if_pos hsame, hsame, Matrix.one_apply_eq]
      field_simp
    · rw [if_neg hsame, Matrix.one_apply_ne hsame]
      ring

theorem flatSimplexDesign_atom (rank : ℕ) (hrank : 0 < rank) :
    (flatSimplexDesign rank hrank).atom = flatSimplexAtom rank := rfl

/-- **EVERY ATOM OF THE SIMPLEX TIE HAS LEVERAGE EXACTLY `rank`.** -/
theorem leverageOf_flatSimplexAtom {rank : ℕ} (hrank : 0 < rank) (label : Fin (rank + 1)) :
    leverageOf (flatSimplexAtom rank label) = (rank : ℝ) := by
  have hgram := flatSimplexAtom_gram hrank
  have hself : ∀ coord : Fin rank,
      flatSimplexAtom rank label coord ^ 2
        = flatSimplexAtom rank label coord * flatSimplexAtom rank label coord := fun _ => pow_two _
  rw [leverageOf, Finset.sum_congr rfl fun coord _ => hself coord]
  -- read the diagonal of the Gram from the other side: sum over labels of the same product
  have hdiag : ∑ coord : Fin rank,
      flatSimplexAtom rank label coord * flatSimplexAtom rank label coord = (rank : ℝ) := by
    rcases Fin.eq_castSucc_or_eq_last label with ⟨axis, rfl⟩ | rfl
    · have hexpand : ∀ coord : Fin rank,
          flatSimplexAtom rank (Fin.castSucc axis) coord
              * flatSimplexAtom rank (Fin.castSucc axis) coord
            = (if coord = axis then flatSimplexScale rank ^ 2 else 0)
              + 2 * flatSimplexShift rank * (if coord = axis then flatSimplexScale rank else 0)
              + flatSimplexShift rank ^ 2 := by
        intro coord
        rw [flatSimplexAtom_castSucc]
        by_cases hcoord : coord = axis
        · simp [hcoord]; ring
        · simp [hcoord]; ring
      rw [Finset.sum_congr rfl fun coord _ => hexpand coord, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ axis, ← Finset.mul_sum,
        Finset.sum_ite_eq' Finset.univ axis, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [Finset.mem_univ, if_true]
      rw [flatSimplexScale_sq]
      have hkey := flatSimplex_key hrank
      linarith
    · have hone : ∀ coord : Fin rank,
          flatSimplexAtom rank (Fin.last rank) coord * flatSimplexAtom rank (Fin.last rank) coord
            = (1 : ℝ) := by
        intro coord
        rw [flatSimplexAtom_last, mul_one]
      rw [Finset.sum_congr rfl fun coord _ => hone coord, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact hdiag

/-! ### The simplex design is an exact tie with no parallel pair -/

/-- The unweighted atom total of the simplex tie is `(rank + 1)` times the
identity. -/
theorem flatSimplexAtom_sum {rank : ℕ} (hrank : 0 < rank) :
    ∑ label : Fin (rank + 1), atomMatrix (flatSimplexAtom rank label)
      = ((rank : ℝ) + 1) • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
  ext rowCoord colCoord
  rw [Matrix.sum_apply]
  have hpoint : ∀ label : Fin (rank + 1),
      atomMatrix (flatSimplexAtom rank label) rowCoord colCoord
        = flatSimplexAtom rank label rowCoord * flatSimplexAtom rank label colCoord := by
    intro label
    rw [atomMatrix, Matrix.vecMulVec_apply]
  rw [Finset.sum_congr rfl fun label _ => hpoint label, flatSimplexAtom_gram hrank,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hsame : rowCoord = colCoord
  · rw [if_pos hsame, hsame, Matrix.one_apply_eq, mul_one]
  · rw [if_neg hsame, Matrix.one_apply_ne hsame, mul_zero]

/-- Every `rank`-subset of `Fin (rank + 1)` is the complement of one label. -/
theorem exists_erase_of_card_eq {ambient : ℕ} {selected : Finset (Fin (ambient + 1))}
    (hcard : selected.card = ambient) :
    ∃ missing : Fin (ambient + 1), selected = Finset.univ.erase missing := by
  classical
  have hcompl : selectedᶜ.card = 1 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
    omega
  obtain ⟨missing, hmissing⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨missing, ?_⟩
  have hback : selected = ({missing} : Finset (Fin (ambient + 1)))ᶜ := by
    rw [← hmissing, compl_compl]
  rw [hback, Finset.compl_singleton]

/-- The gap of every selection of the simplex tie is `rank · I - g_j g_jᵀ`. -/
theorem flatSimplexDesign_gap {rank : ℕ} (hrank : 0 < rank) (missing : Fin (rank + 1)) :
    subsetSum (flatSimplexDesign rank hrank) (Finset.univ.erase missing) - 1
      = (rank : ℝ) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - atomMatrix (flatSimplexAtom rank missing) := by
  have htotal : subsetSum (flatSimplexDesign rank hrank) (Finset.univ.erase missing)
      = ((rank : ℝ) + 1) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - atomMatrix (flatSimplexAtom rank missing) := by
    have hsplit : ∑ label ∈ Finset.univ.erase missing,
          atomMatrix (flatSimplexAtom rank label)
        + atomMatrix (flatSimplexAtom rank missing)
        = ∑ label : Fin (rank + 1), atomMatrix (flatSimplexAtom rank label) :=
      Finset.sum_erase_add _ _ (Finset.mem_univ missing)
    rw [subsetSum, flatSimplexDesign_atom, ← flatSimplexAtom_sum hrank, ← hsplit]
    abel
  rw [htotal]
  have hshift : ((rank : ℝ) + 1) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
      = (rank : ℝ) • (1 : Matrix (Fin rank) (Fin rank) ℝ) + 1 := by
    rw [add_smul, one_smul]
  rw [hshift]
  abel

/-- **EVERY SELECTION OF THE SIMPLEX TIE DOMINATES.**  Cauchy-Schwarz at leverage
exactly `rank`. -/
theorem flatSimplexDesign_dominates {rank : ℕ} (hrank : 0 < rank)
    {selected : Finset (Fin (rank + 1))} (hcard : selected.card = rank) :
    Dominates (flatSimplexDesign rank hrank) selected := by
  obtain ⟨missing, rfl⟩ := exists_erase_of_card_eq hcard
  rw [Dominates, flatSimplexDesign_gap hrank]
  exact posSemidef_smul_one_sub_atomMatrix_of_leverage_le
    (le_of_eq (leverageOf_flatSimplexAtom hrank missing))

/-- **NO SELECTION OF THE SIMPLEX TIE DOMINATES STRICTLY.**  The missing atom is
itself the null direction of the gap. -/
theorem flatSimplexDesign_not_posDef {rank : ℕ} (hrank : 0 < rank)
    {selected : Finset (Fin (rank + 1))} (hcard : selected.card = rank) :
    ¬ (subsetSum (flatSimplexDesign rank hrank) selected - 1).PosDef := by
  obtain ⟨missing, rfl⟩ := exists_erase_of_card_eq hcard
  intro hposDef
  set probe : Fin rank → ℝ := flatSimplexAtom rank missing with hprobe
  have hlev : leverageOf probe = (rank : ℝ) := leverageOf_flatSimplexAtom hrank missing
  have hdot : probe ⬝ᵥ probe = (rank : ℝ) := by
    rw [← hlev, leverageOf, dotProduct]
    exact Finset.sum_congr rfl fun coord _ => (pow_two (probe coord)).symm
  have hne : probe ≠ 0 := by
    intro hzero
    have hcast : (0 : ℝ) < (rank : ℝ) := by exact_mod_cast hrank
    rw [hzero] at hdot
    simp only [dotProduct_zero] at hdot
    linarith
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hposDef
  have hvalue := hposDef.2 hne
  rw [star_trivial, flatSimplexDesign_gap hrank, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_atomMatrix_mulVec, hdot] at hvalue
  nlinarith [hvalue]

/-- **THE SIMPLEX DESIGN IS AN EXACT TIE**, at every rank. -/
theorem flatSimplexDesign_isTie {rank : ℕ} (hrank : 0 < rank) :
    IsTie (flatSimplexDesign rank hrank) := by
  classical
  have hcardErase : (Finset.univ.erase (Fin.last rank)).card = rank := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  refine ⟨⟨Finset.univ.erase (Fin.last rank), hcardErase,
    flatSimplexDesign_dominates hrank hcardErase⟩, ?_⟩
  intro selected hcard
  exact flatSimplexDesign_not_posDef hrank hcard

/-- **THE SIMPLEX TIE CARRIES NO PARALLEL PAIR**, at every rank `≥ 3`. -/
theorem flatSimplexDesign_not_hasParallelPair {rank : ℕ} (hrank : 0 < rank) (hthree : 3 ≤ rank) :
    ¬ HasParallelPair (flatSimplexDesign rank hrank) := by
  classical
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  have hatomEq : ∀ coord : Fin rank,
      flatSimplexAtom rank dropLabel coord = ratio * flatSimplexAtom rank keptLabel coord := by
    intro coord
    have hstep := congrFun hparallel coord
    simpa [flatSimplexDesign_atom, Pi.smul_apply, smul_eq_mul] using hstep
  have hscale : 1 < flatSimplexScale rank := one_lt_flatSimplexScale hrank
  have hshiftNe : flatSimplexShift rank ≠ 0 := flatSimplexShift_ne_zero hrank
  -- a coordinate outside a two-element set exists because the rank is at least three
  have hthird : ∀ first second : Fin rank, ∃ other : Fin rank, other ≠ first ∧ other ≠ second := by
    intro first second
    have hnonempty : (({first, second} : Finset (Fin rank))ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      have hle : ({first, second} : Finset (Fin rank)).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      omega
    obtain ⟨other, hother⟩ := hnonempty
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hother
    exact ⟨other, hother.1, hother.2⟩
  rcases Fin.eq_castSucc_or_eq_last keptLabel with ⟨keptAxis, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last dropLabel with ⟨dropAxis, rfl⟩ | rfl
    · have haxisNe : dropAxis ≠ keptAxis := by
        intro haxis
        exact hdistinct (by rw [haxis])
      obtain ⟨other, hotherKept, hotherDrop⟩ := hthird keptAxis dropAxis
      have hAtOther := hatomEq other
      rw [flatSimplexAtom_castSucc, flatSimplexAtom_castSucc, if_neg hotherDrop,
        if_neg hotherKept] at hAtOther
      have hratio : ratio = 1 := by
        have hstep : flatSimplexShift rank * (ratio - 1) = 0 := by linear_combination -hAtOther
        rcases mul_eq_zero.mp hstep with hzero | hone
        · exact absurd hzero hshiftNe
        · linarith
      have hAtDrop := hatomEq dropAxis
      rw [flatSimplexAtom_castSucc, flatSimplexAtom_castSucc, if_pos rfl,
        if_neg haxisNe, hratio] at hAtDrop
      linarith
    · obtain ⟨other, hotherKept, _⟩ := hthird keptAxis keptAxis
      have hAtKept := hatomEq keptAxis
      have hAtOther := hatomEq other
      rw [flatSimplexAtom_last, flatSimplexAtom_castSucc, if_pos rfl] at hAtKept
      rw [flatSimplexAtom_last, flatSimplexAtom_castSucc, if_neg hotherKept] at hAtOther
      have hzero : ratio * flatSimplexScale rank = 0 := by linear_combination hAtOther - hAtKept
      rcases mul_eq_zero.mp hzero with hratioZero | hscaleZero
      · rw [hratioZero, zero_mul] at hAtOther
        linarith
      · linarith
  · rcases Fin.eq_castSucc_or_eq_last dropLabel with ⟨dropAxis, rfl⟩ | rfl
    · obtain ⟨other, hotherDrop, _⟩ := hthird dropAxis dropAxis
      have hAtDrop := hatomEq dropAxis
      have hAtOther := hatomEq other
      rw [flatSimplexAtom_castSucc, flatSimplexAtom_last, if_pos rfl, mul_one] at hAtDrop
      rw [flatSimplexAtom_castSucc, flatSimplexAtom_last, if_neg hotherDrop, mul_one] at hAtOther
      linarith
    · exact hdistinct rfl

/-- **THE HINGE IS FALSE AT SIZE `rank + 1`, AT EVERY RANK `≥ 3`.**  The campaign
carried this only at rank three, at the two single cells `(4,3)` and `(5,3)`.  The
family above makes the refutation rank-uniform.

CONSEQUENCE FOR THE REGISTRY.  `Skeleton.obligationSubThresholdBandHinge` guards
its size range from below by `2 * rank`.  That guard is NECESSARY at every rank:
`rank + 1 < 2 * rank` holds for every `rank ≥ 2`, so a band statement reaching
down to size `rank + 1` would be refuted here at every rank at once. -/
theorem not_hingeHoldsAtSize_succ_rank {rank : ℕ} (hthree : 3 ≤ rank) :
    ¬ HingeHoldsAtSize (rank + 1) rank := by
  have hrank : 0 < rank := by omega
  intro hhinge
  exact flatSimplexDesign_not_hasParallelPair hrank hthree
    (hhinge (flatSimplexDesign rank hrank) (flatSimplexDesign_isTie hrank))

/-! ## 2. The duplicate split

Append a second copy of one atom and divide that atom's weight.  The new design
carries a parallel pair by construction, and its tie status is exactly the tie
status of the design it came from. -/

-- `Gtz.pos_of_weightedDesign` (Gtz/Design/VolumeSamplingAverage.lean) already states
-- that a weighted design has at least one atom.  It is imported, not re-derived.

/-- **THE DUPLICATE SPLIT.**  Atom `label` is copied, and its weight is divided in
the ratio `share : 1 - share`. -/
noncomputable def duplicateSplitDesign (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1) :
    WeightedDesign (m + 1) k where
  atom := Fin.snoc D.atom (D.atom label)
  weight := Fin.snoc (Function.update D.weight label ((1 - share) * D.weight label))
      (share * D.weight label)
  weight_pos := by
    intro index
    rcases Fin.eq_castSucc_or_eq_last index with ⟨inner, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      by_cases hinner : inner = label
      · subst hinner
        rw [Function.update_self]
        have hpos := D.weight_pos inner
        nlinarith
      · rw [Function.update_of_ne hinner]
        exact D.weight_pos inner
    · rw [Fin.snoc_last]
      have hpos := D.weight_pos label
      positivity
  weight_sum_one := by
    classical
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have hupdate : ∑ inner : Fin m,
        Function.update D.weight label ((1 - share) * D.weight label) inner
        = (1 - share) * D.weight label
          + ∑ inner ∈ Finset.univ \ ({label} : Finset (Fin m)), D.weight inner :=
      Finset.sum_update_of_mem (Finset.mem_univ label) _ _
    have hrest : ∑ inner ∈ Finset.univ \ ({label} : Finset (Fin m)), D.weight inner
        = 1 - D.weight label := by
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _), D.weight_sum_one, Finset.sum_singleton]
    rw [hupdate, hrest]
    ring
  isParseval := by
    classical
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have hpoint : ∀ inner : Fin m,
        (Function.update D.weight label ((1 - share) * D.weight label) inner)
            • atomMatrix (D.atom inner)
          = Function.update (fun outer => D.weight outer • atomMatrix (D.atom outer)) label
              (((1 - share) * D.weight label) • atomMatrix (D.atom label)) inner := by
      intro inner
      by_cases hinner : inner = label
      · subst hinner; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hinner, Function.update_of_ne hinner]
    rw [Finset.sum_congr rfl fun inner _ => hpoint inner,
      Finset.sum_update_of_mem (Finset.mem_univ label) _ _]
    have hrest : ∑ inner ∈ Finset.univ \ ({label} : Finset (Fin m)),
        D.weight inner • atomMatrix (D.atom inner)
        = 1 - D.weight label • atomMatrix (D.atom label) := by
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _), D.isParseval, Finset.sum_singleton]
    rw [hrest]
    have hcombine : ((1 - share) * D.weight label) • atomMatrix (D.atom label)
        + (share * D.weight label) • atomMatrix (D.atom label)
        = D.weight label • atomMatrix (D.atom label) := by
      rw [← add_smul]
      congr 1
      ring
    have hshuffle : ((1 - share) * D.weight label) • atomMatrix (D.atom label)
          + (1 - D.weight label • atomMatrix (D.atom label))
          + (share * D.weight label) • atomMatrix (D.atom label)
        = (((1 - share) * D.weight label) • atomMatrix (D.atom label)
            + (share * D.weight label) • atomMatrix (D.atom label))
          + 1 - D.weight label • atomMatrix (D.atom label) := by abel
    rw [hshuffle, hcombine]
    abel

theorem duplicateSplitDesign_atom_castSucc (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1) (inner : Fin m) :
    (duplicateSplitDesign D label share hshareLow hshareHigh).atom (Fin.castSucc inner)
      = D.atom inner := by
  simp [duplicateSplitDesign]

theorem duplicateSplitDesign_atom_last (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1) :
    (duplicateSplitDesign D label share hshareLow hshareHigh).atom (Fin.last m)
      = D.atom label := by
  simp [duplicateSplitDesign]

/-- **THE SPLIT CARRIES A PARALLEL PAIR**, at ratio one. -/
theorem hasParallelPair_duplicateSplitDesign (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1) :
    HasParallelPair (duplicateSplitDesign D label share hshareLow hshareHigh) := by
  refine ⟨Fin.castSucc label, Fin.last m, 1, (Fin.castSucc_lt_last label).ne, ?_⟩
  rw [duplicateSplitDesign_atom_last, duplicateSplitDesign_atom_castSucc, one_smul]

/-! ### Selections upstairs and downstairs -/

/-- The labels of an upstairs selection that already exist downstairs. -/
def pullbackSelection {ambient : ℕ} (selected : Finset (Fin (ambient + 1))) :
    Finset (Fin ambient) :=
  Finset.univ.filter (fun index => Fin.castSucc index ∈ selected)

theorem mem_pullbackSelection {ambient : ℕ} {selected : Finset (Fin (ambient + 1))}
    {index : Fin ambient} :
    index ∈ pullbackSelection selected ↔ Fin.castSucc index ∈ selected := by
  rw [pullbackSelection, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ index, h⟩⟩

/-- **THE SUM LAW OF A SPLIT SELECTION.**  Every sum over an upstairs selection is
the downstairs sum plus one optional last term. -/
theorem sum_over_split_selection {ambient : ℕ} {Target : Type*} [AddCommMonoid Target]
    (selected : Finset (Fin (ambient + 1))) (summand : Fin (ambient + 1) → Target) :
    ∑ label ∈ selected, summand label
      = (∑ index ∈ pullbackSelection selected, summand (Fin.castSucc index))
        + (if Fin.last ambient ∈ selected then summand (Fin.last ambient) else 0) := by
  classical
  have hindicator : ∑ label ∈ selected, summand label
      = ∑ label : Fin (ambient + 1), if label ∈ selected then summand label else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hindicator, Fin.sum_univ_castSucc]
  congr 1
  rw [pullbackSelection, Finset.sum_filter]

theorem card_split_selection {ambient : ℕ} (selected : Finset (Fin (ambient + 1))) :
    selected.card
      = (pullbackSelection selected).card + (if Fin.last ambient ∈ selected then 1 else 0) := by
  classical
  have hcount := sum_over_split_selection selected (fun _ => (1 : ℕ))
  rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at hcount
  exact hcount

/-- The atom sum of an upstairs selection, read downstairs. -/
theorem subsetSum_duplicateSplitDesign (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1)
    (selected : Finset (Fin (m + 1))) :
    subsetSum (duplicateSplitDesign D label share hshareLow hshareHigh) selected
      = (∑ index ∈ pullbackSelection selected, atomMatrix (D.atom index))
        + (if Fin.last m ∈ selected then atomMatrix (D.atom label) else 0) := by
  classical
  rw [subsetSum, sum_over_split_selection selected
    (fun outer => atomMatrix ((duplicateSplitDesign D label share hshareLow hshareHigh).atom outer))]
  congr 1
  · exact Finset.sum_congr rfl fun index _ => by
      rw [duplicateSplitDesign_atom_castSucc]
  · by_cases hlast : Fin.last m ∈ selected
    · rw [if_pos hlast, if_pos hlast, duplicateSplitDesign_atom_last]
    · rw [if_neg hlast, if_neg hlast]

/-- **A SELECTION THAT TAKES BOTH COPIES DOMINATES NOTHING.** -/
theorem not_dominates_duplicateSplit_of_both (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1)
    {selected : Finset (Fin (m + 1))} (hcard : selected.card = k)
    (hlast : Fin.last m ∈ selected) (hlabel : Fin.castSucc label ∈ selected) :
    ¬ Dominates (duplicateSplitDesign D label share hshareLow hshareHigh) selected := by
  refine not_dominates_of_parallel_within _ hcard hlabel hlast
    (Fin.castSucc_lt_last label).ne (ratio := 1) ?_
  rw [duplicateSplitDesign_atom_last, duplicateSplitDesign_atom_castSucc, one_smul]

/-- **EVERY OTHER SELECTION HAS A DOWNSTAIRS TWIN** of the same size and the same
atom sum. -/
theorem exists_downstairs_selection (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1)
    {selected : Finset (Fin (m + 1))} (hcard : selected.card = k)
    (hnotBoth : ¬ (Fin.last m ∈ selected ∧ Fin.castSucc label ∈ selected)) :
    ∃ chosen : Finset (Fin m), chosen.card = k ∧
      subsetSum D chosen
        = subsetSum (duplicateSplitDesign D label share hshareLow hshareHigh) selected := by
  classical
  have hcount := card_split_selection selected
  by_cases hlast : Fin.last m ∈ selected
  · have hlabel : Fin.castSucc label ∉ selected := fun hmem => hnotBoth ⟨hlast, hmem⟩
    have hnotmem : label ∉ pullbackSelection selected := fun hmem =>
      hlabel (mem_pullbackSelection.mp hmem)
    refine ⟨insert label (pullbackSelection selected), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnotmem, ← hcard, hcount, if_pos hlast]
    · rw [subsetSum, Finset.sum_insert hnotmem,
        subsetSum_duplicateSplitDesign, if_pos hlast]
      abel
  · refine ⟨pullbackSelection selected, ?_, ?_⟩
    · rw [← hcard, hcount, if_neg hlast, add_zero]
    · rw [subsetSum, subsetSum_duplicateSplitDesign, if_neg hlast, add_zero]

/-- **EVERY DOWNSTAIRS SELECTION HAS AN UPSTAIRS TWIN.** -/
theorem subsetSum_image_castSucc (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1) (chosen : Finset (Fin m)) :
    subsetSum (duplicateSplitDesign D label share hshareLow hshareHigh)
        (chosen.image Fin.castSucc) = subsetSum D chosen := by
  classical
  rw [subsetSum, subsetSum, Finset.sum_image
    (fun left _ right _ hcast => Fin.castSucc_injective m hcast)]
  exact Finset.sum_congr rfl fun index _ => by rw [duplicateSplitDesign_atom_castSucc]

theorem card_image_castSucc {ambient : ℕ} (chosen : Finset (Fin ambient)) :
    (chosen.image Fin.castSucc).card = chosen.card :=
  Finset.card_image_of_injective _ (Fin.castSucc_injective ambient)

/-- **THE SPLIT OF A DESIGN IS A TIE EXACTLY WHEN THE DESIGN IS A TIE.** -/
theorem isTie_duplicateSplitDesign_iff (D : WeightedDesign m k) (label : Fin m)
    (share : ℝ) (hshareLow : 0 < share) (hshareHigh : share < 1) :
    IsTie (duplicateSplitDesign D label share hshareLow hshareHigh) ↔ IsTie D := by
  classical
  constructor
  · rintro ⟨⟨selected, hcard, hdom⟩, hnostrict⟩
    refine ⟨?_, ?_⟩
    · have hnotBoth : ¬ (Fin.last m ∈ selected ∧ Fin.castSucc label ∈ selected) := by
        rintro ⟨hlast, hlabel⟩
        exact not_dominates_duplicateSplit_of_both D label share hshareLow hshareHigh
          hcard hlast hlabel hdom
      obtain ⟨chosen, hchosenCard, hchosenSum⟩ :=
        exists_downstairs_selection D label share hshareLow hshareHigh hcard hnotBoth
      exact ⟨chosen, hchosenCard, by rw [Dominates, hchosenSum]; exact hdom⟩
    · intro chosen hchosenCard hposDef
      refine hnostrict (chosen.image Fin.castSucc) ?_ ?_
      · rw [card_image_castSucc, hchosenCard]
      · rw [subsetSum_image_castSucc]
        exact hposDef
  · rintro ⟨⟨chosen, hchosenCard, hdom⟩, hnostrict⟩
    refine ⟨⟨chosen.image Fin.castSucc, ?_, ?_⟩, ?_⟩
    · rw [card_image_castSucc, hchosenCard]
    · rw [Dominates, subsetSum_image_castSucc]
      exact hdom
    · intro selected hcard hposDef
      by_cases hboth : Fin.last m ∈ selected ∧ Fin.castSucc label ∈ selected
      · exact not_dominates_duplicateSplit_of_both D label share hshareLow hshareHigh
          hcard hboth.1 hboth.2 hposDef.posSemidef
      · obtain ⟨downstairs, hdownCard, hdownSum⟩ :=
          exists_downstairs_selection D label share hshareLow hshareHigh hcard hboth
        exact hnostrict downstairs hdownCard (by rw [hdownSum]; exact hposDef)

/-! ## 3. The tie tower -/

/-- **A TIE LIFTS ONE SIZE UP, AND THE LIFT CARRIES A PARALLEL PAIR.** -/
theorem exists_isTie_succ {D : WeightedDesign m k} (htie : IsTie D) :
    ∃ E : WeightedDesign (m + 1) k, IsTie E ∧ HasParallelPair E := by
  have hpos := pos_of_weightedDesign D
  refine ⟨duplicateSplitDesign D ⟨0, hpos⟩ (1 / 2) (by norm_num) (by norm_num), ?_, ?_⟩
  · exact (isTie_duplicateSplitDesign_iff D _ _ _ _).mpr htie
  · exact hasParallelPair_duplicateSplitDesign D _ _ _ _

/-- **AN EXACT TIE EXISTS AT EVERY CELL OF EVERY RANK `≥ 3` FROM SIZE `rank + 1` UP.**
The base is the simplex tie of part 1, and the step is the duplicate split. -/
theorem exists_isTie_of_succ_rank_le {rank size : ℕ} (hthree : 3 ≤ rank)
    (hsize : rank + 1 ≤ size) : ∃ D : WeightedDesign size rank, IsTie D := by
  induction size, hsize using Nat.le_induction with
  | base =>
      exact ⟨flatSimplexDesign rank (by omega), flatSimplexDesign_isTie (by omega)⟩
  | succ current hcurrent ihcurrent =>
      obtain ⟨D, htie⟩ := ihcurrent
      obtain ⟨E, htieE, _⟩ := exists_isTie_succ htie
      exact ⟨E, htieE⟩

/-- **NO CELL OF THE SHARP WINDOW IS EMPTY OF TIES.**  Both general-rank registry
axioms quantify over an inhabited stratum at every cell of every rank.

THE ROUTE THIS KILLS.  A proof of either hinge that argued "this cell holds no
tie" is refuted at every cell at once.  The hinge must exhibit a parallel pair,
never an empty stratum. -/
theorem not_forall_not_isTie {rank size : ℕ} (hthree : 3 ≤ rank) (hsize : rank + 1 ≤ size) :
    ¬ (∀ D : WeightedDesign size rank, ¬ IsTie D) := by
  obtain ⟨D, htie⟩ := exists_isTie_of_succ_rank_le hthree hsize
  exact fun hempty => hempty D htie

/-- The band cells and the threshold cell all carry ties. -/
theorem exists_isTie_bandCell {rank size : ℕ} (hthree : 3 ≤ rank) (hlow : 2 * rank ≤ size) :
    ∃ D : WeightedDesign size rank, IsTie D :=
  exists_isTie_of_succ_rank_le hthree (by omega)

/-- The threshold cell of rank three carries a tie, so `Gtz.HingeHoldsAtSize 6 3`
is not vacuous. -/
theorem exists_isTie_sixThree : ∃ D : WeightedDesign 6 3, IsTie D :=
  exists_isTie_of_succ_rank_le (by norm_num) (by norm_num)

/-- The first band cell of rank four carries a tie. -/
theorem exists_isTie_eightFour : ∃ D : WeightedDesign 8 4, IsTie D :=
  exists_isTie_of_succ_rank_le (by norm_num) (by norm_num)

/-- The threshold cell of rank four carries a tie. -/
theorem exists_isTie_tenFour : ∃ D : WeightedDesign 10 4, IsTie D :=
  exists_isTie_of_succ_rank_le (by norm_num) (by norm_num)

/-! ## 4. The strict merge pullback, and descent

`Gtz.exists_dominating_of_mergedParallel_dominates` (Gtz/Reduction/SplitTransfer.lean)
lifts a WEAK dominator of the merged design.  The strict lift is what turns the
hinge into a descent law, and it was missing.  The proof is the same case split:
if the merged atom is not selected the atom sums agree on the nose, and if it is,
replace it by whichever original is longer and the gap only grows. -/

/-- **THE STRICT MERGE PULLBACK.**  A strictly dominating subset of the merged
design lifts to a strictly dominating subset of the same size upstairs. -/
theorem exists_posDef_of_mergedParallel_posDef (D : WeightedDesign (m + 1) k)
    (keptLabel dropLabel : Fin (m + 1)) (ratio : ℝ) (keptIndex : Fin m)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel)
    {mergedSubset : Finset (Fin m)}
    (hposDef : (subsetSum
      (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel)
      mergedSubset - 1).PosDef) :
    ∃ C : Finset (Fin (m + 1)), C.card = mergedSubset.card
      ∧ (subsetSum D C - 1).PosDef := by
  classical
  set mergedDesign :=
    mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel
    with hmergedDesign
  have hembedInjective : Function.Injective dropLabel.succAbove := Fin.succAbove_right_injective
  by_cases hkeptMem : keptIndex ∈ mergedSubset
  · obtain ⟨longerLabel, hlongerCase, hlongerPsd⟩ :=
      exists_longerParallelLabel D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel
    set restImage := (mergedSubset.erase keptIndex).image dropLabel.succAbove with hrestImage
    have hlongerNotMem : longerLabel ∉ restImage := by
      rw [hrestImage, Finset.mem_image]
      rintro ⟨index, hindexMem, hindexEq⟩
      rcases hlongerCase with hiskept | hisdrop
      · rw [hiskept, ← hkeptIndex] at hindexEq
        exact (Finset.mem_erase.mp hindexMem).1 (hembedInjective hindexEq)
      · exact (Fin.succAbove_ne dropLabel index) (hindexEq.trans hisdrop)
    have hcardPos : 0 < mergedSubset.card := Finset.card_pos.mpr ⟨keptIndex, hkeptMem⟩
    refine ⟨insert longerLabel restImage, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hlongerNotMem, hrestImage,
        Finset.card_image_of_injective _ hembedInjective,
        Finset.card_erase_of_mem hkeptMem]
      omega
    · have hrestSum : ∑ c ∈ restImage, atomMatrix (D.atom c)
          = ∑ index ∈ mergedSubset.erase keptIndex, atomMatrix (mergedDesign.atom index) := by
        rw [hrestImage, Finset.sum_image
          (fun left _ right _ hcast => hembedInjective hcast)]
        refine Finset.sum_congr rfl fun index hindex => ?_
        rw [hmergedDesign, mergedParallelDesign_atom_of_ne D keptLabel dropLabel ratio
          hkeptIndex hparallel (Finset.mem_erase.mp hindex).1]
      have hupperSum : subsetSum D (insert longerLabel restImage)
          = subsetSum mergedDesign mergedSubset
            + (atomMatrix (D.atom longerLabel) - atomMatrix (mergedDesign.atom keptIndex)) := by
        rw [subsetSum, subsetSum, Finset.sum_insert hlongerNotMem, hrestSum,
          ← Finset.sum_erase_add mergedSubset
            (fun index => atomMatrix (mergedDesign.atom index)) hkeptMem]
        abel
      rw [hupperSum, show subsetSum mergedDesign mergedSubset
          + (atomMatrix (D.atom longerLabel) - atomMatrix (mergedDesign.atom keptIndex)) - 1
        = (subsetSum mergedDesign mergedSubset - 1)
          + (atomMatrix (D.atom longerLabel)
            - atomMatrix (mergedDesign.atom keptIndex)) from by abel]
      exact hposDef.add_posSemidef hlongerPsd
  · refine ⟨mergedSubset.image dropLabel.succAbove, ?_, ?_⟩
    · exact Finset.card_image_of_injective _ hembedInjective
    · have hsumEq : subsetSum D (mergedSubset.image dropLabel.succAbove)
          = subsetSum mergedDesign mergedSubset := by
        rw [subsetSum, subsetSum, Finset.sum_image
          (fun left _ right _ hcast => hembedInjective hcast)]
        refine Finset.sum_congr rfl fun index hindex => ?_
        rw [hmergedDesign, mergedParallelDesign_atom_of_ne D keptLabel dropLabel ratio
          hkeptIndex hparallel (fun hiskept => hkeptMem (hiskept ▸ hindex))]
      rw [hsumEq]
      exact hposDef

/-- **A TIE THAT CARRIES A PARALLEL PAIR MERGES TO A TIE ONE SIZE DOWN.**  The weak
half comes from the predecessor cell, and the strict half is the pullback above. -/
theorem isTie_mergedParallelDesign (D : WeightedDesign (m + 1) k)
    (hrecursive : GtzWeighted m k) (htie : IsTie D)
    {keptLabel dropLabel : Fin (m + 1)} {ratio : ℝ} (hdistinct : keptLabel ≠ dropLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel)
    (keptIndex : Fin m) (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel) :
    IsTie (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel) := by
  refine ⟨hrecursive _, ?_⟩
  intro mergedSubset hcard hposDef
  obtain ⟨C, hcardC, hposDefC⟩ :=
    exists_posDef_of_mergedParallel_posDef D keptLabel dropLabel ratio keptIndex hkeptIndex
      hparallel hposDef
  exact htie.2 C (by rw [hcardC, hcard]) hposDefC

/-- **DESCENT.**  At a cell where the hinge holds, and granted the predecessor
cell, every tie descends to a tie one size down. -/
theorem exists_isTie_pred_of_hinge {ambient rank : ℕ} (hrecursive : GtzWeighted ambient rank)
    (hhinge : HingeHoldsAtSize (ambient + 1) rank)
    (D : WeightedDesign (ambient + 1) rank) (htie : IsTie D) :
    ∃ E : WeightedDesign ambient rank, IsTie E := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hhinge D htie
  obtain ⟨keptIndex, hkeptIndex⟩ := Fin.exists_succAbove_eq hdistinct
  exact ⟨mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel,
    isTie_mergedParallelDesign D hrecursive htie hdistinct hparallel keptIndex hkeptIndex⟩

/-! ## 5. What the two readings say together

The split law of part 3 and the descent law of part 4 are inverse to each other
on the tie stratum.  The hinge at one cell says the tie stratum of that cell is
exactly the image of the tie stratum one cell down. -/

/-- **THE HINGE IS A STRATUM EQUATION.**  At a cell where the hinge holds, a tie
exists exactly when a tie exists one cell down.  The forward arrow is descent, and
the backward arrow is the duplicate split, which needs no hypothesis at all. -/
theorem exists_isTie_succ_iff_of_hinge {ambient rank : ℕ}
    (hrecursive : GtzWeighted ambient rank)
    (hhinge : HingeHoldsAtSize (ambient + 1) rank) :
    (∃ D : WeightedDesign (ambient + 1) rank, IsTie D)
      ↔ (∃ E : WeightedDesign ambient rank, IsTie E) := by
  constructor
  · rintro ⟨D, htie⟩
    exact exists_isTie_pred_of_hinge hrecursive hhinge D htie
  · rintro ⟨E, htie⟩
    obtain ⟨F, htieF, _⟩ := exists_isTie_succ htie
    exact ⟨F, htieF⟩

/-- **THE `(6,3)` READING.**  `Gtz.GtzWeighted 5 3` is a theorem in the tree, so at
the threshold cell of rank three the hinge says exactly that every tie merges to a
`(5,3)` tie.  The `(5,3)` tie stratum is inhabited (`Gtz.diamondDesign`), so this
reading is not vacuous in either direction. -/
theorem exists_isTie_sixThree_iff_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    (∃ D : WeightedDesign 6 3, IsTie D) ↔ (∃ E : WeightedDesign 5 3, IsTie E) :=
  exists_isTie_succ_iff_of_hinge (ambient := 5) (rank := 3)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hhinge

/-- **THE BAND READING AT `(8,4)`.**  Granted the predecessor cell, the band hinge
at the first band cell of rank four says every `(8,4)` tie merges to a `(7,4)` tie. -/
theorem exists_isTie_eightFour_iff_of_hinge (hrecursive : GtzWeighted 7 4)
    (hhinge : HingeHoldsAtSize 8 4) :
    (∃ D : WeightedDesign 8 4, IsTie D) ↔ (∃ E : WeightedDesign 7 4, IsTie E) :=
  exists_isTie_succ_iff_of_hinge (ambient := 7) (rank := 4) hrecursive hhinge

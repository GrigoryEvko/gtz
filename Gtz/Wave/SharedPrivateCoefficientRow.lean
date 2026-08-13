import Gtz.Wave.SharedPrivateSlotSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The coefficient row law — the label side of the identical branch

The diagonal ledger is exhausted: every budget that reads only the chart
diagonal collapses to the window bound.  The next input is the
COEFFICIENT REPRESENTATION `chart * basis = basis * coeff`, read row by
row against the tight equation.

## The basis row law

At an atom of a basis slot's own block the chart moves the tight
direction by the captured diagonal.  The representation reads the same
entry as a combination of the basis values.  Thus, at every atom of the
block,

  `Σ_other tightDir_other y * coeff other slot = (value + weight y) * tightDir_slot y`.

The sum runs over the LIVE slots at the atom only, because a dead basis
value kills its term.  Thus the law is a small system whenever the atom
carries few slots.

## The private atom law

At an atom of basis multiplicity one the sum has a single term and the
law reads `coeff slot slot = value + weight y`.  The pinned diagonal of
the datum is the instance at the pin atom.  Because the captured
diagonals total `1 + 6 * value < 1` and the coefficient trace is at
least two, a family of private atoms, one for each slot, is a
contradiction.

## The pair corner

At an atom that carries exactly two slots the law says that the pair of
basis values is an EIGENVECTOR of the transposed two-by-two corner of
the coefficient matrix, with the captured diagonal as its eigenvalue.
Two such atoms with independent value pairs pin the corner completely:
the trace of the corner is the sum of the two captured diagonals and its
determinant is their product.

## The identical branch

Two basis slots with one support give a rank-one shifted gap block.  The
rank-one minors refuse two parallel value pairs: a vanishing pair minor
produces a combination that lives on one atom, and its tight row makes a
cross entry vanish, against a positive shifted diagonal.  Thus every two
atoms of the shared triple give the pair corner exactly.

When ALL THREE atoms of the shared triple carry only the two slots, the
branch dies with no residue.  Every other slot then misses the shared
triple, thus every other slot IS the complement triple.  Two of them
give the landed complement kill.  One of them exhausts the slots, and
then the coefficient trace is the sum of three captured diagonals, which
is less than one, against a trace of at least two.

## The trace cover kills

The same arithmetic kills three more configurations.  A family of
private atoms, one for each slot, reads the whole trace.  A pure pair
plus a private family on the remaining slots reads the whole trace.  Two
disjoint pure pairs that carry every slot read the whole trace.  Each
reading is a sum of captured diagonals over distinct atoms, thus less
than one.

## What the identical branch keeps

Two pure atoms of the shared triple force a FOURTH basis slot with no
atom of basis multiplicity one, because the pinned slot always carries
the pin atom privately.  And the slots outside the identical pair and
the pinned slot carry MORE THAN ONE UNIT of coefficient diagonal.  That
is the narrowest form of the identical branch that this module reaches.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no shared-private datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the basis row law of the coefficient matrix -/

section BasisRow

variable {size rank basisCount : ℕ} {activeIndex : Type}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisLabel : Fin basisCount → activeIndex}
variable {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}

/-- **THE BASIS ROW LAW.**  At every atom of a basis slot's own block the
coefficient column of that slot reproduces the captured diagonal.  The
proof is one entry of the representation against the tight equation: no
left inverse, no span, no reconstruction. -/
theorem basisRow_coeff_capture
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hbasisMem : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (slot : Fin basisCount) {atomIndex : Fin size}
    (hblock : atomIndex ∈ activeSubset (basisLabel slot)) :
    ∑ other : Fin basisCount,
        tightDir (basisLabel other) atomIndex * coeff other slot
      = (value + weight atomIndex) * tightDir (basisLabel slot) atomIndex := by
  have hentry := congrFun (congrFun hrepresentation atomIndex) slot
  simp only [Matrix.mul_apply, tightBasisColumns] at hentry
  have hchart := chart_mulVec_tightDir_apply hdata (hbasisMem slot) hblock
  simp only [Matrix.mulVec, dotProduct] at hchart
  rw [hentry] at hchart
  exact hchart

/-- **THE PRIVATE ATOM LAW.**  At an atom that only one basis slot
reaches, the basis row law collapses to a single term and reads the
diagonal entry of the coefficient matrix.  The pinned diagonal of a
shared-private datum is the instance at the pin atom. -/
theorem coeff_diag_of_private_atom
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hbasisMem : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {slot : Fin basisCount} {atomIndex : Fin size}
    (hblock : atomIndex ∈ activeSubset (basisLabel slot))
    (hlive : tightDir (basisLabel slot) atomIndex ≠ 0)
    (hprivate : ∀ other : Fin basisCount, other ≠ slot →
      tightDir (basisLabel other) atomIndex = 0) :
    coeff slot slot = value + weight atomIndex := by
  classical
  have hrow := basisRow_coeff_capture hdata hbasisMem hrepresentation slot hblock
  have hcollapse : ∑ other : Fin basisCount,
      tightDir (basisLabel other) atomIndex * coeff other slot
      = tightDir (basisLabel slot) atomIndex * coeff slot slot :=
    Finset.sum_eq_single slot
      (fun other _ hne => by rw [hprivate other hne, zero_mul])
      (fun habs => absurd (Finset.mem_univ _) habs)
  rw [hcollapse] at hrow
  exact mul_left_cancel₀ hlive (by rw [hrow]; ring)

/-- **THE PAIR ROW LAW.**  At an atom that exactly two basis slots reach,
the basis row law collapses to a two-term equation.  Read at the two
columns of the pair it says that the pair of basis values is an
eigenvector of the transposed pair corner. -/
theorem pairRow_coeff_capture
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hbasisMem : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {slotOne slotTwo slotCol : Fin basisCount} (hne : slotOne ≠ slotTwo)
    {atomIndex : Fin size}
    (hblock : atomIndex ∈ activeSubset (basisLabel slotCol))
    (hpure : ∀ other : Fin basisCount, other ≠ slotOne → other ≠ slotTwo →
      tightDir (basisLabel other) atomIndex = 0) :
    tightDir (basisLabel slotOne) atomIndex * coeff slotOne slotCol
        + tightDir (basisLabel slotTwo) atomIndex * coeff slotTwo slotCol
      = (value + weight atomIndex) * tightDir (basisLabel slotCol) atomIndex := by
  classical
  have hrow := basisRow_coeff_capture hdata hbasisMem hrepresentation slotCol hblock
  have hrestrict : ∑ other : Fin basisCount,
      tightDir (basisLabel other) atomIndex * coeff other slotCol
      = ∑ other ∈ ({slotOne, slotTwo} : Finset (Fin basisCount)),
          tightDir (basisLabel other) atomIndex * coeff other slotCol := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro other _ hnot
    have honeNe : other ≠ slotOne := fun heq =>
      hnot (heq ▸ Finset.mem_insert_self _ _)
    have htwoNe : other ≠ slotTwo := fun heq =>
      hnot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [hpure other honeNe htwoNe, zero_mul]
  rw [hrestrict, Finset.sum_pair hne] at hrow
  exact hrow

end BasisRow

/-! ## Layer 2 — the datum readings of the row law -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- The datum instance of the basis row law. -/
theorem basisRow_capture (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) {atomIndex : Fin 6}
    (hblock : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)) :
    ∑ other : Fin data.basisCount,
        data.tightDir (data.basisLabel other) atomIndex * data.coeff other slot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slot) atomIndex :=
  basisRow_coeff_capture data.hdata data.basisLabel_mem_activeSet data.hrepresentation
    slot (by rw [data.basisBlock_eq_support slot]; exact hblock)

/-- **THE DATUM PRIVATE ATOM LAW.**  At an atom of basis multiplicity one
the coefficient diagonal of the carrying slot IS the captured diagonal.
The pinned diagonal `hpin` is the instance at the pin atom. -/
theorem coeff_diag_of_private (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomIndex : Fin 6}
    (hblock : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    (hprivate : ∀ other : Fin data.basisCount, other ≠ slot →
      data.tightDir (data.basisLabel other) atomIndex = 0) :
    data.coeff slot slot
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex :=
  coeff_diag_of_private_atom data.hdata data.basisLabel_mem_activeSet
    data.hrepresentation (by rw [data.basisBlock_eq_support slot]; exact hblock)
    (data.basis_live_of_mem_support hblock) hprivate

/-- The datum instance of the pair row law. -/
theorem pairRow_capture (data : SharedPrivateData crux)
    {slotOne slotTwo slotCol : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomIndex : Fin 6}
    (hblock : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotCol))
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomIndex = 0) :
    data.tightDir (data.basisLabel slotOne) atomIndex * data.coeff slotOne slotCol
        + data.tightDir (data.basisLabel slotTwo) atomIndex
          * data.coeff slotTwo slotCol
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slotCol) atomIndex :=
  pairRow_coeff_capture data.hdata data.basisLabel_mem_activeSet data.hrepresentation
    hne (by rw [data.basisBlock_eq_support slotCol]; exact hblock) hpure

/-! ## Layer 3 — the capture total and the coefficient trace -/

/-- The captured diagonals of a datum total `1 + 6 * value`. -/
theorem sum_captureDiag (data : SharedPrivateData crux) :
    ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      = 1 + 6 * chartObjective (chartPointOfDesign crux.design) := by
  rw [Finset.sum_add_distrib, data.hdata.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **THE CAPTURE TOTAL IS LESS THAN ONE.**  The value is negative at
every datum. -/
theorem sum_captureDiag_lt_one (data : SharedPrivateData crux) :
    ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) < 1 := by
  rw [data.sum_captureDiag]
  have hneg := data.hvalueNeg
  linarith

/-- The coefficient trace of a datum is at least two. -/
theorem two_le_trace_coeff (data : SharedPrivateData crux) :
    (2 : ℝ) ≤ Matrix.trace data.coeff := by
  rcases data.htrace with htwo | hthree
  · rw [htwo]
  · rw [hthree]; norm_num

/-- The coefficient trace as a plain sum of diagonal entries. -/
theorem trace_coeff_eq_sum (data : SharedPrivateData crux) :
    Matrix.trace data.coeff = ∑ slot : Fin data.basisCount, data.coeff slot slot :=
  rfl

/-- A triple of distinct atoms carries at most the whole capture total. -/
theorem captureDiag_triple_le_total (data : SharedPrivateData crux)
    {atomA atomB atomC : Fin 6} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hBC : atomB ≠ atomC) :
    (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomA)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomB)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomC)
      ≤ ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) := by
  classical
  have hsum : ∑ atomIndex ∈ ({atomA, atomB, atomC} : Finset (Fin 6)),
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomA)
        + (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomB)
        + (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomC) := by
    rw [Finset.sum_insert (by simp [hAB, hAC]), Finset.sum_insert (by simp [hBC]),
      Finset.sum_singleton]
    ring
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun atomIndex _ _ => data.captureDiag_nonneg atomIndex

/-! ## Layer 4 — the trace cover kills -/

/-- **THE TRACE COVER KILL.**  Whenever the coefficient trace reads as a
sum of captured diagonals over a set of distinct atoms, the datum dies:
the total of all captured diagonals is less than one and the trace is at
least two.  Every kill of this module runs through this one line. -/
theorem false_of_trace_eq_captureSum (data : SharedPrivateData crux)
    {atomSet : Finset (Fin 6)}
    (htrace : Matrix.trace data.coeff
      = ∑ atomIndex ∈ atomSet, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) :
    False := by
  classical
  have hbound : ∑ atomIndex ∈ atomSet,
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      ≤ ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomIndex _ _ => data.captureDiag_nonneg atomIndex
  have hlow := data.two_le_trace_coeff
  have hhigh := data.sum_captureDiag_lt_one
  rw [htrace] at hlow
  linarith

/-- **THE PRIVATE FAMILY TRACE KILL.**  If every basis slot carries an
atom of basis multiplicity one, the coefficient trace is a sum of
captured diagonals over distinct atoms, thus less than one, against a
trace of at least two. -/
theorem false_of_private_atom_family (data : SharedPrivateData crux)
    (privateAtom : Fin data.basisCount → Fin 6)
    (hblock : ∀ slot, privateAtom slot
      ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    (hprivate : ∀ slot other : Fin data.basisCount, other ≠ slot →
      data.tightDir (data.basisLabel other) (privateAtom slot) = 0) :
    False := by
  classical
  have hinjective : Function.Injective privateAtom := by
    intro slotOne slotTwo hsame
    by_contra hne
    have hzero := hprivate slotTwo slotOne hne
    rw [← hsame] at hzero
    exact data.basis_live_of_mem_support (hblock slotOne) hzero
  have hdiag : ∀ slot : Fin data.basisCount, data.coeff slot slot
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight (privateAtom slot) :=
    fun slot => data.coeff_diag_of_private (hblock slot) (hprivate slot)
  have htrace : Matrix.trace data.coeff
      = ∑ slot : Fin data.basisCount,
          (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight (privateAtom slot)) := by
    rw [data.trace_coeff_eq_sum]
    exact Finset.sum_congr rfl fun slot _ => hdiag slot
  have himage : ∑ atomIndex ∈ Finset.image privateAtom Finset.univ,
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      = ∑ slot : Fin data.basisCount,
          (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight (privateAtom slot)) :=
    Finset.sum_image fun slotOne _ slotTwo _ hsame => hinjective hsame
  have hbound : ∑ atomIndex ∈ Finset.image privateAtom Finset.univ,
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      ≤ ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomIndex _ _ => data.captureDiag_nonneg atomIndex
  exact data.false_of_trace_eq_captureSum (htrace.trans himage.symm)

/-! ## Layer 5 — the identical pair has pairwise independent value pairs -/

/-- **THE IDENTICAL PAIR MINOR.**  Two basis slots with one support give
a rank-one shifted gap block, and the rank-one minors refuse two parallel
value pairs.  A vanishing pair minor makes the two columns proportional
at the two atoms and at the third, thus proportional everywhere, against
the independence of the basis columns. -/
theorem identicalPair_wedge_ne_zero (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    data.tightDir (data.basisLabel slotOne) atomU
        * data.tightDir (data.basisLabel slotTwo) atomV
      - data.tightDir (data.basisLabel slotOne) atomV
        * data.tightDir (data.basisLabel slotTwo) atomU ≠ 0 := by
  classical
  intro hwedge
  set dirOne : Fin 6 → ℝ := data.tightDir (data.basisLabel slotOne) with hdirOne
  set dirTwo : Fin 6 → ℝ := data.tightDir (data.basisLabel slotTwo) with hdirTwo
  have hblockOne := data.basisBlock_eq_support slotOne
  have hblockTwo := data.basisBlock_eq_support slotTwo
  have hmemU : atomU ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hmemV : atomV ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hmemS : atomS ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  obtain ⟨hrowOneU, hrowOneV, hrowOneS⟩ :=
    triple_tight_corner_rows data.hdata (data.basisLabel_mem_activeSet slotOne)
      hUV hUS hVS (by rw [hblockOne, hsupportOne]; exact hmemU)
      (by rw [hblockOne, hsupportOne]; exact hmemV)
      (by rw [hblockOne, hsupportOne]; exact hmemS)
      (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
        (by rw [hsupportOne]; simp [hU, hV, hS]))
  obtain ⟨hrowTwoU, hrowTwoV, hrowTwoS⟩ :=
    triple_tight_corner_rows data.hdata (data.basisLabel_mem_activeSet slotTwo)
      hUV hUS hVS (by rw [hblockTwo, hsupportTwo]; exact hmemU)
      (by rw [hblockTwo, hsupportTwo]; exact hmemV)
      (by rw [hblockTwo, hsupportTwo]; exact hmemS)
      (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
        (by rw [hsupportTwo]; simp [hU, hV, hS]))
  obtain ⟨hminorUV, hminorUS, hminorVS, _, _, _⟩ :=
    data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne hsupportTwo
  set residual : ℝ := dirOne atomS * dirTwo atomV - dirOne atomV * dirTwo atomS
    with hresidualDef
  -- the two cross entries against the residual minor
  have hcrossUS : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomU atomS * residual = 0 := by
    rw [hresidualDef]
    linear_combination dirTwo atomV * hrowOneU - dirOne atomV * hrowTwoU
      - (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomU atomU
        - chartObjective (chartPointOfDesign crux.design)) * hwedge
  have hcrossVS : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomV atomS * residual = 0 := by
    rw [hresidualDef]
    linear_combination dirTwo atomV * hrowOneV - dirOne atomV * hrowTwoV
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomU atomV * hwedge
  -- the residual minor vanishes, because a live one kills a cross entry
  have hresidualZero : residual = 0 := by
    by_contra hres
    have hzero : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomU atomS = 0 :=
      (mul_eq_zero.mp hcrossUS).resolve_right hres
    have hgapU := data.shiftedGapDiag_pos atomU
    have hgapS := data.shiftedGapDiag_pos atomS
    rw [shiftedGapDiag] at hgapU hgapS
    rw [hzero] at hminorUS
    nlinarith
  -- the two columns are proportional at every atom
  have hcombo : ∀ atomIndex : Fin 6,
      dirTwo atomV * dirOne atomIndex + -(dirOne atomV) * dirTwo atomIndex = 0 := by
    intro atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU; linear_combination hwedge
    by_cases hV : atomIndex = atomV
    · subst hV; ring
    by_cases hS : atomIndex = atomS
    · subst hS; linear_combination hresidualZero
    have hdeadOne : dirOne atomIndex = 0 :=
      data.basis_dead_of_notMem_support (by rw [hsupportOne]; simp [hU, hV, hS])
    have hdeadTwo : dirTwo atomIndex = 0 :=
      data.basis_dead_of_notMem_support (by rw [hsupportTwo]; simp [hU, hV, hS])
    rw [hdeadOne, hdeadTwo, mul_zero, mul_zero, add_zero]
  obtain ⟨hscaleZero, _⟩ := data.pair_coeff_eq_zero hne hcombo
  exact data.basis_live_of_mem_support (by rw [hsupportTwo]; exact hmemV) hscaleZero

/-! ## Layer 6 — the pair corner of two pure atoms -/

/-- **THE PAIR CORNER TRACE.**  Two atoms that carry exactly the two
slots of the pair, with independent value pairs, pin the trace of the
two-by-two coefficient corner to the sum of the two captured diagonals.
The proof is one Cramer cancellation of the four pair row equations. -/
theorem purePair_corner_trace (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6}
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0) :
    data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomY)
        + (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomZ) := by
  have hYone := data.pairRow_capture hne hblockYone hpureY
  have hYtwo := data.pairRow_capture hne hblockYtwo hpureY
  have hZone := data.pairRow_capture hne hblockZone hpureZ
  have hZtwo := data.pairRow_capture hne hblockZtwo hpureZ
  have hkey : (data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY)
      * (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
        - ((chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomY)
          + (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomZ))) = 0 := by
    linear_combination data.tightDir (data.basisLabel slotTwo) atomZ * hYone
      - data.tightDir (data.basisLabel slotTwo) atomY * hZone
      + data.tightDir (data.basisLabel slotOne) atomY * hZtwo
      - data.tightDir (data.basisLabel slotOne) atomZ * hYtwo
  have hsub := (mul_eq_zero.mp hkey).resolve_left hwedge
  linarith

/-- **THE IDENTICAL PAIR CORNER TRACE.**  At two atoms of the shared
triple that carry only the two identical slots, the corner trace is the
sum of the two captured diagonals.  The wedge comes free from the
rank-one minors. -/
theorem identicalPair_corner_trace (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS})
    (hpureU : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomU = 0)
    (hpureV : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomV = 0) :
    data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomU)
        + (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomV) := by
  refine data.purePair_corner_trace hne (by rw [hsupportOne]; simp)
    (by rw [hsupportTwo]; simp) (by rw [hsupportOne]; simp)
    (by rw [hsupportTwo]; simp) hpureU hpureV ?_
  exact data.identicalPair_wedge_ne_zero hne hUV hUS hVS hsupportOne hsupportTwo

/-! ## Layer 7 — the pure identical triple dies -/

/-- Every slot outside the identical pair misses the shared triple, thus
it IS the complement triple. -/
theorem support_eq_complement_of_pure (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount}
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      ∀ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
        data.tightDir (data.basisLabel other) atomIndex = 0)
    {slot : Fin data.basisCount} (hOne : slot ≠ slotOne) (hTwo : slot ≠ slotTwo) :
    datumTightSupport data.tightDir (data.basisLabel slot)
      = Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)) := by
  classical
  refine data.support_eq_complement_of_disjoint ?_ ?_
  · rw [Finset.card_insert_of_notMem (by simp [hUV, hUS]),
      Finset.card_insert_of_notMem (by simp [hVS]), Finset.card_singleton]
  · intro atomIndex hsupport hshared
    exact data.basis_live_of_mem_support hsupport
      (hpure slot hOne hTwo atomIndex hshared)

/-- **THE PURE IDENTICAL TRIPLE DIES.**  When every atom of the shared
triple carries only the two identical slots, every other slot IS the
complement triple.  Two of them give the landed complement kill.  One of
them exhausts the slots, and then the coefficient trace is the sum of
three captured diagonals — less than one, against a trace of at least
two.  There is no residue. -/
theorem false_of_pure_identical_triple (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS})
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      ∀ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
        data.tightDir (data.basisLabel other) atomIndex = 0) :
    False := by
  classical
  have hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne, hsupportTwo]
  obtain ⟨hprivOne, hprivTwo⟩ := data.privateSlot_notMem_identical_pair hne hsame
  -- the complement triple, named
  have hcomplCard : (Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6))).card = 3 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by simp [hUV, hUS]),
      Finset.card_insert_of_notMem (by simp [hVS]), Finset.card_singleton]
  obtain ⟨atomP, atomQ, atomR, hPQ, hPR, hQR, hcompl⟩ :=
    Finset.card_eq_three.mp hcomplCard
  have hcover : ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
      = Finset.univ := by
    rw [← hcompl, Finset.union_sdiff_self_eq_union]
    exact Finset.eq_univ_of_forall fun atomIndex =>
      Finset.mem_union_right _ (Finset.mem_univ atomIndex)
  -- no slot outside the pair other than the pinned one survives
  have hexhaust : ∀ slot : Fin data.basisCount,
      slot = slotOne ∨ slot = slotTwo ∨ slot = data.privateSlot := by
    intro slot
    by_cases hOne : slot = slotOne
    · exact Or.inl hOne
    by_cases hTwo : slot = slotTwo
    · exact Or.inr (Or.inl hTwo)
    by_cases hPriv : slot = data.privateSlot
    · exact Or.inr (Or.inr hPriv)
    exact absurd (data.false_of_complement_identical_pair hne hPriv hUV hUS hVS
      hPQ hPR hQR hcover hsupportOne hsupportTwo
      (by rw [data.support_eq_complement_of_pure hUV hUS hVS hpure hOne hTwo]
          exact hcompl)
      (by rw [data.support_eq_complement_of_pure hUV hUS hVS hpure hprivOne hprivTwo]
          exact hcompl)) not_false
  -- the trace collapses to three captured diagonals
  have huniv : (Finset.univ : Finset (Fin data.basisCount))
      = {slotOne, slotTwo, data.privateSlot} := by
    refine Finset.eq_of_subset_of_card_le ?_ (Finset.card_le_card (Finset.subset_univ _))
    intro slot _
    rcases hexhaust slot with rfl | rfl | rfl <;> simp
  have hpureU : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomU = 0 :=
    fun other hOne hTwo => hpure other hOne hTwo atomU (by simp)
  have hpureV : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomV = 0 :=
    fun other hOne hTwo => hpure other hOne hTwo atomV (by simp)
  have hcorner := data.identicalPair_corner_trace hne hUV hUS hVS hsupportOne
    hsupportTwo hpureU hpureV
  have htrace : Matrix.trace data.coeff
      = data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
        + data.coeff data.privateSlot data.privateSlot := by
    rw [data.trace_coeff_eq_sum, huniv,
      Finset.sum_insert (by simp [hne, Ne.symm hprivOne]),
      Finset.sum_insert (by simp [Ne.symm hprivTwo]), Finset.sum_singleton]
    ring
  -- the pin atom sits outside the shared triple
  have hpinOut : data.pinAtom ∉ ({atomU, atomV, atomS} : Finset (Fin 6)) := by
    rw [← hsupportOne]
    exact data.pinAtom_notMem_of_identical_support hne hsame
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpinOut
  have hbudget := data.captureDiag_triple_le_total hUV
    (Ne.symm hpinOut.1) (Ne.symm hpinOut.2.1)
  have hlow := data.two_le_trace_coeff
  have hhigh := data.sum_captureDiag_lt_one
  rw [htrace, hcorner, data.hpin] at hlow
  linarith

/-- **THE IMPURE ATOM.**  The identical branch always carries a third
basis slot that reaches the shared triple.  This is the contrapositive of
the pure triple kill. -/
theorem exists_impure_atom_of_identical (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    ∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
      ∧ ∃ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
        atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotThree) := by
  classical
  by_contra hnot
  refine data.false_of_pure_identical_triple hne hUV hUS hVS hsupportOne hsupportTwo
    fun other hOne hTwo atomIndex hshared => ?_
  by_contra hlive
  exact hnot ⟨other, hOne, hTwo, atomIndex, hshared, mem_datumTightSupport.mpr hlive⟩

/-! ## Layer 8 — the pure pair against a private family -/

/-- The private atoms of a slot family are pairwise distinct and distinct
from every atom of a foreign support: a private atom kills every foreign
basis value. -/
theorem privateAtom_notMem_foreign_support (data : SharedPrivateData crux)
    {slot other : Fin data.basisCount} (hne : other ≠ slot) {atomIndex atomOther : Fin 6}
    (hprivate : ∀ third : Fin data.basisCount, third ≠ slot →
      data.tightDir (data.basisLabel third) atomIndex = 0)
    (hforeign : atomOther ∈ datumTightSupport data.tightDir (data.basisLabel other)) :
    atomIndex ≠ atomOther := by
  intro hsame
  refine data.basis_live_of_mem_support hforeign ?_
  rw [← hsame]
  exact hprivate other hne

/-- **THE PURE PAIR AGAINST A PRIVATE FAMILY — A FULL KILL.**  Two slots
with two shared pure atoms pin their corner trace, and every remaining
slot with a private atom pins its own diagonal.  The coefficient trace
then reads as a sum of captured diagonals over distinct atoms, which the
trace cover kill refuses. -/
theorem false_of_purePair_private_family (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6} (hYZ : atomY ≠ atomZ)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0)
    (hrest : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0) :
    False := by
  classical
  have hchoice : ∀ slot : Fin data.basisCount, ∃ atomIndex : Fin 6,
      slot ≠ slotOne → slot ≠ slotTwo →
        (atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0) := by
    intro slot
    by_cases hOne : slot = slotOne
    · exact ⟨atomY, fun hcontra _ => absurd hOne hcontra⟩
    by_cases hTwo : slot = slotTwo
    · exact ⟨atomY, fun _ hcontra => absurd hTwo hcontra⟩
    obtain ⟨atomIndex, hmem, hpriv⟩ := hrest slot hOne hTwo
    exact ⟨atomIndex, fun _ _ => ⟨hmem, hpriv⟩⟩
  choose privateAtom hprop using hchoice
  set outside : Finset (Fin data.basisCount) :=
    Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount)) with houtsideDef
  have hmemOutside : ∀ slot : Fin data.basisCount,
      slot ∈ outside → slot ≠ slotOne ∧ slot ≠ slotTwo := by
    intro slot hslot
    rw [houtsideDef, Finset.mem_sdiff] at hslot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hslot
    exact hslot.2
  have hsplit : Matrix.trace data.coeff
      = (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
        + ∑ slot ∈ outside, data.coeff slot slot := by
    rw [data.trace_coeff_eq_sum, houtsideDef,
      ← Finset.sum_sdiff (Finset.subset_univ ({slotOne, slotTwo} : Finset _)),
      Finset.sum_pair hne]
    ring
  have hdiag : ∀ slot ∈ outside, data.coeff slot slot
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight (privateAtom slot) := by
    intro slot hslot
    obtain ⟨hOne, hTwo⟩ := hmemOutside slot hslot
    obtain ⟨hmem, hpriv⟩ := hprop slot hOne hTwo
    exact data.coeff_diag_of_private hmem hpriv
  have hinjective : ∀ slotA ∈ outside, ∀ slotB ∈ outside,
      privateAtom slotA = privateAtom slotB → slotA = slotB := by
    intro slotA hA slotB hB hsame
    by_contra hdiff
    obtain ⟨hOneA, hTwoA⟩ := hmemOutside slotA hA
    obtain ⟨hOneB, hTwoB⟩ := hmemOutside slotB hB
    obtain ⟨hmemA, _⟩ := hprop slotA hOneA hTwoA
    obtain ⟨_, hprivB⟩ := hprop slotB hOneB hTwoB
    exact data.privateAtom_notMem_foreign_support hdiff hprivB hmemA hsame.symm
  have hYnotImage : atomY ∉ Finset.image privateAtom outside := by
    intro hmem
    obtain ⟨slot, hslot, heq⟩ := Finset.mem_image.mp hmem
    obtain ⟨hOne, hTwo⟩ := hmemOutside slot hslot
    obtain ⟨_, hpriv⟩ := hprop slot hOne hTwo
    exact data.privateAtom_notMem_foreign_support (fun heq' => hOne heq'.symm) hpriv
      hblockYone heq
  have hZnotImage : atomZ ∉ Finset.image privateAtom outside := by
    intro hmem
    obtain ⟨slot, hslot, heq⟩ := Finset.mem_image.mp hmem
    obtain ⟨hOne, hTwo⟩ := hmemOutside slot hslot
    obtain ⟨_, hpriv⟩ := hprop slot hOne hTwo
    exact data.privateAtom_notMem_foreign_support (fun heq' => hOne heq'.symm) hpriv
      hblockZone heq
  have hYnot : atomY ∉ insert atomZ (Finset.image privateAtom outside) := by
    simp only [Finset.mem_insert]
    rintro (heq | himage)
    · exact hYZ heq
    · exact hYnotImage himage
  have hcorner := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  refine data.false_of_trace_eq_captureSum
    (atomSet := insert atomY (insert atomZ (Finset.image privateAtom outside))) ?_
  rw [Finset.sum_insert hYnot, Finset.sum_insert hZnotImage,
    Finset.sum_image hinjective, hsplit, hcorner, Finset.sum_congr rfl hdiag]
  ring

/-- **TWO PURE PAIRS EXHAUST THE TRACE — A FULL KILL.**  Two disjoint
slot pairs, each with two shared pure atoms, that together carry every
basis slot make the coefficient trace a sum of four captured diagonals
over four distinct atoms. -/
theorem false_of_two_purePairs (data : SharedPrivateData crux)
    {slotOne slotTwo slotThree slotFour : Fin data.basisCount}
    (hne : slotOne ≠ slotTwo) (hneOther : slotThree ≠ slotFour)
    (hOneThree : slotOne ≠ slotThree) (hOneFour : slotOne ≠ slotFour)
    (hTwoThree : slotTwo ≠ slotThree) (hTwoFour : slotTwo ≠ slotFour)
    (hexhaust : ∀ slot : Fin data.basisCount,
      slot = slotOne ∨ slot = slotTwo ∨ slot = slotThree ∨ slot = slotFour)
    {atomY atomZ atomP atomQ : Fin 6} (hYZ : atomY ≠ atomZ) (hPQ : atomP ≠ atomQ)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockPthree : atomP ∈ datumTightSupport data.tightDir (data.basisLabel slotThree))
    (hblockPfour : atomP ∈ datumTightSupport data.tightDir (data.basisLabel slotFour))
    (hblockQthree : atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotThree))
    (hblockQfour : atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotFour))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hpureP : ∀ other : Fin data.basisCount, other ≠ slotThree → other ≠ slotFour →
      data.tightDir (data.basisLabel other) atomP = 0)
    (hpureQ : ∀ other : Fin data.basisCount, other ≠ slotThree → other ≠ slotFour →
      data.tightDir (data.basisLabel other) atomQ = 0)
    (hwedgeOne : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0)
    (hwedgeTwo : data.tightDir (data.basisLabel slotThree) atomP
        * data.tightDir (data.basisLabel slotFour) atomQ
      - data.tightDir (data.basisLabel slotThree) atomQ
        * data.tightDir (data.basisLabel slotFour) atomP ≠ 0) :
    False := by
  classical
  have hcornerOne := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedgeOne
  have hcornerTwo := data.purePair_corner_trace hneOther hblockPthree hblockPfour
    hblockQthree hblockQfour hpureP hpureQ hwedgeTwo
  -- the four atoms are pairwise distinct
  have hcross : ∀ atomFirst atomSecond : Fin 6,
      (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
        data.tightDir (data.basisLabel other) atomFirst = 0) →
      atomSecond ∈ datumTightSupport data.tightDir (data.basisLabel slotThree) →
      atomFirst ≠ atomSecond := by
    intro atomFirst atomSecond hpure hmem hsame
    refine data.basis_live_of_mem_support hmem ?_
    rw [← hsame]
    exact hpure slotThree (Ne.symm hOneThree) (Ne.symm hTwoThree)
  have hYP := hcross atomY atomP hpureY hblockPthree
  have hYQ := hcross atomY atomQ hpureY hblockQthree
  have hZP := hcross atomZ atomP hpureZ hblockPthree
  have hZQ := hcross atomZ atomQ hpureZ hblockQthree
  have huniv : (Finset.univ : Finset (Fin data.basisCount))
      = {slotOne, slotTwo, slotThree, slotFour} := by
    refine Finset.eq_of_subset_of_card_le ?_ (Finset.card_le_card (Finset.subset_univ _))
    intro slot _
    rcases hexhaust slot with rfl | rfl | rfl | rfl <;> simp
  have hsplit : Matrix.trace data.coeff
      = (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
        + (data.coeff slotThree slotThree + data.coeff slotFour slotFour) := by
    rw [data.trace_coeff_eq_sum, huniv,
      Finset.sum_insert (by simp [hne, hOneThree, hOneFour]),
      Finset.sum_insert (by simp [hTwoThree, hTwoFour]),
      Finset.sum_insert (by simp [hneOther]), Finset.sum_singleton]
    ring
  have hYnot : atomY ∉ ({atomZ, atomP, atomQ} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq | heq)
    · exact hYZ heq
    · exact hYP heq
    · exact hYQ heq
  have hZnot : atomZ ∉ ({atomP, atomQ} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq)
    · exact hZP heq
    · exact hZQ heq
  refine data.false_of_trace_eq_captureSum
    (atomSet := ({atomY, atomZ, atomP, atomQ} : Finset (Fin 6))) ?_
  rw [Finset.sum_insert hYnot, Finset.sum_insert hZnot,
    Finset.sum_insert (by simp [hPQ]), Finset.sum_singleton, hsplit, hcornerOne,
    hcornerTwo]
  ring

/-- **THE IMPURE SLOT.**  Once two atoms of the shared triple carry only
the identical pair, some further basis slot has NO atom of basis
multiplicity one.  This is the contrapositive of the private family
kill, and it is a new narrowing of the identical branch. -/
theorem exists_impure_slot_of_purePair (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6} (hYZ : atomY ≠ atomZ)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0) :
    ∃ slot : Fin data.basisCount, slot ≠ slotOne ∧ slot ≠ slotTwo
      ∧ ∀ atomIndex : Fin 6,
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          ∃ other : Fin data.basisCount, other ≠ slot
            ∧ data.tightDir (data.basisLabel other) atomIndex ≠ 0 := by
  classical
  by_contra hnot
  refine data.false_of_purePair_private_family hne hYZ hblockYone hblockYtwo
    hblockZone hblockZtwo hpureY hpureZ hwedge fun slot hOne hTwo => ?_
  by_contra hslot
  refine hnot ⟨slot, hOne, hTwo, fun atomIndex hmem => ?_⟩
  by_contra hall
  refine hslot ⟨atomIndex, hmem, fun other hother => ?_⟩
  by_contra hlive
  exact hall ⟨other, hother, hlive⟩

/-! ## Layer 9 — the pinned slot and the remaining trace -/

/-- The pin atom is a private atom of the pinned slot. -/
theorem pinAtom_mem_privateSlot_support (data : SharedPrivateData crux) :
    data.pinAtom
      ∈ datumTightSupport data.tightDir (data.basisLabel data.privateSlot) :=
  mem_datumTightSupport.mpr data.hpinNe

/-- **THE IMPURE SLOT IS A FOURTH SLOT.**  The pinned slot carries the pin
atom privately, thus the slot with no private atom is neither of the
identical pair AND is not the pinned slot.  Two pure atoms of the shared
triple therefore force a fourth basis slot. -/
theorem exists_impure_slot_ne_privateSlot (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6} (hYZ : atomY ≠ atomZ)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0) :
    ∃ slot : Fin data.basisCount, slot ≠ slotOne ∧ slot ≠ slotTwo
      ∧ slot ≠ data.privateSlot
      ∧ ∀ atomIndex : Fin 6,
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          ∃ other : Fin data.basisCount, other ≠ slot
            ∧ data.tightDir (data.basisLabel other) atomIndex ≠ 0 := by
  obtain ⟨slot, hOne, hTwo, himpure⟩ := data.exists_impure_slot_of_purePair hne hYZ
    hblockYone hblockYtwo hblockZone hblockZtwo hpureY hpureZ hwedge
  refine ⟨slot, hOne, hTwo, ?_, himpure⟩
  intro hpriv
  subst hpriv
  obtain ⟨other, hother, hlive⟩ := himpure data.pinAtom data.pinAtom_mem_privateSlot_support
  exact hlive (data.hprivate other hother)

/-- **THE REMAINING TRACE EXCEEDS ONE.**  With two pure atoms of the
shared triple the identical pair pays exactly their captured diagonals
and the pinned slot pays the pin's captured diagonal.  The three atoms
are distinct, thus they total less than one, and the remaining slots must
carry more than one unit of coefficient diagonal. -/
theorem purePair_remaining_trace_gt_one (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hprivOne : data.privateSlot ≠ slotOne) (hprivTwo : data.privateSlot ≠ slotTwo)
    {atomY atomZ : Fin 6} (hYZ : atomY ≠ atomZ)
    (hYpin : atomY ≠ data.pinAtom) (hZpin : atomZ ≠ data.pinAtom)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0) :
    1 < ∑ slot ∈ Finset.univ \ ({slotOne, slotTwo, data.privateSlot}
        : Finset (Fin data.basisCount)), data.coeff slot slot := by
  classical
  have hcorner := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  have hsplit : Matrix.trace data.coeff
      = ∑ slot ∈ Finset.univ \ ({slotOne, slotTwo, data.privateSlot}
          : Finset (Fin data.basisCount)), data.coeff slot slot
        + (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
          + data.coeff data.privateSlot data.privateSlot) := by
    rw [data.trace_coeff_eq_sum,
      ← Finset.sum_sdiff (Finset.subset_univ
        ({slotOne, slotTwo, data.privateSlot} : Finset (Fin data.basisCount))),
      Finset.sum_insert (by simp [hne, Ne.symm hprivOne]),
      Finset.sum_insert (by simp [Ne.symm hprivTwo]), Finset.sum_singleton]
    ring
  have hbudget := data.captureDiag_triple_le_total hYZ hYpin hZpin
  have hlow := data.two_le_trace_coeff
  have hhigh := data.sum_captureDiag_lt_one
  rw [hsplit, hcorner, data.hpin] at hlow
  linarith

/-! ## Layer 10 — the pair corner determinant -/

/-- The four solved entries of the pair corner.  Cramer against the value
wedge reads every entry of the two-by-two corner from the two captured
diagonals and the four basis values. -/
theorem purePair_corner_solved (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6}
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0) :
    (data.tightDir (data.basisLabel slotOne) atomY
          * data.tightDir (data.basisLabel slotTwo) atomZ
        - data.tightDir (data.basisLabel slotOne) atomZ
          * data.tightDir (data.basisLabel slotTwo) atomY)
        * data.coeff slotOne slotOne
      = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomY)
          * (data.tightDir (data.basisLabel slotOne) atomY
            * data.tightDir (data.basisLabel slotTwo) atomZ)
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomZ)
          * (data.tightDir (data.basisLabel slotOne) atomZ
            * data.tightDir (data.basisLabel slotTwo) atomY) := by
  have hYone := data.pairRow_capture hne hblockYone hpureY
  have hZone := data.pairRow_capture hne hblockZone hpureZ
  linear_combination data.tightDir (data.basisLabel slotTwo) atomZ * hYone
    - data.tightDir (data.basisLabel slotTwo) atomY * hZone

/-- The second solved entry of the pair corner. -/
theorem purePair_corner_solved_second (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6}
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0) :
    (data.tightDir (data.basisLabel slotOne) atomY
          * data.tightDir (data.basisLabel slotTwo) atomZ
        - data.tightDir (data.basisLabel slotOne) atomZ
          * data.tightDir (data.basisLabel slotTwo) atomY)
        * data.coeff slotTwo slotTwo
      = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomZ)
          * (data.tightDir (data.basisLabel slotOne) atomY
            * data.tightDir (data.basisLabel slotTwo) atomZ)
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomY)
          * (data.tightDir (data.basisLabel slotOne) atomZ
            * data.tightDir (data.basisLabel slotTwo) atomY) := by
  have hYtwo := data.pairRow_capture hne hblockYtwo hpureY
  have hZtwo := data.pairRow_capture hne hblockZtwo hpureZ
  linear_combination data.tightDir (data.basisLabel slotOne) atomY * hZtwo
    - data.tightDir (data.basisLabel slotOne) atomZ * hYtwo

/-- **THE PAIR CORNER DETERMINANT.**  Two pure atoms with independent
value pairs pin the determinant of the two-by-two coefficient corner to
the product of the two captured diagonals.  Together with the corner
trace this pins the characteristic polynomial of the corner. -/
theorem purePair_corner_det (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6}
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0) :
    data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
        - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomY)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomZ) := by
  have hYone := data.pairRow_capture hne hblockYone hpureY
  have hYtwo := data.pairRow_capture hne hblockYtwo hpureY
  have hZone := data.pairRow_capture hne hblockZone hpureZ
  have hZtwo := data.pairRow_capture hne hblockZtwo hpureZ
  have hsolveOne := data.purePair_corner_solved hne hblockYone hblockZone hpureY hpureZ
  have hsolveTwo := data.purePair_corner_solved_second hne hblockYtwo hblockZtwo
    hpureY hpureZ
  have hcross : (data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY)
      * data.coeff slotTwo slotOne
      = data.tightDir (data.basisLabel slotOne) atomY
          * data.tightDir (data.basisLabel slotOne) atomZ
        * ((chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomZ)
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomY)) := by
    linear_combination data.tightDir (data.basisLabel slotOne) atomY * hZone
      - data.tightDir (data.basisLabel slotOne) atomZ * hYone
  have hcrossTwo : (data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY)
      * data.coeff slotOne slotTwo
      = data.tightDir (data.basisLabel slotTwo) atomY
          * data.tightDir (data.basisLabel slotTwo) atomZ
        * ((chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomY)
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomZ)) := by
    linear_combination data.tightDir (data.basisLabel slotTwo) atomZ * hYtwo
      - data.tightDir (data.basisLabel slotTwo) atomY * hZtwo
  have hkey : (data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY)
      * ((data.tightDir (data.basisLabel slotOne) atomY
          * data.tightDir (data.basisLabel slotTwo) atomZ
        - data.tightDir (data.basisLabel slotOne) atomZ
          * data.tightDir (data.basisLabel slotTwo) atomY)
        * (data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
            - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne
          - (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomY)
            * (chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomZ))) = 0 := by
    linear_combination (data.coeff slotTwo slotTwo
        * (data.tightDir (data.basisLabel slotOne) atomY
            * data.tightDir (data.basisLabel slotTwo) atomZ
          - data.tightDir (data.basisLabel slotOne) atomZ
            * data.tightDir (data.basisLabel slotTwo) atomY)) * hsolveOne
      + ((chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomY)
          * (data.tightDir (data.basisLabel slotOne) atomY
            * data.tightDir (data.basisLabel slotTwo) atomZ)
        - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomZ)
          * (data.tightDir (data.basisLabel slotOne) atomZ
            * data.tightDir (data.basisLabel slotTwo) atomY)) * hsolveTwo
      - (data.coeff slotTwo slotOne
          * (data.tightDir (data.basisLabel slotOne) atomY
              * data.tightDir (data.basisLabel slotTwo) atomZ
            - data.tightDir (data.basisLabel slotOne) atomZ
              * data.tightDir (data.basisLabel slotTwo) atomY)) * hcrossTwo
      - (data.tightDir (data.basisLabel slotTwo) atomY
          * data.tightDir (data.basisLabel slotTwo) atomZ
          * ((chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
            - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomZ))) * hcross
  have hinner := (mul_eq_zero.mp hkey).resolve_left hwedge
  have hfinal := (mul_eq_zero.mp hinner).resolve_left hwedge
  linarith

end SharedPrivateData

/-! ## Layer 11 — the identical residue on the coefficient lattice -/

/-- **THE COEFFICIENT IDENTICAL RESIDUE.**  The identical-support branch
carries every payment of the slot-split lattice AND the four label
payments of the coefficient row law:

* the coefficient trace is at least two,
* the captured diagonals total less than one,
* every atom of basis multiplicity one reads its slot's diagonal,
* two atoms of the shared triple that carry only the two slots pin the
  corner trace to the sum of their captured diagonals,
* a third basis slot reaches the shared triple.

Only the case that some atom of the shared triple carries a third slot,
and the coefficient diagonal of the remaining slots absorbs the whole
trace, remains open. -/
def SharedPrivateCircuitPairIdenticalCoeffClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomU atomV atomS : Fin 6, atomU ≠ atomV → atomU ≠ atomS → atomV ≠ atomS →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomU, atomV, atomS} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomU, atomV, atomS} →
        GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS →
        data.pinAtom ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomV
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 1 →
        1 - 6 * chartObjective (chartPointOfDesign crux.design)
          ≤ ∑ atomIndex ∈ Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex →
        (∀ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
          shiftedGapDiag (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (chartObjective (chartPointOfDesign crux.design)) atomY
              * ((∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
                    shiftedGapDiag (chartPointOfDesign crux.design).chart
                      (chartPointOfDesign crux.design).weight
                      (chartObjective (chartPointOfDesign crux.design)) atomIndex)
                + 2 * (chartObjective (chartPointOfDesign crux.design)
                  + (chartPointOfDesign crux.design).weight atomY) - 1)
            ≤ (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
              * (1 - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY))) →
        (∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
          ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
              = Finset.univ →
          ¬ GapBlockRankOne (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomP atomQ atomR) →
        -- the singular block budget at every basis support
        (∀ slot : Fin data.basisCount,
          ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex ≤ 2) →
        -- the pin slot is a genuine third slot with a different support
        (data.privateSlot ≠ slotOne ∧ data.privateSlot ≠ slotTwo
          ∧ datumTightSupport data.tightDir (data.basisLabel data.privateSlot)
            ≠ ({atomU, atomV, atomS} : Finset (Fin 6))) →
        -- no second identical pair on the complement triple
        (∀ slotThree slotFour : Fin data.basisCount,
          ∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
            ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
                = Finset.univ →
            slotThree ≠ slotFour →
            datumTightSupport data.tightDir (data.basisLabel slotThree)
              = {atomP, atomQ, atomR} →
            datumTightSupport data.tightDir (data.basisLabel slotFour)
              = {atomP, atomQ, atomR} →
            False) →
        -- every straddling support pays a single unit
        (∀ slotThree : Fin data.basisCount, ∀ atomY atomZ atomW : Fin 6,
          atomY ≠ atomZ → atomY ≠ atomW → atomZ ≠ atomW →
            atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
            atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
            datumTightSupport data.tightDir (data.basisLabel slotThree)
              = {atomY, atomZ, atomW} →
            shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomY
              + shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomZ
              + shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomW ≤ 1) →
        -- the coefficient trace is at least two
        (2 : ℝ) ≤ Matrix.trace data.coeff →
        -- the captured diagonals total less than one
        (∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) < 1 →
        -- every atom of basis multiplicity one reads its slot's diagonal
        (∀ slot : Fin data.basisCount, ∀ atomIndex : Fin 6,
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          (∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0) →
          data.coeff slot slot = chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) →
        -- two pure atoms of the shared triple pin the corner trace
        (∀ atomY atomZ : Fin 6, atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
          atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomY = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomZ = 0) →
          data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
              + (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomZ)) →
        -- a third basis slot reaches the shared triple
        (∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
          ∧ ∃ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
            atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotThree)) →
        -- two pure atoms of the shared triple force a slot with no private atom
        (∀ atomY atomZ : Fin 6, atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
          atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomY = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomZ = 0) →
          (∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
            ∧ slotThree ≠ data.privateSlot
            ∧ ∀ atomIndex : Fin 6,
                atomIndex
                  ∈ datumTightSupport data.tightDir (data.basisLabel slotThree) →
                ∃ other : Fin data.basisCount, other ≠ slotThree
                  ∧ data.tightDir (data.basisLabel other) atomIndex ≠ 0)
          -- and the remaining slots carry more than one unit of trace
          ∧ 1 < ∑ slot ∈ Finset.univ \ ({slotOne, slotTwo, data.privateSlot}
              : Finset (Fin data.basisCount)), data.coeff slot slot) →
        False

/-- **THE COEFFICIENT PAYMENT BRIDGE.**  Every hypothesis that the
coefficient residue adds is a theorem at the datum, thus the coefficient
residue closes the slot-split residue. -/
theorem sharedPrivateCircuitPairIdenticalSlotClosed_of_coeff
    (hpaid : SharedPrivateCircuitPairIdenticalCoeffClosed) :
    SharedPrivateCircuitPairIdenticalSlotClosed := by
  classical
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle
  have hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne, hsupportTwo]
  obtain ⟨hprivOne, hprivTwo⟩ := data.privateSlot_notMem_identical_pair hne hsame
  have hpinDistinct : ∀ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
      atomY ≠ data.pinAtom := by
    intro atomY hY heq
    rw [heq] at hY
    exact data.pinAtom_notMem_of_identical_support hne hsame (by rw [hsupportOne]; exact hY)
  -- the three free wedges of the shared triple, from the rank-one minors
  have hwedgeUV := data.identicalPair_wedge_ne_zero hne hUV hUS hVS hsupportOne
    hsupportTwo
  have hwedgeUS := data.identicalPair_wedge_ne_zero hne hUS hUV (Ne.symm hVS)
    (by rw [hsupportOne, Finset.pair_comm atomV atomS])
    (by rw [hsupportTwo, Finset.pair_comm atomV atomS])
  have hwedgeVS := data.identicalPair_wedge_ne_zero hne hVS (Ne.symm hUV)
    (Ne.symm hUS)
    (by rw [hsupportOne]
        ext atomIndex
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto)
    (by rw [hsupportTwo]
        ext atomIndex
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto)
  have hwedgeAll : ∀ atomY atomZ : Fin 6,
      atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
      atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
      data.tightDir (data.basisLabel slotOne) atomY
          * data.tightDir (data.basisLabel slotTwo) atomZ
        - data.tightDir (data.basisLabel slotOne) atomZ
          * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0 := by
    intro atomY atomZ hY hZ hYZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY hZ
    rcases hY with rfl | rfl | rfl <;> rcases hZ with rfl | rfl | rfl
    · exact absurd rfl hYZ
    · exact hwedgeUV
    · exact hwedgeUS
    · intro hzero; exact hwedgeUV (by linarith)
    · exact absurd rfl hYZ
    · exact hwedgeVS
    · intro hzero; exact hwedgeUS (by linarith)
    · intro hzero; exact hwedgeVS (by linarith)
    · exact absurd rfl hYZ
  exact hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle
    data.two_le_trace_coeff data.sum_captureDiag_lt_one
    (fun slot atomIndex hblock hprivate =>
      data.coeff_diag_of_private hblock hprivate)
    (fun atomY atomZ hY hZ hYZ hpureY hpureZ =>
      data.purePair_corner_trace hne (by rw [hsupportOne]; exact hY)
        (by rw [hsupportTwo]; exact hY) (by rw [hsupportOne]; exact hZ)
        (by rw [hsupportTwo]; exact hZ) hpureY hpureZ (hwedgeAll atomY atomZ hY hZ hYZ))
    (data.exists_impure_atom_of_identical hne hUV hUS hVS hsupportOne hsupportTwo)
    fun atomY atomZ hY hZ hYZ hpureY hpureZ =>
      ⟨data.exists_impure_slot_ne_privateSlot hne hYZ (by rw [hsupportOne]; exact hY)
        (by rw [hsupportTwo]; exact hY) (by rw [hsupportOne]; exact hZ)
        (by rw [hsupportTwo]; exact hZ) hpureY hpureZ
        (hwedgeAll atomY atomZ hY hZ hYZ),
       data.purePair_remaining_trace_gt_one hne hprivOne hprivTwo hYZ
        (hpinDistinct atomY hY) (hpinDistinct atomZ hZ)
        (by rw [hsupportOne]; exact hY) (by rw [hsupportTwo]; exact hY)
        (by rw [hsupportOne]; exact hZ) (by rw [hsupportTwo]; exact hZ)
        hpureY hpureZ (hwedgeAll atomY atomZ hY hZ hYZ)⟩

/-! ## Layer 10 — closure two on the coefficient lattice -/

/-- **THE EXTRAS ON THE COEFFICIENT LATTICE.** -/
theorem sharedPrivateExtrasClosed_of_coeffLattice
    (hidentical : SharedPrivateCircuitPairIdenticalCoeffClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_slotLattice
    (sharedPrivateCircuitPairIdenticalSlotClosed_of_coeff hidentical) hwedgeLive
    hwedgeDead hwide

/-- **CLOSURE TWO FROM THE FOUR CIRCUIT RESIDUES ON THE COEFFICIENT
LATTICE.**  The boundary stratum is a theorem and a datum never has a
diagonal Gram core, thus the extras residue IS the generic kill. -/
theorem sharedPrivateKilled_of_coeff_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCoeffClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_slotSplit_circuit
    (sharedPrivateCircuitPairIdenticalSlotClosed_of_coeff hidentical) hwedgeLive
    hwedgeDead hwide

/-- Closure two of the rank-four rung on the coefficient lattice. -/
theorem rankFourSharedPrivateClosed_of_coeff_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCoeffClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_slotSplit_circuit
    (sharedPrivateCircuitPairIdenticalSlotClosed_of_coeff hidentical) hwedgeLive
    hwedgeDead hwide

/-- The shared-private closure of the rank-five rung on the coefficient
lattice.  The rank-five rung still carries this closure on its critical
path. -/
theorem rankFiveSharedPrivateClosed_of_coeff_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCoeffClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_slotSplit_circuit
    (sharedPrivateCircuitPairIdenticalSlotClosed_of_coeff hidentical) hwedgeLive
    hwedgeDead hwide

/-- The shared-private closure of the rank-six rung on the coefficient
lattice. -/
theorem rankSixSharedPrivateClosed_of_coeff_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCoeffClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_slotSplit_circuit
    (sharedPrivateCircuitPairIdenticalSlotClosed_of_coeff hidentical) hwedgeLive
    hwedgeDead hwide

end Gtz

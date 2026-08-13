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

/-! ## Layer 4 — the private family trace kill -/

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
  have hlow := data.two_le_trace_coeff
  have hhigh := data.sum_captureDiag_lt_one
  rw [htrace, ← himage] at hlow
  linarith

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

end SharedPrivateData

/-! ## Layer 8 — the identical residue on the coefficient lattice -/

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
  refine hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle
    data.two_le_trace_coeff data.sum_captureDiag_lt_one
    (fun slot atomIndex hblock hprivate =>
      data.coeff_diag_of_private hblock hprivate)
    (fun atomY atomZ hY hZ hYZ hpureY hpureZ => ?_)
    (data.exists_impure_atom_of_identical hne hUV hUS hVS hsupportOne hsupportTwo)
  refine data.purePair_corner_trace hne (by rw [hsupportOne]; exact hY)
    (by rw [hsupportTwo]; exact hY) (by rw [hsupportOne]; exact hZ)
    (by rw [hsupportTwo]; exact hZ) hpureY hpureZ ?_
  -- the wedge of the two value pairs comes from the rank-one minors
  simp only [Finset.mem_insert, Finset.mem_singleton] at hY hZ
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

/-! ## Layer 9 — closure two on the coefficient lattice -/

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

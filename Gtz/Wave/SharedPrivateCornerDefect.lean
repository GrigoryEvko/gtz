import Gtz.Wave.SharedPrivateCoefficientRow
import Gtz.Wave.PlaneCapTripleClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The corner defect kill — the pure pair closes the identical branch at
basis count four

The identical branch survived CERT-B19 in one narrow shape: two pure
atoms of the shared triple, a pinned slot, and a fourth slot with no
private atom, whose coefficient diagonal exceeds one.  This module kills
that shape, and with it the whole identical branch at basis count at
most four.

## The corner defect law

For an idempotent matrix, each principal corner `M` obeys
`M - M * M = B * C`, where `B` and `C` are the two off-corner blocks.
At basis count four the two complementary corners are both two by two,
thus `det (M - M * M) = det B * det C = det (D - D * D)`.

The pure pair pins the left corner: its characteristic polynomial is
`(t - dY) * (t - dZ)`, thus `det (M - M * M) = dY dZ (1-dY) (1-dZ) > 0`.

The other two slots share a live atom outside the shared triple.  The
two row laws at that atom pin the product of the opposite cross entries:
`cps * csp = (dX - cpp) * (dX - css)`.  With the trace, the right corner
defect determinant factors as `dX (s - dX) (1 - dX) (1 + dX - s)` with
`s = trace - dY - dZ`.  The trace is at least two and the three captured
diagonals total less than one, thus `s > 1 + dX` and the right side is
negative.  One inequality, and the shape is dead.

## The dispatch at basis count at most four

Two pure atoms force every further slot to draw its support from the
third shared atom and the two complement atoms away from the pin.  If
every further slot keeps a private atom, the landed trace cover kill
fires.  If some slot has none, that slot and the pinned slot share a
live atom outside the shared triple, the basis count is exactly four,
and the corner defect law fires.  Thus the identical branch with two
pure atoms needs at least five basis slots.

## Vacuity

The scalar law is unconditional.  The datum statements quantify over
shared-private data, and no shared-private datum exists if
`Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the scalar corner defect law -/

section ScalarCore

/-- **THE CORNER DEFECT KILL.**  Sixteen entries of an idempotent four by
four matrix, the two corner readings of a pure pair, the trace floor,
and the two row laws at one shared live atom refuse the domain: the left
corner defect determinant is positive and the right one is negative. -/
theorem cornerDefect_pair_kill {c11 c12 c21 c22 c1p c1s c2p c2s
    cp1 cp2 cs1 cs2 cpp cps csp css dY dZ dX traceSum vpx vsx : ℝ}
    (h11 : c11 * c11 + (c12 * c21 + (c1p * cp1 + c1s * cs1)) = c11)
    (h12 : c11 * c12 + (c12 * c22 + (c1p * cp2 + c1s * cs2)) = c12)
    (h21 : c21 * c11 + (c22 * c21 + (c2p * cp1 + c2s * cs1)) = c21)
    (h22 : c21 * c12 + (c22 * c22 + (c2p * cp2 + c2s * cs2)) = c22)
    (hpp : cp1 * c1p + (cp2 * c2p + (cpp * cpp + cps * csp)) = cpp)
    (hps : cp1 * c1s + (cp2 * c2s + (cpp * cps + cps * css)) = cps)
    (hsp : cs1 * c1p + (cs2 * c2p + (csp * cpp + css * csp)) = csp)
    (hss : cs1 * c1s + (cs2 * c2s + (csp * cps + css * css)) = css)
    (hMtr : c11 + c22 = dY + dZ)
    (hMdet : c11 * c22 - c12 * c21 = dY * dZ)
    (htrace : c11 + (c22 + (cpp + css)) = traceSum)
    (h2T : 2 ≤ traceSum)
    (hrowP : vpx * cpp + vsx * csp = dX * vpx)
    (hrowS : vpx * cps + vsx * css = dX * vsx)
    (hvp : vpx ≠ 0) (hvs : vsx ≠ 0)
    (hdY : 0 < dY) (hdZ : 0 < dZ) (hdX : 0 < dX)
    (hsum : dY + dZ + dX < 1) : False := by
  have hcolP : vsx * csp = (dX - cpp) * vpx := by linear_combination hrowP
  have hcolS : vpx * cps = (dX - css) * vsx := by linear_combination hrowS
  have hpiMul : vpx * vsx * (cps * csp)
      = vpx * vsx * ((dX - cpp) * (dX - css)) := by
    linear_combination vpx * cps * hcolP + (dX - cpp) * vpx * hcolS
  have hpi : cps * csp = (dX - cpp) * (dX - css) :=
    mul_left_cancel₀ (mul_ne_zero hvp hvs) hpiMul
  have hb11 : c11 - (c11 * c11 + c12 * c21) = c1p * cp1 + c1s * cs1 := by
    linear_combination -h11
  have hb12 : c12 - (c11 * c12 + c12 * c22) = c1p * cp2 + c1s * cs2 := by
    linear_combination -h12
  have hb21 : c21 - (c21 * c11 + c22 * c21) = c2p * cp1 + c2s * cs1 := by
    linear_combination -h21
  have hb22 : c22 - (c21 * c12 + c22 * c22) = c2p * cp2 + c2s * cs2 := by
    linear_combination -h22
  have hcPP : cpp - (cpp * cpp + cps * csp) = cp1 * c1p + cp2 * c2p := by
    linear_combination -hpp
  have hcPS : cps - (cpp * cps + cps * css) = cp1 * c1s + cp2 * c2s := by
    linear_combination -hps
  have hcSP : csp - (csp * cpp + css * csp) = cs1 * c1p + cs2 * c2p := by
    linear_combination -hsp
  have hcSS : css - (csp * cps + css * css) = cs1 * c1s + cs2 * c2s := by
    linear_combination -hss
  have hdetM : (c11 - (c11 * c11 + c12 * c21)) * (c22 - (c21 * c12 + c22 * c22))
      - (c12 - (c11 * c12 + c12 * c22)) * (c21 - (c21 * c11 + c22 * c21))
      = (c1p * c2s - c1s * c2p) * (cp1 * cs2 - cp2 * cs1) := by
    linear_combination (c22 - (c21 * c12 + c22 * c22)) * hb11
      + (c1p * cp1 + c1s * cs1) * hb22
      - (c21 - (c21 * c11 + c22 * c21)) * hb12
      - (c1p * cp2 + c1s * cs2) * hb21
  have hdetD : (cpp - (cpp * cpp + cps * csp)) * (css - (csp * cps + css * css))
      - (cps - (cpp * cps + cps * css)) * (csp - (csp * cpp + css * csp))
      = (cp1 * cs2 - cp2 * cs1) * (c1p * c2s - c1s * c2p) := by
    linear_combination (css - (csp * cps + css * css)) * hcPP
      + (cp1 * c1p + cp2 * c2p) * hcSS
      - (csp - (csp * cpp + css * csp)) * hcPS
      - (cp1 * c1s + cp2 * c2s) * hcSP
  have hMvalue : (c11 - (c11 * c11 + c12 * c21)) * (c22 - (c21 * c12 + c22 * c22))
      - (c12 - (c11 * c12 + c12 * c22)) * (c21 - (c21 * c11 + c22 * c21))
      = dY * dZ * (1 - dY - dZ + dY * dZ) := by
    linear_combination (1 - (c11 + c22) + (c11 * c22 - c12 * c21) + dY * dZ) * hMdet
      - dY * dZ * hMtr
  have hsig : cpp + css = traceSum - dY - dZ := by linarith
  have hDvalue : (cpp - (cpp * cpp + cps * csp)) * (css - (csp * cps + css * css))
      - (cps - (cpp * cps + cps * css)) * (csp - (csp * cpp + css * csp))
      = dX * (traceSum - dY - dZ - dX) * (1 - dX)
        * (1 + dX - (traceSum - dY - dZ)) := by
    linear_combination (1 - (cpp + css) + (cpp * css - cps * csp)
        + dX * (traceSum - dY - dZ - dX)) * (dX * hsig - hpi)
      - dX * (traceSum - dY - dZ - dX) * hsig
  have hkill : dY * dZ * (1 - dY - dZ + dY * dZ)
      = dX * (traceSum - dY - dZ - dX) * (1 - dX)
        * (1 + dX - (traceSum - dY - dZ)) := by
    linear_combination -hMvalue + hdetM - hdetD + hDvalue
  have hposL : 0 < dY * dZ * (1 - dY - dZ + dY * dZ) := by
    nlinarith [mul_pos (mul_pos hdY hdZ)
      (mul_pos (by linarith : (0:ℝ) < 1 - dY) (by linarith : (0:ℝ) < 1 - dZ))]
  have hposA : 0 < dX * (traceSum - dY - dZ - dX) :=
    mul_pos hdX (by linarith)
  have hnegB : (1 - dX) * (1 + dX - (traceSum - dY - dZ)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  nlinarith [hkill, hposL, mul_neg_of_pos_of_neg hposA hnegB]

end ScalarCore

/-! ## Layer 2 — the triple reorder -/

/-- A triple of distinct atoms lists any two named members first.  The
reorder feeds the corner lemmas, whose pure atoms are the first two
atoms of the shared triple. -/
theorem exists_triple_reorder {atomU atomV atomS atomY atomZ : Fin 6}
    (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS) (hVS : atomV ≠ atomS)
    (hY : atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)))
    (hZ : atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)))
    (hYZ : atomY ≠ atomZ) :
    ∃ atomW : Fin 6, atomY ≠ atomW ∧ atomZ ≠ atomW
      ∧ ({atomU, atomV, atomS} : Finset (Fin 6)) = {atomY, atomZ, atomW} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hY hZ
  rcases hY with rfl | rfl | rfl <;> rcases hZ with rfl | rfl | rfl
  · exact absurd rfl hYZ
  · exact ⟨atomS, hUS, hVS, rfl⟩
  · refine ⟨atomV, hUV, Ne.symm hVS, ?_⟩
    ext atomIndex
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨atomS, hVS, hUS, ?_⟩
    ext atomIndex
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact absurd rfl hYZ
  · refine ⟨atomU, Ne.symm hUV, Ne.symm hUS, ?_⟩
    ext atomIndex
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨atomV, Ne.symm hVS, hUV, ?_⟩
    ext atomIndex
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨atomU, Ne.symm hUS, Ne.symm hUV, ?_⟩
    ext atomIndex
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact absurd rfl hYZ

/-! ## Layer 3 — the datum instance of the corner defect kill -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **THE OFF-TRIPLE LINK KILL.**  Four basis slots: an identical pair on
a shared triple with two pure atoms, and two further slots that share a
live atom outside the triple.  The corner defect law refuses the
configuration.  This is the CERT-B19 fourth-slot survivor, dead. -/
theorem false_of_purePair_offTriple_link (data : SharedPrivateData crux)
    {slotOne slotTwo slotP slotS : Fin data.basisCount}
    (hne : slotOne ≠ slotTwo)
    (hPone : slotP ≠ slotOne) (hPtwo : slotP ≠ slotTwo)
    (hSone : slotS ≠ slotOne) (hStwo : slotS ≠ slotTwo) (hPS : slotP ≠ slotS)
    (huniv : (Finset.univ : Finset (Fin data.basisCount))
      = {slotOne, slotTwo, slotP, slotS})
    {atomY atomZ atomW atomX : Fin 6} (hYZ : atomY ≠ atomZ)
    (hYW : atomY ≠ atomW) (hZW : atomZ ≠ atomW)
    (hXY : atomX ≠ atomY) (hXZ : atomX ≠ atomZ) (hXW : atomX ≠ atomW)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomY, atomZ, atomW})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomY, atomZ, atomW})
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hXmemP : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotP))
    (hXmemS : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotS)) :
    False := by
  classical
  have hdeadOneX : data.tightDir (data.basisLabel slotOne) atomX = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportOne]; simp [hXY, hXZ, hXW])
  have hdeadTwoX : data.tightDir (data.basisLabel slotTwo) atomX = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportTwo]; simp [hXY, hXZ, hXW])
  have hliveP : data.tightDir (data.basisLabel slotP) atomX ≠ 0 :=
    data.basis_live_of_mem_support hXmemP
  have hliveS : data.tightDir (data.basisLabel slotS) atomX ≠ 0 :=
    data.basis_live_of_mem_support hXmemS
  -- the sixteen idempotency readings on the four named slots
  have hentry : ∀ rowIdx colIdx : Fin data.basisCount,
      data.coeff rowIdx slotOne * data.coeff slotOne colIdx
        + (data.coeff rowIdx slotTwo * data.coeff slotTwo colIdx
        + (data.coeff rowIdx slotP * data.coeff slotP colIdx
        + data.coeff rowIdx slotS * data.coeff slotS colIdx)) = data.coeff rowIdx colIdx := by
    intro rowIdx colIdx
    have hmul := congrFun (congrFun data.hidempotent rowIdx) colIdx
    rw [Matrix.mul_apply, huniv,
      Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
      Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
      Finset.sum_insert (by simp [hPS]), Finset.sum_singleton] at hmul
    exact hmul
  -- the two row laws of the shared live atom
  have hrowP := data.basisRow_capture slotP hXmemP
  rw [huniv, Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
    Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
    Finset.sum_insert (by simp [hPS]), Finset.sum_singleton,
    hdeadOneX, hdeadTwoX, zero_mul, zero_mul, zero_add, zero_add] at hrowP
  have hrowS := data.basisRow_capture slotS hXmemS
  rw [huniv, Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
    Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
    Finset.sum_insert (by simp [hPS]), Finset.sum_singleton,
    hdeadOneX, hdeadTwoX, zero_mul, zero_mul, zero_add, zero_add] at hrowS
  -- the pure pair corner
  have hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hwedge := data.identicalPair_wedge_ne_zero hne hYZ hYW hZW hsupportOne hsupportTwo
  have hcornerTr := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  have hcornerDet := data.purePair_corner_det hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  -- the trace on the four named slots
  have htraceExpand : data.coeff slotOne slotOne + (data.coeff slotTwo slotTwo
      + (data.coeff slotP slotP + data.coeff slotS slotS)) = Matrix.trace data.coeff := by
    rw [data.trace_coeff_eq_sum, huniv,
      Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
      Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
      Finset.sum_insert (by simp [hPS]), Finset.sum_singleton]
  -- the domain facts
  have hdYpos := crux.shifted_weight_pos atomY
  have hdZpos := crux.shifted_weight_pos atomZ
  have hdXpos := crux.shifted_weight_pos atomX
  have htriple := data.captureDiag_triple_le_total hYZ (Ne.symm hXY) (Ne.symm hXZ)
  have htotal := data.sum_captureDiag_lt_one
  exact cornerDefect_pair_kill
    (hentry slotOne slotOne) (hentry slotOne slotTwo)
    (hentry slotTwo slotOne) (hentry slotTwo slotTwo)
    (hentry slotP slotP) (hentry slotP slotS)
    (hentry slotS slotP) (hentry slotS slotS)
    hcornerTr hcornerDet htraceExpand data.two_le_trace_coeff
    hrowP hrowS hliveP hliveS hdYpos hdZpos hdXpos (by linarith)

/-- **THE PURE PAIR NEEDS FIVE SLOTS.**  An identical pair with two pure
atoms of its shared triple refuses every basis count up to four.  If
every further slot keeps a private atom, the trace cover kill fires.  If
some slot has none, that slot and the pinned slot share a live atom
outside the shared triple and the corner defect law fires. -/
theorem false_of_purePair_of_basisCount_le_four (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS})
    {atomY atomZ : Fin 6} (hY : atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)))
    (hZ : atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6))) (hYZ : atomY ≠ atomZ)
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hcount : data.basisCount ≤ 4) : False := by
  classical
  obtain ⟨atomW, hYW, hZW, hsetEq⟩ := exists_triple_reorder hUV hUS hVS hY hZ hYZ
  rw [hsetEq] at hsupportOne hsupportTwo
  have hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne, hsupportTwo]
  have hwedge := data.identicalPair_wedge_ne_zero hne hYZ hYW hZW hsupportOne hsupportTwo
  have hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  by_cases hallPriv : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0
  · exact data.false_of_purePair_private_family hne hYZ hblockYone hblockYtwo
      hblockZone hblockZtwo hpureY hpureZ hwedge hallPriv
  · obtain ⟨slotS, hSbad⟩ := not_forall.mp hallPriv
    rw [Classical.not_imp, Classical.not_imp] at hSbad
    obtain ⟨hSone, hStwo, hSnoPriv⟩ := hSbad
    obtain ⟨hPone, hPtwo⟩ := data.privateSlot_notMem_identical_pair hne hsame
    have hSp : slotS ≠ data.privateSlot := by
      intro heq
      refine hSnoPriv ⟨data.pinAtom, ?_, fun other hother => ?_⟩
      · rw [heq]; exact data.pinAtom_mem_privateSlot_support
      · rw [heq] at hother
        exact data.hprivate other hother
    have hpinOut : data.pinAtom ∉ ({atomY, atomZ, atomW} : Finset (Fin 6)) := by
      rw [← hsupportOne]
      exact data.pinAtom_notMem_of_identical_support hne hsame
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpinOut
    obtain ⟨hpinY, hpinZ, hpinW⟩ := hpinOut
    -- the four named slots exhaust the basis
    have hcard4 : ({slotOne, slotTwo, data.privateSlot, slotS}
        : Finset (Fin data.basisCount)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hSp]), Finset.card_singleton]
    have huniv : (Finset.univ : Finset (Fin data.basisCount))
        = {slotOne, slotTwo, data.privateSlot, slotS} := by
      refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
      rw [Finset.card_univ, Fintype.card_fin, hcard4]
      exact hcount
    -- a live atom of the pinned slot outside the triple and the pin
    have hXex : ∃ atomX ∈ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot),
        atomX ≠ atomY ∧ atomX ≠ atomZ ∧ atomX ≠ atomW ∧ atomX ≠ data.pinAtom := by
      by_contra hnone
      have hsub : datumTightSupport data.tightDir (data.basisLabel data.privateSlot)
          ⊆ {atomW, data.pinAtom} := by
        intro atomA hmemA
        have hliveA := data.basis_live_of_mem_support hmemA
        have hAY : atomA ≠ atomY := by
          intro heq
          rw [heq] at hliveA
          exact hliveA (hpureY data.privateSlot hPone hPtwo)
        have hAZ : atomA ≠ atomZ := by
          intro heq
          rw [heq] at hliveA
          exact hliveA (hpureZ data.privateSlot hPone hPtwo)
        by_contra hout
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
        exact hnone ⟨atomA, hmemA, hAY, hAZ, hout.1, hout.2⟩
      have hthreeP := data.hthree data.privateSlot
      have hle := Finset.card_le_card hsub
      have htwoCard : ({atomW, data.pinAtom} : Finset (Fin 6)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      omega
    obtain ⟨atomX, hXmemP, hXY, hXZ, hXW, hXpin⟩ := hXex
    -- the private-atom-free slot lives on the whole complement of the pure
    -- pair and the pin, thus at the shared live atom
    have hcompl : ((Finset.univ : Finset (Fin 6))
        \ {atomY, atomZ, data.pinAtom}).card = 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (by simp [hYZ, Ne.symm hpinY]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hpinZ]), Finset.card_singleton]
    have hsubS : datumTightSupport data.tightDir (data.basisLabel slotS)
        ⊆ Finset.univ \ {atomY, atomZ, data.pinAtom} := by
      intro atomA hmemA
      have hliveA := data.basis_live_of_mem_support hmemA
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        rw [heq] at hliveA
        exact hliveA (hpureY slotS hSone hStwo)
      · intro heq
        rw [heq] at hliveA
        exact hliveA (hpureZ slotS hSone hStwo)
      · intro heq
        rw [heq] at hliveA
        exact hliveA (data.hprivate slotS hSp)
    have hsuppSeq : datumTightSupport data.tightDir (data.basisLabel slotS)
        = Finset.univ \ {atomY, atomZ, data.pinAtom} :=
      Finset.eq_of_subset_of_card_le hsubS
        (by rw [hcompl, data.hthree slotS])
    have hXmemS : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotS) := by
      rw [hsuppSeq, Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, by simp [hXY, hXZ, hXpin]⟩
    exact data.false_of_purePair_offTriple_link hne hPone hPtwo hSone hStwo
      (Ne.symm hSp) huniv hYZ hYW hZW hXY hXZ hXW hsupportOne hsupportTwo
      hpureY hpureZ hXmemP hXmemS

end SharedPrivateData

/-! ## Layer 4 — the identical residue above basis count four -/

/-- **THE COUNTED IDENTICAL RESIDUE.**  The coefficient residue plus the
new payment: two pure atoms of the shared triple force at least five
basis slots.  At basis count four the CERT-B19 fourth-slot survivor is
dead, thus the identical branch now needs either a second impure atom or
a basis count of five or six. -/
def SharedPrivateCircuitPairIdenticalCountClosed : Prop :=
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
        (∀ slot : Fin data.basisCount,
          ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex ≤ 2) →
        (data.privateSlot ≠ slotOne ∧ data.privateSlot ≠ slotTwo
          ∧ datumTightSupport data.tightDir (data.basisLabel data.privateSlot)
            ≠ ({atomU, atomV, atomS} : Finset (Fin 6))) →
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
        (2 : ℝ) ≤ Matrix.trace data.coeff →
        (∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) < 1 →
        (∀ slot : Fin data.basisCount, ∀ atomIndex : Fin 6,
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          (∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0) →
          data.coeff slot slot = chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) →
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
        (∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
          ∧ ∃ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
            atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotThree)) →
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
          ∧ 1 < ∑ slot ∈ Finset.univ \ ({slotOne, slotTwo, data.privateSlot}
              : Finset (Fin data.basisCount)), data.coeff slot slot) →
        -- two pure atoms of the shared triple force at least five slots
        (∀ atomY atomZ : Fin 6, atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
          atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomY = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomZ = 0) →
          5 ≤ data.basisCount) →
        False

/-- **THE COUNT PAYMENT BRIDGE.**  The five-slot floor of the pure pair
is a theorem at the datum, thus the counted residue closes the
coefficient residue. -/
theorem sharedPrivateCircuitPairIdenticalCoeffClosed_of_count
    (hpaid : SharedPrivateCircuitPairIdenticalCountClosed) :
    SharedPrivateCircuitPairIdenticalCoeffClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle htraceLow
    hcapture hdiag hcorner himpure hfourth
  refine hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
    hpair atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin
    hbudget hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle
    htraceLow hcapture hdiag hcorner himpure hfourth ?_
  intro atomY atomZ hY hZ hYZ hpureY hpureZ
  by_contra hlt
  exact data.false_of_purePair_of_basisCount_le_four hne hUV hUS hVS hsupportOne
    hsupportTwo hY hZ hYZ hpureY hpureZ (by omega)

/-! ## Layer 5 — closure two on the counted lattice -/

/-- **THE EXTRAS ON THE COUNTED LATTICE.** -/
theorem sharedPrivateExtrasClosed_of_countLattice
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_coeffLattice
    (sharedPrivateCircuitPairIdenticalCoeffClosed_of_count hidentical) hwedgeLive
    hwedgeDead hwide

/-- **CLOSURE TWO FROM THE FOUR CIRCUIT RESIDUES ON THE COUNTED
LATTICE.**  The identical residue now needs at least five basis slots
whenever the shared triple keeps two pure atoms. -/
theorem sharedPrivateKilled_of_count_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_coeff_circuit
    (sharedPrivateCircuitPairIdenticalCoeffClosed_of_count hidentical) hwedgeLive
    hwedgeDead hwide

/-- Closure two of the rank-four rung on the counted lattice. -/
theorem rankFourSharedPrivateClosed_of_count_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_coeff_circuit
    (sharedPrivateCircuitPairIdenticalCoeffClosed_of_count hidentical) hwedgeLive
    hwedgeDead hwide

/-- The shared-private closure of the rank-five rung on the counted
lattice. -/
theorem rankFiveSharedPrivateClosed_of_count_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_coeff_circuit
    (sharedPrivateCircuitPairIdenticalCoeffClosed_of_count hidentical) hwedgeLive
    hwedgeDead hwide

/-- The shared-private closure of the rank-six rung on the counted
lattice. -/
theorem rankSixSharedPrivateClosed_of_count_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeSlotClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_coeff_circuit
    (sharedPrivateCircuitPairIdenticalCoeffClosed_of_count hidentical) hwedgeLive
    hwedgeDead hwide

end Gtz

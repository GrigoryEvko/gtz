/-
# The rank-two hinge fires along every transversal axis: planar compression,
# the pair budget, and the drop-on-plane conditional

Built on `Gtz.rankTwoFourDirectionHinge_holds`.  Three unconditional facts and
one wired conditional:

* **Compression is free.**  Parseval restricts to any orthonormal pair of
  directions, so the rank-two companion of a rank-three design along ANY plane
  is again a genuine weighted design (`planarCompressionDesign`) — no tight
  axis, no moment identities, no reweighting.  The four exact tight-axis moments are
  needed by the EXCHANGE machinery, not by the companion.

* **The naive pair lift is structurally impossible.**  No pair of a rank-three
  design ever weakly dominates (`not_dominates_pair_rank_three`): the pair's
  moment has rank at most two, and the direction orthogonal to both atoms sees
  the gap form as `-(witness . witness) < 0`.  So the hinge's PosDef pair can
  never be transported to a weakly dominating pair upstairs; every transport
  must route through a third atom, and the third atom is where the wall lives.

* **The hinge fires on every tie.**  At any tie of any size, for any unit axis
  and any four atoms pairwise transversal to it (no two coplanar with the
  axis), some pair strictly dominates the orthogonal plane
  (`exists_planeStrictPair_of_isTie_of_transversalAxis`).  The conclusion is in
  the exact handover shape `Gtz.posDef_exchangeTriple_of_planarPairStrict`
  consumes.  Measured caveat (exact rationals, diamond): the transversality
  census fails at four of the diamond's eight tight triples — exactly those
  omitting the spine atom; at each, three atoms share one plane through the
  axis — and holds at the other four, so the four-transversal hypothesis is
  genuinely a hypothesis at a tight axis, though some tight triple of every
  known tie satisfies it.

* **The wired conditional.**  `TightDropOnPlaneSixThree` — some tight triple
  has a drop atom exactly ON the tight plane whose remaining pair dominates the
  plane strictly — implies `Gtz.StressFreeHingeHoldsSixThree` outright
  (`stressFreeHingeHoldsSixThree_of_tightDropOnPlane`), by the landed exchange
  transport plus the free off-plane insert.  At the `(5,3)` diamond the
  drop-on-plane half fails at every tight triple (axis masses
  `3/4, 1/8, 1/8, 2, 2`), while the pair-strictness half HOLDS at every tight
  triple — so the conditional concentrates the whole branch-(i) residual into
  the single quantity `g_drop . axis`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Ties.RepeatedAtomExclusion
import Gtz.Design.StratumTieFreeClasses
import Gtz.Design.StressFreeNormalizer
import Gtz.Reduction.TrichotomyLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 1: no pair of a rank-three design weakly dominates

This kernel-checks the pre-refutation of the naive non-strict pair transport:
"ask for the pair's domination non-strictly upstairs" is not a weakening, it is
an impossibility, at every size and every pair. -/

/-- **A PAIR NEVER WEAKLY DOMINATES AT RANK THREE.**  The witness orthogonal to
both atoms sees the pair's gap form as minus its own squared length. -/
theorem not_dominates_pair_rank_three (design : WeightedDesign size 3)
    (leftLabel rightLabel : Fin size) (hlabelNe : leftLabel ≠ rightLabel) :
    ¬ Dominates design {leftLabel, rightLabel} := by
  intro hdominates
  obtain ⟨witness, hwitnessNe, hleftZero, hrightZero⟩ :=
    exists_ne_zero_dotProduct_pair_eq_zero (design.atom leftLabel) (design.atom rightLabel)
  have hgapValue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 witness
  rw [star_trivial, dominationGap_form, Finset.sum_pair hlabelNe, hleftZero,
    hrightZero] at hgapValue
  have hwitnessNormPos : 0 < witness ⬝ᵥ witness := dotProduct_self_pos hwitnessNe
  nlinarith [hgapValue, hwitnessNormPos]

/-! ## Part 2: completeness of an orthonormal frame -/

/-- **Expansion in an orthonormal frame.**  Three pairwise orthogonal unit
vectors of `ℝ³` resolve every vector: the row matrix is orthogonal, and a
square one-sided inverse is two-sided. -/
theorem orthonormalFrame_expansion {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (vec : Fin 3 → ℝ) :
    vec = (vec ⬝ᵥ pOne) • pOne + (vec ⬝ᵥ pTwo) • pTwo + (vec ⬝ᵥ axis) • axis := by
  set frameMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![pOne, pTwo, axis]
    with hframeDef
  have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  have hAxisOne : axis ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneAxis
  have hAxisTwo : axis ⬝ᵥ pTwo = 0 := by rw [dotProduct_comm]; exact hTwoAxis
  have hgram : frameMatrix * frameMatrixᵀ = 1 := by
    ext rowIndex colIndex
    have hentry : (frameMatrix * frameMatrixᵀ) rowIndex colIndex
        = (![pOne, pTwo, axis] rowIndex) ⬝ᵥ (![pOne, pTwo, axis] colIndex) := by
      rw [Matrix.mul_apply, dotProduct]
      exact Finset.sum_congr rfl fun summandIndex _ => by
        rw [Matrix.transpose_apply]
        rfl
    rw [hentry]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.one_apply, hOneOne, hTwoTwo, hAxisAxis, hOneTwo, hOneAxis, hTwoAxis,
        hTwoOne, hAxisOne, hAxisTwo]
  have hcomm : frameMatrixᵀ * frameMatrix = 1 := mul_eq_one_comm.mp hgram
  have happly : frameMatrixᵀ *ᵥ (frameMatrix *ᵥ vec) = vec := by
    rw [Matrix.mulVec_mulVec, hcomm, Matrix.one_mulVec]
  funext coord
  have hcoord := congrFun happly coord
  have hlhs : (frameMatrixᵀ *ᵥ (frameMatrix *ᵥ vec)) coord
      = (vec ⬝ᵥ pOne) * pOne coord + (vec ⬝ᵥ pTwo) * pTwo coord
        + (vec ⬝ᵥ axis) * axis coord := by
    simp only [hframeDef, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply,
      dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hlhs] at hcoord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact hcoord.symm

/-! ## Part 3: the rank-two compression along any orthonormal plane -/

/-- **THE COMPANION IS FREE.**  Compressing a rank-three weighted design to any
orthonormal pair of directions yields a genuine rank-two weighted design: the
weights are untouched and Parseval restricts entrywise.  Nothing about tight
axes, moments, or rescaling enters — those belong to the transport, not to the
companion. -/
noncomputable def planarCompressionDesign (design : WeightedDesign size 3)
    (pOne pTwo : Fin 3 → ℝ) (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hOneTwo : pOne ⬝ᵥ pTwo = 0) : WeightedDesign size 2 where
  atom label := ![design.atom label ⬝ᵥ pOne, design.atom label ⬝ᵥ pTwo]
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := by
    have hentrySum : ∀ rowIndex colIndex : Fin 2,
        (∑ label, design.weight label • atomMatrix
            (![design.atom label ⬝ᵥ pOne, design.atom label ⬝ᵥ pTwo] : Fin 2 → ℝ))
            rowIndex colIndex
          = ∑ label, design.weight label
              * ((![design.atom label ⬝ᵥ pOne, design.atom label ⬝ᵥ pTwo] : Fin 2 → ℝ)
                    rowIndex
                * (![design.atom label ⬝ᵥ pOne, design.atom label ⬝ᵥ pTwo] : Fin 2 → ℝ)
                    colIndex) := by
      intro rowIndex colIndex
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun label _ => by
        simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
    refine Matrix.ext ?_
    rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · rw [hentrySum]
        simp only [Matrix.cons_val_zero]
        rw [sum_weighted_atomPairing design pOne pOne, hOneOne, Matrix.one_apply_eq]
      · rw [hentrySum]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sum_weighted_atomPairing design pOne pTwo, hOneTwo,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
    · rw [Fin.forall_fin_two]
      constructor
      · rw [hentrySum]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sum_weighted_atomPairing design pTwo pOne, hTwoOne,
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      · rw [hentrySum]
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [sum_weighted_atomPairing design pTwo pTwo, hTwoTwo, Matrix.one_apply_eq]

/-- The compression's atoms, unfolded. -/
theorem planarCompressionDesign_atom (design : WeightedDesign size 3)
    (pOne pTwo : Fin 3 → ℝ) (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hOneTwo : pOne ⬝ᵥ pTwo = 0) (label : Fin size) :
    (planarCompressionDesign design pOne pTwo hOneOne hTwoTwo hOneTwo).atom label
      = ![design.atom label ⬝ᵥ pOne, design.atom label ⬝ᵥ pTwo] := rfl

/-- **The compression's bracket is a Binet-Cauchy pairing** — a polynomial
identity with no hypotheses: the two-by-two minor of the compressed pair equals
the pairing of the frame's cross product with the atoms' cross product. -/
theorem planarCompression_pairBracket (design : WeightedDesign size 3)
    (pOne pTwo : Fin 3 → ℝ) (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hOneTwo : pOne ⬝ᵥ pTwo = 0) (leftLabel rightLabel : Fin size) :
    pairBracket (planarCompressionDesign design pOne pTwo hOneOne hTwoTwo hOneTwo)
        leftLabel rightLabel
      = crossProduct pOne pTwo
          ⬝ᵥ crossProduct (design.atom leftLabel) (design.atom rightLabel) := by
  rw [pairBracket, planarCompressionDesign_atom, planarCompressionDesign_atom]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, cross_apply,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The frame's cross product is the axis up to a unit sign.**  For an
orthonormal frame `(pOne, pTwo, axis)` the cross product `pOne x pTwo` is
orthogonal to the plane, hence a multiple of the axis, and Lagrange pins the
multiplier's square at one. -/
theorem crossProduct_orthonormalFrame_eq_smul_axis {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0) :
    crossProduct pOne pTwo = (crossProduct pOne pTwo ⬝ᵥ axis) • axis
      ∧ (crossProduct pOne pTwo ⬝ᵥ axis) ^ 2 = 1 := by
  have hcrossOne : crossProduct pOne pTwo ⬝ᵥ pOne = 0 := by
    rw [dotProduct_comm]; exact planarCross_probe_dot pOne pTwo
  have hcrossTwo : crossProduct pOne pTwo ⬝ᵥ pTwo = 0 := by
    rw [dotProduct_comm]; exact planarCross_seed_dot pOne pTwo
  have hexpand := orthonormalFrame_expansion hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis (crossProduct pOne pTwo)
  rw [hcrossOne, hcrossTwo, zero_smul, zero_smul, zero_add, zero_add] at hexpand
  refine ⟨hexpand, ?_⟩
  have hnorm : crossProduct pOne pTwo ⬝ᵥ crossProduct pOne pTwo = 1 := by
    rw [planarCross_self_dot, hOneOne, hTwoTwo, hOneTwo]
    norm_num
  calc (crossProduct pOne pTwo ⬝ᵥ axis) ^ 2
      = ((crossProduct pOne pTwo ⬝ᵥ axis) • axis)
          ⬝ᵥ ((crossProduct pOne pTwo ⬝ᵥ axis) • axis) := by
        rw [smul_dotProduct, dotProduct_smul, hAxisAxis, smul_eq_mul, smul_eq_mul]
        ring
    _ = 1 := by rw [← hexpand, hnorm]

/-! ## Part 4: the hinge fires on every design, along every transversal axis -/

/-- **THE PLANE-STRICT PAIR EXISTS AT EVERY DESIGN — no tie hypothesis.**
Given any unit axis, an orthonormal frame of its plane, and four atoms of the
design pairwise transversal to the axis (no two coplanar with it — the six
triple products are nonzero), the rank-two compression is a genuine design
whose four compressed atoms are pairwise non-parallel; the landed hinge
`Gtz.rankTwoFourDirectionHinge_holds` then returns a pair that dominates the
companion STRICTLY, and completeness of the frame reads that back as strict
domination of the plane.  The conclusion is the exact `hpairStrict` shape of
`Gtz.posDef_exchangeTriple_of_planarPairStrict`, restricted to a two-element
carrier.

Note what is NOT here: `IsTie`.  The hinge is a theorem about ALL rank-two
designs, so plane-strict pairs are unconditional structure of the rank-three
cell; ties are special only in that the pair's axis coupling never pays
there. -/
theorem exists_planeStrictPair_of_fourTransversal
    (design : WeightedDesign size 3)
    {axis pOne pTwo : Fin 3 → ℝ}
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneOne : pOne ⬝ᵥ pOne = 1)
    (hTwoTwo : pTwo ⬝ᵥ pTwo = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour)
    (htransversalOneTwo :
      crossProduct (design.atom labelOne) (design.atom labelTwo) ⬝ᵥ axis ≠ 0)
    (htransversalOneThree :
      crossProduct (design.atom labelOne) (design.atom labelThree) ⬝ᵥ axis ≠ 0)
    (htransversalOneFour :
      crossProduct (design.atom labelOne) (design.atom labelFour) ⬝ᵥ axis ≠ 0)
    (htransversalTwoThree :
      crossProduct (design.atom labelTwo) (design.atom labelThree) ⬝ᵥ axis ≠ 0)
    (htransversalTwoFour :
      crossProduct (design.atom labelTwo) (design.atom labelFour) ⬝ᵥ axis ≠ 0)
    (htransversalThreeFour :
      crossProduct (design.atom labelThree) (design.atom labelFour) ⬝ᵥ axis ≠ 0) :
    ∃ strongLabel otherLabel : Fin size, strongLabel ≠ otherLabel
      ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          planar ⬝ᵥ planar
            < (design.atom strongLabel ⬝ᵥ planar) ^ 2
              + (design.atom otherLabel ⬝ᵥ planar) ^ 2 := by
  classical
  set companion := planarCompressionDesign design pOne pTwo hOneOne hTwoTwo hOneTwo
    with hcompanionDef
  obtain ⟨horient, horientSq⟩ := crossProduct_orthonormalFrame_eq_smul_axis hOneOne hTwoTwo
    hAxisAxis hOneTwo hOneAxis hTwoAxis
  have horientNe : crossProduct pOne pTwo ⬝ᵥ axis ≠ 0 := by
    intro hzero
    rw [hzero] at horientSq
    norm_num at horientSq
  have hbracket : ∀ leftLabel rightLabel : Fin size,
      crossProduct (design.atom leftLabel) (design.atom rightLabel) ⬝ᵥ axis ≠ 0 →
      pairBracket companion leftLabel rightLabel ≠ 0 := by
    intro leftLabel rightLabel htransversal
    rw [hcompanionDef, planarCompression_pairBracket, horient, smul_dotProduct, smul_eq_mul]
    exact mul_ne_zero horientNe fun hzero =>
      htransversal (by rw [dotProduct_comm]; exact hzero)
  obtain ⟨dominatingPair, hpairCard, hpairPosDef⟩ :=
    rankTwoFourDirectionHinge_holds size companion labelOne labelTwo labelThree labelFour
      hneOneTwo hneOneThree hneOneFour hneTwoThree hneTwoFour hneThreeFour
      (hbracket _ _ htransversalOneTwo) (hbracket _ _ htransversalOneThree)
      (hbracket _ _ htransversalOneFour) (hbracket _ _ htransversalTwoThree)
      (hbracket _ _ htransversalTwoFour) (hbracket _ _ htransversalThreeFour)
  obtain ⟨strongLabel, otherLabel, hlabelNe, hpairEq⟩ := Finset.card_eq_two.mp hpairCard
  refine ⟨strongLabel, otherLabel, hlabelNe, fun planar hplanarPerp hplanarNe => ?_⟩
  have hexpandPlanar := orthonormalFrame_expansion hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis planar
  rw [hplanarPerp, zero_smul, add_zero] at hexpandPlanar
  set testVec : Fin 2 → ℝ := ![planar ⬝ᵥ pOne, planar ⬝ᵥ pTwo] with htestDef
  have htestNe : testVec ≠ 0 := by
    intro hzero
    have hcoordOne : planar ⬝ᵥ pOne = 0 := by
      have hcomponent := congrFun hzero 0
      simpa [htestDef] using hcomponent
    have hcoordTwo : planar ⬝ᵥ pTwo = 0 := by
      have hcomponent := congrFun hzero 1
      simpa [htestDef] using hcomponent
    rw [hcoordOne, hcoordTwo, zero_smul, zero_smul, zero_add] at hexpandPlanar
    exact hplanarNe hexpandPlanar
  have hquad := quadForm_gt_of_posDef_pair companion dominatingPair hpairPosDef testVec htestNe
  rw [hpairEq, Finset.sum_pair hlabelNe] at hquad
  have hatomPairing : ∀ label : Fin size,
      companion.atom label ⬝ᵥ testVec = design.atom label ⬝ᵥ planar := by
    intro label
    conv_rhs => rw [hexpandPlanar]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hcompanionDef,
      planarCompressionDesign_atom, htestDef]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, smul_eq_mul]
    ring
  have hbilinear : planar ⬝ᵥ planar
      = (planar ⬝ᵥ pOne) * (planar ⬝ᵥ pOne) + (planar ⬝ᵥ pTwo) * (planar ⬝ᵥ pTwo) := by
    have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
    conv_lhs => rw [hexpandPlanar]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hOneOne, hTwoTwo, hOneTwo, hTwoOne]
    ring
  have hnormSplit : testVec ⬝ᵥ testVec = planar ⬝ᵥ planar := by
    rw [hbilinear, htestDef]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  rw [hatomPairing strongLabel, hatomPairing otherLabel, hnormSplit] at hquad
  exact hquad

/-! ## Part 5: an orthonormal frame under every unit axis -/

/-- Every unit axis of `ℝ³` extends to an orthonormal frame of its orthogonal
plane. -/
theorem exists_orthonormal_planarFrame {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1) :
    ∃ pOne pTwo : Fin 3 → ℝ,
      pOne ⬝ᵥ pOne = 1 ∧ pTwo ⬝ᵥ pTwo = 1 ∧ pOne ⬝ᵥ pTwo = 0
        ∧ pOne ⬝ᵥ axis = 0 ∧ pTwo ⬝ᵥ axis = 0 := by
  classical
  by_cases hseedZero : (![axis 1, -axis 0, 0] : Fin 3 → ℝ) = 0
  · -- the axis is the third coordinate direction, up to sign
    have hFirstZero : axis 0 = 0 := by
      have hcomponent := congrFun hseedZero 1
      simpa using hcomponent
    have hSecondZero : axis 1 = 0 := by
      have hcomponent := congrFun hseedZero 0
      simpa using hcomponent
    have hThirdSq : axis 2 ^ 2 = 1 := by
      have hnorm := hunit
      simp only [dotProduct, Fin.sum_univ_three, hFirstZero, hSecondZero] at hnorm
      nlinarith [hnorm]
    refine ⟨![1, 0, 0], ![0, axis 2, 0], ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [dotProduct, Fin.sum_univ_three, hFirstZero, hSecondZero] <;>
      nlinarith [hThirdSq]
  · set seedVec : Fin 3 → ℝ := ![axis 1, -axis 0, 0] with hseedDef
    have hseedNormPos : 0 < seedVec ⬝ᵥ seedVec := dotProduct_self_pos hseedZero
    have hsqrtPos : 0 < Real.sqrt (seedVec ⬝ᵥ seedVec) := Real.sqrt_pos.mpr hseedNormPos
    set pOne : Fin 3 → ℝ := (Real.sqrt (seedVec ⬝ᵥ seedVec))⁻¹ • seedVec with hpOneDef
    have hOneOne : pOne ⬝ᵥ pOne = 1 := by
      rw [hpOneDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← mul_inv, Real.mul_self_sqrt hseedNormPos.le]
      exact inv_mul_cancel₀ hseedNormPos.ne'
    have hseedAxis : seedVec ⬝ᵥ axis = 0 := by
      simp only [hseedDef, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    have hOneAxis : pOne ⬝ᵥ axis = 0 := by
      rw [hpOneDef, smul_dotProduct, hseedAxis, smul_eq_mul, mul_zero]
    set pTwo : Fin 3 → ℝ := crossProduct axis pOne with hpTwoDef
    have hAxisOne : axis ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneAxis
    have hTwoTwo : pTwo ⬝ᵥ pTwo = 1 := by
      rw [hpTwoDef, planarCross_self_dot, hunit, hOneOne, hAxisOne]
      norm_num
    have hOneTwo : pOne ⬝ᵥ pTwo = 0 := by
      rw [hpTwoDef]
      exact planarCross_seed_dot axis pOne
    have hTwoAxis : pTwo ⬝ᵥ axis = 0 := by
      rw [dotProduct_comm, hpTwoDef]
      exact planarCross_probe_dot axis pOne
    exact ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩

/-- **The frame-free form.**  At every design, along every unit axis, four
pairwise transversal atoms force a pair that strictly dominates the axis
plane. -/
theorem exists_planeStrictPair_of_transversalAxis
    (design : WeightedDesign size 3)
    {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    {labelOne labelTwo labelThree labelFour : Fin size}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour)
    (htransversalOneTwo :
      crossProduct (design.atom labelOne) (design.atom labelTwo) ⬝ᵥ axis ≠ 0)
    (htransversalOneThree :
      crossProduct (design.atom labelOne) (design.atom labelThree) ⬝ᵥ axis ≠ 0)
    (htransversalOneFour :
      crossProduct (design.atom labelOne) (design.atom labelFour) ⬝ᵥ axis ≠ 0)
    (htransversalTwoThree :
      crossProduct (design.atom labelTwo) (design.atom labelThree) ⬝ᵥ axis ≠ 0)
    (htransversalTwoFour :
      crossProduct (design.atom labelTwo) (design.atom labelFour) ⬝ᵥ axis ≠ 0)
    (htransversalThreeFour :
      crossProduct (design.atom labelThree) (design.atom labelFour) ⬝ᵥ axis ≠ 0) :
    ∃ strongLabel otherLabel : Fin size, strongLabel ≠ otherLabel
      ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          planar ⬝ᵥ planar
            < (design.atom strongLabel ⬝ᵥ planar) ^ 2
              + (design.atom otherLabel ⬝ᵥ planar) ^ 2 := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  exact exists_planeStrictPair_of_fourTransversal design hunit hOneOne hTwoTwo
    hOneTwo hOneAxis hTwoAxis hneOneTwo hneOneThree hneOneFour hneTwoThree hneTwoFour
    hneThreeFour htransversalOneTwo htransversalOneThree htransversalOneFour
    htransversalTwoThree htransversalTwoFour htransversalThreeFour

/-! ## Part 6: the wired conditional for branch (i)

The exchange transport `Gtz.posDef_exchangeTriple_of_planarPairStrict` needs a
drop atom ON the tight plane and the remaining pair strict on it; the insert
atom is free (`Gtz.exists_outside_axisMass_ge`).  This packages the composition
so that the branch-(i) residual is a single named `Prop`. -/

/-- **A tight triple with an on-plane drop and a plane-strict remaining pair
kills the tie**, at six points and rank three.  The off-plane insert is
supplied by the axis Parseval identity. -/
theorem sixThree_not_isTie_of_dropOnPlane_of_pairPlaneStrict
    (design : WeightedDesign 6 3) {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hdominates : Dominates design selected) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel : Fin 6} (hdrop : dropLabel ∈ selected)
    (hdropOnPlane : design.atom dropLabel ⬝ᵥ axis = 0)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < ∑ atomIndex ∈ selected.erase dropLabel, (design.atom atomIndex ⬝ᵥ planar) ^ 2) :
    ¬ IsTie design := by
  classical
  intro htie
  have hproper : selectedᶜ.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  obtain ⟨addLabel, haddMem, haddBig⟩ := exists_outside_axisMass_ge design hproper htight
  have haddNot : addLabel ∉ selected := Finset.mem_compl.mp haddMem
  have haddOffPlane : design.atom addLabel ⬝ᵥ axis ≠ 0 := by
    intro hzero
    rw [hzero, hunit] at haddBig
    norm_num at haddBig
  refine htie.2 (insert addLabel (selected.erase dropLabel)) ?_
    (posDef_exchangeTriple_of_planarPairStrict design hdominates hunit htight hdrop haddNot
      hdropOnPlane haddOffPlane hpairStrict)
  rw [card_exchangeSubset selected hdrop haddNot, hcard]

/-- **THE BRANCH-(i) RESIDUAL, AS ONE NAMED PROP.**  Every stress-free `(6,3)`
tie has a tight triple with a drop atom exactly on the tight plane whose
remaining pair dominates the plane strictly.

Both halves are calibrated against the `(5,3)` diamond in exact rationals:
the PAIR-STRICTNESS half holds at every one of its eight tight triples (so it
is not the obstruction), while the ON-PLANE half fails at every one of them
(axis masses `3/4, 1/8, 1/8, 2, 2` — never zero).  The residual therefore
concentrates branch (i) into the single scalar `g_drop . axis`, and any proof
of it must use stress-freeness or six-ness, since the diamond refutes the
statement at five points with the stress-freeness clause dropped. -/
def TightDropOnPlaneSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∀ stress : Fin 6 → ℝ,
      (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stress = 0) →
    IsTie design →
    ∃ (selected : Finset (Fin 6)) (axis : Fin 3 → ℝ) (dropLabel : Fin 6),
      selected.card = 3 ∧ Dominates design selected ∧ axis ⬝ᵥ axis = 1
        ∧ axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0
        ∧ dropLabel ∈ selected ∧ design.atom dropLabel ⬝ᵥ axis = 0
        ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
            planar ⬝ᵥ planar
              < ∑ atomIndex ∈ selected.erase dropLabel,
                  (design.atom atomIndex ⬝ᵥ planar) ^ 2

/-- **The conditional, wired end to end**: the named residual closes branch (i)
of the `(6,3)` stress trichotomy. -/
theorem stressFreeHingeHoldsSixThree_of_tightDropOnPlane
    (hresidual : TightDropOnPlaneSixThree) : StressFreeHingeHoldsSixThree := by
  intro design hstressFree htie
  exfalso
  obtain ⟨selected, axis, dropLabel, hcard, hdominates, hunit, htight, hdrop, hdropOnPlane,
    hpairStrict⟩ := hresidual design hstressFree htie
  exact sixThree_not_isTie_of_dropOnPlane_of_pairPlaneStrict design hcard hdominates hunit
    htight hdrop hdropOnPlane hpairStrict htie


/-! # PART TWO: the pair-det gate and the pair budget -/

/-! ## Part 1: scalar LDL cores -/

/-- **The LDL sum of squares for a ternary quadratic.**  Clearing denominators
in the Cholesky decomposition: the form times `a * (ac - b^2)` is a weighted
sum of three squares whose weights are the three leading minors. -/
theorem ldl_clearing_identity (aa bb cc dd ee ff x y z : ℝ) :
    aa * (aa * cc - bb ^ 2)
        * (aa * x ^ 2 + 2 * bb * (x * y) + cc * y ^ 2 + 2 * dd * (x * z)
          + 2 * ee * (y * z) + ff * z ^ 2)
      = (aa * cc - bb ^ 2) * (aa * x + bb * y + dd * z) ^ 2
        + ((aa * cc - bb ^ 2) * y + (aa * ee - bb * dd) * z) ^ 2
        + aa * (aa * (cc * ff - ee ^ 2) - bb * (bb * ff - ee * dd)
            + dd * (bb * ee - cc * dd)) * z ^ 2 := by
  ring

/-- Positive leading minors make the ternary form positive away from zero. -/
theorem posQuadForm_of_frameMinors {aa bb cc dd ee ff x y z : ℝ}
    (haPos : 0 < aa) (hminorPos : 0 < aa * cc - bb ^ 2)
    (hdetPos : 0 < aa * (cc * ff - ee ^ 2) - bb * (bb * ff - ee * dd)
        + dd * (bb * ee - cc * dd))
    (hcoordsNe : ¬ (x = 0 ∧ y = 0 ∧ z = 0)) :
    0 < aa * x ^ 2 + 2 * bb * (x * y) + cc * y ^ 2 + 2 * dd * (x * z)
      + 2 * ee * (y * z) + ff * z ^ 2 := by
  have hkey := ldl_clearing_identity aa bb cc dd ee ff x y z
  by_cases hzZero : z = 0
  · subst hzZero
    by_cases hyZero : y = 0
    · subst hyZero
      have hxNe : x ≠ 0 := fun hxZero => hcoordsNe ⟨hxZero, rfl, rfl⟩
      have hxSqPos : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hxNe))
      nlinarith [hkey, mul_pos haPos hminorPos,
        mul_pos hminorPos (mul_pos (mul_pos haPos haPos) hxSqPos)]
    · have hySqPos : 0 < y ^ 2 :=
        lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hyZero))
      nlinarith [hkey, mul_pos haPos hminorPos, sq_nonneg (aa * x + bb * y),
        mul_pos (mul_pos hminorPos hminorPos) hySqPos]
  · have hzSqPos : 0 < z ^ 2 :=
      lt_of_le_of_ne (sq_nonneg z) (Ne.symm (pow_ne_zero 2 hzZero))
    nlinarith [hkey, mul_pos haPos hminorPos, sq_nonneg (aa * x + bb * y + dd * z),
      sq_nonneg ((aa * cc - bb ^ 2) * y + (aa * ee - bb * dd) * z),
      mul_pos (mul_pos haPos hdetPos) hzSqPos]

/-- With a vanishing determinant the form degenerates to a nonnegative sum of
two squares — the PSD half of the LDL dichotomy. -/
theorem nonnegQuadForm_of_frameMinors_detZero {aa bb cc dd ee ff x y z : ℝ}
    (haPos : 0 < aa) (hminorPos : 0 < aa * cc - bb ^ 2)
    (hdetZero : aa * (cc * ff - ee ^ 2) - bb * (bb * ff - ee * dd)
        + dd * (bb * ee - cc * dd) = 0) :
    0 ≤ aa * x ^ 2 + 2 * bb * (x * y) + cc * y ^ 2 + 2 * dd * (x * z)
      + 2 * ee * (y * z) + ff * z ^ 2 := by
  have hkey := ldl_clearing_identity aa bb cc dd ee ff x y z
  rw [hdetZero] at hkey
  nlinarith [hkey, mul_pos haPos hminorPos, sq_nonneg (aa * x + bb * y + dd * z),
    sq_nonneg ((aa * cc - bb ^ 2) * y + (aa * ee - bb * dd) * z)]

/-! ## Part 2: frame kit (self-contained copy for this file) -/

/-- Transposed pairing, three-dimensional concrete form. -/
theorem dotProduct_transpose_mulVec_three (multiplier : Matrix (Fin 3) (Fin 3) ℝ)
    (leftVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ (multiplierᵀ *ᵥ rightVec) = (multiplier *ᵥ leftVec) ⬝ᵥ rightVec := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

/-- Pairing against a symmetric matrix is symmetric. -/
theorem symmPairing_comm {M : Matrix (Fin 3) (Fin 3) ℝ} (hsym : Mᵀ = M)
    (leftVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ (M *ᵥ rightVec) = rightVec ⬝ᵥ (M *ᵥ leftVec) := by
  conv_lhs => rw [← hsym]
  rw [dotProduct_transpose_mulVec_three, dotProduct_comm]

/-- The row matrix of an orthonormal frame is orthogonal. -/
theorem frameGram_eq_one {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0) :
    Matrix.of ![pOne, pTwo, axis] * (Matrix.of ![pOne, pTwo, axis])ᵀ = 1 := by
  have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  have hAxisOne : axis ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneAxis
  have hAxisTwo : axis ⬝ᵥ pTwo = 0 := by rw [dotProduct_comm]; exact hTwoAxis
  ext rowIndex colIndex
  have hentry : (Matrix.of ![pOne, pTwo, axis] * (Matrix.of ![pOne, pTwo, axis])ᵀ)
        rowIndex colIndex
      = (![pOne, pTwo, axis] rowIndex) ⬝ᵥ (![pOne, pTwo, axis] colIndex) := by
    rw [Matrix.mul_apply, dotProduct]
    exact Finset.sum_congr rfl fun summandIndex _ => by
      rw [Matrix.transpose_apply]
      rfl
  rw [hentry]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.one_apply, hOneOne, hTwoTwo, hAxisAxis, hOneTwo, hOneAxis, hTwoAxis,
      hTwoOne, hAxisOne, hAxisTwo]

/-- **Resolution of a vector in an orthonormal frame** (row-matrix inverse form). -/
theorem orthonormalFrame_resolution {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (vec : Fin 3 → ℝ) :
    vec = (vec ⬝ᵥ pOne) • pOne + (vec ⬝ᵥ pTwo) • pTwo + (vec ⬝ᵥ axis) • axis := by
  have hgram := frameGram_eq_one hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis
  have hcomm : (Matrix.of ![pOne, pTwo, axis])ᵀ * Matrix.of ![pOne, pTwo, axis] = 1 :=
    mul_eq_one_comm.mp hgram
  have happly : (Matrix.of ![pOne, pTwo, axis])ᵀ
      *ᵥ (Matrix.of ![pOne, pTwo, axis] *ᵥ vec) = vec := by
    rw [Matrix.mulVec_mulVec, hcomm, Matrix.one_mulVec]
  funext coord
  have hcoord := congrFun happly coord
  have hlhs : ((Matrix.of ![pOne, pTwo, axis])ᵀ
        *ᵥ (Matrix.of ![pOne, pTwo, axis] *ᵥ vec)) coord
      = (vec ⬝ᵥ pOne) * pOne coord + (vec ⬝ᵥ pTwo) * pTwo coord
        + (vec ⬝ᵥ axis) * axis coord := by
    simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hlhs] at hcoord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact hcoord.symm

/-- Congruence by the frame's row matrix preserves the determinant. -/
theorem det_frameCongruence {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (Matrix.of ![pOne, pTwo, axis] * M * (Matrix.of ![pOne, pTwo, axis])ᵀ).det = M.det := by
  have hgram := frameGram_eq_one hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis
  have hdetProduct : (Matrix.of ![pOne, pTwo, axis]).det
      * ((Matrix.of ![pOne, pTwo, axis])ᵀ).det = 1 := by
    rw [← Matrix.det_mul, hgram, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  linear_combination M.det * hdetProduct

/-- Each entry of the congruated matrix is a frame pairing. -/
theorem frameCongruence_entry (M : Matrix (Fin 3) (Fin 3) ℝ)
    (pOne pTwo axis : Fin 3 → ℝ) (rowIndex colIndex : Fin 3) :
    (Matrix.of ![pOne, pTwo, axis] * M * (Matrix.of ![pOne, pTwo, axis])ᵀ)
        rowIndex colIndex
      = (![pOne, pTwo, axis] rowIndex) ⬝ᵥ (M *ᵥ (![pOne, pTwo, axis] colIndex)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- The gap determinant read through the frame pairings. -/
theorem det_eq_framePairing_det {M : Matrix (Fin 3) (Fin 3) ℝ} (hsym : Mᵀ = M)
    {pOne pTwo axis : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0) :
    M.det
      = (pOne ⬝ᵥ (M *ᵥ pOne)) * ((pTwo ⬝ᵥ (M *ᵥ pTwo)) * (axis ⬝ᵥ (M *ᵥ axis))
            - (pTwo ⬝ᵥ (M *ᵥ axis)) ^ 2)
        - (pOne ⬝ᵥ (M *ᵥ pTwo)) * ((pOne ⬝ᵥ (M *ᵥ pTwo)) * (axis ⬝ᵥ (M *ᵥ axis))
            - (pTwo ⬝ᵥ (M *ᵥ axis)) * (pOne ⬝ᵥ (M *ᵥ axis)))
        + (pOne ⬝ᵥ (M *ᵥ axis)) * ((pOne ⬝ᵥ (M *ᵥ pTwo)) * (pTwo ⬝ᵥ (M *ᵥ axis))
            - (pTwo ⬝ᵥ (M *ᵥ pTwo)) * (pOne ⬝ᵥ (M *ᵥ axis))) := by
  have hcongruence := det_frameCongruence hOneOne hTwoTwo hAxisAxis hOneTwo hOneAxis
    hTwoAxis M
  rw [← hcongruence, Matrix.det_fin_three]
  simp only [frameCongruence_entry, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [symmPairing_comm hsym pTwo pOne, symmPairing_comm hsym axis pOne,
    symmPairing_comm hsym axis pTwo]
  ring

/-- The quadratic form of a symmetric matrix in frame coordinates. -/
theorem quadForm_frameCoordinates {M : Matrix (Fin 3) (Fin 3) ℝ} (hsym : Mᵀ = M)
    (pOne pTwo axis : Fin 3 → ℝ) (x y z : ℝ) :
    (x • pOne + y • pTwo + z • axis) ⬝ᵥ (M *ᵥ (x • pOne + y • pTwo + z • axis))
      = (pOne ⬝ᵥ (M *ᵥ pOne)) * x ^ 2 + 2 * (pOne ⬝ᵥ (M *ᵥ pTwo)) * (x * y)
        + (pTwo ⬝ᵥ (M *ᵥ pTwo)) * y ^ 2 + 2 * (pOne ⬝ᵥ (M *ᵥ axis)) * (x * z)
        + 2 * (pTwo ⬝ᵥ (M *ᵥ axis)) * (y * z) + (axis ⬝ᵥ (M *ᵥ axis)) * z ^ 2 := by
  have hTenEntry : M 1 0 = M 0 1 := by
    conv_lhs => rw [show M 1 0 = Mᵀ 0 1 from rfl, hsym]
  have hTwentyEntry : M 2 0 = M 0 2 := by
    conv_lhs => rw [show M 2 0 = Mᵀ 0 2 from rfl, hsym]
  have hTwentyOneEntry : M 2 1 = M 1 2 := by
    conv_lhs => rw [show M 2 1 = Mᵀ 1 2 from rfl, hsym]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [hTenEntry, hTwentyEntry, hTwentyOneEntry]
  ring

/-! ## Part 3: the pair-det gate -/

/-- The gap matrix of any subset is symmetric (transpose form). -/
theorem transpose_gap_eq_gap (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
      = subsetSum design selected - 1 := by
  have hsymmetric : (subsetSum design selected)ᵀ = subsetSum design selected := by
    rw [subsetSum, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    ext rowIndex colIndex
    simp [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
  rw [Matrix.transpose_sub, Matrix.transpose_one, hsymmetric]

/-- **THE PAIR-DET GATE.**  At a tie, every triple through a plane-strict pair
has nonpositive gap determinant: the pair keeps the gap positive definite on a
plane, so a positive determinant would force positive definiteness by the LDL
sum of squares, which the tie forbids.  Nothing is assumed about the third
atom. -/
theorem det_gap_nonpos_of_isTie_of_pairPlaneStrict
    (design : WeightedDesign size 3) (htie : IsTie design)
    {axis pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel thirdLabel : Fin size}
    (hneStrongOther : strongLabel ≠ otherLabel)
    (hneStrongThird : strongLabel ≠ thirdLabel) (hneOtherThird : otherLabel ≠ thirdLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2) :
    (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0 := by
  classical
  set tripleSet : Finset (Fin size) := {strongLabel, otherLabel, thirdLabel}
    with htripleDef
  have hcard : tripleSet.card = 3 := by
    rw [htripleDef, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hneStrongOther, hneStrongThird⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact hneOtherThird),
      Finset.card_singleton]
  set gapMatrix := subsetSum design tripleSet - (1 : Matrix (Fin 3) (Fin 3) ℝ)
    with hgapDef
  have hsym : gapMatrixᵀ = gapMatrix := transpose_gap_eq_gap design tripleSet
  -- the gap form is positive on the axis plane
  have hplaneFormPos : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (gapMatrix *ᵥ planar) := by
    intro planar hperp hplanarNe
    rw [hgapDef, dominationGap_form]
    have hpairValue := hpairStrict planar hperp hplanarNe
    have hsumSplit : ∑ atomIndex ∈ tripleSet, (design.atom atomIndex ⬝ᵥ planar) ^ 2
        = (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2
          + (design.atom thirdLabel ⬝ᵥ planar) ^ 2 := by
      rw [htripleDef, Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨hneStrongOther, hneStrongThird⟩),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          exact hneOtherThird),
        Finset.sum_singleton]
      ring
    rw [hsumSplit]
    nlinarith [hpairValue, sq_nonneg (design.atom thirdLabel ⬝ᵥ planar)]
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hOneOne
    exact zero_ne_one hOneOne
  have haPos : 0 < pOne ⬝ᵥ (gapMatrix *ᵥ pOne) := hplaneFormPos pOne hOneAxis hOneNe
  -- the plane minor is positive: evaluate the plane form at the Schur direction
  set aa := pOne ⬝ᵥ (gapMatrix *ᵥ pOne) with haaDef
  set bb := pOne ⬝ᵥ (gapMatrix *ᵥ pTwo) with hbbDef
  set cc := pTwo ⬝ᵥ (gapMatrix *ᵥ pTwo) with hccDef
  set dd := pOne ⬝ᵥ (gapMatrix *ᵥ axis) with hddDef
  set ee := pTwo ⬝ᵥ (gapMatrix *ᵥ axis) with heeDef
  set ff := axis ⬝ᵥ (gapMatrix *ᵥ axis) with hffDef
  have hminorPos : 0 < aa * cc - bb ^ 2 := by
    set schurVec : Fin 3 → ℝ := (-bb) • pOne + aa • pTwo + (0 : ℝ) • axis
      with hschurDef
    have hschurPerp : schurVec ⬝ᵥ axis = 0 := by
      rw [hschurDef, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
        smul_dotProduct, hOneAxis, hTwoAxis, hAxisAxis, smul_eq_mul, smul_eq_mul,
        smul_eq_mul]
      ring
    have hschurNe : schurVec ≠ 0 := by
      intro hzero
      have hpairing : schurVec ⬝ᵥ pTwo = aa := by
        rw [hschurDef, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          smul_dotProduct, hOneTwo, hTwoTwo, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        have hAxisTwoComm : axis ⬝ᵥ pTwo = 0 := by rw [dotProduct_comm]; exact hTwoAxis
        rw [hAxisTwoComm]
        ring
      rw [hzero, zero_dotProduct] at hpairing
      exact haPos.ne (by rw [← hpairing])
    have hschurValue := hplaneFormPos schurVec hschurPerp hschurNe
    rw [hschurDef, quadForm_frameCoordinates hsym, ← haaDef, ← hbbDef, ← hccDef,
      ← hddDef, ← heeDef, ← hffDef] at hschurValue
    nlinarith [hschurValue, haPos]
  -- if the determinant were positive the triple would dominate strictly
  by_contra hdetPositive
  push Not at hdetPositive
  have hdetFrame : 0 < aa * (cc * ff - ee ^ 2) - bb * (bb * ff - ee * dd)
      + dd * (bb * ee - cc * dd) := by
    have hdetValue := det_eq_framePairing_det hsym hOneOne hTwoTwo hAxisAxis hOneTwo
      hOneAxis hTwoAxis (M := gapMatrix)
    rw [← haaDef, ← hbbDef, ← hccDef, ← hddDef, ← heeDef, ← hffDef] at hdetValue
    nlinarith [hdetPositive, hdetValue]
  have hposDef : gapMatrix.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_subsetSum_sub_one design tripleSet, fun probe hprobeNe => ?_⟩
    rw [star_trivial]
    have hdecomp := orthonormalFrame_resolution hOneOne hTwoTwo hAxisAxis hOneTwo
      hOneAxis hTwoAxis probe
    have hcoordsNe : ¬ (probe ⬝ᵥ pOne = 0 ∧ probe ⬝ᵥ pTwo = 0 ∧ probe ⬝ᵥ axis = 0) := by
      rintro ⟨hxZero, hyZero, hzZero⟩
      rw [hxZero, hyZero, hzZero, zero_smul, zero_smul, zero_smul, add_zero,
        add_zero] at hdecomp
      exact hprobeNe hdecomp
    calc (0 : ℝ)
        < aa * (probe ⬝ᵥ pOne) ^ 2 + 2 * bb * ((probe ⬝ᵥ pOne) * (probe ⬝ᵥ pTwo))
            + cc * (probe ⬝ᵥ pTwo) ^ 2 + 2 * dd * ((probe ⬝ᵥ pOne) * (probe ⬝ᵥ axis))
            + 2 * ee * ((probe ⬝ᵥ pTwo) * (probe ⬝ᵥ axis))
            + ff * (probe ⬝ᵥ axis) ^ 2 :=
          posQuadForm_of_frameMinors haPos hminorPos hdetFrame hcoordsNe
      _ = probe ⬝ᵥ (gapMatrix *ᵥ probe) := by
          conv_rhs => rw [hdecomp]
          rw [quadForm_frameCoordinates hsym, ← haaDef, ← hbbDef, ← hccDef, ← hddDef,
            ← heeDef, ← hffDef]
  exact htie.2 tripleSet hcard hposDef

/-! ## Part 4: the pair budget and its equality locus -/

/-- **THE PAIR BUDGET.**  At a `(6,3)` tie, the weighted sum of the gap
determinants over the four completions of a plane-strict pair is nonpositive.
An exact aggregate of the gate; strict weight positivity makes its equality
case collapse onto the individual completions. -/
theorem pairBudget_nonpos_of_isTie (design : WeightedDesign 6 3) (htie : IsTie design)
    {axis pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel : Fin 6} (hneStrongOther : strongLabel ≠ otherLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2) :
    ∑ thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ,
        design.weight thirdLabel
          * (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0 := by
  classical
  refine Finset.sum_nonpos fun thirdLabel hmem => ?_
  have hmemNe : thirdLabel ≠ strongLabel ∧ thirdLabel ≠ otherLabel := by
    have hnot := Finset.mem_compl.mp hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
    push Not at hnot
    exact hnot
  refine mul_nonpos_iff.mpr (Or.inl ⟨(design.weight_pos thirdLabel).le, ?_⟩)
  exact det_gap_nonpos_of_isTie_of_pairPlaneStrict design htie hOneOne hTwoTwo hAxisAxis
    hOneTwo hOneAxis hTwoAxis hneStrongOther (Ne.symm hmemNe.1) (Ne.symm hmemNe.2)
    hpairStrict

/-- **THE EQUALITY LOCUS UPGRADES TO WEAK DOMINATION.**  A completion of a
plane-strict pair whose gap determinant vanishes is weakly dominating: the LDL
decomposition degenerates to two squares, so the gap is PSD outright.  No tie
hypothesis — this is unconditional geometry of the pair. -/
theorem dominates_completion_of_pairPlaneStrict_of_det_eq_zero
    (design : WeightedDesign size 3)
    {axis pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel thirdLabel : Fin size}
    (hneStrongOther : strongLabel ≠ otherLabel)
    (hneStrongThird : strongLabel ≠ thirdLabel) (hneOtherThird : otherLabel ≠ thirdLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
    (hdetZero : (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det = 0) :
    Dominates design {strongLabel, otherLabel, thirdLabel} := by
  classical
  set tripleSet : Finset (Fin size) := {strongLabel, otherLabel, thirdLabel}
    with htripleDef
  set gapMatrix := subsetSum design tripleSet - (1 : Matrix (Fin 3) (Fin 3) ℝ)
    with hgapDef
  have hsym : gapMatrixᵀ = gapMatrix := transpose_gap_eq_gap design tripleSet
  have hplaneFormPos : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      0 < planar ⬝ᵥ (gapMatrix *ᵥ planar) := by
    intro planar hperp hplanarNe
    rw [hgapDef, dominationGap_form]
    have hpairValue := hpairStrict planar hperp hplanarNe
    have hsumSplit : ∑ atomIndex ∈ tripleSet, (design.atom atomIndex ⬝ᵥ planar) ^ 2
        = (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2
          + (design.atom thirdLabel ⬝ᵥ planar) ^ 2 := by
      rw [htripleDef, Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨hneStrongOther, hneStrongThird⟩),
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          exact hneOtherThird),
        Finset.sum_singleton]
      ring
    rw [hsumSplit]
    nlinarith [hpairValue, sq_nonneg (design.atom thirdLabel ⬝ᵥ planar)]
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hOneOne
    exact zero_ne_one hOneOne
  have haPos : 0 < pOne ⬝ᵥ (gapMatrix *ᵥ pOne) := hplaneFormPos pOne hOneAxis hOneNe
  set aa := pOne ⬝ᵥ (gapMatrix *ᵥ pOne) with haaDef
  set bb := pOne ⬝ᵥ (gapMatrix *ᵥ pTwo) with hbbDef
  set cc := pTwo ⬝ᵥ (gapMatrix *ᵥ pTwo) with hccDef
  set dd := pOne ⬝ᵥ (gapMatrix *ᵥ axis) with hddDef
  set ee := pTwo ⬝ᵥ (gapMatrix *ᵥ axis) with heeDef
  set ff := axis ⬝ᵥ (gapMatrix *ᵥ axis) with hffDef
  have hminorPos : 0 < aa * cc - bb ^ 2 := by
    set schurVec : Fin 3 → ℝ := (-bb) • pOne + aa • pTwo + (0 : ℝ) • axis
      with hschurDef
    have hschurPerp : schurVec ⬝ᵥ axis = 0 := by
      rw [hschurDef, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
        smul_dotProduct, hOneAxis, hTwoAxis, hAxisAxis, smul_eq_mul, smul_eq_mul,
        smul_eq_mul]
      ring
    have hschurNe : schurVec ≠ 0 := by
      intro hzero
      have hpairing : schurVec ⬝ᵥ pTwo = aa := by
        rw [hschurDef, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          smul_dotProduct, hOneTwo, hTwoTwo, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        have hAxisTwoComm : axis ⬝ᵥ pTwo = 0 := by rw [dotProduct_comm]; exact hTwoAxis
        rw [hAxisTwoComm]
        ring
      rw [hzero, zero_dotProduct] at hpairing
      exact haPos.ne (by rw [← hpairing])
    have hschurValue := hplaneFormPos schurVec hschurPerp hschurNe
    rw [hschurDef, quadForm_frameCoordinates hsym, ← haaDef, ← hbbDef, ← hccDef,
      ← hddDef, ← heeDef, ← hffDef] at hschurValue
    nlinarith [hschurValue, haPos]
  have hdetFrameZero : aa * (cc * ff - ee ^ 2) - bb * (bb * ff - ee * dd)
      + dd * (bb * ee - cc * dd) = 0 := by
    have hdetValue := det_eq_framePairing_det hsym hOneOne hTwoTwo hAxisAxis hOneTwo
      hOneAxis hTwoAxis (M := gapMatrix)
    rw [← haaDef, ← hbbDef, ← hccDef, ← hddDef, ← heeDef, ← hffDef] at hdetValue
    rw [← hdetValue, hgapDef, htripleDef]
    exact hdetZero
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_subsetSum_sub_one design tripleSet, fun probe => ?_⟩
  rw [star_trivial]
  have hdecomp := orthonormalFrame_resolution hOneOne hTwoTwo hAxisAxis hOneTwo
    hOneAxis hTwoAxis probe
  calc (0 : ℝ)
      ≤ aa * (probe ⬝ᵥ pOne) ^ 2 + 2 * bb * ((probe ⬝ᵥ pOne) * (probe ⬝ᵥ pTwo))
          + cc * (probe ⬝ᵥ pTwo) ^ 2 + 2 * dd * ((probe ⬝ᵥ pOne) * (probe ⬝ᵥ axis))
          + 2 * ee * ((probe ⬝ᵥ pTwo) * (probe ⬝ᵥ axis))
          + ff * (probe ⬝ᵥ axis) ^ 2 :=
        nonnegQuadForm_of_frameMinors_detZero haPos hminorPos hdetFrameZero
    _ = probe ⬝ᵥ (gapMatrix *ᵥ probe) := by
        conv_rhs => rw [hdecomp]
        rw [quadForm_frameCoordinates hsym, ← haaDef, ← hbbDef, ← hccDef, ← hddDef,
          ← heeDef, ← hffDef]

/-- **BUDGET EQUALITY MAKES EVERY COMPLETION TIGHT.**  If the pair budget of a
`(6,3)` tie vanishes, all four completions of the pair are weakly dominating
with singular gap.  Strict weight positivity is the whole mechanism: a zero sum
of nonpositive terms with positive weights kills every term. -/
theorem forall_completion_dominates_of_pairBudget_eq_zero
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {axis pOne pTwo : Fin 3 → ℝ}
    (hOneOne : pOne ⬝ᵥ pOne = 1) (hTwoTwo : pTwo ⬝ᵥ pTwo = 1)
    (hAxisAxis : axis ⬝ᵥ axis = 1) (hOneTwo : pOne ⬝ᵥ pTwo = 0)
    (hOneAxis : pOne ⬝ᵥ axis = 0) (hTwoAxis : pTwo ⬝ᵥ axis = 0)
    {strongLabel otherLabel : Fin 6} (hneStrongOther : strongLabel ≠ otherLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
    (hbudgetZero : ∑ thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ,
        design.weight thirdLabel
          * (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det = 0) :
    ∀ thirdLabel : Fin 6, thirdLabel ≠ strongLabel → thirdLabel ≠ otherLabel →
      (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det = 0
        ∧ Dominates design {strongLabel, otherLabel, thirdLabel} := by
  classical
  have hterms : ∀ thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ,
      design.weight thirdLabel
        * (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0 := by
    intro thirdLabel hmem
    have hmemNe : thirdLabel ≠ strongLabel ∧ thirdLabel ≠ otherLabel := by
      have hnot := Finset.mem_compl.mp hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
      push Not at hnot
      exact hnot
    refine mul_nonpos_iff.mpr (Or.inl ⟨(design.weight_pos thirdLabel).le, ?_⟩)
    exact det_gap_nonpos_of_isTie_of_pairPlaneStrict design htie hOneOne hTwoTwo hAxisAxis
      hOneTwo hOneAxis hTwoAxis hneStrongOther (Ne.symm hmemNe.1) (Ne.symm hmemNe.2)
      hpairStrict
  have heachZero := (Finset.sum_eq_zero_iff_of_nonpos hterms).mp hbudgetZero
  intro thirdLabel hneThirdStrong hneThirdOther
  have hmem : thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ := by
    rw [Finset.mem_compl]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hneThirdStrong, hneThirdOther⟩
  have hproductZero := heachZero thirdLabel hmem
  have hdetZero : (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det = 0 :=
    (mul_eq_zero.mp hproductZero).resolve_left (design.weight_pos thirdLabel).ne'
  exact ⟨hdetZero, dominates_completion_of_pairPlaneStrict_of_det_eq_zero design hOneOne
    hTwoTwo hAxisAxis hOneTwo hOneAxis hTwoAxis hneStrongOther (Ne.symm hneThirdStrong)
    (Ne.symm hneThirdOther) hpairStrict hdetZero⟩


/-! ## Capstone: the hinge pair's budget at every `(6,3)` tie -/

/-- **THE PAIR BUDGET FIRES AT EVERY `(6,3)` TIE ALONG EVERY TRANSVERSAL
AXIS.**  The landed rank-two hinge supplies a plane-strict pair among any four
atoms pairwise transversal to the axis; the pair-det gate then caps every one
of its four completions, the weighted budget over the completions is
nonpositive, and budget equality forces ALL FOUR completions to be weakly
dominating with singular gap — the equality locus in which any closure of
branch (i) must find its stress.  Exact calibration: at the `(5,3)` diamond
the budget takes only the values `-2` and `0` over the ten pairs, with
equality exactly at the four pairs whose completions are all tight; at `K4`
it is strictly negative at all fifteen pairs. -/
theorem sixThree_tie_pairBudget_of_transversalAxis (design : WeightedDesign 6 3)
    (htie : IsTie design) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    {labelOne labelTwo labelThree labelFour : Fin 6}
    (hneOneTwo : labelOne ≠ labelTwo) (hneOneThree : labelOne ≠ labelThree)
    (hneOneFour : labelOne ≠ labelFour) (hneTwoThree : labelTwo ≠ labelThree)
    (hneTwoFour : labelTwo ≠ labelFour) (hneThreeFour : labelThree ≠ labelFour)
    (htransversalOneTwo :
      crossProduct (design.atom labelOne) (design.atom labelTwo) ⬝ᵥ axis ≠ 0)
    (htransversalOneThree :
      crossProduct (design.atom labelOne) (design.atom labelThree) ⬝ᵥ axis ≠ 0)
    (htransversalOneFour :
      crossProduct (design.atom labelOne) (design.atom labelFour) ⬝ᵥ axis ≠ 0)
    (htransversalTwoThree :
      crossProduct (design.atom labelTwo) (design.atom labelThree) ⬝ᵥ axis ≠ 0)
    (htransversalTwoFour :
      crossProduct (design.atom labelTwo) (design.atom labelFour) ⬝ᵥ axis ≠ 0)
    (htransversalThreeFour :
      crossProduct (design.atom labelThree) (design.atom labelFour) ⬝ᵥ axis ≠ 0) :
    ∃ strongLabel otherLabel : Fin 6, strongLabel ≠ otherLabel
      ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
          planar ⬝ᵥ planar
            < (design.atom strongLabel ⬝ᵥ planar) ^ 2
              + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
      ∧ (∑ thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ,
            design.weight thirdLabel
              * (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det ≤ 0)
      ∧ ((∑ thirdLabel ∈ ({strongLabel, otherLabel} : Finset (Fin 6))ᶜ,
            design.weight thirdLabel
              * (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det = 0) →
          ∀ thirdLabel : Fin 6, thirdLabel ≠ strongLabel → thirdLabel ≠ otherLabel →
            (subsetSum design {strongLabel, otherLabel, thirdLabel} - 1).det = 0
              ∧ Dominates design {strongLabel, otherLabel, thirdLabel}) := by
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  obtain ⟨strongLabel, otherLabel, hlabelNe, hpairStrict⟩ :=
    exists_planeStrictPair_of_fourTransversal design hunit hOneOne hTwoTwo hOneTwo
      hOneAxis hTwoAxis hneOneTwo hneOneThree hneOneFour hneTwoThree hneTwoFour
      hneThreeFour htransversalOneTwo htransversalOneThree htransversalOneFour
      htransversalTwoThree htransversalTwoFour htransversalThreeFour
  exact ⟨strongLabel, otherLabel, hlabelNe, hpairStrict,
    pairBudget_nonpos_of_isTie design htie hOneOne hTwoTwo hunit hOneTwo hOneAxis
      hTwoAxis hlabelNe hpairStrict,
    fun hbudgetZero => forall_completion_dominates_of_pairBudget_eq_zero design htie
      hOneOne hTwoTwo hunit hOneTwo hOneAxis hTwoAxis hlabelNe hpairStrict hbudgetZero⟩

end Gtz

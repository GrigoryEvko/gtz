/-
# The genericity reduction at the open `(6,3)` cell

Module 4 of the genericity-reduction run: the capstone.  A counterexample to
`Gtz.GtzWeighted 6 3`, if one exists, can be chosen GENERIC — all-heavy, with
every polynomial degeneracy avoided for which a single witness design lies off
the degeneracy locus.  The consumable interface is the CONTRAPOSITIVE family:
to prove `Gtz.GtzWeighted 6 3` it suffices to dominate the generic all-heavy
designs.

Layers, in order:

* **Packing** (`designParamsOf`): a design's frame-side data — the scaled-atom
  Stiefel frame `Gtz.scaledAtomRows` and the weight vector — as a coordinate
  function on `Gtz.FrameParamIndex`, the variable index of degeneracy
  polynomials.  `designOfFrameWeights` inverts the packing: an orthonormal
  frame plus positive unit-sum weights yields a design whose atoms are the
  frame rows rescaled by inverse root weights.
* **The degeneracy polynomials**: `rowPairingPoly` (packed row pairing),
  `clearedExcessPoly` (weight-cleared heavy excess), `clearedGapPoly` /
  `clearedTripleProductPoly` (weight-cleared `Gtz.excessGap` and pairing
  triple product), `clearedDominationGapPoly` (weight-cleared domination-gap
  quadratic form at a fixed probe), and the product bundle
  `genericBundlePoly` whose nonvanishing at a design is EXACTLY the generic
  bundle `IsGenericDesign` (`eval_genericBundlePoly_ne_zero_iff`): all atom
  pairings nonzero, no parallel pair, strict edges, strict bands — and, by
  the split identity `Gtz.discriminantTie_eq_excessGap_add_tripleProduct`, no
  tight triple (`discriminantTie_ne_zero_of_excessGap_sq_ne`; the tie needs
  no polynomial factor of its own).
* **THE CAPSTONE** (`exists_allHeavy_failing_avoiding_of_not_gtzWeighted`).
  If `Gtz.GtzWeighted 6 3` fails, then for EVERY degeneracy polynomial with a
  witness design off its locus there is an all-heavy design with no
  dominating triple avoiding that locus.  Route: extract an all-heavy failing
  design (`exists_allHeavy_failing_of_not_gtzWeighted_six_three`, via the
  shipped collapse `Gtz.gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three`);
  choose one strictly negative probe per triple
  (`exists_negative_gap_probe_of_not_dominates`); lift the design's frame
  into a positive sign chart (`Gtz.exists_signChartFrame_eq`); the failing
  conditions become an OPEN set of packed frame parameters (strict polynomial
  inequalities in the packed coordinates, no square roots anywhere), pulled
  back to an open chart set through `Gtz.continuousOn_signChartParams`; if
  the degeneracy vanished on all of it, the star propagation theorem
  `Gtz.eval_frameParamsOf_eq_zero_of_eval_eq_zero_on_open` would force it to
  vanish at the witness design's parameters — contradiction.  So some chart
  point avoids the locus, and `designOfFrameWeights` turns it into the
  desired design.
* **The witness** (`genericWitnessDesign`): a fresh exact rational `(6,3)`
  design (atoms over denominator `17`, weights `1/9 ×5, 4/9` — perfect
  squares, so the packed frame is rational) passing the FULL generic bundle
  (`genericWitnessDesign_isGenericDesign`), all-heavy
  (`genericWitnessDesign_allHeavy`), with a dominating triple
  (`genericWitnessDesign_dominates`, the subset `{0, 1, 2}`, proved by the
  seven-principal-minor criterion `Gtz.posSemidef_three_of_principalMinors`).
  These three certificates are the inhabitation record for the consumable
  hypothesis bundles: the closing hypotheses below are exercised by at least
  one kernel-checked design and are not vacuously quantified.
* **CONSUMABLES**: `gtzWeighted_of_forall_avoiding_dominates` (the parametric
  template — ONE application per future degeneracy polynomial plus witness),
  `gtzWeighted_of_forall_generic_dominates` (the standard bundle instance),
  `gtzWeighted_of_forall_nonzero_pairings_dominates` (the ZP-DISSOLUTION
  corollary: the zero-pairing branch is not a separate obligation — a closing
  argument may assume every atom pairing nonzero), and
  `eval_designParamsOf_mul_ne_zero_iff` (adding a degeneracy to an existing
  bundle is one polynomial multiplication).
* **BONUS** (`liftingLemma_two_iff_gtzWeighted_six_three`): the rank-two
  lifting-lemma frontier is exactly the single open cell, by composing the
  shipped `Gtz.liftingLemma_two_iff_the_two_residuals` with the shipped
  collapse `Gtz.gtzWeighted_six_three_iff_seven_three`.

HONESTY, VACUITY.  The capstone and the instance
`exists_generic_allHeavy_failing_of_not_gtzWeighted` are conditional on
`¬ Gtz.GtzWeighted 6 3`: if the GTZ conjecture is true they are VACUOUS BY
NATURE, exactly as the dead-end record in the module
Gtz/Quantitative/ResidueReduction.lean documents its own reductions.  The
non-vacuous deliverables are the consumable contrapositives and the witness
certificates, whose hypothesis bundles are inhabited (see the witness layer).

HONESTY, SCOPE.  The genericity reduction narrows QUANTIFIERS: a closing
argument for the open cell may assume strictness and genericity.  It
manufactures NO margins — the hypothetical failing set can hug the tie
boundary arbitrarily closely, no `margin ≥ c > 0` certificate becomes
available anywhere, and the archive verdict that every examined
stratification carries exact zero-margin ties in every stratum stands
untouched.

Backtick convention for this file's docstrings: multi-character backticked
tokens are declaration names (kernel-checked), except the quoted formula
fragments `margin ≥ c > 0`, `1/9 ×5, 4/9`, `17`, `{0, 1, 2}`, `(6,3)`,
`¬ Gtz.GtzWeighted 6 3` above and the tokens `V`, `t`, `u`, `Σu`, `w`,
`eg`, `P`, `S_C`, `√`, `Vᵀ·V = 1`, `rank` inside formulas below, which are
local mathematical notation or binder names, NOT constants; file names are
written without backticks.
-/
import Mathlib
import Gtz.Reduction.ChartPullback
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Reduction.CertificateBall
import Gtz.Reduction.RayleighCertificate
import Gtz.Quantitative.SevenThreeCollapse
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Reduction.StressWalk
import Gtz.Reduction.LiftingLemma

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Packing a design into frame parameters -/

/-- The packed frame-side parameters of a weighted design: the scaled-atom
Stiefel frame (rows `√t_c · g_c`, i.e. `Gtz.scaledAtomRows`) together with the
weight vector, as a coordinate function on `Gtz.FrameParamIndex`.  This is the
interface between the design vocabulary and the degeneracy-polynomial
vocabulary: a degeneracy polynomial is evaluated at a design through this
packing. -/
noncomputable def designParamsOf (D : WeightedDesign size rank) :
    FrameParamIndex size rank → ℝ :=
  frameParamsOf (scaledAtomRows D) D.weight

/-- Normalized weights sum to one wherever the raw sum is nonzero. -/
theorem sum_normalizedWeights {weights : Fin size → ℝ}
    (hsum : (∑ atomIndex, weights atomIndex) ≠ 0) :
    ∑ atomIndex, normalizedWeights weights atomIndex = 1 := by
  simp only [normalizedWeights]
  rw [← Finset.sum_div, div_self hsum]

/-- **Sign-chart frames are orthonormal**: the first `rank` columns of
`diag(signs) · cay(skew)` inherit column orthonormality from the orthogonal
square.  This is the Parseval side of building a design at a chart point. -/
theorem signChartFrame_transpose_mul_self (hrank : rank ≤ size)
    {signs : Fin size → ℝ} (hsigns : IsSignVector signs)
    (raw : Fin size → Fin size → ℝ) :
    (signChartFrame hrank signs raw)ᵀ * signChartFrame hrank signs raw = 1 := by
  have hskew : (skewOfRaw raw)ᵀ = -(skewOfRaw raw) := transpose_skewOfRaw raw
  have horth : (Matrix.diagonal signs * cayleyOf (skewOfRaw raw))ᵀ
      * (Matrix.diagonal signs * cayleyOf (skewOfRaw raw)) = 1 := by
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal signs) (Matrix.diagonal signs)
        (cayleyOf (skewOfRaw raw)),
      hsigns.diagonal_mul_self, Matrix.one_mul, cayleyOf_transpose_mul_self hskew]
  ext colFirst colSecond
  have hentry := congrFun (congrFun horth (Fin.castLE hrank colFirst))
    (Fin.castLE hrank colSecond)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    Fin.castLE_inj] at hentry
  simpa only [signChartFrame, frameOf, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id_eq, Matrix.one_apply] using hentry

/-- **Unpacking frame data into a design**: an orthonormal frame together with
positive weights summing to one yields a weighted design whose atoms are the
frame rows rescaled by the inverse root weights.  Parseval is exactly
`Vᵀ·V = 1` after the root weights cancel. -/
noncomputable def designOfFrameWeights (frame : Matrix (Fin size) (Fin rank) ℝ)
    (weights : Fin size → ℝ) (hframe : frameᵀ * frame = 1)
    (hpos : ∀ atomIndex, 0 < weights atomIndex)
    (hsum : ∑ atomIndex, weights atomIndex = 1) : WeightedDesign size rank where
  atom := fun atomIndex => (Real.sqrt (weights atomIndex))⁻¹ • frame atomIndex
  weight := weights
  weight_pos := hpos
  weight_sum_one := hsum
  isParseval := by
    have hcell : ∀ atomIndex : Fin size,
        weights atomIndex
            • atomMatrix ((Real.sqrt (weights atomIndex))⁻¹ • frame atomIndex)
          = atomMatrix (frame atomIndex) := by
      intro atomIndex
      rw [atomMatrix_smul, smul_smul, inv_pow, Real.sq_sqrt (hpos atomIndex).le,
        mul_inv_cancel₀ (hpos atomIndex).ne', one_smul]
    calc ∑ atomIndex, weights atomIndex
            • atomMatrix ((Real.sqrt (weights atomIndex))⁻¹ • frame atomIndex)
        = ∑ atomIndex, atomMatrix (frame atomIndex) :=
          Finset.sum_congr rfl fun atomIndex _ => hcell atomIndex
      _ = frameᵀ * frame := (transpose_mul_self_eq_sum_rows frame).symm
      _ = 1 := hframe

/-- The scaled-atom rows of the unpacked design recover the frame: the root
weight and its inverse cancel. -/
theorem scaledAtomRows_designOfFrameWeights (frame : Matrix (Fin size) (Fin rank) ℝ)
    (weights : Fin size → ℝ) (hframe : frameᵀ * frame = 1)
    (hpos : ∀ atomIndex, 0 < weights atomIndex)
    (hsum : ∑ atomIndex, weights atomIndex = 1) :
    scaledAtomRows (designOfFrameWeights frame weights hframe hpos hsum) = frame := by
  ext atomIndex coord
  show Real.sqrt (weights atomIndex)
      * ((Real.sqrt (weights atomIndex))⁻¹ • frame atomIndex) coord
    = frame atomIndex coord
  rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (hpos atomIndex)), one_mul]

/-- Packing after unpacking is the identity on frame data. -/
theorem designParamsOf_designOfFrameWeights (frame : Matrix (Fin size) (Fin rank) ℝ)
    (weights : Fin size → ℝ) (hframe : frameᵀ * frame = 1)
    (hpos : ∀ atomIndex, 0 < weights atomIndex)
    (hsum : ∑ atomIndex, weights atomIndex = 1) :
    designParamsOf (designOfFrameWeights frame weights hframe hpos hsum)
      = frameParamsOf frame weights := by
  rw [designParamsOf, scaledAtomRows_designOfFrameWeights]
  rfl

/-! ## The failing-design extraction -/

/-- A non-dominating subset admits a strictly negative probe for its
domination-gap quadratic form: not positive semidefinite means some direction
sees a negative value, the gap matrix being symmetric. -/
theorem exists_negative_gap_probe_of_not_dominates {D : WeightedDesign size rank}
    {C : Finset (Fin size)} (hnot : ¬ Dominates D C) :
    ∃ probe : Fin rank → ℝ, probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) < 0 := by
  by_contra hnone
  push Not at hnone
  refine hnot ?_
  show (subsetSum D C - 1).PosSemidef
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (subsetSum_sub_one_transpose D C), fun probe => ?_⟩
  rw [star_trivial]
  exact hnone probe

/-- **The all-heavy failing extraction**: if the open cell fails, an all-heavy
design with no dominating triple exists — one application of the shipped
collapse `Gtz.gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three`. -/
theorem exists_allHeavy_failing_of_not_gtzWeighted_six_three
    (hnot : ¬ GtzWeighted 6 3) :
    ∃ D : WeightedDesign 6 3, AllHeavy D
      ∧ ∀ C : Finset (Fin 6), C.card = 3 → ¬ Dominates D C := by
  have hnotHeavy : ¬ GtzWeightedHeavy 6 3 := fun hheavy =>
    hnot (gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three.mp hheavy)
  simp only [GtzWeightedHeavy] at hnotHeavy
  push Not at hnotHeavy
  obtain ⟨D, hheavy, hfail⟩ := hnotHeavy
  exact ⟨D, hheavy, fun C hcard hdom => (hfail C hcard) hdom⟩

/-! ## The degeneracy polynomials -/

/-- The packed row-pairing polynomial: at the packing of a design it evaluates
to `√t_a √t_b ⟨g_a, g_b⟩` (`eval_rowPairingPoly_designParamsOf`). -/
noncomputable def rowPairingPoly (rank : ℕ) {size : ℕ}
    (atomFirst atomSecond : Fin size) :
    MvPolynomial (FrameParamIndex size rank) ℝ :=
  ∑ coord : Fin rank, MvPolynomial.X (Sum.inl (atomFirst, coord))
    * MvPolynomial.X (Sum.inl (atomSecond, coord))

/-- The weight-cleared heavy excess: at a design it evaluates to
`t_c · (leverage − 1)`, whose positivity is exactly strict heaviness of the
atom. -/
noncomputable def clearedExcessPoly (rank : ℕ) {size : ℕ} (atomIndex : Fin size) :
    MvPolynomial (FrameParamIndex size rank) ℝ :=
  rowPairingPoly rank atomIndex atomIndex - MvPolynomial.X (Sum.inr atomIndex)

/-- The weight-cleared sign-blind gap: at a design it evaluates to
`t_a t_b t_c · Gtz.excessGap` (`eval_clearedGapPoly_designParamsOf`). -/
noncomputable def clearedGapPoly (rank : ℕ) {size : ℕ}
    (first second third : Fin size) :
    MvPolynomial (FrameParamIndex size rank) ℝ :=
  clearedExcessPoly rank first * clearedExcessPoly rank second
      * clearedExcessPoly rank third
    - (clearedExcessPoly rank third * rowPairingPoly rank first second ^ 2
      + clearedExcessPoly rank second * rowPairingPoly rank first third ^ 2
      + clearedExcessPoly rank first * rowPairingPoly rank second third ^ 2)

/-- The weight-cleared pairing triple product: at a design it evaluates to
`t_a t_b t_c · P_ab P_ac P_bc` — each root weight appears exactly twice, so no
square root survives. -/
noncomputable def clearedTripleProductPoly (rank : ℕ) {size : ℕ}
    (first second third : Fin size) :
    MvPolynomial (FrameParamIndex size rank) ℝ :=
  rowPairingPoly rank first second * rowPairingPoly rank first third
    * rowPairingPoly rank second third

/-- The weight-cleared domination-gap quadratic form of a subset at a FIXED
real probe vector: at a design it evaluates to
`(∏_{c∈C} t_c) · probeᵀ (S_C − 1) probe`
(`eval_clearedDominationGapPoly_designParamsOf`); its strict negativity is an
open condition certifying that the subset does not dominate. -/
noncomputable def clearedDominationGapPoly {size rank : ℕ} (C : Finset (Fin size))
    (probe : Fin rank → ℝ) : MvPolynomial (FrameParamIndex size rank) ℝ :=
  (∑ c ∈ C, (∑ coord, MvPolynomial.C (probe coord)
        * MvPolynomial.X (Sum.inl (c, coord))) ^ 2
      * ∏ other ∈ C.erase c, MvPolynomial.X (Sum.inr other))
    - MvPolynomial.C (probe ⬝ᵥ probe) * ∏ c ∈ C, MvPolynomial.X (Sum.inr c)

/-- The per-pair factor of the generic bundle: pairing nonzero, pair not
parallel, edge strict. -/
noncomputable def genericPairPoly {size : ℕ} (atomFirst atomSecond : Fin size) :
    MvPolynomial (FrameParamIndex size 3) ℝ :=
  rowPairingPoly 3 atomFirst atomSecond
    * (rowPairingPoly 3 atomFirst atomSecond ^ 2
      - rowPairingPoly 3 atomFirst atomFirst
          * rowPairingPoly 3 atomSecond atomSecond)
    * (rowPairingPoly 3 atomFirst atomFirst
        + rowPairingPoly 3 atomSecond atomSecond - 1)

/-- The per-triple factor of the generic bundle: the strict band, i.e. the
cleared `Gtz.excessGap` squared avoids four times the cleared triple product
squared.  The tie condition needs no factor of its own: a strict band forces a
nonzero `Gtz.discriminantTie` through the split identity
(`discriminantTie_ne_zero_of_excessGap_sq_ne`). -/
noncomputable def genericTriplePoly {size : ℕ} (first second third : Fin size) :
    MvPolynomial (FrameParamIndex size 3) ℝ :=
  clearedGapPoly 3 first second third ^ 2
    - (2 * clearedTripleProductPoly 3 first second third) ^ 2

/-- **The generic bundle polynomial**: the product of every per-pair factor
over ordered distinct pairs and every per-triple factor over ordered distinct
triples.  Its nonvanishing at a design's packed parameters is EXACTLY the
generic bundle `IsGenericDesign` (`eval_genericBundlePoly_ne_zero_iff`). -/
noncomputable def genericBundlePoly (size : ℕ) :
    MvPolynomial (FrameParamIndex size 3) ℝ :=
  (∏ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
      genericPairPoly pair.1 pair.2)
    * ∏ triple ∈ (Finset.univ : Finset (Fin size × Fin size × Fin size)).filter
        (fun triple => triple.1 ≠ triple.2.1 ∧ triple.1 ≠ triple.2.2
          ∧ triple.2.1 ≠ triple.2.2),
      genericTriplePoly triple.1 triple.2.1 triple.2.2

/-! ## Evaluation bridges -/

/-- The row-pairing polynomial evaluates at packed frame data to the row dot
product. -/
theorem eval_rowPairingPoly (frame : Matrix (Fin size) (Fin rank) ℝ)
    (weights : Fin size → ℝ) (atomFirst atomSecond : Fin size) :
    MvPolynomial.eval (frameParamsOf frame weights)
        (rowPairingPoly rank atomFirst atomSecond)
      = frame atomFirst ⬝ᵥ frame atomSecond := by
  rw [rowPairingPoly, map_sum, dotProduct]
  refine Finset.sum_congr rfl fun coord _ => ?_
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, frameParamsOf_inl,
    frameParamsOf_inl]

/-- At a design, the row pairing is the atom pairing scaled by the two root
weights. -/
theorem eval_rowPairingPoly_designParamsOf (D : WeightedDesign size rank)
    (atomFirst atomSecond : Fin size) :
    MvPolynomial.eval (designParamsOf D) (rowPairingPoly rank atomFirst atomSecond)
      = Real.sqrt (D.weight atomFirst) * Real.sqrt (D.weight atomSecond)
        * (D.atom atomFirst ⬝ᵥ D.atom atomSecond) := by
  rw [designParamsOf, eval_rowPairingPoly, scaledAtomRows_row, scaledAtomRows_row,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- At a design, the diagonal row pairing is the share `t_c · leverage`. -/
theorem eval_rowPairingPoly_self_designParamsOf (D : WeightedDesign size rank)
    (atomIndex : Fin size) :
    MvPolynomial.eval (designParamsOf D) (rowPairingPoly rank atomIndex atomIndex)
      = D.weight atomIndex * leverageOf (D.atom atomIndex) := by
  rw [eval_rowPairingPoly_designParamsOf,
    Real.mul_self_sqrt (D.weight_pos atomIndex).le, dotProduct_self_eq_sum_sq,
    leverageOf]

/-- At a design, the cleared excess is the weight times the heavy excess. -/
theorem eval_clearedExcessPoly_designParamsOf (D : WeightedDesign size rank)
    (atomIndex : Fin size) :
    MvPolynomial.eval (designParamsOf D) (clearedExcessPoly rank atomIndex)
      = D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) := by
  rw [clearedExcessPoly, map_sub, MvPolynomial.eval_X,
    eval_rowPairingPoly_self_designParamsOf,
    show designParamsOf D (Sum.inr atomIndex) = D.weight atomIndex from rfl]
  ring

/-- At a design, the cleared gap is the weight product times the sign-blind
gap `Gtz.excessGap`. -/
theorem eval_clearedGapPoly_designParamsOf {m : ℕ} (D : WeightedDesign m 3)
    (first second third : Fin m) :
    MvPolynomial.eval (designParamsOf D) (clearedGapPoly 3 first second third)
      = D.weight first * D.weight second * D.weight third
        * excessGap D first second third := by
  simp only [clearedGapPoly, map_sub, map_add, map_mul, map_pow,
    eval_clearedExcessPoly_designParamsOf, eval_rowPairingPoly_designParamsOf]
  simp only [excessGap, heavyExcess, atomPairing]
  simp only [mul_pow, Real.sq_sqrt (D.weight_pos first).le,
    Real.sq_sqrt (D.weight_pos second).le, Real.sq_sqrt (D.weight_pos third).le]
  ring

/-- At a design, the cleared triple product is the weight product times the
pairing triple product: the root weights pair up and vanish. -/
theorem eval_clearedTripleProductPoly_designParamsOf {m : ℕ}
    (D : WeightedDesign m 3) (first second third : Fin m) :
    MvPolynomial.eval (designParamsOf D)
        (clearedTripleProductPoly 3 first second third)
      = D.weight first * D.weight second * D.weight third
        * (atomPairing D first second * atomPairing D first third
          * atomPairing D second third) := by
  simp only [clearedTripleProductPoly, map_mul, eval_rowPairingPoly_designParamsOf,
    atomPairing]
  ring_nf
  simp only [Real.sq_sqrt (D.weight_pos first).le,
    Real.sq_sqrt (D.weight_pos second).le, Real.sq_sqrt (D.weight_pos third).le]
  ring

/-- At a design, the per-triple factor is the squared weight product times the
band expression `eg² − 4 P²`. -/
theorem eval_genericTriplePoly_designParamsOf {m : ℕ} (D : WeightedDesign m 3)
    (first second third : Fin m) :
    MvPolynomial.eval (designParamsOf D) (genericTriplePoly first second third)
      = (D.weight first * D.weight second * D.weight third) ^ 2
        * (excessGap D first second third ^ 2
          - 4 * (atomPairing D first second * atomPairing D first third
              * atomPairing D second third) ^ 2) := by
  simp only [genericTriplePoly, map_sub, map_pow, map_mul, map_ofNat,
    eval_clearedGapPoly_designParamsOf, eval_clearedTripleProductPoly_designParamsOf]
  ring

/-- At a design, the cleared domination-gap form is the weight product over
the subset times the true domination-gap quadratic form
`Gtz.dominationGap_form`. -/
theorem eval_clearedDominationGapPoly_designParamsOf (D : WeightedDesign size rank)
    (C : Finset (Fin size)) (probe : Fin rank → ℝ) :
    MvPolynomial.eval (designParamsOf D) (clearedDominationGapPoly C probe)
      = (∏ c ∈ C, D.weight c) * (probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe)) := by
  classical
  rw [dominationGap_form]
  have hweightProd : ∀ S : Finset (Fin size),
      MvPolynomial.eval (designParamsOf D) (∏ c ∈ S, MvPolynomial.X (Sum.inr c))
        = ∏ c ∈ S, D.weight c := by
    intro S
    rw [map_prod]
    exact Finset.prod_congr rfl fun c _ => by rw [MvPolynomial.eval_X]; rfl
  have hrowDot : ∀ c : Fin size,
      MvPolynomial.eval (designParamsOf D)
        (∑ coord, MvPolynomial.C (probe coord) * MvPolynomial.X (Sum.inl (c, coord)))
        = Real.sqrt (D.weight c) * (D.atom c ⬝ᵥ probe) := by
    intro c
    rw [map_sum, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun coord _ => ?_
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    show probe coord * scaledAtomRows D c coord = _
    rw [scaledAtomRows]
    show probe coord * (Real.sqrt (D.weight c) * D.atom c coord)
      = Real.sqrt (D.weight c) * (D.atom c coord * probe coord)
    ring
  have hterm : ∀ c ∈ C, MvPolynomial.eval (designParamsOf D)
      ((∑ coord, MvPolynomial.C (probe coord)
          * MvPolynomial.X (Sum.inl (c, coord))) ^ 2
        * ∏ other ∈ C.erase c, MvPolynomial.X (Sum.inr other))
      = (∏ c ∈ C, D.weight c) * (D.atom c ⬝ᵥ probe) ^ 2 := by
    intro c hc
    rw [map_mul, map_pow, hrowDot, hweightProd, mul_pow,
      Real.sq_sqrt (D.weight_pos c).le,
      show D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 * ∏ other ∈ C.erase c, D.weight other
          = D.weight c * (∏ other ∈ C.erase c, D.weight other)
            * (D.atom c ⬝ᵥ probe) ^ 2 from by ring,
      Finset.mul_prod_erase C _ hc]
  rw [clearedDominationGapPoly, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    hweightProd, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-! ## The generic bundle in design vocabulary -/

/-- **The generic bundle**, in shipped design vocabulary: every atom pairing
nonzero, no parallel pair (strict Cauchy–Schwarz gap on every pair), strict
edges (no share pair summing to one), strict bands (the sign-blind gap squared
avoids four times the pairing triple product squared), and no tight triple
(nonzero `Gtz.discriminantTie`).  The tie conjunct is DERIVABLE from the band
conjunct (`discriminantTie_ne_zero_of_excessGap_sq_ne`) and is kept for
consumer convenience. -/
def IsGenericDesign {m : ℕ} (D : WeightedDesign m 3) : Prop :=
  (∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0)
  ∧ (∀ first second : Fin m, first ≠ second →
      atomPairing D first second ^ 2
        ≠ leverageOf (D.atom first) * leverageOf (D.atom second))
  ∧ (∀ first second : Fin m, first ≠ second →
      D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second) ≠ 1)
  ∧ (∀ first second third : Fin m,
      first ≠ second → first ≠ third → second ≠ third →
      excessGap D first second third ^ 2
        ≠ 4 * (atomPairing D first second * atomPairing D first third
            * atomPairing D second third) ^ 2)
  ∧ (∀ first second third : Fin m,
      first ≠ second → first ≠ third → second ≠ third →
      discriminantTie D first second third ≠ 0)

/-- A strict band forces a nonzero tie: through the split identity
`Gtz.discriminantTie_eq_excessGap_add_tripleProduct`, a vanishing tie would
mean the gap equals minus twice the triple product, hence squares agree. -/
theorem discriminantTie_ne_zero_of_excessGap_sq_ne {m : ℕ} (D : WeightedDesign m 3)
    {first second third : Fin m}
    (hband : excessGap D first second third ^ 2
      ≠ 4 * (atomPairing D first second * atomPairing D first third
          * atomPairing D second third) ^ 2) :
    discriminantTie D first second third ≠ 0 := by
  rw [discriminantTie_eq_excessGap_add_tripleProduct]
  intro hzero
  apply hband
  have hgap : excessGap D first second third
      = -(2 * (atomPairing D first second * atomPairing D first third
          * atomPairing D second third)) := by linarith
  rw [hgap]
  ring

/-- A positive scale factor preserves nonvanishing. -/
theorem pos_mul_ne_zero_iff {scale value : ℝ} (hscale : 0 < scale) :
    scale * value ≠ 0 ↔ value ≠ 0 := by
  rw [mul_ne_zero_iff]
  exact and_iff_right hscale.ne'

/-- The per-pair factor is nonzero at a design exactly when the pair passes
its three generic conditions. -/
theorem eval_genericPairPoly_ne_zero_iff {m : ℕ} (D : WeightedDesign m 3)
    (first second : Fin m) :
    MvPolynomial.eval (designParamsOf D) (genericPairPoly first second) ≠ 0
      ↔ (atomPairing D first second ≠ 0
        ∧ atomPairing D first second ^ 2
            ≠ leverageOf (D.atom first) * leverageOf (D.atom second)
        ∧ D.weight first * leverageOf (D.atom first)
            + D.weight second * leverageOf (D.atom second) ≠ 1) := by
  have hposF := D.weight_pos first
  have hposS := D.weight_pos second
  have hparallelEval : MvPolynomial.eval (designParamsOf D)
      (rowPairingPoly 3 first second ^ 2
        - rowPairingPoly 3 first first * rowPairingPoly 3 second second)
      = D.weight first * D.weight second
        * ((D.atom first ⬝ᵥ D.atom second) ^ 2
          - leverageOf (D.atom first) * leverageOf (D.atom second)) := by
    rw [map_sub, map_pow, map_mul, eval_rowPairingPoly_designParamsOf,
      eval_rowPairingPoly_self_designParamsOf, eval_rowPairingPoly_self_designParamsOf,
      mul_pow, mul_pow, Real.sq_sqrt hposF.le, Real.sq_sqrt hposS.le]
    ring
  have hedgeEval : MvPolynomial.eval (designParamsOf D)
      (rowPairingPoly 3 first first + rowPairingPoly 3 second second - 1)
      = D.weight first * leverageOf (D.atom first)
        + D.weight second * leverageOf (D.atom second) - 1 := by
    rw [map_sub, map_add, map_one, eval_rowPairingPoly_self_designParamsOf,
      eval_rowPairingPoly_self_designParamsOf]
  rw [genericPairPoly, map_mul, map_mul, eval_rowPairingPoly_designParamsOf,
    hparallelEval, hedgeEval, mul_ne_zero_iff, mul_ne_zero_iff, and_assoc,
    pos_mul_ne_zero_iff (mul_pos (Real.sqrt_pos.mpr hposF) (Real.sqrt_pos.mpr hposS)),
    pos_mul_ne_zero_iff (mul_pos hposF hposS), sub_ne_zero, sub_ne_zero]
  exact Iff.rfl

/-- The per-triple factor is nonzero at a design exactly when the band is
strict. -/
theorem eval_genericTriplePoly_ne_zero_iff {m : ℕ} (D : WeightedDesign m 3)
    (first second third : Fin m) :
    MvPolynomial.eval (designParamsOf D) (genericTriplePoly first second third) ≠ 0
      ↔ excessGap D first second third ^ 2
          ≠ 4 * (atomPairing D first second * atomPairing D first third
              * atomPairing D second third) ^ 2 := by
  rw [eval_genericTriplePoly_designParamsOf,
    pos_mul_ne_zero_iff (pow_pos (mul_pos (mul_pos (D.weight_pos first)
      (D.weight_pos second)) (D.weight_pos third)) 2), sub_ne_zero]

/-- **The bundle bridge**: the generic bundle polynomial is nonzero at a
design's packed parameters exactly when the design is generic.  The tie
conjunct on the design side is recovered from the band factors through the
split identity — the bundle needs no tie factor. -/
theorem eval_genericBundlePoly_ne_zero_iff {m : ℕ} (D : WeightedDesign m 3) :
    MvPolynomial.eval (designParamsOf D) (genericBundlePoly m) ≠ 0
      ↔ IsGenericDesign D := by
  rw [genericBundlePoly, map_mul, mul_ne_zero_iff, map_prod, map_prod,
    Finset.prod_ne_zero_iff, Finset.prod_ne_zero_iff]
  constructor
  · rintro ⟨hpairs, htriples⟩
    have hpairFact : ∀ first second : Fin m, first ≠ second →
        (atomPairing D first second ≠ 0
          ∧ atomPairing D first second ^ 2
              ≠ leverageOf (D.atom first) * leverageOf (D.atom second)
          ∧ D.weight first * leverageOf (D.atom first)
              + D.weight second * leverageOf (D.atom second) ≠ 1) :=
      fun first second hne => (eval_genericPairPoly_ne_zero_iff D first second).mp
        (hpairs (first, second)
          (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩))
    have htripleFact : ∀ first second third : Fin m,
        first ≠ second → first ≠ third → second ≠ third →
        excessGap D first second third ^ 2
          ≠ 4 * (atomPairing D first second * atomPairing D first third
              * atomPairing D second third) ^ 2 :=
      fun first second third hfs hft hst =>
        (eval_genericTriplePoly_ne_zero_iff D first second third).mp
          (htriples (first, second, third)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfs, hft, hst⟩))
    exact ⟨fun first second hne => (hpairFact first second hne).1,
      fun first second hne => (hpairFact first second hne).2.1,
      fun first second hne => (hpairFact first second hne).2.2,
      htripleFact,
      fun first second third hfs hft hst =>
        discriminantTie_ne_zero_of_excessGap_sq_ne D (htripleFact first second third hfs hft hst)⟩
  · rintro ⟨hpairing, hparallel, hedge, hband, -⟩
    constructor
    · intro pair hpair
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hpair
      exact (eval_genericPairPoly_ne_zero_iff D pair.1 pair.2).mpr
        ⟨hpairing _ _ hne, hparallel _ _ hne, hedge _ _ hne⟩
    · intro triple htriple
      obtain ⟨-, hfs, hft, hst⟩ := Finset.mem_filter.mp htriple
      exact (eval_genericTriplePoly_ne_zero_iff D triple.1 triple.2.1 triple.2.2).mpr
        (hband _ _ _ hfs hft hst)

/-! ## The capstone -/

/-- **THE CAPSTONE — parametric avoidance.**  If the open cell fails, then for
EVERY degeneracy polynomial admitting one witness design off its vanishing
locus, a counterexample can be chosen all-heavy, with no dominating triple,
and off the locus.  This theorem is simultaneously the TEMPLATE for future
degeneracies: one application per new polynomial-plus-witness.

HONESTY: the statement is conditional on `¬ Gtz.GtzWeighted 6 3` and is
vacuous by nature if the GTZ conjecture is true — see the module header; the
non-vacuous interface is the consumable family below. -/
theorem exists_allHeavy_failing_avoiding_of_not_gtzWeighted
    (degeneracy : MvPolynomial (FrameParamIndex 6 3) ℝ)
    (witness : WeightedDesign 6 3)
    (hwitness : MvPolynomial.eval (designParamsOf witness) degeneracy ≠ 0)
    (hnot : ¬ GtzWeighted 6 3) :
    ∃ D : WeightedDesign 6 3, AllHeavy D
      ∧ (∀ C : Finset (Fin 6), C.card = 3 → ¬ Dominates D C)
      ∧ MvPolynomial.eval (designParamsOf D) degeneracy ≠ 0 := by
  classical
  obtain ⟨baseDesign, hbaseHeavy, hbaseFail⟩ :=
    exists_allHeavy_failing_of_not_gtzWeighted_six_three hnot
  have hrank : (3 : ℕ) < 6 := by norm_num
  obtain ⟨signs, baseRaw, hsigns, hdetSigns, hframeEq⟩ :=
    exists_signChartFrame_eq hrank (scaledAtomRows baseDesign)
      (transpose_mul_scaledAtomRows baseDesign)
  -- one strictly negative probe per triple of the failing base design
  have hprobeExists : ∀ C : Finset (Fin 6), C.card = 3 →
      ∃ probe : Fin 3 → ℝ,
        probe ⬝ᵥ ((subsetSum baseDesign C - 1) *ᵥ probe) < 0 :=
    fun C hcard => exists_negative_gap_probe_of_not_dominates (hbaseFail C hcard)
  set tripleProbe : Finset (Fin 6) → (Fin 3 → ℝ) := fun C =>
    if hcard : C.card = 3 then Classical.choose (hprobeExists C hcard) else 0
    with htripleProbe
  have htripleProbeSpec : ∀ (C : Finset (Fin 6)) (hcard : C.card = 3),
      tripleProbe C ⬝ᵥ ((subsetSum baseDesign C - 1) *ᵥ tripleProbe C) < 0 := by
    intro C hcard
    rw [htripleProbe]
    dsimp only
    rw [dif_pos hcard]
    exact Classical.choose_spec (hprobeExists C hcard)
  -- the open set of packed frame parameters where a design would be
  -- all-heavy and fail every triple through the chosen probes
  set goodParams : Set (FrameParamIndex 6 3 → ℝ) :=
    {frameParams | (∀ atomIndex : Fin 6, 0 < frameParams (Sum.inr atomIndex))
      ∧ (∀ atomIndex : Fin 6,
          0 < MvPolynomial.eval frameParams (clearedExcessPoly 3 atomIndex))
      ∧ ∀ C ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)),
          MvPolynomial.eval frameParams
            (clearedDominationGapPoly C (tripleProbe C)) < 0}
    with hgoodParams
  have hgoodOpen : IsOpen goodParams := by
    rw [hgoodParams, Set.setOf_and, Set.setOf_and]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun atomIndex =>
        isOpen_lt continuous_const (continuous_apply (Sum.inr atomIndex))
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun atomIndex =>
        isOpen_lt continuous_const (MvPolynomial.continuous_eval _)
    · rw [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun C => ?_
      by_cases hC : C ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6))
      · have hset : {frameParams : FrameParamIndex 6 3 → ℝ |
            C ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)) →
              MvPolynomial.eval frameParams
                (clearedDominationGapPoly C (tripleProbe C)) < 0}
            = {frameParams | MvPolynomial.eval frameParams
                (clearedDominationGapPoly C (tripleProbe C)) < 0} := by
          ext frameParams
          simp [hC]
        rw [hset]
        exact isOpen_lt (MvPolynomial.continuous_eval _) continuous_const
      · have hset : {frameParams : FrameParamIndex 6 3 → ℝ |
            C ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)) →
              MvPolynomial.eval frameParams
                (clearedDominationGapPoly C (tripleProbe C)) < 0}
            = Set.univ := by
          ext frameParams
          simp [hC]
        rw [hset]
        exact isOpen_univ
  -- the base design's packed parameters are good
  have hbaseMem : designParamsOf baseDesign ∈ goodParams := by
    refine ⟨fun atomIndex => baseDesign.weight_pos atomIndex,
      fun atomIndex => ?_, fun C hC => ?_⟩
    · rw [eval_clearedExcessPoly_designParamsOf]
      exact mul_pos (baseDesign.weight_pos atomIndex)
        (by linarith [hbaseHeavy atomIndex])
    · have hcard : C.card = 3 := Finset.mem_powersetCard_univ.mp hC
      rw [eval_clearedDominationGapPoly_designParamsOf]
      exact mul_neg_of_pos_of_neg
        (Finset.prod_pos fun c _ => baseDesign.weight_pos c)
        (htripleProbeSpec C hcard)
  -- pull back to an open chart set through the sign chart of the lift
  set chartGood : Set (ChartParamIndex 6 → ℝ) :=
    {chartParams | chartWeightSum chartParams ≠ 0}
      ∩ signChartParams hrank.le signs ⁻¹' goodParams
    with hchartGood
  have hchartOpen : IsOpen chartGood :=
    ContinuousOn.isOpen_inter_preimage (continuousOn_signChartParams hrank.le signs)
      isOpen_chartWeightSum_ne_zero hgoodOpen
  have hbaseChartMem : chartParamsOf baseRaw baseDesign.weight ∈ chartGood := by
    constructor
    · show chartWeightSum (chartParamsOf baseRaw baseDesign.weight) ≠ 0
      rw [chartWeightSum_chartParamsOf, baseDesign.weight_sum_one]
      exact one_ne_zero
    · show signChartParams hrank.le signs (chartParamsOf baseRaw baseDesign.weight)
        ∈ goodParams
      rw [signChartParams_chartParamsOf, hframeEq,
        normalizedWeights_of_sum_one baseDesign.weight_sum_one]
      exact hbaseMem
  by_cases hall : ∀ chartParams ∈ chartGood,
      MvPolynomial.eval (signChartParams hrank.le signs chartParams) degeneracy = 0
  · -- if the degeneracy vanished on the whole open chart set, the star
    -- propagation theorem would kill it at the witness — contradiction
    exact absurd
      (eval_frameParamsOf_eq_zero_of_eval_eq_zero_on_open hrank degeneracy hsigns
        hdetSigns hchartOpen ⟨_, hbaseChartMem⟩ (fun chartParams hmem => hmem.1) hall
        (scaledAtomRows witness) witness.weight
        (transpose_mul_scaledAtomRows witness) witness.weight_sum_one)
      hwitness
  · push Not at hall
    obtain ⟨chartParams, hchartMem, havoid⟩ := hall
    obtain ⟨hsumNe, hgoodMem⟩ := hchartMem
    obtain ⟨hweightPos, hheavyPos, hfailNeg⟩ := hgoodMem
    -- build the design carried by this chart point
    have hframeOrth := signChartFrame_transpose_mul_self hrank.le hsigns
      (chartRawPart chartParams)
    have hnormPos : ∀ atomIndex,
        0 < normalizedWeights (chartWeightPart chartParams) atomIndex :=
      hweightPos
    have hnormSum : ∑ atomIndex,
        normalizedWeights (chartWeightPart chartParams) atomIndex = 1 :=
      sum_normalizedWeights hsumNe
    set extractedDesign : WeightedDesign 6 3 :=
      designOfFrameWeights (signChartFrame hrank.le signs (chartRawPart chartParams))
        (normalizedWeights (chartWeightPart chartParams)) hframeOrth hnormPos hnormSum
      with hextractedDesign
    have hparamsEq : designParamsOf extractedDesign
        = signChartParams hrank.le signs chartParams := by
      rw [hextractedDesign, designParamsOf_designOfFrameWeights]
      rfl
    refine ⟨extractedDesign, ?_, ?_, ?_⟩
    · -- all-heavy from the packed cleared excess
      intro atomIndex
      have hvalue := hheavyPos atomIndex
      rw [← hparamsEq, eval_clearedExcessPoly_designParamsOf] at hvalue
      by_contra hle
      push Not at hle
      have hnonpos : extractedDesign.weight atomIndex
          * (leverageOf (extractedDesign.atom atomIndex) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (extractedDesign.weight_pos atomIndex).le (by linarith)
      linarith
    · -- no dominating triple, from the packed cleared gap forms
      intro C hcard hdom
      have hpsd : (subsetSum extractedDesign C - 1).PosSemidef := hdom
      have hquadNonneg :
          0 ≤ tripleProbe C ⬝ᵥ ((subsetSum extractedDesign C - 1) *ᵥ tripleProbe C) := by
        have hval := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (tripleProbe C)
        rwa [star_trivial] at hval
      have hvalue := hfailNeg C (Finset.mem_powersetCard_univ.mpr hcard)
      rw [← hparamsEq, eval_clearedDominationGapPoly_designParamsOf] at hvalue
      have hprodNonneg : 0 ≤ ∏ c ∈ C, extractedDesign.weight c :=
        (Finset.prod_pos fun c _ => extractedDesign.weight_pos c).le
      nlinarith
    · rw [hparamsEq]
      exact havoid

/-! ## The witness design

An exact rational `(6,3)` design passing the full generic bundle.  Its
weights are perfect rational squares, so all packed frame data is rational
and every certificate below is finite rational arithmetic. -/

/-- The atom table of the generic witness: six vectors over denominator
seventeen. -/
noncomputable def genericWitnessAtom : Fin 6 → Fin 3 → ℝ :=
  ![![-23/17, -8/17, -24/17], ![-4/17, 23/17, 18/17], ![16/17, 10/17, -21/17],
    ![30/17, 6/17, 18/17], ![24/17, -36/17, -6/17], ![9/17, 12/17, -15/17]]

/-- **The generic witness design**: exact rational Parseval weights
one-ninth (five times) and four-ninths. -/
noncomputable def genericWitnessDesign : WeightedDesign 6 3 where
  atom := genericWitnessAtom
  weight := ![1/9, 1/9, 1/9, 1/9, 1/9, 4/9]
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext coordFirst coordSecond
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, genericWitnessAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases coordFirst <;> fin_cases coordSecond <;> norm_num [Matrix.one_apply]

/-- The witness is all-heavy: every leverage exceeds one. -/
theorem genericWitnessDesign_allHeavy : AllHeavy genericWitnessDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    simp [genericWitnessDesign, genericWitnessAtom, leverageOf, Fin.sum_univ_three]
  all_goals norm_num

-- The generic-bundle certificate is 30 + 30 + 30 + 216 exact rational cases;
-- the heartbeat bump covers the case blast.
set_option maxHeartbeats 2000000 in
/-- **The witness passes the full generic bundle** — every conjunct certified
by exact rational arithmetic; the tie conjunct derived from the band conjunct
through the split identity. -/
theorem genericWitnessDesign_isGenericDesign : IsGenericDesign genericWitnessDesign := by
  have hband : ∀ first second third : Fin 6,
      first ≠ second → first ≠ third → second ≠ third →
      excessGap genericWitnessDesign first second third ^ 2
        ≠ 4 * (atomPairing genericWitnessDesign first second
            * atomPairing genericWitnessDesign first third
            * atomPairing genericWitnessDesign second third) ^ 2 := by
    intro first second third hfs hft hst
    fin_cases first <;> fin_cases second <;> fin_cases third
    all_goals try exact absurd rfl hfs
    all_goals try exact absurd rfl hft
    all_goals try exact absurd rfl hst
    all_goals
      simp [excessGap, heavyExcess, atomPairing, leverageOf, genericWitnessDesign,
        genericWitnessAtom, dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have hpairing : ∀ first second : Fin 6, first ≠ second →
      atomPairing genericWitnessDesign first second ≠ 0 := by
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    all_goals
      simp [atomPairing, genericWitnessDesign, genericWitnessAtom, dotProduct,
        Fin.sum_univ_three]
    all_goals norm_num
  have hparallel : ∀ first second : Fin 6, first ≠ second →
      atomPairing genericWitnessDesign first second ^ 2
        ≠ leverageOf (genericWitnessDesign.atom first)
          * leverageOf (genericWitnessDesign.atom second) := by
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    all_goals
      simp [atomPairing, leverageOf, genericWitnessDesign, genericWitnessAtom,
        dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have hedge : ∀ first second : Fin 6, first ≠ second →
      genericWitnessDesign.weight first * leverageOf (genericWitnessDesign.atom first)
        + genericWitnessDesign.weight second
          * leverageOf (genericWitnessDesign.atom second) ≠ 1 := by
    intro first second hne
    fin_cases first <;> fin_cases second
    all_goals try exact absurd rfl hne
    all_goals
      simp [leverageOf, genericWitnessDesign, genericWitnessAtom,
        Fin.sum_univ_three]
    all_goals norm_num
  exact ⟨hpairing, hparallel, hedge, hband, fun first second third hfs hft hst =>
    discriminantTie_ne_zero_of_excessGap_sq_ne genericWitnessDesign
      (hband first second third hfs hft hst)⟩

/-- **The witness has a dominating triple**: the subset `{0, 1, 2}`, certified
by the seven principal minors of the gap matrix — all exact rationals over
denominator two-eighty-nine. -/
theorem genericWitnessDesign_dominates : Dominates genericWitnessDesign {0, 1, 2} := by
  have hmat : subsetSum genericWitnessDesign {0, 1, 2} - 1
      = !![512/289, 252/289, 144/289;
           252/289, 404/289, 396/289;
           144/289, 396/289, 1052/289] := by
    rw [subsetSum, show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [atomMatrix, genericWitnessDesign, genericWitnessAtom]
    all_goals norm_num
  show (subsetSum genericWitnessDesign {0, 1, 2} - 1).PosSemidef
  rw [hmat]
  apply posSemidef_three_of_principalMinors
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> rfl
  all_goals simp [Matrix.det_fin_three]
  all_goals norm_num

/-- The witness's dominating triple, packaged: the closing hypotheses of the
consumable family are exercised by a kernel-checked design. -/
theorem genericWitnessDesign_exists_dominating_triple :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates genericWitnessDesign C :=
  ⟨{0, 1, 2}, by decide, genericWitnessDesign_dominates⟩

/-- The witness avoids the generic bundle locus — the packaged nonvanishing
certificate the capstone consumes. -/
theorem eval_genericBundlePoly_genericWitnessDesign_ne_zero :
    MvPolynomial.eval (designParamsOf genericWitnessDesign)
      (genericBundlePoly 6) ≠ 0 :=
  (eval_genericBundlePoly_ne_zero_iff genericWitnessDesign).mpr
    genericWitnessDesign_isGenericDesign

/-! ## The standard instance and the consumables -/

/-- **The standard bundle instance**: if the open cell fails, a counterexample
can be chosen all-heavy AND generic — every pairing nonzero, no parallel
pair, strict edges, strict bands, no tight triple.  Conditional on the cell
failing, hence vacuous by nature if the GTZ conjecture is true (module
header). -/
theorem exists_generic_allHeavy_failing_of_not_gtzWeighted
    (hnot : ¬ GtzWeighted 6 3) :
    ∃ D : WeightedDesign 6 3, AllHeavy D ∧ IsGenericDesign D
      ∧ ∀ C : Finset (Fin 6), C.card = 3 → ¬ Dominates D C := by
  obtain ⟨D, hheavy, hfail, havoid⟩ :=
    exists_allHeavy_failing_avoiding_of_not_gtzWeighted (genericBundlePoly 6)
      genericWitnessDesign eval_genericBundlePoly_genericWitnessDesign_ne_zero hnot
  exact ⟨D, hheavy, (eval_genericBundlePoly_ne_zero_iff D).mp havoid, hfail⟩

/-- **CONSUMABLE, parametric template**: to prove the open cell it suffices to
dominate the all-heavy designs off ANY single degeneracy locus with a witness.
Future degeneracy conditions are one application of this theorem (or one
polynomial multiplication via `eval_designParamsOf_mul_ne_zero_iff`). -/
theorem gtzWeighted_of_forall_avoiding_dominates
    (degeneracy : MvPolynomial (FrameParamIndex 6 3) ℝ)
    (witness : WeightedDesign 6 3)
    (hwitness : MvPolynomial.eval (designParamsOf witness) degeneracy ≠ 0)
    (hclose : ∀ D : WeightedDesign 6 3, AllHeavy D →
      MvPolynomial.eval (designParamsOf D) degeneracy ≠ 0 →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeighted 6 3 := by
  by_contra hnot
  obtain ⟨D, hheavy, hfail, havoid⟩ :=
    exists_allHeavy_failing_avoiding_of_not_gtzWeighted degeneracy witness hwitness hnot
  obtain ⟨C, hcard, hdom⟩ := hclose D hheavy havoid
  exact hfail C hcard hdom

/-- **CONSUMABLE, the standard bundle**: to prove the open cell it suffices to
dominate the GENERIC all-heavy designs.  Every future closing argument may
assume strictness and genericity.  (Scope: this narrows quantifiers only — no
margin certificate is manufactured; see the module header.) -/
theorem gtzWeighted_of_forall_generic_dominates
    (hclose : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_forall_avoiding_dominates (genericBundlePoly 6) genericWitnessDesign
    eval_genericBundlePoly_genericWitnessDesign_ne_zero
    fun D hheavy havoid =>
      hclose D hheavy ((eval_genericBundlePoly_ne_zero_iff D).mp havoid)

/-- **CONSUMABLE, ZP dissolution**: the zero-pairing branch is not a separate
obligation — to prove the open cell it suffices to dominate the all-heavy
designs whose atom pairings are ALL nonzero. -/
theorem gtzWeighted_of_forall_nonzero_pairings_dominates
    (hclose : ∀ D : WeightedDesign 6 3, AllHeavy D →
      (∀ first second : Fin 6, first ≠ second → atomPairing D first second ≠ 0) →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_forall_generic_dominates fun D hheavy hgeneric =>
    hclose D hheavy hgeneric.1

/-- Adding a degeneracy to an existing bundle is one polynomial
multiplication: the product avoids its locus exactly when both factors do. -/
theorem eval_designParamsOf_mul_ne_zero_iff (D : WeightedDesign 6 3)
    (degeneracyFirst degeneracySecond : MvPolynomial (FrameParamIndex 6 3) ℝ) :
    MvPolynomial.eval (designParamsOf D) (degeneracyFirst * degeneracySecond) ≠ 0
      ↔ (MvPolynomial.eval (designParamsOf D) degeneracyFirst ≠ 0
        ∧ MvPolynomial.eval (designParamsOf D) degeneracySecond ≠ 0) := by
  rw [map_mul, mul_ne_zero_iff]

/-! ## Bonus: the lifting-lemma frontier is the single open cell -/

/-- **The rank-two lifting lemma is exactly the open cell**: composing the
shipped `Gtz.liftingLemma_two_iff_the_two_residuals` with the shipped collapse
`Gtz.gtzWeighted_six_three_iff_seven_three` absorbs the second residual. -/
theorem liftingLemma_two_iff_gtzWeighted_six_three :
    LiftingLemma 2 ↔ GtzWeighted 6 3 :=
  liftingLemma_two_iff_the_two_residuals.trans
    (and_iff_left_iff_imp.mpr gtzWeighted_six_three_iff_seven_three.mp)

end Gtz

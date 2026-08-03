/-
# Chart pullback and star propagation

Module 3 of the genericity reduction for the open `(6,3)` cell: the cleared
polynomial pullback of the sign-chart atlas, and the STAR PROPAGATION theorem —
a degeneracy polynomial whose chart pullback vanishes on a nonempty open subset
of ONE positive chart's parameter space vanishes at EVERY orthonormal frame
with normalized weights.

The frame side of a `(size, rank)` design is a matrix `V` with orthonormal
columns (`Vᵀ·V = 1`) together with a weight vector summing to one; the pair is
packed into the coordinate function `frameParamsOf` on the variable index
`FrameParamIndex`.  A degeneracy condition is an arbitrary
`MvPolynomial (FrameParamIndex size rank) ℝ`.  Chart parameters are a raw skew
square plus a HOMOGENEOUS weight vector, packed by `chartParamsOf` on
`ChartParamIndex`; the chart with sign vector `ε` maps them to the frame data
`signChartFrame` (the first `rank` columns of `diag(ε) · cay(skewOfRaw raw)`)
and the normalized weights `u / Σu` — packaged as `signChartParams`.

Layers, in order:

* **The cleared pullback** (`exists_cleared_pullback`).  The chart map is
  rational with the two positive denominators `det(1 + A)` (K1) and `Σu`; by
  induction on the degeneracy polynomial (`MvPolynomial.induction_on`) there is
  a genuine polynomial `cleared` in the chart variables and exponents
  `detPower, sumPower` with
  `eval cleared = det(1+A)^detPower · (Σu)^sumPower · (degeneracy ∘ chart map)`
  wherever `Σu ≠ 0`.  CONVENTION RECORDED: exponents are EXISTENTIAL (padded to
  a common maximum at additions), not a homogenization by total degree — the
  general route of the blueprint, with two separate exponents instead of one
  power of a combined denominator.  The matrix twins live over the polynomial
  ring: `skewPolyMatrix` mirrors `Gtz.skewOfRaw` entrywise in the variables,
  `cayleyNumeratorPoly = (1 - S)·adj(1 + S)` clears the Cayley transform via
  the value-level identity `one_sub_mul_adjugate_one_add_of_skew`
  (`(1-A)·adj(1+A) = det(1+A) • cay(A)`), and evaluation commutes with `det`,
  `adjugate`, and the ring operations (`RingHom.map_det`,
  `RingHom.map_adjugate`).
* **The workhorse** (`chartVanishes_of_eval_eq_zero_on_open`): vanishing of the
  pulled-back degeneracy on a nonempty open set of chart parameters with
  nonvanishing weight sum forces `cleared = 0` (K5,
  `Gtz.mvPoly_eq_zero_of_eval_eq_zero_on_open`), hence — the denominators never
  vanishing, `det(1+A) > 0` by K1 — vanishing on the ENTIRE chart:
  `ChartVanishes`.
* **The two-flip chain step** (`chartVanishes_flipTwoSign_mul`): the K4 witness
  `Gtz.flipTwoWitnessSkew` gives a nonempty open overlap between a chart and
  its two-flip neighbour (openness via `MvPolynomial.continuous_eval` of the
  cleared overlap determinant), where every flipped-chart point re-expresses in
  the base chart by exact membership (`Gtz.exists_skew_of_det_sign_add_ne_zero`
  after the dressing `Gtz.diagonal_add_diagonal_mul_of_isSignVector`); the
  workhorse then propagates full vanishing to the neighbour.
* **The chain** (`chartVanishes_of_det_diagonal_eq`): two sign charts of equal
  diagonal determinant differ on an EVEN coordinate set
  (`even_card_disagreement_of_det_diagonal_eq`), so two-flip steps walk from
  one to the other; fuel induction on the disagreement count.
* **The lift** (`exists_specialOrthogonal_frameOf`, `exists_signChartFrame_eq`):
  every orthonormal frame extends to a SPECIAL orthogonal square matrix whose
  first `rank` columns it is — `Gtz.exists_orthonormal_completion` plus the
  `Matrix.fromCols`/`finSumFinEquiv` assembly and a determinant flip on a
  non-frame column (this is where `rank < size` is used); then K3
  (`Gtz.exists_positive_chart`) places the square in a positive chart.
* **THE STAR PROPAGATION THEOREM**
  (`eval_frameParamsOf_eq_zero_of_eval_eq_zero_on_open`): base chart vanishing
  from the workhorse, chain to the lift's chart, evaluate — the degeneracy
  vanishes at every frame pair with `Vᵀ·V = 1` and weight sum one.  Weight
  POSITIVITY is never needed on this side; the design layer (capstone module)
  supplies it when constructing `WeightedDesign` values.
* **Continuity** (`continuousOn_signChartParams`): the chart-to-frame-data map
  is continuous on the nonvanishing-weight-sum domain — each frame coordinate
  is a quotient of polynomial evaluations with K1-positive denominator, each
  weight coordinate a quotient with denominator nonzero on the domain.  This is
  what lets the capstone pull an open set of failing designs back to an open
  set of chart parameters.

Everything is at general size; only `rank < size` is assumed where the
determinant flip needs a spare column.  The design-vocabulary layer
(`Gtz.WeightedDesign`, `Gtz.AllHeavy`, and the capstone's planned packing map)
is deliberately NOT here — the capstone bridges to it (note: the tree's
`Gtz.chartFrame` on `Gtz.WeightedDesign` is that bridge's frame side, a
DIFFERENT map from this file's `signChartFrame`).

Backtick convention for this file's docstrings: multi-character backticked
tokens are declaration names (kernel-checked); single-letter backticked tokens
(`A`, `E`, `V`, `Q`, `S`) and the tokens `ε`, `Σu`, `u`, `raw`, `cay`, `adj`,
`diag`, `det`, `adjugate`, `cleared`, `rank` inside formulas are local
mathematical notation or local binder names, NOT constants.
-/
import Mathlib
import Gtz.LinAlg.CayleyAtlas
import Gtz.LinAlg.PolynomialOpenVanishing
import Gtz.LinAlg.Completion

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Parameter packing -/

/-- Variable index for frame-side data: a frame entry per `(row, column)` pair
plus a weight per atom. -/
abbrev FrameParamIndex (size rank : ℕ) : Type :=
  (Fin size × Fin rank) ⊕ Fin size

/-- Variable index for chart-side data: a raw skew coordinate per index pair
plus a homogeneous weight per atom. -/
abbrev ChartParamIndex (size : ℕ) : Type :=
  (Fin size × Fin size) ⊕ Fin size

/-- Pack a frame matrix and a weight vector into a coordinate function on the
frame variable index. -/
def frameParamsOf (frame : Matrix (Fin size) (Fin rank) ℝ) (weights : Fin size → ℝ) :
    FrameParamIndex size rank → ℝ :=
  Sum.elim (fun entry => frame entry.1 entry.2) weights

/-- The packed frame coordinates restrict to the frame entries. -/
theorem frameParamsOf_inl (frame : Matrix (Fin size) (Fin rank) ℝ)
    (weights : Fin size → ℝ) (entry : Fin size × Fin rank) :
    frameParamsOf frame weights (Sum.inl entry) = frame entry.1 entry.2 := rfl

/-- The packed frame coordinates restrict to the weights. -/
theorem frameParamsOf_inr (frame : Matrix (Fin size) (Fin rank) ℝ)
    (weights : Fin size → ℝ) (atomIndex : Fin size) :
    frameParamsOf frame weights (Sum.inr atomIndex) = weights atomIndex := rfl

/-- Pack a raw skew square and a homogeneous weight vector into a coordinate
function on the chart variable index. -/
def chartParamsOf (raw : Fin size → Fin size → ℝ) (weights : Fin size → ℝ) :
    ChartParamIndex size → ℝ :=
  Sum.elim (fun entry => raw entry.1 entry.2) weights

/-- The raw-square component of packed chart coordinates. -/
def chartRawPart (params : ChartParamIndex size → ℝ) : Fin size → Fin size → ℝ :=
  fun rowIndex colIndex => params (Sum.inl (rowIndex, colIndex))

/-- The weight component of packed chart coordinates. -/
def chartWeightPart (params : ChartParamIndex size → ℝ) : Fin size → ℝ :=
  fun atomIndex => params (Sum.inr atomIndex)

/-- The homogeneous weight sum of packed chart coordinates — the second
clearing denominator. -/
def chartWeightSum (params : ChartParamIndex size → ℝ) : ℝ :=
  ∑ atomIndex, chartWeightPart params atomIndex

/-- Unpacking after packing recovers the raw square. -/
theorem chartRawPart_chartParamsOf (raw : Fin size → Fin size → ℝ)
    (weights : Fin size → ℝ) : chartRawPart (chartParamsOf raw weights) = raw := rfl

/-- Unpacking after packing recovers the weights. -/
theorem chartWeightPart_chartParamsOf (raw : Fin size → Fin size → ℝ)
    (weights : Fin size → ℝ) : chartWeightPart (chartParamsOf raw weights) = weights := rfl

/-- Unpacking after packing recovers the weight sum. -/
theorem chartWeightSum_chartParamsOf (raw : Fin size → Fin size → ℝ)
    (weights : Fin size → ℝ) :
    chartWeightSum (chartParamsOf raw weights) = ∑ atomIndex, weights atomIndex := rfl

/-- Normalize a homogeneous weight vector to sum one (division by the sum;
meaningful where the sum is nonzero). -/
noncomputable def normalizedWeights (weights : Fin size → ℝ) : Fin size → ℝ :=
  fun atomIndex => weights atomIndex / ∑ otherIndex, weights otherIndex

/-- A weight vector already summing to one is its own normalization. -/
theorem normalizedWeights_of_sum_one {weights : Fin size → ℝ}
    (hsum : (∑ atomIndex, weights atomIndex) = 1) :
    normalizedWeights weights = weights := by
  funext atomIndex
  rw [normalizedWeights, hsum, div_one]

/-! ## The sign-chart frame map -/

/-- The first `rank` columns of a square matrix — the frame a square orthogonal
matrix carries. -/
def frameOf (hrank : rank ≤ size) (square : Matrix (Fin size) (Fin size) ℝ) :
    Matrix (Fin size) (Fin rank) ℝ :=
  square.submatrix id (Fin.castLE hrank)

/-- The frame of the sign-chart point: the first `rank` columns of
`diag(signs) · cay(skewOfRaw raw)`.  (The tree's `Gtz.chartFrame` is the
design-side Stiefel factor — a different map.) -/
noncomputable def signChartFrame (hrank : rank ≤ size) (signs : Fin size → ℝ)
    (raw : Fin size → Fin size → ℝ) : Matrix (Fin size) (Fin rank) ℝ :=
  frameOf hrank (Matrix.diagonal signs * cayleyOf (skewOfRaw raw))

/-- The full chart-to-frame-data map in packed coordinates: chart parameters to
the packed pair (sign-chart frame, normalized weights). -/
noncomputable def signChartParams (hrank : rank ≤ size) (signs : Fin size → ℝ)
    (params : ChartParamIndex size → ℝ) : FrameParamIndex size rank → ℝ :=
  frameParamsOf (signChartFrame hrank signs (chartRawPart params))
    (normalizedWeights (chartWeightPart params))

/-- The chart map at packed-then-unpacked coordinates, in unpacked vocabulary. -/
theorem signChartParams_chartParamsOf (hrank : rank ≤ size) (signs : Fin size → ℝ)
    (raw : Fin size → Fin size → ℝ) (weights : Fin size → ℝ) :
    signChartParams hrank signs (chartParamsOf raw weights)
      = frameParamsOf (signChartFrame hrank signs raw) (normalizedWeights weights) := by
  unfold signChartParams
  rw [chartRawPart_chartParamsOf, chartWeightPart_chartParamsOf]

/-- **Full vanishing on one chart**: the degeneracy polynomial, pulled through
the chart with the given signs, vanishes at EVERY raw square and every weight
vector with nonzero sum. -/
def ChartVanishes (hrank : rank ≤ size) (signs : Fin size → ℝ)
    (degeneracy : MvPolynomial (FrameParamIndex size rank) ℝ) : Prop :=
  ∀ (raw : Fin size → Fin size → ℝ) (weights : Fin size → ℝ),
    (∑ atomIndex, weights atomIndex) ≠ 0 →
    MvPolynomial.eval (frameParamsOf (signChartFrame hrank signs raw)
      (normalizedWeights weights)) degeneracy = 0

/-! ## Polynomial twins of the chart map -/

/-- The polynomial twin of `Gtz.skewOfRaw`: the skew matrix over the chart
polynomial ring whose strictly upper entries are the raw variables. -/
noncomputable def skewPolyMatrix (size : ℕ) :
    Matrix (Fin size) (Fin size) (MvPolynomial (ChartParamIndex size) ℝ) :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex < colIndex then MvPolynomial.X (Sum.inl (rowIndex, colIndex))
    else if colIndex < rowIndex then -(MvPolynomial.X (Sum.inl (colIndex, rowIndex)))
    else 0

/-- The cleared Cayley numerator over the polynomial ring:
`(1 - S)·adj(1 + S)` for `S` the skew twin.  Its entries are polynomials whose
evaluations are `det(1+A)` times the Cayley entries. -/
noncomputable def cayleyNumeratorPoly (size : ℕ) :
    Matrix (Fin size) (Fin size) (MvPolynomial (ChartParamIndex size) ℝ) :=
  (1 - skewPolyMatrix size) * (1 + skewPolyMatrix size).adjugate

/-- The Cayley clearing denominator over the polynomial ring:
`det(1 + S)` for `S` the skew twin. -/
noncomputable def cayleyDenominatorPoly (size : ℕ) :
    MvPolynomial (ChartParamIndex size) ℝ :=
  (1 + skewPolyMatrix size).det

/-- The weight-sum clearing denominator over the polynomial ring. -/
noncomputable def weightSumPoly (size : ℕ) : MvPolynomial (ChartParamIndex size) ℝ :=
  ∑ atomIndex, MvPolynomial.X (Sum.inr atomIndex)

/-- Evaluating the skew twin entrywise gives `skewOfRaw` of the unpacked raw
square. -/
theorem map_skewPolyMatrix (params : ChartParamIndex size → ℝ) :
    (skewPolyMatrix size).map (MvPolynomial.eval params)
      = skewOfRaw (chartRawPart params) := by
  ext rowIndex colIndex
  simp only [Matrix.map_apply, skewPolyMatrix, skewOfRaw, Matrix.of_apply]
  split_ifs <;> simp [chartRawPart]

/-- Evaluating the denominator twin gives the true Cayley denominator
determinant. -/
theorem eval_cayleyDenominatorPoly (params : ChartParamIndex size → ℝ) :
    MvPolynomial.eval params (cayleyDenominatorPoly size)
      = ((1 : Matrix (Fin size) (Fin size) ℝ) + skewOfRaw (chartRawPart params)).det := by
  rw [cayleyDenominatorPoly, RingHom.map_det]
  congr 1
  rw [map_add, map_one, RingHom.mapMatrix_apply, map_skewPolyMatrix]

/-- Evaluating the numerator twin entrywise gives the true cleared Cayley
numerator. -/
theorem map_cayleyNumeratorPoly (params : ChartParamIndex size → ℝ) :
    (MvPolynomial.eval params).mapMatrix (cayleyNumeratorPoly size)
      = (1 - skewOfRaw (chartRawPart params))
        * ((1 : Matrix (Fin size) (Fin size) ℝ) + skewOfRaw (chartRawPart params)).adjugate := by
  rw [cayleyNumeratorPoly, map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one]
  rw [RingHom.mapMatrix_apply, map_skewPolyMatrix]

/-- Evaluating the weight-sum twin gives the weight sum. -/
theorem eval_weightSumPoly (params : ChartParamIndex size → ℝ) :
    MvPolynomial.eval params (weightSumPoly size) = chartWeightSum params := by
  rw [weightSumPoly, map_sum, chartWeightSum]
  simp [chartWeightPart]

/-- **The value-level clearing identity**: for skew `A`,
`(1 - A)·adj(1 + A) = det(1 + A) • cay(A)`.  This is how the polynomial
numerator twin relates to the rational Cayley transform. -/
theorem one_sub_mul_adjugate_one_add_of_skew {skew : Matrix (Fin size) (Fin size) ℝ}
    (hskew : skewᵀ = -skew) :
    (1 - skew) * ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).adjugate
      = ((1 : Matrix (Fin size) (Fin size) ℝ) + skew).det • cayleyOf skew := by
  have hdetNe := det_one_add_ne_zero_of_skew hskew
  rw [cayleyOf_eq, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hdetNe, one_smul]

/-- Entrywise clearing: each numerator-twin evaluation is the denominator
determinant times the Cayley entry. -/
theorem eval_cayleyNumeratorPoly_entry (params : ChartParamIndex size → ℝ)
    (rowIndex colIndex : Fin size) :
    MvPolynomial.eval params ((cayleyNumeratorPoly size) rowIndex colIndex)
      = ((1 : Matrix (Fin size) (Fin size) ℝ) + skewOfRaw (chartRawPart params)).det
        * cayleyOf (skewOfRaw (chartRawPart params)) rowIndex colIndex := by
  have hentry := congrArg (fun matrixValue => matrixValue rowIndex colIndex)
    (map_cayleyNumeratorPoly params)
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hentry
  rw [hentry, one_sub_mul_adjugate_one_add_of_skew (transpose_skewOfRaw _),
    Matrix.smul_apply, smul_eq_mul]

/-! ## The cleared pullback -/

/-- **THE CLEARED PULLBACK.**  For every degeneracy polynomial there are a chart
polynomial and two exponents such that, wherever the weight sum is nonzero, the
chart polynomial evaluates to the degeneracy value at the chart image scaled by
the two clearing denominators to those powers.  Existential-exponent
convention: additions pad both summands to the maximum exponent pair. -/
theorem exists_cleared_pullback (hrank : rank ≤ size) (signs : Fin size → ℝ)
    (degeneracy : MvPolynomial (FrameParamIndex size rank) ℝ) :
    ∃ (cleared : MvPolynomial (ChartParamIndex size) ℝ) (detPower sumPower : ℕ),
      ∀ params : ChartParamIndex size → ℝ, chartWeightSum params ≠ 0 →
        MvPolynomial.eval params cleared
          = ((1 : Matrix (Fin size) (Fin size) ℝ) + skewOfRaw (chartRawPart params)).det
              ^ detPower
            * chartWeightSum params ^ sumPower
            * MvPolynomial.eval (signChartParams hrank signs params) degeneracy := by
  induction degeneracy using MvPolynomial.induction_on with
  | C constant =>
      refine ⟨MvPolynomial.C constant, 0, 0, fun params _ => ?_⟩
      simp
  | add leftPoly rightPoly leftInduction rightInduction =>
      obtain ⟨clearedLeft, detLeft, sumLeft, hleft⟩ := leftInduction
      obtain ⟨clearedRight, detRight, sumRight, hright⟩ := rightInduction
      refine ⟨clearedLeft * (cayleyDenominatorPoly size) ^ (max detLeft detRight - detLeft)
            * (weightSumPoly size) ^ (max sumLeft sumRight - sumLeft)
          + clearedRight * (cayleyDenominatorPoly size) ^ (max detLeft detRight - detRight)
            * (weightSumPoly size) ^ (max sumLeft sumRight - sumRight),
        max detLeft detRight, max sumLeft sumRight, fun params hsum => ?_⟩
      rw [map_add, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
        eval_cayleyDenominatorPoly, eval_weightSumPoly, hleft params hsum,
        hright params hsum, map_add]
      set detValue := ((1 : Matrix (Fin size) (Fin size) ℝ)
        + skewOfRaw (chartRawPart params)).det with hdetValue
      set sumValue := chartWeightSum params with hsumValue
      set leftValue := MvPolynomial.eval (signChartParams hrank signs params) leftPoly
        with hleftValue
      set rightValue := MvPolynomial.eval (signChartParams hrank signs params) rightPoly
        with hrightValue
      have hdetLeft : detValue ^ detLeft * detValue ^ (max detLeft detRight - detLeft)
          = detValue ^ max detLeft detRight := by
        rw [← pow_add, Nat.add_sub_cancel' (le_max_left detLeft detRight)]
      have hdetRight : detValue ^ detRight * detValue ^ (max detLeft detRight - detRight)
          = detValue ^ max detLeft detRight := by
        rw [← pow_add, Nat.add_sub_cancel' (le_max_right detLeft detRight)]
      have hsumLeft : sumValue ^ sumLeft * sumValue ^ (max sumLeft sumRight - sumLeft)
          = sumValue ^ max sumLeft sumRight := by
        rw [← pow_add, Nat.add_sub_cancel' (le_max_left sumLeft sumRight)]
      have hsumRight : sumValue ^ sumRight * sumValue ^ (max sumLeft sumRight - sumRight)
          = sumValue ^ max sumLeft sumRight := by
        rw [← pow_add, Nat.add_sub_cancel' (le_max_right sumLeft sumRight)]
      calc detValue ^ detLeft * sumValue ^ sumLeft * leftValue
              * detValue ^ (max detLeft detRight - detLeft)
              * sumValue ^ (max sumLeft sumRight - sumLeft)
            + detValue ^ detRight * sumValue ^ sumRight * rightValue
              * detValue ^ (max detLeft detRight - detRight)
              * sumValue ^ (max sumLeft sumRight - sumRight)
          = (detValue ^ detLeft * detValue ^ (max detLeft detRight - detLeft))
              * ((sumValue ^ sumLeft * sumValue ^ (max sumLeft sumRight - sumLeft))
                * leftValue)
            + (detValue ^ detRight * detValue ^ (max detLeft detRight - detRight))
              * ((sumValue ^ sumRight * sumValue ^ (max sumLeft sumRight - sumRight))
                * rightValue) := by ring
        _ = detValue ^ max detLeft detRight
              * (sumValue ^ max sumLeft sumRight * leftValue)
            + detValue ^ max detLeft detRight
              * (sumValue ^ max sumLeft sumRight * rightValue) := by
            rw [hdetLeft, hdetRight, hsumLeft, hsumRight]
        _ = detValue ^ max detLeft detRight * sumValue ^ max sumLeft sumRight
              * (leftValue + rightValue) := by ring
  | mul_X innerPoly varIndex innerInduction =>
      obtain ⟨clearedInner, detInner, sumInner, hinner⟩ := innerInduction
      rcases varIndex with ⟨rowIndex, colIndex⟩ | atomIndex
      · -- frame-entry variable: multiply by the sign-scaled numerator entry
        refine ⟨clearedInner * (MvPolynomial.C (signs rowIndex)
            * (cayleyNumeratorPoly size) rowIndex (Fin.castLE hrank colIndex)),
          detInner + 1, sumInner, fun params hsum => ?_⟩
        have hentry : signChartParams hrank signs params (Sum.inl (rowIndex, colIndex))
            = signs rowIndex
              * cayleyOf (skewOfRaw (chartRawPart params)) rowIndex
                  (Fin.castLE hrank colIndex) := by
          unfold signChartParams frameParamsOf signChartFrame frameOf
          simp [Matrix.submatrix_apply, Matrix.diagonal_mul]
        rw [map_mul, map_mul, MvPolynomial.eval_C, eval_cayleyNumeratorPoly_entry,
          hinner params hsum, map_mul, MvPolynomial.eval_X, hentry]
        ring
      · -- weight variable: multiply by the weight variable itself
        refine ⟨clearedInner * MvPolynomial.X (Sum.inr atomIndex),
          detInner, sumInner + 1, fun params hsum => ?_⟩
        have hentry : signChartParams hrank signs params (Sum.inr atomIndex)
            = chartWeightPart params atomIndex / chartWeightSum params := rfl
        rw [map_mul, MvPolynomial.eval_X, hinner params hsum, map_mul,
          MvPolynomial.eval_X, hentry, pow_succ,
          show params (Sum.inr atomIndex) = chartWeightPart params atomIndex from rfl]
        conv_lhs => rw [show chartWeightPart params atomIndex
          = chartWeightPart params atomIndex / chartWeightSum params
            * chartWeightSum params from (div_mul_cancel₀ _ hsum).symm]
        ring

/-! ## The workhorse: open vanishing forces full chart vanishing -/

/-- **THE WORKHORSE.**  If the pulled-back degeneracy vanishes on a nonempty
OPEN set of chart parameters with nonvanishing weight sum, it vanishes on the
ENTIRE chart: the cleared pullback vanishes on the open set (denominators
nonzero there), hence is the zero polynomial (K5), hence the degeneracy value
vanishes wherever the weight sum is nonzero — the Cayley denominator never
vanishes at all (K1). -/
theorem chartVanishes_of_eval_eq_zero_on_open (hrank : rank ≤ size)
    (signs : Fin size → ℝ) (degeneracy : MvPolynomial (FrameParamIndex size rank) ℝ)
    {vanishingSet : Set (ChartParamIndex size → ℝ)}
    (hopen : IsOpen vanishingSet) (hnonempty : vanishingSet.Nonempty)
    (hsum : ∀ params ∈ vanishingSet, chartWeightSum params ≠ 0)
    (hvanish : ∀ params ∈ vanishingSet,
      MvPolynomial.eval (signChartParams hrank signs params) degeneracy = 0) :
    ChartVanishes hrank signs degeneracy := by
  obtain ⟨cleared, detPower, sumPower, hidentity⟩ :=
    exists_cleared_pullback hrank signs degeneracy
  have hclearedZero : cleared = 0 := by
    apply mvPoly_eq_zero_of_eval_eq_zero_on_open cleared hopen hnonempty
    intro params hparams
    rw [hidentity params (hsum params hparams), hvanish params hparams, mul_zero]
  intro raw weights hweights
  have hsumPacked : chartWeightSum (chartParamsOf raw weights) ≠ 0 := by
    rw [chartWeightSum_chartParamsOf]
    exact hweights
  have hzero := hidentity (chartParamsOf raw weights) hsumPacked
  rw [hclearedZero, map_zero] at hzero
  have hdetNe : ((1 : Matrix (Fin size) (Fin size) ℝ)
      + skewOfRaw (chartRawPart (chartParamsOf raw weights))).det ≠ 0 :=
    det_one_add_ne_zero_of_skew (transpose_skewOfRaw _)
  have hfactorNe : ((1 : Matrix (Fin size) (Fin size) ℝ)
        + skewOfRaw (chartRawPart (chartParamsOf raw weights))).det ^ detPower
      * chartWeightSum (chartParamsOf raw weights) ^ sumPower ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hdetNe) (pow_ne_zero _ hsumPacked)
  have hevalZero : MvPolynomial.eval
      (signChartParams hrank signs (chartParamsOf raw weights)) degeneracy = 0 :=
    (mul_eq_zero.mp hzero.symm).resolve_left hfactorNe
  rwa [signChartParams_chartParamsOf] at hevalZero

/-! ## The two-flip chain step -/

/-- **THE CHAIN STEP.**  Chart vanishing propagates to the two-flip neighbour:
the K4 witness gives a nonempty open overlap set (cleared overlap determinant
nonzero, weight sum nonzero), on which every flipped-chart point factors
through the base chart by exact membership; the workhorse upgrades vanishing
there to the whole flipped chart. -/
theorem chartVanishes_flipTwoSign_mul (hrank : rank ≤ size)
    {signs : Fin size → ℝ} (hsigns : IsSignVector signs)
    {first second : Fin size} (hne : first ≠ second)
    {degeneracy : MvPolynomial (FrameParamIndex size rank) ℝ}
    (hvanish : ChartVanishes hrank signs degeneracy) :
    ChartVanishes hrank (fun index => flipTwoSign first second index * signs index)
      degeneracy := by
  classical
  have hflipped : IsSignVector (fun index => flipTwoSign first second index * signs index) :=
    (isSignVector_flipTwoSign first second).mul hsigns
  -- the cleared overlap determinant as a chart polynomial
  set flipDiagPoly : Matrix (Fin size) (Fin size) (MvPolynomial (ChartParamIndex size) ℝ) :=
    Matrix.diagonal (fun index => MvPolynomial.C (flipTwoSign first second index))
    with hflipDiagPoly
  set overlapPoly : MvPolynomial (ChartParamIndex size) ℝ :=
    ((flipDiagPoly + 1) + (flipDiagPoly - 1) * skewPolyMatrix size).det with hoverlapPoly
  have hmapDiag : ∀ params : ChartParamIndex size → ℝ,
      (MvPolynomial.eval params).mapMatrix flipDiagPoly
        = Matrix.diagonal (flipTwoSign first second) := by
    intro params
    rw [RingHom.mapMatrix_apply, hflipDiagPoly, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext index
    rw [MvPolynomial.eval_C]
  have hevalOverlap : ∀ params : ChartParamIndex size → ℝ,
      MvPolynomial.eval params overlapPoly
        = ((Matrix.diagonal (flipTwoSign first second) + 1)
            + (Matrix.diagonal (flipTwoSign first second) - 1)
              * skewOfRaw (chartRawPart params)).det := by
    intro params
    rw [hoverlapPoly, RingHom.map_det]
    congr 1
    rw [map_add, map_add, map_one, map_mul, map_sub, map_one, hmapDiag params,
      RingHom.mapMatrix_apply, map_skewPolyMatrix]
  -- the overlap parameter set
  set overlapSet : Set (ChartParamIndex size → ℝ) :=
    {params | MvPolynomial.eval params overlapPoly ≠ 0 ∧ chartWeightSum params ≠ 0}
    with hoverlapSet
  have hopen : IsOpen overlapSet := by
    have hopenDet : IsOpen {params : ChartParamIndex size → ℝ |
        MvPolynomial.eval params overlapPoly ≠ 0} :=
      isOpen_ne.preimage (MvPolynomial.continuous_eval overlapPoly)
    have hopenSum : IsOpen {params : ChartParamIndex size → ℝ |
        chartWeightSum params ≠ 0} :=
      isOpen_ne.preimage (by
        unfold chartWeightSum chartWeightPart
        exact continuous_finsetSum Finset.univ
          fun atomIndex _ => continuous_apply (Sum.inr atomIndex))
    exact hopenDet.inter hopenSum
  have hnonempty : overlapSet.Nonempty := by
    refine ⟨chartParamsOf
      (fun rowIndex colIndex => flipTwoWitnessSkew first second rowIndex colIndex)
      (fun _ => 1), ?_, ?_⟩
    · show MvPolynomial.eval _ overlapPoly ≠ 0
      rw [hevalOverlap, chartRawPart_chartParamsOf,
        skewOfRaw_entries_of_skew (transpose_flipTwoWitnessSkew first second)]
      exact det_flipTwoNumerator_ne_zero hne
    · show chartWeightSum _ ≠ 0
      rw [chartWeightSum_chartParamsOf]
      have hpos : (0 : ℝ) < size := by
        have := first.pos
        exact_mod_cast this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      exact ne_of_gt hpos
  -- on the overlap, flipped-chart points vanish through the base chart
  have hvanishOverlap : ∀ params ∈ overlapSet,
      MvPolynomial.eval (signChartParams hrank
        (fun index => flipTwoSign first second index * signs index) params)
        degeneracy = 0 := by
    intro params hparams
    obtain ⟨hoverlapNe, hsumNe⟩ := hparams
    have hskewCurrent : (skewOfRaw (chartRawPart params))ᵀ
        = -(skewOfRaw (chartRawPart params)) := transpose_skewOfRaw _
    have hdetOneNe : ((1 : Matrix (Fin size) (Fin size) ℝ)
        + skewOfRaw (chartRawPart params)).det ≠ 0 :=
      det_one_add_ne_zero_of_skew hskewCurrent
    -- the genuine overlap determinant is nonzero
    have hoverlapDet : (Matrix.diagonal (flipTwoSign first second)
        + cayleyOf (skewOfRaw (chartRawPart params))).det ≠ 0 := by
      intro hzero
      apply hoverlapNe
      rw [hevalOverlap params]
      have hcleared := congrArg Matrix.det
        (add_cayleyOf_mul_one_add (Matrix.diagonal (flipTwoSign first second)) hdetOneNe)
      rw [det_mul, hzero, zero_mul] at hcleared
      exact hcleared.symm
    -- dress the flipped-chart point into the base chart's membership condition
    have hproductFun : (fun index =>
        (flipTwoSign first second index * signs index) * signs index)
        = flipTwoSign first second := by
      funext index
      rw [mul_assoc, hsigns.mul_self, mul_one]
    have hdressed : Matrix.diagonal signs
        + Matrix.diagonal (fun index => flipTwoSign first second index * signs index)
          * cayleyOf (skewOfRaw (chartRawPart params))
        = Matrix.diagonal (fun index => flipTwoSign first second index * signs index)
          * (Matrix.diagonal (flipTwoSign first second)
            + cayleyOf (skewOfRaw (chartRawPart params))) := by
      rw [diagonal_add_diagonal_mul_of_isSignVector hflipped, hproductFun]
    have hmemberDet : (Matrix.diagonal signs
        + Matrix.diagonal (fun index => flipTwoSign first second index * signs index)
          * cayleyOf (skewOfRaw (chartRawPart params))).det ≠ 0 := by
      rw [hdressed, det_mul]
      exact mul_ne_zero hflipped.det_diagonal_ne_zero hoverlapDet
    have horthQ : (Matrix.diagonal (fun index => flipTwoSign first second index * signs index)
          * cayleyOf (skewOfRaw (chartRawPart params)))ᵀ
        * (Matrix.diagonal (fun index => flipTwoSign first second index * signs index)
          * cayleyOf (skewOfRaw (chartRawPart params))) = 1 := by
      rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc
          (Matrix.diagonal (fun index => flipTwoSign first second index * signs index))
          (Matrix.diagonal (fun index => flipTwoSign first second index * signs index))
          (cayleyOf (skewOfRaw (chartRawPart params))),
        hflipped.diagonal_mul_self, Matrix.one_mul,
        cayleyOf_transpose_mul_self hskewCurrent]
    obtain ⟨memberSkew, hmemberSkew, hfactor⟩ :=
      exists_skew_of_det_sign_add_ne_zero horthQ hsigns hmemberDet
    -- rewrite the flipped chart frame as a base chart frame
    have hframeEq : signChartFrame hrank
        (fun index => flipTwoSign first second index * signs index) (chartRawPart params)
        = signChartFrame hrank signs
            (fun rowIndex colIndex => memberSkew rowIndex colIndex) := by
      unfold signChartFrame
      rw [skewOfRaw_entries_of_skew hmemberSkew, hfactor]
    have hbase := hvanish (fun rowIndex colIndex => memberSkew rowIndex colIndex)
      (chartWeightPart params) hsumNe
    show MvPolynomial.eval (frameParamsOf (signChartFrame hrank
      (fun index => flipTwoSign first second index * signs index) (chartRawPart params))
      (normalizedWeights (chartWeightPart params))) degeneracy = 0
    rw [hframeEq]
    exact hbase
  exact chartVanishes_of_eval_eq_zero_on_open hrank
    (fun index => flipTwoSign first second index * signs index) degeneracy
    hopen hnonempty (fun params hparams => hparams.2) hvanishOverlap

/-! ## Parity and the chain -/

/-- Two sign vectors whose diagonal determinants agree disagree on an EVEN set
of coordinates: the product of all pairwise sign products is `(-1)` to the
disagreement count and also the product of the two determinants' quotient,
which is one. -/
theorem even_card_disagreement_of_det_diagonal_eq
    {signsLeft signsRight : Fin size → ℝ}
    (hleft : IsSignVector signsLeft) (hright : IsSignVector signsRight)
    (hdet : (Matrix.diagonal signsLeft).det = (Matrix.diagonal signsRight).det) :
    Even (Finset.univ.filter
      (fun index => signsLeft index ≠ signsRight index)).card := by
  classical
  have hprodEq : (∏ index, signsLeft index) = ∏ index, signsRight index := by
    rw [← det_diagonal, ← det_diagonal, hdet]
  have hpair : (∏ index, signsLeft index * signsRight index) = 1 := by
    rw [Finset.prod_mul_distrib, hprodEq, ← Finset.prod_mul_distrib]
    calc (∏ index, signsRight index * signsRight index)
        = ∏ _index, (1 : ℝ) :=
          Finset.prod_congr rfl fun index _ => hright.mul_self index
      _ = 1 := Finset.prod_const_one
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun index => signsLeft index ≠ signsRight index)
    (fun index => signsLeft index * signsRight index)
  have hdisagree : (∏ index ∈ Finset.univ.filter
      (fun index => signsLeft index ≠ signsRight index),
        signsLeft index * signsRight index)
      = (-1 : ℝ) ^ (Finset.univ.filter
          (fun index => signsLeft index ≠ signsRight index)).card := by
    rw [Finset.prod_congr rfl (fun index hindex => ?_), Finset.prod_const]
    rw [Finset.mem_filter] at hindex
    rcases hleft index with hvalLeft | hvalLeft <;> rcases hright index with hvalRight | hvalRight
    · exact absurd (hvalLeft.trans hvalRight.symm) hindex.2
    · rw [hvalLeft, hvalRight]; norm_num
    · rw [hvalLeft, hvalRight]; norm_num
    · exact absurd (hvalLeft.trans hvalRight.symm) hindex.2
  have hagree : (∏ index ∈ Finset.univ.filter
      (fun index => ¬(signsLeft index ≠ signsRight index)),
        signsLeft index * signsRight index) = 1 := by
    refine Finset.prod_eq_one fun index hindex => ?_
    rw [Finset.mem_filter] at hindex
    have hvalEq : signsLeft index = signsRight index := not_ne_iff.mp hindex.2
    rw [hvalEq]
    exact hright.mul_self index
  rw [hdisagree, hagree, mul_one, hpair] at hsplit
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hsplit

/-- **THE CHAIN.**  Chart vanishing propagates between ANY two sign charts of
equal diagonal determinant, by two-flip steps across the (even) disagreement
set; fuel induction on the disagreement count. -/
theorem chartVanishes_of_det_diagonal_eq (hrank : rank ≤ size)
    {signsBase signsTarget : Fin size → ℝ}
    (hbase : IsSignVector signsBase) (htarget : IsSignVector signsTarget)
    (hdet : (Matrix.diagonal signsBase).det = (Matrix.diagonal signsTarget).det)
    {degeneracy : MvPolynomial (FrameParamIndex size rank) ℝ}
    (hvanish : ChartVanishes hrank signsBase degeneracy) :
    ChartVanishes hrank signsTarget degeneracy := by
  classical
  suffices hfuel : ∀ (fuel : ℕ) (signsCurrent : Fin size → ℝ),
      IsSignVector signsCurrent →
      (Finset.univ.filter (fun index => signsCurrent index ≠ signsTarget index)).card
        ≤ fuel →
      Even (Finset.univ.filter
        (fun index => signsCurrent index ≠ signsTarget index)).card →
      ChartVanishes hrank signsCurrent degeneracy →
      ChartVanishes hrank signsTarget degeneracy by
    exact hfuel (Finset.univ.filter
        (fun index => signsBase index ≠ signsTarget index)).card
      signsBase hbase le_rfl
      (even_card_disagreement_of_det_diagonal_eq hbase htarget hdet) hvanish
  intro fuel
  induction fuel with
  | zero =>
      intro signsCurrent _ hcard _ hvanishCurrent
      have hempty : Finset.univ.filter
          (fun index => signsCurrent index ≠ signsTarget index) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hequal : signsCurrent = signsTarget := by
        funext index
        by_contra hneq
        have hmem : index ∈ Finset.univ.filter
            (fun index => signsCurrent index ≠ signsTarget index) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ index, hneq⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty index)
      rwa [hequal] at hvanishCurrent
  | succ fuelRemaining fuelInduction =>
      intro signsCurrent hcurrent hcard heven hvanishCurrent
      by_cases hempty : Finset.univ.filter
          (fun index => signsCurrent index ≠ signsTarget index) = ∅
      · have hequal : signsCurrent = signsTarget := by
          funext index
          by_contra hneq
          have hmem : index ∈ Finset.univ.filter
              (fun index => signsCurrent index ≠ signsTarget index) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ index, hneq⟩
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty index)
        rwa [hequal] at hvanishCurrent
      · -- the disagreement set has at least two elements (it is even, nonempty)
        have hcardNe : (Finset.univ.filter
            (fun index => signsCurrent index ≠ signsTarget index)).card ≠ 0 := by
          rwa [ne_eq, Finset.card_eq_zero]
        have htwoLe : 1 < (Finset.univ.filter
            (fun index => signsCurrent index ≠ signsTarget index)).card := by
          rcases heven with ⟨halfCount, hhalf⟩
          omega
        obtain ⟨first, hfirst, second, hsecond, hne⟩ := Finset.one_lt_card.mp htwoLe
        have hfirstNe : signsCurrent first ≠ signsTarget first :=
          (Finset.mem_filter.mp hfirst).2
        have hsecondNe : signsCurrent second ≠ signsTarget second :=
          (Finset.mem_filter.mp hsecond).2
        -- flip the current signs at the two disagreement indices
        have hvanishNext : ChartVanishes hrank
            (fun index => flipTwoSign first second index * signsCurrent index)
            degeneracy :=
          chartVanishes_flipTwoSign_mul hrank hcurrent hne hvanishCurrent
        have hnextSign : IsSignVector
            (fun index => flipTwoSign first second index * signsCurrent index) :=
          (isSignVector_flipTwoSign first second).mul hcurrent
        -- the new disagreement set drops exactly the two flipped indices
        have hdisNext : Finset.univ.filter
            (fun index => flipTwoSign first second index * signsCurrent index
              ≠ signsTarget index)
            = (Finset.univ.filter
                (fun index => signsCurrent index ≠ signsTarget index))
              \ {first, second} := by
          ext index
          rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_filter]
          simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
          by_cases hpair : index = first ∨ index = second
          · have hflipValue : flipTwoSign first second index = -1 := by
              simp [flipTwoSign, hpair]
            have hcurrentNe : signsCurrent index ≠ signsTarget index := by
              rcases hpair with rfl | rfl
              · exact hfirstNe
              · exact hsecondNe
            have htargetValue : signsTarget index = -(signsCurrent index) := by
              rcases hcurrent index with hcur | hcur <;>
                rcases htarget index with htar | htar
              · exact absurd (hcur.trans htar.symm) hcurrentNe
              · norm_num [hcur, htar]
              · norm_num [hcur, htar]
              · exact absurd (hcur.trans htar.symm) hcurrentNe
            constructor
            · intro hnextNe
              exfalso
              apply hnextNe
              rw [hflipValue, htargetValue]
              ring
            · rintro ⟨_, hnotPair⟩
              exact absurd hpair hnotPair
          · have hflipValue : flipTwoSign first second index = 1 := by
              simp [flipTwoSign, hpair]
            rw [hflipValue, one_mul]
            exact ⟨fun hneq => ⟨hneq, hpair⟩, fun hboth => hboth.1⟩
        have hpairSubset : ({first, second} : Finset (Fin size))
            ⊆ Finset.univ.filter
              (fun index => signsCurrent index ≠ signsTarget index) := by
          rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨hfirst, hsecond⟩
        have hpairCard : ({first, second} : Finset (Fin size)).card = 2 := by
          rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hne),
            Finset.card_singleton]
        have hcardNext : (Finset.univ.filter
            (fun index => flipTwoSign first second index * signsCurrent index
              ≠ signsTarget index)).card
            = (Finset.univ.filter
                (fun index => signsCurrent index ≠ signsTarget index)).card - 2 := by
          rw [hdisNext, Finset.card_sdiff, Finset.inter_eq_left.mpr hpairSubset,
            hpairCard]
        refine fuelInduction
          (fun index => flipTwoSign first second index * signsCurrent index)
          hnextSign ?_ ?_ hvanishNext
        · rw [hcardNext]
          omega
        · rw [hcardNext, Nat.even_sub (by omega)]
          exact iff_of_true heven (by decide)

/-! ## The lift: frames extend to special orthogonal squares in positive charts -/

/-- **THE LIFT, ORTHOGONAL ASSEMBLY.**  Every `size × rank` frame with
orthonormal columns is the first-`rank`-columns frame of a SPECIAL orthogonal
square matrix, provided `rank < size`: complete the columns
(`Gtz.exists_orthonormal_completion`), assemble by column blocks along
`finSumFinEquiv`, and if the determinant lands at `-1` flip one complement
column. -/
theorem exists_specialOrthogonal_frameOf (hrank : rank < size)
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hframe : frameᵀ * frame = 1) :
    ∃ square : Matrix (Fin size) (Fin size) ℝ,
      squareᵀ * square = 1 ∧ square.det = 1 ∧ frameOf hrank.le square = frame := by
  classical
  obtain ⟨complement, hcompGram, hcross, _⟩ := exists_orthonormal_completion frame hframe
  have hcrossT : complementᵀ * frame = 0 := by
    have htransposed := congrArg Matrix.transpose hcross
    rwa [transpose_mul, transpose_transpose, transpose_zero] at htransposed
  have hsplit : rank + (size - rank) = size := Nat.add_sub_cancel' hrank.le
  set colEquiv : Fin size ≃ Fin rank ⊕ Fin (size - rank) :=
    (finCongr hsplit.symm).trans finSumFinEquiv.symm with hcolEquiv
  set assembled : Matrix (Fin size) (Fin size) ℝ :=
    (frame.fromCols complement).submatrix id ⇑colEquiv with hassembled
  -- column Gram of the assembled square
  have hgram : assembledᵀ * assembled = 1 := by
    rw [hassembled, transpose_submatrix, Matrix.transpose_fromCols]
    have hmul := Matrix.submatrix_mul_equiv
      (Matrix.fromRows frameᵀ complementᵀ) (frame.fromCols complement)
      (⇑colEquiv) (Equiv.refl (Fin size)) (⇑colEquiv)
    simp only [Equiv.coe_refl] at hmul
    rw [show (Matrix.fromRows frameᵀ complementᵀ).submatrix (⇑colEquiv) id
        * (frame.fromCols complement).submatrix id (⇑colEquiv)
        = (Matrix.fromRows frameᵀ complementᵀ * frame.fromCols complement).submatrix
            (⇑colEquiv) (⇑colEquiv) from hmul]
    rw [Matrix.fromRows_mul_fromCols, hframe, hcross, hcrossT, hcompGram,
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  -- the frame recovery
  have hframeRecover : frameOf hrank.le assembled = frame := by
    have hcolLeft : ∀ colIndex : Fin rank,
        colEquiv (Fin.castLE hrank.le colIndex) = Sum.inl colIndex := by
      intro colIndex
      rw [hcolEquiv, Equiv.trans_apply, Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
      apply Fin.ext
      simp
    ext rowIndex colIndex
    rw [frameOf, Matrix.submatrix_apply, hassembled, Matrix.submatrix_apply, id_eq,
      hcolLeft colIndex, Matrix.fromCols_apply_inl]
    rfl
  -- determinant is a sign
  have hdetSquare : assembled.det * assembled.det = 1 := by
    have hdetGram := congrArg Matrix.det hgram
    rwa [det_mul, det_transpose, det_one] at hdetGram
  rcases mul_self_eq_one_iff.mp hdetSquare with hdetOne | hdetNeg
  · exact ⟨assembled, hgram, hdetOne, hframeRecover⟩
  · -- flip one complement column to repair the determinant
    set flipIndex : Fin size := ⟨rank, hrank⟩ with hflipIndex
    set flipSigns : Fin size → ℝ :=
      fun colIndex => if colIndex = flipIndex then -1 else 1 with hflipSigns
    have hflipIsSign : IsSignVector flipSigns := by
      intro index
      rw [hflipSigns]
      dsimp only
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    refine ⟨assembled * Matrix.diagonal flipSigns, ?_, ?_, ?_⟩
    · rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc assembledᵀ assembled (Matrix.diagonal flipSigns),
        hgram, Matrix.one_mul, hflipIsSign.diagonal_mul_self]
    · rw [det_mul, det_diagonal, hdetNeg]
      have hprodFlip : (∏ index, flipSigns index) = -1 := by
        rw [hflipSigns]
        rw [Finset.prod_ite_eq' Finset.univ flipIndex (fun _ => (-1 : ℝ))]
        simp
      rw [hprodFlip]
      norm_num
    · ext rowIndex colIndex
      rw [frameOf, Matrix.submatrix_apply, id_eq, Matrix.mul_diagonal]
      have hcolNe : Fin.castLE hrank.le colIndex ≠ flipIndex := by
        intro habs
        have hval := congrArg Fin.val habs
        rw [hflipIndex] at hval
        simp only [Fin.val_castLE] at hval
        omega
      rw [hflipSigns]
      dsimp only
      rw [if_neg hcolNe, mul_one]
      have hentry := congrArg (fun frameMatrix => frameMatrix rowIndex colIndex)
        hframeRecover
      simpa [frameOf, Matrix.submatrix_apply] using hentry

/-- **THE LIFT, CHART FORM (the consumable the capstone uses twice).**  Every
orthonormal frame is the sign-chart frame of a POSITIVE chart at some raw
square: lift to a special orthogonal square, place it in a positive chart (K3),
and read off the chart coordinates by exact membership. -/
theorem exists_signChartFrame_eq (hrank : rank < size)
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hframe : frameᵀ * frame = 1) :
    ∃ (signs : Fin size → ℝ) (raw : Fin size → Fin size → ℝ),
      IsSignVector signs ∧ (Matrix.diagonal signs).det = 1 ∧
      signChartFrame hrank.le signs raw = frame := by
  obtain ⟨square, hgram, hdetOne, hframeOf⟩ :=
    exists_specialOrthogonal_frameOf hrank frame hframe
  obtain ⟨signs, hsigns, hdetSigns, hchart⟩ := exists_positive_chart hgram hdetOne
  obtain ⟨memberSkew, hmemberSkew, hfactor⟩ :=
    exists_skew_of_det_sign_add_ne_zero hgram hsigns hchart
  refine ⟨signs, fun rowIndex colIndex => memberSkew rowIndex colIndex,
    hsigns, hdetSigns, ?_⟩
  unfold signChartFrame
  rw [skewOfRaw_entries_of_skew hmemberSkew, ← hfactor]
  exact hframeOf

/-! ## The star propagation theorem -/

/-- **THE STAR PROPAGATION THEOREM.**  A degeneracy polynomial whose chart
pullback vanishes on a NONEMPTY OPEN subset of ONE positive chart's parameter
space (with nonvanishing weight sum there) vanishes at EVERY orthonormal frame
with weights summing to one.  Route: the workhorse turns open vanishing into
full vanishing on the base chart; the two-flip chain reaches every positive
chart; the lift writes an arbitrary frame in one of them; normalization is the
identity on weights already summing to one.  Note the frame side needs NO
weight positivity — the design layer adds it separately. -/
theorem eval_frameParamsOf_eq_zero_of_eval_eq_zero_on_open (hrank : rank < size)
    (degeneracy : MvPolynomial (FrameParamIndex size rank) ℝ)
    {signs : Fin size → ℝ} (hsigns : IsSignVector signs)
    (hdetSigns : (Matrix.diagonal signs).det = 1)
    {vanishingSet : Set (ChartParamIndex size → ℝ)}
    (hopen : IsOpen vanishingSet) (hnonempty : vanishingSet.Nonempty)
    (hsum : ∀ params ∈ vanishingSet, chartWeightSum params ≠ 0)
    (hvanish : ∀ params ∈ vanishingSet,
      MvPolynomial.eval (signChartParams hrank.le signs params) degeneracy = 0)
    (frame : Matrix (Fin size) (Fin rank) ℝ) (weights : Fin size → ℝ)
    (hframe : frameᵀ * frame = 1) (hweights : (∑ atomIndex, weights atomIndex) = 1) :
    MvPolynomial.eval (frameParamsOf frame weights) degeneracy = 0 := by
  have hbaseVanishes : ChartVanishes hrank.le signs degeneracy :=
    chartVanishes_of_eval_eq_zero_on_open hrank.le signs degeneracy
      hopen hnonempty hsum hvanish
  obtain ⟨liftSigns, liftRaw, hliftSigns, hliftDet, hliftFrame⟩ :=
    exists_signChartFrame_eq hrank frame hframe
  have hliftVanishes : ChartVanishes hrank.le liftSigns degeneracy :=
    chartVanishes_of_det_diagonal_eq hrank.le hsigns hliftSigns
      (by rw [hdetSigns, hliftDet]) hbaseVanishes
  have hvalue := hliftVanishes liftRaw weights (by rw [hweights]; exact one_ne_zero)
  rwa [hliftFrame, normalizedWeights_of_sum_one hweights] at hvalue

/-! ## Continuity of the chart-to-frame-data map -/

/-- Each frame entry of the chart map is GLOBALLY continuous in the packed
chart parameters: it is a sign times a quotient of two polynomial evaluations
whose denominator — the Cayley denominator determinant — never vanishes (K1). -/
theorem continuous_signChartFrame_entry (hrank : rank ≤ size) (signs : Fin size → ℝ)
    (rowIndex : Fin size) (colIndex : Fin rank) :
    Continuous fun params : ChartParamIndex size → ℝ =>
      signChartFrame hrank signs (chartRawPart params) rowIndex colIndex := by
  have hentry : ∀ params : ChartParamIndex size → ℝ,
      signChartFrame hrank signs (chartRawPart params) rowIndex colIndex
        = signs rowIndex
          * (MvPolynomial.eval params
              ((cayleyNumeratorPoly size) rowIndex (Fin.castLE hrank colIndex))
            / MvPolynomial.eval params (cayleyDenominatorPoly size)) := by
    intro params
    have hdetNe : ((1 : Matrix (Fin size) (Fin size) ℝ)
        + skewOfRaw (chartRawPart params)).det ≠ 0 :=
      det_one_add_ne_zero_of_skew (transpose_skewOfRaw _)
    rw [eval_cayleyNumeratorPoly_entry, eval_cayleyDenominatorPoly,
      mul_div_cancel_left₀ _ hdetNe]
    unfold signChartFrame frameOf
    simp [Matrix.submatrix_apply, Matrix.diagonal_mul]
  simp only [hentry]
  exact continuous_const.mul (Continuous.div
    (MvPolynomial.continuous_eval _) (MvPolynomial.continuous_eval _)
    (fun params => by
      rw [eval_cayleyDenominatorPoly]
      exact det_one_add_ne_zero_of_skew (transpose_skewOfRaw _)))

/-- The nonvanishing-weight-sum domain is open. -/
theorem isOpen_chartWeightSum_ne_zero :
    IsOpen {params : ChartParamIndex size → ℝ | chartWeightSum params ≠ 0} :=
  isOpen_ne.preimage (by
    unfold chartWeightSum chartWeightPart
    exact continuous_finsetSum Finset.univ
      fun atomIndex _ => continuous_apply (Sum.inr atomIndex))

/-- **CONTINUITY OF THE CHART-TO-FRAME-DATA MAP** on the nonvanishing-weight-sum
domain: frame coordinates are globally continuous, weight coordinates are
quotients with nonvanishing denominator on the domain.  This is what pulls an
open set of frame data back to an open set of chart parameters. -/
theorem continuousOn_signChartParams (hrank : rank ≤ size) (signs : Fin size → ℝ) :
    ContinuousOn (signChartParams hrank signs)
      {params : ChartParamIndex size → ℝ | chartWeightSum params ≠ 0} := by
  rw [continuousOn_pi]
  intro coordIndex
  rcases coordIndex with ⟨rowIndex, colIndex⟩ | atomIndex
  · exact (continuous_signChartFrame_entry hrank signs rowIndex colIndex).continuousOn
  · have hnum : ContinuousOn (fun params : ChartParamIndex size → ℝ =>
        chartWeightPart params atomIndex)
        {params : ChartParamIndex size → ℝ | chartWeightSum params ≠ 0} :=
      (continuous_apply (Sum.inr atomIndex)).continuousOn
    have hden : ContinuousOn (fun params : ChartParamIndex size → ℝ =>
        chartWeightSum params)
        {params : ChartParamIndex size → ℝ | chartWeightSum params ≠ 0} := by
      refine Continuous.continuousOn ?_
      unfold chartWeightSum chartWeightPart
      exact continuous_finsetSum Finset.univ
        fun otherIndex _ => continuous_apply (Sum.inr otherIndex)
    exact ContinuousOn.div hnum hden fun params hparams => hparams

end Gtz

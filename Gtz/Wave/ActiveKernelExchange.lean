import Gtz.Quantitative.ChartArgmaxIndexFloorTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- The quadratic form of a symmetric `4 x 4` matrix, with the ten upper-triangular
entries written explicitly.  This scalar packaging keeps the exchange calculation
independent of finite-index bookkeeping. -/
def symmetricFourForm
    (a b c d e f g h i j x0 x1 x2 x3 : ℝ) : ℝ :=
  a * x0 ^ 2 + 2 * b * x0 * x1 + 2 * c * x0 * x2 + 2 * d * x0 * x3
    + e * x1 ^ 2 + 2 * f * x1 * x2 + 2 * g * x1 * x3
    + h * x2 ^ 2 + 2 * i * x2 * x3 + j * x3 ^ 2

/-- The principal form on coordinates `0,1,3`. -/
def symmetricZeroOneThreeForm
    (a b d e g j x0 x1 x3 : ℝ) : ℝ :=
  a * x0 ^ 2 + 2 * b * x0 * x1 + 2 * d * x0 * x3
    + e * x1 ^ 2 + 2 * g * x1 * x3 + j * x3 ^ 2

/-- **THE DUPLICATE-COLUMN QUADRATIC IDENTITY.**

If `(0,u,v,0)` is killed by a symmetric four-coordinate form, then after clearing
the nonzero coordinate `v`, the full quadratic form is exactly the principal
`{0,1,3}` form with coordinate `1` replaced by `v*x1-u*x2`.  This is the algebraic
heart of the active-kernel exchange: coordinate `2` is a duplicate of coordinate
`1`, so adjoining it cannot destroy positive semidefiniteness. -/
theorem sq_mul_symmetricFourForm_eq_symmetricZeroOneThreeForm
    {a b c d e f g h i j u v x0 x1 x2 x3 : ℝ}
    (hzero : b * u + c * v = 0)
    (hone : e * u + f * v = 0)
    (htwo : f * u + h * v = 0)
    (hthree : g * u + i * v = 0) :
    v ^ 2 * symmetricFourForm a b c d e f g h i j x0 x1 x2 x3
      = symmetricZeroOneThreeForm a b d e g j
          (v * x0) (v * x1 - u * x2) (v * x3) := by
  unfold symmetricFourForm symmetricZeroOneThreeForm
  linear_combination
    (2 * v * x0 * x2) * hzero
      + (2 * v * x1 * x2 - u * x2 ^ 2) * hone
      + (v * x2 ^ 2) * htwo
      + (2 * v * x2 * x3) * hthree

/-- A positive-semidefinite principal block stays positive semidefinite after adjoining
a coordinate which is forced to duplicate one of its columns by a nonzero two-supported
kernel vector. -/
theorem symmetricFourForm_nonneg_of_duplicateColumn
    {a b c d e f g h i j u v : ℝ}
    (hv : v ≠ 0)
    (hzero : b * u + c * v = 0)
    (hone : e * u + f * v = 0)
    (htwo : f * u + h * v = 0)
    (hthree : g * u + i * v = 0)
    (hprincipal : ∀ x0 x1 x3 : ℝ,
      0 ≤ symmetricZeroOneThreeForm a b d e g j x0 x1 x3) :
    ∀ x0 x1 x2 x3 : ℝ,
      0 ≤ symmetricFourForm a b c d e f g h i j x0 x1 x2 x3 := by
  intro x0 x1 x2 x3
  have hscaled : 0 ≤ v ^ 2
      * symmetricFourForm a b c d e f g h i j x0 x1 x2 x3 := by
    rw [sq_mul_symmetricFourForm_eq_symmetricZeroOneThreeForm
      hzero hone htwo hthree]
    exact hprincipal (v * x0) (v * x1 - u * x2) (v * x3)
  rw [mul_comm] at hscaled
  exact nonneg_of_mul_nonneg_left hscaled (sq_pos_of_ne_zero hv)

/-- Entrywise expansion of a symmetric real `4 x 4` quadratic form. -/
theorem dotProduct_mulVec_fin_four_eq_symmetricFourForm
    (form : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : Matrix.transpose form = form)
    (x : Fin 4 → ℝ) :
    x ⬝ᵥ (form *ᵥ x) =
      symmetricFourForm
        (form 0 0) (form 0 1) (form 0 2) (form 0 3)
        (form 1 1) (form 1 2) (form 1 3)
        (form 2 2) (form 2 3) (form 3 3)
        (x 0) (x 1) (x 2) (x 3) := by
  have h10 : form 1 0 = form 0 1 := by
    have hentry := congrFun (congrFun hsymm (0 : Fin 4)) (1 : Fin 4)
    simpa using hentry
  have h20 : form 2 0 = form 0 2 := by
    have hentry := congrFun (congrFun hsymm (0 : Fin 4)) (2 : Fin 4)
    simpa using hentry
  have h30 : form 3 0 = form 0 3 := by
    have hentry := congrFun (congrFun hsymm (0 : Fin 4)) (3 : Fin 4)
    simpa using hentry
  have h21 : form 2 1 = form 1 2 := by
    have hentry := congrFun (congrFun hsymm (1 : Fin 4)) (2 : Fin 4)
    simpa using hentry
  have h31 : form 3 1 = form 1 3 := by
    have hentry := congrFun (congrFun hsymm (1 : Fin 4)) (3 : Fin 4)
    simpa using hentry
  have h32 : form 3 2 = form 2 3 := by
    have hentry := congrFun (congrFun hsymm (2 : Fin 4)) (3 : Fin 4)
    simpa using hentry
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  rw [h10, h20, h30, h21, h31, h32]
  unfold symmetricFourForm
  ring

/-- **MATRIX DUPLICATE-COLUMN EXCHANGE.**  If a symmetric `4 x 4` matrix kills a
vector supported exactly in coordinates `1,2`, then PSD of its principal block on
`{0,1,3}` forces PSD of the whole matrix.  In the crux application the killed vector
is the aligned exchange of two active tight directions. -/
theorem posSemidef_fin_four_of_pairKernel_of_zeroOneThree
    (form : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : Matrix.transpose form = form)
    {u v : ℝ} (hv : v ≠ 0)
    (hkernel : form *ᵥ (![0, u, v, 0] : Fin 4 → ℝ) = 0)
    (hprincipal :
      (form.submatrix (![0, 1, 3] : Fin 3 → Fin 4)
        (![0, 1, 3] : Fin 3 → Fin 4)).PosSemidef) :
    form.PosSemidef := by
  have hzero := congrFun hkernel (0 : Fin 4)
  have hone := congrFun hkernel (1 : Fin 4)
  have htwo := congrFun hkernel (2 : Fin 4)
  have hthree := congrFun hkernel (3 : Fin 4)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hzero hone htwo hthree
  have h10 : form 1 0 = form 0 1 := by
    have hentry := congrFun (congrFun hsymm (0 : Fin 4)) (1 : Fin 4)
    simpa using hentry
  have h21 : form 2 1 = form 1 2 := by
    have hentry := congrFun (congrFun hsymm (1 : Fin 4)) (2 : Fin 4)
    simpa using hentry
  have h31 : form 3 1 = form 1 3 := by
    have hentry := congrFun (congrFun hsymm (1 : Fin 4)) (3 : Fin 4)
    simpa using hentry
  have h32 : form 3 2 = form 2 3 := by
    have hentry := congrFun (congrFun hsymm (2 : Fin 4)) (3 : Fin 4)
    simpa using hentry
  rw [h21] at htwo
  rw [h31, h32] at hthree
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_of_transpose_eq hsymm) ?_
  intro x
  rw [star_trivial, dotProduct_mulVec_fin_four_eq_symmetricFourForm form hsymm]
  apply symmetricFourForm_nonneg_of_duplicateColumn hv hzero hone htwo hthree
  intro x0 x1 x3
  have hnonneg := hprincipal.dotProduct_mulVec_nonneg
    (![x0, x1, x3] : Fin 3 → ℝ)
  rw [star_trivial] at hnonneg
  have h30 : form 3 0 = form 0 3 := by
    have hentry := congrFun (congrFun hsymm (0 : Fin 4)) (3 : Fin 4)
    simpa using hentry
  simp [dotProduct, Matrix.mulVec, Matrix.submatrix_apply,
    Fin.sum_univ_three] at hnonneg
  rw [h10, h30, h31] at hnonneg
  unfold symmetricZeroOneThreeForm
  nlinarith

/-- Two aligned active kernel vectors and a selected pair kernel weld into a global
kernel on their four-coordinate union.  The two active blocks supply coordinates
`0,3`; the selected block supplies coordinates `1,2`. -/
theorem exchangedPair_globalKernel_fin_four
    (form : Matrix (Fin 4) (Fin 4) ℝ)
    (left right pair : Fin 4 → ℝ) (scale : ℝ)
    (hpair : pair = right - scale • left)
    (hleftZero : (form *ᵥ left) 0 = 0)
    (hleftThree : (form *ᵥ left) 3 = 0)
    (hrightZero : (form *ᵥ right) 0 = 0)
    (hrightThree : (form *ᵥ right) 3 = 0)
    (hpairOne : (form *ᵥ pair) 1 = 0)
    (hpairTwo : (form *ᵥ pair) 2 = 0) :
    form *ᵥ pair = 0 := by
  funext coordinate
  fin_cases coordinate
  · rw [hpair, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change (form *ᵥ right) 0 - scale * (form *ᵥ left) 0 = 0
    rw [hrightZero, hleftZero]
    ring
  · exact hpairOne
  · exact hpairTwo
  · rw [hpair, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change (form *ᵥ right) 3 - scale * (form *ᵥ left) 3 = 0
    rw [hrightThree, hleftThree]
    ring

/-- **ALIGNED ACTIVE-KERNEL EXCHANGE.**  This is the directly consumable canonical
four-label statement.  If the exchanged vector of two active directions is a genuine
pair-supported kernel of the selected block, then the full four-label shifted gap is
PSD.  Every principal triple in that four-set therefore has value at least the active
value, so an argmax family which omitted one of them was not the full argmax family. -/
theorem posSemidef_fin_four_of_aligned_active_exchange
    (form : Matrix (Fin 4) (Fin 4) ℝ) (hsymm : Matrix.transpose form = form)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (form *ᵥ left) 0 = 0)
    (hleftThree : (form *ᵥ left) 3 = 0)
    (hrightZero : (form *ᵥ right) 0 = 0)
    (hrightThree : (form *ᵥ right) 3 = 0)
    (hpairOne : (form *ᵥ pair) 1 = 0)
    (hpairTwo : (form *ᵥ pair) 2 = 0)
    (hprincipal :
      (form.submatrix (![0, 1, 3] : Fin 3 → Fin 4)
        (![0, 1, 3] : Fin 3 → Fin 4)).PosSemidef) :
    form.PosSemidef := by
  have hglobal := exchangedPair_globalKernel_fin_four form left right pair scale
    hpair hleftZero hleftThree hrightZero hrightThree hpairOne hpairTwo
  rw [hpairShape] at hglobal
  exact posSemidef_fin_four_of_pairKernel_of_zeroOneThree form hsymm hv hglobal hprincipal

/-- Two vectors killed by the same row of a `2 x 2` block with nonzero diagonal are
proportional.  This is the tiny rigidity which makes the diamond exchange unconditional:
the selected pair kernel and the aligned residual exchange cannot be independent. -/
theorem pairKernel_minor_eq_zero_of_posDiagonal
    {diagonal cross x y u v : ℝ}
    (hdiagonal : 0 < diagonal)
    (hfirst : diagonal * x + cross * y = 0)
    (hsecond : diagonal * u + cross * v = 0) :
    x * v = y * u := by
  have hidentity : diagonal * (x * v - y * u) = 0 := by
    calc
      diagonal * (x * v - y * u)
          = (diagonal * x + cross * y) * v
              - (diagonal * u + cross * v) * y := by ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hidentity).resolve_left (ne_of_gt hdiagonal))

/-- Explicit proportionality form of `pairKernel_minor_eq_zero_of_posDiagonal`. -/
theorem pairKernel_eq_smul_of_posDiagonal
    {diagonal cross x y u v : ℝ}
    (hdiagonal : 0 < diagonal) (hx : x ≠ 0)
    (hfirst : diagonal * x + cross * y = 0)
    (hsecond : diagonal * u + cross * v = 0) :
    (![u, v] : Fin 2 → ℝ) = (u / x) • (![x, y] : Fin 2 → ℝ) := by
  have hminor := pairKernel_minor_eq_zero_of_posDiagonal hdiagonal hfirst hsecond
  funext coordinate
  fin_cases coordinate
  · simp [hx]
  · change v = u / x * y
    field_simp
    nlinarith [hminor]

/-! ## Chart-level consumption -/

/-- Restrict an ambient chart-tight direction to an injective four-coordinate window.
At every selected coordinate the shifted local window kills the local vector. -/
theorem shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection
    {size : ℕ} (point : ChartPoint size 3)
    (fourPick : Fin 4 → Fin size) (hfourPick : Function.Injective fourPick)
    (selected : Finset (Fin size))
    (ambientVec : Fin size → ℝ) (localVec : Fin 4 → ℝ)
    (hspread : ambientVec = selectionInjection fourPick *ᵥ localVec)
    (htight : IsChartTightDirection point.chart point.weight
      (chartObjective point) selected ambientVec)
    (localIndex : Fin 4) (hmem : fourPick localIndex ∈ selected) :
    (((chartPointGap point).submatrix fourPick fourPick
        - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ localVec)
      localIndex = 0 := by
  have htightAt := htight.isTight (fourPick localIndex) hmem
  have hzero :
      ((chartStationaryGap point.chart point.weight
        - chartObjective point • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ ambientVec)
          (fourPick localIndex) = 0 := by
    rw [Matrix.sub_mulVec, Pi.sub_apply, htightAt, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, sub_self]
  change (((chartPointGap point
      - chartObjective point • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ ambientVec)
        (fourPick localIndex) = 0) at hzero
  rw [hspread] at hzero
  have hread := mulVec_selectionInjection_apply
    (chartPointGap point
      - chartObjective point • (1 : Matrix (Fin size) (Fin size) ℝ))
    fourPick localVec localIndex
  rw [Matrix.submatrix_sub, Matrix.submatrix_smul] at hread
  change (((chartPointGap point
      - chartObjective point • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ
        (selectionInjection fourPick *ᵥ localVec)) (fourPick localIndex)
    = (((chartPointGap point).submatrix fourPick fourPick
        - chartObjective point •
          (1 : Matrix (Fin size) (Fin size) ℝ).submatrix fourPick fourPick) *ᵥ localVec)
      localIndex) at hread
  rw [Matrix.submatrix_one _ hfourPick] at hread
  rw [hread] at hzero
  exact hzero

/-- A PSD shifted four-coordinate block forces any injectively selected principal
`rank`-subblock into the chart argmax family.  The only bookkeeping hypothesis identifies
the selected finset's canonical order embedding with the requested coordinates of the
four-block. -/
theorem mem_chartArgmaxFamily_of_shiftedFourBlock_posSemidef
    {size rank : ℕ} [Nonempty (Fin rank)]
    (point : ChartPoint size rank)
    (fourPick : Fin 4 → Fin size) (triplePick : Fin rank → Fin 4)
    (htripleInjective : Function.Injective triplePick)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hpick : selected.orderEmbOfFin hcard = fourPick ∘ triplePick)
    (hfull : ((chartPointGap point).submatrix fourPick fourPick
        - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)).PosSemidef) :
    selected ∈ chartArgmaxFamily point := by
  apply (mem_chartArgmaxFamily_iff point selected).mpr
  refine ⟨hcard, ?_⟩
  rw [chartBlockValue, dif_pos hcard, chartGapRaw_chartConfig]
  apply (le_lambdaMinMat_iff_posSemidef_sub_smul_one _ ?_
    (chartObjective point)).mpr
  · have hsub := hfull.submatrix triplePick
    rw [Matrix.submatrix_sub] at hsub
    change (((chartPointGap point).submatrix fourPick fourPick).submatrix
        triplePick triplePick
      - (chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)).submatrix
          triplePick triplePick).PosSemidef at hsub
    rw [Matrix.submatrix_submatrix, Matrix.submatrix_smul] at hsub
    change ((chartPointGap point).submatrix (fourPick ∘ triplePick)
        (fourPick ∘ triplePick)
      - chartObjective point •
          (1 : Matrix (Fin 4) (Fin 4) ℝ).submatrix triplePick triplePick).PosSemidef at hsub
    rw [Matrix.submatrix_one _ htripleInjective] at hsub
    rw [← hpick] at hsub
    exact hsub
  · rw [Matrix.transpose_submatrix, chartPointGap_transpose]

/-- Conversely, an active triple supplies the PSD principal shifted block required by
the four-coordinate exchange theorem. -/
theorem shiftedFourBlock_submatrix_posSemidef_of_mem_chartArgmaxFamily
    {size rank : ℕ} [Nonempty (Fin rank)]
    (point : ChartPoint size rank)
    (fourPick : Fin 4 → Fin size) (triplePick : Fin rank → Fin 4)
    (htripleInjective : Function.Injective triplePick)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (hpick : selected.orderEmbOfFin hcard = fourPick ∘ triplePick)
    (hactive : selected ∈ chartArgmaxFamily point) :
    (((chartPointGap point).submatrix fourPick fourPick
        - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)).submatrix
      triplePick triplePick).PosSemidef := by
  have hbound := ((mem_chartArgmaxFamily_iff point selected).mp hactive).2
  rw [chartBlockValue, dif_pos hcard, chartGapRaw_chartConfig] at hbound
  have hpsd := (le_lambdaMinMat_iff_posSemidef_sub_smul_one _
    (by rw [Matrix.transpose_submatrix, chartPointGap_transpose])
    (chartObjective point)).mp hbound
  rw [Matrix.submatrix_sub]
  change (((chartPointGap point).submatrix fourPick fourPick).submatrix
      triplePick triplePick
    - (chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)).submatrix
        triplePick triplePick).PosSemidef
  rw [Matrix.submatrix_submatrix, Matrix.submatrix_smul]
  change ((chartPointGap point).submatrix (fourPick ∘ triplePick)
      (fourPick ∘ triplePick)
    - chartObjective point •
        (1 : Matrix (Fin 4) (Fin 4) ℝ).submatrix triplePick triplePick).PosSemidef
  rw [Matrix.submatrix_one _ htripleInjective, ← hpick]
  exact hpsd

/-- Permutation-aware form of
`shiftedFourBlock_submatrix_posSemidef_of_mem_chartArgmaxFamily`.  The local
coordinates of the principal triple need not be the canonical increasing order of
the selected finset: an injective reordering transports the active PSD block. -/
theorem shiftedFourBlock_submatrix_posSemidef_of_mem_chartArgmaxFamily_reordered
    {size rank : ℕ} [Nonempty (Fin rank)]
    (point : ChartPoint size rank)
    (fourPick : Fin 4 → Fin size) (triplePick : Fin rank → Fin 4)
    (htripleInjective : Function.Injective triplePick)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (reorder : Fin rank → Fin rank)
    (hreorderInjective : Function.Injective reorder)
    (hpick : fourPick ∘ triplePick
      = selected.orderEmbOfFin hcard ∘ reorder)
    (hactive : selected ∈ chartArgmaxFamily point) :
    (((chartPointGap point).submatrix fourPick fourPick
        - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)).submatrix
      triplePick triplePick).PosSemidef := by
  have hbound := ((mem_chartArgmaxFamily_iff point selected).mp hactive).2
  rw [chartBlockValue, dif_pos hcard, chartGapRaw_chartConfig] at hbound
  have hpsd := (le_lambdaMinMat_iff_posSemidef_sub_smul_one _
    (by rw [Matrix.transpose_submatrix, chartPointGap_transpose])
    (chartObjective point)).mp hbound
  have hsub := hpsd.submatrix reorder
  rw [Matrix.submatrix_sub] at hsub
  change ((((chartPointGap point).submatrix
      (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)).submatrix
        reorder reorder
      - (chartObjective point • (1 : Matrix (Fin rank) (Fin rank) ℝ)).submatrix
        reorder reorder).PosSemidef) at hsub
  rw [Matrix.submatrix_submatrix, Matrix.submatrix_smul] at hsub
  change (((chartPointGap point).submatrix
      (selected.orderEmbOfFin hcard ∘ reorder)
      (selected.orderEmbOfFin hcard ∘ reorder)
    - chartObjective point •
        (1 : Matrix (Fin rank) (Fin rank) ℝ).submatrix reorder reorder).PosSemidef) at hsub
  rw [Matrix.submatrix_one _ hreorderInjective] at hsub
  rw [Matrix.submatrix_sub]
  change ((((chartPointGap point).submatrix fourPick fourPick).submatrix
      triplePick triplePick
    - (chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)).submatrix
      triplePick triplePick).PosSemidef)
  rw [Matrix.submatrix_submatrix, Matrix.submatrix_smul]
  change (((chartPointGap point).submatrix (fourPick ∘ triplePick)
      (fourPick ∘ triplePick)
    - chartObjective point •
        (1 : Matrix (Fin 4) (Fin 4) ℝ).submatrix triplePick triplePick).PosSemidef)
  rw [Matrix.submatrix_one _ htripleInjective]
  rw [hpick]
  exact hsub

/-- Permutation-aware aligned exchange.  Once the active principal triple gives the
PSD local block, the duplicate-column argument makes the whole four-window PSD; hence
*any* injectively picked triple in that window, not just the other aligned input, is
active. -/
theorem mem_chartArgmaxFamily_of_aligned_active_exchange_reordered
    {size : ℕ} (point : ChartPoint size 3) (fourPick : Fin 4 → Fin size)
    (principal exchanged : Finset (Fin size))
    (hprincipalCard : principal.card = 3) (hexchangedCard : exchanged.card = 3)
    (reorder : Fin 3 → Fin 3) (hreorderInjective : Function.Injective reorder)
    (hprincipalPick : fourPick ∘ (![0, 1, 3] : Fin 3 → Fin 4)
      = principal.orderEmbOfFin hprincipalCard ∘ reorder)
    (exchangedPick : Fin 3 → Fin 4)
    (hexchangedPickInjective : Function.Injective exchangedPick)
    (hexchangedPick : exchanged.orderEmbOfFin hexchangedCard
      = fourPick ∘ exchangedPick)
    (hprincipalActive : principal ∈ chartArgmaxFamily point)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ left) 0 = 0)
    (hleftThree : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ left) 3 = 0)
    (hrightZero : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ right) 0 = 0)
    (hrightThree : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ right) 3 = 0)
    (hpairOne : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ pair) 1 = 0)
    (hpairTwo : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ pair) 2 = 0) :
    exchanged ∈ chartArgmaxFamily point := by
  let form : Matrix (Fin 4) (Fin 4) ℝ :=
    (chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)
  have hformSymmetric : formᵀ = form := by
    dsimp only [form]
    rw [Matrix.transpose_sub, Matrix.transpose_submatrix, chartPointGap_transpose,
      Matrix.transpose_smul, Matrix.transpose_one]
  have hprincipalPsd :
      (form.submatrix (![0, 1, 3] : Fin 3 → Fin 4)
        (![0, 1, 3] : Fin 3 → Fin 4)).PosSemidef := by
    dsimp only [form]
    exact shiftedFourBlock_submatrix_posSemidef_of_mem_chartArgmaxFamily_reordered
      point fourPick (![0, 1, 3] : Fin 3 → Fin 4) (by decide)
      principal hprincipalCard reorder hreorderInjective hprincipalPick
      hprincipalActive
  have hfull : form.PosSemidef :=
    posSemidef_fin_four_of_aligned_active_exchange form hformSymmetric left right pair
      scale u v hpair hpairShape hv hleftZero hleftThree hrightZero hrightThree
      hpairOne hpairTwo hprincipalPsd
  exact mem_chartArgmaxFamily_of_shiftedFourBlock_posSemidef point fourPick
    exchangedPick hexchangedPickInjective exchanged hexchangedCard hexchangedPick hfull

/-- **CHART-LEVEL ALIGNED ACTIVE-KERNEL EXCHANGE.**  On a four-coordinate window,
the active principal triple supplies the PSD input to
`posSemidef_fin_four_of_aligned_active_exchange`.  The resulting full shifted window is
PSD, so the exchanged triple also attains the chart objective and belongs to the argmax
family. -/
theorem mem_chartArgmaxFamily_of_aligned_active_exchange
    {size : ℕ} (point : ChartPoint size 3) (fourPick : Fin 4 → Fin size)
    (principal exchanged : Finset (Fin size))
    (hprincipalCard : principal.card = 3) (hexchangedCard : exchanged.card = 3)
    (hprincipalPick : principal.orderEmbOfFin hprincipalCard
      = fourPick ∘ (![0, 1, 3] : Fin 3 → Fin 4))
    (hexchangedPick : exchanged.orderEmbOfFin hexchangedCard
      = fourPick ∘ (![0, 2, 3] : Fin 3 → Fin 4))
    (hprincipalActive : principal ∈ chartArgmaxFamily point)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ left) 0 = 0)
    (hleftThree : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ left) 3 = 0)
    (hrightZero : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ right) 0 = 0)
    (hrightThree : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ right) 3 = 0)
    (hpairOne : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ pair) 1 = 0)
    (hpairTwo : (((chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ pair) 2 = 0) :
    exchanged ∈ chartArgmaxFamily point := by
  let form : Matrix (Fin 4) (Fin 4) ℝ :=
    (chartPointGap point).submatrix fourPick fourPick
      - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)
  have hformSymmetric : formᵀ = form := by
    dsimp only [form]
    rw [Matrix.transpose_sub, Matrix.transpose_submatrix, chartPointGap_transpose,
      Matrix.transpose_smul, Matrix.transpose_one]
  have hprincipalPsd :
      (form.submatrix (![0, 1, 3] : Fin 3 → Fin 4)
        (![0, 1, 3] : Fin 3 → Fin 4)).PosSemidef := by
    dsimp only [form]
    exact shiftedFourBlock_submatrix_posSemidef_of_mem_chartArgmaxFamily point fourPick
      (![0, 1, 3] : Fin 3 → Fin 4) (by decide) principal hprincipalCard
      hprincipalPick hprincipalActive
  have hfull : form.PosSemidef :=
    posSemidef_fin_four_of_aligned_active_exchange form hformSymmetric left right pair
      scale u v hpair hpairShape hv hleftZero hleftThree hrightZero hrightThree
      hpairOne hpairTwo hprincipalPsd
  exact mem_chartArgmaxFamily_of_shiftedFourBlock_posSemidef point fourPick
    (![0, 2, 3] : Fin 3 → Fin 4) (by decide) exchanged hexchangedCard
    hexchangedPick hfull

/-! ### Fixed-label canonical window -/

/-- The first four labels of `Fin 6`, in increasing order. -/
def chartFirstFourPickSix : Fin 4 → Fin 6 := ![0, 1, 2, 3]

/-- The canonical active principal triple in the first-four window. -/
def chartZeroOneThree : Finset (Fin 6) := {0, 1, 3}

/-- Its one-slot exchange, replacing label `1` by label `2`. -/
def chartZeroTwoThree : Finset (Fin 6) := {0, 2, 3}

theorem chartZeroOneThree_card : chartZeroOneThree.card = 3 := by decide

theorem chartZeroTwoThree_card : chartZeroTwoThree.card = 3 := by decide

theorem chartZeroOneThree_orderEmb :
    chartZeroOneThree.orderEmbOfFin chartZeroOneThree_card
      = chartFirstFourPickSix ∘ (![0, 1, 3] : Fin 3 → Fin 4) := by
  have hordered : chartZeroOneThree.orderEmbOfFin chartZeroOneThree_card
      = (![0, 1, 3] : Fin 3 → Fin 6) := by
    symm
    apply Finset.orderEmbOfFin_unique chartZeroOneThree_card
    · intro index
      fin_cases index <;> simp [chartZeroOneThree]
    · intro first second hlt
      fin_cases first <;> fin_cases second <;> simp_all
  rw [hordered]
  funext index
  fin_cases index <;> rfl

theorem chartZeroTwoThree_orderEmb :
    chartZeroTwoThree.orderEmbOfFin chartZeroTwoThree_card
      = chartFirstFourPickSix ∘ (![0, 2, 3] : Fin 3 → Fin 4) := by
  have hordered : chartZeroTwoThree.orderEmbOfFin chartZeroTwoThree_card
      = (![0, 2, 3] : Fin 3 → Fin 6) := by
    symm
    apply Finset.orderEmbOfFin_unique chartZeroTwoThree_card
    · intro index
      fin_cases index <;> simp [chartZeroTwoThree]
    · intro first second hlt
      fin_cases first <;> fin_cases second <;> simp_all
  rw [hordered]
  funext index
  fin_cases index <;> rfl

/-- The shifted gap on the canonical first-four window. -/
noncomputable def chartFirstFourShiftedGap (point : ChartPoint 6 3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (chartPointGap point).submatrix chartFirstFourPickSix chartFirstFourPickSix
    - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Fixed-label form of the chart exchange bridge.  In particular, a purported
four-member argmax family containing the aligned inputs but omitting `{0,2,3}` is
contradictory. -/
theorem chartZeroTwoThree_mem_of_aligned_active_exchange
    (point : ChartPoint 6 3)
    (hprincipalActive : chartZeroOneThree ∈ chartArgmaxFamily point)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (chartFirstFourShiftedGap point *ᵥ left) 0 = 0)
    (hleftThree : (chartFirstFourShiftedGap point *ᵥ left) 3 = 0)
    (hrightZero : (chartFirstFourShiftedGap point *ᵥ right) 0 = 0)
    (hrightThree : (chartFirstFourShiftedGap point *ᵥ right) 3 = 0)
    (hpairOne : (chartFirstFourShiftedGap point *ᵥ pair) 1 = 0)
    (hpairTwo : (chartFirstFourShiftedGap point *ᵥ pair) 2 = 0) :
    chartZeroTwoThree ∈ chartArgmaxFamily point := by
  exact mem_chartArgmaxFamily_of_aligned_active_exchange point chartFirstFourPickSix
    chartZeroOneThree chartZeroTwoThree chartZeroOneThree_card chartZeroTwoThree_card
    chartZeroOneThree_orderEmb chartZeroTwoThree_orderEmb hprincipalActive
    left right pair scale u v hpair hpairShape hv hleftZero hleftThree hrightZero
    hrightThree hpairOne hpairTwo

/-! ### Canonical four-active orbit `{012,013,045,234}` -/

def chartZeroOneTwo : Finset (Fin 6) := {0, 1, 2}

def chartZeroFourFive : Finset (Fin 6) := {0, 4, 5}

def chartTwoThreeFour : Finset (Fin 6) := {2, 3, 4}

/-- The canonical four-active family used by orbit 11 of the exact census. -/
def chartOrbitElevenFamily : Finset (Finset (Fin 6)) :=
  {chartZeroOneTwo, chartZeroOneThree, chartZeroFourFive, chartTwoThreeFour}

/-- Local order `[0,2,3,1]`: middle coordinates are the exchanged pair `2,3`, and
the endpoint coordinates are the shared labels `0,1` of the aligned active blocks
`012,013`. -/
def chartOrbitElevenPickSix : Fin 4 → Fin 6 := ![0, 2, 3, 1]

/-- The local principal order `[0,2,1]` is the canonical order of `012` with its
last two coordinates swapped. -/
def chartOrbitElevenPrincipalReorder : Fin 3 → Fin 3 := ![0, 2, 1]

theorem chartZeroOneTwo_card : chartZeroOneTwo.card = 3 := by decide

theorem chartZeroOneTwo_orderEmb :
    chartZeroOneTwo.orderEmbOfFin chartZeroOneTwo_card
      = (![0, 1, 2] : Fin 3 → Fin 6) := by
  symm
  apply Finset.orderEmbOfFin_unique chartZeroOneTwo_card
  · intro index
    fin_cases index <;> simp [chartZeroOneTwo]
  · intro first second hlt
    fin_cases first <;> fin_cases second <;> simp_all

theorem chartOrbitEleven_principalPick :
    chartOrbitElevenPickSix ∘ (![0, 1, 3] : Fin 3 → Fin 4)
      = chartZeroOneTwo.orderEmbOfFin chartZeroOneTwo_card
        ∘ chartOrbitElevenPrincipalReorder := by
  rw [chartZeroOneTwo_orderEmb]
  funext index
  fin_cases index <;> rfl

theorem chartOrbitEleven_omittedPick :
    chartZeroTwoThree.orderEmbOfFin chartZeroTwoThree_card
      = chartOrbitElevenPickSix ∘ (![0, 1, 2] : Fin 3 → Fin 4) := by
  have hordered : chartZeroTwoThree.orderEmbOfFin chartZeroTwoThree_card
      = (![0, 2, 3] : Fin 3 → Fin 6) := by
    symm
    apply Finset.orderEmbOfFin_unique chartZeroTwoThree_card
    · intro index
      fin_cases index <;> simp [chartZeroTwoThree]
    · intro first second hlt
      fin_cases first <;> fin_cases second <;> simp_all
  rw [hordered]
  funext index
  fin_cases index <;> rfl

theorem chartZeroOneTwo_mem_chartOrbitElevenFamily :
    chartZeroOneTwo ∈ chartOrbitElevenFamily := by
  simp [chartOrbitElevenFamily]

theorem chartZeroTwoThree_not_mem_chartOrbitElevenFamily :
    chartZeroTwoThree ∉ chartOrbitElevenFamily := by
  decide

noncomputable def chartOrbitElevenShiftedGap (point : ChartPoint 6 3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (chartPointGap point).submatrix chartOrbitElevenPickSix chartOrbitElevenPickSix
    - chartObjective point • (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- In the canonical orbit-11 coordinates, the aligned duplicate-column exchange
forces the omitted triple `023` into the exact chart argmax family. -/
theorem chartOrbitEleven_omitted_mem_of_aligned_active_exchange
    (point : ChartPoint 6 3)
    (hfamily : chartArgmaxFamily point = chartOrbitElevenFamily)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (chartOrbitElevenShiftedGap point *ᵥ left) 0 = 0)
    (hleftThree : (chartOrbitElevenShiftedGap point *ᵥ left) 3 = 0)
    (hrightZero : (chartOrbitElevenShiftedGap point *ᵥ right) 0 = 0)
    (hrightThree : (chartOrbitElevenShiftedGap point *ᵥ right) 3 = 0)
    (hpairOne : (chartOrbitElevenShiftedGap point *ᵥ pair) 1 = 0)
    (hpairTwo : (chartOrbitElevenShiftedGap point *ᵥ pair) 2 = 0) :
    chartZeroTwoThree ∈ chartArgmaxFamily point := by
  have hprincipalActive : chartZeroOneTwo ∈ chartArgmaxFamily point := by
    rw [hfamily]
    exact chartZeroOneTwo_mem_chartOrbitElevenFamily
  exact mem_chartArgmaxFamily_of_aligned_active_exchange_reordered point
    chartOrbitElevenPickSix chartZeroOneTwo chartZeroTwoThree
    chartZeroOneTwo_card chartZeroTwoThree_card chartOrbitElevenPrincipalReorder
    (by decide) chartOrbitEleven_principalPick (![0, 1, 2] : Fin 3 → Fin 4)
    (by decide) chartOrbitEleven_omittedPick hprincipalActive
    left right pair scale u v hpair hpairShape hv hleftZero hleftThree hrightZero
    hrightThree hpairOne hpairTwo

/-- Therefore the canonical four-active orbit cannot be the complete argmax family
when the aligned exchange hypotheses hold. -/
theorem false_of_chartArgmaxFamily_eq_orbitEleven_of_aligned_active_exchange
    (point : ChartPoint 6 3)
    (hfamily : chartArgmaxFamily point = chartOrbitElevenFamily)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (chartOrbitElevenShiftedGap point *ᵥ left) 0 = 0)
    (hleftThree : (chartOrbitElevenShiftedGap point *ᵥ left) 3 = 0)
    (hrightZero : (chartOrbitElevenShiftedGap point *ᵥ right) 0 = 0)
    (hrightThree : (chartOrbitElevenShiftedGap point *ᵥ right) 3 = 0)
    (hpairOne : (chartOrbitElevenShiftedGap point *ᵥ pair) 1 = 0)
    (hpairTwo : (chartOrbitElevenShiftedGap point *ᵥ pair) 2 = 0) : False := by
  have homitted := chartOrbitEleven_omitted_mem_of_aligned_active_exchange point
    hfamily left right pair scale u v hpair hpairShape hv hleftZero hleftThree
    hrightZero hrightThree hpairOne hpairTwo
  rw [hfamily] at homitted
  exact chartZeroTwoThree_not_mem_chartOrbitElevenFamily homitted

/-- Tight-direction interface to the canonical orbit contradiction.  The three active
tight directions live on `012`, `013`, and `234`; their window restrictions provide
all six row equations consumed by the algebraic exchange theorem.  Thus only the
genuine alignment equation and two-supported shape remain as geometric hypotheses. -/
theorem false_of_chartArgmaxFamily_eq_orbitEleven_of_aligned_tightDirections
    (point : ChartPoint 6 3)
    (hfamily : chartArgmaxFamily point = chartOrbitElevenFamily)
    (ambientLeft ambientRight ambientPair : Fin 6 → ℝ)
    (left right pair : Fin 4 → ℝ)
    (hleftSpread : ambientLeft = selectionInjection chartOrbitElevenPickSix *ᵥ left)
    (hrightSpread : ambientRight = selectionInjection chartOrbitElevenPickSix *ᵥ right)
    (hpairSpread : ambientPair = selectionInjection chartOrbitElevenPickSix *ᵥ pair)
    (hleftTight : IsChartTightDirection point.chart point.weight
      (chartObjective point) chartZeroOneTwo ambientLeft)
    (hrightTight : IsChartTightDirection point.chart point.weight
      (chartObjective point) chartZeroOneThree ambientRight)
    (hpairTight : IsChartTightDirection point.chart point.weight
      (chartObjective point) chartTwoThreeFour ambientPair)
    (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0) : False := by
  have hpickInjective : Function.Injective chartOrbitElevenPickSix := by decide
  have hleftZero : (chartOrbitElevenShiftedGap point *ᵥ left) 0 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartOrbitElevenPickSix hpickInjective chartZeroOneTwo ambientLeft left
      hleftSpread hleftTight 0 (by simp [chartOrbitElevenPickSix, chartZeroOneTwo])
  have hleftThree : (chartOrbitElevenShiftedGap point *ᵥ left) 3 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartOrbitElevenPickSix hpickInjective chartZeroOneTwo ambientLeft left
      hleftSpread hleftTight 3 (by simp [chartOrbitElevenPickSix, chartZeroOneTwo])
  have hrightZero : (chartOrbitElevenShiftedGap point *ᵥ right) 0 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartOrbitElevenPickSix hpickInjective chartZeroOneThree ambientRight right
      hrightSpread hrightTight 0 (by simp [chartOrbitElevenPickSix, chartZeroOneThree])
  have hrightThree : (chartOrbitElevenShiftedGap point *ᵥ right) 3 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartOrbitElevenPickSix hpickInjective chartZeroOneThree ambientRight right
      hrightSpread hrightTight 3 (by simp [chartOrbitElevenPickSix, chartZeroOneThree])
  have hpairOne : (chartOrbitElevenShiftedGap point *ᵥ pair) 1 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartOrbitElevenPickSix hpickInjective chartTwoThreeFour ambientPair pair
      hpairSpread hpairTight 1 (by simp [chartOrbitElevenPickSix, chartTwoThreeFour])
  have hpairTwo : (chartOrbitElevenShiftedGap point *ᵥ pair) 2 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartOrbitElevenPickSix hpickInjective chartTwoThreeFour ambientPair pair
      hpairSpread hpairTight 2 (by simp [chartOrbitElevenPickSix, chartTwoThreeFour])
  exact false_of_chartArgmaxFamily_eq_orbitEleven_of_aligned_active_exchange point
    hfamily left right pair scale u v hpair hpairShape hv hleftZero hleftThree
    hrightZero hrightThree hpairOne hpairTwo


end Gtz

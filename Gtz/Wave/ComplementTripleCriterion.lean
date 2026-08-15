import Gtz.Wave.GaugeWallTriangleTreeReduction
import Gtz.Design.OneDeterminantReduction
import Gtz.Wave.KFourGaugeStarTransportWiring
import Gtz.Wave.KFourPivotTriangleClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A three-label complement is three scalar minors

The complement-form machinery decides an arbitrary selection by a quadratic
form on the labels it omits.  This file specializes that law to three omitted
labels.  It removes the coefficient quantifier completely: a positive corner,
one pair minor, and one determinant polynomial are necessary and sufficient.

The second half spends an already-positive omitted pair.  Once the associated
card-four selection is positive definite, extending its omitted set by one
label is decided by the determinant alone.  This is the exact scalar interface
needed by nonlocal card-four stall arguments.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The ternary quadratic form -/

/-- The symmetric ternary quadratic polynomial in its six matrix entries. -/
def ternaryQuadraticForm (a b c d e f x y z : ℝ) : ℝ :=
  a * x * x + 2 * b * x * y + 2 * c * x * z
    + d * y * y + 2 * e * y * z + f * z * z

/-- The determinant polynomial of the same symmetric `3 x 3` matrix. -/
def ternaryDeterminant (a b c d e f : ℝ) : ℝ :=
  a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d

/-- The quadratic form of the explicit symmetric matrix is the ternary
polynomial. -/
theorem dotProduct_ternaryMatrix_mulVec
    (a b c d e f : ℝ) (v : Fin 3 → ℝ) :
    v ⬝ᵥ ((!![a, b, c; b, d, e; c, e, f] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v)
      = ternaryQuadraticForm a b c d e f (v 0) (v 1) (v 2) := by
  simp only [ternaryQuadraticForm, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE TERNARY FORM CRITERION.**  A symmetric quadratic form in three
variables is positive away from the origin exactly when its three leading
principal minors are positive.  The statement is division-free and square-root
free. -/
theorem ternaryQuadraticForm_pos_iff {a b c d e f : ℝ} :
    (∀ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
        0 < ternaryQuadraticForm a b c d e f x y z)
      ↔ (0 < a ∧ 0 < a * d - b ^ 2 ∧ 0 < ternaryDeterminant a b c d e f) := by
  let form : Matrix (Fin 3) (Fin 3) ℝ := !![a, b, c; b, d, e; c, e, f]
  have hform : ∀ v : Fin 3 → ℝ,
      v ⬝ᵥ (form *ᵥ v) = ternaryQuadraticForm a b c d e f (v 0) (v 1) (v 2) := by
    intro v
    exact dotProduct_ternaryMatrix_mulVec a b c d e f v
  have hsymm : formᵀ = form := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hpd : form.PosDef ↔
      (0 < a ∧ 0 < a * d - b ^ 2 ∧ 0 < ternaryDeterminant a b c d e f) := by
    dsimp only [form]
    rw [leadingMinors_pos_iff_posDef_fin_three]
    rfl
  constructor
  · intro hpositive
    rw [← hpd]
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymm, ?_⟩
    intro v hv
    rw [star_trivial, hform v]
    apply hpositive
    by_contra hall
    push Not at hall
    apply hv
    funext i
    fin_cases i <;> simp_all
  · intro hminors x y z hne
    have hposDef : form.PosDef := hpd.mpr hminors
    let v : Fin 3 → ℝ := ![x, y, z]
    have hv : v ≠ 0 := by
      intro hzero
      have hx := congrFun hzero 0
      have hy := congrFun hzero 1
      have hz := congrFun hzero 2
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at hx hy hz
      exact hne.elim (fun h => h hx) (fun hyz => hyz.elim (fun h => h hy) (fun h => h hz))
    have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hv
    rw [star_trivial, hform v] at hquad
    simpa [v] using hquad

/-! ## 2. Restrict the complement form to three labels -/

/-- The explicit determinant of the complement matrix on three named labels. -/
noncomputable def complementTripleDeterminant
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size) : ℝ :=
  let entry := complementMatrixEntry direction mass weight
  ternaryDeterminant (entry i i) (entry i j) (entry i k)
    (entry j j) (entry j k) (entry k k)

/-- The complement form on exactly three distinct labels is the explicit
ternary quadratic form of their complement-matrix entries. -/
theorem complementForm_triple
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (coeff : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    complementForm direction mass weight ({i, j, k} : Finset (Fin size)) coeff
      = ternaryQuadraticForm
          (complementMatrixEntry direction mass weight i i)
          (complementMatrixEntry direction mass weight i j)
          (complementMatrixEntry direction mass weight i k)
          (complementMatrixEntry direction mass weight j j)
          (complementMatrixEntry direction mass weight j k)
          (complementMatrixEntry direction mass weight k k)
          (coeff i) (coeff j) (coeff k) := by
  rw [complementForm_eq_sum]
  have hji : j ≠ i := Ne.symm hij
  have hki : k ≠ i := Ne.symm hik
  have hkj : k ≠ j := Ne.symm hjk
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, not_or, not_false_eq_true, hij, hik, hjk, and_self]
  rw [complementMatrixEntry_symm direction mass weight huniv j i,
    complementMatrixEntry_symm direction mass weight huniv k i,
    complementMatrixEntry_symm direction mass weight huniv k j]
  simp only [ternaryQuadraticForm]
  ring

/-- A coefficient vector is nonzero somewhere on a named triple exactly when
one of its three named coordinates is nonzero. -/
theorem exists_ne_zero_mem_triple_iff {i j k : Fin size}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (coeff : Fin size → ℝ) :
    (∃ label ∈ ({i, j, k} : Finset (Fin size)), coeff label ≠ 0)
      ↔ (coeff i ≠ 0 ∨ coeff j ≠ 0 ∨ coeff k ≠ 0) := by
  constructor
  · rintro ⟨label, hlabel, hne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · exact Or.inl hne
    · exact Or.inr (Or.inl hne)
    · exact Or.inr (Or.inr hne)
  · intro hne
    rcases hne with hi | hj | hk
    · exact ⟨i, by simp, hi⟩
    · exact ⟨j, by simp, hj⟩
    · exact ⟨k, by simp, hk⟩

/-- Build a global coefficient vector with prescribed values on three distinct
labels. -/
def tripleCoefficient {i j k : Fin size} (x y z : ℝ) : Fin size → ℝ :=
  fun label => if label = i then x else if label = j then y else if label = k then z else 0

@[simp] theorem tripleCoefficient_first {i j k : Fin size} (x y z : ℝ) :
    tripleCoefficient (i := i) (j := j) (k := k) x y z i = x := by
  simp [tripleCoefficient]

@[simp] theorem tripleCoefficient_second {i j k : Fin size} (hik : i ≠ j)
    (x y z : ℝ) :
    tripleCoefficient (i := i) (j := j) (k := k) x y z j = y := by
  simp [tripleCoefficient, Ne.symm hik]

@[simp] theorem tripleCoefficient_third {i j k : Fin size} (hik : i ≠ k)
    (hjk : j ≠ k) (x y z : ℝ) :
    tripleCoefficient (i := i) (j := j) (k := k) x y z k = z := by
  simp [tripleCoefficient, Ne.symm hik, Ne.symm hjk]

/-- **THE THREE-LABEL COMPLEMENT CRITERION.**  A selection omitting three
distinct labels is positive definite exactly when the three leading principal
minors of their complement matrix are positive.  One inverse of the full gap
decides the selection. -/
theorem posDef_directionChartGap_compl_triple_iff
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (directionChartGap direction mass weight
        (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef
      ↔ let entry := complementMatrixEntry direction mass weight
        0 < entry i i ∧
          0 < entry i i * entry j j - entry i j ^ 2 ∧
          0 < complementTripleDeterminant direction mass weight i j k := by
  dsimp only
  have hboost : ∀ label ∈ ({i, j, k} : Finset (Fin size)),
      0 < mass label / weight label := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · exact hboostI
    · exact hboostJ
    · exact hboostK
  rw [posDef_directionChartGap_compl_iff direction mass weight {i, j, k} hboost huniv]
  let a := complementMatrixEntry direction mass weight i i
  let b := complementMatrixEntry direction mass weight i j
  let c := complementMatrixEntry direction mass weight i k
  let d := complementMatrixEntry direction mass weight j j
  let e := complementMatrixEntry direction mass weight j k
  let f := complementMatrixEntry direction mass weight k k
  have hternary := ternaryQuadraticForm_pos_iff (a := a) (b := b) (c := c)
    (d := d) (e := e) (f := f)
  change (∀ coeff : Fin size → ℝ,
      (∃ label ∈ ({i, j, k} : Finset (Fin size)), coeff label ≠ 0) →
        0 < complementForm direction mass weight {i, j, k} coeff) ↔
    (0 < a ∧ 0 < a * d - b ^ 2 ∧ 0 < ternaryDeterminant a b c d e f)
  rw [← hternary]
  constructor
  · intro hform x y z hne
    let coeff := tripleCoefficient (i := i) (j := j) (k := k) x y z
    have hcoeffNe : ∃ label ∈ ({i, j, k} : Finset (Fin size)), coeff label ≠ 0 := by
      rw [exists_ne_zero_mem_triple_iff hij hik hjk]
      simpa only [coeff, tripleCoefficient_first,
        tripleCoefficient_second hij, tripleCoefficient_third hik hjk] using hne
    have hpos := hform coeff hcoeffNe
    rw [complementForm_triple direction mass weight hij hik hjk coeff huniv] at hpos
    simpa only [a, b, c, d, e, f, coeff, tripleCoefficient_first,
      tripleCoefficient_second hij, tripleCoefficient_third hik hjk] using hpos
  · intro hpositive coeff hcoeffNe
    have hne : coeff i ≠ 0 ∨ coeff j ≠ 0 ∨ coeff k ≠ 0 :=
      (exists_ne_zero_mem_triple_iff hij hik hjk coeff).mp hcoeffNe
    have hpos := hpositive (coeff i) (coeff j) (coeff k) hne
    rw [complementForm_triple direction mass weight hij hik hjk coeff huniv]
    simpa [a, b, c, d, e, f] using hpos

/-! ## 3. Once a pair is live, only the determinant remains -/

/-- A positive-definite selection omitting `{i,j}` supplies exactly the first
two minors needed by the three-label criterion. -/
theorem posDef_compl_pair_leadingMinors
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j : Fin size} (hij : i ≠ j)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hpair : (directionChartGap direction mass weight
      (Finset.univ \ ({i, j} : Finset (Fin size)))).PosDef) :
    let entry := complementMatrixEntry direction mass weight
    0 < entry i i ∧ 0 < entry i i * entry j j - entry i j ^ 2 := by
  dsimp only
  have hmain := (posDef_directionChartGap_compl_pair_iff direction mass weight hij
    hboostI hboostJ huniv).mp hpair
  have hdiagI : pairFormDiag direction mass weight i =
      complementMatrixEntry direction mass weight i i := by
    simp only [pairFormDiag, complementMatrixEntry, if_pos, fullPivot]
    ring
  have hdiagJ : pairFormDiag direction mass weight j =
      complementMatrixEntry direction mass weight j j := by
    simp only [pairFormDiag, complementMatrixEntry, if_pos, fullPivot]
    ring
  have hcross : pairFormCross direction mass weight i j ^ 2 =
      complementMatrixEntry direction mass weight i j ^ 2 := by
    simp only [pairFormCross, complementMatrixEntry, if_neg hij]
    ring
  rw [hdiagI, hdiagJ, hcross] at hmain
  exact ⟨hmain.1, by linarith [hmain.2]⟩

/-- **THE ONE-DETERMINANT EXTENSION LAW.**  Suppose the card-four selection
omitting `{i,j}` is already positive definite.  Omitting one further distinct
label `k` produces a positive-definite selection exactly when the explicit
complement triple determinant is positive.  All diagonal and pair-minor side
conditions are inherited from the live pair. -/
theorem posDef_compl_triple_iff_determinant_of_posDef_compl_pair
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hpair : (directionChartGap direction mass weight
      (Finset.univ \ ({i, j} : Finset (Fin size)))).PosDef) :
    (directionChartGap direction mass weight
        (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef
      ↔ 0 < complementTripleDeterminant direction mass weight i j k := by
  rw [posDef_directionChartGap_compl_triple_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK huniv]
  have hlead := posDef_compl_pair_leadingMinors direction mass weight hij hboostI hboostJ
    huniv hpair
  exact and_iff_right hlead.1 |>.trans (and_iff_right hlead.2)

/-! ## 4. The gauge wall as nine scalar tests -/

/-- A triangle label is distinct from every star label. -/
theorem kFourTriangle_ne_star {triangle star : Fin 6}
    (htriangle : triangle ∈ kFourTriangleLabels)
    (hstar : star ∈ kFourStarLabels) : triangle ≠ star := by
  intro heq
  subst star
  revert htriangle hstar
  fin_cases triangle <;> decide

/-- **THE SCALAR TEST FOR EACH OF THE NINE GAUGE TREES.**  On the gauge wall,
the triangle corner is automatically positive.  A tree whose omitted labels are
one triangle and two stars is therefore positive definite exactly when one
triangle-star pair minor and the full triple determinant are positive. -/
theorem kFourGaugeWall_tree_posDef_iff_complementMinors
    (point : DirectionChartPoint 6) (axis : Fin 3 → ℝ) (scale : ℝ)
    (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0)
    {triangle starOne starTwo : Fin 6}
    (htriangle : triangle ∈ kFourTriangleLabels)
    (hstarOne : starOne ∈ kFourStarLabels)
    (hstarTwo : starTwo ∈ kFourStarLabels) (hstars : starOne ≠ starTwo) :
    (directionChartGap kFourDirection point.mass point.weight
        (Finset.univ \ ({triangle, starOne, starTwo} : Finset (Fin 6)))).PosDef
      ↔ let entry := complementMatrixEntry kFourDirection point.mass point.weight
        0 < entry triangle triangle * entry starOne starOne
              - entry triangle starOne ^ 2 ∧
          0 < complementTripleDeterminant kFourDirection point.mass point.weight
            triangle starOne starTwo := by
  have htsOne := kFourTriangle_ne_star htriangle hstarOne
  have htsTwo := kFourTriangle_ne_star htriangle hstarTwo
  rw [posDef_directionChartGap_compl_triple_iff kFourDirection point.mass point.weight
    htsOne htsTwo hstars
    (div_pos (point.mass_pos triangle) (point.weight_pos triangle))
    (div_pos (point.mass_pos starOne) (point.weight_pos starOne))
    (div_pos (point.mass_pos starTwo) (point.weight_pos starTwo))
    (posDef_directionChartGap_univ point)]
  exact and_iff_right (kFourGaugeWall_triangle_complement_diag_pos point axis scale hscale
    hwall haxisSum triangle htriangle)

/-- The complement of one triangle and two distinct star labels is one of the
nine K4 spanning trees. -/
theorem kFour_compl_triangle_twoStars_mem_spanningTreeList
    {triangle starOne starTwo : Fin 6}
    (htriangle : triangle ∈ kFourTriangleLabels)
    (hstarOne : starOne ∈ kFourStarLabels)
    (hstarTwo : starTwo ∈ kFourStarLabels) (hstars : starOne ≠ starTwo) :
    (Finset.univ \ ({triangle, starOne, starTwo} : Finset (Fin 6)))
      ∈ kFourSpanningTreeList := by
  revert htriangle hstarOne hstarTwo hstars
  fin_cases triangle <;> fin_cases starOne <;> fin_cases starTwo <;> decide

/-- The scalar covering statement left by the gauge wall: among the nine
triangle-plus-two-star complement blocks, one has positive pair minor and
positive determinant.  It has no matrix positivity and no probe quantifier. -/
def KFourGaugeWallComplementMinorCover : Prop :=
  ∀ (point : DirectionChartPoint 6),
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    ∃ triangle ∈ kFourTriangleLabels,
      ∃ starOne ∈ kFourStarLabels, ∃ starTwo ∈ kFourStarLabels,
        starOne ≠ starTwo ∧
          let entry := complementMatrixEntry kFourDirection point.mass point.weight
          0 < entry triangle triangle * entry starOne starOne
                - entry triangle starOne ^ 2 ∧
            0 < complementTripleDeterminant kFourDirection point.mass point.weight
              triangle starOne starTwo

/-- **THE SCALAR COVER CLOSES THE GAUGE WALL.**  The corank package supplies the
positive wall axis.  The two scalar inequalities then produce a positive
definite member of the exact nine-tree shortlist. -/
theorem kFourGaugeStarCorankWallClosure_of_complementMinorCover
    (hcover : KFourGaugeWallComplementMinorCover) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hcorank
  obtain ⟨axis, scale, hwall, hscale, haxis0, haxis1, haxis2⟩ :=
    kFourGaugeStarWall_positive_axis point hpsd hcorank
  have haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0 := by
    simp only [kFourAllOnes, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linarith
  obtain ⟨triangle, htriangle, starOne, hstarOne, starTwo, hstarTwo,
      hstars, hminor, hdet⟩ := hcover point hpsd hcorank
  refine ⟨Finset.univ \ ({triangle, starOne, starTwo} : Finset (Fin 6)),
    kFour_compl_triangle_twoStars_mem_spanningTreeList htriangle hstarOne hstarTwo hstars, ?_⟩
  exact (kFourGaugeWall_tree_posDef_iff_complementMinors point axis scale hscale hwall
    haxisSum htriangle hstarOne hstarTwo hstars).2 ⟨hminor, hdet⟩

/-- Conversely, a closed gauge wall returns a scalar witness.  The rank-one
triangle block first cuts the spanning-tree list to the nine live trees; each
of those nine is then read by `kFourGaugeWall_tree_posDef_iff_complementMinors`.
-/
theorem kFourGaugeWallComplementMinorCover_of_gaugeStarCorankWallClosure
    (hclose : KFourGaugeStarCorankWallClosure) :
    KFourGaugeWallComplementMinorCover := by
  intro point hpsd hcorank
  obtain ⟨axis, scale, hwall, hscale, haxis0, haxis1, haxis2⟩ :=
    kFourGaugeStarWall_positive_axis point hpsd hcorank
  have haxisSum : axis ⬝ᵥ kFourAllOnes ≠ 0 := by
    simp only [kFourAllOnes, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linarith
  obtain ⟨winner, hwinner, hpd⟩ := hclose point hpsd hcorank
  have hshort := kFourGaugeWall_posDef_spanningTree_mem_nine point axis scale hscale
    hwall haxisSum hwinner hpd
  have produce (triangle starOne starTwo : Fin 6)
      (htriangle : triangle ∈ kFourTriangleLabels)
      (hstarOne : starOne ∈ kFourStarLabels)
      (hstarTwo : starTwo ∈ kFourStarLabels) (hstars : starOne ≠ starTwo)
      (htree : (directionChartGap kFourDirection point.mass point.weight
        (Finset.univ \ ({triangle, starOne, starTwo} : Finset (Fin 6)))).PosDef) :
      ∃ triangle ∈ kFourTriangleLabels,
        ∃ starOne ∈ kFourStarLabels, ∃ starTwo ∈ kFourStarLabels,
          starOne ≠ starTwo ∧
            let entry := complementMatrixEntry kFourDirection point.mass point.weight
            0 < entry triangle triangle * entry starOne starOne
                  - entry triangle starOne ^ 2 ∧
              0 < complementTripleDeterminant kFourDirection point.mass point.weight
                triangle starOne starTwo := by
    obtain ⟨hminor, hdet⟩ :=
      (kFourGaugeWall_tree_posDef_iff_complementMinors point axis scale hscale hwall
        haxisSum htriangle hstarOne hstarTwo hstars).mp htree
    exact ⟨triangle, htriangle, starOne, hstarOne, starTwo, hstarTwo,
      hstars, hminor, hdet⟩
  simp only [kFourGaugeWallTreeShortList, List.mem_cons, List.not_mem_nil, or_false] at hshort
  rcases hshort with h | h | h | h | h | h | h | h | h
  · subst winner
    apply produce 2 4 5 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({2, 4, 5} : Finset (Fin 6))) = {0, 1, 3} := by decide
    rwa [hset]
  · subst winner
    apply produce 2 3 5 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({2, 3, 5} : Finset (Fin 6))) = {0, 1, 4} := by decide
    rwa [hset]
  · subst winner
    apply produce 2 3 4 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({2, 3, 4} : Finset (Fin 6))) = {0, 1, 5} := by decide
    rwa [hset]
  · subst winner
    apply produce 1 4 5 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({1, 4, 5} : Finset (Fin 6))) = {0, 2, 3} := by decide
    rwa [hset]
  · subst winner
    apply produce 1 3 5 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({1, 3, 5} : Finset (Fin 6))) = {0, 2, 4} := by decide
    rwa [hset]
  · subst winner
    apply produce 1 3 4 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({1, 3, 4} : Finset (Fin 6))) = {0, 2, 5} := by decide
    rwa [hset]
  · subst winner
    apply produce 0 4 5 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({0, 4, 5} : Finset (Fin 6))) = {1, 2, 3} := by decide
    rwa [hset]
  · subst winner
    apply produce 0 3 5 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({0, 3, 5} : Finset (Fin 6))) = {1, 2, 4} := by decide
    rwa [hset]
  · subst winner
    apply produce 0 3 4 (by decide) (by decide) (by decide) (by decide)
    have hset : (Finset.univ \ ({0, 3, 4} : Finset (Fin 6))) = {1, 2, 5} := by decide
    rwa [hset]

/-- **THE EXACT SCALARIZATION OF THE GAUGE WALL.**  Closing the canonical
corank-two gauge wall is equivalent to proving that one of nine explicit
complement blocks has a positive triangle-star pair minor and positive
determinant.  Both matrix positivity and the spanning-tree census have been
eliminated from the remaining target. -/
theorem kFourGaugeStarCorankWallClosure_iff_complementMinorCover :
    KFourGaugeStarCorankWallClosure ↔ KFourGaugeWallComplementMinorCover :=
  ⟨kFourGaugeWallComplementMinorCover_of_gaugeStarCorankWallClosure,
    kFourGaugeStarCorankWallClosure_of_complementMinorCover⟩

/-! ## 5. Registry-facing composition -/

/-- The exact terminal A3 package after scalarizing the gauge wall.  Its pivot
component is the contextual triangle-stall closure; its gauge component is the
nine-test scalar minor cover. -/
def KFourComplementMinorEndgameClosure : Prop :=
  KFourPivotWallTriangleStallClosure ∧ KFourGaugeWallComplementMinorCover

/-- The scalar endgame supplies both terminal wall closures. -/
theorem kFourGaugeAndPivotWallClosure_of_complementMinorEndgame
    (hclose : KFourComplementMinorEndgameClosure) :
    KFourGaugeAndPivotWallClosure :=
  ⟨kFourWindowAllPivotWallClosure_of_triangleStallClosure hclose.1,
    kFourGaugeStarCorankWallClosure_of_complementMinorCover hclose.2⟩

/-- Conversely, closed terminal walls recover the exact scalar endgame.  This
keeps the replacement logically exact rather than merely sufficient. -/
theorem kFourComplementMinorEndgameClosure_of_gaugeAndPivotWallClosure
    (hclose : KFourGaugeAndPivotWallClosure) :
    KFourComplementMinorEndgameClosure :=
  ⟨kFourPivotWallTriangleStallClosure_of_windowAllPivotWallClosure hclose.1,
    kFourGaugeWallComplementMinorCover_of_gaugeStarCorankWallClosure hclose.2⟩

/-- **THE TERMINAL A3 SCALARIZATION.**  The existing gauge-plus-pivot wall
package is exactly a pivot triangle-stall closure together with the finite
nine-test gauge minor cover. -/
theorem kFourGaugeAndPivotWallClosure_iff_complementMinorEndgame :
    KFourGaugeAndPivotWallClosure ↔ KFourComplementMinorEndgameClosure :=
  ⟨kFourComplementMinorEndgameClosure_of_gaugeAndPivotWallClosure,
    kFourGaugeAndPivotWallClosure_of_complementMinorEndgame⟩

/-- The exact scalar endgame discharges the public refined K4 knife band. -/
theorem kFourKnifeBandRefined_of_complementMinorEndgame
    (hclose : KFourComplementMinorEndgameClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_complementMinorEndgame hclose)

/-- The exact scalar endgame reaches the design-side family selector consumed
by the rank-three registry. -/
theorem kFourFamilySelection_of_complementMinorEndgame
    (hclose : KFourComplementMinorEndgameClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_complementMinorEndgame hclose)

/-- The same two residual propositions give a strict K4 tree at every chart
point. -/
theorem kFourEveryPointHasStrictTree_of_complementMinorEndgame
    (hclose : KFourComplementMinorEndgameClosure) :
    KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_complementMinorEndgame hclose)

/-- Producer form for lanes proving the pivot and gauge residuals separately. -/
theorem kFourFamilySelection_of_pivotTriangle_of_complementMinorCover
    (hpivot : KFourPivotWallTriangleStallClosure)
    (hgauge : KFourGaugeWallComplementMinorCover) : KFourFamilySelection :=
  kFourFamilySelection_of_complementMinorEndgame ⟨hpivot, hgauge⟩

end Gtz

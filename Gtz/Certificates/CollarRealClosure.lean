import Mathlib

/-!
# Bridge (iv): from the rational points of the chart cube to the real cube

`checkChart_sound` certifies its sign package at every RATIONAL point of the
half-open chart cube: at every `(den, n1, n2, n3, n4)` of integers with
`1 <= den` and `1 <= n_v <= den`.  The collar statement lives on the REAL
cube.  This file supplies the passage, and it is careful about what survives
it.

Three pieces.

1. `nonnegOnClosureOfNonnegOn` -- the closure principle: a continuous
   function that is nonnegative on a set is nonnegative on its closure.
   This is where STRICTNESS IS LOST: `0 < f` on a dense subset gives only
   `0 <= f` on the closure, and that degradation is real, not an artefact
   (the collar margin genuinely vanishes on the `w0 = 0` face -- the rung-13
   face law).  Strictness on the real cube needs a uniform margin, not
   density.

2. `cubeSubsetClosureOfChartRationalPoints` -- the density input: every point
   of the closed real cube `[0,1]^4` lies in the closure of the admissible
   rational points.  Proved by the explicit approximation
   `n_v = max 1 (ceil (x_v * den))`, `den -> infinity`.

3. `polyValueNonnegOnCube` -- the conclusion for one continuous
   coordinate function: nonnegativity at every admissible rational point
   forces nonnegativity on the whole closed real cube.

WHAT THIS DOES NOT DO, stated plainly.  The kernel-replay package is an
EXISTENTIAL at each point ("there is a threshold, and either a free win or a
candidate"), and the witnessing indices vary from point to point.  Density
transfers a FIXED inequality, not a pointwise-varying disjunction: to reach
the real cube one must first uniformize the index choice on a cell -- which
the cover tree already does, since each leaf box carries ONE witness for all
of its points.  The per-leaf transfer is therefore the intended route, and
this file is its analytic half.
-/

namespace GtzCollarRealClosure

open scoped Topology

/-! ## The closure principle -/

/-- A continuous function nonnegative on a set is nonnegative on its
closure.  The strict version is FALSE, which is exactly why the collar needs
a margin and not merely density. -/
theorem nonnegOnClosureOfNonnegOn {X : Type*} [TopologicalSpace X]
    {valueFunction : X → ℝ} (isContinuous : Continuous valueFunction)
    {sampleSet : Set X}
    (nonnegOnSamples : ∀ point ∈ sampleSet, 0 ≤ valueFunction point) :
    ∀ point ∈ closure sampleSet, 0 ≤ valueFunction point := by
  have preimageIsClosed : IsClosed (valueFunction ⁻¹' Set.Ici (0 : ℝ)) :=
    IsClosed.preimage isContinuous isClosed_Ici
  have subsetPreimage : sampleSet ⊆ valueFunction ⁻¹' Set.Ici (0 : ℝ) :=
    fun point pointMem => nonnegOnSamples point pointMem
  intro point pointMem
  exact closure_minimal subsetPreimage preimageIsClosed pointMem

/-! ## The admissible rational points of the chart cube -/

/-- The rational points the kernel replay quantifies over: `(n1/den, ..,
n4/den)` with `1 <= den` and `1 <= n_v <= den`, i.e. the rational points of
the half-open cube `(0,1]^4`. -/
def chartRationalPoints : Set (ℝ × ℝ × ℝ × ℝ) :=
  {point | ∃ den one two three four : ℤ,
      1 ≤ den ∧ 1 ≤ one ∧ one ≤ den ∧ 1 ≤ two ∧ two ≤ den
        ∧ 1 ≤ three ∧ three ≤ den ∧ 1 ≤ four ∧ four ≤ den
        ∧ point = ((one : ℝ) / den, (two : ℝ) / den, (three : ℝ) / den,
            (four : ℝ) / den)}

/-- The closed real chart cube. -/
def closedChartCube : Set (ℝ × ℝ × ℝ × ℝ) :=
  {point | point.1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.2.1 ∈ Set.Icc (0 : ℝ) 1
    ∧ point.2.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.2.2.2 ∈ Set.Icc (0 : ℝ) 1}

/-- One coordinate of the approximation: the admissible integer numerator. -/
noncomputable def approximateNumerator (coordinate : ℝ) (denominator : ℕ) :
    ℤ :=
  max 1 ⌈coordinate * denominator⌉

theorem approximateNumeratorIsAdmissible {coordinate : ℝ}
    (inUnitInterval : coordinate ∈ Set.Icc (0 : ℝ) 1) {denominator : ℕ}
    (denominatorPos : 0 < denominator) :
    1 ≤ approximateNumerator coordinate denominator
      ∧ approximateNumerator coordinate denominator ≤ (denominator : ℤ) := by
  obtain ⟨lowerBound, upperBound⟩ := inUnitInterval
  refine ⟨le_max_left _ _, max_le ?_ ?_⟩
  · exact_mod_cast denominatorPos
  · have scaledLe : coordinate * denominator ≤ (denominator : ℝ) := by
      have denominatorNonneg : (0 : ℝ) ≤ (denominator : ℝ) := by positivity
      calc coordinate * denominator ≤ 1 * denominator :=
            mul_le_mul_of_nonneg_right upperBound denominatorNonneg
        _ = (denominator : ℝ) := one_mul _
    have ceilLe : ⌈coordinate * denominator⌉ ≤ (denominator : ℤ) := by
      apply Int.ceil_le.mpr
      simpa using scaledLe
    exact ceilLe

theorem approximateNumeratorIsClose {coordinate : ℝ}
    (inUnitInterval : coordinate ∈ Set.Icc (0 : ℝ) 1) {denominator : ℕ}
    (denominatorPos : 0 < denominator) :
    |(approximateNumerator coordinate denominator : ℝ) / denominator
      - coordinate| ≤ 1 / denominator := by
  obtain ⟨lowerBound, _⟩ := inUnitInterval
  have denominatorRealPos : (0 : ℝ) < (denominator : ℝ) := by
    exact_mod_cast denominatorPos
  have ceilLower : coordinate * denominator ≤ ⌈coordinate * denominator⌉ :=
    Int.le_ceil _
  have ceilUpper : (⌈coordinate * denominator⌉ : ℝ)
      < coordinate * denominator + 1 := Int.ceil_lt_add_one _
  have numeratorLower :
      coordinate * denominator ≤ (approximateNumerator coordinate denominator : ℝ) := by
    unfold approximateNumerator
    have : (⌈coordinate * denominator⌉ : ℝ)
        ≤ ((max 1 ⌈coordinate * denominator⌉ : ℤ) : ℝ) := by
      exact_mod_cast le_max_right (1 : ℤ) ⌈coordinate * denominator⌉
    linarith
  have numeratorUpper :
      ((approximateNumerator coordinate denominator : ℤ) : ℝ)
        ≤ coordinate * denominator + 1 := by
    unfold approximateNumerator
    rcases max_cases (1 : ℤ) ⌈coordinate * denominator⌉ with
      ⟨isOne, _⟩ | ⟨isCeil, _⟩
    · rw [isOne]
      have coordinateNonneg : 0 ≤ coordinate * denominator :=
        mul_nonneg lowerBound (le_of_lt denominatorRealPos)
      push_cast
      linarith
    · rw [isCeil]
      linarith
  have lowerSide : coordinate
      ≤ (approximateNumerator coordinate denominator : ℝ) / denominator :=
    (le_div_iff₀ denominatorRealPos).mpr numeratorLower
  have upperSide :
      (approximateNumerator coordinate denominator : ℝ) / denominator
        ≤ coordinate + 1 / denominator := by
    refine (div_le_iff₀ denominatorRealPos).mpr ?_
    have expand : (coordinate + 1 / denominator) * denominator
        = coordinate * denominator + 1 := by
      field_simp
    rw [expand]
    exact numeratorUpper
  rw [abs_le]
  constructor <;> linarith

/-- THE DENSITY INPUT: every point of the closed real cube is a limit of
admissible rational points. -/
theorem cubeSubsetClosureOfChartRationalPoints :
    closedChartCube ⊆ closure chartRationalPoints := by
  intro point pointInCube
  obtain ⟨oneIn, twoIn, threeIn, fourIn⟩ := pointInCube
  rw [Metric.mem_closure_iff]
  intro radius radiusPos
  obtain ⟨denominator, denominatorLarge⟩ := exists_nat_gt (1 / radius)
  have denominatorPos : 0 < denominator := by
    by_contra notPos
    have denominatorZero : denominator = 0 := by omega
    rw [denominatorZero] at denominatorLarge
    have : (0 : ℝ) < 1 / radius := by positivity
    simp at denominatorLarge
    linarith
  have denominatorRealPos : (0 : ℝ) < (denominator : ℝ) := by
    exact_mod_cast denominatorPos
  have reciprocalSmall : 1 / (denominator : ℝ) < radius := by
    rw [div_lt_iff₀ denominatorRealPos]
    rw [div_lt_iff₀ radiusPos] at denominatorLarge
    linarith [denominatorLarge]
  refine ⟨((approximateNumerator point.1 denominator : ℝ) / denominator,
      (approximateNumerator point.2.1 denominator : ℝ) / denominator,
      (approximateNumerator point.2.2.1 denominator : ℝ) / denominator,
      (approximateNumerator point.2.2.2 denominator : ℝ) / denominator),
    ⟨denominator, approximateNumerator point.1 denominator,
      approximateNumerator point.2.1 denominator,
      approximateNumerator point.2.2.1 denominator,
      approximateNumerator point.2.2.2 denominator, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact_mod_cast denominatorPos
  · exact (approximateNumeratorIsAdmissible oneIn denominatorPos).1
  · exact (approximateNumeratorIsAdmissible oneIn denominatorPos).2
  · exact (approximateNumeratorIsAdmissible twoIn denominatorPos).1
  · exact (approximateNumeratorIsAdmissible twoIn denominatorPos).2
  · exact (approximateNumeratorIsAdmissible threeIn denominatorPos).1
  · exact (approximateNumeratorIsAdmissible threeIn denominatorPos).2
  · exact (approximateNumeratorIsAdmissible fourIn denominatorPos).1
  · exact (approximateNumeratorIsAdmissible fourIn denominatorPos).2
  · push_cast
    rfl
  · have closeOne := approximateNumeratorIsClose oneIn denominatorPos
    have closeTwo := approximateNumeratorIsClose twoIn denominatorPos
    have closeThree := approximateNumeratorIsClose threeIn denominatorPos
    have closeFour := approximateNumeratorIsClose fourIn denominatorPos
    simp only [Prod.dist_eq, Real.dist_eq]
    refine max_lt ?_ (max_lt ?_ (max_lt ?_ ?_)) <;> rw [abs_sub_comm] <;>
      linarith

/-- THE CONCLUSION: a continuous coordinate function that the kernel replay
certifies nonnegative at every admissible rational point is nonnegative on
the whole closed real cube. -/
theorem valueIsNonnegOnClosedCube {valueFunction : ℝ × ℝ × ℝ × ℝ → ℝ}
    (isContinuous : Continuous valueFunction)
    (nonnegAtRationalPoints : ∀ den one two three four : ℤ,
      1 ≤ den → 1 ≤ one → one ≤ den → 1 ≤ two → two ≤ den → 1 ≤ three →
      three ≤ den → 1 ≤ four → four ≤ den →
      0 ≤ valueFunction ((one : ℝ) / den, (two : ℝ) / den, (three : ℝ) / den,
        (four : ℝ) / den)) :
    ∀ point ∈ closedChartCube, 0 ≤ valueFunction point := by
  intro point pointInCube
  refine nonnegOnClosureOfNonnegOn isContinuous ?_ point
    (cubeSubsetClosureOfChartRationalPoints pointInCube)
  rintro sample ⟨den, one, two, three, four, denGe, oneGe, oneLe, twoGe,
    twoLe, threeGe, threeLe, fourGe, fourLe, sampleForm⟩
  rw [sampleForm]
  exact nonnegAtRationalPoints den one two three four denGe oneGe oneLe
    twoGe twoLe threeGe threeLe fourGe fourLe

end GtzCollarRealClosure

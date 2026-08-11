import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Reduction.ComplementKernelWeld
import Gtz.Reduction.ComplementKernelRepairsDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A dominating triple that no ladder rung can certify

The descent ladder reads domination through `Gtz.erase_strictDominates_iff_pivot_lt_one`
and `Gtz.erase_dominates_iff_pivot_le_one`, both of which need a POSITIVE DEFINITE
base to invert.  The complement-kernel weld
(`Gtz.dominates_complement_iff_kernel_posSemidef`) needs no base at all: it
inverts the full excess once and reads principal minors.

The two are therefore NOT interchangeable as decision procedures, and this module
exhibits the separation.

The general obstruction is
`Gtz.not_posDef_gap_insert_of_two_independent_gapProbes`
(`Gtz/Reduction/ComplementKernelRepairsDescent.lean`): a subset whose gap carries
two independent probes has NO positive definite one-label extension, so no rung
of the ladder has it as an erasure.  ** THAT THEOREM IS CONSUMED HERE RATHER THAN
RESTATED. **  A weaker form of it, carrying a redundant `Gtz.Dominates`
hypothesis, was proved independently while this module was written; the two were
compared in the kernel, the weaker one is a corollary of the stronger, and only
the stronger survives.

What this module adds is the INHABITANT, which is what turns the obstruction
from a statement into a separation:

* `Gtz.axisSplitDesign` inhabits the hypothesis with rational data: a `(6,3)`
  design on the three coordinate axes, two atoms per axis, whose triple
  `{0, 1, 2}` dominates with a gap of corank two.  Rationality is not automatic
  here -- at uniform weights no rational version exists, six not being a sum of
  two rational squares -- and dropping uniformity is what buys it.

The consequence for the weld is stated at
`Gtz.axisSplitDesign_dominates_baseTriple_with_no_posDef_extension`: at that
triple the ladder's rung hypothesis is uninhabited while domination holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## A rational inhabitant

Two atoms on each coordinate axis, of squared lengths one and four, with the
weights fixed by Parseval.  Every subset sum is diagonal, so every question about
this design is three scalar questions. -/

/-- The six axis atoms: the short atom of each axis first, then the long ones. -/
def axisSplitAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 2]
  | 3 => ![2, 0, 0]
  | 4 => ![0, 2, 0]
  | 5 => ![0, 0, 1]

/-- The six weights.  Parseval is one scalar equation per axis. -/
noncomputable def axisSplitWeight : Fin 6 → ℝ
  | 0 => 1 / 12
  | 1 => 1 / 12
  | 2 => 5 / 24
  | 3 => 11 / 48
  | 4 => 11 / 48
  | 5 => 1 / 6

/-- **The axis-split design.**  A genuine weighted `(6,3)` design, entirely
rational, built so that the triple `{0, 1, 2}` dominates with a two-dimensional
tight space. -/
noncomputable def axisSplitDesign : WeightedDesign 6 3 where
  atom := axisSplitAtom
  weight := axisSplitWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [axisSplitWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [axisSplitWeight]
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [axisSplitAtom, axisSplitWeight] <;> norm_num

/-- The base triple's unweighted atom sum, entry by entry. -/
theorem axisSplitDesign_baseTripleSubsetSum_eq :
    subsetSum axisSplitDesign {0, 1, 2}
      = Matrix.of ![![1, 0, 0], ![0, 1, 0], ![0, 0, 4]] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [axisSplitDesign, axisSplitAtom, atomMatrix, Matrix.vecMulVec]

/-- The base triple's gap, entry by entry: `diag(0, 0, 3)`. -/
theorem axisSplitDesign_baseTripleGap_eq :
    subsetSum axisSplitDesign {0, 1, 2} - 1
      = Matrix.of ![![0, 0, 0], ![0, 0, 0], ![0, 0, 3]] := by
  rw [axisSplitDesign_baseTripleSubsetSum_eq]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num

/-- The base triple's quadratic form is a single square. -/
theorem axisSplitDesign_baseTripleGap_form (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum axisSplitDesign {0, 1, 2} - 1) *ᵥ probe)
      = 3 * probe 2 ^ 2 := by
  rw [axisSplitDesign_baseTripleGap_eq]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- **THE BASE TRIPLE DOMINATES.** -/
theorem axisSplitDesign_dominates_baseTriple :
    Dominates axisSplitDesign {0, 1, 2} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
  · rw [axisSplitDesign_baseTripleGap_eq]
    refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp
  · rw [star_trivial, axisSplitDesign_baseTripleGap_form]
    positivity

/-- The first null direction of the base triple. -/
theorem axisSplitDesign_baseTriple_firstNull :
    (subsetSum axisSplitDesign {0, 1, 2} - 1) *ᵥ ![1, 0, 0] = 0 := by
  rw [axisSplitDesign_baseTripleGap_eq]
  ext coordinate
  fin_cases coordinate <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The second null direction of the base triple. -/
theorem axisSplitDesign_baseTriple_secondNull :
    (subsetSum axisSplitDesign {0, 1, 2} - 1) *ᵥ ![0, 1, 0] = 0 := by
  rw [axisSplitDesign_baseTripleGap_eq]
  ext coordinate
  fin_cases coordinate <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The two null directions are independent. -/
theorem axisSplitDesign_baseTriple_nullIndependent
    (firstScalar secondScalar : ℝ)
    (hvanishes : firstScalar • (![1, 0, 0] : Fin 3 → ℝ)
      + secondScalar • (![0, 1, 0] : Fin 3 → ℝ) = 0) :
    firstScalar = 0 ∧ secondScalar = 0 := by
  constructor
  · have hzero := congrFun hvanishes 0
    simpa using hzero
  · have hzero := congrFun hvanishes 1
    simpa using hzero

/-- **THE SEPARATION.**  The base triple dominates, and no one-label extension of
it is positive definite -- so every rung of the descent ladder is vacuous there,
while `Gtz.dominates_complement_iff_kernel_posSemidef` decides it with no base at
all. -/
theorem axisSplitDesign_dominates_baseTriple_with_no_posDef_extension :
    Dominates axisSplitDesign {0, 1, 2}
      ∧ ∀ added : Fin 6, added ∉ ({0, 1, 2} : Finset (Fin 6)) →
          ¬ (subsetSum axisSplitDesign (insert added {0, 1, 2}) - 1).PosDef := by
  refine ⟨axisSplitDesign_dominates_baseTriple, fun added hnew => ?_⟩
  exact not_posDef_gap_insert_of_two_independent_gapProbes axisSplitDesign {0, 1, 2}
    added hnew
    axisSplitDesign_baseTriple_firstNull axisSplitDesign_baseTriple_secondNull
    axisSplitDesign_baseTriple_nullIndependent

/-- The base triple is not strictly dominating: it is a genuine corank-two
winner, not a positive definite one. -/
theorem axisSplitDesign_not_posDef_baseTriple :
    ¬ (subsetSum axisSplitDesign {0, 1, 2} - 1).PosDef := by
  intro hposDef
  have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2
    (x := ![1, 0, 0]) (by
      intro hzero
      have hentry := congrFun hzero 0
      simp at hentry)
  rw [star_trivial, axisSplitDesign_baseTripleGap_form] at hpositive
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hpositive

end Gtz

/-
# A `(6,3)` crux carries no stress -- the new crux field, and its geometry

`Gtz.exists_dominating_sixThree_of_stress` (`Gtz.Reduction.StressConditionalWalk`)
says that a `(6,3)` design carrying ANY nonzero stress is dominated.  A crux is by
definition not dominated, so:

  **A `(6,3)` CRUX CARRIES NO STRESS.**  `SixThreeCrux.stress_eq_zero`.

Equivalently its six Veronese images `g_c g_c^T` are linearly independent in
`Sym_3(R)`, and since `dim Sym_3(R) = 6` exactly they are a BASIS of it.  Three
readings follow, each of a shape some other lane can consume.

* GEOMETRIC.  `SixThreeCrux.no_commonQuadric`: no nonzero symmetric form
  annihilates all six directions, i.e. THE SIX DIRECTIONS OF A `(6,3)` CRUX LIE ON
  NO CONIC OF `RP^2`.  This is strictly stronger than the shipped field
  `hasNoParallelPair`, which it reproves as `not_hasParallelPair_via_stress`, and
  the degenerate line-pair case `not_twoPlanes` -- six atoms splitting into two
  coplanar triples -- is invisible to parallelism.

* ALGEBRAIC.  `SixThreeCrux.det_hadamardSquareGram_ne_zero` and
  `rank_hadamardSquareGram_eq_six`: the shipped cap
  `Gtz.rank_hadamardSquareGram_le_six` is ATTAINED at a crux.  A nonvanishing
  determinant is a legitimate saturation polynomial for an elimination run.

* PARAMETRIC.  `SixThreeCrux.weight_unique`: Parseval has a UNIQUE solution at a
  crux, so the weights are DETERMINED by the atoms and six unknowns leave any
  search over the crux locus.

The bridge between the two vocabularies is the FROBENIUS IDENTITY
`trace_transpose_mul_self_momentCombination`, which reads the quadratic form of
the shipped Hadamard-square Gram as a squared Frobenius norm.  It upgrades the
shipped one-way `Gtz.hadamardSquareGram_mulVec_eq_zero` to the equivalence
`hadamardSquareGram_mulVec_eq_zero_iff`: the kernel of the Hadamard square IS the
syzygy space, not merely a superset of it.

NO COMPLEX ANALOGUE, and this is orientation prose, not a theorem of this file.
The exclusion is inherited from the walk, whose landing theorem
`Gtz.gtzWeighted_of_le_five` is FALSE over `C` -- see
`Gtz.complexGtzWeighted_iff_size_le_rank_add_one`, which pins the complex
rank-three threshold at size at most four.  The complex refuting witness
`Gtz.paddedDesign` does carry a stress (its antipodal spike pair has equal
Hermitian images) and walking it produces a complex `(5,3)` design with no
dominating triple, so the walk RUNS over `C` and concludes nothing.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.SevenThreeSyzygy
import Gtz.Quantitative.SixThreeCrux
import Gtz.Reduction.StressConditionalWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## The Frobenius identity: the Hadamard square form IS the squared stress norm -/

/-- **THE FROBENIUS IDENTITY.**  `||sum_c x_c u_c u_c^T||_F^2 = x^T W x`, where `W`
is the Hadamard square of the direction Gram.  Immediate from
`tr(u_c u_c^T u_d u_d^T) = <u_c, u_d>^2`; it is the coordinate-free content of the
shipped factorisation `Gtz.hadamardSquareGram_eq_veroneseRows_mul_transpose`. -/
theorem trace_transpose_mul_self_momentCombination (design : WeightedDesign size 3)
    (coefficient : Fin size → ℝ) :
    Matrix.trace ((momentCombination design coefficient)ᵀ
        * momentCombination design coefficient)
      = coefficient ⬝ᵥ (hadamardSquareGram design *ᵥ coefficient) := by
  have hpair : ∀ firstIndex secondIndex : Fin size,
      Matrix.trace ((atomMatrix (unitAtom design firstIndex))ᵀ
          * atomMatrix (unitAtom design secondIndex))
        = directionGram design firstIndex secondIndex ^ 2 := by
    intro firstIndex secondIndex
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, atomMatrix,
      Matrix.vecMulVec_apply, directionGram, dotProduct, Fin.sum_univ_three]
    ring
  rw [momentCombination, Matrix.transpose_sum, Finset.sum_mul]
  rw [Matrix.trace_sum]
  have hrow : ∀ firstIndex : Fin size,
      Matrix.trace ((coefficient firstIndex • atomMatrix (unitAtom design firstIndex))ᵀ
          * ∑ secondIndex, coefficient secondIndex • atomMatrix (unitAtom design secondIndex))
        = ∑ secondIndex, hadamardSquareGram design firstIndex secondIndex
            * (coefficient firstIndex * coefficient secondIndex) := by
    intro firstIndex
    rw [Matrix.transpose_smul, Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun secondIndex _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
      smul_eq_mul, hpair firstIndex secondIndex, hadamardSquareGram_apply]
    ring
  rw [Finset.sum_congr rfl fun firstIndex (_ : firstIndex ∈ Finset.univ) => hrow firstIndex]
  rw [dotProduct_mulVec_eq_entrySum]

/-- **THE CONVERSE OF `Gtz.hadamardSquareGram_mulVec_eq_zero`.**  A kernel vector of
the Hadamard square has vanishing Frobenius norm as a moment combination, hence IS
a syzygy. -/
theorem momentCombination_eq_zero_of_mulVec_eq_zero (design : WeightedDesign size 3)
    {coefficient : Fin size → ℝ}
    (hkernel : hadamardSquareGram design *ᵥ coefficient = 0) :
    momentCombination design coefficient = 0 := by
  refine eq_zero_of_trace_transpose_mul_self ?_
  rw [trace_transpose_mul_self_momentCombination, hkernel, dotProduct_zero]

/-- **THE KERNEL OF THE HADAMARD SQUARE IS EXACTLY THE SYZYGY SPACE.**  Both ways;
the tree shipped only the forward half. -/
theorem hadamardSquareGram_mulVec_eq_zero_iff (design : WeightedDesign size 3)
    (coefficient : Fin size → ℝ) :
    hadamardSquareGram design *ᵥ coefficient = 0
      ↔ momentCombination design coefficient = 0 :=
  ⟨momentCombination_eq_zero_of_mulVec_eq_zero design,
    hadamardSquareGram_mulVec_eq_zero design⟩

/-- Raw stresses and unit-direction syzygies are the same object, rescaled by the
leverages. -/
theorem momentCombination_eq_smul_sum (design : WeightedDesign size 3)
    (coefficient : Fin size → ℝ) :
    momentCombination design coefficient
      = ∑ c, (coefficient c / leverageOf (design.atom c)) • atomMatrix (design.atom c) := by
  rw [momentCombination]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [atomMatrix_unitAtom, smul_smul, div_eq_mul_inv]

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-! ## The field itself -/

/-- **THE NEW CRUX FIELD: A `(6,3)` CRUX CARRIES NO STRESS.**  A nonzero stress
would reduce the design below size six by the stress-conditional walk, and every
cell below six is a theorem, so a dominating triple would exist -- which the field
`hasNoDominatingTriple` forbids. -/
theorem stress_eq_zero {stress : Fin 6 → ℝ}
    (hstress : (∑ c, stress c • atomMatrix (crux.design.atom c)) = 0) : stress = 0 := by
  by_contra hnonzero
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_sixThree_of_stress crux.design hnonzero hstress
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-- The same statement as linear independence: the six Veronese images of a crux are
independent in `Sym_3(R)`, hence -- there being exactly six of them and
`dim Sym_3(R) = 6` -- a BASIS of it. -/
theorem linearIndependent_veronese :
    LinearIndependent ℝ (fun c : Fin 6 => atomMatrix (crux.design.atom c)) := by
  rw [Fintype.linearIndependent_iff]
  intro stress hstress
  have hzero := stress_eq_zero crux hstress
  exact fun c => congrFun hzero c

/-! ## The algebraic reading -/

/-- **THE HADAMARD SQUARE GRAM OF A CRUX IS NONSINGULAR.**  A determinant zero would
supply a kernel vector, the Frobenius identity would turn it into a syzygy, and the
leverages -- all positive by `isAllHeavy` -- would rescale it into a genuine
stress. -/
theorem det_hadamardSquareGram_ne_zero : (hadamardSquareGram crux.design).det ≠ 0 := by
  intro hdet
  obtain ⟨coefficient, hnonzero, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsyzygy : momentCombination crux.design coefficient = 0 :=
    momentCombination_eq_zero_of_mulVec_eq_zero crux.design hkernel
  have hleverage : ∀ c, 0 < leverageOf (crux.design.atom c) := fun c =>
    lt_trans zero_lt_one (crux.isAllHeavy c)
  have hraw : (∑ c, (coefficient c / leverageOf (crux.design.atom c))
      • atomMatrix (crux.design.atom c)) = 0 := by
    rw [← momentCombination_eq_smul_sum crux.design coefficient]
    exact hsyzygy
  have hzero := stress_eq_zero crux hraw
  refine hnonzero (funext fun c => ?_)
  have hentry : coefficient c / leverageOf (crux.design.atom c) = 0 := congrFun hzero c
  rw [Pi.zero_apply]
  exact (div_eq_zero_iff.mp hentry).resolve_right (ne_of_gt (hleverage c))

/-- **THE CAP IS ATTAINED.**  `Gtz.rank_hadamardSquareGram_le_six` bounds the rank by
the Veronese dimension at every size; at a `(6,3)` crux the rank is EXACTLY six. -/
theorem rank_hadamardSquareGram_eq_six : (hadamardSquareGram crux.design).rank = 6 := by
  have hunit : IsUnit (hadamardSquareGram crux.design) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (det_hadamardSquareGram_ne_zero crux))
  simpa using Matrix.rank_of_isUnit _ hunit

/-! ## The geometric reading -/

/-- **THE HEADLINE: NO CONIC PASSES THROUGH A `(6,3)` CRUX.**  No nonzero symmetric
form annihilates the quadratic form of every atom, so the six directions, read as
six points of `RP^2`, lie on no conic. -/
theorem no_commonQuadric {form : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : formᵀ = form)
    (hquadric : ∀ atomIndex, crux.design.atom atomIndex
      ⬝ᵥ (form *ᵥ crux.design.atom atomIndex) = 0) :
    form = 0 := by
  by_contra hnonzero
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_of_commonQuadric crux.design hsymmetric hnonzero hquadric
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-- **CONSISTENCY: THE NEW FIELD SUBSUMES `hasNoParallelPair`.**  The shipped crux
field is a CONSEQUENCE of stress-freeness, not an independent assumption. -/
theorem not_hasParallelPair_via_stress : ¬ HasParallelPair crux.design :=
  not_hasParallelPair_of_no_stress crux.design fun _ hstress => stress_eq_zero crux hstress

/-- **AND IT IS STRICTLY STRONGER.**  Six atoms may be pairwise non-parallel and
still split into two coplanar triples; a crux cannot.  No parallelism appears in the
statement. -/
theorem not_twoPlanes {firstNormal secondNormal : Fin 3 → ℝ} (hfirst : firstNormal ≠ 0)
    (hsecond : secondNormal ≠ 0) :
    ¬ (∀ atomIndex, firstNormal ⬝ᵥ crux.design.atom atomIndex = 0
      ∨ secondNormal ⬝ᵥ crux.design.atom atomIndex = 0) := by
  intro hsplit
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_of_twoPlanes crux.design hfirst hsecond hsplit
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-! ## The parametric reading -/

/-- **AT A CRUX THE WEIGHTS ARE DETERMINED BY THE ATOMS.**  Parseval has a UNIQUE
solution, because two solutions differ by a stress.  Six unknowns therefore leave
any parameterisation of the crux locus: it is cut out by its atoms alone. -/
theorem weight_unique (weight : Fin 6 → ℝ)
    (hparseval : (∑ c, weight c • atomMatrix (crux.design.atom c)) = 1) :
    weight = crux.design.weight := by
  have hstress : (∑ c, (weight c - crux.design.weight c)
      • atomMatrix (crux.design.atom c)) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hparseval, crux.design.isParseval, sub_self]
  have hzero := stress_eq_zero crux hstress
  funext c
  have hentry : weight c - crux.design.weight c = 0 := congrFun hzero c
  linarith [hentry]

end SixThreeCrux

end Gtz

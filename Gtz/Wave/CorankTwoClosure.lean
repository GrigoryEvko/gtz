/-
# The planar-outside corner of the corank-two arm: the calibrated fixture and the residual

## What this module shows

`Gtz.corankTwoPlanarDesign` is an exact rational `(6,3)` design built for the
corank-two arm's hardest corner: the dominator `{0,1,2}` has the rank-one gap
`3 • atomMatrix ![0,0,1]` EXACTLY, and all three outside atoms are planar
(they read zero against the gap direction).  At this fixture every landed
corank-two instrument is silent:

* the nine swaps carry no information (`Gtz.not_posDef_swap_of_rankOneGap`);
* the complement `{3,4,5}` is REFUSED — its gap-direction mass is zero — so
  the landed threshold `Gtz.posDef_compl_of_rankOneGap_of_threshold` cannot
  fire (`Gtz.corankTwoPlanar_complement_refused`);

and the design is nevertheless not a tie, because a ONE-SHARED triple
dominates strictly: `{0,4,5}` shares exactly the atom `0` with the dominator,
and the split criterion of `Gtz/Wave/CorankTwoOneShared.lean` proves its gap
positive definite through an explicit sum of squares
(`Gtz.corankTwoPlanar_oneShared_strict`).  The one-shared instrument decides
configurations that everything previously landed cannot see.

## The inside frame

The inside plane parts are the rational `(3,2)` Parseval triple
`(1/3, 2/3), (2/3, 1/3), (2/3, -2/3)`, and the gap-direction components
`(-4/3, 4/3, -2/3)` are `sqrt(1+lam)` times the Cramer coefficients of that
triple at `lam = 3` — the `(3,2)` kernel rigidity of a rank-one gap realized
over the rationals with no whitener.

## The residual, exactly (MEASURED and paper-derived, recorded for the next fork)

The corank-two arm is NOT closed here.  What remains is: a `(6,3)` tie with
gap `lam • atomMatrix u`, `lam > 0`, has a parallel pair.  The split
criterion turns each of the nine one-shared refusals into

  `B_T ≤ 1`  or  `∃ w ⊥ u: (B_T − 1)·G_T(w) ≤ cross_T(w)²`,

and the paper analysis of the planar-outside corner shows the fight is a
weight-geometry tension, not an alignment identity: outside pair-sums that
are "thin" (`λ_min(Q_k) ≤ 1`) refuse their triples for free, while the plane
Parseval `Σ_d s_d q_d q_dᵀ = I_K − Σ_e t_e p_e p_eᵀ ⪰ (1 − t_max)·I_K`
forbids all three pairs from thinning at once.  In the equal-weights slice
the two-thin case is contradictory (the non-thin pair's refusal caps the
maximal gap-direction mass at `1 + (lam−2)/6`, below the forced maximum
`(1+lam)/3`), while the zero- and one-thin cases survive the coarse
eigenvalue bounds and need the alignment of the inside plane parts against
the outside atoms.  No surviving corner was found; no closure was proved.
-/
import Mathlib
import Gtz.Wave.CorankTwoOneShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The six atoms: the rational `(3,2)` Parseval triple lifted by its Cramer
coefficients at `lam = 3`, plus three planar outside atoms. -/
noncomputable def corankTwoPlanarAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![1 / 3, 2 / 3, -(4 / 3)]
  | 1 => ![2 / 3, 1 / 3, 4 / 3]
  | 2 => ![2 / 3, -(2 / 3), -(2 / 3)]
  | 3 => ![1, 2, 0]
  | 4 => ![2, 1, 0]
  | 5 => ![2, -2, 0]

/-- The six weights: equal quarters inside, equal twelfths outside. -/
noncomputable def corankTwoPlanarWeight : Fin 6 → ℝ
  | 0 => 1 / 4
  | 1 => 1 / 4
  | 2 => 1 / 4
  | 3 => 1 / 12
  | 4 => 1 / 12
  | 5 => 1 / 12

/-- **The planar-outside fixture.**  An exact rational `(6,3)` design whose
dominator `{0,1,2}` carries the rank-one gap `3 • atomMatrix ![0,0,1]`. -/
noncomputable def corankTwoPlanarDesign : WeightedDesign 6 3 where
  atom := corankTwoPlanarAtom
  weight := corankTwoPlanarWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [corankTwoPlanarWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [corankTwoPlanarWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [corankTwoPlanarAtom, corankTwoPlanarWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem corankTwoPlanarDesign_atom :
    corankTwoPlanarDesign.atom = corankTwoPlanarAtom := rfl

/-- **The rank-one gap, exactly.**  `S_{0,1,2} − 1 = 3 • atomMatrix ![0,0,1]`:
the fixture inhabits the corank-two hypothesis with `lam = 3` and gap
direction the third axis, in exact rational arithmetic. -/
theorem corankTwoPlanarDesign_gap :
    subsetSum corankTwoPlanarDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = (3 : ℝ) • atomMatrix (![0, 0, 1] : Fin 3 → ℝ) := by
  rw [subsetSum,
    show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [corankTwoPlanarDesign_atom, corankTwoPlanarAtom, atomMatrix,
      Matrix.cons_val_two]

/-- The gap direction is a unit vector. -/
theorem corankTwoPlanar_gapDir_unit :
    (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1] = 1 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- A scaled rank-one atom is symmetric. -/
theorem transpose_smul_atomMatrix (c : ℝ) (g : Fin 3 → ℝ) :
    ((c • atomMatrix g)ᵀ : Matrix (Fin 3) (Fin 3) ℝ) = c • atomMatrix g := by
  rw [Matrix.transpose_smul]
  congr 1
  ext i j
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.transpose_apply, mul_comm]

/-- **The fixture dominates at `{0,1,2}`.**  The gap is three times a rank-one
atom, positive semidefinite outright. -/
theorem corankTwoPlanarDesign_dominates :
    Dominates corankTwoPlanarDesign ({0, 1, 2} : Finset (Fin 6)) := by
  rw [Dominates, corankTwoPlanarDesign_gap]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_smul_atomMatrix 3 ![0, 0, 1]),
      fun y => ?_⟩
  rw [star_trivial, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm]
  nlinarith [sq_nonneg ((![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ y)]

/-- **The complement is refused, so the landed threshold is silent here.**  The
outside atoms are planar: the complement's gap-direction mass is zero, and
`Gtz.not_posDef_gap_of_uMass_le` refuses `{3,4,5}` outright.  The landed
corank-two closer `Gtz.posDef_compl_of_rankOneGap_of_threshold` therefore
cannot decide this fixture. -/
theorem corankTwoPlanar_complement_refused :
    ¬ (subsetSum corankTwoPlanarDesign ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine not_posDef_gap_of_uMass_le corankTwoPlanarDesign _
    corankTwoPlanar_gapDir_unit ?_
  rw [show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [corankTwoPlanarDesign_atom, corankTwoPlanarAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **A one-shared triple dominates strictly.**  `{0,4,5}` shares exactly the
atom `0` with the dominator; its gap-direction mass is `16/9 > 1` and the
plane cover holds by the explicit sum of squares
`(7/9)·G − cross² = (8/9)·(2w₀² + (2w₀ − w₁)² + 2w₁²)`.  The split criterion
fires where every landed instrument is silent. -/
theorem corankTwoPlanar_oneShared_strict :
    (subsetSum corankTwoPlanarDesign ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine (posDef_gap_iff_uSplit corankTwoPlanarDesign _
    corankTwoPlanar_gapDir_unit).mpr ⟨?_, fun w hw hwne => ?_⟩
  · rw [show ({0, 4, 5} : Finset (Fin 6)) = insert 0 (insert 4 {5}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [corankTwoPlanarDesign_atom, corankTwoPlanarAtom, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · have hw2 : w 2 = 0 := by
      have h := hw
      simp [dotProduct, Fin.sum_univ_three] at h
      exact h
    have hne01 : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hwne (funext fun i => ?_)
      fin_cases i
      · exact hcon.1
      · exact hcon.2
      · exact hw2
    simp only [show ({0, 4, 5} : Finset (Fin 6)) = insert 0 (insert 4 {5}) from rfl,
      Finset.sum_insert (by decide : (0 : Fin 6) ∉ (insert 4 {5} : Finset (Fin 6))),
      Finset.sum_insert (by decide : (4 : Fin 6) ∉ ({5} : Finset (Fin 6))),
      Finset.sum_singleton, corankTwoPlanarDesign_atom, corankTwoPlanarAtom,
      dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [hw2]
    have hpos : 0 < w 0 ^ 2 + w 1 ^ 2 := by
      rcases hne01 with h0 | h1
      · positivity
      · positivity
    nlinarith [sq_nonneg (2 * w 0 - w 1), sq_nonneg (w 0), sq_nonneg (w 1),
      sq_nonneg (w 0 + 2 * w 1), sq_nonneg (2 * w 0 + w 1), sq_nonneg (w 0 - w 1)]

/-- **The fixture is not a tie**, and only the one-shared instrument can tell:
the swaps are informationless at a rank-one gap, and the complement is
refused. -/
theorem corankTwoPlanar_not_isTie : ¬ IsTie corankTwoPlanarDesign := fun htie =>
  htie.2 ({0, 4, 5} : Finset (Fin 6)) (by decide) corankTwoPlanar_oneShared_strict

end Gtz

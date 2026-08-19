import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Wave.CorankTwoClosure
import Gtz.Design.LineClassObstructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The non-planar corank-two fixture

An exact rational `(6,3)` design for the non-planar corner of the corank-two
arm: the dominator `{0,1,2}` carries the rank-one gap `3 • atomMatrix ![0,0,1]`
EXACTLY (the same inside frame as `Gtz.corankTwoPlanarDesign`), two outside
atoms are planar, and the third outside atom `(5,-6,1)` reads the gap
direction at `1 ≠ 0`.  The corner hypotheses of the non-planar closure are
inhabited in exact rational arithmetic.

The design is NOT a tie: the one-shared triple `{0,4,5}` dominates strictly,
certified through the three-invariant criterion
(`Gtz.subsetSum_posDef_iff_tripleInvariants`) by three rational comparisons —
no witness direction, no eigenvalue.

The fixture also calibrates the identity layer: the planar corner's weight
rigidity (`t_e = 1/(1+lam)` at every inside atom) fails here in the exact
direction `Gtz.exists_inside_deficit_of_nonplanar` predicts — the inside
weight `t_0 = 97/420` satisfies `(1+lam)·t_0 = 97/105 < 1` at `lam = 3`.
The full exact calibration of every block identity at this fixture is
recorded in the campaign log.
-/

namespace Gtz

open Matrix Finset

/-- The six atoms: the planar fixture's inside frame, two planar outside
atoms, and the off-plane outside atom `(5,-6,1)`. -/
noncomputable def corankTwoNonplanarAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![1 / 3, 2 / 3, -(4 / 3)]
  | 1 => ![2 / 3, 1 / 3, 4 / 3]
  | 2 => ![2 / 3, -(2 / 3), -(2 / 3)]
  | 3 => ![1, 2, 0]
  | 4 => ![2, 1, 0]
  | 5 => ![5, -6, 1]

/-- The six weights: the exact rational Parseval solution at the tilted
outside atom. -/
noncomputable def corankTwoNonplanarWeight : Fin 6 → ℝ
  | 0 => 97 / 420
  | 1 => 5 / 21
  | 2 => 37 / 105
  | 3 => 17 / 252
  | 4 => 32 / 315
  | 5 => 1 / 105

/-- **The non-planar fixture.**  An exact rational `(6,3)` design whose
dominator `{0,1,2}` carries the rank-one gap `3 • atomMatrix ![0,0,1]` with
one outside atom off the gap plane. -/
noncomputable def corankTwoNonplanarDesign : WeightedDesign 6 3 where
  atom := corankTwoNonplanarAtom
  weight := corankTwoNonplanarWeight
  weight_pos := by
    intro label
    fin_cases label <;> norm_num [corankTwoNonplanarWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [corankTwoNonplanarWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [corankTwoNonplanarAtom, corankTwoNonplanarWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem corankTwoNonplanarDesign_atom :
    corankTwoNonplanarDesign.atom = corankTwoNonplanarAtom := rfl

theorem corankTwoNonplanarDesign_weight :
    corankTwoNonplanarDesign.weight = corankTwoNonplanarWeight := rfl

/-- **The rank-one gap, exactly.**  `S_{0,1,2} − 1 = 3 • atomMatrix ![0,0,1]`:
the fixture inhabits the corank-two hypothesis with `lam = 3` and the third
axis as gap direction. -/
theorem corankTwoNonplanarDesign_gap :
    subsetSum corankTwoNonplanarDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = (3 : ℝ) • atomMatrix (![0, 0, 1] : Fin 3 → ℝ) := by
  rw [subsetSum,
    show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [corankTwoNonplanarDesign_atom, corankTwoNonplanarAtom,
      atomMatrix, Matrix.cons_val_two]

/-- **The corner is non-planar.**  The outside atom `5` reads the gap
direction at `1 ≠ 0`. -/
theorem corankTwoNonplanar_offPlane_witness :
    corankTwoNonplanarDesign.atom 5 ⬝ᵥ (![0, 0, 1] : Fin 3 → ℝ) = 1 := by
  norm_num [corankTwoNonplanarDesign_atom, corankTwoNonplanarAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- The off-plane atom lives outside the dominator. -/
theorem corankTwoNonplanar_offPlane_mem :
    (5 : Fin 6) ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ := by decide

/-- **A one-shared triple dominates strictly**, by the three-invariant
criterion: `e₁ = 199/3`, `e₂ = 2695/9`, `e₃ = 308/3`, all positive in exact
rational arithmetic. -/
theorem corankTwoNonplanar_oneShared_strict :
    (subsetSum corankTwoNonplanarDesign ({0, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  refine (subsetSum_posDef_iff_tripleInvariants corankTwoNonplanarDesign
    0 4 5 (by decide) (by decide) (by decide)).mpr ⟨?_, ?_, ?_⟩ <;>
    norm_num [tripleLeverageSum, triplePairAreaSum, atomBracket,
      crossNormSq, bracketNormal, leverageOf, tripleBracket_eq,
      corankTwoNonplanarDesign_atom, corankTwoNonplanarAtom, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two]

/-- **The fixture is not a tie.** -/
theorem corankTwoNonplanar_not_isTie : ¬ IsTie corankTwoNonplanarDesign :=
  fun htie => htie.2 ({0, 4, 5} : Finset (Fin 6)) (by decide)
    corankTwoNonplanar_oneShared_strict

/-- **The planar weight rigidity fails here, exactly as predicted.**  The
inside weight `t_0` satisfies `(1+lam)·t_0 = 97/105 < 1`: the non-planar
deficit of `Gtz.exists_inside_deficit_of_nonplanar` is inhabited. -/
theorem corankTwoNonplanar_inside_deficit :
    (1 + 3 : ℝ) * corankTwoNonplanarDesign.weight 0 < 1 := by
  norm_num [corankTwoNonplanarDesign_weight, corankTwoNonplanarWeight]

end Gtz

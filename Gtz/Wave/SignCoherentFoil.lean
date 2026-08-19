import Gtz.Wave.CornerSignMatching
import Gtz.Design.KFourBandAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# An exact non-planar corner on the coherent horn

`Gtz.corner_signWord_dichotomy` splits a corank-two corner into the
opposite-sign horn, where the bracket floor fires, and the coherent horn, where
every outside atom is coplanar with an inside pair.  This module settles the
status of the coherent horn with one exact rational design: it is INHABITED, it
is inhabited PRIMITIVELY, and it is inhabited inside the NON-PLANAR corner
hypothesis that blocks the campaign.  So the coherent horn cannot be emptied by
corner data alone; only the tie hypothesis can empty it.

## The foil

Six atoms, weights `(1/6, 1/4, 1/4, 1/6, 1/9, 1/18)`.  The dominator `{0,1,2}`
carries the rank-one gap `3 • atomMatrix ![0,0,1]`.  Each outside atom is
coplanar with one inside pair — the matching of
`Gtz.corner_matching_of_signCoherent` realized with brackets
`[g₁g₂g₃] = [g₀g₂g₄] = [g₀g₁g₅] = 0` — and all three outside axis readings are
`±2/3 ≠ 0`, so the corner is non-planar.  The base minor patterns are
`(4,0,0)`, `(0,12,0)`, `(0,0,12)`: one strictly positive minor per base, signs
coherent with the pairings `(2/3, 4/3, 2/3)`, and the matching quantization of
`Gtz.corner_matching_quantization` holds on the nose:
`(1/6)·4 = 2/3`, `(1/9)·12 = 4/3`, `(1/18)·12 = 2/3`.

The foil is NOT a tie: `{2,4,5}` dominates strictly, with leading minors
`5`, `419/9`, `176/3`.  That is the point — the coherent horn contains
primitive non-planar corners of non-ties, so a closing certificate for the
corner must consume the refusals on this horn and not only its geometry.
-/

namespace Gtz

open Matrix Finset

namespace SignCoherentFoil

/-- The six atoms of the foil. -/
noncomputable def atomFn : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1 / 3, 2 / 3, 4 / 3]
  | 1 => ![2 / 3, -(2 / 3), 2 / 3]
  | 2 => ![-(2 / 3), -(1 / 3), 4 / 3]
  | 3 => ![4 / 3, -(1 / 3), -(2 / 3)]
  | 4 => ![5 / 3, 11 / 6, 2 / 3]
  | 5 => ![-(5 / 3), 8 / 3, -(2 / 3)]

/-- The six weights of the foil. -/
noncomputable def weightFn : Fin 6 → ℝ
  | 0 => 1 / 6
  | 1 => 1 / 4
  | 2 => 1 / 4
  | 3 => 1 / 6
  | 4 => 1 / 9
  | 5 => 1 / 18

/-- The gap axis of the corner. -/
def axisVec : Fin 3 → ℝ := ![0, 0, 1]

end SignCoherentFoil

open SignCoherentFoil

/-- **The foil.**  An exact rational `(6,3)` design with a non-planar
corank-two corner at `{0,1,2}` on the coherent horn of the sign-word
dichotomy. -/
noncomputable def signCoherentFoil : WeightedDesign 6 3 where
  atom := atomFn
  weight := weightFn
  weight_pos := by
    intro c
    fin_cases c <;> norm_num [weightFn]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [weightFn]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [atomFn, weightFn, atomMatrix, Matrix.cons_val_two] <;> norm_num

theorem signCoherentFoil_atom : signCoherentFoil.atom = atomFn := rfl

theorem signCoherentFoil_weight : signCoherentFoil.weight = weightFn := rfl

/-! ## 1. The corner -/

/-- The rank-one gap: `S_{0,1,2} − 1 = 3 • atomMatrix ![0,0,1]`. -/
theorem signCoherentFoil_corner :
    subsetSum signCoherentFoil ({0, 1, 2} : Finset (Fin 6)) - 1
      = (3 : ℝ) • atomMatrix axisVec := by
  have hsum : subsetSum signCoherentFoil ({0, 1, 2} : Finset (Fin 6))
      = atomMatrix (signCoherentFoil.atom 0) + atomMatrix (signCoherentFoil.atom 1)
        + atomMatrix (signCoherentFoil.atom 2) := by
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    abel
  rw [hsum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signCoherentFoil_atom, atomFn, axisVec, atomMatrix, Matrix.cons_val_two]

/-- The gap axis is a unit vector. -/
theorem signCoherentFoil_axis_unit : axisVec ⬝ᵥ axisVec = 1 := by
  norm_num [axisVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-! ## 2. The matching coplanarities and the non-planarity -/

/-- Each outside atom is coplanar with one inside pair: the matching pattern. -/
theorem signCoherentFoil_coplanar :
    atomBracket signCoherentFoil 1 2 3 = 0
      ∧ atomBracket signCoherentFoil 0 2 4 = 0
      ∧ atomBracket signCoherentFoil 0 1 5 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
      Matrix.cons_val_two]

/-- The corner is NON-planar: the first outside atom reads the gap axis as
`−2/3`. -/
theorem signCoherentFoil_nonplanar :
    signCoherentFoil.atom 3 ⬝ᵥ axisVec = -(2 / 3) := by
  norm_num [signCoherentFoil_atom, atomFn, axisVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-! ## 3. The pairings and the minor patterns -/

/-- The three inside pairings, all nonzero. -/
theorem signCoherentFoil_pairings :
    atomPairing signCoherentFoil 0 1 = 2 / 3
      ∧ atomPairing signCoherentFoil 0 2 = 4 / 3
      ∧ atomPairing signCoherentFoil 1 2 = 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [atomPairing, signCoherentFoil_atom, atomFn, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two]

/-- The base-`0` outside mixed minors: `(4, 0, 0)`. -/
theorem signCoherentFoil_base0_minors :
    atomBracket signCoherentFoil 0 1 3 * atomBracket signCoherentFoil 0 2 3 = 4
      ∧ atomBracket signCoherentFoil 0 1 4 * atomBracket signCoherentFoil 0 2 4 = 0
      ∧ atomBracket signCoherentFoil 0 1 5 * atomBracket signCoherentFoil 0 2 5 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
      Matrix.cons_val_two]

/-- The base-`1` outside mixed minors: `(0, 12, 0)`. -/
theorem signCoherentFoil_base1_minors :
    atomBracket signCoherentFoil 1 0 3 * atomBracket signCoherentFoil 1 2 3 = 0
      ∧ atomBracket signCoherentFoil 1 0 4 * atomBracket signCoherentFoil 1 2 4 = 12
      ∧ atomBracket signCoherentFoil 1 0 5 * atomBracket signCoherentFoil 1 2 5 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
      Matrix.cons_val_two]

/-- The base-`2` outside mixed minors: `(0, 0, 12)`. -/
theorem signCoherentFoil_base2_minors :
    atomBracket signCoherentFoil 2 0 3 * atomBracket signCoherentFoil 2 1 3 = 0
      ∧ atomBracket signCoherentFoil 2 0 4 * atomBracket signCoherentFoil 2 1 4 = 0
      ∧ atomBracket signCoherentFoil 2 0 5 * atomBracket signCoherentFoil 2 1 5 = 12 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
      Matrix.cons_val_two]

/-! ## 4. Sign coherence: no base has an opposite-sign pair -/

/-- Base `0` is sign-coherent. -/
theorem signCoherentFoil_coherent_base0 :
    ∀ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, ∀ d' ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
      0 ≤ (atomBracket signCoherentFoil 0 1 d * atomBracket signCoherentFoil 0 2 d)
        * (atomBracket signCoherentFoil 0 1 d' * atomBracket signCoherentFoil 0 2 d') := by
  intro d hd d' hd'
  fin_cases d <;> fin_cases d' <;>
    first
      | exact absurd hd (by decide)
      | exact absurd hd' (by decide)
      | norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
          Matrix.cons_val_two]

/-- Base `1` is sign-coherent. -/
theorem signCoherentFoil_coherent_base1 :
    ∀ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, ∀ d' ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
      0 ≤ (atomBracket signCoherentFoil 1 0 d * atomBracket signCoherentFoil 1 2 d)
        * (atomBracket signCoherentFoil 1 0 d' * atomBracket signCoherentFoil 1 2 d') := by
  intro d hd d' hd'
  fin_cases d <;> fin_cases d' <;>
    first
      | exact absurd hd (by decide)
      | exact absurd hd' (by decide)
      | norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
          Matrix.cons_val_two]

/-- Base `2` is sign-coherent. -/
theorem signCoherentFoil_coherent_base2 :
    ∀ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, ∀ d' ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
      0 ≤ (atomBracket signCoherentFoil 2 0 d * atomBracket signCoherentFoil 2 1 d)
        * (atomBracket signCoherentFoil 2 0 d' * atomBracket signCoherentFoil 2 1 d') := by
  intro d hd d' hd'
  fin_cases d <;> fin_cases d' <;>
    first
      | exact absurd hd (by decide)
      | exact absurd hd' (by decide)
      | norm_num [atomBracket, tripleBracket_eq, signCoherentFoil_atom, atomFn,
          Matrix.cons_val_two]

/-! ## 5. The quantization, on the nose -/

/-- The matching quantization of the three transports, exactly:
`(1/6)·4 = 2/3`, `(1/9)·12 = 4/3`, `(1/18)·12 = 2/3`. -/
theorem signCoherentFoil_quantized :
    signCoherentFoil.weight 3
        * (atomBracket signCoherentFoil 0 1 3 * atomBracket signCoherentFoil 0 2 3)
        = atomPairing signCoherentFoil 1 2
      ∧ signCoherentFoil.weight 4
        * (atomBracket signCoherentFoil 1 0 4 * atomBracket signCoherentFoil 1 2 4)
        = atomPairing signCoherentFoil 0 2
      ∧ signCoherentFoil.weight 5
        * (atomBracket signCoherentFoil 2 0 5 * atomBracket signCoherentFoil 2 1 5)
        = atomPairing signCoherentFoil 0 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [atomBracket, tripleBracket_eq, atomPairing, dotProduct, Fin.sum_univ_three,
      signCoherentFoil_atom, signCoherentFoil_weight, atomFn, weightFn,
      Matrix.cons_val_two]

/-! ## 6. The foil is primitive and is not a tie -/

/-- No two atoms are parallel. -/
theorem isPrimitiveDesign_signCoherentFoil : IsPrimitiveDesign signCoherentFoil := by
  intro keptLabel dropLabel ratio hne hparallel
  have hcomponents : ∀ coordinate : Fin 3,
      atomFn dropLabel coordinate = ratio * atomFn keptLabel coordinate := by
    intro coordinate
    simpa [signCoherentFoil_atom, Pi.smul_apply, smul_eq_mul] using
      congrFun hparallel coordinate
  have hzero := hcomponents 0
  have hone := hcomponents 1
  have htwo := hcomponents 2
  clear hcomponents hparallel
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    [skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip;
      skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip; skip;
      skip; skip; skip; skip; skip; skip; skip; skip] <;>
  · first
    | exact hne rfl
    | (simp only [atomFn, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo
       linarith)

/-- The triple `{2,4,5}` dominates strictly: leading minors `5`, `419/9`,
`176/3`. -/
theorem signCoherentFoil_dominator :
    (subsetSum signCoherentFoil ({2, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  have hsum : subsetSum signCoherentFoil ({2, 4, 5} : Finset (Fin 6))
      = atomMatrix (signCoherentFoil.atom 2) + atomMatrix (signCoherentFoil.atom 4)
        + atomMatrix (signCoherentFoil.atom 5) := by
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    abel
  have hgap : subsetSum signCoherentFoil ({2, 4, 5} : Finset (Fin 6)) - 1
      = !![5, -(7/6), 4/3; -(7/6), 115/12, -1; 4/3, -1, 5/3] := by
    rw [hsum]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signCoherentFoil_atom, atomFn, atomMatrix, Matrix.cons_val_two]
  rw [hgap, posDef_finThree_iff_leadingMinors _ (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const])]
  norm_num [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]

/-- **The foil is not a tie.** -/
theorem signCoherentFoil_not_isTie : ¬ IsTie signCoherentFoil := by
  intro htie
  exact htie.2 ({2, 4, 5} : Finset (Fin 6)) (by decide) signCoherentFoil_dominator

/-! ## 7. The inhabitation -/

/-- **THE COHERENT HORN IS INHABITED, PRIMITIVELY AND NON-PLANARLY.**  A
primitive `(6,3)` design that is not a tie carries a corank-two corner with a
positive gap scale, a non-planar outside atom, and full sign coherence at all
three bases.  So the coherent horn of `Gtz.corner_signWord_dichotomy` cannot
be emptied from the corner data alone: a closing certificate must consume the
ten refusals on this horn. -/
theorem signCoherent_nonplanar_corner_inhabited :
    ∃ D : WeightedDesign 6 3, IsPrimitiveDesign D ∧ ¬ IsTie D
      ∧ subsetSum D ({0, 1, 2} : Finset (Fin 6)) - 1 = (3 : ℝ) • atomMatrix axisVec
      ∧ (∃ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, D.atom d ⬝ᵥ axisVec ≠ 0)
      ∧ (∀ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, ∀ d' ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
          0 ≤ (atomBracket D 0 1 d * atomBracket D 0 2 d)
            * (atomBracket D 0 1 d' * atomBracket D 0 2 d'))
      ∧ (∀ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, ∀ d' ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
          0 ≤ (atomBracket D 1 0 d * atomBracket D 1 2 d)
            * (atomBracket D 1 0 d' * atomBracket D 1 2 d'))
      ∧ (∀ d ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ, ∀ d' ∈ ({0, 1, 2} : Finset (Fin 6))ᶜ,
          0 ≤ (atomBracket D 2 0 d * atomBracket D 2 1 d)
            * (atomBracket D 2 0 d' * atomBracket D 2 1 d')) :=
  ⟨signCoherentFoil, isPrimitiveDesign_signCoherentFoil, signCoherentFoil_not_isTie,
    signCoherentFoil_corner,
    ⟨3, by decide, by rw [signCoherentFoil_nonplanar]; norm_num⟩,
    signCoherentFoil_coherent_base0, signCoherentFoil_coherent_base1,
    signCoherentFoil_coherent_base2⟩

end Gtz

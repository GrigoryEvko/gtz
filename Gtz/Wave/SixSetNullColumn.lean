/-
# The null column of the six-set projection: the touching eigenvector of a
# corank-one dominator, exactly

The six-set gap `W = S_univ − 1` is positive definite at every design
(`Gtz.sixSetGap_posDef`), and the sibling projection program reads every
refusal of a `(6,3)` tie as a spectral condition on a complementary block of
the pivot matrix `P_{ab} = g_aᵀ W⁻¹ g_b`.  This module gives the corank-one
arm its distinguished structure inside that arena.

## The laws

At a weak dominator `C` whose gap form kills `w`:

* `Gtz.sixSetGap_mulVec_nullDir` — `W *ᵥ w = S_{Cᶜ} *ᵥ w`: the six-set gap
  maps the null direction into the complement's atom sum, because the
  dominator's gap annihilates it;
* `Gtz.nullDir_sixSet_resolve` — `w = Σ_{d∈Cᶜ} (q_d·w) • (W⁻¹ *ᵥ q_d)`: the
  null direction RESOLVES through the complement in the `W⁻¹` metric — the
  six-set mirror of the landed inside resolve
  `Gtz.dominator_resolves_nullDir`;
* `Gtz.nullReading_pivot_column_identity` — for EVERY atom `a`:
  `Σ_{d∈Cᶜ} P_{ad} (q_d·w) = g_a·w`: the complement columns of the pivot
  matrix fix the whole null-reading vector;
* `Gtz.nullReading_touching_eigenvector` — restricted to `a ∈ Cᶜ` this says
  the outside null-reading vector is a `+1`-eigenvector of the complement
  block: THE TOUCHING EIGENVECTOR OF THE WEAK DOMINATOR, EXPLICITLY.  The
  tie's refusal of `Cᶜ` demands `λmax(P[Cᶜ]) ≥ 1`; weak domination caps the
  block at `I`; this law exhibits the contact eigenvector as the outside
  null readings — nonzero by the landed
  `Gtz.exists_compl_dotProduct_ne_zero_of_nullDirection`;
* `Gtz.sum_nullReading_pivot_pairing_eq_one` — the scalar trace of the
  contact: `Σ_{d∈Cᶜ} (q_d·w)·(wᵀW⁻¹q_d) = 1`.

## Why this is the assembly hook

The projection program's tie combinatorics lives on the twenty blocks of
`P`; the corank-one arm's calculus lives on the null readings.  These laws
identify the two at the dominator: the block that touches the unit sphere
touches it AT the null-reading vector.  A parallel pair is a singular 2×2
principal minor of `P`, and the doubled family realizes the contact with two
equal rows — the degeneration the rigidity fight must isolate.
-/
import Gtz.Wave.SixSetGapUniversal
import Gtz.Wave.SixSetProjection
import Gtz.Wave.CorankOneGramMirror

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **The six-set gap maps the null direction into the complement.**  The
dominator's gap annihilates `w`, so only the complement's atoms carry it. -/
theorem sixSetGap_mulVec_nullDir (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    (subsetSum D (Finset.univ : Finset (Fin m)) - 1) *ᵥ nullDir
      = subsetSum D Cᶜ *ᵥ nullDir := by
  have hker : (subsetSum D C - 1) *ᵥ nullDir = 0 :=
    mulVec_eq_zero_of_form_eq_zero hdominates
      (transpose_subsetSum_sub_one D C) hnull
  have hsplit : subsetSum D (Finset.univ : Finset (Fin m)) - 1
      = (subsetSum D C - 1) + subsetSum D Cᶜ := by
    rw [subsetSum_univ_split D C]
    abel
  rw [hsplit, Matrix.add_mulVec, hker, zero_add]

/-- **The null direction resolves through the complement in the `W⁻¹`
metric.**  The six-set mirror of the inside resolve identity. -/
theorem nullDir_sixSet_resolve (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ nullDir) •
        ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom d)
      = nullDir := by
  have hW := sixSetGap_posDef D hm
  have hdet : IsUnit (subsetSum D (Finset.univ : Finset (Fin m)) - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hW.det_pos)
  have hmap := sixSetGap_mulVec_nullDir D hdominates hnull
  have hout : subsetSum D Cᶜ *ᵥ nullDir
      = ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ nullDir) • D.atom d := by
    rw [subsetSum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun d _ => by
      rw [atomMatrix, vecMulVec_mulVec_eq]
  calc ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ nullDir) •
        ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom d)
      = (subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ
          (∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ nullDir) • D.atom d) := by
        rw [Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun d _ => by rw [Matrix.mulVec_smul]
    _ = (subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ
          ((subsetSum D (Finset.univ : Finset (Fin m)) - 1) *ᵥ nullDir) := by
        rw [← hout, hmap]
    _ = nullDir := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **The complement columns of the pivot matrix fix the null readings.**  For
every atom `a`, the `Cᶜ`-columns of `P` weighted by the outside null readings
reproduce `a`'s own null reading. -/
theorem nullReading_pivot_column_identity (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) (a : Fin m) :
    ∑ d ∈ Cᶜ, (D.atom a ⬝ᵥ
        ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom d))
        * (D.atom d ⬝ᵥ nullDir)
      = D.atom a ⬝ᵥ nullDir := by
  have hres := nullDir_sixSet_resolve D hm hdominates hnull
  have hdot := congrArg (fun v => D.atom a ⬝ᵥ v) hres
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul] at hdot
  rw [← hdot]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- **THE TOUCHING EIGENVECTOR.**  At a weak dominator with a null direction,
the outside null-reading vector is a `+1`-eigenvector of the complement block
of the pivot matrix: for every `e ∈ Cᶜ`,

  `Σ_{d∈Cᶜ} P_{ed} (q_d·w) = q_e·w` .

The block is capped at `I` by weak domination and must reach `1` at a tie;
this law says the contact happens exactly at the null readings, which do not
all vanish (`Gtz.exists_compl_dotProduct_ne_zero_of_nullDirection`). -/
theorem nullReading_touching_eigenvector (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    {e : Fin m} (_ : e ∈ Cᶜ) :
    ∑ d ∈ Cᶜ, (D.atom e ⬝ᵥ
        ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom d))
        * (D.atom d ⬝ᵥ nullDir)
      = D.atom e ⬝ᵥ nullDir :=
  nullReading_pivot_column_identity D hm hdominates hnull e

/-- **The scalar contact.**  Pairing the resolve with the null direction:
`Σ_{d∈Cᶜ} (q_d·w) · (wᵀ W⁻¹ q_d) = |w|²`.  At unit `w` the outside
null readings pair to exactly one against the pivot metric. -/
theorem sum_nullReading_pivot_pairing (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    ∑ d ∈ Cᶜ, (nullDir ⬝ᵥ
        ((subsetSum D (Finset.univ : Finset (Fin m)) - 1)⁻¹ *ᵥ D.atom d))
        * (D.atom d ⬝ᵥ nullDir)
      = nullDir ⬝ᵥ nullDir := by
  have hres := nullDir_sixSet_resolve D hm hdominates hnull
  have hdot := congrArg (fun v => nullDir ⬝ᵥ v) hres
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul] at hdot
  rw [← hdot]
  exact Finset.sum_congr rfl fun d _ => by ring

end Gtz

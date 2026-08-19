import Gtz.Wave.CornerRefusalCensus
import Gtz.Reduction.PolarDeletionWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The gap scale of a corank-two corner sits in a weight window

The corner normal form `S_C − 1 = lam·u uᵀ` carries one scalar, the GAP SCALE
`lam`.  Every landed corner law reads the pivot matrix and none of them prices
`lam` itself.  This module prices it, from Parseval alone, and finds it trapped
between two weight expressions.

## The ceiling

Parseval reads the gap direction with total one, `Σ_a t_a (g_a·u)² = 1`, while
the dominator reads it with total `1 + lam`
(`Gtz.inside_quadForm_of_rankOneGap` at `z = u`).  Dropping the outside atoms
and replacing every inside weight by a floor gives

  `t_min·(1 + lam) ≤ 1`   (`Gtz.corner_gapScale_le_of_weightFloor`),

with no tie hypothesis: **a light dominator forces a large gap scale, and a
heavy one forbids it.**

## The floor

The same Parseval split at an arbitrary direction, with the inside weights
replaced by a ceiling and the outside weights by a ceiling, gives the
QUANTITATIVE outside cover (`Gtz.outside_cover_quantitative`)

  `z·z ≤ ceilIn·(z·z) + ceilIn·lam·(u·z)² + ceilOut·Σ_{d∉C}(g_d·z)²` .

`Gtz.outside_plane_cover_of_rankOneGap` is the qualitative shadow of this
inequality on `u^⊥`; the inequality itself keeps the constant.  At a TIE the
complement triple refuses, so some direction has
`Σ_{d∉C}(g_d·z)² ≤ z·z`, and Cauchy–Schwarz caps `(u·z)²` by `z·z`.  Dividing by
`z·z > 0`:

  `1 ≤ ceilIn·(1 + lam) + ceilOut`   (`Gtz.corner_gapScale_floor_of_isTie`).

Since two atoms of a design never carry the whole weight
(`Gtz.weight_pair_lt_one`), the floor is strictly positive: at a corank-two
corner of a tie

  `1 − t_e − t_d ≤ t_e·lam`  for a heaviest inside atom `e` and a heaviest
outside atom `d`   (`Gtz.corner_gapScale_floor_concrete`),

so `lam > 0` with an explicit weight-carrying margin, and `lam → ∞` as the
heaviest inside weight goes to zero.  That is the exact shape the corner
obstruction has: it degenerates linearly at the weight floor, which is where the
`(5,3)` diamond sits.

## The window

Putting the two together (`Gtz.corner_gapScale_window`) traps the gap scale:

  `(1 − ceilIn − ceilOut)/ceilIn  ≤  lam  ≤  1/t_min − 1` .

Both ends are weights, and neither reads the pivot matrix.

## The refusals, priced

The census (`Gtz.strictDominator_inter_card_le_one`) leaves exactly ten triples
that can dominate strictly at a corner: the complement `Cᶜ` and the nine triples
with one inside atom and two outside ones.  The quantitative cover prices the
refusal of each.  For `Cᶜ` the refusal direction is pinned to the gap axis
(`Gtz.refusal_direction_axis_floor`)

  `(1 − ceilIn − ceilOut)·(z·z) ≤ ceilIn·lam·(u·z)²` ,

which sharpens `Gtz.refusal_reads_axis` from "not orthogonal to `u`" to an
explicit angle.  For the nine one-inside triples
(`Gtz.swapRefusal_axis_bound`, `Gtz.exists_swapRefusal_bound`)

  `(1 − ceilIn − ceilOut)·(z·z) + ceilOut·(g_e·z)²
      ≤ ceilIn·lam·(u·z)² + ceilOut·(g_d·z)²` ,

so the inside atom the triple carries never reads harder than the outside atom
it drops, up to the axis term and the free mass `1 − ceilIn − ceilOut`.  Those
ten inequalities are the whole quantitative content of a tie at a corank-two
corner.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The weighted reading total -/

/-- **Parseval as a reading total.**  The weighted squared readings of any
direction sum to its own square norm. -/
theorem sum_weight_read_sq (D : WeightedDesign m 3) (z : Fin 3 → ℝ) :
    ∑ a, D.weight a * (D.atom a ⬝ᵥ z) ^ 2 = z ⬝ᵥ z := by
  have hform : z ⬝ᵥ ((∑ a, D.weight a • atomMatrix (D.atom a)) *ᵥ z)
      = ∑ a, D.weight a * (D.atom a ⬝ᵥ z) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      show atomMatrix (D.atom a) = Matrix.vecMulVec (D.atom a) (D.atom a) from rfl,
      quadForm_atomMatrix]
  rw [D.isParseval, Matrix.one_mulVec] at hform
  exact hform.symm

/-! ## 2. The ceiling on the gap scale -/

/-- **A weight floor on the dominator caps the gap scale.**  The inside atoms
read the gap direction with total `1 + lam`, and Parseval caps their weighted
total by one. -/
theorem corner_gapScale_le_of_weightFloor (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {weightFloor : ℝ} (hfloor : ∀ e ∈ C, weightFloor ≤ D.weight e) :
    weightFloor * (1 + lam) ≤ 1 := by
  classical
  have htotal := sum_weight_read_sq D u
  have hinside := inside_quadForm_of_rankOneGap D C hgap u
  rw [hunit] at hinside
  norm_num at hinside
  have h1 : ∑ e ∈ C, weightFloor * (D.atom e ⬝ᵥ u) ^ 2
      ≤ ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ u) ^ 2 :=
    Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_right (hfloor e he) (sq_nonneg _)
  have h2 : ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ u) ^ 2
      ≤ ∑ a, D.weight a * (D.atom a ⬝ᵥ u) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
      (fun a _ _ => mul_nonneg (D.weight_pos a).le (sq_nonneg _))
  rw [← Finset.mul_sum, hinside] at h1
  rw [htotal, hunit] at h2
  linarith

/-! ## 3. The quantitative outside cover -/

/-- **The outside cover, with its constant.**  Replacing the inside weights by a
ceiling and the outside weights by a ceiling turns the Parseval split into an
inequality that keeps track of both.  `Gtz.outside_plane_cover_of_rankOneGap` is
its qualitative shadow at `u ⬝ᵥ z = 0`. -/
theorem outside_cover_quantitative (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {ceilIn ceilOut : ℝ} (hIn : ∀ e ∈ C, D.weight e ≤ ceilIn)
    (hOut : ∀ d ∈ Cᶜ, D.weight d ≤ ceilOut) (z : Fin 3 → ℝ) :
    z ⬝ᵥ z ≤ ceilIn * (z ⬝ᵥ z) + ceilIn * (lam * (u ⬝ᵥ z) ^ 2)
      + ceilOut * ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ z) ^ 2 := by
  classical
  have htotal := sum_weight_read_sq D z
  have hsplit := Finset.sum_add_sum_compl C (fun a => D.weight a * (D.atom a ⬝ᵥ z) ^ 2)
  have hinside := inside_quadForm_of_rankOneGap D C hgap z
  have h1 : ∑ e ∈ C, D.weight e * (D.atom e ⬝ᵥ z) ^ 2
      ≤ ceilIn * ∑ e ∈ C, (D.atom e ⬝ᵥ z) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_right (hIn e he) (sq_nonneg _)
  have h2 : ∑ d ∈ Cᶜ, D.weight d * (D.atom d ⬝ᵥ z) ^ 2
      ≤ ceilOut * ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ z) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_right (hOut d hd) (sq_nonneg _)
  rw [hinside, mul_add] at h1
  linarith

/-! ## 4. The floor on the gap scale at a tie -/

/-- **A tie floors the gap scale.**  The complement triple of a corank-two corner
refuses, so some direction reads the outside atoms below its own square norm, and
the quantitative cover then prices the gap scale from below. -/
theorem corner_gapScale_floor_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    (C : Finset (Fin m)) (hcompl : (Cᶜ).card = 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {ceilIn ceilOut : ℝ} (hIn : ∀ e ∈ C, D.weight e ≤ ceilIn)
    (hOut : ∀ d ∈ Cᶜ, D.weight d ≤ ceilOut) (hIn0 : 0 ≤ ceilIn) :
    1 ≤ ceilIn * (1 + lam) + ceilOut := by
  classical
  obtain ⟨z, hz, hread⟩ := exists_refusal_direction D Cᶜ (htie.2 Cᶜ hcompl)
  have hpos : 0 < z ⬝ᵥ z := dotProduct_self_pos hz
  have hquad := subsetSum_quadForm_eq_sum_sq D Cᶜ z
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hquad] at hread
  have hcover := outside_cover_quantitative D C hgap hIn hOut z
  have hcs : (u ⬝ᵥ z) ^ 2 ≤ z ⬝ᵥ z := by
    have h := dotProduct_sq_le_mul u z
    rwa [hunit, one_mul] at h
  have hstep1 : ceilIn * (lam * (u ⬝ᵥ z) ^ 2) ≤ ceilIn * (lam * (z ⬝ᵥ z)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs hlam) hIn0
  have hstep2 : ceilOut * ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ z) ^ 2 ≤ ceilOut * (z ⬝ᵥ z) := by
    refine mul_le_mul_of_nonneg_left (by linarith) ?_
    obtain ⟨d0, hd0⟩ := Finset.card_pos.mp (by omega : 0 < (Cᶜ : Finset (Fin m)).card)
    exact le_trans (D.weight_pos d0).le (hOut d0 hd0)
  have hmain : 1 * (z ⬝ᵥ z) ≤ (ceilIn * (1 + lam) + ceilOut) * (z ⬝ᵥ z) := by nlinarith
  exact le_of_mul_le_mul_right hmain hpos

/-! ## 5. The window -/

/-- **The gap scale window.**  At a corank-two corner of a tie the gap scale sits
between two weight expressions, and nothing in either end reads the pivot
matrix. -/
theorem corner_gapScale_window (D : WeightedDesign m 3) (htie : IsTie D)
    (C : Finset (Fin m)) (hcompl : (Cᶜ).card = 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {weightFloor ceilIn ceilOut : ℝ} (hfloor : ∀ e ∈ C, weightFloor ≤ D.weight e)
    (hIn : ∀ e ∈ C, D.weight e ≤ ceilIn) (hOut : ∀ d ∈ Cᶜ, D.weight d ≤ ceilOut)
    (hIn0 : 0 ≤ ceilIn) :
    1 - ceilIn - ceilOut ≤ ceilIn * lam ∧ weightFloor * (1 + lam) ≤ 1 := by
  refine ⟨?_, corner_gapScale_le_of_weightFloor D C hunit hgap hfloor⟩
  have h := corner_gapScale_floor_of_isTie D htie C hcompl hlam hunit hgap hIn hOut hIn0
  nlinarith [h]

/-- **The gap scale of a corner of a tie is strictly positive, with a weight
margin.**  A heaviest inside atom and a heaviest outside atom never carry the
whole weight, so the floor is strictly positive.  The margin degenerates exactly
when one of the two weights approaches its own bound. -/
theorem corner_gapScale_floor_concrete (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∃ e ∈ C, ∃ d ∈ Cᶜ, 0 < 1 - D.weight e - D.weight d
      ∧ 1 - D.weight e - D.weight d ≤ D.weight e * lam := by
  classical
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]; simp
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  have hDne : (Cᶜ : Finset (Fin 6)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨eStar, heStar, hemax⟩ := C.exists_max_image D.weight hCne
  obtain ⟨dStar, hdStar, hdmax⟩ := Cᶜ.exists_max_image D.weight hDne
  have hne : eStar ≠ dStar := by
    intro heq
    rw [Finset.mem_compl] at hdStar
    exact hdStar (heq ▸ heStar)
  have hpair : D.weight eStar + D.weight dStar < 1 :=
    weight_pair_lt_one D hne (by norm_num)
  refine ⟨eStar, heStar, dStar, hdStar, by linarith, ?_⟩
  have h := corner_gapScale_floor_of_isTie D htie C hcompl hlam hunit hgap hemax hdmax
    (D.weight_pos eStar).le
  nlinarith [h]


/-! ## 6. The refusal direction is pinned to the gap axis -/

/-- **The refusal direction of the complement triple is pinned to the gap axis,
quantitatively.**  `Gtz.refusal_reads_axis` says such a direction is not
orthogonal to `u`; this gives the angle an explicit weight-carrying floor. -/
theorem refusal_direction_axis_floor (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {ceilIn ceilOut : ℝ} (hIn : ∀ e ∈ C, D.weight e ≤ ceilIn)
    (hOut : ∀ d ∈ Cᶜ, D.weight d ≤ ceilOut) (hOut0 : 0 ≤ ceilOut)
    {z : Fin 3 → ℝ} (hread : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0) :
    (1 - ceilIn - ceilOut) * (z ⬝ᵥ z) ≤ ceilIn * (lam * (u ⬝ᵥ z) ^ 2) := by
  have hquad := subsetSum_quadForm_eq_sum_sq D Cᶜ z
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hquad] at hread
  have hcover := outside_cover_quantitative D C hgap hIn hOut z
  have hstep : ceilOut * ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ z) ^ 2 ≤ ceilOut * (z ⬝ᵥ z) :=
    mul_le_mul_of_nonneg_left (by linarith) hOut0
  nlinarith [hcover, hstep]

/-! ## 7. The nine surviving refusals, priced -/

/-- **The quadratic form of a one-inside triple.**  Trading the outside atom `d`
for the inside atom `e` moves the complement's reading by exactly those two
atoms. -/
theorem swapTriple_quadForm (D : WeightedDesign m 3) (C : Finset (Fin m))
    {e d : Fin m} (he : e ∈ C) (hd : d ∈ Cᶜ) (z : Fin 3 → ℝ) :
    ∑ a ∈ insert e (Cᶜ.erase d), (D.atom a ⬝ᵥ z) ^ 2
      = ∑ a ∈ Cᶜ, (D.atom a ⬝ᵥ z) ^ 2 + (D.atom e ⬝ᵥ z) ^ 2 - (D.atom d ⬝ᵥ z) ^ 2 := by
  classical
  have heout : e ∉ (Cᶜ : Finset (Fin m)) := by simpa using he
  have hswap := subsetSum_swap D Cᶜ hd heout
  have hform := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => z ⬝ᵥ (M *ᵥ z)) hswap
  simp only [Matrix.add_mulVec, dotProduct_add] at hform
  rw [subsetSum_quadForm_eq_sum_sq, subsetSum_quadForm_eq_sum_sq,
    show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
    show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e) from rfl,
    quadForm_atomMatrix, quadForm_atomMatrix] at hform
  linarith

/-- **Each surviving refusal prices one inside reading against one outside
reading.**  At a corank-two corner the only triples that can dominate strictly
carry one inside atom and two outside ones (`Gtz.strictDominator_inter_card_le_one`).
A direction where such a triple refuses obeys an explicit weight inequality: the
inside atom it carries reads no harder than the outside atom it drops, up to the
axis term and the free mass. -/
theorem swapRefusal_axis_bound (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {ceilIn ceilOut : ℝ} (hIn : ∀ c ∈ C, D.weight c ≤ ceilIn)
    (hOut : ∀ c ∈ Cᶜ, D.weight c ≤ ceilOut) (hOut0 : 0 ≤ ceilOut)
    {e d : Fin m} (he : e ∈ C) (hd : d ∈ Cᶜ) {z : Fin 3 → ℝ}
    (hread : z ⬝ᵥ ((subsetSum D (insert e (Cᶜ.erase d)) - 1) *ᵥ z) ≤ 0) :
    (1 - ceilIn - ceilOut) * (z ⬝ᵥ z) + ceilOut * (D.atom e ⬝ᵥ z) ^ 2
      ≤ ceilIn * (lam * (u ⬝ᵥ z) ^ 2) + ceilOut * (D.atom d ⬝ᵥ z) ^ 2 := by
  classical
  have hquad := subsetSum_quadForm_eq_sum_sq D (insert e (Cᶜ.erase d)) z
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hquad,
    swapTriple_quadForm D C he hd z] at hread
  have hcover := outside_cover_quantitative D C hgap hIn hOut z
  have hstep : ceilOut * ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ z) ^ 2
      ≤ ceilOut * ((z ⬝ᵥ z) - (D.atom e ⬝ᵥ z) ^ 2 + (D.atom d ⬝ᵥ z) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hOut0
  nlinarith [hcover, hstep]

/-- **A tie supplies the direction.**  At a corank-two corner of a `(6,3)` tie
every one of the nine one-inside triples refuses, so each carries a direction
where the weight inequality binds. -/
theorem exists_swapRefusal_bound (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {ceilIn ceilOut : ℝ} (hIn : ∀ c ∈ C, D.weight c ≤ ceilIn)
    (hOut : ∀ c ∈ Cᶜ, D.weight c ≤ ceilOut) (hOut0 : 0 ≤ ceilOut)
    {e d : Fin 6} (he : e ∈ C) (hd : d ∈ Cᶜ) :
    ∃ z : Fin 3 → ℝ, z ≠ 0 ∧
      (1 - ceilIn - ceilOut) * (z ⬝ᵥ z) + ceilOut * (D.atom e ⬝ᵥ z) ^ 2
        ≤ ceilIn * (lam * (u ⬝ᵥ z) ^ 2) + ceilOut * (D.atom d ⬝ᵥ z) ^ 2 := by
  classical
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]; simp
  have heout : e ∉ (Cᶜ : Finset (Fin 6)) := by simpa using he
  have hnotmem : e ∉ (Cᶜ : Finset (Fin 6)).erase d := fun hc =>
    heout (Finset.mem_of_mem_erase hc)
  have hcardT : (insert e ((Cᶜ : Finset (Fin 6)).erase d)).card = 3 := by
    rw [Finset.card_insert_of_notMem hnotmem, Finset.card_erase_of_mem hd, hcompl]
  obtain ⟨z, hz, hread⟩ := exists_refusal_direction D (insert e (Cᶜ.erase d))
    (htie.2 _ hcardT)
  exact ⟨z, hz, swapRefusal_axis_bound D C hgap hIn hOut hOut0 he hd hread⟩


/-! ## 8. The angle floor, in weights alone -/

/-- **The refusal direction of the complement triple makes a weight-bounded angle
with the gap axis.**  The ceiling on the gap scale eliminates `lam` from
`Gtz.refusal_direction_axis_floor`, leaving a floor on the squared cosine that
reads only the weights.  It is stated in multiplied form, so no weight has to be
inverted. -/
theorem refusal_direction_angle_floor (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {weightFloor ceilIn ceilOut : ℝ} (hfloor : ∀ e ∈ C, weightFloor ≤ D.weight e)
    (hIn : ∀ e ∈ C, D.weight e ≤ ceilIn) (hOut : ∀ d ∈ Cᶜ, D.weight d ≤ ceilOut)
    (hfloor0 : 0 ≤ weightFloor) (hIn0 : 0 ≤ ceilIn) (hOut0 : 0 ≤ ceilOut)
    {z : Fin 3 → ℝ} (hread : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0) :
    weightFloor * ((1 - ceilIn - ceilOut) * (z ⬝ᵥ z))
      ≤ ceilIn * ((1 - weightFloor) * (u ⬝ᵥ z) ^ 2) := by
  have haxis := refusal_direction_axis_floor D C hgap hIn hOut hOut0 hread
  have hcap := corner_gapScale_le_of_weightFloor D C hunit hgap hfloor
  have hstep : weightFloor * ((1 - ceilIn - ceilOut) * (z ⬝ᵥ z))
      ≤ weightFloor * (ceilIn * (lam * (u ⬝ᵥ z) ^ 2)) :=
    mul_le_mul_of_nonneg_left haxis hfloor0
  nlinarith [hstep, hcap, sq_nonneg (u ⬝ᵥ z), mul_nonneg hIn0 (sq_nonneg (u ⬝ᵥ z))]

end Gtz

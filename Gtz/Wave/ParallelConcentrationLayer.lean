import Gtz.Wave.AmbientCeilingToolbox
import Gtz.Wave.CaptureSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The parallel concentration layer — the both-parallel dichotomy at the C4 shape

The dense C4 pattern carries two doubled slot pairs.  When the two doubles
are parallel, the parallel combinations of the two pairs concentrate on
the two single atoms: each combination vanishes on its own double and off
the joint support, and its two remaining coordinates are products of dense
block coordinates.  Two concentrated vectors on one atom pair then split
into a dichotomy:

- **The dependent case.**  A vanishing cross determinant between the two
  concentrations makes a nontrivial linear relation among the four basis
  directions.  The left inverse reads the relation at one slot and finds a
  nonzero coefficient equal to zero.  The case dies with no ceiling input.
- **The independent case.**  A nonzero cross determinant solves the
  two-by-two system and writes BOTH coordinate singles of the atom pair as
  explicit combinations of the four basis directions.  The singles are the
  entry point of the ceiling certificate: the span of the basis directions
  contains the full coordinate plane of the single atoms.

The capstone theorem removes the case split: at every both-parallel C4
configuration with dense blocks, the coordinate singles of the two single
atoms lie in the span of the four basis directions.  The dependent case is
absorbed as a kill.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.parallel_combination_apply` with the one-sided value laws and the
  nonvanishing law — **THE CONCENTRATION VALUES.**
* `Gtz.twoSparse_crossDet_combination_eq_zero` — **THE TWO-SPARSE
  PROPORTIONALITY.**
* `Gtz.false_of_bothParallel_concentrations_dependent` — **THE DEPENDENT
  KILL.**
* `Gtz.twoSparse_scaled_single_left`,
  `Gtz.twoSparse_scaled_single_right` — **THE SCALED SOLVES**, with the
  cross determinant as the division-free scale.
* `Gtz.four_direction_scaled_single_left`,
  `Gtz.four_direction_scaled_single_right` — **THE SPAN EXPORTS.**
* `Gtz.twoSparse_eq_combination_of_singles` — the plane decomposition.
* `Gtz.leftInverse_read_of_four_direction_combination` — **THE
  COEFFICIENT READ.**
* `Gtz.bothParallel_concentration_support` — **THE SUPPORT LAW.**
* `Gtz.bothParallel_concentration_value_single`,
  `Gtz.bothParallel_concentration_value_anchor` — the two coordinate
  values of a concentration.
* `Gtz.bothParallel_single_exports` — **THE CAPSTONE.**  A nonzero
  multiple of each coordinate single of the two single atoms lies in the
  span of the four directions.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every family
of directions with the stated support pattern.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-! ## The concentration values -/

/-- The pointwise value of a parallel combination. -/
theorem parallel_combination_apply (firstDir secondDir : Fin size → ℝ)
    (leftAtom atomIndex : Fin size) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) atomIndex
      = secondDir leftAtom * firstDir atomIndex
        - firstDir leftAtom * secondDir atomIndex := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The combination value where the first direction vanishes: one product
survives with a sign. -/
theorem parallel_combination_apply_of_first_vanish
    (firstDir secondDir : Fin size → ℝ) (leftAtom : Fin size)
    {atomIndex : Fin size} (hfirst : firstDir atomIndex = 0) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) atomIndex
      = -(firstDir leftAtom * secondDir atomIndex) := by
  rw [parallel_combination_apply, hfirst, mul_zero, zero_sub]

/-- The combination value where the second direction vanishes: one product
survives. -/
theorem parallel_combination_apply_of_second_vanish
    (firstDir secondDir : Fin size → ℝ) (leftAtom : Fin size)
    {atomIndex : Fin size} (hsecond : secondDir atomIndex = 0) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) atomIndex
      = secondDir leftAtom * firstDir atomIndex := by
  rw [parallel_combination_apply, hsecond, mul_zero, sub_zero]

/-- A concentration coordinate is nonzero when the surviving product is a
product of nonzero block coordinates. -/
theorem parallel_combination_ne_zero_of_first_vanish
    (firstDir secondDir : Fin size → ℝ) (leftAtom : Fin size)
    {atomIndex : Fin size} (hfirst : firstDir atomIndex = 0)
    (hleft : firstDir leftAtom ≠ 0) (hsecond : secondDir atomIndex ≠ 0) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) atomIndex
      ≠ 0 := by
  rw [parallel_combination_apply_of_first_vanish firstDir secondDir leftAtom
    hfirst]
  exact neg_ne_zero.mpr (mul_ne_zero hleft hsecond)

/-- A concentration coordinate is nonzero on the second-vanishing side. -/
theorem parallel_combination_ne_zero_of_second_vanish
    (firstDir secondDir : Fin size → ℝ) (leftAtom : Fin size)
    {atomIndex : Fin size} (hsecond : secondDir atomIndex = 0)
    (hleft : secondDir leftAtom ≠ 0) (hfirst : firstDir atomIndex ≠ 0) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) atomIndex
      ≠ 0 := by
  rw [parallel_combination_apply_of_second_vanish firstDir secondDir leftAtom
    hsecond]
  exact mul_ne_zero hleft hfirst

/-! ## The two-sparse proportionality -/

/-- **THE TWO-SPARSE PROPORTIONALITY.**  Two vectors supported on one atom
pair with a vanishing cross determinant satisfy the exact proportionality
relation, as a function identity. -/
theorem twoSparse_crossDet_combination_eq_zero
    {concentration concentration' : Fin size → ℝ} {atomB atomD : Fin size}
    (hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration atomIndex = 0)
    (hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration' atomIndex = 0)
    (hdet : concentration atomB * concentration' atomD
      - concentration atomD * concentration' atomB = 0) :
    concentration' atomB • concentration
      - concentration atomB • concentration' = 0 := by
  funext atomIndex
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hb : atomIndex = atomB
  · rw [hb]
    ring
  · by_cases hd : atomIndex = atomD
    · rw [hd]
      linear_combination -hdet
    · rw [hsuppR atomIndex hb hd, hsuppR' atomIndex hb hd]
      ring

/-! ## The dependent kill -/

/-- **THE DEPENDENT KILL.**  When the two concentrations of a both-parallel
C4 configuration have a vanishing cross determinant, the proportionality
relation is a nontrivial linear relation among the four basis directions.
The left inverse reads the relation at the third slot and finds a nonzero
coefficient equal to zero. -/
theorem false_of_bothParallel_concentrations_dependent
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {slotA slotB slotC slotD : Fin basisCount}
    (hCA : slotC ≠ slotA) (hCB : slotC ≠ slotB) (hCD : slotC ≠ slotD)
    {atomA1 atomC1 atomB atomD : Fin size}
    {concentration concentration' : Fin size → ℝ}
    (hrDef : concentration
      = tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB))
    (hr'Def : concentration'
      = tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1 • tightDir (basisLabel slotD))
    (hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration atomIndex = 0)
    (hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration' atomIndex = 0)
    (hdet : concentration atomB * concentration' atomD
      - concentration atomD * concentration' atomB = 0)
    (hrb : concentration atomB ≠ 0)
    (hqD : tightDir (basisLabel slotD) atomC1 ≠ 0) :
    False := by
  have hcomb :=
    twoSparse_crossDet_combination_eq_zero hsuppR hsuppR' hdet
  have happ := congrArg (fun ambientVec => L *ᵥ ambientVec) hcomb
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_zero]
    at happ
  have hLr : L *ᵥ concentration
      = tightDir (basisLabel slotB) atomA1 • Pi.single slotA 1
        - tightDir (basisLabel slotA) atomA1 • Pi.single slotB 1 := by
    rw [hrDef, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotA,
      leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotB]
  have hLr' : L *ᵥ concentration'
      = tightDir (basisLabel slotD) atomC1 • Pi.single slotC 1
        - tightDir (basisLabel slotC) atomC1 • Pi.single slotD 1 := by
    rw [hr'Def, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotC,
      leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotD]
  rw [hLr, hLr'] at happ
  have hread := congrFun happ slotC
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Pi.single_apply] at hread
  rw [if_pos trivial, if_neg hCA, if_neg hCB, if_neg hCD] at hread
  have hzero : concentration atomB * tightDir (basisLabel slotD) atomC1
      = 0 := by
    linear_combination -hread
  rcases mul_eq_zero.mp hzero with hcase | hcase
  · exact hrb hcase
  · exact hqD hcase

/-! ## The scaled two-by-two solve -/

/-- **THE SCALED SOLVE, LEFT.**  Two vectors supported on one atom pair
combine into the cross-determinant multiple of the left coordinate single.
The identity is division-free: the determinant IS the scale. -/
theorem twoSparse_scaled_single_left
    {concentration concentration' : Fin size → ℝ} {atomB atomD : Fin size}
    (hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration atomIndex = 0)
    (hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration' atomIndex = 0) :
    concentration' atomD • concentration - concentration atomD • concentration'
      = (concentration atomB * concentration' atomD
          - concentration atomD * concentration' atomB)
        • (Pi.single atomB 1 : Fin size → ℝ) := by
  funext atomIndex
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hb : atomIndex = atomB
  · rw [hb, if_pos rfl]
    ring
  · rw [if_neg hb]
    by_cases hd : atomIndex = atomD
    · rw [hd]
      ring
    · rw [hsuppR atomIndex hb hd, hsuppR' atomIndex hb hd]
      ring

/-- **THE SCALED SOLVE, RIGHT.**  The mirror identity for the right
coordinate single of the pair. -/
theorem twoSparse_scaled_single_right
    {concentration concentration' : Fin size → ℝ} {atomB atomD : Fin size}
    (hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration atomIndex = 0)
    (hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration' atomIndex = 0) :
    concentration atomB • concentration' - concentration' atomB • concentration
      = (concentration atomB * concentration' atomD
          - concentration atomD * concentration' atomB)
        • (Pi.single atomD 1 : Fin size → ℝ) := by
  funext atomIndex
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hd : atomIndex = atomD
  · rw [hd, if_pos rfl]
    ring
  · rw [if_neg hd]
    by_cases hb : atomIndex = atomB
    · rw [hb]
      ring
    · rw [hsuppR atomIndex hb hd, hsuppR' atomIndex hb hd]
      ring

/-! ## The span exports -/

/-- **THE SPAN EXPORT, LEFT.**  The cross-determinant multiple of the left
coordinate single is an explicit combination of the four basis directions.
The identity is unconditional: the determinant is the scale. -/
theorem four_direction_scaled_single_left
    (basisLabel : Fin basisCount → activeIndex)
    {slotA slotB slotC slotD : Fin basisCount}
    {atomA1 atomC1 atomB atomD : Fin size}
    {concentration concentration' : Fin size → ℝ}
    (hrDef : concentration
      = tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB))
    (hr'Def : concentration'
      = tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1 • tightDir (basisLabel slotD))
    (hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration atomIndex = 0)
    (hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration' atomIndex = 0) :
    ∃ coeffA coeffB coeffC coeffD : ℝ,
      coeffA • tightDir (basisLabel slotA) + coeffB • tightDir (basisLabel slotB)
        + coeffC • tightDir (basisLabel slotC)
        + coeffD • tightDir (basisLabel slotD)
      = (concentration atomB * concentration' atomD
          - concentration atomD * concentration' atomB)
        • (Pi.single atomB 1 : Fin size → ℝ) := by
  refine ⟨concentration' atomD * tightDir (basisLabel slotB) atomA1,
    -(concentration' atomD * tightDir (basisLabel slotA) atomA1),
    -(concentration atomD * tightDir (basisLabel slotD) atomC1),
    concentration atomD * tightDir (basisLabel slotC) atomC1, ?_⟩
  rw [← twoSparse_scaled_single_left hsuppR hsuppR', hrDef, hr'Def]
  funext atomIndex
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **THE SPAN EXPORT, RIGHT.**  The mirror combination for the right
coordinate single. -/
theorem four_direction_scaled_single_right
    (basisLabel : Fin basisCount → activeIndex)
    {slotA slotB slotC slotD : Fin basisCount}
    {atomA1 atomC1 atomB atomD : Fin size}
    {concentration concentration' : Fin size → ℝ}
    (hrDef : concentration
      = tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB))
    (hr'Def : concentration'
      = tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1 • tightDir (basisLabel slotD))
    (hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration atomIndex = 0)
    (hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      concentration' atomIndex = 0) :
    ∃ coeffA coeffB coeffC coeffD : ℝ,
      coeffA • tightDir (basisLabel slotA) + coeffB • tightDir (basisLabel slotB)
        + coeffC • tightDir (basisLabel slotC)
        + coeffD • tightDir (basisLabel slotD)
      = (concentration atomB * concentration' atomD
          - concentration atomD * concentration' atomB)
        • (Pi.single atomD 1 : Fin size → ℝ) := by
  refine ⟨-(concentration' atomB * tightDir (basisLabel slotB) atomA1),
    concentration' atomB * tightDir (basisLabel slotA) atomA1,
    concentration atomB * tightDir (basisLabel slotD) atomC1,
    -(concentration atomB * tightDir (basisLabel slotC) atomC1), ?_⟩
  rw [← twoSparse_scaled_single_right hsuppR hsuppR', hrDef, hr'Def]
  funext atomIndex
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-! ## The support law and the coordinate values -/

/-- **THE SUPPORT LAW.**  A parallel combination of two directions with the
C4 support pattern concentrates on the single atoms: it vanishes at the
double by parallelism and off the joint support by the two supports. -/
theorem bothParallel_concentration_support
    {qA qB : Fin size → ℝ} {atomA1 atomA2 atomB atomD : Fin size}
    (hdetAB : qA atomA1 * qB atomA2 - qA atomA2 * qB atomA1 = 0)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → qA atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → qB atomIndex = 0) :
    ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      (qB atomA1 • qA - qA atomA1 • qB) atomIndex = 0 := by
  intro atomIndex hnotB hnotD
  by_cases ha1 : atomIndex = atomA1
  · rw [ha1]
    exact parallel_combination_apply_pair_left qA qB atomA1
  · by_cases ha2 : atomIndex = atomA2
    · rw [ha2]
      exact parallel_combination_apply_pair_right qA qB hdetAB
    · exact parallel_combination_apply_of_vanish qA qB atomA1
        (hsuppA atomIndex ha1 ha2 hnotD) (hsuppB atomIndex ha1 ha2 hnotB)

/-- The concentration value at the single atom of the second direction:
the product of two dense coordinates, with a sign. -/
theorem bothParallel_concentration_value_single
    {qA qB : Fin size → ℝ} {atomA1 atomA2 atomB atomD : Fin size}
    (hBA1 : atomB ≠ atomA1) (hBA2 : atomB ≠ atomA2) (hBD : atomB ≠ atomD)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → qA atomIndex = 0) :
    (qB atomA1 • qA - qA atomA1 • qB) atomB
      = -(qA atomA1 * qB atomB) := by
  exact parallel_combination_apply_of_first_vanish qA qB atomA1
    (hsuppA atomB hBA1 hBA2 hBD)

/-- The concentration value at the anchor atom of the first direction: the
product of two dense coordinates. -/
theorem bothParallel_concentration_value_anchor
    {qA qB : Fin size → ℝ} {atomA1 atomA2 atomB atomD : Fin size}
    (hDA1 : atomD ≠ atomA1) (hDA2 : atomD ≠ atomA2) (hDB : atomD ≠ atomB)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → qB atomIndex = 0) :
    (qB atomA1 • qA - qA atomA1 • qB) atomD
      = qB atomA1 * qA atomD := by
  exact parallel_combination_apply_of_second_vanish qA qB atomA1
    (hsuppB atomD hDA1 hDA2 hDB)

/-! ## The plane decomposition and the coefficient reads -/

/-- A vector supported on one atom pair is the combination of the two
coordinate singles, with its own coordinates as weights. -/
theorem twoSparse_eq_combination_of_singles
    {sparseVec : Fin size → ℝ} {atomB atomD : Fin size} (hBD : atomB ≠ atomD)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      sparseVec atomIndex = 0) :
    sparseVec atomB • (Pi.single atomB 1 : Fin size → ℝ)
      + sparseVec atomD • (Pi.single atomD 1 : Fin size → ℝ) = sparseVec := by
  funext atomIndex
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hb : atomIndex = atomB
  · rw [hb, if_pos rfl, if_neg hBD]
    ring
  · rw [if_neg hb]
    by_cases hd : atomIndex = atomD
    · rw [hd, if_pos rfl]
      ring
    · rw [if_neg hd, hsupp atomIndex hb hd]
      ring

/-- **THE COEFFICIENT READ.**  The left inverse reads the first coefficient
of a four-direction combination: the coefficients of a span certificate
are unique and computable. -/
theorem leftInverse_read_of_four_direction_combination
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {slotA slotB slotC slotD : Fin basisCount}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    {ambientVec : Fin size → ℝ} {coeffA coeffB coeffC coeffD : ℝ}
    (hcomb : coeffA • tightDir (basisLabel slotA)
        + coeffB • tightDir (basisLabel slotB)
        + coeffC • tightDir (basisLabel slotC)
        + coeffD • tightDir (basisLabel slotD) = ambientVec) :
    (L *ᵥ ambientVec) slotA = coeffA := by
  have happ := congrArg (fun sparseVec => L *ᵥ sparseVec) hcomb
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul] at happ
  rw [leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotA,
    leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotB,
    leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotC,
    leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft slotD] at happ
  have hread := congrFun happ slotA
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    if_pos, mul_ite, mul_one, mul_zero] at hread
  rw [if_neg hAB, if_neg hAC, if_neg hAD] at hread
  linarith [hread]

/-! ## The capstone -/

/-- **THE CAPSTONE.**  At every both-parallel C4 configuration with dense
blocks and a left inverse, both coordinate singles of the two single atoms
are explicit combinations of the four basis directions.  The dependent
case of the concentration dichotomy dies inside the proof, and only the
independent case reaches the conclusion. -/
theorem bothParallel_single_exports
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {slotA slotB slotC slotD : Fin basisCount}
    (hCA : slotC ≠ slotA) (hCB : slotC ≠ slotB) (hCD : slotC ≠ slotD)
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin size}
    (hBA1 : atomB ≠ atomA1) (hBA2 : atomB ≠ atomA2) (hBD : atomB ≠ atomD)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hqAa1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hqDc1 : tightDir (basisLabel slotD) atomC1 ≠ 0) :
    ∃ scale : ℝ, scale ≠ 0
      ∧ (∃ coeffA coeffB coeffC coeffD : ℝ,
        coeffA • tightDir (basisLabel slotA)
          + coeffB • tightDir (basisLabel slotB)
          + coeffC • tightDir (basisLabel slotC)
          + coeffD • tightDir (basisLabel slotD)
          = scale • (Pi.single atomB 1 : Fin size → ℝ))
      ∧ ∃ coeffA coeffB coeffC coeffD : ℝ,
        coeffA • tightDir (basisLabel slotA)
          + coeffB • tightDir (basisLabel slotB)
          + coeffC • tightDir (basisLabel slotC)
          + coeffD • tightDir (basisLabel slotD)
          = scale • (Pi.single atomD 1 : Fin size → ℝ) := by
  have hsuppR : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      (tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB))
        atomIndex = 0 :=
    bothParallel_concentration_support hdetAB hsuppA hsuppB
  have hsuppR' : ∀ atomIndex, atomIndex ≠ atomB → atomIndex ≠ atomD →
      (tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1 • tightDir (basisLabel slotD))
        atomIndex = 0 := by
    intro atomIndex hnotB hnotD
    by_cases hc1 : atomIndex = atomC1
    · rw [hc1]
      exact parallel_combination_apply_pair_left _ _ atomC1
    · by_cases hc2 : atomIndex = atomC2
      · rw [hc2]
        exact parallel_combination_apply_pair_right _ _ hdetCD
      · exact parallel_combination_apply_of_vanish _ _ atomC1
          (hsuppC atomIndex hc1 hc2 hnotB) (hsuppD atomIndex hc1 hc2 hnotD)
  by_cases hdet : (tightDir (basisLabel slotB) atomA1
        • tightDir (basisLabel slotA)
      - tightDir (basisLabel slotA) atomA1
        • tightDir (basisLabel slotB)) atomB
      * (tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1
          • tightDir (basisLabel slotD)) atomD
      - (tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1
          • tightDir (basisLabel slotB)) atomD
      * (tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1
          • tightDir (basisLabel slotD)) atomB = 0
  · exfalso
    refine false_of_bothParallel_concentrations_dependent basisLabel hleft
      hCA hCB hCD rfl rfl hsuppR hsuppR' hdet ?_ hqDc1
    rw [bothParallel_concentration_value_single hBA1 hBA2 hBD hsuppA]
    exact neg_ne_zero.mpr (mul_ne_zero hqAa1 hqBb)
  · exact ⟨_, hdet,
      four_direction_scaled_single_left basisLabel rfl rfl hsuppR hsuppR',
      four_direction_scaled_single_right basisLabel rfl rfl hsuppR hsuppR'⟩

end Gtz

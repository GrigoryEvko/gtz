import Gtz.Wave.OuterCofactorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The outer cofactor span form — the extras cap in cross-pairing coordinates

The extras residue of the outer cofactor reduction caps every positive
label outside the basis against the dual row.  This file puts that cap
into its working coordinates.  The landed range membership puts every
positive label in the span of the basis columns.  The dual energy of a
span combination expands into a quadratic form in the combination
coefficients.  The equality caps kill the diagonal of that form.  Thus
the extras cap is a zero-diagonal quadratic in the finite cross-pairing
matrix of the dual row, at rank four a `4 x 4` matrix and at rank five
a `5 x 5` matrix.  The residues of the reduction now press on finitely
many numbers.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.dual_energy_expansion` — **THE ENERGY EXPANSION.**
* `Gtz.RankFourOuterData.crossPairing_symm` — the pairing symmetry.
* `Gtz.RankFourOuterData.crossPairing_self_eq_zero` — **THE ZERO
  DIAGONAL.**
* `Gtz.RankFourOuterData.exists_basis_combination` — the span
  membership of every positive label.
* `Gtz.RankFourOuterData.cap_cross_form` — **THE RANK-FOUR CAP FORM.**
* `Gtz.RankFiveOuterData.crossPairing_symm`,
  `Gtz.RankFiveOuterData.crossPairing_self_eq_zero`,
  `Gtz.RankFiveOuterData.exists_basis_combination`,
  `Gtz.RankFiveOuterData.cap_cross_form` — the rank-five mirrors.

## Vacuity

The statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the generic energy expansion -/

/-- **THE ENERGY EXPANSION.**  The dual energy of a span combination is
a quadratic form in the combination coefficients, with the cross
pairings of the base as its matrix. -/
theorem dual_energy_expansion {atomCount baseCount : ℕ}
    (dualCoeff : Fin atomCount → ℝ) (base : Fin baseCount → Fin atomCount → ℝ)
    (coeff : Fin baseCount → ℝ) :
    ∑ atomIndex : Fin atomCount, dualCoeff atomIndex
        * (∑ colIndex : Fin baseCount,
            coeff colIndex * base colIndex atomIndex) ^ 2
      = ∑ colOne : Fin baseCount, ∑ colTwo : Fin baseCount,
          coeff colOne * coeff colTwo
            * ∑ atomIndex : Fin atomCount, dualCoeff atomIndex
                * base colOne atomIndex * base colTwo atomIndex := by
  calc ∑ atomIndex : Fin atomCount, dualCoeff atomIndex
        * (∑ colIndex : Fin baseCount,
            coeff colIndex * base colIndex atomIndex) ^ 2
      = ∑ atomIndex : Fin atomCount, ∑ colOne : Fin baseCount,
          ∑ colTwo : Fin baseCount, dualCoeff atomIndex
            * (coeff colOne * base colOne atomIndex)
            * (coeff colTwo * base colTwo atomIndex) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun colOne _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun colTwo _ => by ring
    _ = ∑ colOne : Fin baseCount, ∑ atomIndex : Fin atomCount,
          ∑ colTwo : Fin baseCount, dualCoeff atomIndex
            * (coeff colOne * base colOne atomIndex)
            * (coeff colTwo * base colTwo atomIndex) := Finset.sum_comm
    _ = ∑ colOne : Fin baseCount, ∑ colTwo : Fin baseCount,
          ∑ atomIndex : Fin atomCount, dualCoeff atomIndex
            * (coeff colOne * base colOne atomIndex)
            * (coeff colTwo * base colTwo atomIndex) :=
        Finset.sum_congr rfl fun colOne _ => Finset.sum_comm
    _ = ∑ colOne : Fin baseCount, ∑ colTwo : Fin baseCount,
          coeff colOne * coeff colTwo
            * ∑ atomIndex : Fin atomCount, dualCoeff atomIndex
                * base colOne atomIndex * base colTwo atomIndex := by
        refine Finset.sum_congr rfl fun colOne _ => ?_
        refine Finset.sum_congr rfl fun colTwo _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-! ## Layer 2 — the rank-four cap form -/

/-- The rank-four cross pairing of the dual row against two basis
columns. -/
def RankFourOuterData.crossPairing {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (colOne colTwo : Fin 4) : ℝ :=
  ∑ atomIndex : Fin 6, data.dualRow atomIndex
    * data.frame.tightDir (data.frame.basisLabel colOne) atomIndex
    * data.frame.tightDir (data.frame.basisLabel colTwo) atomIndex

/-- The cross pairing is symmetric. -/
theorem RankFourOuterData.crossPairing_symm {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (colOne colTwo : Fin 4) :
    data.crossPairing colOne colTwo = data.crossPairing colTwo colOne :=
  Finset.sum_congr rfl fun atomIndex _ => by
    show data.dualRow atomIndex * _ * _ = data.dualRow atomIndex * _ * _
    ring

/-- **THE ZERO DIAGONAL.**  The diagonal cross pairings vanish: they are
the equality caps of the reduction. -/
theorem RankFourOuterData.crossPairing_self_eq_zero {crux : SixThreeCrux}
    (data : RankFourOuterData crux) (colIndex : Fin 4) :
    data.crossPairing colIndex colIndex = 0 := by
  have hannih := data.dualRow_annihilates_basis colIndex
  calc data.crossPairing colIndex colIndex
      = ∑ atomIndex : Fin 6, data.dualRow atomIndex
          * data.frame.tightDir (data.frame.basisLabel colIndex)
              atomIndex ^ 2 :=
        Finset.sum_congr rfl fun atomIndex _ => by
          show data.dualRow atomIndex * _ * _ = _
          ring
    _ = 0 := hannih

/-- **THE SPAN MEMBERSHIP.**  Every positive active label of a
rank-four frame is a combination of the four basis columns. -/
theorem RankFourOuterData.exists_basis_combination {crux : SixThreeCrux}
    (data : RankFourOuterData crux) {label : data.frame.activeIndex}
    (hmem : label ∈ data.frame.activeSet)
    (hpos : 0 < data.frame.reducedWeight label) :
    ∃ coeff : Fin 4 → ℝ, ∀ atomIndex : Fin 6,
      data.frame.tightDir label atomIndex
        = ∑ colIndex : Fin 4, coeff colIndex
            * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex := by
  have hrange := tightDir_mem_range_multiplier_of_pos data.frame.hdata hmem hpos
  rw [← data.frame.hspan] at hrange
  rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hrange
  obtain ⟨coeff, hcoeff⟩ := hrange
  refine ⟨coeff, fun atomIndex => ?_⟩
  have hentry := congrFun hcoeff atomIndex
  rw [← hentry, Finset.sum_apply]
  exact Finset.sum_congr rfl fun colIndex _ => by
    rw [Pi.smul_apply, smul_eq_mul]

/-- **THE RANK-FOUR CAP FORM.**  The cap of every positive label is a
zero-diagonal quadratic in the cross pairings.  The extras residue
presses on the off-diagonal pairings alone. -/
theorem RankFourOuterData.cap_cross_form {crux : SixThreeCrux}
    (data : RankFourOuterData crux) {label : data.frame.activeIndex}
    (hmem : label ∈ data.frame.activeSet)
    (hpos : 0 < data.frame.reducedWeight label) :
    ∃ coeff : Fin 4 → ℝ,
      ∑ atomIndex : Fin 6, data.dualRow atomIndex
          * data.frame.tightDir label atomIndex ^ 2
        = ∑ colOne : Fin 4, ∑ colTwo : Fin 4,
            coeff colOne * coeff colTwo * data.crossPairing colOne colTwo := by
  obtain ⟨coeff, hcomb⟩ := data.exists_basis_combination hmem hpos
  refine ⟨coeff, ?_⟩
  have hexp := dual_energy_expansion data.dualRow
    (fun colIndex => data.frame.tightDir (data.frame.basisLabel colIndex)) coeff
  calc ∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin 6, data.dualRow atomIndex
          * (∑ colIndex : Fin 4, coeff colIndex
              * data.frame.tightDir (data.frame.basisLabel colIndex)
                  atomIndex) ^ 2 := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [hcomb atomIndex]
    _ = ∑ colOne : Fin 4, ∑ colTwo : Fin 4,
          coeff colOne * coeff colTwo * data.crossPairing colOne colTwo :=
        hexp

/-! ## Layer 3 — the rank-five cap form -/

/-- The rank-five cross pairing of the dual row against two basis
columns. -/
def RankFiveOuterData.crossPairing {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) (colOne colTwo : Fin 5) : ℝ :=
  ∑ atomIndex : Fin 6, data.dualRow atomIndex
    * data.frame.tightDir (data.frame.basisLabel colOne) atomIndex
    * data.frame.tightDir (data.frame.basisLabel colTwo) atomIndex

/-- The cross pairing is symmetric. -/
theorem RankFiveOuterData.crossPairing_symm {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) (colOne colTwo : Fin 5) :
    data.crossPairing colOne colTwo = data.crossPairing colTwo colOne :=
  Finset.sum_congr rfl fun atomIndex _ => by
    show data.dualRow atomIndex * _ * _ = data.dualRow atomIndex * _ * _
    ring

/-- **THE ZERO DIAGONAL.**  The diagonal cross pairings vanish. -/
theorem RankFiveOuterData.crossPairing_self_eq_zero {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) (colIndex : Fin 5) :
    data.crossPairing colIndex colIndex = 0 := by
  have hannih := data.dualRow_annihilates_basis colIndex
  calc data.crossPairing colIndex colIndex
      = ∑ atomIndex : Fin 6, data.dualRow atomIndex
          * data.frame.tightDir (data.frame.basisLabel colIndex)
              atomIndex ^ 2 :=
        Finset.sum_congr rfl fun atomIndex _ => by
          show data.dualRow atomIndex * _ * _ = _
          ring
    _ = 0 := hannih

/-- **THE SPAN MEMBERSHIP.**  Every positive active label of a
rank-five frame is a combination of the five basis columns. -/
theorem RankFiveOuterData.exists_basis_combination {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) {label : data.frame.activeIndex}
    (hmem : label ∈ data.frame.activeSet)
    (hpos : 0 < data.frame.reducedWeight label) :
    ∃ coeff : Fin 5 → ℝ, ∀ atomIndex : Fin 6,
      data.frame.tightDir label atomIndex
        = ∑ colIndex : Fin 5, coeff colIndex
            * data.frame.tightDir (data.frame.basisLabel colIndex) atomIndex := by
  have hrange := tightDir_mem_range_multiplier_of_pos data.frame.hdata hmem hpos
  rw [← data.frame.hspan] at hrange
  rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hrange
  obtain ⟨coeff, hcoeff⟩ := hrange
  refine ⟨coeff, fun atomIndex => ?_⟩
  have hentry := congrFun hcoeff atomIndex
  rw [← hentry, Finset.sum_apply]
  exact Finset.sum_congr rfl fun colIndex _ => by
    rw [Pi.smul_apply, smul_eq_mul]

/-- **THE RANK-FIVE CAP FORM.**  The cap of every positive label is a
zero-diagonal quadratic in the cross pairings. -/
theorem RankFiveOuterData.cap_cross_form {crux : SixThreeCrux}
    (data : RankFiveOuterData crux) {label : data.frame.activeIndex}
    (hmem : label ∈ data.frame.activeSet)
    (hpos : 0 < data.frame.reducedWeight label) :
    ∃ coeff : Fin 5 → ℝ,
      ∑ atomIndex : Fin 6, data.dualRow atomIndex
          * data.frame.tightDir label atomIndex ^ 2
        = ∑ colOne : Fin 5, ∑ colTwo : Fin 5,
            coeff colOne * coeff colTwo * data.crossPairing colOne colTwo := by
  obtain ⟨coeff, hcomb⟩ := data.exists_basis_combination hmem hpos
  refine ⟨coeff, ?_⟩
  have hexp := dual_energy_expansion data.dualRow
    (fun colIndex => data.frame.tightDir (data.frame.basisLabel colIndex)) coeff
  calc ∑ atomIndex : Fin 6, data.dualRow atomIndex
        * data.frame.tightDir label atomIndex ^ 2
      = ∑ atomIndex : Fin 6, data.dualRow atomIndex
          * (∑ colIndex : Fin 5, coeff colIndex
              * data.frame.tightDir (data.frame.basisLabel colIndex)
                  atomIndex) ^ 2 := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [hcomb atomIndex]
    _ = ∑ colOne : Fin 5, ∑ colTwo : Fin 5,
          coeff colOne * coeff colTwo * data.crossPairing colOne colTwo :=
        hexp

end Gtz

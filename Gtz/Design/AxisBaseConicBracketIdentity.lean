import Gtz.Design.AxisBaseOffConic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-! ## The axis-base conic invariant as a bracket cross-ratio

For six vectors ordered as the three coordinate axes followed by three free
vectors, the off-diagonal Veronese determinant is the difference of the two
four-bracket products associated with the two perfect matchings of the
octahedral bracket diagram.  This is the polynomial form in which off-conicity
can interact with the free-pair refusal graph.
-/

theorem freeOffDiagonalGrid_det_eq_bracketProducts
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    let atom := axisBaseAtom (fun _ : Fin 3 => (1 : ℝ)) freeAtom
    (freeOffDiagonalGrid freeAtom).det =
        tripleBracket (atom 0) (atom 1) (atom 3)
          * tripleBracket (atom 0) (atom 2) (atom 4)
          * tripleBracket (atom 1) (atom 2) (atom 5)
          * tripleBracket (atom 3) (atom 4) (atom 5)
      - tripleBracket (atom 0) (atom 1) (atom 2)
          * tripleBracket (atom 0) (atom 3) (atom 4)
          * tripleBracket (atom 1) (atom 3) (atom 5)
          * tripleBracket (atom 2) (atom 4) (atom 5) := by
  simp [axisBaseAtom, freeOffDiagonalGrid, Matrix.det_fin_three, tripleBracket_eq]
  ring

theorem freeOffDiagonalGrid_det_ne_zero_iff_bracketProducts_ne
    (freeAtom : Fin 3 -> Fin 3 -> ℝ) :
    let atom := axisBaseAtom (fun _ : Fin 3 => (1 : ℝ)) freeAtom
    (freeOffDiagonalGrid freeAtom).det ≠ 0 ↔
        tripleBracket (atom 0) (atom 1) (atom 3)
            * tripleBracket (atom 0) (atom 2) (atom 4)
            * tripleBracket (atom 1) (atom 2) (atom 5)
            * tripleBracket (atom 3) (atom 4) (atom 5)
          ≠ tripleBracket (atom 0) (atom 1) (atom 2)
            * tripleBracket (atom 0) (atom 3) (atom 4)
            * tripleBracket (atom 1) (atom 3) (atom 5)
            * tripleBracket (atom 2) (atom 4) (atom 5) := by
  dsimp only
  rw [freeOffDiagonalGrid_det_eq_bracketProducts]
  exact sub_ne_zero

theorem bracketProducts_ne_of_hasNoCommonQuadric_axisBaseAtom
    (baseScale : Fin 3 -> ℝ) (freeAtom : Fin 3 -> Fin 3 -> ℝ)
    (hoffConic : HasNoCommonQuadric (axisBaseAtom baseScale freeAtom)) :
    let atom := axisBaseAtom (fun _ : Fin 3 => (1 : ℝ)) freeAtom
    tripleBracket (atom 0) (atom 1) (atom 3)
          * tripleBracket (atom 0) (atom 2) (atom 4)
          * tripleBracket (atom 1) (atom 2) (atom 5)
          * tripleBracket (atom 3) (atom 4) (atom 5)
      ≠ tripleBracket (atom 0) (atom 1) (atom 2)
          * tripleBracket (atom 0) (atom 3) (atom 4)
          * tripleBracket (atom 1) (atom 3) (atom 5)
          * tripleBracket (atom 2) (atom 4) (atom 5) := by
  exact (freeOffDiagonalGrid_det_ne_zero_iff_bracketProducts_ne freeAtom).mp
    (freeOffDiagonalGrid_det_ne_zero_of_hasNoCommonQuadric
      baseScale freeAtom hoffConic)

end Gtz

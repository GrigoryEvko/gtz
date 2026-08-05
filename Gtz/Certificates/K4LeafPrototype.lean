/-
# K4 diagonal star-law certificate: leaf-0 transcription prototype

Leaf 0 of the Tier-1 certificate (sector 0, star vertex 3): each
region vertex's gap matrix `N = Gap_star - 2 w_min B` is PSD, witnessed by the
stored rational LDL sum-of-squares.  The pattern here scales mechanically to
all 108 leaves / 1416 vertices; with the convexity step (N affine in w on the
region) it yields the whole diagonal star law in kernel.
-/
import Mathlib
import Gtz.Core.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Gtz

/-- A nonnegative multiple of an atom matrix is PSD. -/
theorem posSemidefSmulAtom (coeff : ℝ) (vec : Fin 3 → ℝ)
    (hcoeff : 0 ≤ coeff) : (coeff • atomMatrix vec).PosSemidef :=
  (posSemidef_atomMatrix vec).smul hcoeff

/-- Vertex 0 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex0_posSemidef :
    (!![(1 : ℝ), (0 : ℝ), (-1 : ℝ); (0 : ℝ), (0 : ℝ), (0 : ℝ); (-1 : ℝ), (0 : ℝ), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![(1 : ℝ), (0 : ℝ), (-1 : ℝ); (0 : ℝ), (0 : ℝ), (0 : ℝ); (-1 : ℝ), (0 : ℝ), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ)
      = (1 : ℝ) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + (1 : ℝ) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact ((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))))

/-- Vertex 1 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex1_posSemidef :
    (!![(1 : ℝ), (0 : ℝ), (-1 : ℝ); (0 : ℝ), (1 : ℝ), (-1 : ℝ); (-1 : ℝ), (-1 : ℝ), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![(1 : ℝ), (0 : ℝ), (-1 : ℝ); (0 : ℝ), (1 : ℝ), (-1 : ℝ); (-1 : ℝ), (-1 : ℝ), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ)
      = (1 : ℝ) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + (1 : ℝ) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact ((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))))

/-- Vertex 2 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex2_posSemidef :
    (!![(1 : ℝ), (0 : ℝ), (-1 : ℝ); (0 : ℝ), ((1 : ℝ) / 3), (-(2 : ℝ) / 3); (-1 : ℝ), (-(2 : ℝ) / 3), ((7 : ℝ) / 3)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![(1 : ℝ), (0 : ℝ), (-1 : ℝ); (0 : ℝ), ((1 : ℝ) / 3), (-(2 : ℝ) / 3); (-1 : ℝ), (-(2 : ℝ) / 3), ((7 : ℝ) / 3)] : Matrix (Fin 3) (Fin 3) ℝ)
      = (1 : ℝ) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + ((1 : ℝ) / 3) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-2 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact ((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 3))))

/-- Vertex 3 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex3_posSemidef :
    (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((1 : ℝ) / 12), (-(1 : ℝ) / 12); (-(11 : ℝ) / 12), (-(1 : ℝ) / 12), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((1 : ℝ) / 12), (-(1 : ℝ) / 12); (-(11 : ℝ) / 12), (-(1 : ℝ) / 12), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 12) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + ((1 : ℝ) / 12) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + (1 : ℝ) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 12))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 12)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))))

/-- Vertex 4 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex4_posSemidef :
    (!![((5 : ℝ) / 6), ((1 : ℝ) / 12), (-(11 : ℝ) / 12); ((1 : ℝ) / 12), ((1 : ℝ) / 12), (-(1 : ℝ) / 6); (-(11 : ℝ) / 12), (-(1 : ℝ) / 6), ((25 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((5 : ℝ) / 6), ((1 : ℝ) / 12), (-(11 : ℝ) / 12); ((1 : ℝ) / 12), ((1 : ℝ) / 12), (-(1 : ℝ) / 6); (-(11 : ℝ) / 12), (-(1 : ℝ) / 6), ((25 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((5 : ℝ) / 6) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 10), (-(11 : ℝ) / 10)] + ((3 : ℝ) / 40) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + (1 : ℝ) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 6))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 40)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ))))

/-- Vertex 5 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex5_posSemidef :
    (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), (1 : ℝ), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), (1 : ℝ), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), (2 : ℝ)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 12) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + (1 : ℝ) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + ((1 : ℝ) / 12) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 12))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ (1 : ℝ)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 12))))

/-- Vertex 6 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex6_posSemidef :
    (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((1 : ℝ) / 12), (-(1 : ℝ) / 6); (-(11 : ℝ) / 12), (-(1 : ℝ) / 6), ((25 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((1 : ℝ) / 12), (-(1 : ℝ) / 6); (-(11 : ℝ) / 12), (-(1 : ℝ) / 6), ((25 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 12) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + ((1 : ℝ) / 12) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-2 : ℝ)] + ((5 : ℝ) / 6) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 12))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 12)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 6))))

/-- Vertex 7 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex7_posSemidef :
    (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((11 : ℝ) / 12), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), ((25 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((11 : ℝ) / 12), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), ((25 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 12) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + ((11 : ℝ) / 12) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(12 : ℝ) / 11)] + ((5 : ℝ) / 66) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 12))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 12)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 66))))

/-- Vertex 8 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex8_posSemidef :
    (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((13 : ℝ) / 36), (-(13 : ℝ) / 18); (-(11 : ℝ) / 12), (-(13 : ℝ) / 18), ((85 : ℝ) / 36)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 12), (0 : ℝ), (-(11 : ℝ) / 12); (0 : ℝ), ((13 : ℝ) / 36), (-(13 : ℝ) / 18); (-(11 : ℝ) / 12), (-(13 : ℝ) / 18), ((85 : ℝ) / 36)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 12) • atomMatrix ![(1 : ℝ), (0 : ℝ), (-1 : ℝ)] + ((13 : ℝ) / 36) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-2 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact ((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 12))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((13 : ℝ) / 36))))

/-- Vertex 9 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex9_posSemidef :
    (!![((5 : ℝ) / 8), ((1 : ℝ) / 8), (-(7 : ℝ) / 8); ((1 : ℝ) / 8), ((1 : ℝ) / 8), (-(3 : ℝ) / 8); (-(7 : ℝ) / 8), (-(3 : ℝ) / 8), ((17 : ℝ) / 8)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((5 : ℝ) / 8), ((1 : ℝ) / 8), (-(7 : ℝ) / 8); ((1 : ℝ) / 8), ((1 : ℝ) / 8), (-(3 : ℝ) / 8); (-(7 : ℝ) / 8), (-(3 : ℝ) / 8), ((17 : ℝ) / 8)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((5 : ℝ) / 8) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 5), (-(7 : ℝ) / 5)] + ((1 : ℝ) / 10) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-2 : ℝ)] + ((1 : ℝ) / 2) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 8))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 10)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 2))))

/-- Vertex 10 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex10_posSemidef :
    (!![((5 : ℝ) / 8), ((1 : ℝ) / 8), (-(7 : ℝ) / 8); ((1 : ℝ) / 8), ((5 : ℝ) / 8), (-(7 : ℝ) / 8); (-(7 : ℝ) / 8), (-(7 : ℝ) / 8), ((17 : ℝ) / 8)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((5 : ℝ) / 8), ((1 : ℝ) / 8), (-(7 : ℝ) / 8); ((1 : ℝ) / 8), ((5 : ℝ) / 8), (-(7 : ℝ) / 8); (-(7 : ℝ) / 8), (-(7 : ℝ) / 8), ((17 : ℝ) / 8)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((5 : ℝ) / 8) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 5), (-(7 : ℝ) / 5)] + ((3 : ℝ) / 5) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(7 : ℝ) / 6)] + ((1 : ℝ) / 12) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 8))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 5)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 12))))

/-- Vertex 11 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex11_posSemidef :
    (!![((5 : ℝ) / 8), ((1 : ℝ) / 8), (-(7 : ℝ) / 8); ((1 : ℝ) / 8), ((7 : ℝ) / 24), (-(17 : ℝ) / 24); (-(7 : ℝ) / 8), (-(17 : ℝ) / 24), ((55 : ℝ) / 24)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((5 : ℝ) / 8), ((1 : ℝ) / 8), (-(7 : ℝ) / 8); ((1 : ℝ) / 8), ((7 : ℝ) / 24), (-(17 : ℝ) / 24); (-(7 : ℝ) / 8), (-(17 : ℝ) / 24), ((55 : ℝ) / 24)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((5 : ℝ) / 8) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 5), (-(7 : ℝ) / 5)] + ((4 : ℝ) / 15) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-2 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact ((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 8))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((4 : ℝ) / 15))))

/-- Vertex 12 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex12_posSemidef :
    (!![((3 : ℝ) / 4), ((1 : ℝ) / 4), (-1 : ℝ); ((1 : ℝ) / 4), ((3 : ℝ) / 4), (-1 : ℝ); (-1 : ℝ), (-1 : ℝ), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((3 : ℝ) / 4), ((1 : ℝ) / 4), (-1 : ℝ); ((1 : ℝ) / 4), ((3 : ℝ) / 4), (-1 : ℝ); (-1 : ℝ), (-1 : ℝ), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((3 : ℝ) / 4) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 3), (-(4 : ℝ) / 3)] + ((2 : ℝ) / 3) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + ((1 : ℝ) / 4) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 4))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((2 : ℝ) / 3)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 4))))

/-- Vertex 13 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex13_posSemidef :
    (!![((3 : ℝ) / 4), ((1 : ℝ) / 4), (-1 : ℝ); ((1 : ℝ) / 4), ((1 : ℝ) / 4), (-(1 : ℝ) / 2); (-1 : ℝ), (-(1 : ℝ) / 2), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((3 : ℝ) / 4), ((1 : ℝ) / 4), (-1 : ℝ); ((1 : ℝ) / 4), ((1 : ℝ) / 4), (-(1 : ℝ) / 2); (-1 : ℝ), (-(1 : ℝ) / 2), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((3 : ℝ) / 4) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 3), (-(4 : ℝ) / 3)] + ((1 : ℝ) / 6) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + ((3 : ℝ) / 4) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 4))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 6)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 4))))

/-- Vertex 14 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex14_posSemidef :
    (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((3 : ℝ) / 4), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((3 : ℝ) / 4), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((2 : ℝ) / 3) • atomMatrix ![(1 : ℝ), ((3 : ℝ) / 8), (-(11 : ℝ) / 8)] + ((21 : ℝ) / 32) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + ((1 : ℝ) / 3) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((2 : ℝ) / 3))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((21 : ℝ) / 32)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 3))))

/-- Vertex 15 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex15_posSemidef :
    (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((1 : ℝ) / 4), (-(1 : ℝ) / 2); (-(11 : ℝ) / 12), (-(1 : ℝ) / 2), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((1 : ℝ) / 4), (-(1 : ℝ) / 2); (-(11 : ℝ) / 12), (-(1 : ℝ) / 2), ((9 : ℝ) / 4)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((2 : ℝ) / 3) • atomMatrix ![(1 : ℝ), ((3 : ℝ) / 8), (-(11 : ℝ) / 8)] + ((5 : ℝ) / 32) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-1 : ℝ)] + ((5 : ℝ) / 6) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((2 : ℝ) / 3))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 32)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((5 : ℝ) / 6))))

/-- Vertex 16 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex16_posSemidef :
    (!![((3 : ℝ) / 4), ((1 : ℝ) / 4), (-1 : ℝ); ((1 : ℝ) / 4), ((5 : ℝ) / 12), (-(5 : ℝ) / 6); (-1 : ℝ), (-(5 : ℝ) / 6), ((29 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((3 : ℝ) / 4), ((1 : ℝ) / 4), (-1 : ℝ); ((1 : ℝ) / 4), ((5 : ℝ) / 12), (-(5 : ℝ) / 6); (-1 : ℝ), (-(5 : ℝ) / 6), ((29 : ℝ) / 12)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((3 : ℝ) / 4) • atomMatrix ![(1 : ℝ), ((1 : ℝ) / 3), (-(4 : ℝ) / 3)] + ((1 : ℝ) / 3) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(3 : ℝ) / 2)] + ((1 : ℝ) / 3) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 4))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 3)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 3))))

/-- Vertex 17 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex17_posSemidef :
    (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((2 : ℝ) / 3), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), ((7 : ℝ) / 3)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((2 : ℝ) / 3), (-1 : ℝ); (-(11 : ℝ) / 12), (-1 : ℝ), ((7 : ℝ) / 3)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((2 : ℝ) / 3) • atomMatrix ![(1 : ℝ), ((3 : ℝ) / 8), (-(11 : ℝ) / 8)] + ((55 : ℝ) / 96) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(63 : ℝ) / 55)] + ((53 : ℝ) / 165) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((2 : ℝ) / 3))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((55 : ℝ) / 96)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((53 : ℝ) / 165))))

/-- Vertex 18 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex18_posSemidef :
    (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((4 : ℝ) / 9), (-(8 : ℝ) / 9); (-(11 : ℝ) / 12), (-(8 : ℝ) / 9), ((22 : ℝ) / 9)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((2 : ℝ) / 3), ((1 : ℝ) / 4), (-(11 : ℝ) / 12); ((1 : ℝ) / 4), ((4 : ℝ) / 9), (-(8 : ℝ) / 9); (-(11 : ℝ) / 12), (-(8 : ℝ) / 9), ((22 : ℝ) / 9)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((2 : ℝ) / 3) • atomMatrix ![(1 : ℝ), ((3 : ℝ) / 8), (-(11 : ℝ) / 8)] + ((101 : ℝ) / 288) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(157 : ℝ) / 101)] + ((34 : ℝ) / 101) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((2 : ℝ) / 3))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((101 : ℝ) / 288)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((34 : ℝ) / 101))))

/-- Vertex 19 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex19_posSemidef :
    (!![((11 : ℝ) / 24), ((7 : ℝ) / 24), (-(7 : ℝ) / 8); ((7 : ℝ) / 24), ((11 : ℝ) / 24), (-(7 : ℝ) / 8); (-(7 : ℝ) / 8), (-(7 : ℝ) / 8), ((55 : ℝ) / 24)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 24), ((7 : ℝ) / 24), (-(7 : ℝ) / 8); ((7 : ℝ) / 24), ((11 : ℝ) / 24), (-(7 : ℝ) / 8); (-(7 : ℝ) / 8), (-(7 : ℝ) / 8), ((55 : ℝ) / 24)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 24) • atomMatrix ![(1 : ℝ), ((7 : ℝ) / 11), (-(21 : ℝ) / 11)] + ((3 : ℝ) / 11) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(7 : ℝ) / 6)] + ((1 : ℝ) / 4) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 24))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((3 : ℝ) / 11)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 4))))

/-- Vertex 20 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex20_posSemidef :
    (!![((11 : ℝ) / 24), ((7 : ℝ) / 24), (-(7 : ℝ) / 8); ((7 : ℝ) / 24), ((7 : ℝ) / 24), (-(17 : ℝ) / 24); (-(7 : ℝ) / 8), (-(17 : ℝ) / 24), ((55 : ℝ) / 24)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 24), ((7 : ℝ) / 24), (-(7 : ℝ) / 8); ((7 : ℝ) / 24), ((7 : ℝ) / 24), (-(17 : ℝ) / 24); (-(7 : ℝ) / 8), (-(17 : ℝ) / 24), ((55 : ℝ) / 24)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 24) • atomMatrix ![(1 : ℝ), ((7 : ℝ) / 11), (-(21 : ℝ) / 11)] + ((7 : ℝ) / 66) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(10 : ℝ) / 7)] + ((17 : ℝ) / 42) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 24))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((7 : ℝ) / 66)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((17 : ℝ) / 42))))

/-- Vertex 21 of leaf 0 (sector 0, star 3):
`N ⪰ 0` by its stored rational sum-of-squares. -/
theorem k4LeafZeroVertex21_posSemidef :
    (!![((11 : ℝ) / 24), ((7 : ℝ) / 24), (-(7 : ℝ) / 8); ((7 : ℝ) / 24), ((25 : ℝ) / 72), (-(59 : ℝ) / 72); (-(7 : ℝ) / 8), (-(59 : ℝ) / 72), ((169 : ℝ) / 72)] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hdecomposition : (!![((11 : ℝ) / 24), ((7 : ℝ) / 24), (-(7 : ℝ) / 8); ((7 : ℝ) / 24), ((25 : ℝ) / 72), (-(59 : ℝ) / 72); (-(7 : ℝ) / 8), (-(59 : ℝ) / 72), ((169 : ℝ) / 72)] : Matrix (Fin 3) (Fin 3) ℝ)
      = ((11 : ℝ) / 24) • atomMatrix ![(1 : ℝ), ((7 : ℝ) / 11), (-(21 : ℝ) / 11)] + ((16 : ℝ) / 99) • atomMatrix ![(0 : ℝ), (1 : ℝ), (-(13 : ℝ) / 8)] + ((1 : ℝ) / 4) • atomMatrix ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] := by
    ext rowIdx colIdx
    fin_cases rowIdx <;> fin_cases colIdx <;>
      simp [atomMatrix, Matrix.vecMulVec_apply] <;> norm_num
  rw [hdecomposition]
  exact (((posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((11 : ℝ) / 24))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((16 : ℝ) / 99)))).add (posSemidefSmulAtom _ _ (by norm_num : (0:ℝ) ≤ ((1 : ℝ) / 4))))

end Gtz

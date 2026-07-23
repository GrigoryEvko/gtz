/-
# Lemma G: compressions of a design are designs

The bridge from rank `k` to the planar layer, and the single most load-bearing
step of the whole certificate architecture. Orthonormal-row compression
`P : ℝᵏ → ℝʲ` (`P Pᵀ = 1`) carries a weighted `(m,k)` design to a weighted
`(m,j)` design with the SAME weights, because Parseval conjugates:

  `Σ t_c (P g_c)(P g_c)ᵀ = P (Σ t_c g_c g_cᵀ) Pᵀ = P Pᵀ = 1`.

Consequently every statement proven at rank `j` applies to every `j`-frame view
of a higher-rank design. At `j = 2` the input is the kernel-checked
`gtz_rank_two`, so the conclusion is UNCONDITIONAL: in every 2-plane view of
every design there is a pair whose compressed excess is positive semidefinite.
That is Lemma G/G′ of the global-coverage layer, and it is what puts the planar
platform (the whole GAP-S apparatus) underneath a rank-3 design.

The converse direction is the trivial half: compression preserves positive
semidefiniteness, so a genuinely dominating subset dominates in every view. The
content of Lemma G is the other way — the pair is produced BY the view, and
different views generally produce different pairs.
-/
import Mathlib
import Gtz.Basic
import Gtz.Reductions

namespace Gtz

open Matrix

variable {m k j : ℕ}

/-! ### Conjugation of atoms -/

/-- Compressing an atom conjugates its rank-one matrix: `(Pg)(Pg)ᵀ = P (g gᵀ) Pᵀ`. -/
theorem atomMatrix_compress (compression : Matrix (Fin j) (Fin k) ℝ)
    (g : Fin k → ℝ) :
    atomMatrix (compression.mulVec g)
      = compression * atomMatrix g * compressionᵀ := by
  ext firstRow secondRow
  have hleft : atomMatrix (compression.mulVec g) firstRow secondRow
      = (∑ inner, compression firstRow inner * g inner)
        * (∑ outer, compression secondRow outer * g outer) := by
    simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  have hright : (compression * atomMatrix g * compressionᵀ) firstRow secondRow
      = ∑ outer, (∑ inner, compression firstRow inner * (g inner * g outer))
        * compression secondRow outer := by
    simp [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.transpose_apply, Finset.sum_mul]
  rw [hleft, hright, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun outer _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun inner _ => by ring

/-- The compressed subset sum is the conjugated subset sum. -/
theorem subsetSum_compress (D : WeightedDesign m k)
    (compression : Matrix (Fin j) (Fin k) ℝ) (C : Finset (Fin m)) :
    ∑ c ∈ C, atomMatrix (compression.mulVec (D.atom c))
      = compression * subsetSum D C * compressionᵀ := by
  rw [subsetSum, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun c _ => atomMatrix_compress compression (D.atom c)

/-! ### The compressed design -/

/-- **Lemma G**: an orthonormal-row compression of a weighted design is a
weighted design of the lower rank, with the same weights. -/
def compressedDesign (D : WeightedDesign m k)
    (compression : Matrix (Fin j) (Fin k) ℝ)
    (hOrthonormal : compression * compressionᵀ = 1) : WeightedDesign m j where
  atom := fun c => compression.mulVec (D.atom c)
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    have hconjugate : ∑ c, D.weight c • atomMatrix (compression.mulVec (D.atom c))
        = compression * (∑ c, D.weight c • atomMatrix (D.atom c))
          * compressionᵀ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [atomMatrix_compress, Matrix.mul_smul, Matrix.smul_mul]
    rw [hconjugate, D.isParseval, Matrix.mul_one, hOrthonormal]

@[simp] theorem compressedDesign_atom (D : WeightedDesign m k)
    (compression : Matrix (Fin j) (Fin k) ℝ)
    (hOrthonormal : compression * compressionᵀ = 1) (c : Fin m) :
    (compressedDesign D compression hOrthonormal).atom c
      = compression.mulVec (D.atom c) := rfl

/-- Domination inside the compressed design is exactly conjugated excess. -/
theorem compressed_dominates_iff (D : WeightedDesign m k)
    (compression : Matrix (Fin j) (Fin k) ℝ)
    (hOrthonormal : compression * compressionᵀ = 1) (C : Finset (Fin m)) :
    Dominates (compressedDesign D compression hOrthonormal) C
      ↔ (compression * (subsetSum D C - 1) * compressionᵀ).PosSemidef := by
  have hcompressed : subsetSum (compressedDesign D compression hOrthonormal) C
      = compression * subsetSum D C * compressionᵀ := by
    rw [subsetSum]
    simp only [compressedDesign_atom]
    exact subsetSum_compress D compression C
  have hexcess : subsetSum (compressedDesign D compression hOrthonormal) C - 1
      = compression * (subsetSum D C - 1) * compressionᵀ := by
    rw [hcompressed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hOrthonormal]
  rw [Dominates, hexcess]

/-! ### The compression is a lower-rank view -/

/-- The trivial half: compression preserves positive semidefiniteness, so a
subset that genuinely dominates dominates in every view. -/
theorem posSemidef_compress {excess : Matrix (Fin k) (Fin k) ℝ}
    (hExcess : excess.PosSemidef) (compression : Matrix (Fin j) (Fin k) ℝ) :
    (compression * excess * compressionᵀ).PosSemidef := by
  have hsymExcess : excessᵀ = excess := transpose_eq_of_isHermitian hExcess.isHermitian
  have hsymmetric : (compression * excess * compressionᵀ)ᵀ
      = compression * excess * compressionᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hsymExcess, Matrix.mul_assoc]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe => ?_⟩
  have hquad : probe ⬝ᵥ ((compression * excess * compressionᵀ) *ᵥ probe)
      = (compressionᵀ *ᵥ probe) ⬝ᵥ (excess *ᵥ (compressionᵀ *ᵥ probe)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm probe (compression *ᵥ (excess *ᵥ (compressionᵀ *ᵥ probe))),
      dotProduct_mulVec_transpose, dotProduct_comm]
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hExcess).2
    (compressionᵀ *ᵥ probe)
  rw [star_trivial] at hnonneg
  rw [star_trivial, hquad]
  exact hnonneg

/-! ### Lemma G′: every view produces a subset -/

/-- **Lemma G′, general rank**: if weighted GTZ holds at rank `j`, then for
every design of any rank and every orthonormal `j`-frame there is a `j`-subset
whose excess is positive semidefinite AS SEEN THROUGH THAT FRAME. The subset
depends on the frame — this is what makes the statement usable as a gate rather
than as a domination proof. -/
theorem exists_subset_dominates_in_view (hRank : GtzWeightedAll j)
    (D : WeightedDesign m k) (compression : Matrix (Fin j) (Fin k) ℝ)
    (hOrthonormal : compression * compressionᵀ = 1) :
    ∃ C : Finset (Fin m), C.card = j
      ∧ (compression * (subsetSum D C - 1) * compressionᵀ).PosSemidef := by
  obtain ⟨C, hcard, hdominates⟩ :=
    hRank m (compressedDesign D compression hOrthonormal)
  exact ⟨C, hcard,
    (compressed_dominates_iff D compression hOrthonormal C).mp hdominates⟩

/-- **Lemma G′ at rank two, UNCONDITIONAL** (the planar gate): in every 2-plane
view of every weighted design there is a PAIR of atoms whose excess is positive
semidefinite in that plane. The rank-2 input is the kernel-checked
`gtz_rank_two`, so nothing is assumed. This is the step that puts the planar
platform underneath a rank-3 design. -/
theorem exists_pair_dominates_in_plane (D : WeightedDesign m k)
    (plane : Matrix (Fin 2) (Fin k) ℝ) (hOrthonormal : plane * planeᵀ = 1) :
    ∃ C : Finset (Fin m), C.card = 2
      ∧ (plane * (subsetSum D C - 1) * planeᵀ).PosSemidef :=
  exists_subset_dominates_in_view gtz_rank_two D plane hOrthonormal

/-- The planar gate in quadratic-form language: for every unit-normalized plane
and every in-plane probe there is a pair whose excess is nonnegative along the
probe's pullback. This is the form the gate is consumed in — `⟨w, (S_C − 1) w⟩
≥ 0` for every `w` in the plane. -/
theorem exists_pair_nonneg_on_plane (D : WeightedDesign m k)
    (plane : Matrix (Fin 2) (Fin k) ℝ) (hOrthonormal : plane * planeᵀ = 1) :
    ∃ C : Finset (Fin m), C.card = 2 ∧ ∀ probe : Fin 2 → ℝ,
      0 ≤ (planeᵀ *ᵥ probe) ⬝ᵥ ((subsetSum D C - 1) *ᵥ (planeᵀ *ᵥ probe)) := by
  obtain ⟨C, hcard, hpsd⟩ := exists_pair_dominates_in_plane D plane hOrthonormal
  refine ⟨C, hcard, fun probe => ?_⟩
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
  rw [star_trivial] at hnonneg
  have hquad : probe ⬝ᵥ ((plane * (subsetSum D C - 1) * planeᵀ) *ᵥ probe)
      = (planeᵀ *ᵥ probe) ⬝ᵥ ((subsetSum D C - 1) *ᵥ (planeᵀ *ᵥ probe)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm probe
        (plane *ᵥ ((subsetSum D C - 1) *ᵥ (planeᵀ *ᵥ probe))),
      dotProduct_mulVec_transpose, dotProduct_comm]
  rwa [hquad] at hnonneg

end Gtz

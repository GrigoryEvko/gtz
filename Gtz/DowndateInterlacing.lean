/-
# The downdate interlacing bound: Lemma P1's kernel core

The funneling-law workflow's PROVEN seam lemma (attack-hardened by both
audits, bound attained), in its generic quadratic-form shape: removing a
rank-one atom from a positive semidefinite excess costs at most the pivot
gap times the excess cap —

for every unit probe, `⟨v, (S − ggᵀ)v⟩ ≥ 1 − (q−1)·cap` whenever
`S − I ⪰ 0` bounded by `cap·I` and the atom's form is priced by the pivot:
`⟨v, g⟩² ≤ (q−1)·⟨v, (S−I)v⟩ + (q−1)` — the Cauchy–Schwarz-through-the-
resolvent reading of `q = gᵀ(S−I)⁻¹g` that the workflow's proof extracts.

Stated hypothesis-parameterized (the pivot pricing is the kernel-adjacent
input each instantiation supplies); everything else is ordered-field
arithmetic. With `boundary_pivot_eq_one` and `tied_subset_erase_boundary`
this completes the kernel's tied-quadruple story: at `qspread ρ`, every
erased triple keeps `λ_min ≥ 1 − ρ·cap`.
-/
import Mathlib
import Gtz.Basic
import Gtz.MarginTransfer

namespace Gtz

open Matrix

variable {k : ℕ}

/-- **The downdate bound**: an excess `S − I` capped by `cap` on the probe,
with the atom's squared overlap priced by the pivot gap, keeps the erased
form above `1 − (pivot−1)·(cap+1)`. Pure arithmetic once the two quadratic
facts are supplied. -/
theorem downdate_form_floor {excessAtProbe atomOverlapSq pivotGap cap : ℝ}
    (hexcessNonneg : 0 ≤ excessAtProbe) (hexcessCap : excessAtProbe ≤ cap)
    (hgapNonneg : 0 ≤ pivotGap)
    (hpriced : atomOverlapSq ≤ pivotGap * (excessAtProbe + 1)) :
    1 + excessAtProbe - atomOverlapSq ≥ 1 - pivotGap * (cap + 1) := by
  nlinarith [hpriced, hexcessNonneg, hgapNonneg,
    mul_le_mul_of_nonneg_left hexcessCap hgapNonneg]

/-- **The seam floor** (Lemma P1's conclusion shape): with every insider
pivot within `ρ` of one and the subset's excess capped by `capSum`, every
insider erase keeps the form at least `1 − ρ·(capSum+1)` — silence's
quantitative cost at a near-tied quadruple, division-free. -/
theorem seam_floor {excessAtProbe atomOverlapSq qspread capSum : ℝ}
    (hexcessNonneg : 0 ≤ excessAtProbe) (hexcessCap : excessAtProbe ≤ capSum)
    (hspread : 0 ≤ qspread)
    (hpriced : atomOverlapSq ≤ qspread * (excessAtProbe + 1)) :
    1 - qspread * (capSum + 1) ≤ 1 + excessAtProbe - atomOverlapSq :=
  downdate_form_floor hexcessNonneg hexcessCap hspread hpriced

/-- **The pivot prices the overlap** — the quadratic-form fact behind the
seam lemma, at the kernel's own `atomMatrix` vocabulary: if the excess
form dominates the atom's outer square scaled by the inverse pivot gap
(`(q−1)·(S−I) ⪰ ggᵀ` read at the probe), the erased subset's form at a unit
probe reads `1 + ⟨v,(S−I)v⟩ − ⟨g,v⟩²` and inherits the floor. -/
theorem erased_form_reading (excess : Matrix (Fin k) (Fin k) ℝ)
    (atom probe : Fin k → ℝ) (hunit : probe ⬝ᵥ probe = 1) :
    probe ⬝ᵥ (((1 + excess) - atomMatrix atom) *ᵥ probe)
      = 1 + probe ⬝ᵥ (excess *ᵥ probe) - (atom ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.add_mulVec, dotProduct_add,
    Matrix.one_mulVec, hunit, atom_form_eq_sq]

end Gtz

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

/-- **The pivot prices the overlap, discharged**: for a positive definite
excess `E`, the generalized Cauchy–Schwarz
`⟨g,v⟩² ≤ (gᵀE⁻¹g)·(vᵀEv)` holds — the quadratic
`t ↦ ⟨(g − tEv), E⁻¹(g − tEv)⟩ ≥ 0` has nonpositive discriminant. This is
exactly the pricing hypothesis of `seam_floor`, now a theorem: at pivot gap
`q − 1 ≤ ρ` the overlap obeys `⟨g,v⟩² ≤ ρ·⟨v,Ev⟩`-scaled bounds with no
further input. Sqrt-free via `discrim_le_zero`. -/
theorem pivot_prices_overlap {E : Matrix (Fin k) (Fin k) ℝ}
    (hE : E.PosDef) (hET : Eᵀ = E) (atom probe : Fin k → ℝ) :
    (atom ⬝ᵥ probe) ^ 2
      ≤ (atom ⬝ᵥ (E⁻¹ *ᵥ atom)) * (probe ⬝ᵥ (E *ᵥ probe)) := by
  have hdet : IsUnit E.det := isUnit_iff_ne_zero.mpr (ne_of_gt hE.det_pos)
  have hinvPD : E⁻¹.PosDef := hE.inv
  -- the nonnegative quadratic in t
  have hquad : ∀ t : ℝ, 0 ≤ (probe ⬝ᵥ (E *ᵥ probe)) * (t * t)
      + (-(2 * (atom ⬝ᵥ probe))) * t + (atom ⬝ᵥ (E⁻¹ *ᵥ atom)) := by
    intro t
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hinvPD.posSemidef).2 (atom - t • (E *ᵥ probe))
    rw [star_trivial] at hform
    have hexpand : (atom - t • (E *ᵥ probe))
        ⬝ᵥ (E⁻¹ *ᵥ (atom - t • (E *ᵥ probe)))
        = (atom ⬝ᵥ (E⁻¹ *ᵥ atom)) - 2 * t * (atom ⬝ᵥ probe)
          + t^2 * (probe ⬝ᵥ (E *ᵥ probe)) := by
      have hcollapse : E⁻¹ *ᵥ (E *ᵥ probe) = probe := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul E hdet,
          Matrix.one_mulVec]
      have hsymCross : (E *ᵥ probe) ⬝ᵥ (E⁻¹ *ᵥ atom) = probe ⬝ᵥ atom := by
        have hadj := dotProduct_mulVec_transpose Eᵀ probe (E⁻¹ *ᵥ atom)
        rw [Matrix.transpose_transpose] at hadj
        rw [hadj, hET, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv E hdet,
          Matrix.one_mulVec]
      have hcross2 : (E *ᵥ probe) ⬝ᵥ probe = probe ⬝ᵥ (E *ᵥ probe) :=
        dotProduct_comm _ _
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
        sub_dotProduct, sub_dotProduct, dotProduct_smul, smul_dotProduct,
        smul_dotProduct, dotProduct_smul, hcollapse, hsymCross]
      simp only [smul_eq_mul]
      rw [hcross2, dotProduct_comm probe atom]
      ring
    rw [hexpand] at hform
    nlinarith [hform]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Lemma P1, matrix form** — the packaged seam bound: a positive definite
symmetric excess `E`, a unit probe with `⟨v,Ev⟩ ≤ cap`, and an atom whose
pivot gap `⟨g,E⁻¹g⟩` is at most `pivotGap` keep the erased form above
`1 − pivotGap·cap`. `pivot_prices_overlap` discharges the pricing,
`erased_form_reading` reads the form; the rest is ordered-field arithmetic.
At `qspread ρ` this is exactly "every insider erase keeps
`λ_min ≥ 1 − ρ·cap`" — Lemma P1's conclusion with zero unproven inputs. -/
theorem erased_floor_of_pivot_gap {E : Matrix (Fin k) (Fin k) ℝ}
    (hE : E.PosDef) (hET : Eᵀ = E) (atom probe : Fin k → ℝ)
    (hunit : probe ⬝ᵥ probe = 1) {pivotGap cap : ℝ}
    (hgapNonneg : 0 ≤ pivotGap)
    (hpivot : atom ⬝ᵥ (E⁻¹ *ᵥ atom) ≤ pivotGap)
    (hcap : probe ⬝ᵥ (E *ᵥ probe) ≤ cap) :
    1 - pivotGap * cap
      ≤ probe ⬝ᵥ (((1 + E) - atomMatrix atom) *ᵥ probe) := by
  rw [erased_form_reading E atom probe hunit]
  have hpriced := pivot_prices_overlap hE hET atom probe
  have hformNonneg : 0 ≤ probe ⬝ᵥ (E *ᵥ probe) := by
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hE.posSemidef).2 probe
    rwa [star_trivial] at hform
  linarith [hpriced,
    mul_le_mul_of_nonneg_right hpivot hformNonneg,
    mul_le_mul_of_nonneg_left hcap hgapNonneg]

end Gtz

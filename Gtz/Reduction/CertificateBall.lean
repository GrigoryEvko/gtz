/-
# One certificate, many designs: what a fixed LDL witness covers

An atlas argument for weighted GTZ would need finitely many rational certificates, each
valid on an OPEN SET of designs, together covering the family. This file states, at the
level of designs, exactly how much of a certificate transports off its own point — and
the answer is: half of it, with an explicit radius, and the other half not at all.

* `gate_posDef_of_nearby_design` — the gate `S_Q ≻ 1` is certified by a FIXED pair
  `(L, d)` for EVERY design whose base Gram is entrywise within
  `diagFloor / (k³ · pivotBound²)` of the certified one. The certificate is reused
  verbatim; nothing is recomputed. This is a genuine open ball of validity.

* `certificate_ball_dominates` — the full consumer, with the transported gate and the
  outsider excess of the NEW design. The outsider hypothesis is re-stated at the new
  design because it does not transport: it is a non-strict inequality which is met with
  EQUALITY on the tie locus (`Gtz.splitTetraRat_excess_eq_zero`), so its slack is `0`
  there and no ball around such a point can inherit it.

The consequence for the atlas plan is a split, not a verdict. The gate radius does not
shrink near the tie locus; the outsider INRADIUS does, linearly in the distance to it.

What does NOT follow is that a finite atlas is impossible. The tempting count — cells
of radius proportional to `delta` around a locus of codimension `c` in dimension `D`
give `delta^(c − D)` of them — models the cell as a BALL of that inradius, and the cell
is not a ball. It is cut out by ONE scalar inequality, so it is slab-shaped: thin in the
single direction the excess grows fastest and long in the rest. Measured on this family
the anisotropy is large and grows toward the locus, which is exactly the regime the ball
count would need. So the inradius bounds one direction and says nothing about cell
VOLUME, and the atlas question is open rather than closed.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.CongruenceRobustness
import Gtz.Design.TraceIdentity
import Gtz.Reduction.Deflation
import Gtz.Reduction.RatCertificate

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- The domination gap of a subset is symmetric. -/
theorem subsetSum_sub_one_transpose (D : WeightedDesign m k) (Q : Finset (Fin m)) :
    (subsetSum D Q - 1)ᵀ = subsetSum D Q - 1 := by
  rw [Matrix.transpose_sub, subsetSum_transpose, Matrix.transpose_one]

/-- **A certificate's gate covers a ball of designs.** A single LDL congruence
`Lᵀ(S_Q − 1)L = diagonal d` with diagonal floor `diagFloor` and entries capped by
`pivotBound` certifies the gate of EVERY design whose base Gram is entrywise within

    diagFloor / (k³ · pivotBound²)

of the certified one — the same `(L, d)`, no recomputation, no new factorization.

This is the half of the branch-(a) certificate that genuinely defines an open cell. -/
theorem gate_posDef_of_nearby_design
    {certified nearby : WeightedDesign m k} {Q : Finset (Fin m)}
    {L : Matrix (Fin k) (Fin k) ℝ} {d : Fin k → ℝ}
    {diagFloor entryBound pivotBound : ℝ}
    (hLdet : IsUnit L.det)
    (hLDL : Lᵀ * (subsetSum certified Q - 1) * L = Matrix.diagonal d)
    (hfloor : ∀ i, diagFloor ≤ d i)
    (hL : ∀ i j, |L i j| ≤ pivotBound) (hEnonneg : 0 ≤ entryBound)
    (hclose : ∀ i j,
      |subsetSum nearby Q i j - subsetSum certified Q i j| ≤ entryBound)
    (hradius : entryBound * k ^ 3 * pivotBound ^ 2 < diagFloor) :
    (subsetSum nearby Q - 1).PosDef := by
  have hsplit : subsetSum nearby Q - 1
      = (subsetSum certified Q - 1) + (subsetSum nearby Q - subsetSum certified Q) := by
    abel
  have hEsym : (subsetSum nearby Q - subsetSum certified Q)ᵀ
      = subsetSum nearby Q - subsetSum certified Q := by
    rw [Matrix.transpose_sub, subsetSum_transpose, subsetSum_transpose]
  rw [hsplit]
  exact posDef_of_congruence_entryBound (subsetSum_sub_one_transpose certified Q) hEsym
    hLdet hLDL hfloor (fun i j => by simpa using hclose i j) hL hEnonneg hradius

/-- **The certificate consumed at a nearby design.** The gate travels with the
certificate; the outsider excess must be re-supplied at the new design. Splitting the
two hypotheses this way is the honest shape of "one certificate covers a cell": the
cell is cut out by the second hypothesis alone. -/
theorem certificate_ball_dominates
    {certified nearby : WeightedDesign m k} (hk : 1 ≤ k) {Q : Finset (Fin m)}
    (hcard : Q.card = k + 1)
    {L : Matrix (Fin k) (Fin k) ℝ} {d : Fin k → ℝ}
    {diagFloor entryBound pivotBound : ℝ}
    (hLdet : IsUnit L.det)
    (hLDL : Lᵀ * (subsetSum certified Q - 1) * L = Matrix.diagonal d)
    (hfloor : ∀ i, diagFloor ≤ d i)
    (hL : ∀ i j, |L i j| ≤ pivotBound) (hEnonneg : 0 ≤ entryBound)
    (hclose : ∀ i j,
      |subsetSum nearby Q i j - subsetSum certified Q i j| ≤ entryBound)
    (hradius : entryBound * k ^ 3 * pivotBound ^ 2 < diagFloor)
    (hexcess : ∑ e ∈ Qᶜ, nearby.weight e * (pivot nearby Q e - 1) ≤ 0) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates nearby C := by
  have hgate := gate_posDef_of_nearby_design hLdet hLDL hfloor hL hEnonneg hclose hradius
  obtain ⟨dropped, hdropped, hdom⟩ := pigeonhole nearby hk Q hgate hcard hexcess
  refine ⟨Q.erase dropped, ?_, hdom⟩
  rw [Finset.card_erase_of_mem hdropped, hcard]
  omega

end Gtz

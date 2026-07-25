/-
# Certificate robustness: how far an LDL congruence certificate reaches

The rational certificate layer (`Gtz.Reduction.RatCertificate`) certifies ONE design at
a time: its gate hypothesis `Lᵀ(S_Q − 1)L = diagonal d` is an EQUATION in the design, so
a fixed pair `(L, d)` names a single point of the configuration space, not a
neighbourhood.  This file measures how far that single certificate actually reaches.

The answer splits the certificate cleanly in two, and only one half is robust.

* **The gate half is robust, with an explicit radius.**  `Lᵀ X L = diagonal d` with
  `d ≥ diagFloor > 0` survives every symmetric perturbation `E` whose congruated
  quadratic form stays below `diagFloor` — `posDef_of_congruence_perturbed`.  The
  certificate does not have to be recomputed: the SAME `(L, d)` witnesses positive
  definiteness of `X + E`.  `posDef_of_congruence_entryBound` turns that into a
  radius one can compute from the certificate data alone: entrywise `|E i j| ≤ eps`
  and `|L i j| ≤ pivotBound` suffice whenever

      eps · k³ · pivotBound² < diagFloor.

* **The outsider half is not robust at all**, and that is not a defect of this file
  but a fact about the problem.  The pigeonhole hypothesis
  `∑_{e ∉ Q} t_e (q_e − 1) ≤ 0` is non-strict, and it holds with EQUALITY on the tie
  locus (see `Gtz.Ties.SplitTetrahedronTie`, where every base quad carrying the four
  distinct tetrahedron directions has both outsider pivots exactly `1`).  A hypothesis
  that is tight at a point survives no ball around that point.

So a certificate covers a ball whose radius is governed by the certificate's
outsider SLACK, and that slack vanishes on the tie locus.  The gate radius below is
the half that stays bounded away from zero; the honest statement of the other half is
that it is `0` wherever the design ties.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ResolventPerturbation

namespace Gtz

open Matrix

variable {k : ℕ}

/-- **Congruence moves the quadratic form along `L`**: `⟨u, (LᵀEL)u⟩ = ⟨Lu, E(Lu)⟩`.
The single computation every statement below runs on. -/
theorem dotProduct_congruence (E L : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) :
    u ⬝ᵥ ((Lᵀ * E * L) *ᵥ u) = (L *ᵥ u) ⬝ᵥ (E *ᵥ (L *ᵥ u)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_comm u (Lᵀ *ᵥ (E *ᵥ (L *ᵥ u))), dotProduct_mulVec_transpose,
    dotProduct_comm]

/-- A diagonal with a floor bounds its form below by that floor. -/
theorem diagonal_quadForm_floor {d : Fin k → ℝ} {diagFloor : ℝ}
    (hfloor : ∀ i, diagFloor ≤ d i) (u : Fin k → ℝ) :
    diagFloor * (u ⬝ᵥ u) ≤ u ⬝ᵥ (Matrix.diagonal d *ᵥ u) := by
  have hform : u ⬝ᵥ (Matrix.diagonal d *ᵥ u) = ∑ i, d i * u i ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal, sq]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hform, dotProduct_self_eq_sum_sq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hfloor i) (sq_nonneg (u i))

/-- **The gate half of a certificate is robust.** An LDL congruence certificate
`Lᵀ X L = diagonal d` with diagonal floor `diagFloor` still certifies the PERTURBED
matrix `X + E` positive definite, with the very same `(L, d)`, as soon as the
congruated form of `E` is capped strictly below the floor.

No spectra, no operator norms, no recomputation of the factorization: the certificate
is reused verbatim and the perturbation is absorbed by the diagonal's headroom. -/
theorem posDef_of_congruence_perturbed
    {X E L : Matrix (Fin k) (Fin k) ℝ} {d : Fin k → ℝ} {diagFloor perturbBound : ℝ}
    (hXsym : Xᵀ = X) (hEsym : Eᵀ = E) (hLdet : IsUnit L.det)
    (hLDL : Lᵀ * X * L = Matrix.diagonal d)
    (hfloor : ∀ i, diagFloor ≤ d i)
    (hbound : ∀ u : Fin k → ℝ,
      |(L *ᵥ u) ⬝ᵥ (E *ᵥ (L *ᵥ u))| ≤ perturbBound * (u ⬝ᵥ u))
    (hgap : perturbBound < diagFloor) :
    (X + E).PosDef := by
  have hsum : (X + E)ᵀ = X + E := by rw [Matrix.transpose_add, hXsym, hEsym]
  rw [posDef_congr_right hsum hLdet]
  have hexpand : Lᵀ * (X + E) * L = Matrix.diagonal d + Lᵀ * E * L := by
    rw [Matrix.mul_add, Matrix.add_mul, hLDL, Matrix.mul_assoc]
  rw [hexpand]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun u hu => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_add, Matrix.diagonal_transpose, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hEsym, Matrix.mul_assoc]
  · rw [star_trivial, Matrix.add_mulVec, dotProduct_add, dotProduct_congruence]
    have hpos : 0 < u ⬝ᵥ u := dotProduct_self_pos hu
    have hdiag := diagonal_quadForm_floor hfloor u
    have hlower : -(perturbBound * (u ⬝ᵥ u))
        ≤ (L *ᵥ u) ⬝ᵥ (E *ᵥ (L *ᵥ u)) :=
      neg_le_of_abs_le (hbound u)
    nlinarith [hdiag, hlower, hpos, hgap]

/-- **The congruated form of an entrywise-small perturbation is small.** With
`|E i j| ≤ entryBound` and `|L i j| ≤ pivotBound`, the form `⟨Lu, E(Lu)⟩` is capped by
`entryBound · k³ · pivotBound² · ⟨u,u⟩`. Two applications of the same Cauchy–Schwarz
bound `noise_mulVec_sq_le` — once for `E`, once for `L`. -/
theorem abs_congruence_quadForm_le
    {E L : Matrix (Fin k) (Fin k) ℝ} {entryBound pivotBound : ℝ}
    (hE : ∀ i j, |E i j| ≤ entryBound) (hL : ∀ i j, |L i j| ≤ pivotBound)
    (hEnonneg : 0 ≤ entryBound) (u : Fin k → ℝ) :
    |(L *ᵥ u) ⬝ᵥ (E *ᵥ (L *ᵥ u))|
      ≤ entryBound * k ^ 3 * pivotBound ^ 2 * (u ⬝ᵥ u) := by
  set image := L *ᵥ u with himage
  have hLbound := noise_mulVec_sq_le hL u
  have hEbound := noise_mulVec_sq_le hE image
  have hImageNonneg : 0 ≤ image ⬝ᵥ image := dotProduct_self_nonneg image
  have hUnonneg : 0 ≤ u ⬝ᵥ u := dotProduct_self_nonneg u
  -- Cauchy–Schwarz on the form, then the two entrywise caps
  have hcs : (image ⬝ᵥ (E *ᵥ image)) ^ 2
      ≤ (image ⬝ᵥ image) * ((E *ᵥ image) ⬝ᵥ (E *ᵥ image)) :=
    dotProduct_sq_le_mul image (E *ᵥ image)
  have hchain : (image ⬝ᵥ (E *ᵥ image)) ^ 2
      ≤ (entryBound * k * (image ⬝ᵥ image)) ^ 2 := by
    have hstep : (image ⬝ᵥ image) * ((E *ᵥ image) ⬝ᵥ (E *ᵥ image))
        ≤ (image ⬝ᵥ image) * (entryBound ^ 2 * k ^ 2 * (image ⬝ᵥ image)) :=
      mul_le_mul_of_nonneg_left hEbound hImageNonneg
    nlinarith [hcs, hstep]
  have hcapNonneg : 0 ≤ entryBound * k * (image ⬝ᵥ image) := by positivity
  have habs : |image ⬝ᵥ (E *ᵥ image)| ≤ entryBound * k * (image ⬝ᵥ image) :=
    abs_le.mpr (abs_le_of_sq_le_sq' hchain hcapNonneg)
  -- and the image length is capped by the certificate's own entries
  have hfinal : entryBound * k * (image ⬝ᵥ image)
      ≤ entryBound * k ^ 3 * pivotBound ^ 2 * (u ⬝ᵥ u) := by
    have hscaled : entryBound * k * (image ⬝ᵥ image)
        ≤ entryBound * k * (pivotBound ^ 2 * k ^ 2 * (u ⬝ᵥ u)) := by
      refine mul_le_mul_of_nonneg_left hLbound ?_
      positivity
    nlinarith [hscaled]
  exact le_trans habs hfinal

/-- **The certificate's reach, entirely in certificate data.** An LDL congruence
certificate with diagonal floor `diagFloor` and entries capped by `pivotBound`
certifies EVERY symmetric perturbation of `X` whose entries are smaller than

    diagFloor / (k³ · pivotBound²).

This is the explicit covering radius of one certificate — the quantity an atlas
argument would have to integrate against. It depends only on `(L, d)`, never on the
perturbed matrix. -/
theorem posDef_of_congruence_entryBound
    {X E L : Matrix (Fin k) (Fin k) ℝ} {d : Fin k → ℝ}
    {diagFloor entryBound pivotBound : ℝ}
    (hXsym : Xᵀ = X) (hEsym : Eᵀ = E) (hLdet : IsUnit L.det)
    (hLDL : Lᵀ * X * L = Matrix.diagonal d)
    (hfloor : ∀ i, diagFloor ≤ d i)
    (hE : ∀ i j, |E i j| ≤ entryBound) (hL : ∀ i j, |L i j| ≤ pivotBound)
    (hEnonneg : 0 ≤ entryBound)
    (hradius : entryBound * k ^ 3 * pivotBound ^ 2 < diagFloor) :
    (X + E).PosDef :=
  posDef_of_congruence_perturbed hXsym hEsym hLdet hLDL hfloor
    (abs_congruence_quadForm_le hE hL hEnonneg) hradius

end Gtz

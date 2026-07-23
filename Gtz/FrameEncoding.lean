/-
# The frame-encoding dictionary: cleared polynomials = the geometric layer

The P4/C5 exclusion runs on integer-coefficient polynomials in the
`(cos, sin, r)` encoding (gauge `ξ = (r,0)`, `N = 1+2rc`, `D = 1−2rc`,
`P = 1−4r²c_ic_j`). For the kernel to consume the coming Nullstellensatz
cofactors, it needs the bridge "equality design ⟹ guarded-variety point":
each cleared generator must equal (a unit multiple of) the corresponding
kernel-checked geometric condition. The dictionary, verified upstream by 19
sympy identities and here as kernel theorems:

* the cleared tightness `T_ij` is exactly `4·[(1+⟨u_i,u_j⟩)/2 − ν_iν_j]` —
  the conic-form tightness of `TightGraph`;
* the cleared leaf polynomial `g_{i,j}` is exactly
  `2·⟨n_j, J·u_i⟩` — the angular criticality that `leaf_tangency` consumes;
* the leverage dictionary `ℓ = 2/D`, `ℓ·ν = N/D`, and the pair normalizer
  `β_i + β_j = 2P/(D_iD_j)` — the division layer of the encoding.
-/
import Mathlib
import Gtz.TightGraph
import Gtz.SplittingRule

namespace Gtz

open Matrix

/-- **The cleared tightness polynomial is the conic tightness**:
`T_ij = 4·[(1+⟨u_i,u_j⟩)/2 − ν_i·ν_j]` at `ν = 1/2 + r·c`. -/
theorem tight_cleared_eq (leafCos leafSin partnerCos partnerSin moment : ℝ) :
    1 + 2*leafCos*partnerCos + 2*leafSin*partnerSin
        - 2*moment*(leafCos + partnerCos)
        - 4*moment^2*leafCos*partnerCos
      = 4 * ((1 + (leafCos*partnerCos + leafSin*partnerSin)) / 2
        - (1/2 + moment*leafCos) * (1/2 + moment*partnerCos)) := by
  ring

/-- **The cleared leaf polynomial is the angular criticality**:
`g_{i,j} = 2·⟨n_j, J·u_i⟩` — the exact identity behind `leaf_tangency`'s
criticality hypothesis (the workflow's T2, now in the kernel). -/
theorem leaf_cleared_eq_criticality
    (leafCos leafSin partnerCos partnerSin moment : ℝ) :
    partnerSin*leafCos - partnerCos*leafSin
        + moment*leafSin*(1 + 2*moment*partnerCos)
      = 2 * (polarNormal ![moment, 0] ![partnerCos, partnerSin]
          (1/2 + moment*partnerCos)
        ⬝ᵥ rotateQuarter ![leafCos, leafSin]) := by
  simp only [polarNormal, rotateQuarter, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **The leverage dictionary**: `ℓ = 1/(1−ν) = 2/D` at `D = 1−2rc`. -/
theorem leverage_cleared (moment ownCos : ℝ)
    (hgate : 1 - 2*moment*ownCos ≠ 0) :
    1 / (1 - (1/2 + moment*ownCos)) = 2 / (1 - 2*moment*ownCos) := by
  rw [show 1 - (1/2 + moment*ownCos) = (1 - 2*moment*ownCos)/2 by ring,
    one_div_div]

/-- **The β dictionary**: `ℓ·ν = N/D` at `N = 1+2rc`, `D = 1−2rc`. -/
theorem beta_cleared (moment ownCos : ℝ)
    (hgate : 1 - 2*moment*ownCos ≠ 0) :
    2 / (1 - 2*moment*ownCos) * (1/2 + moment*ownCos)
      = (1 + 2*moment*ownCos) / (1 - 2*moment*ownCos) := by
  field_simp

/-- **The pair normalizer**: `β_i + β_j = 2P/(D_i·D_j)` at
`P = 1−4r²c_ic_j` — the two cross terms cancel. -/
theorem pair_normalizer_cleared (moment leafCos partnerCos : ℝ)
    (hleafGate : 1 - 2*moment*leafCos ≠ 0)
    (hpartnerGate : 1 - 2*moment*partnerCos ≠ 0) :
    (1 + 2*moment*leafCos) / (1 - 2*moment*leafCos)
        + (1 + 2*moment*partnerCos) / (1 - 2*moment*partnerCos)
      = 2 * (1 - 4*moment^2*leafCos*partnerCos)
        / ((1 - 2*moment*leafCos) * (1 - 2*moment*partnerCos)) := by
  field_simp
  ring

end Gtz

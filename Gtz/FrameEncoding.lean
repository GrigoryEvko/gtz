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

/-- **The Euler–Chasles biquadratic** (the deep-cycle wall's structural
frame): in half-angle coordinates `x = tan(θ/2)` the cleared tightness is the
symmetric (2,2)-correspondence
`a(1+b)x_i²x_j² − ab(x_i²+x_j²) + 2x_ix_j + b(1+a)` with `a = 1/2+ρ`,
`b = 1/2−ρ` — clone-free walks along the conic are QRT iterates and deep
cycles close on Cayley-torsion loci of `ρ`. Audit-verified upstream; here a
kernel identity. -/
theorem tight_half_angle_biquadratic (leafTan partnerTan moment : ℝ) :
    1 + 2*((1-leafTan^2)/(1+leafTan^2))*((1-partnerTan^2)/(1+partnerTan^2))
        + 2*(2*leafTan/(1+leafTan^2))*(2*partnerTan/(1+partnerTan^2))
        - 2*moment*((1-leafTan^2)/(1+leafTan^2)
          + (1-partnerTan^2)/(1+partnerTan^2))
        - 4*moment^2*((1-leafTan^2)/(1+leafTan^2))
          *((1-partnerTan^2)/(1+partnerTan^2))
      = 4 * ((1/2+moment)*(1+(1/2-moment))*leafTan^2*partnerTan^2
          - (1/2+moment)*(1/2-moment)*(leafTan^2+partnerTan^2)
          + 2*leafTan*partnerTan
          + (1/2-moment)*(1+(1/2+moment)))
        / ((1+leafTan^2)*(1+partnerTan^2)) := by
  have hleafDenom : (1:ℝ)+leafTan^2 ≠ 0 := by positivity
  have hpartnerDenom : (1:ℝ)+partnerTan^2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The biquadratic is a quadratic in the partner** — the QRT reading:
`B(x,y) = L(x)·y² + 2xy + C(x)` with leading `L = a(1+b)x² − ab` and
constant `C = b(1+a) − abx²`. Pure ring; the whole walk dynamics follows. -/
theorem biquadratic_leading_constant (moment leafTan partnerTan : ℝ) :
    (1/2+moment)*(1+(1/2-moment))*leafTan^2*partnerTan^2
        - (1/2+moment)*(1/2-moment)*(leafTan^2+partnerTan^2)
        + 2*leafTan*partnerTan
        + (1/2-moment)*(1+(1/2+moment))
      = ((1/2+moment)*(1+(1/2-moment))*leafTan^2
          - (1/2+moment)*(1/2-moment)) * partnerTan^2
        + 2*leafTan*partnerTan
        + ((1/2-moment)*(1+(1/2+moment))
          - (1/2+moment)*(1/2-moment)*leafTan^2) := by
  ring

/-- **Vieta for tight partners**: two partners of the same conic atom
satisfy `(y₁−y₂)·(L·(y₁+y₂) + 2x) = 0` — subtracting the two quadratics
factors the difference. Pure ring, coefficient-generic. -/
theorem tight_partners_vieta_factor {leading crossTan constant
    firstPartner secondPartner : ℝ}
    (hfirst : leading*firstPartner^2 + 2*crossTan*firstPartner
      + constant = 0)
    (hsecond : leading*secondPartner^2 + 2*crossTan*secondPartner
      + constant = 0) :
    (firstPartner - secondPartner)
      * (leading*(firstPartner + secondPartner) + 2*crossTan) = 0 := by
  linear_combination hfirst - hsecond

/-- **The walk is deterministic** (the QRT step): a clone-free second
partner is UNIQUELY determined by the first — `L·y₂ = −2x − L·y₁` — and
symmetrically the product reads the constant: `L·y₁·y₂ = C`. This is
"clone-free walks along the conic are deterministic QRT iterates", the
dynamical germ of the Poncelet-torsion wall, division-free. -/
theorem qrt_step_deterministic {leading crossTan constant
    firstPartner secondPartner : ℝ}
    (hfirst : leading*firstPartner^2 + 2*crossTan*firstPartner
      + constant = 0)
    (hsecond : leading*secondPartner^2 + 2*crossTan*secondPartner
      + constant = 0)
    (hcloneFree : firstPartner ≠ secondPartner) :
    leading*(firstPartner + secondPartner) = -(2*crossTan)
      ∧ leading*(firstPartner*secondPartner) = constant := by
  have hfactor := tight_partners_vieta_factor hfirst hsecond
  have hsum : leading*(firstPartner + secondPartner) + 2*crossTan = 0 := by
    rcases mul_eq_zero.mp hfactor with hbad | hgood
    · exact absurd (sub_eq_zero.mp hbad) hcloneFree
    · exact hgood
  refine ⟨by linarith, ?_⟩
  -- plug the sum relation back into the first quadratic
  have hproduct : leading*(firstPartner*secondPartner) - constant = 0 := by
    linear_combination (-1) * hfirst + firstPartner * hsum
  linarith

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

/-- **The conic covector annihilates the atom-moment rows** (gaps-stability
S1, the "kernel ⊇ span κ" leg): at conic level `ℓ(1/2 − ⟨u,ξ⟩) = 1`, the
moment row `(1, S, ℓ)` of the Bloch square `S = ℓ·u` pairs to zero against
`κ = (1, ξ, −1/2)` — the design-tangent degeneracy is exactly the focal
conic, at every atom, every rank-2 plane. -/
theorem moment_row_annihilated {lev : ℝ} (unitDir moment : Fin 2 → ℝ)
    (hconic : lev * (1/2 - unitDir ⬝ᵥ moment) = 1) :
    1 + (lev • unitDir) ⬝ᵥ moment + lev * (-(1/2)) = 0 := by
  rw [smul_dotProduct, smul_eq_mul]
  nlinarith [hconic]

end Gtz

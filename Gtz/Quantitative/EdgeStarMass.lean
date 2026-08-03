/-
PROVENANCE.  Harvested by the sweep from the think-realness adjudication rung, which
identified the magnitude half of the edge law as the first consumable form of the
rank-three realness quantum and prototyped every statement below.  The sweep
re-compiled, re-audited and wired it; the mathematics is think-realness's.

# The edge-mass law: the MAGNITUDE half of the edge law

`Gtz.sum_erasePair_weight_mul_atomPairing` is the frame identity read at an
off-diagonal entry: `∑_e t_e p_ce p_ed = p_cd (1 − s_c − s_d)`.  Multiplying by
`p_cd` turns every summand into the oriented triple product of `{c, d, e}`.  The
shipped levers (`Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge`,
`Gtz.one_lt_atomShare_add_atomShare_of_incoherentEdge`) then read only the SIGN of
each summand and conclude an INEQUALITY on the two shares.

This file reads the MAGNITUDE as well.  Over `ℝ` the oriented triple product is
`tripleParity · |p_cd| · |p_ce p_de|` with the magnitude at its FULL value -- that
is `Gtz.tripleParity_mul_abs_atomPairingProduct`, the 2-torsion of the Bargmann
triangle invariant.  Dividing the edge law by `|p_cd|` therefore leaves a signed
sum of EXPLICIT nonnegative masses:

  `∑_e t_e · parity(c,d,e) · |p_ce p_de|  =  |p_cd| (1 − s_c − s_d)`.

Two consequences that the sign-only levers cannot state.  A uniformly signed edge
gives the shares EXACTLY, not merely on one side of `1`:

  all-incoherent  `s_c + s_d = 1 + edgeStarMass / |p_cd|`,
  all-coherent    `s_c + s_d = 1 − edgeStarMass / |p_cd|`,

with `edgeStarMass` the weighted total magnitude, a positive number as soon as one
pairing through the edge is nonzero.  And in general the two shares are pinned
inside a field-blind window of half-width `edgeStarMass / |p_cd|`.

**WHERE THE FIELD ENTERS.**  Over `ℂ` the same edge law holds with the oriented
product replaced by the real part of the Bargmann invariant
`Re⟨g_c,g_d⟩⟨g_d,g_e⟩⟨g_e,g_c⟩`, whose magnitude is only BOUNDED by
`|p_cd||p_ce||p_de|` (`Gtz.IsPhaseFreeAdmissible.triangleCap`).  The shared-axis
trine `Gtz.trineSixData` sets every Bargmann phase to a right angle, so every
summand is `0` while every magnitude is at least `1`; the law then forces
`s_c + s_d = 1` at every edge, which is exactly the uniform share `1/2` that trine
carries, and every triple fails.  Re-imposing the full magnitude is what
`Gtz.not_phaseFreeCovering_six` says is the ONE missing relation, and this file is
that relation in the form the edge law wants.
-/
import Gtz.Quantitative.TwoGraphCollision

namespace Gtz

open Finset

variable {sizeIndex : ℕ}

/-- The **star mass** of an edge: the weighted total MAGNITUDE of the oriented
triple products through `{edgeFirst, edgeSecond}`, with the edge's own factor
`|p_cd|` divided out.  Field-blind: it reads only squared pairings. -/
noncomputable def edgeStarMass (design : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond : Fin sizeIndex) : ℝ :=
  ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
    design.weight other
      * |atomPairing design edgeFirst other * atomPairing design edgeSecond other|

/-- The edge-star mass is a sum of nonnegative terms, since the weights are positive
and the summand is a modulus. -/
theorem edgeStarMass_nonneg (design : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond : Fin sizeIndex) :
    0 ≤ edgeStarMass design edgeFirst edgeSecond :=
  Finset.sum_nonneg fun other _ =>
    mul_nonneg (design.weight_pos other).le (abs_nonneg _)

/-- The star mass is strictly positive as soon as ONE atom off the edge pairs
nontrivially with both endpoints. -/
theorem edgeStarMass_pos (design : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond witness : Fin sizeIndex}
    (hwitnessFirst : witness ≠ edgeFirst) (hwitnessSecond : witness ≠ edgeSecond)
    (hfirst : atomPairing design edgeFirst witness ≠ 0)
    (hsecond : atomPairing design edgeSecond witness ≠ 0) :
    0 < edgeStarMass design edgeFirst edgeSecond := by
  refine Finset.sum_pos' (fun other _ =>
    mul_nonneg (design.weight_pos other).le (abs_nonneg _)) ⟨witness, ?_, ?_⟩
  · exact Finset.mem_erase.2 ⟨hwitnessSecond,
      Finset.mem_erase.2 ⟨hwitnessFirst, Finset.mem_univ _⟩⟩
  · exact mul_pos (design.weight_pos witness) (abs_pos.2 (mul_ne_zero hfirst hsecond))

/-- **THE EDGE-MASS LAW.**  The edge law with every summand split into its parity
and its full magnitude.  This is the point where the realness of the design is
spent: over `ℂ` the magnitude factor is only an upper bound. -/
theorem sum_erasePair_weight_mul_tripleParity_mul_absPairing
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond)
    (hpairing : atomPairing design edgeFirst edgeSecond ≠ 0) :
    ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        design.weight other
          * (tripleParity design edgeFirst edgeSecond other
            * |atomPairing design edgeFirst other
              * atomPairing design edgeSecond other|)
      = |atomPairing design edgeFirst edgeSecond|
        * (1 - atomShare design edgeFirst - atomShare design edgeSecond) := by
  have habsPos : 0 < |atomPairing design edgeFirst edgeSecond| := abs_pos.2 hpairing
  refine mul_left_cancel₀ (ne_of_gt habsPos) ?_
  have hscaled : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      |atomPairing design edgeFirst edgeSecond|
          * (design.weight other
            * (tripleParity design edgeFirst edgeSecond other
              * |atomPairing design edgeFirst other
                * atomPairing design edgeSecond other|))
        = atomPairing design edgeFirst edgeSecond
          * (design.weight other
            * (atomPairing design edgeFirst other
              * atomPairing design other edgeSecond)) := by
    intro other _
    have hcarry := tripleParity_mul_abs_atomPairingProduct design edgeFirst edgeSecond other
    have hsplit : |atomPairing design edgeFirst edgeSecond
          * atomPairing design edgeFirst other * atomPairing design edgeSecond other|
        = |atomPairing design edgeFirst edgeSecond|
          * |atomPairing design edgeFirst other * atomPairing design edgeSecond other| := by
      rw [mul_assoc, abs_mul]
    rw [hsplit] at hcarry
    rw [atomPairing_comm design other edgeSecond]
    linear_combination design.weight other * hcarry
  have hsq : |atomPairing design edgeFirst edgeSecond|
      * |atomPairing design edgeFirst edgeSecond|
      = atomPairing design edgeFirst edgeSecond
        * atomPairing design edgeFirst edgeSecond := abs_mul_abs_self _
  rw [Finset.mul_sum, Finset.sum_congr rfl hscaled, ← Finset.mul_sum,
    sum_erasePair_weight_mul_atomPairing design hedge]
  linear_combination
    (-(1 - atomShare design edgeFirst - atomShare design edgeSecond)) * hsq

/-- The two shares are pinned inside a field-blind window whose half-width is the
star mass over the edge magnitude.  (This half is valid over `ℂ` too -- it is the
triangle inequality applied to the same law.) -/
theorem abs_one_sub_atomShare_add_atomShare_mul_absPairing_le_edgeStarMass
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond)
    (hpairing : atomPairing design edgeFirst edgeSecond ≠ 0) :
    |atomPairing design edgeFirst edgeSecond|
        * |1 - atomShare design edgeFirst - atomShare design edgeSecond|
      ≤ edgeStarMass design edgeFirst edgeSecond := by
  have hlaw := sum_erasePair_weight_mul_tripleParity_mul_absPairing design hedge hpairing
  have hbound : |∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      design.weight other
        * (tripleParity design edgeFirst edgeSecond other
          * |atomPairing design edgeFirst other
            * atomPairing design edgeSecond other|)|
      ≤ edgeStarMass design edgeFirst edgeSecond := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro other _
    have hweight := (design.weight_pos other).le
    have habsParity : |tripleParity design edgeFirst edgeSecond other| = 1 := by
      rcases tripleParity_eq_one_or_neg_one design edgeFirst edgeSecond other with h | h <;>
        rw [h] <;> norm_num
    rw [abs_mul, abs_of_nonneg hweight, abs_mul, habsParity, abs_abs, one_mul]
  rw [hlaw, abs_mul, abs_abs] at hbound
  exact hbound

/-- **THE ALL-INCOHERENT EDGE, EXACTLY.**  Sharpens
`Gtz.one_lt_atomShare_add_atomShare_of_incoherentEdge` from a strict inequality to
an identity with an explicit positive excess. -/
theorem atomShare_add_atomShare_eq_one_add_of_incoherentEdge
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond)
    (hpairing : atomPairing design edgeFirst edgeSecond ≠ 0)
    (hincoherent : ∀ other : Fin sizeIndex, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = -1) :
    atomShare design edgeFirst + atomShare design edgeSecond
      = 1 + edgeStarMass design edgeFirst edgeSecond
        / |atomPairing design edgeFirst edgeSecond| := by
  have habsPos : 0 < |atomPairing design edgeFirst edgeSecond| := abs_pos.2 hpairing
  have hne : |atomPairing design edgeFirst edgeSecond| ≠ 0 := ne_of_gt habsPos
  have hlaw := sum_erasePair_weight_mul_tripleParity_mul_absPairing design hedge hpairing
  have hcancel : (∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      design.weight other
        * (tripleParity design edgeFirst edgeSecond other
          * |atomPairing design edgeFirst other
            * atomPairing design edgeSecond other|))
      + edgeStarMass design edgeFirst edgeSecond = 0 := by
    rw [edgeStarMass, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun other hother => ?_
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    rw [hincoherent other hother.2 hother.1]
    ring
  have hkey : |atomPairing design edgeFirst edgeSecond|
      * (1 - atomShare design edgeFirst - atomShare design edgeSecond)
      + edgeStarMass design edgeFirst edgeSecond = 0 := by
    rw [← hlaw]; exact hcancel
  field_simp
  linear_combination -hkey

/-- **THE ALL-COHERENT EDGE, EXACTLY.**  Sharpens
`Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge` the same way. -/
theorem atomShare_add_atomShare_eq_one_sub_of_coherentEdge
    (design : WeightedDesign sizeIndex 3) {edgeFirst edgeSecond : Fin sizeIndex}
    (hedge : edgeFirst ≠ edgeSecond)
    (hpairing : atomPairing design edgeFirst edgeSecond ≠ 0)
    (hcoherent : ∀ other : Fin sizeIndex, other ≠ edgeFirst → other ≠ edgeSecond →
      tripleParity design edgeFirst edgeSecond other = 1) :
    atomShare design edgeFirst + atomShare design edgeSecond
      = 1 - edgeStarMass design edgeFirst edgeSecond
        / |atomPairing design edgeFirst edgeSecond| := by
  have habsPos : 0 < |atomPairing design edgeFirst edgeSecond| := abs_pos.2 hpairing
  have hne : |atomPairing design edgeFirst edgeSecond| ≠ 0 := ne_of_gt habsPos
  have hlaw := sum_erasePair_weight_mul_tripleParity_mul_absPairing design hedge hpairing
  have hsame : (∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      design.weight other
        * (tripleParity design edgeFirst edgeSecond other
          * |atomPairing design edgeFirst other
            * atomPairing design edgeSecond other|))
      = edgeStarMass design edgeFirst edgeSecond := by
    rw [edgeStarMass]
    refine Finset.sum_congr rfl fun other hother => ?_
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hother
    rw [hcoherent other hother.2 hother.1]
    ring
  have hkey : |atomPairing design edgeFirst edgeSecond|
      * (1 - atomShare design edgeFirst - atomShare design edgeSecond)
      = edgeStarMass design edgeFirst edgeSecond := by
    rw [← hlaw]; exact hsame
  field_simp
  linear_combination -hkey

end Gtz

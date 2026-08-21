/-
# The two-zero stratum of a `(5,3)` design, killed

`Gtz.k2Frame_kill` closes the two-zero stratum for frame scalars.
`Gtz.tripleGapDet_eq_frame_coords` says every gap determinant may be read in an
orthonormal frame.  Putting the two together removes the frame from the
statement: what is left is a hypothesis about a design and two probes.

## The adapted frame

Take the axis atom `x` of unit leverage whose pairings with the two plane atoms
vanish — that is the two-zero condition — and any orthonormal pair `vh, nh` of
its orthogonal complement with `vh` carrying the outside line.  Then

* the two plane atoms have zero axis coordinate, by the two-zero condition,
* the two outside atoms have zero `nh` coordinate: the first by the choice of
  `vh`, the second by the collinearity (`Gtz.k2FivePlane_outside_nhat_zero`),

so in that frame the five atoms sit exactly as `Gtz.k2Frame_kill` wants them.
The four relations it consumes are `Gtz.k2FivePlane_relations`, the excess
equation is `Gtz.k2FiveAxis_excess_eq`, and the budget is
`Gtz.k2FiveAxis_budget` — all three already proved at design level.

## What is assumed and what is not

Nothing here assumes a normal form.  The probes are universally quantified and
their only properties are orthonormality, orthogonality to the axis, and that
`vh` carries the outside line.  Producing such a pair from a design is a
Gram–Schmidt step in a plane, not a chart.

The plane gap is assumed positive definite through its two Sylvester data.  That
is the stratum's own corank condition, not an extra hypothesis.
-/
import Gtz.Wave.KTwoFrameChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-- **THE TWO-ZERO STRATUM OF A `(5,3)` DESIGN IS EMPTY.**  A design carrying a
unit axis atom orthogonal to the two plane atoms, read in any orthonormal frame
of the axis complement whose first probe carries the outside line, and refusing
the four triples that avoid the axis, does not exist.

Every hypothesis of the frame kill is discharged: the four relations and the
collinearity from Parseval, the excess equation and the budget from the axis
reading, the angle bounds from the plane pair, and the four refusals through the
coordinate transport. -/
theorem k2Five_kill (D : WeightedDesign 5 3)
    (hunit : leverageOf (D.atom 0) = 1)
    (hy : atomPairing D 0 1 = 0) (hz : atomPairing D 0 2 = 0)
    (vh nh : Fin 3 → ℝ)
    (hvv : vh ⬝ᵥ vh = 1) (hnn : nh ⬝ᵥ nh = 1) (hvn : vh ⬝ᵥ nh = 0)
    (hv0 : D.atom 0 ⬝ᵥ vh = 0) (hn0 : D.atom 0 ⬝ᵥ nh = 0)
    (hdn : D.atom 3 ⬝ᵥ nh = 0)
    (hal : atomPairing D 3 0 ≠ 0) (hax : atomPairing D 4 0 ≠ 0)
    (hp : D.atom 3 ⬝ᵥ vh ≠ 0)
    (hB11 : 0 < (D.atom 1 ⬝ᵥ vh)^2 + (D.atom 2 ⬝ᵥ vh)^2 - 1)
    (hdet : 0 < ((D.atom 1 ⬝ᵥ vh)^2 + (D.atom 2 ⬝ᵥ vh)^2 - 1)
        * ((D.atom 1 ⬝ᵥ nh)^2 + (D.atom 2 ⬝ᵥ nh)^2 - 1)
        - ((D.atom 1 ⬝ᵥ vh)*(D.atom 1 ⬝ᵥ nh)
            + (D.atom 2 ⬝ᵥ vh)*(D.atom 2 ⬝ᵥ nh))^2)
    (hRyzd : tripleGapDet (D.atom 1) (D.atom 2) (D.atom 3) ≤ 0)
    (hRyze : tripleGapDet (D.atom 1) (D.atom 2) (D.atom 4) ≤ 0)
    (hRyde : tripleGapDet (D.atom 1) (D.atom 3) (D.atom 4) ≤ 0)
    (hRzde : tripleGapDet (D.atom 2) (D.atom 3) (D.atom 4) ≤ 0) :
    False := by
  -- the frame, and its orthonormality in the order the transport wants
  have hxx : D.atom 0 ⬝ᵥ D.atom 0 = 1 := by
    simpa only [leverageOf, dotProduct, Fin.sum_univ_three, sq] using hunit
  have hvx : vh ⬝ᵥ D.atom 0 = 0 := by rw [dotProduct_comm]; exact hv0
  have hnx : nh ⬝ᵥ D.atom 0 = 0 := by rw [dotProduct_comm]; exact hn0
  have key : ∀ a b c : Fin 3 → ℝ, tripleGapDet a b c
      = tripleGapDet ![a ⬝ᵥ vh, a ⬝ᵥ nh, a ⬝ᵥ D.atom 0]
          ![b ⬝ᵥ vh, b ⬝ᵥ nh, b ⬝ᵥ D.atom 0]
          ![c ⬝ᵥ vh, c ⬝ᵥ nh, c ⬝ᵥ D.atom 0] :=
    fun a b c => tripleGapDet_eq_frame_coords hvv hnn hxx hvn hvx hnx a b c
  -- the vanishing coordinates
  have h1x : D.atom 1 ⬝ᵥ D.atom 0 = 0 := by
    rw [dotProduct_comm]; exact hy
  have h2x : D.atom 2 ⬝ᵥ D.atom 0 = 0 := by
    rw [dotProduct_comm]; exact hz
  have h4n : D.atom 4 ⬝ᵥ nh = 0 :=
    k2FivePlane_outside_nhat_zero D hunit hy hz nh hn0 hdn hax
  -- the four Parseval relations
  obtain ⟨hr1, hr2, hr3, hrcol⟩ :=
    k2FivePlane_relations D hunit hy hz vh nh hvv hnn hvn hv0 hn0 hdn hax
  -- the axis reading and the budget
  have hexc := k2FiveAxis_excess_eq D hunit hy hz
  have hbud := k2FiveAxis_budget D
  -- transport the four refusals into frame coordinates
  rw [key (D.atom 1) (D.atom 2) (D.atom 3), h1x, h2x, hdn] at hRyzd
  rw [key (D.atom 1) (D.atom 2) (D.atom 4), h1x, h2x, h4n] at hRyze
  rw [key (D.atom 1) (D.atom 3) (D.atom 4), h1x, hdn, h4n] at hRyde
  rw [key (D.atom 2) (D.atom 3) (D.atom 4), h2x, hdn, h4n] at hRzde
  exact k2Frame_kill (y1 := D.atom 1 ⬝ᵥ vh) (y2 := D.atom 1 ⬝ᵥ nh)
    (z1 := D.atom 2 ⬝ᵥ vh) (z2 := D.atom 2 ⬝ᵥ nh)
    (al := atomPairing D 3 0) (be := atomPairing D 4 0)
    (p := D.atom 3 ⬝ᵥ vh) (v := D.atom 4 ⬝ᵥ vh)
    (ty := D.weight 1) (tz := D.weight 2)
    (td := D.weight 3) (te := D.weight 4)
    (D.weight_pos 1) (D.weight_pos 2) (D.weight_pos 3) (D.weight_pos 4)
    hal hax hp hr1 hr2 hr3 (by linear_combination hrcol)
    (by linarith) (by linarith) hB11 hdet
    hRyzd hRyze hRyde hRzde

end Gtz

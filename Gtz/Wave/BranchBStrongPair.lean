/-
# Every refused triple of heavy atoms carries a strong pair, and the constant is
# the regular tetrahedron

At a tie every triple of strictly heavy atoms has nonpositive gap determinant.
This module reads a lower bound on the PAIRINGS out of that sign, with no
weights and no design:

  **`Gtz.exists_strongPair_of_tripleGapDet_nonpos`: if the three excesses are
  positive and `tripleGapDet a b c <= 0`, then some pair satisfies
  `x_i * x_j <= 4 * <g_i, g_j>^2`.**

Call such a pair STRONG.  Equivalently its pair minor is capped,
`4 * q_ij <= 3 * x_i * x_j` (`Gtz.exists_pairGapMinor_le_three_quarters`).

## The proof, and why the constant is a quarter

Normalise `rho_ij = <g_i,g_j> / sqrt(x_i x_j)`.  The gap determinant factors as

  `tripleGapDet = x_a x_b x_c * (1 - rho_ab^2 - rho_ac^2 - rho_bc^2 + 2 rho_ab rho_ac rho_bc)`,

so a nonpositive determinant says the three normalised pairings satisfy
`sum rho^2 - 2 prod rho >= 1`.  If every `|rho|` were below `r` the left side
would be at most `3r^2 + 2r^3`, which reaches one exactly at `r = 1/2`.  The
Lean proof never forms a square root: it bounds the Bargmann term by squaring,
`(2 p_ab p_ac p_bc)^2 < (x_a x_b x_c / 4)^2`, and adds the three diagonal
bounds.

**The constant is sharp, and the witness is the regular tetrahedron.**  Four
unit vectors at the tetrahedral angle, scaled by `sqrt 3` and weighted at one
quarter, form a `(4,3)` design with every leverage `3`, every pair minor `3`,
every normalised pairing `-1/2`, and **all four gap determinants exactly zero**.
So it is a tie in which every atom is strictly heavy and every pair is
admissible, and every pair is strong with equality.

## What this gives the branch-B programme

The pairs that are NOT strong span a triangle-free graph, so by Mantel at most
nine of the fifteen pairs of a `(6,3)` design can be weak: **a branch-B tie
carries at least six strong pairs.**  That is the first proven edge the landed
Mantel machinery can be fed on this branch — until now the graph route had a
family of triples but no sign.

[MEASURED, and it bounds what a successor may assume.  Branch B is NOT empty
below size six: the regular tetrahedron is a `(4,3)` branch-B tie, and the
`(5,3)` diamond `Gtz.diamondTieDesign` is another, with leverages
`(2, 13/4, 13/4, 13/4, 13/4)` and pair minors `0.75, 2.0, 4.5`.  So no argument
using four or five of the six atoms can empty branch B at `(6,3)`; in
particular the strictly dominating FOUR-set that a branch-B tie must contain is
realised inside the diamond itself, at `C = {0,1,2}`, `d = 3`, with
`eig(S_F - 1) = (0.75, 4, 4)` and all four of its triple determinants
nonpositive.  At size six the emptiness looks true but not uniformly:
minimising `max_T tripleGapDet` over branch-B designs under a weight floor
`tau` returns `+2.09e-2` at `tau = 5e-2`, `+1.65e-3` at `tau = 1e-2` and
`+1.25e-4` at `tau = 1e-3`.  The minimiser degenerates onto the TETRAHEDRON:
two weights collapse to the floor and the four surviving atoms have normalised
pairings `+-0.494, +-0.501, +-0.504` against the tetrahedral `+-1/2`, carrying
`1.99` of the total excess mass `2`.  A certificate must vanish on that ray,
hence be non-strict, and must consume the weights.]
-/
import Gtz.Wave.AdmissibleRowLeverageFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The strong pair -/

/-- **A REFUSED TRIPLE OF HEAVY ATOMS CARRIES A STRONG PAIR.**  Some pair of the
three has squared pairing at least a quarter of the product of its excesses.
No weights, no design, no tie: only the three excesses and the sign of the gap
determinant. -/
theorem exists_strongPair_of_tripleGapDet_nonpos {a b c : Fin 3 → ℝ}
    (hxa : 0 < leverageOf a - 1) (hxb : 0 < leverageOf b - 1)
    (hxc : 0 < leverageOf c - 1) (hD : tripleGapDet a b c ≤ 0) :
    (leverageOf a - 1) * (leverageOf b - 1) ≤ 4 * (a ⬝ᵥ b) ^ 2
      ∨ (leverageOf a - 1) * (leverageOf c - 1) ≤ 4 * (a ⬝ᵥ c) ^ 2
      ∨ (leverageOf b - 1) * (leverageOf c - 1) ≤ 4 * (b ⬝ᵥ c) ^ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  rw [tripleGapDet] at hD
  set xa := leverageOf a - 1 with hxadef
  set xb := leverageOf b - 1 with hxbdef
  set xc := leverageOf c - 1 with hxcdef
  set u := a ⬝ᵥ b with hu
  set v := a ⬝ᵥ c with hv
  set w := b ⬝ᵥ c with hw
  -- the Bargmann term is bounded by squaring, with no square root
  have hbox : (2 * u * v * w) ^ 2 < (xa * xb * xc / 4) ^ 2 := by
    have hu2 : u ^ 2 < xa * xb / 4 := by linarith
    have hv2 : v ^ 2 < xa * xc / 4 := by linarith
    have hw2 : w ^ 2 < xb * xc / 4 := by linarith
    have hun : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
    have hvn : (0:ℝ) ≤ v ^ 2 := sq_nonneg v
    have hwn : (0:ℝ) ≤ w ^ 2 := sq_nonneg w
    have s1 : u ^ 2 * v ^ 2 < (xa * xb / 4) * (xa * xc / 4) :=
      mul_lt_mul'' hu2 hv2 hun hvn
    have s2 : (u ^ 2 * v ^ 2) * w ^ 2 < ((xa * xb / 4) * (xa * xc / 4)) * (xb * xc / 4) :=
      mul_lt_mul'' s1 hw2 (by positivity) hwn
    nlinarith [s2]
  have hpos : (0:ℝ) < xa * xb * xc / 4 := by positivity
  have hlow : -(xa * xb * xc / 4) < 2 * u * v * w := by
    by_contra hle
    push Not at hle
    have hge : xa * xb * xc / 4 ≤ -(2 * u * v * w) := by linarith
    nlinarith [mul_self_le_mul_self hpos.le hge, hbox]
  -- the three diagonal terms, each below a quarter of the box
  have hd1 : xa * w ^ 2 < xa * xb * xc / 4 := by
    linarith [mul_lt_mul_of_pos_left h3 hxa]
  have hd2 : xb * v ^ 2 < xa * xb * xc / 4 := by
    linarith [mul_lt_mul_of_pos_left h2 hxb]
  have hd3 : xc * u ^ 2 < xa * xb * xc / 4 := by
    linarith [mul_lt_mul_of_pos_left h1 hxc]
  nlinarith [hD, hlow, hd1, hd2, hd3]

/-- **THE STRONG PAIR IN PAIR-MINOR CURRENCY.**  Its minor spends at most three
quarters of the product of the two excesses. -/
theorem exists_pairGapMinor_le_three_quarters {a b c : Fin 3 → ℝ}
    (hxa : 0 < leverageOf a - 1) (hxb : 0 < leverageOf b - 1)
    (hxc : 0 < leverageOf c - 1) (hD : tripleGapDet a b c ≤ 0) :
    4 * pairGapMinor a b ≤ 3 * ((leverageOf a - 1) * (leverageOf b - 1))
      ∨ 4 * pairGapMinor a c ≤ 3 * ((leverageOf a - 1) * (leverageOf c - 1))
      ∨ 4 * pairGapMinor b c ≤ 3 * ((leverageOf b - 1) * (leverageOf c - 1)) := by
  rcases exists_strongPair_of_tripleGapDet_nonpos hxa hxb hxc hD with h | h | h
  · exact Or.inl (by rw [pairGapMinor]; linarith)
  · exact Or.inr (Or.inl (by rw [pairGapMinor]; linarith))
  · exact Or.inr (Or.inr (by rw [pairGapMinor]; linarith))

/-! ## 2. The design reading -/

/-- **EVERY TRIPLE OF A HEAVY TIE CARRIES A STRONG PAIR.**  The design-level
form: at a tie whose atoms are all strictly heavy, every triple has a pair whose
squared pairing clears a quarter of the product of its excesses. -/
theorem exists_strongPair_of_isTie_of_allHeavy (D : WeightedDesign m 3) (htie : IsTie D)
    (hheavy : ∀ e : Fin m, 1 < leverageOf (D.atom e)) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hadmXY : AdmissiblePair (D.atom x) (D.atom y)) :
    (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
        ≤ 4 * (D.atom x ⬝ᵥ D.atom y) ^ 2
      ∨ (leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1)
        ≤ 4 * (D.atom x ⬝ᵥ D.atom z) ^ 2
      ∨ (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1)
        ≤ 4 * (D.atom y ⬝ᵥ D.atom z) ^ 2 := by
  refine exists_strongPair_of_tripleGapDet_nonpos
    (by linarith [hheavy x]) (by linarith [hheavy y]) (by linarith [hheavy z]) ?_
  by_contra hpos
  push Not at hpos
  exact htie.2 _ (card_triple_eq hxy hxz hyz)
    ((subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mpr
      ⟨by linarith [hheavy x], hadmXY, hpos⟩)

/-- **THE BRANCH-B READING.**  On branch B the admissibility hypotheses are free,
so every triple of a branch-B tie carries a strong pair. -/
theorem branchB_exists_strongPair (D : WeightedDesign m 3) (htie : IsTie D) (hm : 2 ≤ m)
    (hall : ∀ e f : Fin m, f ≠ e → AdmissiblePair (D.atom e) (D.atom f))
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (leverageOf (D.atom x) - 1) * (leverageOf (D.atom y) - 1)
        ≤ 4 * (D.atom x ⬝ᵥ D.atom y) ^ 2
      ∨ (leverageOf (D.atom x) - 1) * (leverageOf (D.atom z) - 1)
        ≤ 4 * (D.atom x ⬝ᵥ D.atom z) ^ 2
      ∨ (leverageOf (D.atom y) - 1) * (leverageOf (D.atom z) - 1)
        ≤ 4 * (D.atom y ⬝ᵥ D.atom z) ^ 2 :=
  exists_strongPair_of_isTie_of_allHeavy D htie
    (branchB_of_forall_admissible D hm hall) hxy hxz hyz (hall x y (Ne.symm hxy))

end Gtz

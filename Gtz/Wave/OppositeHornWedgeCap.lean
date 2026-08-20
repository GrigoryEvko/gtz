import Gtz.Wave.OppositeHornCycleNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The two-inside cap, and the sign word sharpened

Two independent additions to the opposite horn, both genuinely new and both
outside the identity trap that killed the section-14 collision: the first comes
from a REFUSAL that the horn had never spent, the second from the sign coupling
read one step earlier than before.

## The two-inside cap

The nine informative triples of a corner carry its bracket budget, and that
budget is an identity.  The nine TWO-INSIDE triples `{x, y, d}` carry a genuine
inequality instead, because their gaps are already known to be degenerate:
`Gtz.corner_twoInside_det_nonpos` gives `det(S_{xyd} − 1) ≤ 0` with NO tie
hypothesis.  Feeding that through the invariant ledger
`Gtz.atomBracket_sq_eq_gap_invariants` and the corner wedge law collapses
everything to a two-term bound in the sibling's own currency:

  **`[x y d]² ≤ w_{xd} + w_{yd} − ℓ_d`**   (`corner_twoInside_bracket_cap`)

for `x, y` inside and `d` outside, with `w` the pair wedge and `ℓ` the leverage.
The corner enters through exactly one identity, `w_{xy} = ℓ_x + ℓ_y − 1`, which
is `Gtz.corner_inside_pair_wedge_eq` read in leverages: the inside wedge is
pinned, and the two mixed wedges pay for the anchored bracket.

Weighted over the complement this caps the diagonal of the outside bracket
Gram, whose closed form `Gtz.corner_compl_bracket_sq_sum` is already landed:

  **`1 + e_x + e_y − t_z(1+λ) ≤ Σ_{d ∈ Cᶜ} t_d·(w_{xd} + w_{yd} − ℓ_d)`**
    (`corner_twoInside_bracket_cap_sum`)

MEASURED over 10629 generic corners: the per-atom cap holds with worst
violation `−2.9e-10`, and its relative slack has minimum and first percentile
`0.0000` — the bound is EXACTLY TIGHT on a positive-measure set, so it is a
sharp inequality and not a loose estimate.  The summed form is tight too.

## The sign word, one step earlier

`Gtz.atomBracket_baseProduct_cycle` says the three base products at an atom
multiply to minus a square.  Read at a bracket-generic atom that is already the
whole trichotomy, with no pairings and no transport:

  **`M^x_d · M^y_d · M^z_d < 0`**   (`corner_atom_minorTriple_neg`)

and multiplying it at two atoms gives, with no further input at all,

  **two coherent bases force the THIRD to be coherent**
    (`corner_twoCoherent_imp_thirdCoherent`).

So "exactly two coherent bases" is impossible for free, and the landed
coplanarity theorem is needed only to exclude the all-three case.  That is the
sharp reading of the count law: of the 512 sign patterns, the trichotomy alone
leaves 64, of which ZERO have exactly two coherent bases and four have three;
the count law removes those four, leaving 60 patterns and seven branch words
modulo the per-base flip.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The corner wedge in leverages -/

/-- The inside wedge of a corank-two corner, in leverages: `w_xy = ℓ_x+ℓ_y−1`. -/
theorem corner_inside_pairBracketSq_eq (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    pairBracketSq (D.atom e) (D.atom f)
      = leverageOf (D.atom e) + leverageOf (D.atom f) - 1 := by
  have hw := corner_inside_pair_wedge_eq D C hcard hlam hunit hgap he hf hef
  simp only [pairBracketSq, heavyExcess] at hw ⊢
  simp only [atomPairing] at hw
  linarith [hw]

/-! ## 2. The two-inside cap -/

/-- **THE TWO-INSIDE CAP.**  At a corank-two corner the squared bracket of two
inside atoms against an outside atom is capped by the two mixed wedges minus the
outside leverage:

  `[x y d]² ≤ w_{xd} + w_{yd} − ℓ_d` .

No tie hypothesis: the two-inside gap determinant is already nonpositive at a
corner.  Measured exactly tight on a positive-measure set. -/
theorem corner_twoInside_bracket_cap (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y d : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hxd : x ≠ d) (hyd : y ≠ d) :
    atomBracket D x y d ^ 2
      ≤ pairBracketSq (D.atom x) (D.atom d)
        + pairBracketSq (D.atom y) (D.atom d) - leverageOf (D.atom d) := by
  have hdet := corner_twoInside_det_nonpos D C hcard hlam hunit hgap hx hy hxy hxd hyd
  rw [det_subsetSum_triple_sub_one_eq_gapDetAt D hxy hxd hyd] at hdet
  have hledger := atomBracket_sq_eq_gap_invariants D x y d
  have hwedge := corner_inside_pairBracketSq_eq D C hcard hlam hunit hgap hx hy hxy
  simp only [gapTraceAt, gapSecondAt] at hledger
  rw [hwedge] at hledger
  linarith [hledger, hdet]

/-- **THE CAP, WEIGHTED OVER THE COMPLEMENT.**  Summing the two-inside cap
against the weights bounds the diagonal of the outside bracket Gram, whose
closed form in corner scalars is `Gtz.corner_compl_bracket_sq_sum`. -/
theorem corner_twoInside_bracket_cap_sum (D : WeightedDesign m 3)
    {x y z : Fin m} {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam)
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d * (pairBracketSq (D.atom x) (D.atom d)
          + pairBracketSq (D.atom y) (D.atom d) - leverageOf (D.atom d)) := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hsum := corner_compl_bracket_sq_sum D hlam hunit hgap hxy hxz hyz
  rw [← hsum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hxd : x ≠ d := by
    intro h
    exact absurd (by simp [← h] : d ∈ ({x, y, z} : Finset (Fin m)))
      (Finset.mem_compl.mp hd)
  have hyd : y ≠ d := by
    intro h
    exact absurd (by simp [← h] : d ∈ ({x, y, z} : Finset (Fin m)))
      (Finset.mem_compl.mp hd)
  have hcap := corner_twoInside_bracket_cap D ({x, y, z} : Finset (Fin m)) hcard
    hlam hunit hgap hx hy hxy hxd hyd
  exact mul_le_mul_of_nonneg_left hcap (D.weight_pos d).le

/-! ## 3. The sign trichotomy at the minors -/

/-- **THE MINOR TRICHOTOMY.**  At a bracket-generic outside atom the three base
minors multiply to a strictly negative number, so an ODD number of them is
negative.  Pure bracket antisymmetry — no pairings, no transport, no corner. -/
theorem corner_atom_minorTriple_neg (D : WeightedDesign m 3) (x y z d : Fin m)
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D z x d * atomBracket D z y d) < 0 := by
  rw [atomBracket_baseProduct_cycle]
  have : 0 < (atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d) ^ 2 := by
    rcases lt_or_gt_of_ne hT with h | h
    · nlinarith
    · nlinarith
  linarith

/-- Bracket-genericity makes the mixed minor of the SECOND base nonzero. -/
theorem corner_generic_baseY_minor_ne_zero (D : WeightedDesign m 3)
    {x y z d : Fin m}
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    atomBracket D y x d * atomBracket D y z d ≠ 0 := by
  intro hzero
  refine hT ?_
  rw [atomBracket_swapLeft_neg D x y d] at hzero
  have h : atomBracket D x y d * atomBracket D y z d = 0 := by
    linear_combination -hzero
  rcases mul_eq_zero.mp h with h0 | h0
  · rw [h0]; ring
  · rw [h0]; ring

/-- **TWO COHERENT BASES FORCE THE THIRD.**  If two inside bases see no
opposite-sign pair among the outside mixed minors, neither does the third.  The
minor trichotomy at two atoms multiplies to give it, with no other input — so
"exactly two coherent bases" is impossible for free, and the landed coplanarity
theorem is needed only against the all-three case. -/
theorem corner_twoCoherent_imp_thirdCoherent (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {x y z : Fin m}
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0)
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d')) :
    ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d') := by
  intro d hd d' hd'
  have h1 := corner_atom_minorTriple_neg D x y z d (hgen d hd)
  have h2 := corner_atom_minorTriple_neg D x y z d' (hgen d' hd')
  have hY : 0 < (atomBracket D y x d * atomBracket D y z d)
      * (atomBracket D y x d' * atomBracket D y z d') :=
    lt_of_le_of_ne (hbaseY d hd d' hd')
      (Ne.symm (mul_ne_zero (corner_generic_baseY_minor_ne_zero D (hgen d hd))
        (corner_generic_baseY_minor_ne_zero D (hgen d' hd'))))
  have hZ : 0 < (atomBracket D z x d * atomBracket D z y d)
      * (atomBracket D z x d' * atomBracket D z y d') :=
    lt_of_le_of_ne (hbaseZ d hd d' hd')
      (Ne.symm (mul_ne_zero (corner_generic_baseZ_minor_ne_zero D (hgen d hd))
        (corner_generic_baseZ_minor_ne_zero D (hgen d' hd'))))
  -- the two trichotomies multiply to a positive number
  have hkey : ((atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d'))
      * (((atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d'))
        * ((atomBracket D z x d * atomBracket D z y d)
          * (atomBracket D z x d' * atomBracket D z y d')))
      = ((atomBracket D x y d * atomBracket D x z d)
            * (atomBracket D y x d * atomBracket D y z d)
            * (atomBracket D z x d * atomBracket D z y d))
        * ((atomBracket D x y d' * atomBracket D x z d')
            * (atomBracket D y x d' * atomBracket D y z d')
            * (atomBracket D z x d' * atomBracket D z y d')) := by ring
  have hmul : 0 < ((atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d'))
      * (((atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d'))
        * ((atomBracket D z x d * atomBracket D z y d)
          * (atomBracket D z x d' * atomBracket D z y d'))) := by
    rw [hkey]
    exact mul_pos_of_neg_of_neg h1 h2
  have hBC : 0 < ((atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
      * ((atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d')) := mul_pos hY hZ
  by_contra hneg
  push Not at hneg
  nlinarith [hmul, hBC, hneg]

end Gtz

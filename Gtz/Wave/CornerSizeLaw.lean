/-
# The size law at a corner: ten of the twenty terms are exact

`Gtz.sum_sixSet_gapDet_eq` totals the twenty gap determinants of a six-atom
design against three invariants of the whole design's gap, with the size spent
in the coefficients `3, 3, −1`.  It is hypothesis-free, and it is the corank-one
arm's first law whose STATEMENT depends on the size.

Its tie consequence, `Gtz.isTie_branchB_sixSet_bound`, needs BRANCH B — every
atom heavy and every pair admissible.  **A corank-two corner is never in branch
B** (`Gtz.cornerForm_not_branchB`): its three inside pair minors are exactly
zero, so its inside pairs are inadmissible and the branch-B hypothesis fails at
the first step.  The size law therefore arrives at the horn with its only tie
consequence unusable.

This module repairs that, by evaluating the corner's own share of the twenty
terms EXACTLY instead of bounding it.

## The corner's share, in closed form

Ten of the twenty triples carry two inside atoms: the corner itself and the nine
two-inside triples.  `Gtz.cornerForm_corner_gapDet_eq_neg_pairGapMinor` kills the
first, and `Gtz.cornerForm_twoInside_gapDet_pure` gives each of the other nine as
a single squared axis bracket.  Summed over the three inside pairs at a fixed
outside atom, `Gtz.cornerForm_axisCross_total` collapses the three brackets and

  **`Σ_{e∈C} det(gap of C∖{e} ∪ {d}) = − λ·(ℓ_d − ⟨u,g_d⟩²)`**

(`Gtz.cornerForm_twoInside_gapDet_atom_total`): the three two-inside triples at an
outside atom total MINUS THE SCALE TIMES THAT ATOM'S TRANSVERSE MASS.  Nothing is
left of the individual brackets.  Totalling over the three outside atoms
(`Gtz.cornerForm_twoInside_gapDet_total`) prices the corner's entire share.

## What the size law becomes

Subtracting that share from `Gtz.sum_sixSet_gapDet_eq` leaves the ten triples a
corner tie must actually kill — the nine informative ones and the complement —
against the size-carrying invariants plus one explicit correction
(`Gtz.cornerForm_sixSet_liveTotal`):

  `Σ_{informative} det + det(gap_{Cᶜ})`
    `= det G − 3·e₂(G) + 3·tr G − 1 + λ·Σ_{d∉C} (ℓ_d − ⟨u,g_d⟩²)` .

Every term on the right is closed: the three invariants of the whole design's
gap, the scale, and the outside atoms' transverse masses.  **The correction is
the corner's own price, and it is strictly positive whenever the outside atoms
are not all parallel to the axis** — so at a corner the size law's right-hand
side is strictly LARGER than the branch-B bound would suggest, and the ten live
determinants have strictly more to absorb.

`Gtz.cornerForm_isTie_sixSet_bound` states the consequence: on the sub-branch
where every live triple refuses through its determinant, that whole right-hand
side is nonpositive.  Since the correction is nonnegative, this is strictly
sharper than `det G − 3·e₂(G) + 3·tr G ≤ 1` and it holds on a stratum where the
branch-B version cannot even be stated.

[MEASURED on the exact corner parametrisation, 6771 corners.  The atom total
reproduces to `2.0e-13`, the stripped size law to `6.1e-13` in both the matrix
form and the closed-scalar form

  `det W + λ⟨u, adj(W) u⟩ − 3·e₂(W) + 3·tr W − 1 + 3λ − 2λ(tr W − ⟨u,W u⟩)` ,

`W = S_{Cᶜ}`.  Branch B is empty at a corner: 0 of 6771, with the inside pair
minors at `3.7e-14`.  `scratchpad/f42/sizelaw.jl`.]
-/
import Gtz.Wave.CornerAxisBridges
import Gtz.Wave.TripleSumSizeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 0. The bracket's outer swap -/

/-- Exchanging the outer two slots of a bracket changes only its sign, so the
squared bracket is invariant. -/
theorem tripleBracket_sq_swap_outer (a b c : Fin 3 → ℝ) :
    tripleBracket a b c ^ 2 = tripleBracket c b a ^ 2 := by
  rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

variable {gx gy gz u : Fin 3 → ℝ} {lam : ℝ}

/-! ## 1. The corner's share of the twenty terms -/

/-- **THE THREE TWO-INSIDE TRIPLES AT AN OUTSIDE ATOM.**  Each is a single
squared axis bracket, and the three brackets are exactly the ones
`Gtz.cornerForm_axisCross_total` totals.  So the three determinants collapse to
minus the scale times the outside atom's transverse mass, with no bracket left:

  `Σ_{e∈C} det(gap of C∖{e} ∪ {d}) = − λ·(ℓ_d − ⟨u,g_d⟩²)` . -/
theorem cornerForm_twoInside_gapDet_atom_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hyz : pairGapMinor gy gz = 0) (gd : Fin 3 → ℝ) :
    tripleGapDet gx gy gd + tripleGapDet gx gz gd + tripleGapDet gy gz gd
      = - lam * (leverageOf gd - (u ⬝ᵥ gd) ^ 2) := by
  -- the corner form is symmetric in its three inside slots
  have hp1 : CornerForm gx gz gy u lam := fun v => by have := h v; linarith [this]
  have hp2 : CornerForm gy gz gx u lam := fun v => by have := h v; linarith [this]
  have e1 := cornerForm_twoInside_gapDet_pure h hu hxy gd
  have e2 := cornerForm_twoInside_gapDet_pure hp1 hu hxz gd
  have e3 := cornerForm_twoInside_gapDet_pure hp2 hu hyz gd
  have hax := cornerForm_axisCross_total h hu gd
  -- each law names its bracket with the axis last; the total names it first
  have s1 : tripleBracket gz gd u ^ 2 = tripleBracket u gd gz ^ 2 :=
    tripleBracket_sq_swap_outer gz gd u
  have s2 : tripleBracket gy gd u ^ 2 = tripleBracket u gd gy ^ 2 :=
    tripleBracket_sq_swap_outer gy gd u
  have s3 : tripleBracket gx gd u ^ 2 = tripleBracket u gd gx ^ 2 :=
    tripleBracket_sq_swap_outer gx gd u
  rw [s1] at e1; rw [s2] at e2; rw [s3] at e3
  -- the scale multiplies the total, so linearise it before adding
  have hlam : lam * tripleBracket u gd gx ^ 2 + lam * tripleBracket u gd gy ^ 2
        + lam * tripleBracket u gd gz ^ 2
      = lam * (leverageOf gd - (u ⬝ᵥ gd) ^ 2) := by
    rw [← hax]; ring
  linarith [e1, e2, e3, hlam]

/-- **THE CORNER'S WHOLE SHARE.**  Ten of the twenty triples carry two inside
atoms.  The corner's own determinant vanishes and the nine two-inside ones total
minus the scale times the outside triple's total transverse mass. -/
theorem cornerForm_twoInside_gapDet_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hyz : pairGapMinor gy gz = 0) (d₁ d₂ d₃ : Fin 3 → ℝ) :
    tripleGapDet gx gy gz
        + (tripleGapDet gx gy d₁ + tripleGapDet gx gz d₁ + tripleGapDet gy gz d₁)
        + (tripleGapDet gx gy d₂ + tripleGapDet gx gz d₂ + tripleGapDet gy gz d₂)
        + (tripleGapDet gx gy d₃ + tripleGapDet gx gz d₃ + tripleGapDet gy gz d₃)
      = - lam * ((leverageOf d₁ - (u ⬝ᵥ d₁) ^ 2)
          + (leverageOf d₂ - (u ⬝ᵥ d₂) ^ 2)
          + (leverageOf d₃ - (u ⬝ᵥ d₃) ^ 2)) := by
  have hc : tripleGapDet gx gy gz = 0 := by
    have := cornerForm_corner_gapDet_eq_neg_pairGapMinor h hu
    rw [hxy] at this; linarith [this]
  have a₁ := cornerForm_twoInside_gapDet_atom_total h hu hxy hxz hyz d₁
  have a₂ := cornerForm_twoInside_gapDet_atom_total h hu hxy hxz hyz d₂
  have a₃ := cornerForm_twoInside_gapDet_atom_total h hu hxy hxz hyz d₃
  have hlin : lam * (leverageOf d₁ - (u ⬝ᵥ d₁) ^ 2)
        + lam * (leverageOf d₂ - (u ⬝ᵥ d₂) ^ 2)
        + lam * (leverageOf d₃ - (u ⬝ᵥ d₃) ^ 2)
      = lam * ((leverageOf d₁ - (u ⬝ᵥ d₁) ^ 2) + (leverageOf d₂ - (u ⬝ᵥ d₂) ^ 2)
          + (leverageOf d₃ - (u ⬝ᵥ d₃) ^ 2)) := by ring
  linarith [hc, a₁, a₂, a₃, hlin]

/-- The corner's share is nonpositive: a transverse mass is a squared cross
length, and the scale of a corner is nonnegative. -/
theorem cornerForm_transverseMass_nonneg (hu : leverageOf u = 1)
    (gd : Fin 3 → ℝ) :
    0 ≤ leverageOf gd - (u ⬝ᵥ gd) ^ 2 := by
  -- Lagrange: the transverse mass is the squared cross length, a sum of squares
  have hw := pairWedge_eq_cross_self u gd
  have hnn : 0 ≤ crossProduct u gd ⬝ᵥ crossProduct u gd := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [← hw, pairWedge, hu] at hnn
  linarith [hnn]

/-! ## 2. A corner is never in branch B -/

/-- **THE BRANCH-B HYPOTHESIS FAILS AT EVERY CORNER.**  Branch B asks that every
pair be admissible; a corner's inside pair minor is exactly zero, and
admissibility is STRICT positivity.  So the size law's branch-B tie consequence
cannot be stated on the corner stratum at all — which is why the corner needs its
own evaluation of the twenty terms. -/
theorem cornerForm_not_branchB {m : ℕ} (D : WeightedDesign m 3)
    {a b : Fin m} (hab : a ≠ b)
    (hax : D.atom a = gx) (hby : D.atom b = gy)
    (hxy : pairGapMinor gx gy = 0) :
    ¬ BranchB D := by
  rintro ⟨-, hadm⟩
  have := hadm a b hab
  rw [hax, hby] at this
  exact cornerForm_insidePair_not_admissible hxy this

/-! ## 3. The size law with the corner's share stripped -/

/-- **THE SIZE LAW AT A CORNER.**  Subtract the corner's exact share from
`Gtz.sum_sixSet_gapDet_eq`.  What is left is exactly the ten triples a corner tie
must kill — the nine informative ones and the complement — against the
size-carrying invariants of the whole design's gap, plus one explicit
correction: the scale times the outside triple's total transverse mass.

The correction is nonnegative (`Gtz.cornerForm_transverseMass_nonneg`), so at a
corner the ten live determinants have STRICTLY MORE to absorb than the
branch-B reading of the same law would demand. -/
theorem cornerForm_sixSet_liveTotal (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hyz : pairGapMinor gy gz = 0) (d₁ d₂ d₃ : Fin 3 → ℝ) :
    (tripleGapDet gx d₁ d₂ + tripleGapDet gx d₁ d₃ + tripleGapDet gx d₂ d₃)
        + (tripleGapDet gy d₁ d₂ + tripleGapDet gy d₁ d₃ + tripleGapDet gy d₂ d₃)
        + (tripleGapDet gz d₁ d₂ + tripleGapDet gz d₁ d₃ + tripleGapDet gz d₂ d₃)
        + tripleGapDet d₁ d₂ d₃
      = (atomMatrix gx + atomMatrix gy + atomMatrix gz + atomMatrix d₁
            + atomMatrix d₂ + atomMatrix d₃ - 1).det
        - 3 * gapSecondInvariant (atomMatrix gx + atomMatrix gy + atomMatrix gz
            + atomMatrix d₁ + atomMatrix d₂ + atomMatrix d₃ - 1)
        + 3 * Matrix.trace (atomMatrix gx + atomMatrix gy + atomMatrix gz
            + atomMatrix d₁ + atomMatrix d₂ + atomMatrix d₃ - 1)
        - 1
        + lam * ((leverageOf d₁ - (u ⬝ᵥ d₁) ^ 2)
            + (leverageOf d₂ - (u ⬝ᵥ d₂) ^ 2)
            + (leverageOf d₃ - (u ⬝ᵥ d₃) ^ 2)) := by
  have hsize := sum_sixSet_gapDet_eq gx gy gz d₁ d₂ d₃
  have hshare := cornerForm_twoInside_gapDet_total h hu hxy hxz hyz d₁ d₂ d₃
  linarith [hsize, hshare]

/-! ## 4. What a corner tie must then absorb -/

/-- **THE CORNER'S SIZE BOUND.**  On the sub-branch where every one of the ten
live triples refuses through its DETERMINANT — the nine informative triples and
the complement — the whole right-hand side of the corner size law is
nonpositive.  Because the correction is nonnegative this is strictly sharper
than the branch-B bound `det G − 3·e₂(G) + 3·tr G ≤ 1`, and unlike that bound it
is available on the corner stratum. -/
theorem cornerForm_isTie_sixSet_bound (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hyz : pairGapMinor gy gz = 0) (d₁ d₂ d₃ : Fin 3 → ℝ)
    (r₁ : tripleGapDet gx d₁ d₂ ≤ 0) (r₂ : tripleGapDet gx d₁ d₃ ≤ 0)
    (r₃ : tripleGapDet gx d₂ d₃ ≤ 0) (r₄ : tripleGapDet gy d₁ d₂ ≤ 0)
    (r₅ : tripleGapDet gy d₁ d₃ ≤ 0) (r₆ : tripleGapDet gy d₂ d₃ ≤ 0)
    (r₇ : tripleGapDet gz d₁ d₂ ≤ 0) (r₈ : tripleGapDet gz d₁ d₃ ≤ 0)
    (r₉ : tripleGapDet gz d₂ d₃ ≤ 0) (r₁₀ : tripleGapDet d₁ d₂ d₃ ≤ 0) :
    (atomMatrix gx + atomMatrix gy + atomMatrix gz + atomMatrix d₁
          + atomMatrix d₂ + atomMatrix d₃ - 1).det
        - 3 * gapSecondInvariant (atomMatrix gx + atomMatrix gy + atomMatrix gz
            + atomMatrix d₁ + atomMatrix d₂ + atomMatrix d₃ - 1)
        + 3 * Matrix.trace (atomMatrix gx + atomMatrix gy + atomMatrix gz
            + atomMatrix d₁ + atomMatrix d₂ + atomMatrix d₃ - 1)
        - 1
        + lam * ((leverageOf d₁ - (u ⬝ᵥ d₁) ^ 2)
            + (leverageOf d₂ - (u ⬝ᵥ d₂) ^ 2)
            + (leverageOf d₃ - (u ⬝ᵥ d₃) ^ 2))
      ≤ 0 := by
  have hlive := cornerForm_sixSet_liveTotal h hu hxy hxz hyz d₁ d₂ d₃
  linarith [hlive, r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀]

/-- The branch-B invariant bound follows from the corner bound, since the
correction the corner adds is nonnegative.  So the corner statement implies the
size law's original reading and is strictly stronger by exactly the corner's own
share. -/
theorem cornerForm_isTie_sixSet_bound_invariants (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (hlam : 0 ≤ lam)
    (hxy : pairGapMinor gx gy = 0) (hxz : pairGapMinor gx gz = 0)
    (hyz : pairGapMinor gy gz = 0) (d₁ d₂ d₃ : Fin 3 → ℝ)
    (r₁ : tripleGapDet gx d₁ d₂ ≤ 0) (r₂ : tripleGapDet gx d₁ d₃ ≤ 0)
    (r₃ : tripleGapDet gx d₂ d₃ ≤ 0) (r₄ : tripleGapDet gy d₁ d₂ ≤ 0)
    (r₅ : tripleGapDet gy d₁ d₃ ≤ 0) (r₆ : tripleGapDet gy d₂ d₃ ≤ 0)
    (r₇ : tripleGapDet gz d₁ d₂ ≤ 0) (r₈ : tripleGapDet gz d₁ d₃ ≤ 0)
    (r₉ : tripleGapDet gz d₂ d₃ ≤ 0) (r₁₀ : tripleGapDet d₁ d₂ d₃ ≤ 0) :
    (atomMatrix gx + atomMatrix gy + atomMatrix gz + atomMatrix d₁
          + atomMatrix d₂ + atomMatrix d₃ - 1).det
        - 3 * gapSecondInvariant (atomMatrix gx + atomMatrix gy + atomMatrix gz
            + atomMatrix d₁ + atomMatrix d₂ + atomMatrix d₃ - 1)
        + 3 * Matrix.trace (atomMatrix gx + atomMatrix gy + atomMatrix gz
            + atomMatrix d₁ + atomMatrix d₂ + atomMatrix d₃ - 1)
      ≤ 1 := by
  have hbound := cornerForm_isTie_sixSet_bound h hu hxy hxz hyz d₁ d₂ d₃
    r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ r₁₀
  have t₁ := cornerForm_transverseMass_nonneg (u := u) hu d₁
  have t₂ := cornerForm_transverseMass_nonneg (u := u) hu d₂
  have t₃ := cornerForm_transverseMass_nonneg (u := u) hu d₃
  nlinarith [hbound, t₁, t₂, t₃, hlam]

end Gtz

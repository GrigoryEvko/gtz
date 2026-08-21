/-
# The axis calculus of a corank-two corner

A corank-two corner is a weak dominator `C = {x,y,z}` whose gap is a nonnegative
multiple of a single rank-one form:

  `S_C − 1 = λ · u uᵀ` ,  `|u| = 1` .

Read as a quadratic form that is ONE equation in one free probe:

  `⟨g_x,v⟩² + ⟨g_y,v⟩² + ⟨g_z,v⟩² = ⟨v,v⟩ + λ⟨u,v⟩²`   for every `v`

(`Gtz.CornerForm`).  This module spends that single equation at FOUR probes and
gets the corner's whole scalar calculus out of it, with no chart, no frame, no
eigenvector and no inverse.

## The probes, and what each one closes

* `v = g_d` — `Gtz.cornerForm_atom_reading`: the three inside atoms read any atom
  by its own leverage plus the axis mass, `Σ_e ⟨g_e,g_d⟩² = ℓ_d + λ⟨u,g_d⟩²`.
* the three coordinate axes — `Gtz.cornerForm_leverage_total`: `Σ_e ℓ_e = 3 + λ`.
* `v = g_a × g_b` — `Gtz.cornerForm_bracket_total`, **THE AXIS ELIMINATION**:

    `Σ_{e ∈ C} [e a b]² = w_ab + λ·[u a b]²` ,

  where `w_ab = ℓ_aℓ_b − ⟨g_a,g_b⟩²` is the pair wedge.  Every axis bracket is a
  bracket total minus a wedge, so `u` can be removed from any corner statement.
* `v = u × g_d` — `Gtz.cornerForm_axisCross_total`: `Σ_e [u g_d g_e]² = ℓ_d −
  ⟨u,g_d⟩²`, the one identity that lets the axis brackets themselves be totalled.

## The three totals at an outside atom

Feeding those back gives, for `d` outside and `e` ranging over `C`, closed forms
with the axis appearing only through the single scalar `⟨u,g_d⟩²`:

* `Gtz.cornerForm_mixed_wedge_total` — `Σ_e w_ed = (2+λ)ℓ_d − λ⟨u,g_d⟩²`
* `Gtz.cornerForm_mixed_pairMinor_total` — `Σ_e q_ed = (λ−1)ℓ_d − λ⟨u,g_d⟩² − λ`
* `Gtz.cornerForm_insidePair_bracket_total` — `Σ_{i<j⊆C} [i j d]² = (1+λ)ℓ_d −
  λ⟨u,g_d⟩²`

with `q_ab = Gtz.pairGapMinor a b` the pair-local Sylvester minor.  The middle
one is the useful one: it decides by a SIGN whether the outside atom `d` has an
admissible partner inside `C` at all, and it costs nothing to evaluate.

## The two-inside determinant, exactly

The ledger `Gtz.tripleGapDet_eq_bracketSq_sub_wedgeSum` — a `ring` identity at
every triple of every design, no corner needed —

  `det(gap_abc) = [abc]² + ℓ_a + ℓ_b + ℓ_c − w_ab − w_ac − w_bc − 1`

collides with the three totals and everything cancels:

  **`det(gap_{x y d}) = − λ·[z g_d u]² − q_xy`**  (`Gtz.cornerForm_twoInside_gapDet`).

Two corollaries follow with no further work.  Taking `d := g_z` makes the bracket
degenerate, so

  **`det(gap_C) = − q_xy = − q_xz = − q_yz`**

(`Gtz.cornerForm_corner_gapDet_eq_neg_pairGapMinor`,
`Gtz.cornerForm_insidePair_pairGapMinor_eq`): at a corner the THREE inside pair
minors are equal, and equal to minus the corner's own gap determinant.  Weak
domination makes both sides nonnegative, so all four vanish
(`Gtz.cornerForm_insidePair_pairGapMinor_eq_zero`), and then the two-inside
determinant is exactly `−λ[z g_d u]²`, nonpositive with an explicit equality
locus: the two-inside triple sits on the boundary exactly when the ERASED inside
atom, the axis and the outside atom are coplanar.

## Why the vanishing inside minor is the corner's real gift

`Gtz.pairGapMinor` vanishing means the pair is NOT admissible
(`Gtz.cornerForm_insidePair_not_admissible`), and admissibility is an EDGE
property while the tie trichotomy is a statement about triangles.  So at a corner
the three inside edges are deleted from the admissibility graph BEFORE any tie
hypothesis is used, and every triple carrying two inside atoms — the dominator
itself and the nine two-inside triples — is dead by Sylvester locality alone
(`Gtz.cornerForm_twoInside_not_posDef`, `Gtz.cornerForm_ten_refusals_free`).
That is the ten free refusals of `Gtz.corner_posDef_triple_inter_le_one` again,
reached through the graph instead of through the determinant, and it says why
they are free: `K₆` minus the inside triangle is exactly the ten triples a corner
tie still has to kill.

[MEASURED, all on the exact corner parametrisation, 10k–17k corners per line.
The four probe laws and the two-inside determinant reproduce to `1.4e-13` or
better (`scratchpad/f42/probe.jl`, `laws.jl`); the inside pair minors vanish to
`4.1e-14`.  Two independent adversarial descents put `max_{d<d'} q_{dd'} ≥
0.2138` over all corners, so at least one OUTSIDE pair is always admissible —
recorded as a target, NOT proved here.  REFUTED in the same runs: summing the
informative determinant over the retained inside atom does NOT decide the horn —
`Σ_x det(gap_{x d d'})` is negative at 48722 of 49845 admissible outside pairs,
and 35868 of them carry no `x` at all with a positive determinant.]
-/
import Gtz.Wave.OppositeHornRefusalBudget
import Gtz.Wave.GramCrossFloor
import Gtz.Wave.TieMantelBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 0. The pair wedge, and the ledger every triple obeys -/

/-- The pair wedge: the squared area of the parallelogram, by Lagrange the
squared length of the cross product. -/
noncomputable def pairWedge (a b : Fin 3 → ℝ) : ℝ :=
  leverageOf a * leverageOf b - (a ⬝ᵥ b) ^ 2

theorem pairWedge_eq_cross_self (a b : Fin 3 → ℝ) :
    pairWedge a b = crossProduct a b ⬝ᵥ crossProduct a b := by
  rw [pairWedge, cross_dot_cross, ← leverageOf_eq_dotProduct,
    ← leverageOf_eq_dotProduct, dotProduct_comm b a]
  ring

theorem pairWedge_comm (a b : Fin 3 → ℝ) : pairWedge a b = pairWedge b a := by
  rw [pairWedge, pairWedge, dotProduct_comm b a]; ring

/-- The pair minor is the wedge less the two leverages plus one. -/
theorem pairGapMinor_eq_pairWedge_sub (a b : Fin 3 → ℝ) :
    pairGapMinor a b = pairWedge a b - leverageOf a - leverageOf b + 1 := by
  rw [pairGapMinor_eq_sub_sq, pairWedge]; ring

/-- **THE TRIPLE LEDGER.**  At every triple of every design the third Sylvester
minor is the squared bracket, plus the leverage total, less the wedge total, less
one.  A `ring` identity in the three leverages and the three pairings — no
positivity, no design, no corner. -/
theorem tripleGapDet_eq_bracketSq_sub_wedgeSum (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleBracket a b c ^ 2
        + leverageOf a + leverageOf b + leverageOf c
        - pairWedge a b - pairWedge a c - pairWedge b c - 1 := by
  rw [sq_tripleBracket_eq_evenAtLeverage_add_cross, evenAtLeverage,
    atomTripleProduct, tripleGapDet, pairWedge, pairWedge, pairWedge]
  ring

/-! ## 1. The corner form -/

/-- **THE CORNER AS ONE EQUATION IN ONE PROBE.**  The three inside atoms of a
corank-two corner read every probe by the probe's own square plus the scale times
the squared axis reading.  This is `S_C − 1 = λ·u uᵀ` with the matrix removed. -/
def CornerForm (gx gy gz u : Fin 3 → ℝ) (lam : ℝ) : Prop :=
  ∀ v : Fin 3 → ℝ,
    (gx ⬝ᵥ v) ^ 2 + (gy ⬝ᵥ v) ^ 2 + (gz ⬝ᵥ v) ^ 2
      = v ⬝ᵥ v + lam * (u ⬝ᵥ v) ^ 2

variable {gx gy gz u : Fin 3 → ℝ} {lam : ℝ}

/-- **PROBE ONE, AT AN ATOM.**  The inside triple reads any vector by its
leverage plus the axis mass it carries. -/
theorem cornerForm_atom_reading (h : CornerForm gx gy gz u lam) (w : Fin 3 → ℝ) :
    (gx ⬝ᵥ w) ^ 2 + (gy ⬝ᵥ w) ^ 2 + (gz ⬝ᵥ w) ^ 2
      = leverageOf w + lam * (u ⬝ᵥ w) ^ 2 := by
  rw [h w, leverageOf_eq_dotProduct]

/-- **PROBE TWO, AT THE AXIS.**  The inside axis readings total `1 + λ`. -/
theorem cornerForm_axis_reading (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) :
    (gx ⬝ᵥ u) ^ 2 + (gy ⬝ᵥ u) ^ 2 + (gz ⬝ᵥ u) ^ 2 = 1 + lam := by
  have h1 := cornerForm_atom_reading h u
  have h2 : u ⬝ᵥ u = 1 := by rw [← leverageOf_eq_dotProduct]; exact hu
  rw [h1, hu, h2]; ring

/-- **PROBE THREE, AT THE COORDINATE AXES.**  The inside leverages total
`3 + λ`: the trace of `1 + λ·u uᵀ`. -/
theorem cornerForm_leverage_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) :
    leverageOf gx + leverageOf gy + leverageOf gz = 3 + lam := by
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have h2 := h ![0, 0, 1]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h0 h1 h2
  have hlx : leverageOf gx = gx 0 ^ 2 + gx 1 ^ 2 + gx 2 ^ 2 := by
    simp [leverageOf, Fin.sum_univ_three]
  have hly : leverageOf gy = gy 0 ^ 2 + gy 1 ^ 2 + gy 2 ^ 2 := by
    simp [leverageOf, Fin.sum_univ_three]
  have hlz : leverageOf gz = gz 0 ^ 2 + gz 1 ^ 2 + gz 2 ^ 2 := by
    simp [leverageOf, Fin.sum_univ_three]
  have hlu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    rw [← hu]; simp [leverageOf, Fin.sum_univ_three]
  rw [hlx, hly, hlz]
  nlinarith [h0, h1, h2, hlu]

/-! ## 2. The axis elimination -/

/-- **THE AXIS ELIMINATION.**  Read the corner form at the cross product of two
vectors: the squared brackets of the inside atoms against that pair total the
pair's wedge plus the scale times the squared AXIS bracket.  Every axis bracket
is therefore a bracket total minus a wedge, so `u` can be eliminated from any
corner statement written in brackets. -/
theorem cornerForm_bracket_total (h : CornerForm gx gy gz u lam)
    (a b : Fin 3 → ℝ) :
    tripleBracket a b gx ^ 2 + tripleBracket a b gy ^ 2
        + tripleBracket a b gz ^ 2
      = pairWedge a b + lam * tripleBracket a b u ^ 2 := by
  have hb : ∀ w : Fin 3 → ℝ, tripleBracket a b w = crossProduct a b ⬝ᵥ w :=
    fun w => tripleBracket_eq_cross_dot a b w
  have hcomm : ∀ w : Fin 3 → ℝ,
      (w ⬝ᵥ crossProduct a b) = crossProduct a b ⬝ᵥ w :=
    fun w => dotProduct_comm w (crossProduct a b)
  have := h (crossProduct a b)
  rw [hcomm gx, hcomm gy, hcomm gz, hcomm u] at this
  rw [hb gx, hb gy, hb gz, hb u, this, pairWedge_eq_cross_self]

/-- The axis elimination in solved form. -/
theorem cornerForm_axisBracket_eq (h : CornerForm gx gy gz u lam)
    (a b : Fin 3 → ℝ) :
    lam * tripleBracket a b u ^ 2
      = tripleBracket a b gx ^ 2 + tripleBracket a b gy ^ 2
        + tripleBracket a b gz ^ 2 - pairWedge a b := by
  rw [cornerForm_bracket_total h a b]; ring

/-- **THE AXIS CROSS TOTAL.**  Read the corner form at `u × g_d`.  The axis term
dies because the bracket of the axis against its own cross product vanishes, so
the axis brackets at `d` total the plain transverse mass `ℓ_d − ⟨u,g_d⟩²`. -/
theorem cornerForm_axisCross_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ) :
    tripleBracket u gd gx ^ 2 + tripleBracket u gd gy ^ 2
        + tripleBracket u gd gz ^ 2
      = leverageOf gd - (u ⬝ᵥ gd) ^ 2 := by
  have hdeg : tripleBracket u gd u = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hb := cornerForm_bracket_total h u gd
  rw [hdeg] at hb
  rw [hb]
  simp only [pairWedge, hu]
  ring

/-! ## 3. The three totals at an outside atom -/

/-- **THE MIXED WEDGE TOTAL.**  The wedges of an outside atom against the three
inside atoms total `(2+λ)ℓ_d − λ⟨u,g_d⟩²`. -/
theorem cornerForm_mixed_wedge_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ) :
    pairWedge gx gd + pairWedge gy gd + pairWedge gz gd
      = (2 + lam) * leverageOf gd - lam * (u ⬝ᵥ gd) ^ 2 := by
  have hlev := cornerForm_leverage_total h hu
  have hread := cornerForm_atom_reading h gd
  simp only [pairWedge]
  have hxd : (gx ⬝ᵥ gd) ^ 2 + (gy ⬝ᵥ gd) ^ 2 + (gz ⬝ᵥ gd) ^ 2
      = leverageOf gd + lam * (u ⬝ᵥ gd) ^ 2 := hread
  -- the leverage total enters multiplied by the outside leverage
  have hprod : leverageOf gx * leverageOf gd + leverageOf gy * leverageOf gd
        + leverageOf gz * leverageOf gd
      = leverageOf gd * (3 + lam) := by
    rw [← hlev]; ring
  linarith [hprod, hxd]

/-- **THE MIXED PAIR MINOR TOTAL.**  The Sylvester pair minors of an outside atom
against the three inside atoms total `(λ−1)ℓ_d − λ⟨u,g_d⟩² − λ`.  This is the
corner's cheapest admissibility test: a nonpositive total forces an inadmissible
mixed pair, and a positive total supplies an admissible one. -/
theorem cornerForm_mixed_pairMinor_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ) :
    pairGapMinor gx gd + pairGapMinor gy gd + pairGapMinor gz gd
      = (lam - 1) * leverageOf gd - lam * (u ⬝ᵥ gd) ^ 2 - lam := by
  have hw := cornerForm_mixed_wedge_total h hu gd
  have hlev := cornerForm_leverage_total h hu
  simp only [pairGapMinor_eq_pairWedge_sub]
  linarith [hw, hlev]

/-- **THE INSIDE-PAIR BRACKET TOTAL.**  The squared brackets of an outside atom
against the three INSIDE PAIRS total `(1+λ)ℓ_d − λ⟨u,g_d⟩²`.  Obtained by
totalling the axis elimination over the three mixed pairs and cancelling the axis
brackets with `Gtz.cornerForm_axisCross_total`. -/
theorem cornerForm_insidePair_bracket_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ) :
    tripleBracket gx gd gy ^ 2 + tripleBracket gx gd gz ^ 2
        + tripleBracket gy gd gz ^ 2
      = (1 + lam) * leverageOf gd - lam * (u ⬝ᵥ gd) ^ 2 := by
  have hx := cornerForm_bracket_total h gx gd
  have hy := cornerForm_bracket_total h gy gd
  have hz := cornerForm_bracket_total h gz gd
  have hax := cornerForm_axisCross_total h hu gd
  -- the degenerate slots vanish
  have hdx : tripleBracket gx gd gx = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hdy : tripleBracket gy gd gy = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hdz : tripleBracket gz gd gz = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdx] at hx; rw [hdy] at hy; rw [hdz] at hz
  -- the axis brackets appearing in hx, hy, hz are the ones hax totals,
  -- up to the sign-free swap of the two leading slots
  have hswx : tripleBracket gx gd u ^ 2 = tripleBracket u gd gx ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hswy : tripleBracket gy gd u ^ 2 = tripleBracket u gd gy ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hswz : tripleBracket gz gd u ^ 2 = tripleBracket u gd gz ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hswx] at hx; rw [hswy] at hy; rw [hswz] at hz
  -- the six mixed brackets pair up two by two
  have hxy : tripleBracket gx gd gy ^ 2 = tripleBracket gy gd gx ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hxz : tripleBracket gx gd gz ^ 2 = tripleBracket gz gd gx ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hyz : tripleBracket gy gd gz ^ 2 = tripleBracket gz gd gy ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hwsum := cornerForm_mixed_wedge_total h hu gd
  rw [← hxy] at hy
  rw [← hxz, ← hyz] at hz
  -- the three axis brackets enter multiplied by the scale, so linearise them first
  have hlamA : lam * tripleBracket u gd gx ^ 2 + lam * tripleBracket u gd gy ^ 2
        + lam * tripleBracket u gd gz ^ 2
      = lam * (leverageOf gd - (u ⬝ᵥ gd) ^ 2) := by
    rw [← hax]; ring
  have hzx : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hzx] at hx hy hz
  linarith [hx, hy, hz, hlamA, hwsum]

/-! ## 4. The two-inside determinant, exactly -/

/-- **THE TWO-INSIDE GAP DETERMINANT.**  For two inside atoms and one outside
atom the third Sylvester minor collapses to a single squared bracket against the
axis, corrected by the inside pair's own minor:

  `det(gap_{x y d}) = − λ·[g_z g_d u]² − q_xy` .

Everything else cancels between the ledger and the three totals — the leverages,
the mixed wedges, the axis mass and the outside leverage all go. -/
theorem cornerForm_twoInside_gapDet (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ) :
    tripleGapDet gx gy gd
      = - lam * tripleBracket gz gd u ^ 2 - pairGapMinor gx gy := by
  have hled := tripleGapDet_eq_bracketSq_sub_wedgeSum gx gy gd
  have hins := cornerForm_insidePair_bracket_total h hu gd
  have hbx := cornerForm_bracket_total h gx gd
  have hby := cornerForm_bracket_total h gy gd
  have hax := cornerForm_axisCross_total h hu gd
  have hdx : tripleBracket gx gd gx = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hdy : tripleBracket gy gd gy = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdx] at hbx; rw [hdy] at hby
  have hswx : tripleBracket gx gd u ^ 2 = tripleBracket u gd gx ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hswy : tripleBracket gy gd u ^ 2 = tripleBracket u gd gy ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hswz : tripleBracket gz gd u ^ 2 = tripleBracket u gd gz ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hswx] at hbx; rw [hswy] at hby
  rw [hswz]
  -- bracket slot permutations, all squared so sign-free
  have hxyd : tripleBracket gx gy gd ^ 2 = tripleBracket gx gd gy ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hyx : tripleBracket gy gd gx ^ 2 = tripleBracket gx gd gy ^ 2 := by
    rw [tripleBracket, tripleBracket, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have hpm : pairGapMinor gx gy
      = pairWedge gx gy - leverageOf gx - leverageOf gy + 1 :=
    pairGapMinor_eq_pairWedge_sub gx gy
  -- linearise the scale against the three axis brackets
  have hlamA : lam * tripleBracket u gd gx ^ 2 + lam * tripleBracket u gd gy ^ 2
        + lam * tripleBracket u gd gz ^ 2
      = lam * (leverageOf gd - (u ⬝ᵥ gd) ^ 2) := by
    rw [← hax]; ring
  have hzx : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hzx] at hbx hby
  rw [hyx] at hby
  rw [hled, hxyd, hpm]
  linarith [hins, hbx, hby, hlamA]

/-- **THE CORNER'S OWN DETERMINANT IS MINUS AN INSIDE PAIR MINOR.**  Take the
outside slot to be the third inside atom: the axis bracket degenerates and the
two-inside law reads `det(gap_C) = − q_xy`. -/
theorem cornerForm_corner_gapDet_eq_neg_pairGapMinor
    (h : CornerForm gx gy gz u lam) (hu : leverageOf u = 1) :
    tripleGapDet gx gy gz = - pairGapMinor gx gy := by
  have := cornerForm_twoInside_gapDet h hu gz
  have hdeg : tripleBracket gz gz u = 0 := by
    rw [tripleBracket, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdeg] at this
  rw [this]; ring

/-- **THE THREE INSIDE PAIR MINORS ARE EQUAL.**  Each is minus the corner's own
gap determinant, so they agree with no positivity input at all. -/
theorem cornerForm_insidePair_pairGapMinor_eq
    (h : CornerForm gx gy gz u lam) (hu : leverageOf u = 1) :
    pairGapMinor gx gy = pairGapMinor gx gz
      ∧ pairGapMinor gx gy = pairGapMinor gy gz := by
  have hxy := cornerForm_corner_gapDet_eq_neg_pairGapMinor h hu
  -- the corner form is symmetric in its three inside slots
  have hperm1 : CornerForm gx gz gy u lam := fun v => by
    have := h v; linarith [this]
  have hperm2 : CornerForm gy gz gx u lam := fun v => by
    have := h v; linarith [this]
  have hxz := cornerForm_corner_gapDet_eq_neg_pairGapMinor hperm1 hu
  have hyz := cornerForm_corner_gapDet_eq_neg_pairGapMinor hperm2 hu
  have hd1 : tripleGapDet gx gz gy = tripleGapDet gx gy gz := by
    rw [tripleGapDet_eq_tripleDetForm, tripleGapDet_eq_tripleDetForm,
      tripleDetForm, tripleDetForm, dotProduct_comm gz gy]
    ring
  have hd2 : tripleGapDet gy gz gx = tripleGapDet gx gy gz := by
    rw [tripleGapDet_eq_tripleDetForm, tripleGapDet_eq_tripleDetForm,
      tripleDetForm, tripleDetForm, dotProduct_comm gy gx, dotProduct_comm gz gx]
    ring
  rw [hd1] at hxz
  rw [hd2] at hyz
  constructor
  · linarith [hxy, hxz]
  · linarith [hxy, hyz]

/-- **THE INSIDE PAIR MINORS VANISH.**  Weak domination makes the corner's gap
positive semidefinite, so its third minor is nonnegative and its pair minors are
nonnegative too.  The corner law makes them negatives of each other, so all four
scalars are zero. -/
theorem cornerForm_insidePair_pairGapMinor_eq_zero
    (h : CornerForm gx gy gz u lam) (hu : leverageOf u = 1)
    (hdet : 0 ≤ tripleGapDet gx gy gz) (hmin : 0 ≤ pairGapMinor gx gy) :
    pairGapMinor gx gy = 0 ∧ tripleGapDet gx gy gz = 0 := by
  have hxy := cornerForm_corner_gapDet_eq_neg_pairGapMinor h hu
  constructor
  · linarith [hxy, hdet, hmin]
  · linarith [hxy, hdet, hmin]

/-- **THE TWO-INSIDE DETERMINANT AT A GENUINE CORNER.**  With the inside minor
gone the law is a bare squared bracket against the axis. -/
theorem cornerForm_twoInside_gapDet_pure (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (hq : pairGapMinor gx gy = 0) (gd : Fin 3 → ℝ) :
    tripleGapDet gx gy gd = - lam * tripleBracket gz gd u ^ 2 := by
  rw [cornerForm_twoInside_gapDet h hu gd, hq]; ring

/-- **THE TWO-INSIDE DETERMINANT IS NONPOSITIVE, WITH ITS EQUALITY LOCUS.**  A
two-inside triple sits on the refusal boundary exactly when the ERASED inside
atom, the gap axis and the outside atom are coplanar. -/
theorem cornerForm_twoInside_gapDet_nonpos (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (hq : pairGapMinor gx gy = 0) (hlam : 0 ≤ lam)
    (gd : Fin 3 → ℝ) :
    tripleGapDet gx gy gd ≤ 0 := by
  rw [cornerForm_twoInside_gapDet_pure h hu hq gd]
  nlinarith [sq_nonneg (tripleBracket gz gd u), hlam]

theorem cornerForm_twoInside_gapDet_eq_zero_iff (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (hq : pairGapMinor gx gy = 0) (hlam : 0 < lam)
    (gd : Fin 3 → ℝ) :
    tripleGapDet gx gy gd = 0 ↔ tripleBracket gz gd u = 0 := by
  rw [cornerForm_twoInside_gapDet_pure h hu hq gd]
  constructor
  · intro hz
    have : tripleBracket gz gd u ^ 2 = 0 := by
      rcases mul_eq_zero.mp (by linarith [hz] :
        (- lam) * tripleBracket gz gd u ^ 2 = 0) with h1 | h2
      · exact absurd h1 (by intro hc; nlinarith [hlam, hc])
      · exact h2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro hz; rw [hz]; ring

/-! ## 5. The inside triangle is deleted before any tie hypothesis -/

/-- **AN INSIDE PAIR OF A CORNER IS NOT ADMISSIBLE.**  Admissibility is STRICT
positivity of the pair minor, and at a corner that minor is exactly zero.  So the
three inside edges leave the admissibility graph for free. -/
theorem cornerForm_insidePair_not_admissible (hq : pairGapMinor gx gy = 0) :
    ¬ AdmissiblePair gx gy := by
  rw [AdmissiblePair, hq]
  exact lt_irrefl 0

/-- **NO TRIPLE CARRYING TWO INSIDE ATOMS IS LIVE.**  Sylvester locality: the
inadmissible edge sits inside the triple, so the triple loses its second minor
whatever the third one does. -/
theorem cornerForm_twoInside_not_live {m : ℕ} (D : WeightedDesign m 3)
    {a b c : Fin m} (hax : D.atom a = gx) (hby : D.atom b = gy)
    (hq : pairGapMinor gx gy = 0) :
    ¬ LiveTriple D a b c := by
  rintro ⟨-, -, -, hadm, -, -⟩
  rw [hax, hby] at hadm
  exact cornerForm_insidePair_not_admissible hq hadm

/-- **THE TEN FREE REFUSALS, THROUGH THE GRAPH.**  Every triple of the design
that carries two of the corner's inside atoms fails to dominate strictly — the
corner itself and the nine two-inside triples, with no tie hypothesis anywhere.
This is `Gtz.corner_posDef_triple_inter_le_one` reached by Sylvester locality
instead of by the determinant, and it explains the count: `K₆` less the inside
triangle leaves exactly the ten triples a corner tie still has to kill. -/
theorem cornerForm_ten_refusals_free {m : ℕ} (D : WeightedDesign m 3)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hax : D.atom a = gx) (hby : D.atom b = gy)
    (hq : pairGapMinor gx gy = 0) :
    ¬ (subsetSum D ({a, b, c} : Finset (Fin m)) - 1).PosDef := by
  intro hpd
  obtain ⟨hlive, -⟩ :=
    (posDef_subsetSum_iff_live_and_gapDet D a b c hab hac hbc).mp hpd
  exact cornerForm_twoInside_not_live D hax hby hq hlive

/-! ## 6. The admissibility test at an outside atom -/

/-- **A SIGN DECIDES WHETHER AN OUTSIDE ATOM HAS AN INSIDE PARTNER.**  If the
mixed pair minor total is nonpositive then some mixed pair is inadmissible, and
every informative triple through that pair is dead.  The total is closed by
`Gtz.cornerForm_mixed_pairMinor_total`, so the test costs one evaluation of
`(λ−1)ℓ_d − λ⟨u,g_d⟩² − λ`. -/
theorem cornerForm_exists_inadmissible_mixed (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ)
    (hsign : (lam - 1) * leverageOf gd - lam * (u ⬝ᵥ gd) ^ 2 - lam ≤ 0) :
    ¬ AdmissiblePair gx gd ∨ ¬ AdmissiblePair gy gd
      ∨ ¬ AdmissiblePair gz gd := by
  by_contra hcon
  simp only [not_or, not_not, AdmissiblePair] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have htot := cornerForm_mixed_pairMinor_total h hu gd
  linarith [h1, h2, h3, htot, hsign]

/-- The complementary reading: a positive total supplies an admissible mixed
pair, which is the edge an informative triple through `d` needs. -/
theorem cornerForm_exists_admissible_mixed (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (gd : Fin 3 → ℝ)
    (hsign : 0 < (lam - 1) * leverageOf gd - lam * (u ⬝ᵥ gd) ^ 2 - lam) :
    AdmissiblePair gx gd ∨ AdmissiblePair gy gd ∨ AdmissiblePair gz gd := by
  by_contra hcon
  simp only [not_or, AdmissiblePair, not_lt] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have htot := cornerForm_mixed_pairMinor_total h hu gd
  linarith [h1, h2, h3, htot, hsign]

end Gtz

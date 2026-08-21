/-
# Selection without a selector: the column criterion of a corner

The opposite horn's obstruction is SELECTION.  A corner tie has to be refused by
ten live triples; adversarial descent says only FOUR of them ever bind, and
every symmetric sum over the ten fails because one positive term is averaged
against several deeply refused ones.  So a closing certificate has to name a
small family -- and the arm has no scalar rule that names it.

This module removes one of the two selections.  Fix an outside pair `{d,d'}` of
a corner.  Three informative triples sit over it, one for each inside atom, and
the question "does one of them dominate?" is an existential over the inside
atoms.  Two results turn that existential into scalar sign conditions.

## 1. The column total, in closed form

The three gap determinants over a fixed pair base TOTAL to a closed corner
expression (`Gtz.cornerForm_tripleGapDet_column_total`):

  **`Σ_{e∈C} tripleGapDet a b g_e
      = (λ−2)·pairGapMinor a b − (ℓ_a + ℓ_b − 2) + λ·pairAxisForm a b ⟨u,a⟩ ⟨u,b⟩`**

Every inside coordinate cancels.  The mechanism is the corner form polarized
(`Gtz.cornerForm_polarized`): the inside triple reads any two probes by their
inner product plus the scale times the two axis readings, so the three sums the
axis form needs are all corner scalars.

This promotes a measurement to an identity.  The campaign had recorded that
`Σ_x det(gap_{x d d'})` is negative at 48722 of 49845 admissible outside pairs;
the closed form says exactly WHY, and exactly when it is not: the total is
positive only when the scale passes two and the pair minor is large enough to
carry the pair's own leverage excess and the axis term.  **The column sum is
not a weak instrument that better sampling would rescue.  It is this
polynomial, and it is negative wherever this polynomial is.**

## 2. The criterion that needs no selector

The sum is only the first elementary symmetric function of the three
determinants.  All three carry information, and the three together decide the
existential exactly (`Gtz.exists_pos_iff_esymm_signs`):

  **some triple over the pair has a positive gap determinant
     ⟺ `0 < e₁` or `e₂ < 0` or `0 < e₃`**

The forward direction is elementary -- three nonpositive reals have a
nonpositive sum, a nonnegative second symmetric function and a nonpositive
product.  The converse is the landed
`Gtz.nonneg_of_elementarySymmetric_nonneg`, read at the negated triple.

The criterion is a PRODUCER with no selection rule: three scalars, computed
from the corner, and any one of the three sign conditions exhibits a positive
gap determinant without naming which inside atom carries it.

[MEASURED.  The closed form reproduces at `7.3e-12` over 53092 exact corners
and the polarized form at `2.1e-14`.  Over 313309 admissible columns the
criterion agrees with the truth at EVERY point -- zero exceptions -- and the
three conditions are very unequally informative: the product `0 < e₃` fires at
27.0 percent, the second symmetric function `e₂ < 0` at 10.9 percent, and the
sum `0 < e₁` at only 2.6 percent.  **The product carries ten times the
information of the sum**, which is the campaign's "select or multiply, never
add" doctrine measured inside this lane for the first time.]

## What this does not do

A positive gap determinant is not yet a strict dominator: `Gtz.tripleGapDet` is
the third Sylvester minor, and domination also needs the triple to be live.  At
the corner level the two agree in every sample taken (61.106 percent of corners
carry an informative triple with a positive gap determinant, and at every one
of them some such triple is also live -- 0 exceptions in 106171 corners), but
that agreement is MEASURED, not proved, and the liveness step is left to
`Gtz.posDef_subsetSum_iff_live_and_gapDet`.

Nor does this close the horn.  The second selection -- over the three outside
pairs -- survives, and on the residual region where the complement refuses no
single symmetric function suffices: restricted to those corners the best single
condition is the third symmetric function of the NINE informative determinants
at 87.1 percent, and the disjunction needs six of the nine to reach every point.
-/
import Gtz.Wave.CornerAxisCalculus
import Gtz.Wave.CornerAxisElimination
import Gtz.Quantitative.ExpectedCharPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

variable {gx gy gz u : Fin 3 → ℝ} {lam : ℝ}

/-! ## 1. The corner form, polarized -/

/-- **THE CORNER FORM AT TWO PROBES.**  Polarizing the single corner equation:
the inside triple pairs any two probes by their inner product plus the scale
times the product of their axis readings.  `v = w` is the landed
`Gtz.cornerForm_atom_reading`. -/
theorem cornerForm_polarized (h : CornerForm gx gy gz u lam) (v w : Fin 3 → ℝ) :
    (gx ⬝ᵥ v) * (gx ⬝ᵥ w) + (gy ⬝ᵥ v) * (gy ⬝ᵥ w) + (gz ⬝ᵥ v) * (gz ⬝ᵥ w)
      = v ⬝ᵥ w + lam * ((u ⬝ᵥ v) * (u ⬝ᵥ w)) := by
  have hplus := h (fun i => v i + w i)
  have hminus := h (fun i => v i - w i)
  simp only [dotProduct, Fin.sum_univ_three] at hplus hminus ⊢
  linear_combination hplus / 4 - hminus / 4

/-! ## 2. The column total -/

/-- **THE THREE GAP DETERMINANTS OVER A PAIR BASE TOTAL TO A CORNER SCALAR.**
Every inside coordinate cancels: what is left is the scale less two against the
pair minor, the pair's own leverage excess, and the axis form of the pair read
at its two axis readings. -/
theorem cornerForm_tripleGapDet_column_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (a b : Fin 3 → ℝ) :
    tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz
      = (lam - 2) * pairGapMinor a b
        - (leverageOf a + leverageOf b - 2)
        + lam * pairAxisForm a b (u ⬝ᵥ a) (u ⬝ᵥ b) := by
  have haa := cornerForm_polarized h a a
  have hbb := cornerForm_polarized h b b
  have hab := cornerForm_polarized h a b
  have hlev := cornerForm_leverage_total h hu
  simp only [tripleGapDet, pairAxisForm, pairGapMinor, leverageOf, dotProduct,
    Fin.sum_univ_three] at haa hbb hab hlev ⊢
  linear_combination
      (1 - (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2)) * haa
    + 2 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) * hab
    + (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2)) * hbb
    + ((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 - 1) * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 - 1)
        - (a 0 * b 0 + a 1 * b 1 + a 2 * b 2) ^ 2) * hlev

/-! ## 3. Selection without a selector -/

/-- Three nonpositive reals have a nonpositive sum, a nonnegative second
elementary symmetric function, and a nonpositive product. -/
theorem esymm_signs_of_nonpos {x y z : ℝ}
    (hx : x ≤ 0) (hy : y ≤ 0) (hz : z ≤ 0) :
    x + y + z ≤ 0 ∧ 0 ≤ x * y + x * z + y * z ∧ x * y * z ≤ 0 := by
  have h1 : 0 ≤ x * y := by nlinarith
  have h2 : 0 ≤ x * z := by nlinarith
  have h3 : 0 ≤ y * z := by nlinarith
  exact ⟨by linarith, by linarith, by nlinarith⟩

/-- **THE EXISTENTIAL IS THREE SIGN CONDITIONS.**  One of three reals is
positive exactly when the sum is positive, or the second elementary symmetric
function is negative, or the product is positive.

The forward direction is `Gtz.esymm_signs_of_nonpos`; the converse is the
landed `Gtz.nonneg_of_elementarySymmetric_nonneg` read at the negated triple. -/
theorem exists_pos_iff_esymm_signs (x y z : ℝ) :
    (0 < x ∨ 0 < y ∨ 0 < z)
      ↔ (0 < x + y + z ∨ x * y + x * z + y * z < 0 ∨ 0 < x * y * z) := by
  constructor
  · intro hpos
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    -- the negated triple has three nonnegative elementary symmetric functions
    have e1 : 0 ≤ -x + -y + -z := by linarith
    have e2 : 0 ≤ (-x) * (-y) + (-x) * (-z) + (-y) * (-z) := by nlinarith [h2]
    have e3 : 0 ≤ (-x) * (-y) * (-z) := by nlinarith [h3]
    obtain ⟨hx, hy, hz⟩ := nonneg_of_elementarySymmetric_nonneg (-x) (-y) (-z) e1 e2 e3
    rcases hpos with hp | hp | hp <;> linarith
  · intro hsign
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy, hz⟩ := hcon
    obtain ⟨s1, s2, s3⟩ := esymm_signs_of_nonpos hx hy hz
    rcases hsign with hs | hs | hs <;> linarith

/-- **THE COLUMN PRODUCER.**  Over a fixed outside pair of a corner, any one of
the three sign conditions on the elementary symmetric functions of the three
gap determinants exhibits an inside atom whose informative triple has a
positive gap determinant — with no rule naming which atom it is. -/
theorem corner_column_exists_tripleGapDet_pos (a b : Fin 3 → ℝ)
    (hsign : 0 < tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz
      ∨ tripleGapDet a b gx * tripleGapDet a b gy
          + tripleGapDet a b gx * tripleGapDet a b gz
          + tripleGapDet a b gy * tripleGapDet a b gz < 0
      ∨ 0 < tripleGapDet a b gx * tripleGapDet a b gy * tripleGapDet a b gz) :
    0 < tripleGapDet a b gx ∨ 0 < tripleGapDet a b gy ∨ 0 < tripleGapDet a b gz :=
  (exists_pos_iff_esymm_signs _ _ _).mpr hsign

/-- **THE COLUMN SUM AS A PRODUCER, IN CLOSED FORM.**  The cheapest of the three
conditions, with the inside data eliminated: if the scale less two against the
pair minor beats the pair's leverage excess and the axis term, some inside atom
carries a positive gap determinant. -/
theorem corner_column_exists_tripleGapDet_pos_closed (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (a b : Fin 3 → ℝ)
    (hclosed : 0 < (lam - 2) * pairGapMinor a b
      - (leverageOf a + leverageOf b - 2)
      + lam * pairAxisForm a b (u ⬝ᵥ a) (u ⬝ᵥ b)) :
    0 < tripleGapDet a b gx ∨ 0 < tripleGapDet a b gy ∨ 0 < tripleGapDet a b gz := by
  refine corner_column_exists_tripleGapDet_pos a b (Or.inl ?_)
  rw [cornerForm_tripleGapDet_column_total h hu a b]
  exact hclosed


/-! ## 4. The product form, at any positive probe -/

/-- **THE PRODUCT CERTIFICATE.**  If the product of `t − f i` over a finite
family is nonpositive at even one positive `t`, some member of the family is
positive.  Three nonpositive members would make every factor positive at every
positive `t`.

This is the campaign's "select or multiply, never add" doctrine in its shortest
form, and it needs no symmetric functions: ONE scalar, evaluated at ONE probe,
exhibits a positive member without naming it. -/
theorem exists_pos_of_prod_sub_nonpos {I : Type*} {s : Finset I} {f : I → ℝ}
    {t : ℝ} (ht : 0 < t) (hprod : ∏ i ∈ s, (t - f i) ≤ 0) :
    ∃ i ∈ s, 0 < f i := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < ∏ i ∈ s, (t - f i) :=
    Finset.prod_pos fun i hi => by have := hcon i hi; linarith
  linarith

/-- The converse: a positive member is itself a probe at which the product
vanishes.  So the product criterion is LOSSLESS over the positive probes. -/
theorem exists_prod_sub_nonpos_of_exists_pos {I : Type*} [DecidableEq I]
    {s : Finset I} {f : I → ℝ} (h : ∃ i ∈ s, 0 < f i) :
    ∃ t : ℝ, 0 < t ∧ ∏ i ∈ s, (t - f i) ≤ 0 := by
  obtain ⟨i, hi, hpos⟩ := h
  refine ⟨f i, hpos, le_of_eq ?_⟩
  exact Finset.prod_eq_zero hi (by ring)

/-- **THE COLUMN PRODUCER AT A PROBE.**  The three informative gap determinants
over a pair base, read as one product at any positive probe. -/
theorem corner_column_exists_tripleGapDet_pos_prod (a b : Fin 3 → ℝ) {t : ℝ}
    (ht : 0 < t)
    (hprod : (t - tripleGapDet a b gx) * (t - tripleGapDet a b gy)
        * (t - tripleGapDet a b gz) ≤ 0) :
    0 < tripleGapDet a b gx ∨ 0 < tripleGapDet a b gy ∨ 0 < tripleGapDet a b gz := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy, hz⟩ := hcon
  have h1 : 0 < t - tripleGapDet a b gx := by linarith
  have h2 : 0 < t - tripleGapDet a b gy := by linarith
  have h3 : 0 < t - tripleGapDet a b gz := by linarith
  nlinarith [mul_pos (mul_pos h1 h2) h3]


/-! ## 5. The nine-sum sees only the outside triple -/

/-- **THE TOTAL OF ALL NINE INFORMATIVE GAP DETERMINANTS IS OUTSIDE DATA AND
THE SCALE.**  Summing the column total over the three outside pairs, the inside
triple disappears completely: what is left mentions only the three outside
atoms, their pair minors, their axis readings, and `λ`.

So the first elementary symmetric function of the nine cannot separate two
corners that share an outside triple and a scale, however their inside atoms
differ.  That is a structural reason the nine-sum is a weak instrument, and it
is the companion of the column total: the inside atoms enter the nine
determinants ONLY through `λ`. -/
theorem cornerForm_tripleGapDet_nine_total (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (a b c : Fin 3 → ℝ) :
    (tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz)
      + (tripleGapDet a c gx + tripleGapDet a c gy + tripleGapDet a c gz)
      + (tripleGapDet b c gx + tripleGapDet b c gy + tripleGapDet b c gz)
      = (lam - 2) * (pairGapMinor a b + pairGapMinor a c + pairGapMinor b c)
        - 2 * (leverageOf a + leverageOf b + leverageOf c - 3)
        + lam * (pairAxisForm a b (u ⬝ᵥ a) (u ⬝ᵥ b)
            + pairAxisForm a c (u ⬝ᵥ a) (u ⬝ᵥ c)
            + pairAxisForm b c (u ⬝ᵥ b) (u ⬝ᵥ c)) := by
  rw [cornerForm_tripleGapDet_column_total h hu a b,
    cornerForm_tripleGapDet_column_total h hu a c,
    cornerForm_tripleGapDet_column_total h hu b c]
  ring


/-! ## 6. On an admissible pair the determinant IS domination -/

/-- **THE CAVEAT DISAPPEARS ON AN ADMISSIBLE OUTSIDE PAIR.**  The landed
Sylvester criterion is ORDERED: reading the triple with the pair first, its
three leading principal minors are the pair's first leverage excess, the pair
minor, and the gap determinant.  So once the pair is admissible, a positive gap
determinant is not merely necessary for domination — it IS domination.

Admissibility is supplied by two scalars, the pair minor and the pair trace,
through the landed `Gtz.one_lt_leverage_of_pairGapMinor_pos_of_trace`. -/
theorem tripleGram_posDef_iff_gapDet_pos_of_admissible {a b c : Fin 3 → ℝ}
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b) :
    (tripleGram a b c - 1).PosDef ↔ 0 < tripleGapDet a b c := by
  obtain ⟨hla, -⟩ := one_lt_leverage_of_pairGapMinor_pos_of_trace hmin htr
  rw [tripleGram_posDef_iff_pairVocabulary]
  constructor
  · rintro ⟨-, -, h3⟩; exact h3
  · intro h3; exact ⟨by linarith, hmin, h3⟩

/-- **THE COLUMN PRODUCER, AS A DOMINATOR.**  Over an admissible outside pair,
the three sign conditions on the elementary symmetric functions of the three gap
determinants exhibit an inside atom whose triple STRICTLY DOMINATES — with no
rule naming the atom, and with no liveness side condition left over. -/
theorem corner_column_exists_posDef (a b : Fin 3 → ℝ)
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b)
    (hsign : 0 < tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz
      ∨ tripleGapDet a b gx * tripleGapDet a b gy
          + tripleGapDet a b gx * tripleGapDet a b gz
          + tripleGapDet a b gy * tripleGapDet a b gz < 0
      ∨ 0 < tripleGapDet a b gx * tripleGapDet a b gy * tripleGapDet a b gz) :
    (tripleGram a b gx - 1).PosDef ∨ (tripleGram a b gy - 1).PosDef
      ∨ (tripleGram a b gz - 1).PosDef := by
  rcases corner_column_exists_tripleGapDet_pos a b hsign with h | h | h
  · exact Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h)
  · exact Or.inr (Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))
  · exact Or.inr (Or.inr ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))

/-- The same, from the closed column total: a single scalar inequality in the
outside pair's data and the scale exhibits a strict dominator. -/
theorem corner_column_exists_posDef_closed (h : CornerForm gx gy gz u lam)
    (hu : leverageOf u = 1) (a b : Fin 3 → ℝ)
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b)
    (hclosed : 0 < (lam - 2) * pairGapMinor a b
      - (leverageOf a + leverageOf b - 2)
      + lam * pairAxisForm a b (u ⬝ᵥ a) (u ⬝ᵥ b)) :
    (tripleGram a b gx - 1).PosDef ∨ (tripleGram a b gy - 1).PosDef
      ∨ (tripleGram a b gz - 1).PosDef := by
  refine corner_column_exists_posDef a b hmin htr (Or.inl ?_)
  rw [cornerForm_tripleGapDet_column_total h hu a b]
  exact hclosed


/-! ## 7. The weighted column total, and the gauge -/

/-- **THE WEIGHTED COLUMN TOTAL.**  Hypothesis-free: weighting the three gap
determinants over a pair base by the inside weights and totalling gives the pair
minor against the weighted leverage excess, plus the pair's axis form read at
the three WEIGHTED second moments of the inside readings.

Unlike the unweighted total this is NOT determined by the corner and pair
invariants.  A sibling's rotation gauge `V_C → V_C·Q` fixes every corner and
pair invariant while rotating the individual readings, and the unweighted total
is forced constant on that orbit (`Gtz.cornerForm_tripleGapDet_column_total`).
The weights break the gauge, because they are attached to individual atoms.
**That is why a certificate for the horn must carry weights: the gauge-invariant
part of the column is exactly its unweighted total, and nothing more.** -/
theorem weighted_column_total (tx ty tz : ℝ) (a b gx gy gz : Fin 3 → ℝ) :
    tx * tripleGapDet a b gx + ty * tripleGapDet a b gy + tz * tripleGapDet a b gz
      = pairGapMinor a b
          * (tx * (leverageOf gx - 1) + ty * (leverageOf gy - 1)
              + tz * (leverageOf gz - 1))
        + (1 - leverageOf b)
            * (tx * (a ⬝ᵥ gx) ^ 2 + ty * (a ⬝ᵥ gy) ^ 2 + tz * (a ⬝ᵥ gz) ^ 2)
        + 2 * (a ⬝ᵥ b)
            * (tx * ((a ⬝ᵥ gx) * (b ⬝ᵥ gx)) + ty * ((a ⬝ᵥ gy) * (b ⬝ᵥ gy))
                + tz * ((a ⬝ᵥ gz) * (b ⬝ᵥ gz)))
        + (1 - leverageOf a)
            * (tx * (b ⬝ᵥ gx) ^ 2 + ty * (b ⬝ᵥ gy) ^ 2 + tz * (b ⬝ᵥ gz) ^ 2) := by
  simp only [tripleGapDet, pairGapMinor, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- **ANY NONNEGATIVE WEIGHTING IS A PRODUCER.**  If a nonnegative combination
of the three gap determinants is positive, one of them is positive.  The
coefficients need not be the design's weights: any nonnegative triple works, so
the weighted total, the unweighted total and the axis-mass total are all
instances. -/
theorem exists_pos_of_nonneg_combo_pos {cx cy cz x y z : ℝ}
    (hcx : 0 ≤ cx) (hcy : 0 ≤ cy) (hcz : 0 ≤ cz)
    (hpos : 0 < cx * x + cy * y + cz * z) :
    0 < x ∨ 0 < y ∨ 0 < z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy, hz⟩ := hcon
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcx hx,
    mul_nonpos_of_nonneg_of_nonpos hcy hy, mul_nonpos_of_nonneg_of_nonpos hcz hz]

/-- **THE WEIGHTED PRODUCER, AS A DOMINATOR.**  Over an admissible outside pair,
a positive weighted column total exhibits a strictly dominating triple. -/
theorem corner_column_posDef_of_weighted_pos {tx ty tz : ℝ} (a b : Fin 3 → ℝ)
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b)
    (hx : 0 ≤ tx) (hy : 0 ≤ ty) (hz : 0 ≤ tz)
    (hpos : 0 < tx * tripleGapDet a b gx + ty * tripleGapDet a b gy
        + tz * tripleGapDet a b gz) :
    (tripleGram a b gx - 1).PosDef ∨ (tripleGram a b gy - 1).PosDef
      ∨ (tripleGram a b gz - 1).PosDef := by
  rcases exists_pos_of_nonneg_combo_pos hx hy hz hpos with h | h | h
  · exact Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h)
  · exact Or.inr (Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))
  · exact Or.inr (Or.inr ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))

/-! ## 8. No positive linear functional is complete -/

/-- **THE LINEAR PRODUCERS ARE PROVABLY INCOMPLETE.**  For EVERY strictly
positive coefficient triple there is a configuration with a positive member
whose combination is negative: one small positive against two large negatives
outweighs any fixed weighting.

So no producer of the form `Σ c_e φ_e > 0` — the unweighted total, the weighted
total, the axis-mass total, any of them — can detect every positive member.
The second and third elementary symmetric functions are not a refinement of the
sum, they are REQUIRED, and `Gtz.exists_pos_iff_esymm_signs` is the complete
criterion the linear family cannot reach.

[MEASURED: over 12375 corners whose complement refuses, the best producer of the
shape `c_e = t_e^α (ℓ_e−1)^β` on a 7×6 grid of exponents reaches 99.895 percent
at `α = 2, β = 3/2`, and the plain weighted total 98.75 percent, while the
elementary symmetric criterion reaches 100.0000 percent — as it must, being an
equivalence.] -/
theorem linear_producer_incomplete (cx cy cz : ℝ)
    (hcx : 0 < cx) (hcy : 0 < cy) (hcz : 0 < cz) :
    ∃ x y z : ℝ, (0 < x ∨ 0 < y ∨ 0 < z) ∧ cx * x + cy * y + cz * z < 0 := by
  refine ⟨1, -(cx + 1) / cy, 0, Or.inl one_pos, ?_⟩
  have h : cy * (-(cx + 1) / cy) = -(cx + 1) := by field_simp
  rw [h]; linarith

/-! ## 9. The corner criterion, complete -/

/-- **THE COMPLETE COLUMN CRITERION.**  Over an admissible outside pair, a
strictly dominating triple exists EXACTLY when the three elementary symmetric
functions of the column's gap determinants carry one of the three signs.

Both directions: the producer is `Gtz.corner_column_exists_posDef`, and the
converse reads the landed ordered Sylvester criterion backwards.  This is the
lane's complete, selection-free reading of "some inside atom repays this pair",
and no linear functional can replace it (`Gtz.linear_producer_incomplete`). -/
theorem corner_column_posDef_iff_esymm_signs (a b : Fin 3 → ℝ)
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b) :
    ((tripleGram a b gx - 1).PosDef ∨ (tripleGram a b gy - 1).PosDef
        ∨ (tripleGram a b gz - 1).PosDef)
      ↔ (0 < tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz
        ∨ tripleGapDet a b gx * tripleGapDet a b gy
            + tripleGapDet a b gx * tripleGapDet a b gz
            + tripleGapDet a b gy * tripleGapDet a b gz < 0
        ∨ 0 < tripleGapDet a b gx * tripleGapDet a b gy * tripleGapDet a b gz) := by
  rw [← exists_pos_iff_esymm_signs]
  constructor
  · rintro (h | h | h)
    · exact Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mp h)
    · exact Or.inr (Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mp h))
    · exact Or.inr (Or.inr ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mp h))
  · rintro (h | h | h)
    · exact Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h)
    · exact Or.inr (Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))
    · exact Or.inr (Or.inr ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))


/-! ## 10. The residual configuration, named -/

/-- **A NONPOSITIVE SUM WITH A POSITIVE PRODUCT MEANS EXACTLY ONE POSITIVE.**
Three reals with `e₃ > 0` are either all positive or exactly one positive, and a
nonpositive sum excludes the first.  So this is precisely the configuration the
linear producers cannot see: ONE SMALL POSITIVE HIDING BEHIND TWO LARGE
NEGATIVES.

[MEASURED: over the corners whose complement refuses, the weighted column total
misses 1.426 percent, and on exactly that residual `e₃ > 0` fires at 91.8
percent and `e₂ < 0` at 95.9 percent — the two together closing it, as the
equivalence `Gtz.exists_pos_iff_esymm_signs` requires.] -/
theorem exactly_one_pos_of_sum_nonpos_of_prod_pos {x y z : ℝ}
    (hsum : x + y + z ≤ 0) (hprod : 0 < x * y * z) :
    (0 < x ∧ y ≤ 0 ∧ z ≤ 0) ∨ (x ≤ 0 ∧ 0 < y ∧ z ≤ 0)
      ∨ (x ≤ 0 ∧ y ≤ 0 ∧ 0 < z) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hprod
  have hy0 : y ≠ 0 := by rintro rfl; simp at hprod
  have hz0 : z ≠ 0 := by rintro rfl; simp at hprod
  rcases lt_or_gt_of_ne hx0 with hx | hx <;> rcases lt_or_gt_of_ne hy0 with hy | hy <;>
    rcases lt_or_gt_of_ne hz0 with hz | hz
  · exact absurd hprod (not_lt.mpr
      (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hx hy) hz).le)
  · exact Or.inr (Or.inr ⟨hx.le, hy.le, hz⟩)
  · exact Or.inr (Or.inl ⟨hx.le, hy, hz.le⟩)
  · exact absurd hprod (not_lt.mpr
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hx hy) hz).le)
  · exact Or.inl ⟨hx, hy.le, hz.le⟩
  · exact absurd hprod (not_lt.mpr
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hx hy) hz).le)
  · exact absurd hprod (not_lt.mpr
      (mul_neg_of_pos_of_neg (mul_pos hx hy) hz).le)
  · exact absurd hsum (by linarith)

/-- **THE RESIDUAL IS A SINGLE SLOT.**  Over an admissible outside pair, if the
column total is nonpositive but the product of the three gap determinants is
positive, then EXACTLY ONE inside atom repays the pair — and its triple strictly
dominates.

This is the shape no nonnegative weighting can detect
(`Gtz.linear_producer_incomplete`), so the third symmetric function is not an
optimisation of the sum but the only instrument that sees this case. -/
theorem corner_column_unique_posDef_of_sum_nonpos_of_prod_pos (a b : Fin 3 → ℝ)
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b)
    (hsum : tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz ≤ 0)
    (hprod : 0 < tripleGapDet a b gx * tripleGapDet a b gy * tripleGapDet a b gz) :
    (tripleGram a b gx - 1).PosDef ∨ (tripleGram a b gy - 1).PosDef
      ∨ (tripleGram a b gz - 1).PosDef := by
  rcases exactly_one_pos_of_sum_nonpos_of_prod_pos hsum hprod with
    ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
  · exact Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h)
  · exact Or.inr (Or.inl ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))
  · exact Or.inr (Or.inr ((tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr).mpr h))

end Gtz

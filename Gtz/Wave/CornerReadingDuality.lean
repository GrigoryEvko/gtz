/-
# The dual reading law: a triple with a bracket determines every pairing it sees

The corank-two arm's remaining existence fact was split by the campaign into two
conditions on a corner `S_C = 1 + lam * u uᵀ`:

* **(A)** some outside pair is admissible, `0 < pairGapMinor`;
* **(B)** an admissible outside pair is repaid, `0 < tripleGapDet` for some inside
  atom.

This module supplies the algebra that governs both, and it settles what kind of
argument can prove them.

## The law

Three atoms with a nonzero bracket span the rank-three space, so every other
vector is a combination of them, and its pairings are FORCED by its readings
against them.  In inverse-free form
(`Gtz.sq_tripleBracket_mul_dotProduct_eq_dualReadingForm`):

  **`[g₁,g₂,g₃]² * (a ⬝ᵥ b) = dualReadingForm K (a's readings) (b's readings)`**

where `dualReadingForm` is the adjugate of the triple's Gram read at the two
reading vectors.  One `ring`, no hypothesis, and it holds at degenerate triples
too, where both sides vanish.

The specialisations are the two scalars an outside pair contributes:
`Gtz.sq_tripleBracket_mul_leverage_eq_dualReadingForm` for its leverage, and the
law itself for its pairing.  So the pair minor of an outside pair, and with it
its admissibility, is a function of the six readings alone.

## The corner form

At a corner the inside Gram is `1 + c cᵀ` with `c_e² = l_e - 1` and
`c_e c_f = ⟨g_e, g_f⟩` -- the landed axis law.  There the bracket squares to
`1 + |c|²` and the adjugate is `(1 + |c|²) * 1 - c cᵀ`, so the law collapses to
(`Gtz.corner_dotProduct_eq_readings`):

  **`(1+|c|²) * (a ⬝ᵥ b) = (1+|c|²) * ⟨x, y⟩ - (c ⬝ x)(c ⬝ y)`** ,

with `x`, `y` the readings.  Every scalar of an outside pair is now an explicit
polynomial in `c` and the six readings.

## WHAT THIS RULES OUT, AND IT IS THE POINT

Because the pair is determined by its readings, the pair `(c, W)` of the axis
data and the reading matrix is a FREE parameter: every such pair is realised by
five genuine vectors in rank three.  So a proof of (B) that uses only the corner
and one outside pair is proving a statement about `(c, W)` alone -- and that
statement is FALSE.

[MEASURED, scratchpad/NOTES-f73-etwo-selector.txt F73-1: over 166735 samples of
`(c, W)` with the pair admissible, the per-pair form of (B) fails at 43.6117%,
worst scaled margin `-9.953581e-01`.  Verified against this law: the readings
reproduce `W` to `1.332e-14` and the repayment matrix diagonal reproduces
`Gtz.tripleGapDet` to `1.478e-12`.]

So Parseval with six positive weights is not decoration in (B): it is the only
remaining input.  This is the algebraic reason F49-13's "the corner and its pair
determine `e1` and nothing else" was a diagnosis of the wrong object -- the
corner and its pair determine EVERYTHING about the pair, and still do not decide
the repayment.

## The statement the arm actually needs

The per-pair reading of (B) is FALSE at genuine designs, not merely at free
`(c, W)`: NOTES-f73 F73-0 records a verified six-atom design whose corner has an
admissible outside pair repaid by no inside atom, while its OTHER admissible
pair is repaid.  Conditions (A) and (B) must therefore be merged into the single
existential this module names, `Gtz.CornerRepaysSomePair`, which is what the
contradiction consumes and is strictly weaker than the conjunction.
`Gtz.not_isTie_of_cornerRepaysSomePair` runs it into the landed Sylvester
producer.
-/
import Gtz.Wave.CornerPairAdjugate
import Gtz.Reduction.PolarGapDeterminant
import Gtz.Certificates.ResidueDissolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The dual reading form -/

/-- The adjugate of a triple's Gram matrix, read at two reading vectors.  The
six scalars are the triple's three leverages and three pairings; the entries are
the cofactors, written out so that `ring` can see them. -/
noncomputable def dualReadingForm
    (levOne levTwo levThree pairOneTwo pairOneThree pairTwoThree
      xOne xTwo xThree yOne yTwo yThree : ℝ) : ℝ :=
  (levTwo * levThree - pairTwoThree ^ 2) * (xOne * yOne)
    + (pairOneThree * pairTwoThree - pairOneTwo * levThree) * (xOne * yTwo + xTwo * yOne)
    + (pairOneTwo * pairTwoThree - pairOneThree * levTwo) * (xOne * yThree + xThree * yOne)
    + (levOne * levThree - pairOneThree ^ 2) * (xTwo * yTwo)
    + (pairOneTwo * pairOneThree - pairTwoThree * levOne) * (xTwo * yThree + xThree * yTwo)
    + (levOne * levTwo - pairOneTwo ^ 2) * (xThree * yThree)

/-- The dual reading form is symmetric in its two reading vectors. -/
theorem dualReadingForm_comm
    (levOne levTwo levThree pairOneTwo pairOneThree pairTwoThree
      xOne xTwo xThree yOne yTwo yThree : ℝ) :
    dualReadingForm levOne levTwo levThree pairOneTwo pairOneThree pairTwoThree
        xOne xTwo xThree yOne yTwo yThree
      = dualReadingForm levOne levTwo levThree pairOneTwo pairOneThree pairTwoThree
        yOne yTwo yThree xOne xTwo xThree := by
  simp only [dualReadingForm]; ring

/-! ## 2. The law -/

/-- **THE DUAL READING LAW.**  A triple's squared bracket times any pairing of
two vectors equals the adjugate of the triple's Gram read at the two vectors'
readings.  No hypothesis: at a degenerate triple the bracket vanishes and so
does the adjugate form, because the adjugate of a singular Gram annihilates
every reading vector of the span.

Divided by the squared bracket this is the dual-basis expansion
`⟨a,b⟩ = rₐᵀ K⁻¹ r_b`; the inverse-free form is the one `ring` proves and the
one a certificate can use. -/
theorem sq_tripleBracket_mul_dotProduct_eq_dualReadingForm
    (gOne gTwo gThree a b : Fin 3 → ℝ) :
    tripleBracket gOne gTwo gThree ^ 2 * (a ⬝ᵥ b)
      = dualReadingForm (leverageOf gOne) (leverageOf gTwo) (leverageOf gThree)
          (gOne ⬝ᵥ gTwo) (gOne ⬝ᵥ gThree) (gTwo ⬝ᵥ gThree)
          (a ⬝ᵥ gOne) (a ⬝ᵥ gTwo) (a ⬝ᵥ gThree)
          (b ⬝ᵥ gOne) (b ⬝ᵥ gTwo) (b ⬝ᵥ gThree) := by
  simp only [dualReadingForm, tripleBracket, Matrix.det_fin_three, leverageOf,
    dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE LEVERAGE OF AN OUTSIDE ATOM IS ITS READINGS.**  The diagonal case of
the law. -/
theorem sq_tripleBracket_mul_leverage_eq_dualReadingForm
    (gOne gTwo gThree a : Fin 3 → ℝ) :
    tripleBracket gOne gTwo gThree ^ 2 * leverageOf a
      = dualReadingForm (leverageOf gOne) (leverageOf gTwo) (leverageOf gThree)
          (gOne ⬝ᵥ gTwo) (gOne ⬝ᵥ gThree) (gTwo ⬝ᵥ gThree)
          (a ⬝ᵥ gOne) (a ⬝ᵥ gTwo) (a ⬝ᵥ gThree)
          (a ⬝ᵥ gOne) (a ⬝ᵥ gTwo) (a ⬝ᵥ gThree) := by
  rw [← sq_tripleBracket_mul_dotProduct_eq_dualReadingForm, dotProduct_self_eq_leverageOf]

/-! ## 3. The corner form

At a corner the inside Gram is `1 + c cᵀ`.  Both invariants the law needs -- the
squared bracket and the adjugate -- collapse to polynomials in `c`. -/

/-- At a rank-one inside gap the squared bracket is one plus the axis square. -/
theorem sq_tripleBracket_of_rankOneGram {gOne gTwo gThree : Fin 3 → ℝ}
    {cOne cTwo cThree : ℝ}
    (hlevOne : leverageOf gOne = 1 + cOne ^ 2)
    (hlevTwo : leverageOf gTwo = 1 + cTwo ^ 2)
    (hlevThree : leverageOf gThree = 1 + cThree ^ 2)
    (hpairOneTwo : gOne ⬝ᵥ gTwo = cOne * cTwo)
    (hpairOneThree : gOne ⬝ᵥ gThree = cOne * cThree)
    (hpairTwoThree : gTwo ⬝ᵥ gThree = cTwo * cThree) :
    tripleBracket gOne gTwo gThree ^ 2 = 1 + cOne ^ 2 + cTwo ^ 2 + cThree ^ 2 := by
  rw [sq_tripleBracket_eq_gramDet, hlevOne, hlevTwo, hlevThree, hpairOneTwo,
    hpairOneThree, hpairTwoThree]
  ring

/-- **THE CORNER READING LAW.**  With the inside Gram at `1 + c cᵀ`, every
pairing of two vectors is their readings' inner product corrected by the axis
components.  Every scalar of an outside pair -- leverage, pairing, hence pair
minor and admissibility -- is now an explicit polynomial in `c` and the six
readings. -/
theorem corner_dotProduct_eq_readings {gOne gTwo gThree : Fin 3 → ℝ}
    {cOne cTwo cThree : ℝ} (a b : Fin 3 → ℝ)
    (hlevOne : leverageOf gOne = 1 + cOne ^ 2)
    (hlevTwo : leverageOf gTwo = 1 + cTwo ^ 2)
    (hlevThree : leverageOf gThree = 1 + cThree ^ 2)
    (hpairOneTwo : gOne ⬝ᵥ gTwo = cOne * cTwo)
    (hpairOneThree : gOne ⬝ᵥ gThree = cOne * cThree)
    (hpairTwoThree : gTwo ⬝ᵥ gThree = cTwo * cThree) :
    (1 + cOne ^ 2 + cTwo ^ 2 + cThree ^ 2) * (a ⬝ᵥ b)
      = (1 + cOne ^ 2 + cTwo ^ 2 + cThree ^ 2)
          * ((a ⬝ᵥ gOne) * (b ⬝ᵥ gOne) + (a ⬝ᵥ gTwo) * (b ⬝ᵥ gTwo)
            + (a ⬝ᵥ gThree) * (b ⬝ᵥ gThree))
        - (cOne * (a ⬝ᵥ gOne) + cTwo * (a ⬝ᵥ gTwo) + cThree * (a ⬝ᵥ gThree))
          * (cOne * (b ⬝ᵥ gOne) + cTwo * (b ⬝ᵥ gTwo) + cThree * (b ⬝ᵥ gThree)) := by
  have hlaw := sq_tripleBracket_mul_dotProduct_eq_dualReadingForm gOne gTwo gThree a b
  rw [sq_tripleBracket_of_rankOneGram hlevOne hlevTwo hlevThree hpairOneTwo
      hpairOneThree hpairTwoThree, dualReadingForm, hlevOne, hlevTwo, hlevThree,
    hpairOneTwo, hpairOneThree, hpairTwoThree] at hlaw
  linear_combination hlaw

/-! ## 4. The statement the arm needs, and its producer -/

/-- **THE MERGED EXISTENTIAL.**  At a selection `C`, SOME outside pair is heavy,
admissible, and repaid by SOME member of `C`.

This is the corrected form of the corner arm's second existence fact.  The
per-pair reading -- "EVERY admissible outside pair is repaid" -- is false; a
verified six-atom design refuting it is recorded verbatim in
`scratchpad/NOTES-f73-etwo-selector.txt` (F73-0), and at that design the other
admissible pair IS repaid, so this existential survives.  It is also all the
contradiction needs, since one strictly dominating triple is enough. -/
def CornerRepaysSomePair (D : WeightedDesign m 3) (C : Finset (Fin m)) : Prop :=
  ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, ∃ e ∈ C, d ≠ d'
    ∧ 1 < leverageOf (D.atom d)
    ∧ 0 < pairGapMinor (D.atom d) (D.atom d')
    ∧ 0 < tripleGapDet (D.atom d) (D.atom d') (D.atom e)

/-- **THE PRODUCER.**  The merged existential names a strictly dominating triple,
so no design carrying it is a tie.  Routed through the landed Sylvester producer
`Gtz.subsetSum_posDef_of_admissible_of_repay`; nothing new about positive
definiteness is spent. -/
theorem not_isTie_of_cornerRepaysSomePair (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (h : CornerRepaysSomePair D C) : ¬ IsTie D := by
  classical
  obtain ⟨d, hd, d', hd', e, he, hne, hheavy, hmin, hrepay⟩ := h
  have hdC : d ∉ C := Finset.mem_compl.mp hd
  have hd'C : d' ∉ C := Finset.mem_compl.mp hd'
  have hde : d ≠ e := fun hcon => hdC (hcon ▸ he)
  have hd'e : d' ≠ e := fun hcon => hd'C (hcon ▸ he)
  have hposDef : (subsetSum D ({d, d', e} : Finset (Fin m)) - 1).PosDef := by
    refine subsetSum_posDef_of_admissible_of_repay D hne hde hd'e hheavy hmin ?_
    rw [pairGap_adjugate_reading]
    linarith
  intro htie
  exact htie.2 _ (card_triple_eq hne hde hd'e) hposDef

/-- **THE CONTRAPOSITIVE, AS A TIE LAW.**  At a tie no heavy admissible outside
pair is repaid by any member -- every one of the nine slots of a corner sits at
its nonpositive branch.  This is the exact statement the corner arm must refute,
and stating it per pair rather than per corner is what made the older form
false. -/
theorem tripleGapDet_nonpos_of_isTie_of_admissible (D : WeightedDesign m 3)
    (htie : IsTie D) {C : Finset (Fin m)} {d d' e : Fin m}
    (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (he : e ∈ C) (hne : d ≠ d')
    (hheavy : 1 < leverageOf (D.atom d))
    (hmin : 0 < pairGapMinor (D.atom d) (D.atom d')) :
    tripleGapDet (D.atom d) (D.atom d') (D.atom e) ≤ 0 := by
  by_contra hcon
  push Not at hcon
  exact not_isTie_of_cornerRepaysSomePair D
    ⟨d, hd, d', hd', e, he, hne, hheavy, hmin, hcon⟩ htie

end Gtz

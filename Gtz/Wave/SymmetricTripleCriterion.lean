/-
# The symmetric criterion, and the pair cap solved

Two instruments, both about a single triple of a boundary system, and both
symmetric in the three atoms where the campaign's standing tools are not.

## 1. The criterion without an order

`Gtz.tripleGram_posDef_iff_pairVocabulary` decides a triple by SYLVESTER's
ordered chain: the first leverage, then one pair minor, then the determinant.
The chain names one atom and one pair, so every statement built on it has to
choose them, and every symmetry of the triple is lost at that choice.

The elementary symmetric functions decide the same question and choose nothing.
For the gap `N = K_C - 1` of a triple they are, in the campaign's own currency,

  `e₁(N) = ℓ_a + ℓ_b + ℓ_c - 3` ,
  `e₂(N) = q_ab + q_ac + q_bc` ,
  `e₃(N) = det(gap) = tripleGapDet a b c` ,

(`Gtz.trace_tripleGap`, `Gtz.secondInvariant_tripleGap_eq_pairMinorSum`,
`Gtz.det_tripleGap_eq_tripleGapDet`), and the landed
`Gtz.posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos` turns their
positivity into strict domination (`Gtz.tripleGram_posDef_of_esymm_pos`).  So

  **a triple strictly dominates as soon as its leverages pass three, its three
  pair minors total more than zero, and its gap determinant is positive** ,

with no atom and no pair singled out.  The contrapositive is the shape a
boundary system must obey at EVERY one of its twenty triples
(`Gtz.isTie_triple_esymm_trichotomy`), and since every atom of a boundary
system is heavy the first alternative collapses to the all-unit case
(`Gtz.isTie_triple_pairMinorSum_or_det_nonpos`):

  **at a boundary system every triple has `q_ab + q_ac + q_bc ≤ 0` or
  `tripleGapDet ≤ 0`, unless all three of its leverages are exactly one.**

That replaces the standing per-pair trichotomy, which had to name a pair, by
one symmetric disjunction of two clauses.

## 2. The pair cap, solved

`Gtz.pairCap_scalar_of_isTie` reads the erasure ladder's pair rung through the
three elementary symmetric functions and returns a disjunction of THREE
polynomial inequalities.  That disjunction is exactly the statement

  `λmax(t_a·g_a g_aᵀ + t_b·g_b g_bᵀ) ≥ t_a + t_b` ,

and a two-by-two matrix has a closed-form largest eigenvalue, so the three
clauses collapse to two (`Gtz.pairCap_solved_of_isTie`).  Writing `T` for the
pair's mass, `S` for its weighted leverage share and `α_c = t_c(ℓ_c - 1)` for
the weighted excess:

  **`S ≥ 2T`  or  `t_a t_b · w_ab ≤ T · (α_a + α_b)` .**

The second clause is the first upper bound this arm has on a pair's WEDGE, and
`Gtz.crossNormSq_le_of_isTie_of_share_lt` states it alone on the regime where
it holds.  Two readings follow.

**The cap is blind to a collinear pair** (`Gtz.pairCap_vacuous_of_collinear`).
A collinear pair has `w_ab = 0`, and heaviness makes the right side
nonnegative, so the bound holds with nothing spent.  That is the exact sense in
which the ladder cannot see the object the hinge produces: at a collinear pair
the pair matrix has rank one, its largest eigenvalue IS its trace, and the rung
is an identity.

**On a pair that is not collinear the cap forces excess**
(`Gtz.exists_pos_excess_of_crossNormSq_pos`).  Rank two makes `w_ab > 0`, the
bound then forces `α_a + α_b > 0`, and some atom of the pair is strictly heavy.

[MEASURED before proving.  The solved form was checked against the eigenvalue
statement at 200,000 random pairs with zero mismatches, and both clauses were
checked at every pair of six exact boundary systems -- the split diamond, the
split tetrahedron and four systems found as zeros of `Σ_T max(λmin,0)²` under
a weight floor -- with worst slack `+9.5e-2` on the rung and `+5.9e-2` on the
wedge bound over the seven pairs that lie in its regime.  The symmetric
criterion was checked against the eigenvalue test at 60,000 triples of random
designs with zero mismatches.]
-/
import Gtz.Wave.ErasedPairCap
import Gtz.Reduction.PolarGapDeterminant
import Gtz.Design.TripleGramSylvester
import Gtz.Quantitative.WindowPolarity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The three invariants of a triple's gap, in pair currency -/

/-- The trace of a triple's gap is its leverage sum less three. -/
theorem trace_tripleGap (a b c : Fin 3 → ℝ) :
    Matrix.trace (tripleGram a b c - 1)
      = leverageOf a + leverageOf b + leverageOf c - 3 := by
  rw [Matrix.trace_fin_three, gap_zero_zero, gap_one_one, gap_two_two]; ring

/-- **THE SECOND INVARIANT IS THE PAIR MINOR SUM.**  No hypothesis: the three
two-by-two principal minors of a triple's gap are exactly its three pair
minors. -/
theorem secondInvariant_tripleGap_eq_pairMinorSum (a b c : Fin 3 → ℝ) :
    secondInvariantOfThree (tripleGram a b c - 1)
      = pairGapMinor a b + pairGapMinor a c + pairGapMinor b c := by
  rw [secondInvariantOfThree, gap_zero_zero, gap_one_one, gap_two_two,
    gap_zero_one, gap_one_zero, gap_zero_two, gap_two_zero, gap_one_two, gap_two_one,
    pairGapMinor, pairGapMinor, pairGapMinor]
  ring

/-- The determinant of a triple's gap is the landed third Sylvester minor. -/
theorem det_tripleGap_eq_tripleGapDet (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1).det = tripleGapDet a b c := by
  rw [Matrix.det_fin_three, gap_zero_zero, gap_one_one, gap_two_two,
    gap_zero_one, gap_one_zero, gap_zero_two, gap_two_zero, gap_one_two, gap_two_one,
    tripleGapDet]
  ring

/-! ## 2. The symmetric criterion -/

/-- **THE SYMMETRIC PRODUCER.**  A triple whose leverages pass three, whose
pair minors total more than zero and whose gap determinant is positive
dominates strictly.  Nothing distinguishes the three atoms.

The landed `Gtz.tripleGram_posDef_iff_pairVocabulary` decides the same question
through Sylvester's ordered chain, which must name one atom and one pair. -/
theorem tripleGram_posDef_of_esymm_pos {a b c : Fin 3 → ℝ}
    (htrace : 3 < leverageOf a + leverageOf b + leverageOf c)
    (hminor : 0 < pairGapMinor a b + pairGapMinor a c + pairGapMinor b c)
    (hdet : 0 < tripleGapDet a b c) :
    (tripleGram a b c - 1).PosDef := by
  refine posDef_of_trace_pos_of_secondInvariant_pos_of_det_pos ?_ ?_ ?_ ?_
  · rw [Matrix.IsHermitian, conjTranspose_eq_transpose_real]
    exact tripleGram_sub_one_symm a b c
  · rw [trace_tripleGap]; linarith
  · rw [secondInvariant_tripleGap_eq_pairMinorSum]; exact hminor
  · rw [det_tripleGap_eq_tripleGapDet]; exact hdet

/-- The same producer at a design: a triple of a design whose three symmetric
invariants are positive dominates strictly. -/
theorem subsetSum_posDef_of_esymm_pos (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htrace : 3 < leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z))
    (hminor : 0 < pairGapMinor (D.atom x) (D.atom y)
      + pairGapMinor (D.atom x) (D.atom z) + pairGapMinor (D.atom y) (D.atom z))
    (hdet : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr
    (tripleGram_posDef_of_esymm_pos htrace hminor hdet)

/-- **THE SYMMETRIC TRICHOTOMY OF A BOUNDARY SYSTEM.**  Every triple of a
boundary system fails one of the three symmetric invariants.  The contrapositive
of the producer, and the symmetric replacement for the campaign's standing
per-pair trichotomy. -/
theorem isTie_triple_esymm_trichotomy (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) ≤ 3
      ∨ pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
          + pairGapMinor (D.atom y) (D.atom z) ≤ 0
      ∨ tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨htrace, hminor, hdet⟩ := hcon
  exact htie.2 _ (card_triple_eq hxy hxz hyz)
    (subsetSum_posDef_of_esymm_pos D hxy hxz hyz htrace hminor hdet)

/-- **THE TRICHOTOMY WITH HEAVINESS SPENT.**  Every atom of a boundary system
is heavy, so the leverage clause can only fire when all three leverages are
exactly one.  Away from that case a boundary system pays, at every triple,
either a nonpositive pair minor sum or a nonpositive gap determinant. -/
theorem isTie_triple_pairMinorSum_or_det_nonpos (D : WeightedDesign m 3)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (_hx : 1 ≤ leverageOf (D.atom x)) (_hy : 1 ≤ leverageOf (D.atom y))
    (_hz : 1 ≤ leverageOf (D.atom z))
    (hnotall : 1 < leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 2) :
    pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
        + pairGapMinor (D.atom y) (D.atom z) ≤ 0
      ∨ tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  rcases isTie_triple_esymm_trichotomy D htie hxy hxz hyz with htrace | hrest
  · exact absurd htrace (by linarith)
  · exact hrest

/-! ## 3. The pair cap, solved

The landed `Gtz.pairCap_scalar_of_isTie` is the erasure ladder's pair rung read
through the three symmetric invariants of `(t_a + t_b)·1 - P_ab`.  Its three
clauses say that the largest eigenvalue of the two-by-two Gram of the weighted
pair reaches the pair's mass, and that eigenvalue is a closed form, so two
clauses suffice. -/

/-- **THE PAIR CAP, SOLVED.**  At a boundary system of size six every pair
either carries a weighted leverage share of at least twice its mass, or has its
WEDGE bounded by its mass times its weighted excess.

The three clauses of `Gtz.pairCap_scalar_of_isTie` collapse to these two: the
first clause is strictly stronger than the left one, the third clause IS the
right one, and on the regime where the left one fails the second clause implies
the third. -/
theorem pairCap_solved_of_isTie (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b) :
    2 * (D.weight a + D.weight b)
        ≤ D.weight a * leverageOf (D.atom a) + D.weight b * leverageOf (D.atom b)
      ∨ D.weight a * D.weight b * crossNormSq (D.atom a) (D.atom b)
          ≤ (D.weight a + D.weight b)
            * (D.weight a * (leverageOf (D.atom a) - 1)
              + D.weight b * (leverageOf (D.atom b) - 1)) := by
  have hcap := pairCap_scalar_of_isTie D htie hab pick hinj havoidA havoidB
  have hwa := D.weight_pos a
  have hwb := D.weight_pos b
  have hmass : 0 < D.weight a + D.weight b := by linarith
  by_cases hshare : 2 * (D.weight a + D.weight b)
      ≤ D.weight a * leverageOf (D.atom a) + D.weight b * leverageOf (D.atom b)
  · exact Or.inl hshare
  push_neg at hshare
  refine Or.inr ?_
  rcases hcap with h1 | h2 | h3
  · nlinarith [h1, hshare, hmass]
  · nlinarith [h2, hshare, hmass]
  · nlinarith [h3, hmass]

/-- **THE WEDGE BOUND.**  On the regime where the pair's weighted leverage
share falls below twice its mass, the cap is an upper bound on the pair's
wedge, in the pair's own weights and excesses. -/
theorem crossNormSq_le_of_isTie_of_share_lt (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b)
    (hshare : D.weight a * leverageOf (D.atom a) + D.weight b * leverageOf (D.atom b)
      < 2 * (D.weight a + D.weight b)) :
    D.weight a * D.weight b * crossNormSq (D.atom a) (D.atom b)
      ≤ (D.weight a + D.weight b)
        * (D.weight a * (leverageOf (D.atom a) - 1)
          + D.weight b * (leverageOf (D.atom b) - 1)) := by
  rcases pairCap_solved_of_isTie D htie hab pick hinj havoidA havoidB with hleft | hright
  · exact absurd hleft (by linarith)
  · exact hright

/-! ## 4. What the cap sees, and what it does not -/

/-- **THE CAP IS BLIND TO A COLLINEAR PAIR.**  A collinear pair has vanishing
wedge, and heaviness makes the cap's right side nonnegative, so the bound holds
with nothing spent.  The pair matrix of a collinear pair has rank one and its
largest eigenvalue is its trace, so the rung is an identity there — this is that
statement in scalars. -/
theorem pairCap_vacuous_of_collinear (D : WeightedDesign m 3) {a b : Fin m}
    (hcol : crossNormSq (D.atom a) (D.atom b) = 0)
    (ha : 1 ≤ leverageOf (D.atom a)) (hb : 1 ≤ leverageOf (D.atom b)) :
    D.weight a * D.weight b * crossNormSq (D.atom a) (D.atom b)
      ≤ (D.weight a + D.weight b)
        * (D.weight a * (leverageOf (D.atom a) - 1)
          + D.weight b * (leverageOf (D.atom b) - 1)) := by
  have hwa := (D.weight_pos a).le
  have hwb := (D.weight_pos b).le
  rw [hcol, mul_zero]
  have hexcess : 0 ≤ D.weight a * (leverageOf (D.atom a) - 1)
      + D.weight b * (leverageOf (D.atom b) - 1) := by
    have h1 : 0 ≤ D.weight a * (leverageOf (D.atom a) - 1) :=
      mul_nonneg hwa (by linarith)
    have h2 : 0 ≤ D.weight b * (leverageOf (D.atom b) - 1) :=
      mul_nonneg hwb (by linarith)
    linarith
  exact mul_nonneg (by linarith) hexcess

/-- **A PAIR THAT IS NOT COLLINEAR PAYS EXCESS.**  In the cap's regime a
positive wedge forces the pair's weighted excess to be positive, so at least one
of its two atoms is strictly heavy.  This is the rank dichotomy of the pair
matrix — rank one against rank two — read quantitatively. -/
theorem exists_pos_excess_of_crossNormSq_pos (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b)
    (hshare : D.weight a * leverageOf (D.atom a) + D.weight b * leverageOf (D.atom b)
      < 2 * (D.weight a + D.weight b))
    (hwedge : 0 < crossNormSq (D.atom a) (D.atom b)) :
    0 < D.weight a * (leverageOf (D.atom a) - 1)
      + D.weight b * (leverageOf (D.atom b) - 1) := by
  have hbound := crossNormSq_le_of_isTie_of_share_lt D htie hab pick hinj havoidA havoidB hshare
  have hwa := D.weight_pos a
  have hwb := D.weight_pos b
  have hmass : 0 < D.weight a + D.weight b := by linarith
  nlinarith [hbound, mul_pos (mul_pos hwa hwb) hwedge, hmass]

/-- **THE STRICTLY HEAVY MEMBER.**  Under the same hypotheses one of the two
atoms has leverage strictly above one. -/
theorem exists_strictly_heavy_of_crossNormSq_pos (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b : Fin 6} (hab : a ≠ b)
    (pick : Fin 4 → Fin 6) (hinj : Function.Injective pick)
    (havoidA : ∀ i, pick i ≠ a) (havoidB : ∀ i, pick i ≠ b)
    (hshare : D.weight a * leverageOf (D.atom a) + D.weight b * leverageOf (D.atom b)
      < 2 * (D.weight a + D.weight b))
    (hwedge : 0 < crossNormSq (D.atom a) (D.atom b)) :
    1 < leverageOf (D.atom a) ∨ 1 < leverageOf (D.atom b) := by
  have hpos := exists_pos_excess_of_crossNormSq_pos D htie hab pick hinj havoidA havoidB
    hshare hwedge
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hwa := (D.weight_pos a).le
  have hwb := (D.weight_pos b).le
  nlinarith [mul_nonneg hwa (sub_nonneg.mpr ha), mul_nonneg hwb (sub_nonneg.mpr hb)]

/-! ## 5. The weight-rescaled rung

The erasure ladder's triple rung compares a triple's weighted frame operator
with the triple's total MASS.  The comparison can be made with the triple's
LARGEST WEIGHT instead, which is smaller, and the sharpening costs nothing: it
needs no erasure, no corank floor and no smaller-size instance of the theorem.

The whole content is that dropping a weight only helps.  If every weight of the
triple is at most `tau`, then

  `tau · S_T - P_T = Σ_{x ∈ T} (tau - t_x) · g_x g_xᵀ ⪰ 0` ,

so `tau · S_T ⪰ P_T`, and a weighted frame operator that already beats `tau`
strictly carries its unweighted triple past the identity. -/

/-- The weighted frame operator of a triple is below its unweighted one, scaled
by any bound on the triple's weights.  Dropping a weight only helps. -/
theorem posSemidef_smul_subsetSum_sub_weightedTriple (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {tau : ℝ}
    (hx : D.weight x ≤ tau) (hy : D.weight y ≤ tau) (hz : D.weight z ≤ tau) :
    (tau • subsetSum D ({x, y, z} : Finset (Fin m))
      - (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z))).PosSemidef := by
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]
  have hsplit : tau • subsetSum D ({x, y, z} : Finset (Fin m))
      - (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z))
      = (tau - D.weight x) • atomMatrix (D.atom x)
        + ((tau - D.weight y) • atomMatrix (D.atom y)
          + (tau - D.weight z) • atomMatrix (D.atom z)) := by
    rw [hsum, smul_add, smul_add, sub_smul, sub_smul, sub_smul]
    abel
  rw [hsplit]
  exact ((posSemidef_atomMatrix (D.atom x)).smul (by linarith)).add
    (((posSemidef_atomMatrix (D.atom y)).smul (by linarith)).add
      ((posSemidef_atomMatrix (D.atom z)).smul (by linarith)))

/-- **THE WEIGHT-RESCALED PRODUCER.**  If a triple's WEIGHTED frame operator
beats its largest weight strictly, the triple dominates strictly.

Sharper than the erasure ladder's triple rung, which compares with the triple's
whole mass `t_x + t_y + t_z` rather than with `max(t_x, t_y, t_z)`, and unlike
that rung this needs no erasure and no smaller instance of the theorem. -/
theorem subsetSum_posDef_of_weightedTriple_posDef (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {tau : ℝ}
    (htau : 0 < tau) (hx : D.weight x ≤ tau) (hy : D.weight y ≤ tau)
    (hz : D.weight z ≤ tau)
    (hpos : (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z)
      - tau • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  have hdrop := posSemidef_smul_subsetSum_sub_weightedTriple D hxy hxz hyz hx hy hz
  have hscaled : (tau • (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)).PosDef := by
    have hsplit : tau • (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        = (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
              + D.weight z • atomMatrix (D.atom z)
            - tau • (1 : Matrix (Fin 3) (Fin 3) ℝ))
          + (tau • subsetSum D ({x, y, z} : Finset (Fin m))
            - (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
              + D.weight z • atomMatrix (D.atom z))) := by
      rw [smul_sub]; abel
    rw [hsplit]
    exact hpos.add_posSemidef hdrop
  have := hscaled.smul (inv_pos.mpr htau)
  rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt htau), one_smul] at this

/-- **THE RESCALED RUNG AT A BOUNDARY SYSTEM.**  No triple of a boundary system
has its weighted frame operator strictly past its own largest weight.

Read with the largest weight of the triple in the role of `tau`, this says
`lambda_min(Σ_{x ∈ T} t_x·g_x g_xᵀ) ≤ max_{x ∈ T} t_x`, which is strictly
sharper than the ladder's `lambda_min(P_T) ≤ t_x + t_y + t_z`. -/
theorem isTie_not_posDef_weightedTriple (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {tau : ℝ}
    (htau : 0 < tau) (hx : D.weight x ≤ tau) (hy : D.weight y ≤ tau)
    (hz : D.weight z ≤ tau) :
    ¬ (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z)
      - tau • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  intro hpos
  exact htie.2 _ (card_triple_eq hxy hxz hyz)
    (subsetSum_posDef_of_weightedTriple_posDef D hxy hxz hyz htau hx hy hz hpos)

end Gtz

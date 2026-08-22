/-
# The atom cap: every dependency coordinate is priced by the co-share

`Gtz/Wave/DependencyDominationCriterion.lean` reads domination off the linear
DEPENDENCIES of the atoms,

    `Dominates D C  <->  for every z with sum_c z_c g_c = 0 :`
    `    sum_{c in C} z_c^2/(1 - t_c)  <=  sum_{c not in C} z_c^2/t_c` ,

and `Gtz/Wave/CircuitSwapLaw.lean` feeds that criterion ONE Cramer circuit at a
time.  This module supplies the two things that reading was missing: a bound on
what a SINGLE coordinate of a dependency can be, and the bilinear form behind
the criterion, which prices TWO dependencies at once.

## 1. The co-dependency, and the atom cap

Every label carries a canonical dependency, the column of the co-projection:

    `Gtz.coDependency D c := fun i => [i = c] - t_i * <g_c, g_i>` .

Parseval makes it a genuine dependency (`Gtz.sum_coDependency_smul_atom`), and
it pairs against EVERY dependency `z` in the weight-reciprocal inner product by
reading one coordinate:

  **`Gtz.sum_coDependency_mul_div_weight`:**
    `sum_i coDependency D c i * z_i / t_i  =  z_c / t_c` .

Read at `z = coDependency D c` itself this computes its own square norm,
`(1 - s_c)/t_c` with `s_c = t_c l_c` the share (`Gtz.dualNormSq_coDependency`),
and one Cauchy-Schwarz step then gives the headline:

  **`Gtz.sq_le_weight_mul_coShare_mul_dualNormSq` — THE ATOM CAP.**
    `z_c ^ 2  <=  t_c * (1 - s_c) * sum_i z_i^2/t_i` ,  at every dependency.

It is SHARP at every label: `Gtz.coDependency` attains it
(`Gtz.atomCap_eq_at_coDependency`).  The cap is the design-side statement that
the co-projection has diagonal `1 - s_c`, proved without any projection, any
chart, any kernel basis and any square root but the one inside Cauchy-Schwarz.

## 2. What the cap buys: a share-and-weight test for domination

Write `Gtz.dualRatio D c := (1 - s_c)/(1 - t_c)`.  Splitting the criterion by
`1/t + 1/(1-t) = 1/(t(1-t))` (`Gtz.depSlack_eq_dualNormSq_sub`) and spending the
cap on each selected label gives, with NO hypothesis on the atoms at all:

  **`Gtz.dominates_of_sum_dualRatio_le_one`:**
    `sum_{c in C} (1 - s_c)/(1 - t_c) <= 1`  implies  `Dominates D C` ,

and the strict twin `Gtz.posDef_gap_of_sum_dualRatio_lt_one`.  This is the first
criterion the campaign has that decides domination from the SHARES and the
WEIGHTS alone — the twelve numbers of a `(6,3)` design, with the directions of
the atoms nowhere in sight.

Its contrapositive prices every tie and every would-be GTZ counterexample:

  **`Gtz.one_le_sum_dualRatio_of_isTie`** — at a tie EVERY `k`-subset obeys
  `sum_{c in C} (1 - s_c)/(1 - t_c) >= 1`, so at `(6,3)` all TWENTY triples do
  (`Gtz.one_le_dualRatio_triple_of_isTie_sixThree`), and
  **`Gtz.gtzWeighted_sixThree_of_light_triple`** reduces `Gtz.GtzWeighted 6 3`
  to producing ONE triple of share-and-weight ratio total at most one.

The dual ratios are not free: `Gtz.sum_one_sub_weight_mul_dualRatio` says
`sum_c (1 - t_c) * dualRatio D c = m - k`, which at `(6,3)` is `3`, and
`Gtz.dualRatio_lt_one_iff_one_lt_leverage` identifies `dualRatio D c < 1` with
the ALL-HEAVY condition `l_c > 1`.  So at an all-heavy `(6,3)` tie the six dual
ratios lie in `(0,1)`, have `(1 - t)`-weighted total exactly three, and every
one of the twenty triples of them totals at least one.

[MEASURED before proving, `scratchpad/kzero`, double precision.  The atom cap
was tested at 7200000 instances — 200000 random `(6,3)` designs, six random
dependencies each, six labels each — with ZERO violations and worst ratio
`1.000000`, attained at the co-dependency.  The co-dependency was confirmed a
dependency to `1e-10` and tight in the cap at all 1200000 tests.  The
sufficient condition fired at 94416 of 4000000 triples and NEVER failed.  At
the five `(6,3)` splits of the `(5,3)` diamond — exact ties, Parseval residual
`5.6e-16`, largest triple eigenvalue `-1.4e-17`, 12 dominators for one split
and 13 for the other four, ALL of type `K0` — the smallest of the twenty
triple totals of `dualRatio` is exactly `1.3125` at every split and every
share, against the proved floor of one.]

## 3. The budget law

The bilinear form `Gtz.depCross` of the criterion splits across a subset and its
complement with no remainder:

  **`Gtz.depCross_add_depCross_compl`:**
    `depCross D C z z' + depCross D Cᶜ z z'
       = sum_i z_i z'_i/t_i - sum_i z_i z'_i/(1 - t_i)` ,

a quantity that does not mention `C`.  This is the `(6,3)` analogue of the
budget law of `Gtz/Wave/RankFourDependencyChart.lean`: at `(6,3)` a triple and
its complement are both triples, so the twenty forms pair off into ten
complementary pairs of CONSTANT total, and both members of a pair dominate only
if the budget is nonnegative (`Gtz.depBudget_self_nonneg_of_dominates_both`).
Every weight at most one half makes the budget free
(`Gtz.depBudget_self_nonneg_of_weight_le_half`).

## 4. Two circuits at once

The criterion applied to a PENCIL `x * z + z'` of dependencies is a nonnegative
quadratic in `x`, so its discriminant is dominated:

  **`Gtz.depCross_sq_le_depSlack_mul_of_dominates`:**
    `depCross D C z z' ^ 2  <=  depSlack D C z * depSlack D C z'` .

Fed the two Cramer circuits of the four-sets `{a,b,c,d}` and `{a,b,c,e}` this
becomes a relation among brackets and weights only, because the two circuits
have DISJOINT support outside the dominator and the whole outside term of the
cross form vanishes:

  **`Gtz.twoCircuitMinor_of_dominates`.**  At a dominating triple `{a,b,c}` and
  any two further labels `d`, `e`,

    `([bcd][bce]/(1-t_a) + [acd][ace]/(1-t_b) + [abd][abe]/(1-t_c))^2`
    `  <= ([abc]^2/t_d - [bcd]^2/(1-t_a) - [acd]^2/(1-t_b) - [abd]^2/(1-t_c))`
    `     * ([abc]^2/t_e - [bce]^2/(1-t_a) - [ace]^2/(1-t_b) - [abe]^2/(1-t_c))` .

The two factors on the right are exactly the slacks of the landed swap law
(`Gtz.swapLaw_of_dominates`), so this is the OFF-DIAGONAL reading of the same
matrix criterion whose diagonal the swap law already owned.

[MEASURED.  Over 300000 random `(6,3)` designs and all 6000000 triples the
two-circuit minor was tested at every one of the 1247248 dominators and its
three outside pairs, with ZERO violations and worst ratio `0.999721`, so it is
sharp.  Of the 1646557 triples that pass all three swap-law conditions only
1247248 dominate; adding the three two-circuit minors removes 331700 of the
399309 impostors, so the off-diagonal readings close `83.07` percent of the
swap law's gap and the determinant of part 5 closes the remaining `16.93`.]

## 5. The circuit Gram

At `(6,3)` the three circuits of a triple against its three outside labels are a
BASIS of the three-dimensional dependency space whenever the triple's bracket is
nonzero, which a dominator's always is
(`Gtz.tripleBracket_ne_zero_of_dominates`).  Assembling the form in that basis
gives one explicit symmetric `3 x 3` matrix per triple,

    `Gtz.circuitGram D a b c out` ,

whose diagonal is the swap law and whose off-diagonal is part 4, and

  **`Gtz.dominates_iff_posSemidef_circuitGram_sixThree`** — domination is
  exactly its positive semidefiniteness, and
  **`Gtz.posDef_gap_iff_posDef_circuitGram_sixThree`** — strict domination is
  exactly its positive definiteness.

So the whole `(6,3)` criterion at a triple is SEVEN polynomial sign conditions
in the brackets and the weights: three diagonal entries, three two-by-two
minors, one determinant.  At a tie the determinant of every dominator's circuit
Gram VANISHES (`Gtz.det_circuitGram_eq_zero_of_isTie_sixThree`), which is one
explicit polynomial equation among the three swap slacks and the three cross
terms (`Gtz.circuitGram_determinant_relation_of_isTie_sixThree`).

[MEASURED.  Over the same 6000000 triples the circuit Gram agreed with
domination at every single one, weakly and strictly, with ZERO mismatches.]

## What this module does NOT claim

* Nothing about `Gtz.HingeHoldsAtSize 6 3`.  Part 2 gives a SUFFICIENT condition
  for domination and hence a NECESSARY condition on a tie, not a proof that ties
  carry a parallel pair.
* Every statement here is FIELD-BLIND.  The cap is one Cauchy-Schwarz on a
  Parseval identity, the budget law is arithmetic, and the circuit Gram is the
  Cramer relation; each transports to `ℂ` with the squared modulus in place of
  the square.  By `Gtz/Complex/ComplexTransportLedger.lean` a field-blind
  instrument admits `Gtz.complexHingeSixDesign` as a feasible point, so none of
  these can prove the hinge on its own.  They are STRATUM tools.
-/
import Gtz.Wave.CircuitSwapLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — the quadratic form and the bilinear form of the criterion

The landed criterion compares two sums.  Naming their difference turns it into
the nonnegativity of a quadratic form on the dependency space, and polarising
that form supplies the bilinear companion that parts 3 and 4 spend. -/

/-- **THE SLACK OF THE CRITERION** at a subset and a dependency: the outside
total minus the inside total.  Domination is exactly its nonnegativity at every
dependency. -/
noncomputable def depSlack (D : WeightedDesign m k) (C : Finset (Fin m))
    (dep : Fin m → ℝ) : ℝ :=
  (∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index)
    - ∑ index ∈ C, dep index ^ 2 / (1 - D.weight index)

/-- **THE BILINEAR COMPANION** of the slack.  It is the polarisation of
`Gtz.depSlack` and it is what prices two dependencies against each other. -/
noncomputable def depCross (D : WeightedDesign m k) (C : Finset (Fin m))
    (dep other : Fin m → ℝ) : ℝ :=
  (∑ index ∈ Cᶜ, dep index * other index / D.weight index)
    - ∑ index ∈ C, dep index * other index / (1 - D.weight index)

theorem depCross_self (D : WeightedDesign m k) (C : Finset (Fin m)) (dep : Fin m → ℝ) :
    depCross D C dep dep = depSlack D C dep := by
  simp only [depCross, depSlack, pow_two]

theorem depCross_comm (D : WeightedDesign m k) (C : Finset (Fin m)) (dep other : Fin m → ℝ) :
    depCross D C dep other = depCross D C other dep := by
  simp only [depCross]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Cᶜ) => by rw [mul_comm (dep index)],
    Finset.sum_congr rfl fun index (_ : index ∈ C) => by rw [mul_comm (dep index)]]

/-- **POLARISATION.**  The slack of a pencil of dependencies is a quadratic in
the pencil parameter whose middle coefficient is twice the cross form.  No
hypothesis on the weights: the vanishing-denominator case is handled by hand. -/
theorem depSlack_smul_add (D : WeightedDesign m k) (C : Finset (Fin m))
    (scale : ℝ) (dep other : Fin m → ℝ) :
    depSlack D C (fun index => scale * dep index + other index)
      = scale ^ 2 * depSlack D C dep + 2 * scale * depCross D C dep other
        + depSlack D C other := by
  have hterm : ∀ (den : ℝ) (index : Fin m),
      (scale * dep index + other index) ^ 2 / den
        = scale ^ 2 * (dep index ^ 2 / den) + 2 * scale * (dep index * other index / den)
          + other index ^ 2 / den := by
    intro den index
    rcases eq_or_ne den 0 with hzero | hne
    · rw [hzero]; simp
    · field_simp; ring
  simp only [depSlack, depCross]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Cᶜ) => hterm (D.weight index) index,
    Finset.sum_congr rfl fun index (_ : index ∈ C) => hterm (1 - D.weight index) index]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **THE THREE-TERM POLARISATION**, which the circuit Gram of part 5 consumes. -/
theorem depSlack_sum_three (D : WeightedDesign m k) (C : Finset (Fin m))
    (scaleFirst scaleSecond scaleThird : ℝ) (depFirst depSecond depThird : Fin m → ℝ) :
    depSlack D C (fun index => scaleFirst * depFirst index + scaleSecond * depSecond index
        + scaleThird * depThird index)
      = scaleFirst ^ 2 * depSlack D C depFirst + scaleSecond ^ 2 * depSlack D C depSecond
        + scaleThird ^ 2 * depSlack D C depThird
        + 2 * scaleFirst * scaleSecond * depCross D C depFirst depSecond
        + 2 * scaleFirst * scaleThird * depCross D C depFirst depThird
        + 2 * scaleSecond * scaleThird * depCross D C depSecond depThird := by
  have hterm : ∀ (den : ℝ) (index : Fin m),
      (scaleFirst * depFirst index + scaleSecond * depSecond index
          + scaleThird * depThird index) ^ 2 / den
        = scaleFirst ^ 2 * (depFirst index ^ 2 / den)
          + scaleSecond ^ 2 * (depSecond index ^ 2 / den)
          + scaleThird ^ 2 * (depThird index ^ 2 / den)
          + 2 * scaleFirst * scaleSecond * (depFirst index * depSecond index / den)
          + 2 * scaleFirst * scaleThird * (depFirst index * depThird index / den)
          + 2 * scaleSecond * scaleThird * (depSecond index * depThird index / den) := by
    intro den index
    rcases eq_or_ne den 0 with hzero | hne
    · rw [hzero]; simp
    · field_simp; ring
  simp only [depSlack, depCross]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Cᶜ) => hterm (D.weight index) index,
    Finset.sum_congr rfl fun index (_ : index ∈ C) => hterm (1 - D.weight index) index]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **DOMINATION IS THE NONNEGATIVITY OF THE SLACK.**  The landed criterion,
renamed. -/
theorem dominates_iff_depSlack_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ ∀ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0 →
          0 ≤ depSlack D (Finset.image pick Finset.univ) dep := by
  rw [dominates_iff_dependencyBound_compl D hm pick hinj]
  simp only [depSlack, sub_nonneg]

/-- **STRICT DOMINATION IS THE STRICT POSITIVITY OF THE SLACK.** -/
theorem posDef_gap_iff_depSlack_pos (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ∀ dep : Fin m → ℝ, dep ≠ 0 → (∑ index, dep index • D.atom index) = 0 →
          0 < depSlack D (Finset.image pick Finset.univ) dep := by
  rw [posDef_gap_iff_dependencyBound_compl D hm pick hinj]
  simp only [depSlack, sub_pos]

/-- A pencil of dependencies is a dependency. -/
theorem sum_smul_add_smul_atom_eq_zero (D : WeightedDesign m k) (scale : ℝ)
    {dep other : Fin m → ℝ}
    (hdep : (∑ index, dep index • D.atom index) = 0)
    (hother : (∑ index, other index • D.atom index) = 0) :
    (∑ index, (scale * dep index + other index) • D.atom index) = 0 := by
  have hsplit : ∀ index : Fin m,
      (scale * dep index + other index) • D.atom index
        = scale • (dep index • D.atom index) + other index • D.atom index := by
    intro index
    rw [add_smul, smul_smul]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hsplit index,
    Finset.sum_add_distrib, ← Finset.smul_sum, hdep, hother, smul_zero, add_zero]

/-- The three-term pencil is a dependency as well. -/
theorem sum_smul_three_atom_eq_zero (D : WeightedDesign m k)
    (scaleFirst scaleSecond scaleThird : ℝ) {depFirst depSecond depThird : Fin m → ℝ}
    (hfirst : (∑ index, depFirst index • D.atom index) = 0)
    (hsecond : (∑ index, depSecond index • D.atom index) = 0)
    (hthird : (∑ index, depThird index • D.atom index) = 0) :
    (∑ index, (scaleFirst * depFirst index + scaleSecond * depSecond index
        + scaleThird * depThird index) • D.atom index) = 0 := by
  have hsplit : ∀ index : Fin m,
      (scaleFirst * depFirst index + scaleSecond * depSecond index
          + scaleThird * depThird index) • D.atom index
        = scaleFirst • (depFirst index • D.atom index)
          + scaleSecond • (depSecond index • D.atom index)
          + scaleThird • (depThird index • D.atom index) := by
    intro index
    rw [add_smul, add_smul, smul_smul, smul_smul, smul_smul]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hsplit index,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    ← Finset.smul_sum, hfirst, hsecond, hthird, smul_zero, smul_zero, smul_zero,
    add_zero, add_zero]

/-! ## Part 2 — the budget law

A subset and its complement split the criterion with no remainder.  At `(6,3)`
both members of the split are triples, so the twenty forms pair off into ten
complementary pairs of constant total. -/

/-- **THE BUDGET** of a pair of vectors: the criterion's form with the whole
label set on each side.  No subset appears. -/
noncomputable def depBudget (D : WeightedDesign m k) (dep other : Fin m → ℝ) : ℝ :=
  (∑ index, dep index * other index / D.weight index)
    - ∑ index, dep index * other index / (1 - D.weight index)

/-- **THE BUDGET LAW.**  The cross forms of a subset and of its complement total
the budget, which does not mention the subset. -/
theorem depCross_add_depCross_compl (D : WeightedDesign m k) (C : Finset (Fin m))
    (dep other : Fin m → ℝ) :
    depCross D C dep other + depCross D Cᶜ dep other = depBudget D dep other := by
  classical
  have hone := Finset.sum_add_sum_compl C
    (fun index => dep index * other index / D.weight index)
  have htwo := Finset.sum_add_sum_compl C
    (fun index => dep index * other index / (1 - D.weight index))
  simp only [depCross, depBudget, compl_compl]
  linarith

/-- **THE BUDGET LAW ON THE DIAGONAL.**  The slacks of a subset and of its
complement total one quantity that does not mention the subset. -/
theorem depSlack_add_depSlack_compl (D : WeightedDesign m k) (C : Finset (Fin m))
    (dep : Fin m → ℝ) :
    depSlack D C dep + depSlack D Cᶜ dep = depBudget D dep dep := by
  rw [← depCross_self D C dep, ← depCross_self D Cᶜ dep]
  exact depCross_add_depCross_compl D C dep dep

/-- The complement's slack is the budget minus the subset's. -/
theorem depSlack_compl_eq_sub (D : WeightedDesign m k) (C : Finset (Fin m))
    (dep : Fin m → ℝ) :
    depSlack D Cᶜ dep = depBudget D dep dep - depSlack D C dep := by
  have hlaw := depSlack_add_depSlack_compl D C dep
  linarith

/-- **A COMPLEMENTARY PAIR OF DOMINATORS COSTS A NONNEGATIVE BUDGET.**  At
`(6,3)` a triple and its complement are both triples, so this is a genuine
constraint on the ten complementary pairs. -/
theorem depBudget_self_nonneg_of_dominates_both (D : WeightedDesign m k) (C : Finset (Fin m))
    {dep : Fin m → ℝ}
    (hinside : 0 ≤ depSlack D C dep) (houtside : 0 ≤ depSlack D Cᶜ dep) :
    0 ≤ depBudget D dep dep := by
  have hlaw := depSlack_add_depSlack_compl D C dep
  linarith

/-- **A LIGHT DESIGN HAS A FREE BUDGET.**  When every weight is at most one half
the reciprocal of the weight beats the reciprocal of the co-weight at every
label, so the budget is nonnegative at every vector. -/
theorem depBudget_self_nonneg_of_weight_le_half (D : WeightedDesign m k)
    (hlight : ∀ index : Fin m, D.weight index ≤ 1 / 2) (dep : Fin m → ℝ) :
    0 ≤ depBudget D dep dep := by
  have hterm : ∀ index : Fin m,
      dep index * dep index / (1 - D.weight index) ≤ dep index * dep index / D.weight index := by
    intro index
    have hpos := D.weight_pos index
    have hco : D.weight index ≤ 1 - D.weight index := by linarith [hlight index]
    have hcopos : (0 : ℝ) < 1 - D.weight index := by linarith
    have hsq : 0 ≤ dep index * dep index := mul_self_nonneg _
    exact div_le_div_of_nonneg_left hsq hpos hco
  simp only [depBudget, sub_nonneg]
  exact Finset.sum_le_sum fun index _ => hterm index

/-! ## Part 3 — the co-dependency and the atom cap -/

/-- **THE CO-DEPENDENCY OF A LABEL.**  The column of the co-projection at that
label, written with no projection: `1` at the label, minus the weighted pairings
of the label's atom against every atom.  Parseval makes it a dependency. -/
noncomputable def coDependency (D : WeightedDesign m k) (center : Fin m) : Fin m → ℝ :=
  fun index => (if index = center then (1 : ℝ) else 0)
    - D.weight index * (D.atom center ⬝ᵥ D.atom index)

/-- **PARSEVAL, READ AT AN ATOM.**  The weighted pairings of one atom against all
atoms rebuild that atom. -/
theorem sum_weight_mul_pairing_smul_atom (D : WeightedDesign m k) (center : Fin m) :
    (∑ index, (D.weight index * (D.atom center ⬝ᵥ D.atom index)) • D.atom index)
      = D.atom center := by
  have hpar := congrArg (fun mat : Matrix (Fin k) (Fin k) ℝ => mat *ᵥ D.atom center)
    D.isParseval
  simp only [Matrix.one_mulVec] at hpar
  rw [Matrix.sum_mulVec] at hpar
  have hterm : ∀ index : Fin m,
      (D.weight index • atomMatrix (D.atom index)) *ᵥ D.atom center
        = (D.weight index * (D.atom center ⬝ᵥ D.atom index)) • D.atom index := by
    intro index
    rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, smul_smul,
      dotProduct_comm (D.atom index) (D.atom center)]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hterm index] at hpar
  exact hpar

/-- **THE CO-DEPENDENCY IS A DEPENDENCY.** -/
theorem sum_coDependency_smul_atom (D : WeightedDesign m k) (center : Fin m) :
    (∑ index, coDependency D center index • D.atom index) = 0 := by
  classical
  have hsplit : ∀ index : Fin m,
      coDependency D center index • D.atom index
        = (if index = center then (1 : ℝ) else 0) • D.atom index
          - (D.weight index * (D.atom center ⬝ᵥ D.atom index)) • D.atom index := by
    intro index
    rw [coDependency, sub_smul]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hsplit index,
    Finset.sum_sub_distrib, sum_weight_mul_pairing_smul_atom D center]
  have hindicator : (∑ index, (if index = center then (1 : ℝ) else 0) • D.atom index)
      = D.atom center := by
    rw [Finset.sum_eq_single center]
    · rw [if_pos rfl, one_smul]
    · intro other _ hne
      rw [if_neg hne, zero_smul]
    · intro hnot
      exact absurd (Finset.mem_univ center) hnot
  rw [hindicator, sub_self]

theorem coDependency_apply_self (D : WeightedDesign m k) (center : Fin m) :
    coDependency D center center = 1 - shareOf D center := by
  rw [coDependency, if_pos rfl, shareOf, leverageOf_eq_dotProduct]

theorem coDependency_apply_of_ne (D : WeightedDesign m k) {center index : Fin m}
    (hne : index ≠ center) :
    coDependency D center index = -(D.weight index * (D.atom center ⬝ᵥ D.atom index)) := by
  rw [coDependency, if_neg hne]
  ring

/-- **THE SQUARE NORM OF A VECTOR IN THE WEIGHT-RECIPROCAL METRIC.**  It is the
right side of the criterion when the selected subset is empty, and it is the
ambient norm of the dependency chart. -/
noncomputable def dualNormSq (D : WeightedDesign m k) (dep : Fin m → ℝ) : ℝ :=
  ∑ index, dep index ^ 2 / D.weight index

theorem dualNormSq_nonneg (D : WeightedDesign m k) (dep : Fin m → ℝ) :
    0 ≤ dualNormSq D dep :=
  Finset.sum_nonneg fun index _ => div_nonneg (sq_nonneg _) (D.weight_pos index).le

theorem dualNormSq_pos_of_ne_zero (D : WeightedDesign m k) {dep : Fin m → ℝ}
    (hne : dep ≠ 0) : 0 < dualNormSq D dep := by
  obtain ⟨badIndex, hbad⟩ := Function.ne_iff.mp hne
  refine Finset.sum_pos' (fun index _ => div_nonneg (sq_nonneg _) (D.weight_pos index).le)
    ⟨badIndex, Finset.mem_univ badIndex, ?_⟩
  have hne' : dep badIndex ≠ 0 := by simpa using hbad
  have hsq : 0 < dep badIndex ^ 2 := by
    have habs : 0 < |dep badIndex| := abs_pos.mpr hne'
    nlinarith [sq_abs (dep badIndex), habs]
  exact div_pos hsq (D.weight_pos badIndex)

/-- **THE READING LAW.**  In the weight-reciprocal metric the co-dependency of a
label pairs against EVERY dependency by reading that one coordinate.  The atoms
disappear because the dependency annihilates them. -/
theorem sum_coDependency_mul_div_weight (D : WeightedDesign m k) (center : Fin m)
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    (∑ index, coDependency D center index * dep index / D.weight index)
      = dep center / D.weight center := by
  classical
  have hannihilate : (∑ index, dep index * (D.atom center ⬝ᵥ D.atom index)) = 0 := by
    have hzero : (D.atom center) ⬝ᵥ (∑ index, dep index • D.atom index) = 0 := by
      rw [hdep, dotProduct_zero]
    rw [dotProduct_sum] at hzero
    rw [← hzero]
    exact Finset.sum_congr rfl fun index _ => by rw [dotProduct_smul, smul_eq_mul]
  have hterm : ∀ index : Fin m,
      coDependency D center index * dep index / D.weight index
        = (if index = center then dep index / D.weight index else 0)
          - dep index * (D.atom center ⬝ᵥ D.atom index) := by
    intro index
    have hw := (D.weight_pos index).ne'
    rw [coDependency]
    by_cases hindex : index = center
    · rw [if_pos hindex, if_pos hindex]
      field_simp
      try ring
    · rw [if_neg hindex, if_neg hindex]
      field_simp
      try ring
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hterm index,
    Finset.sum_sub_distrib, hannihilate, sub_zero,
    Finset.sum_ite_eq' Finset.univ center (fun index => dep index / D.weight index),
    if_pos (Finset.mem_univ center)]

/-- **THE CO-DEPENDENCY'S OWN SQUARE NORM** is the co-share over the weight.  It
is the reading law applied to the co-dependency itself. -/
theorem dualNormSq_coDependency (D : WeightedDesign m k) (center : Fin m) :
    dualNormSq D (coDependency D center) = (1 - shareOf D center) / D.weight center := by
  have hread := sum_coDependency_mul_div_weight D center (sum_coDependency_smul_atom D center)
  rw [coDependency_apply_self] at hread
  rw [dualNormSq, ← hread]
  exact Finset.sum_congr rfl fun index _ => by rw [pow_two]

/-- **THE ATOM CAP.**  Every coordinate of every dependency is capped by the
co-share of its label, measured against the ambient square norm.  One
Cauchy-Schwarz step against the co-dependency, and the atoms never appear.

The bound is SHARP at every label: `Gtz.atomCap_eq_at_coDependency`. -/
theorem sq_le_weight_mul_coShare_mul_dualNormSq (D : WeightedDesign m k) (center : Fin m)
    {dep : Fin m → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    dep center ^ 2 ≤ D.weight center * (1 - shareOf D center) * dualNormSq D dep := by
  have hsqrtPos : ∀ index : Fin m, 0 < Real.sqrt (D.weight index) := fun index =>
    Real.sqrt_pos.mpr (D.weight_pos index)
  have hsq : ∀ index : Fin m, Real.sqrt (D.weight index) ^ 2 = D.weight index := fun index =>
    Real.sq_sqrt (D.weight_pos index).le
  have hCS := sum_mul_sq_le Finset.univ
    (fun index => coDependency D center index / Real.sqrt (D.weight index))
    (fun index => dep index / Real.sqrt (D.weight index))
  have hmix : ∀ index : Fin m,
      (coDependency D center index / Real.sqrt (D.weight index))
          * (dep index / Real.sqrt (D.weight index))
        = coDependency D center index * dep index / D.weight index := by
    intro index
    rw [div_mul_div_comm, ← pow_two, hsq]
  have hleftSq : ∀ index : Fin m,
      (coDependency D center index / Real.sqrt (D.weight index)) ^ 2
        = coDependency D center index ^ 2 / D.weight index := by
    intro index
    rw [div_pow, hsq]
  have hrightSq : ∀ index : Fin m,
      (dep index / Real.sqrt (D.weight index)) ^ 2 = dep index ^ 2 / D.weight index := by
    intro index
    rw [div_pow, hsq]
  rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hmix index,
    Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hleftSq index,
    Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hrightSq index,
    sum_coDependency_mul_div_weight D center hdep] at hCS
  have hnormLeft : (∑ index, coDependency D center index ^ 2 / D.weight index)
      = (1 - shareOf D center) / D.weight center := dualNormSq_coDependency D center
  have hnormRight : (∑ index, dep index ^ 2 / D.weight index) = dualNormSq D dep := rfl
  rw [hnormLeft, hnormRight] at hCS
  have hwPos := D.weight_pos center
  have hscaled := mul_le_mul_of_nonneg_right hCS (sq_nonneg (D.weight center))
  have hleftEq : (dep center / D.weight center) ^ 2 * D.weight center ^ 2 = dep center ^ 2 := by
    field_simp
  have hrightEq : (1 - shareOf D center) / D.weight center * dualNormSq D dep
        * D.weight center ^ 2
      = D.weight center * (1 - shareOf D center) * dualNormSq D dep := by
    field_simp
    try ring
  rw [hleftEq, hrightEq] at hscaled
  exact hscaled

/-- **THE ATOM CAP IS SHARP.**  The co-dependency of a label attains it. -/
theorem atomCap_eq_at_coDependency (D : WeightedDesign m k) (center : Fin m) :
    coDependency D center center ^ 2
      = D.weight center * (1 - shareOf D center) * dualNormSq D (coDependency D center) := by
  rw [dualNormSq_coDependency, coDependency_apply_self]
  have hw := (D.weight_pos center).ne'
  field_simp
  try ring

/-! ## Part 4 — the share-and-weight test for domination

Splitting the criterion by `1/t + 1/(1-t) = 1/(t(1-t))` puts the ambient norm on
one side, and the cap prices each selected label by its DUAL RATIO.  The result
decides domination from twelve numbers, with the directions of the atoms nowhere
in the statement. -/

/-- **THE DUAL RATIO** of a label: its co-share over its co-weight.  It is the
square length of the label's dual atom in the dependency chart, and it is below
one exactly when the label is heavy. -/
noncomputable def dualRatio (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  (1 - shareOf D label) / (1 - D.weight label)

theorem dualRatio_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m) (label : Fin m) :
    0 ≤ dualRatio D label := by
  have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
  exact div_nonneg (by linarith [shareOf_le_one D label]) hco.le

/-- **THE DUAL RATIO READS THE HEAVY CONDITION.**  A label is heavy exactly when
its dual ratio is below one. -/
theorem dualRatio_lt_one_iff_one_lt_leverage (D : WeightedDesign m k) (hm : 2 ≤ m)
    (label : Fin m) :
    dualRatio D label < 1 ↔ 1 < leverageOf (D.atom label) := by
  have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
  have hw := D.weight_pos label
  rw [dualRatio, div_lt_one hco, shareOf]
  constructor
  · intro hstep
    nlinarith [hstep, hw]
  · intro hlev
    nlinarith [hlev, hw]

/-- **THE DUAL TRACE.**  The co-weighted total of the dual ratios is `m - k`: it
is the co-share total, which Parseval fixes.  At `(6,3)` it is three. -/
theorem sum_one_sub_weight_mul_dualRatio (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (∑ label, (1 - D.weight label) * dualRatio D label) = (m : ℝ) - (k : ℝ) := by
  have hterm : ∀ label : Fin m,
      (1 - D.weight label) * dualRatio D label = 1 - shareOf D label := by
    intro label
    have hco : (0 : ℝ) < 1 - D.weight label := by linarith [weight_lt_one D hm label]
    rw [dualRatio, mul_div_cancel₀ _ hco.ne']
  rw [Finset.sum_congr rfl fun label (_ : label ∈ Finset.univ) => hterm label,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_shareOf D]

/-- **THE SLACK, WITH THE AMBIENT NORM SPLIT OFF.**  The criterion at a subset
subtracts from the ambient square norm one term per selected label, and that term
is the label's square DUAL reading `z_c^2/(t_c(1 - t_c))`. -/
theorem depSlack_eq_dualNormSq_sub (D : WeightedDesign m k) (hm : 2 ≤ m)
    (C : Finset (Fin m)) (dep : Fin m → ℝ) :
    depSlack D C dep
      = dualNormSq D dep
        - ∑ index ∈ C, dep index ^ 2 / (D.weight index * (1 - D.weight index)) := by
  classical
  have hsplit : dualNormSq D dep
      = (∑ index ∈ C, dep index ^ 2 / D.weight index)
        + ∑ index ∈ Cᶜ, dep index ^ 2 / D.weight index :=
    (Finset.sum_add_sum_compl C _).symm
  have hmerge : ∀ index : Fin m,
      dep index ^ 2 / (D.weight index * (1 - D.weight index))
        = dep index ^ 2 / D.weight index + dep index ^ 2 / (1 - D.weight index) := by
    intro index
    have hw := (D.weight_pos index).ne'
    have hco : (1 : ℝ) - D.weight index ≠ 0 := by
      have := weight_lt_one D hm index
      intro hzero; linarith [hzero]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun index (_ : index ∈ C) => hmerge index, Finset.sum_add_distrib,
    depSlack, hsplit]
  ring

/-- **THE CAP, SPENT ON A SUBSET.**  Each selected label's dual reading is capped
by its dual ratio times the ambient norm. -/
theorem sum_dualReading_le_of_dependency (D : WeightedDesign m k) (hm : 2 ≤ m)
    (C : Finset (Fin m)) {dep : Fin m → ℝ}
    (hdep : (∑ index, dep index • D.atom index) = 0) :
    (∑ index ∈ C, dep index ^ 2 / (D.weight index * (1 - D.weight index)))
      ≤ (∑ index ∈ C, dualRatio D index) * dualNormSq D dep := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun index _ => ?_
  have hw := D.weight_pos index
  have hco : (0 : ℝ) < 1 - D.weight index := by linarith [weight_lt_one D hm index]
  have hcap := sq_le_weight_mul_coShare_mul_dualNormSq D index hdep
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < D.weight index * (1 - D.weight index))]
  have hexpand : dualRatio D index * dualNormSq D dep
        * (D.weight index * (1 - D.weight index))
      = D.weight index * (1 - shareOf D index) * dualNormSq D dep := by
    rw [dualRatio]
    field_simp
    try ring
  rw [hexpand]
  exact hcap

/-- **THE SHARE-AND-WEIGHT TEST.**  A subset whose dual ratios total at most one
DOMINATES.  No hypothesis on the atoms, no bracket, no Gram: the criterion is
decided by the shares and the weights alone. -/
theorem dominates_of_sum_dualRatio_le_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (hsum : (∑ index ∈ Finset.image pick Finset.univ, dualRatio D index) ≤ 1) :
    Dominates D (Finset.image pick Finset.univ) := by
  classical
  rw [dominates_iff_depSlack_nonneg D hm pick hinj]
  intro dep hdep
  have hsplit := depSlack_eq_dualNormSq_sub D hm (Finset.image pick Finset.univ) dep
  have hcap := sum_dualReading_le_of_dependency D hm (Finset.image pick Finset.univ) hdep
  have hnorm := dualNormSq_nonneg D dep
  nlinarith [hsplit, hcap, hnorm, hsum]

/-- **THE STRICT SHARE-AND-WEIGHT TEST.**  Below one the subset dominates
STRICTLY. -/
theorem posDef_gap_of_sum_dualRatio_lt_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (hsum : (∑ index ∈ Finset.image pick Finset.univ, dualRatio D index) < 1) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
  classical
  rw [posDef_gap_iff_depSlack_pos D hm pick hinj]
  intro dep hne hdep
  have hsplit := depSlack_eq_dualNormSq_sub D hm (Finset.image pick Finset.univ) dep
  have hcap := sum_dualReading_le_of_dependency D hm (Finset.image pick Finset.univ) hdep
  have hnorm := dualNormSq_pos_of_ne_zero D hne
  nlinarith [hsplit, hcap, hnorm, hsum]

/-- **THE TIE PRICES EVERY SUBSET.**  A tie carries no strictly dominating
`k`-subset, so EVERY `k`-subset has dual ratios totalling at least one.  At
`(6,3)` that is twenty inequalities in the six shares and the six weights, with
the atoms nowhere in sight. -/
theorem one_le_sum_dualRatio_of_isTie (D : WeightedDesign m k) (hm : 2 ≤ m) (htie : IsTie D)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    1 ≤ ∑ index ∈ Finset.image pick Finset.univ, dualRatio D index := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcard : (Finset.image pick Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  exact htie.2 _ hcard (posDef_gap_of_sum_dualRatio_lt_one D hm pick hinj hcon)

/-- **THE GTZ TEST AT `(6,3)`.**  `Gtz.GtzWeighted 6 3` follows from producing,
at every `(6,3)` design, ONE triple whose dual ratios total at most one. -/
theorem gtzWeighted_sixThree_of_light_triple
    (hlight : ∀ D : WeightedDesign 6 3, ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ dualRatio D a + dualRatio D b + dualRatio D c ≤ 1) :
    GtzWeighted 6 3 := by
  classical
  intro D
  obtain ⟨a, b, c, hab, hac, hbc, hsum⟩ := hlight D
  refine ⟨({a, b, c} : Finset (Fin 6)), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  · have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 6) :=
      injective_tripleVec hab hac hbc
    have himage : Finset.image (![a, b, c] : Fin 3 → Fin 6) Finset.univ
        = ({a, b, c} : Finset (Fin 6)) := image_tripleVec_eq
    have hstep : Dominates D (Finset.image (![a, b, c] : Fin 3 → Fin 6) Finset.univ) := by
      refine dominates_of_sum_dualRatio_le_one D (by norm_num) _ hinj ?_
      rw [himage, sum_over_triple (fun index => dualRatio D index) hab hac hbc]
      exact hsum
    rwa [himage] at hstep

/-- **THE TIE PRICES EVERY TRIPLE AT `(6,3)`.**  The packaged form: twenty
inequalities among the six shares and the six weights. -/
theorem one_le_dualRatio_triple_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    1 ≤ dualRatio D a + dualRatio D b + dualRatio D c := by
  classical
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 6) := injective_tripleVec hab hac hbc
  have himage : Finset.image (![a, b, c] : Fin 3 → Fin 6) Finset.univ
      = ({a, b, c} : Finset (Fin 6)) := image_tripleVec_eq
  have hstep := one_le_sum_dualRatio_of_isTie D (by norm_num) htie _ hinj
  rwa [himage, sum_over_triple (fun index => dualRatio D index) hab hac hbc] at hstep

/-- **THE ALL-HEAVY TIE, IN SHARES AND WEIGHTS.**  At an all-heavy `(6,3)` tie
every dual ratio lies strictly below one and every triple of them totals at
least one. -/
theorem allHeavy_isTie_sixThree_dualRatio_window (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D) (htie : IsTie D) :
    (∀ label : Fin 6, dualRatio D label < 1)
      ∧ ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
          1 ≤ dualRatio D a + dualRatio D b + dualRatio D c :=
  ⟨fun label => (dualRatio_lt_one_iff_one_lt_leverage D (by norm_num) label).mpr (hheavy label),
    fun a b c hab hac hbc => one_le_dualRatio_triple_of_isTie_sixThree D htie hab hac hbc⟩

/-! ## Part 5 — two circuits at once -/

/-- **THE DISCRIMINANT READING.**  At a dominator the cross form of two
dependencies is dominated by the geometric mean of their slacks.  The criterion
applied to the whole pencil is a nonnegative quadratic, and its discriminant
does the rest. -/
theorem depCross_sq_le_depSlack_mul_of_dominates (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick)
    (hdom : Dominates D (Finset.image pick Finset.univ))
    {dep other : Fin m → ℝ}
    (hdep : (∑ index, dep index • D.atom index) = 0)
    (hother : (∑ index, other index • D.atom index) = 0) :
    depCross D (Finset.image pick Finset.univ) dep other ^ 2
      ≤ depSlack D (Finset.image pick Finset.univ) dep
        * depSlack D (Finset.image pick Finset.univ) other := by
  classical
  have hcrit := (dominates_iff_depSlack_nonneg D hm pick hinj).mp hdom
  refine discriminant_le_of_quadratic_nonneg (hcrit dep hdep) fun coordinate => ?_
  have hpencil := hcrit _ (sum_smul_add_smul_atom_eq_zero D coordinate hdep hother)
  rw [depSlack_smul_add] at hpencil
  linarith

/-! ### The two circuits of a dominator against two outside labels -/

/-- **THE OUTSIDE PART OF A CROSS OF TWO CIRCUITS VANISHES.**  The circuits of
`{a,b,c,d}` and of `{a,b,c,e}` meet the complement of `{a,b,c}` in the single
labels `d` and `e`, which are different, so every product is zero. -/
theorem sum_circuitDep_mul_circuitDep_compl (D : WeightedDesign m 3) {a b c d e : Fin m}
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    (∑ index ∈ (({a, b, c} : Finset (Fin m))ᶜ),
        circuitDep D a b c d index * circuitDep D a b c e index / D.weight index) = 0 := by
  classical
  refine Finset.sum_eq_zero fun index hindex => ?_
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hindex
  obtain ⟨hna, hnb, hnc⟩ := hindex
  by_cases hd : index = d
  · have hne : index ≠ e := by rw [hd]; exact hde
    rw [circuitDep_apply_of_notMem D hna hnb hnc hne, mul_zero, zero_div]
  · rw [circuitDep_apply_of_notMem D hna hnb hnc hd, zero_mul, zero_div]

/-- **THE CROSS OF TWO CIRCUITS.**  Only the three inside labels survive, and
each contributes the product of the two omitted brackets. -/
theorem depCross_circuitDep (D : WeightedDesign m 3) {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e) :
    depCross D ({a, b, c} : Finset (Fin m)) (circuitDep D a b c d) (circuitDep D a b c e)
      = -(tripleBracket (D.atom b) (D.atom c) (D.atom d)
              * tripleBracket (D.atom b) (D.atom c) (D.atom e) / (1 - D.weight a)
            + tripleBracket (D.atom a) (D.atom c) (D.atom d)
              * tripleBracket (D.atom a) (D.atom c) (D.atom e) / (1 - D.weight b)
            + tripleBracket (D.atom a) (D.atom b) (D.atom d)
              * tripleBracket (D.atom a) (D.atom b) (D.atom e) / (1 - D.weight c)) := by
  classical
  rw [depCross, sum_circuitDep_mul_circuitDep_compl D had hbd hcd hae hbe hce hde,
    sum_over_triple (fun index => circuitDep D a b c d index * circuitDep D a b c e index
      / (1 - D.weight index)) hab hac hbc,
    circuitDep_apply_first D hab hac had, circuitDep_apply_first D hab hac hae,
    circuitDep_apply_second D hab hbc hbd, circuitDep_apply_second D hab hbc hbe,
    circuitDep_apply_third D hac hbc hcd, circuitDep_apply_third D hac hbc hce]
  ring

/-- **THE SLACK OF A CIRCUIT** is the swap law's own slack: the dominator's own
squared volume against the incoming weight, minus the three swapped volumes
against the co-weights. -/
theorem depSlack_circuitDep (D : WeightedDesign m 3) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    depSlack D ({a, b, c} : Finset (Fin m)) (circuitDep D a b c d)
      = tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d
        - (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
          + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
          + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c)) := by
  classical
  have hdmem : d ∈ (({a, b, c} : Finset (Fin m))ᶜ) := by
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm had, Ne.symm hbd, Ne.symm hcd⟩
  have houtside : (∑ index ∈ (({a, b, c} : Finset (Fin m))ᶜ),
        circuitDep D a b c d index ^ 2 / D.weight index)
      = tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d := by
    rw [Finset.sum_eq_single_of_mem d hdmem]
    · rw [circuitDep_apply_fourth D had hbd hcd, neg_pow]
      ring
    · intro other hother hne
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hother
      rw [circuitDep_apply_of_notMem D hother.1 hother.2.1 hother.2.2 hne]
      simp
  rw [depSlack, houtside,
    sum_over_triple (fun index => circuitDep D a b c d index ^ 2 / (1 - D.weight index))
      hab hac hbc,
    circuitDep_apply_first D hab hac had, circuitDep_apply_second D hab hbc hbd,
    circuitDep_apply_third D hac hbc hcd]
  rw [neg_pow]
  ring

/-- **THE TWO-CIRCUIT MINOR.**  The off-diagonal reading of the matrix criterion
whose diagonal is the landed swap law.  Every quantity is a bracket and a
weight, and the left side is a full square, so the law is strictly stronger than
the product of the two swap-law slacks. -/
theorem twoCircuitMinor_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m) {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    (tripleBracket (D.atom b) (D.atom c) (D.atom d)
            * tripleBracket (D.atom b) (D.atom c) (D.atom e) / (1 - D.weight a)
          + tripleBracket (D.atom a) (D.atom c) (D.atom d)
            * tripleBracket (D.atom a) (D.atom c) (D.atom e) / (1 - D.weight b)
          + tripleBracket (D.atom a) (D.atom b) (D.atom d)
            * tripleBracket (D.atom a) (D.atom b) (D.atom e) / (1 - D.weight c)) ^ 2
      ≤ (tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d
            - (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
              + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
              + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c)))
        * (tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight e
            - (tripleBracket (D.atom b) (D.atom c) (D.atom e) ^ 2 / (1 - D.weight a)
              + tripleBracket (D.atom a) (D.atom c) (D.atom e) ^ 2 / (1 - D.weight b)
              + tripleBracket (D.atom a) (D.atom b) (D.atom e) ^ 2 / (1 - D.weight c))) := by
  classical
  set pick : Fin 3 → Fin m := ![a, b, c] with hpick
  have hinj : Function.Injective pick := injective_tripleVec hab hac hbc
  have himage : Finset.image pick Finset.univ = ({a, b, c} : Finset (Fin m)) :=
    image_tripleVec_eq
  have hdom' : Dominates D (Finset.image pick Finset.univ) := by rw [himage]; exact hdom
  have hstep := depCross_sq_le_depSlack_mul_of_dominates D hm pick hinj hdom'
    (sum_circuitDep_smul_atom D a b c d) (sum_circuitDep_smul_atom D a b c e)
  rw [himage, depCross_circuitDep D hab hac hbc had hbd hcd hae hbe hce hde,
    depSlack_circuitDep D hab hac hbc had hbd hcd,
    depSlack_circuitDep D hab hac hbc hae hbe hce, neg_pow] at hstep
  simpa using hstep

/-- **THE CONTRAPOSITIVE**, the shape a search reports. -/
theorem not_dominates_of_twoCircuitMinor_violation (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c d e : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e) (hde : d ≠ e)
    (hviolate :
      (tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight d
            - (tripleBracket (D.atom b) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight a)
              + tripleBracket (D.atom a) (D.atom c) (D.atom d) ^ 2 / (1 - D.weight b)
              + tripleBracket (D.atom a) (D.atom b) (D.atom d) ^ 2 / (1 - D.weight c)))
        * (tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 / D.weight e
            - (tripleBracket (D.atom b) (D.atom c) (D.atom e) ^ 2 / (1 - D.weight a)
              + tripleBracket (D.atom a) (D.atom c) (D.atom e) ^ 2 / (1 - D.weight b)
              + tripleBracket (D.atom a) (D.atom b) (D.atom e) ^ 2 / (1 - D.weight c)))
      < (tripleBracket (D.atom b) (D.atom c) (D.atom d)
            * tripleBracket (D.atom b) (D.atom c) (D.atom e) / (1 - D.weight a)
          + tripleBracket (D.atom a) (D.atom c) (D.atom d)
            * tripleBracket (D.atom a) (D.atom c) (D.atom e) / (1 - D.weight b)
          + tripleBracket (D.atom a) (D.atom b) (D.atom d)
            * tripleBracket (D.atom a) (D.atom b) (D.atom e) / (1 - D.weight c)) ^ 2) :
    ¬ Dominates D ({a, b, c} : Finset (Fin m)) := fun hdom =>
  absurd (twoCircuitMinor_of_dominates D hm hab hac hbc had hbd hcd hae hbe hce hde hdom)
    (not_le.mpr hviolate)

/-! ## Part 6 — the circuit Gram

At `(6,3)` the three circuits of a triple against its three outside labels are a
basis of the dependency space, so the whole criterion at that triple is ONE
explicit symmetric `3 x 3` matrix. -/

/-- **THE CIRCUIT GRAM** of a triple against three further labels: the form of
the criterion in the basis its own circuits supply.  Its diagonal is the swap
law and its off-diagonal is the two-circuit minor. -/
noncomputable def circuitGram (D : WeightedDesign m 3) (a b c : Fin m)
    (out : Fin 3 → Fin m) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun rowSlot colSlot =>
    depCross D ({a, b, c} : Finset (Fin m))
      (circuitDep D a b c (out rowSlot)) (circuitDep D a b c (out colSlot))

@[simp] theorem circuitGram_apply (D : WeightedDesign m 3) (a b c : Fin m)
    (out : Fin 3 → Fin m) (rowSlot colSlot : Fin 3) :
    circuitGram D a b c out rowSlot colSlot
      = depCross D ({a, b, c} : Finset (Fin m))
          (circuitDep D a b c (out rowSlot)) (circuitDep D a b c (out colSlot)) := rfl

theorem circuitGram_transpose (D : WeightedDesign m 3) (a b c : Fin m) (out : Fin 3 → Fin m) :
    (circuitGram D a b c out)ᵀ = circuitGram D a b c out := by
  ext rowSlot colSlot
  rw [Matrix.transpose_apply, circuitGram_apply, circuitGram_apply]
  exact depCross_comm D _ _ _

/-- **THE QUADRATIC FORM OF THE CIRCUIT GRAM** is the slack of the corresponding
combination of the three circuits. -/
theorem dotProduct_circuitGram_mulVec (D : WeightedDesign m 3) (a b c : Fin m)
    (out : Fin 3 → Fin m) (coord : Fin 3 → ℝ) :
    coord ⬝ᵥ (circuitGram D a b c out *ᵥ coord)
      = depSlack D ({a, b, c} : Finset (Fin m))
          (fun index => coord 0 * circuitDep D a b c (out 0) index
            + coord 1 * circuitDep D a b c (out 1) index
            + coord 2 * circuitDep D a b c (out 2) index) := by
  rw [depSlack_sum_three]
  simp only [dotProduct, Matrix.mulVec, circuitGram_apply, Fin.sum_univ_three,
    depCross_self]
  rw [depCross_comm D _ (circuitDep D a b c (out 1)) (circuitDep D a b c (out 0)),
    depCross_comm D _ (circuitDep D a b c (out 2)) (circuitDep D a b c (out 0)),
    depCross_comm D _ (circuitDep D a b c (out 2)) (circuitDep D a b c (out 1))]
  ring

/-- **A DOMINATOR HAS A POSITIVE SEMIDEFINITE CIRCUIT GRAM.** -/
theorem posSemidef_circuitGram_of_dominates (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (out : Fin 3 → Fin m)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    (circuitGram D a b c out).PosSemidef := by
  classical
  set pick : Fin 3 → Fin m := ![a, b, c] with hpick
  have hinj : Function.Injective pick := injective_tripleVec hab hac hbc
  have himage : Finset.image pick Finset.univ = ({a, b, c} : Finset (Fin m)) :=
    image_tripleVec_eq
  have hdom' : Dominates D (Finset.image pick Finset.univ) := by rw [himage]; exact hdom
  have hcrit := (dominates_iff_depSlack_nonneg D hm pick hinj).mp hdom'
  rw [posSemidef_iff_quadForm_nonneg _ (circuitGram_transpose D a b c out)]
  intro coord
  rw [dotProduct_circuitGram_mulVec]
  have hcombo := hcrit _ (sum_smul_three_atom_eq_zero D (coord 0) (coord 1) (coord 2)
    (sum_circuitDep_smul_atom D a b c (out 0)) (sum_circuitDep_smul_atom D a b c (out 1))
    (sum_circuitDep_smul_atom D a b c (out 2)))
  rwa [himage] at hcombo

/-! ### The circuits span, at a dominator -/

/-- **CRAMER, AS AN INDEPENDENCE STATEMENT.**  Three vectors of nonzero bracket
carry no nontrivial relation. -/
theorem circuitCoeffs_eq_zero_of_tripleBracket_ne_zero {leftVec midVec rightVec : Fin 3 → ℝ}
    (hbracket : tripleBracket leftVec midVec rightVec ≠ 0)
    {coeffLeft coeffMid coeffRight : ℝ}
    (hzero : ∀ coord : Fin 3,
      coeffLeft * leftVec coord + coeffMid * midVec coord + coeffRight * rightVec coord = 0) :
    coeffLeft = 0 ∧ coeffMid = 0 ∧ coeffRight = 0 := by
  have hfirst := hzero 0
  have hsecond := hzero 1
  have hthird := hzero 2
  refine ⟨?_, ?_, ?_⟩
  · have hkey : coeffLeft * tripleBracket leftVec midVec rightVec = 0 := by
      simp only [tripleBracket_eq]
      linear_combination (midVec 1 * rightVec 2 - midVec 2 * rightVec 1) * hfirst
        - (midVec 0 * rightVec 2 - midVec 2 * rightVec 0) * hsecond
        + (midVec 0 * rightVec 1 - midVec 1 * rightVec 0) * hthird
    exact (mul_eq_zero.mp hkey).resolve_right hbracket
  · have hkey : coeffMid * tripleBracket leftVec midVec rightVec = 0 := by
      simp only [tripleBracket_eq]
      linear_combination (leftVec 2 * rightVec 1 - leftVec 1 * rightVec 2) * hfirst
        + (leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0) * hsecond
        + (leftVec 1 * rightVec 0 - leftVec 0 * rightVec 1) * hthird
    exact (mul_eq_zero.mp hkey).resolve_right hbracket
  · have hkey : coeffRight * tripleBracket leftVec midVec rightVec = 0 := by
      simp only [tripleBracket_eq]
      linear_combination (leftVec 1 * midVec 2 - leftVec 2 * midVec 1) * hfirst
        + (leftVec 2 * midVec 0 - leftVec 0 * midVec 2) * hsecond
        + (leftVec 0 * midVec 1 - leftVec 1 * midVec 0) * hthird
    exact (mul_eq_zero.mp hkey).resolve_right hbracket

/-- The unweighted sum of three atoms has determinant the squared bracket. -/
theorem det_subsetSum_triple (D : WeightedDesign m 3) {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (subsetSum D ({a, b, c} : Finset (Fin m))).det
      = tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 := by
  classical
  rw [subsetSum, sum_over_triple (fun index => atomMatrix (D.atom index)) hab hac hbc]
  have hone : atomMatrix (D.atom a) + atomMatrix (D.atom b) + atomMatrix (D.atom c)
      = (1 : ℝ) • atomMatrix (D.atom a) + (1 : ℝ) • atomMatrix (D.atom b)
        + (1 : ℝ) • atomMatrix (D.atom c) := by
    simp only [one_smul]
  rw [hone, det_smul_atomMatrix_three]
  ring

/-- **A DOMINATOR HAS A NONZERO BRACKET.**  Its gap is positive semidefinite, so
the unweighted sum is positive definite, so its determinant is positive. -/
theorem tripleBracket_ne_zero_of_dominates (D : WeightedDesign m 3) {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdom : Dominates D ({a, b, c} : Finset (Fin m))) :
    tripleBracket (D.atom a) (D.atom b) (D.atom c) ≠ 0 := by
  have hposDef : (subsetSum D ({a, b, c} : Finset (Fin m))).PosDef := by
    have hsum : (1 : Matrix (Fin 3) (Fin 3) ℝ) + (subsetSum D ({a, b, c} : Finset (Fin m)) - 1)
        = subsetSum D ({a, b, c} : Finset (Fin m)) := by
      rw [add_sub_cancel]
    rw [← hsum]
    exact Matrix.PosDef.add_posSemidef Matrix.PosDef.one hdom
  have hdet := hposDef.det_pos
  rw [det_subsetSum_triple D hab hac hbc] at hdet
  intro hzero
  rw [hzero] at hdet
  norm_num at hdet

/-- Six distinct labels of `Fin 6` enumerate their own sum. -/
theorem sum_over_six {carrier : Type*} [AddCommMonoid carrier] (summand : Fin 6 → carrier)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    (∑ index, summand index)
      = summand a + summand b + summand c + summand d + summand e + summand f := by
  have hbij : Function.Bijective (![a, b, c, d, e, f] : Fin 6 → Fin 6) :=
    bijective_six hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  have hre : (∑ index : Fin 6, summand index)
      = ∑ slot : Fin 6, summand ((![a, b, c, d, e, f] : Fin 6 → Fin 6) slot) :=
    (Fintype.sum_bijective _ hbij _ _ fun _ => rfl).symm
  rw [hre, Fin.sum_univ_six]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  have hlast : (![a, b, c, d, e, f] : Fin 6 → Fin 6) 5 = f := rfl
  rw [hlast]

/-- **THE CIRCUITS SPAN, AT `(6,3)`.**  Every dependency is the combination of
the three circuits whose coefficients its own outside coordinates supply. -/
theorem dependency_eq_circuit_combination_sixThree (D : WeightedDesign 6 3)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e)
    (haf : a ≠ f) (hbf : b ≠ f) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hbracket : tripleBracket (D.atom a) (D.atom b) (D.atom c) ≠ 0)
    {dep : Fin 6 → ℝ} (hdep : (∑ index, dep index • D.atom index) = 0) :
    dep = fun index =>
      (-(dep d) / tripleBracket (D.atom a) (D.atom b) (D.atom c))
          * circuitDep D a b c d index
        + (-(dep e) / tripleBracket (D.atom a) (D.atom b) (D.atom c))
          * circuitDep D a b c e index
        + (-(dep f) / tripleBracket (D.atom a) (D.atom b) (D.atom c))
          * circuitDep D a b c f index := by
  classical
  set combo : Fin 6 → ℝ := fun index =>
    (-(dep d) / tripleBracket (D.atom a) (D.atom b) (D.atom c)) * circuitDep D a b c d index
      + (-(dep e) / tripleBracket (D.atom a) (D.atom b) (D.atom c)) * circuitDep D a b c e index
      + (-(dep f) / tripleBracket (D.atom a) (D.atom b) (D.atom c)) * circuitDep D a b c f index
    with hcombo
  set res : Fin 6 → ℝ := fun index => dep index - combo index with hres
  have hcomboDep : (∑ index, combo index • D.atom index) = 0 := by
    rw [hcombo]
    exact sum_smul_three_atom_eq_zero D _ _ _ (sum_circuitDep_smul_atom D a b c d)
      (sum_circuitDep_smul_atom D a b c e) (sum_circuitDep_smul_atom D a b c f)
  have hresDep : (∑ index, res index • D.atom index) = 0 := by
    have hsplit : ∀ index : Fin 6,
        res index • D.atom index = dep index • D.atom index - combo index • D.atom index := by
      intro index
      simp only [hres, sub_smul]
    rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hsplit index,
      Finset.sum_sub_distrib, hdep, hcomboDep, sub_zero]
  have hresD : res d = 0 := by
    simp only [hres, hcombo, circuitDep_apply_fourth D had hbd hcd,
      circuitDep_apply_of_notMem D (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hde,
      circuitDep_apply_of_notMem D (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hdf]
    field_simp
    ring
  have hresE : res e = 0 := by
    simp only [hres, hcombo, circuitDep_apply_fourth D hae hbe hce,
      circuitDep_apply_of_notMem D (Ne.symm hae) (Ne.symm hbe) (Ne.symm hce) (Ne.symm hde),
      circuitDep_apply_of_notMem D (Ne.symm hae) (Ne.symm hbe) (Ne.symm hce) hef]
    field_simp
    ring
  have hresF : res f = 0 := by
    simp only [hres, hcombo, circuitDep_apply_fourth D haf hbf hcf,
      circuitDep_apply_of_notMem D (Ne.symm haf) (Ne.symm hbf) (Ne.symm hcf) (Ne.symm hdf),
      circuitDep_apply_of_notMem D (Ne.symm haf) (Ne.symm hbf) (Ne.symm hcf) (Ne.symm hef)]
    field_simp
    ring
  have hrelation : ∀ coord : Fin 3,
      res a * D.atom a coord + res b * D.atom b coord + res c * D.atom c coord = 0 := by
    intro coord
    have hsum := congrFun hresDep coord
    rw [Finset.sum_apply] at hsum
    have hterm : ∀ index : Fin 6, (res index • D.atom index) coord
        = res index * D.atom index coord := fun index => rfl
    rw [Finset.sum_congr rfl fun index (_ : index ∈ Finset.univ) => hterm index,
      sum_over_six (fun index => res index * D.atom index coord) hab hac had hae haf
        hbc hbd hbe hbf hcd hce hcf hde hdf hef, hresD, hresE, hresF] at hsum
    have hzero : (0 : Fin 3 → ℝ) coord = 0 := rfl
    rw [hzero] at hsum
    linarith
  obtain ⟨hra, hrb, hrc⟩ :=
    circuitCoeffs_eq_zero_of_tripleBracket_ne_zero hbracket hrelation
  have huniv : ∀ probe : Fin 6, probe = a ∨ probe = b ∨ probe = c ∨ probe = d ∨ probe = e
      ∨ probe = f := by
    intro probe
    have hbij : Function.Bijective (![a, b, c, d, e, f] : Fin 6 → Fin 6) :=
      bijective_six hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
    obtain ⟨slot, hslot⟩ := hbij.2 probe
    fin_cases slot
    · exact Or.inl hslot.symm
    · exact Or.inr (Or.inl hslot.symm)
    · exact Or.inr (Or.inr (Or.inl hslot.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hslot.symm)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hslot.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hslot.symm))))
  have hall : ∀ index : Fin 6, res index = 0 := by
    intro index
    rcases huniv index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hra
    · exact hrb
    · exact hrc
    · exact hresD
    · exact hresE
    · exact hresF
  funext index
  have hpoint := hall index
  simp only [hres] at hpoint
  simp only [hcombo] at hpoint ⊢
  linarith

/-- **THE CIRCUIT GRAM IS THE CRITERION, AT `(6,3)`.**  Domination of a triple is
exactly the positive semidefiniteness of ONE explicit symmetric `3 x 3` matrix in
the brackets and the weights. -/
theorem dominates_iff_posSemidef_circuitGram_sixThree (D : WeightedDesign 6 3)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e)
    (haf : a ≠ f) (hbf : b ≠ f) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hbracket : tripleBracket (D.atom a) (D.atom b) (D.atom c) ≠ 0) :
    Dominates D ({a, b, c} : Finset (Fin 6))
      ↔ (circuitGram D a b c ![d, e, f]).PosSemidef := by
  classical
  constructor
  · intro hdom
    exact posSemidef_circuitGram_of_dominates D (by norm_num) hab hac hbc _ hdom
  · intro hpsd
    set pick : Fin 3 → Fin 6 := ![a, b, c] with hpick
    have hinj : Function.Injective pick := injective_tripleVec hab hac hbc
    have himage : Finset.image pick Finset.univ = ({a, b, c} : Finset (Fin 6)) :=
      image_tripleVec_eq
    have hstep : Dominates D (Finset.image pick Finset.univ) := by
      rw [dominates_iff_depSlack_nonneg D (by norm_num) pick hinj]
      intro dep hdep
      have hexpand := dependency_eq_circuit_combination_sixThree D hab hac hbc had hbd hcd
        hae hbe hce haf hbf hcf hde hdf hef hbracket hdep
      have hquad := (posSemidef_iff_quadForm_nonneg _
        (circuitGram_transpose D a b c ![d, e, f])).mp hpsd
        ![-(dep d) / tripleBracket (D.atom a) (D.atom b) (D.atom c),
          -(dep e) / tripleBracket (D.atom a) (D.atom b) (D.atom c),
          -(dep f) / tripleBracket (D.atom a) (D.atom b) (D.atom c)]
      rw [dotProduct_circuitGram_mulVec] at hquad
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hquad
      have hcongr := congrArg (depSlack D ({a, b, c} : Finset (Fin 6))) hexpand
      rw [himage, hcongr]
      exact hquad
    rwa [himage] at hstep

/-- **THE STRICT CIRCUIT GRAM CRITERION AT `(6,3)`.** -/
theorem posDef_gap_iff_posDef_circuitGram_sixThree (D : WeightedDesign 6 3)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e)
    (haf : a ≠ f) (hbf : b ≠ f) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hbracket : tripleBracket (D.atom a) (D.atom b) (D.atom c) ≠ 0) :
    (subsetSum D ({a, b, c} : Finset (Fin 6)) - 1).PosDef
      ↔ (circuitGram D a b c ![d, e, f]).PosDef := by
  classical
  set pick : Fin 3 → Fin 6 := ![a, b, c] with hpick
  have hinj : Function.Injective pick := injective_tripleVec hab hac hbc
  have himage : Finset.image pick Finset.univ = ({a, b, c} : Finset (Fin 6)) :=
    image_tripleVec_eq
  constructor
  · intro hstrict
    rw [posDef_iff_quadForm_pos _ (circuitGram_transpose D a b c ![d, e, f])]
    intro coord hne
    rw [dotProduct_circuitGram_mulVec]
    have hstrict' : (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
      rw [himage]; exact hstrict
    have hcrit := (posDef_gap_iff_depSlack_pos D (by norm_num) pick hinj).mp hstrict'
    have hdepNe : (fun index => coord 0 * circuitDep D a b c d index
        + coord 1 * circuitDep D a b c e index + coord 2 * circuitDep D a b c f index) ≠ 0 := by
      intro hzero
      have hbrNe := hbracket
      have hd : coord 0 * (-(tripleBracket (D.atom a) (D.atom b) (D.atom c))) = 0 := by
        have hval := congrFun hzero d
        rw [circuitDep_apply_fourth D had hbd hcd,
          circuitDep_apply_of_notMem D (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hde,
          circuitDep_apply_of_notMem D (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hdf]
          at hval
        simpa using hval
      have he : coord 1 * (-(tripleBracket (D.atom a) (D.atom b) (D.atom c))) = 0 := by
        have hval := congrFun hzero e
        rw [circuitDep_apply_fourth D hae hbe hce,
          circuitDep_apply_of_notMem D (Ne.symm hae) (Ne.symm hbe) (Ne.symm hce) (Ne.symm hde),
          circuitDep_apply_of_notMem D (Ne.symm hae) (Ne.symm hbe) (Ne.symm hce) hef]
          at hval
        simpa using hval
      have hf : coord 2 * (-(tripleBracket (D.atom a) (D.atom b) (D.atom c))) = 0 := by
        have hval := congrFun hzero f
        rw [circuitDep_apply_fourth D haf hbf hcf,
          circuitDep_apply_of_notMem D (Ne.symm haf) (Ne.symm hbf) (Ne.symm hcf) (Ne.symm hdf),
          circuitDep_apply_of_notMem D (Ne.symm haf) (Ne.symm hbf) (Ne.symm hcf) (Ne.symm hef)]
          at hval
        simpa using hval
      have hneg : -(tripleBracket (D.atom a) (D.atom b) (D.atom c)) ≠ 0 := neg_ne_zero.mpr hbrNe
      refine hne (funext fun slot => ?_)
      fin_cases slot
      · exact (mul_eq_zero.mp hd).resolve_right hneg
      · exact (mul_eq_zero.mp he).resolve_right hneg
      · exact (mul_eq_zero.mp hf).resolve_right hneg
    have hvalue := hcrit _ hdepNe (sum_smul_three_atom_eq_zero D (coord 0) (coord 1) (coord 2)
      (sum_circuitDep_smul_atom D a b c d) (sum_circuitDep_smul_atom D a b c e)
      (sum_circuitDep_smul_atom D a b c f))
    rwa [himage] at hvalue
  · intro hposDef
    have hstep : (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef := by
      rw [posDef_gap_iff_depSlack_pos D (by norm_num) pick hinj]
      intro dep hne hdep
      have hexpand := dependency_eq_circuit_combination_sixThree D hab hac hbc had hbd hcd
        hae hbe hce haf hbf hcf hde hdf hef hbracket hdep
      have hcoordNe : (![-(dep d) / tripleBracket (D.atom a) (D.atom b) (D.atom c),
          -(dep e) / tripleBracket (D.atom a) (D.atom b) (D.atom c),
          -(dep f) / tripleBracket (D.atom a) (D.atom b) (D.atom c)] : Fin 3 → ℝ) ≠ 0 := by
        intro hzero
        refine hne ?_
        rw [hexpand]
        funext index
        have hd : -(dep d) / tripleBracket (D.atom a) (D.atom b) (D.atom c) = 0 := by
          simpa using congrFun hzero 0
        have he : -(dep e) / tripleBracket (D.atom a) (D.atom b) (D.atom c) = 0 := by
          simpa using congrFun hzero 1
        have hf : -(dep f) / tripleBracket (D.atom a) (D.atom b) (D.atom c) = 0 := by
          simpa using congrFun hzero 2
        rw [hd, he, hf]
        simp
      have hquad := (posDef_iff_quadForm_pos _
        (circuitGram_transpose D a b c ![d, e, f])).mp hposDef _ hcoordNe
      rw [dotProduct_circuitGram_mulVec] at hquad
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at hquad
      have hcongr := congrArg (depSlack D ({a, b, c} : Finset (Fin 6))) hexpand
      rw [himage, hcongr]
      exact hquad
    rwa [himage] at hstep

/-- **AT A TIE THE CIRCUIT GRAM OF EVERY DOMINATOR IS SINGULAR.** -/
theorem det_circuitGram_eq_zero_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e)
    (haf : a ≠ f) (hbf : b ≠ f) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hdom : Dominates D ({a, b, c} : Finset (Fin 6))) :
    (circuitGram D a b c ![d, e, f]).det = 0 := by
  classical
  have hbracket := tripleBracket_ne_zero_of_dominates D hab hac hbc hdom
  have hpsd := posSemidef_circuitGram_of_dominates D (by norm_num) hab hac hbc ![d, e, f] hdom
  have hcard : ({a, b, c} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hnotStrict := htie.2 ({a, b, c} : Finset (Fin 6)) hcard
  by_contra hne
  refine hnotStrict ?_
  rw [posDef_gap_iff_posDef_circuitGram_sixThree D hab hac hbc had hbd hcd hae hbe hce
    haf hbf hcf hde hdf hef hbracket]
  exact hpsd.posDef_iff_det_ne_zero.mpr hne

/-- **THE TIE RELATION AMONG THE THREE SWAP SLACKS AND THE THREE CROSS TERMS.**
Writing the circuit Gram out, the vanishing determinant is one explicit
polynomial equation.  Its three diagonal entries are the slacks of the landed
swap law and its three off-diagonal entries are the two-circuit cross terms. -/
theorem circuitGram_determinant_relation_of_isTie_sixThree (D : WeightedDesign 6 3)
    (htie : IsTie D) {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hae : a ≠ e) (hbe : b ≠ e) (hce : c ≠ e)
    (haf : a ≠ f) (hbf : b ≠ f) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hdom : Dominates D ({a, b, c} : Finset (Fin 6))) :
    depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c d)
        * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c e)
        * depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c f)
      + 2 * (depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c d) (circuitDep D a b c e)
            * depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c d) (circuitDep D a b c f)
            * depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c e) (circuitDep D a b c f))
      = depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c d)
            * depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c e) (circuitDep D a b c f) ^ 2
        + depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c e)
            * depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c d) (circuitDep D a b c f) ^ 2
        + depSlack D ({a, b, c} : Finset (Fin 6)) (circuitDep D a b c f)
            * depCross D ({a, b, c} : Finset (Fin 6))
              (circuitDep D a b c d) (circuitDep D a b c e) ^ 2 := by
  have hdet := det_circuitGram_eq_zero_of_isTie_sixThree D htie hab hac hbc had hbd hcd
    hae hbe hce haf hbf hcf hde hdf hef hdom
  rw [Matrix.det_fin_three] at hdet
  simp only [circuitGram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, depCross_self] at hdet
  rw [depCross_comm D _ (circuitDep D a b c e) (circuitDep D a b c d),
    depCross_comm D _ (circuitDep D a b c f) (circuitDep D a b c d),
    depCross_comm D _ (circuitDep D a b c f) (circuitDep D a b c e)] at hdet
  nlinarith [hdet]

end Gtz

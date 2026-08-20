import Gtz.Wave.OppositeHornBudget
import Gtz.Wave.TripleInvariantLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The sign split of the opposite horn, and the refusal scalarisation

Three independent sharpenings of the corank-two corner.

**1. The sign trichotomy.**  At a bracket-generic outside atom the three
signed base readings

  `α_d = P_yz·M^x_d` ,  `β_d = P_xz·M^y_d` ,  `γ_d = P_xy·M^z_d`

multiply to `−(P_xyP_xzP_yz)·T_d²`, a STRICTLY negative number
(`corner_atom_signTriple_neg`).  So an ODD number of the three readings is
negative: every generic outside atom disagrees with its own pairing at one or
at all three bases.  This is the master sign law of the corner; the landed
dichotomy and the two-coherent count of `Gtz.OppositeHornCount` are its two
aggregate corollaries.  In the residual stratum — exactly one coherent base —
it collapses completely: every generic atom then disagrees at EXACTLY ONE of
the two remaining bases (`corner_coherentBase_atom_alternates`).

**2. The two-point bracket form.**  The landed bridge reads the informative
bracket as a `2×2` minor, `(1+λ)[x d d']² = (a − b)²` with
`a = [xyd][xzd']`, `b = [xyd'][xzd]`, `ab = M^x_d·M^x_{d'}`.  Over `ℝ` the
product `ab` HAS A SIGN, so the bracket is pinned to a TWO-POINT set:

  `ab < 0  ⟹  (1+λ)[x d d']² = (|a| + |b|)²`   (`corner_oppositePair_bracket_exact`)
  `0 < ab  ⟹  (1+λ)[x d d']² = (|a| − |b|)²`   (`corner_samePair_bracket_exact`)

Over `ℂ` only the interval between those two values is available.  The landed
`Gtz.corner_oppositePair_bracket_floor` is the AM–GM weakening
`(|a|+|b|)² ≥ 4|ab|` of the first line; keeping the exact form gives the
STRICTLY sharper budget bound `corner_oppositePair_budget_sharp`, which adds
`a² + b²` on top of the landed `4|ab|`.

**3. The refusal scalarisation.**  A refused triple is a triple whose gap fails
one of the three characteristic invariants
(`refused_triple_invariant_trichotomy`), through the landed exact criterion
`Gtz.posDef_iff_invariants_pos`.  Together with the ledger

  `[p l r]² = 1 + gapTrace + gapSecond + gapDet`   (`atomBracket_sq_eq_gap_invariants`)

every refusal becomes a CAP on the squared bracket of its triple
(`isTie_bracket_invariant_cap`).  That is the upper half the exact budget of
`Gtz.OppositeHornBudget` has been waiting for, and it is stated for every
design and every triple, not only at a corner.

**4. The bracket partition.**  Finally, the twenty triples of a corner split
into four channels whose closed forms total the whole unit bracket budget
(`corner_bracket_partition`).  Consequence, recorded honestly: the sibling
`Gtz.bracket_budget` is IDENTICALLY satisfied at a corner once the heavy
excesses sum to the scale, so it carries no information there.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The sign trichotomy at an outside atom -/

/-- **THE SIGN TRICHOTOMY.**  At a corank-two corner with nondegenerate inside
pairings, the three signed base readings of a bracket-generic outside atom
multiply to a strictly negative number.  An odd number of them is negative. -/
theorem corner_atom_signTriple_neg (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    {d : Fin m}
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
        * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
          * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d)))
      < 0 := by
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hx : x ∈ C := by rw [hC]; simp
  have hy : y ∈ C := by rw [hC]; simp
  have hz : z ∈ C := by rw [hC]; simp
  have hP := corner_inside_tripleProduct_nonneg D C hcard hlam hunit hgap
    hx hy hz hxy hxz hyz
  have hPne : atomPairing D x y * atomPairing D x z * atomPairing D y z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hPxy hPxz) hPyz
  have hPpos : 0 < atomPairing D x y * atomPairing D x z * atomPairing D y z :=
    lt_of_le_of_ne hP (Ne.symm hPne)
  have hTsq : 0 < (atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d) ^ 2 := by
    rcases lt_or_gt_of_ne hT with h | h
    · nlinarith
    · nlinarith
  have hprod : (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
      * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
        * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d)))
      = -((atomPairing D x y * atomPairing D x z * atomPairing D y z)
        * (atomBracket D x y d * atomBracket D x z d
          * atomBracket D y z d) ^ 2) := by
    have hcyc := atomBracket_baseProduct_cycle D x y z d
    linear_combination (atomPairing D x y * atomPairing D x z
      * atomPairing D y z) * hcyc
  rw [hprod]
  nlinarith [hPpos, hTsq]

/-- **THE RESIDUAL STRATUM IS RIGID.**  If one inside base is coherent, every
bracket-generic outside atom disagrees at EXACTLY ONE of the two other bases:
the two remaining signed readings have strictly opposite signs. -/
theorem corner_coherentBase_atom_alternates (D : WeightedDesign m 3)
    (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d'))
    {d : Fin m} (hd : d ∈ Cᶜ)
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
        * (atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
      < 0 := by
  have hCz : C = ({z, x, y} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have htZ := corner_compl_bracket_transport D C hlam hunit hgap hCz
    (Ne.symm hxz) (Ne.symm hyz) hxy
  have hw : ∀ a ∈ Cᶜ, 0 < D.weight a := fun a _ => D.weight_pos a
  have hsZ := sum_sign_forced_of_pairwise_nonneg hw hbaseZ htZ hPxy d hd
  have htri := corner_atom_signTriple_neg D C hlam hunit hgap hC hxy hxz hyz
    hPyz hPxz hPxy hT
  by_contra hge
  push Not at hge
  have hnn := mul_nonneg hge hsZ
  have heq : ((atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
        * (atomPairing D x z * (atomBracket D y x d * atomBracket D y z d)))
      * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d))
      = (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
        * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
          * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d))) := by
    ring
  rw [heq] at hnn
  linarith [htri, hnn]

/-- A disagreeing atom and an agreeing atom form an opposite-sign pair at the
base, so the landed floor fires on them. -/
theorem corner_disagree_agree_oppositePair (D : WeightedDesign m 3)
    {x y z : Fin m} {d d' : Fin m}
    (hdis : atomPairing D y z * (atomBracket D x y d * atomBracket D x z d) < 0)
    (hagr : 0 < atomPairing D y z
      * (atomBracket D x y d' * atomBracket D x z d')) :
    (atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d') < 0 := by
  nlinarith [hdis, hagr, sq_nonneg (atomPairing D y z)]

/-! ## 2. The two-point form of the informative bracket -/

/-- **THE OPPOSITE-PAIR BRACKET, EXACTLY.**  On an opposite-sign pair the
informative bracket is the SUM of the two cross magnitudes, squared. -/
theorem corner_oppositePair_bracket_exact (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    {d d' : Fin m}
    (hsign : (atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d') < 0) :
    (1 + lam) * atomBracket D x d d' ^ 2
      = (|atomBracket D x y d * atomBracket D x z d'|
        + |atomBracket D x y d' * atomBracket D x z d|) ^ 2 := by
  have hbridge := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap d d'
  have hprod : (atomBracket D x y d * atomBracket D x z d')
      * (atomBracket D x y d' * atomBracket D x z d)
      = (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d') := by ring
  have hneg : (atomBracket D x y d * atomBracket D x z d')
      * (atomBracket D x y d' * atomBracket D x z d) < 0 := by
    rw [hprod]; exact hsign
  have habs : |(atomBracket D x y d * atomBracket D x z d')
      * (atomBracket D x y d' * atomBracket D x z d)|
      = -((atomBracket D x y d * atomBracket D x z d')
        * (atomBracket D x y d' * atomBracket D x z d)) := abs_of_neg hneg
  rw [abs_mul] at habs
  rw [hbridge]
  nlinarith [habs, sq_abs (atomBracket D x y d * atomBracket D x z d'),
    sq_abs (atomBracket D x y d' * atomBracket D x z d)]

/-- **THE SAME-SIGN PAIR BRACKET, EXACTLY.**  On a same-sign pair the
informative bracket is the DIFFERENCE of the two cross magnitudes, squared.
The two statements together pin the bracket of a real corner to a two-point
set; over `ℂ` only the interval between them is available. -/
theorem corner_samePair_bracket_exact (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    {d d' : Fin m}
    (hsign : 0 < (atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d')) :
    (1 + lam) * atomBracket D x d d' ^ 2
      = (|atomBracket D x y d * atomBracket D x z d'|
        - |atomBracket D x y d' * atomBracket D x z d|) ^ 2 := by
  have hbridge := corner_bracket_bridge D hxy hxz hyz hlam hunit hgap d d'
  have hprod : (atomBracket D x y d * atomBracket D x z d')
      * (atomBracket D x y d' * atomBracket D x z d)
      = (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d') := by ring
  have hpos : 0 < (atomBracket D x y d * atomBracket D x z d')
      * (atomBracket D x y d' * atomBracket D x z d) := by
    rw [hprod]; exact hsign
  have habs : |(atomBracket D x y d * atomBracket D x z d')
      * (atomBracket D x y d' * atomBracket D x z d)|
      = (atomBracket D x y d * atomBracket D x z d')
        * (atomBracket D x y d' * atomBracket D x z d) := abs_of_pos hpos
  rw [abs_mul] at habs
  rw [hbridge]
  nlinarith [habs, sq_abs (atomBracket D x y d * atomBracket D x z d'),
    sq_abs (atomBracket D x y d' * atomBracket D x z d)]

/-- **THE SHARPENED FLOOR–BUDGET COLLISION.**  Keeping the exact two-point form
instead of its AM–GM weakening adds the two squared cross magnitudes on top of
the landed four-times-product floor:

  `t_dt_{d'}·(a² + b² + 2|ab|) ≤ A_xy·A_xz − e_ye_z` .

The landed `Gtz.corner_oppositePair_budget_bound` is the `2|ab| + 2|ab|` part
of the same left side. -/
theorem corner_oppositePair_budget_sharp (D : WeightedDesign 6 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    {x y z d4 d5 d6 : Fin 6}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ) = {d4, d5, d6})
    (hsign : (atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d5 * atomBracket D x z d5) < 0) :
    D.weight d4 * D.weight d5
        * ((atomBracket D x y d4 * atomBracket D x z d5) ^ 2
          + (atomBracket D x y d5 * atomBracket D x z d4) ^ 2
          + 2 * |(atomBracket D x y d4 * atomBracket D x z d5)
            * (atomBracket D x y d5 * atomBracket D x z d4)|)
      ≤ (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
          * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        - heavyExcess D y * heavyExcess D z := by
  have hexact := corner_oppositePair_bracket_exact D hxy hxz hyz hlam hunit hgap
    hsign
  have hpair := corner_informative_pair_le_budget D hlam hunit hgap hxy hxz hyz
    h45 h46 h56 hcompl
  have hw : 0 < D.weight d4 * D.weight d5 :=
    mul_pos (D.weight_pos d4) (D.weight_pos d5)
  have hexpand : (|atomBracket D x y d4 * atomBracket D x z d5|
        + |atomBracket D x y d5 * atomBracket D x z d4|) ^ 2
      = (atomBracket D x y d4 * atomBracket D x z d5) ^ 2
        + (atomBracket D x y d5 * atomBracket D x z d4) ^ 2
        + 2 * |(atomBracket D x y d4 * atomBracket D x z d5)
          * (atomBracket D x y d5 * atomBracket D x z d4)| := by
    linear_combination sq_abs (atomBracket D x y d4 * atomBracket D x z d5)
      + sq_abs (atomBracket D x y d5 * atomBracket D x z d4)
      - 2 * abs_mul (atomBracket D x y d4 * atomBracket D x z d5)
        (atomBracket D x y d5 * atomBracket D x z d4)
  rw [← hexpand]
  nlinarith [hexact, hpair, hw]

/-! ## 3. The refusal scalarisation -/

/-- **THE INVARIANT LEDGER OF A TRIPLE.**  The squared bracket of a triple is
one plus the three characteristic invariants of its gap. -/
theorem atomBracket_sq_eq_gap_invariants (D : WeightedDesign m 3)
    (p l r : Fin m) :
    atomBracket D p l r ^ 2
      = 1 + gapTraceAt D p l r + gapSecondAt D p l r + gapDetAt D p l r := by
  simp only [gapTraceAt, gapSecondAt, gapDetAt, atomBracket]
  ring

/-- **THE REFUSAL TRICHOTOMY.**  A triple whose gap is not positive definite
fails one of the three characteristic invariants.  This scalarises every
refusal of the campaign: no matrix, no eigenvalue, three polynomials. -/
theorem refused_triple_invariant_trichotomy (D : WeightedDesign m 3)
    {p l r : Fin m} (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (href : ¬ (subsetSum D ({p, l, r} : Finset (Fin m)) - 1).PosDef) :
    gapTraceAt D p l r ≤ 0 ∨ gapSecondAt D p l r ≤ 0
      ∨ gapDetAt D p l r ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨htr, hsec, hdet⟩ := hcon
  refine href ?_
  have hherm : (subsetSum D ({p, l, r} : Finset (Fin m)) - 1).IsHermitian :=
    isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _)
  refine (posDef_iff_invariants_pos hherm).mpr ⟨?_, ?_, ?_⟩
  · rw [trace_subsetSum_triple_sub_one D hpl hpr hlr]; exact htr
  · rw [secondInvariantOfThree_subsetSum_triple_sub_one D hpl hpr hlr]
    exact hsec
  · rw [det_subsetSum_triple_sub_one_eq_gapDetAt D hpl hpr hlr]; exact hdet

/-- **EVERY TRIPLE OF A TIE FAILS AN INVARIANT.**  The tie hypothesis is
exactly the refusal of every triple, so the trichotomy holds at all of them. -/
theorem isTie_triple_invariant_trichotomy (D : WeightedDesign m 3)
    (htie : IsTie D) {p l r : Fin m} (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r) :
    gapTraceAt D p l r ≤ 0 ∨ gapSecondAt D p l r ≤ 0
      ∨ gapDetAt D p l r ≤ 0 :=
  refused_triple_invariant_trichotomy D hpl hpr hlr
    (htie.2 _ (card_triple_eq hpl hpr hlr))

/-- **THE REFUSAL BRACKET CAP.**  At a tie the squared bracket of every triple
is capped by one plus the sum of the two invariants that survive: the failing
invariant may be dropped from the ledger.

This is the upper half that the exact informative bracket budget of
`Gtz.OppositeHornBudget` collides with — the budget fixes the total weighted
bracket mass of a base from BELOW, and each refusal caps its own triple from
ABOVE. -/
theorem isTie_bracket_invariant_cap (D : WeightedDesign m 3) (htie : IsTie D)
    {p l r : Fin m} (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r) :
    atomBracket D p l r ^ 2 ≤ 1 + gapTraceAt D p l r + gapSecondAt D p l r
      ∨ atomBracket D p l r ^ 2 ≤ 1 + gapTraceAt D p l r + gapDetAt D p l r
      ∨ atomBracket D p l r ^ 2 ≤ 1 + gapSecondAt D p l r + gapDetAt D p l r := by
  have hledger := atomBracket_sq_eq_gap_invariants D p l r
  rcases isTie_triple_invariant_trichotomy D htie hpl hpr hlr with
    htr | hsec | hdet
  · exact Or.inr (Or.inr (by linarith [hledger, htr]))
  · exact Or.inr (Or.inl (by linarith [hledger, hsec]))
  · exact Or.inl (by linarith [hledger, hdet])

/-! ## 4. The bracket partition of a corner -/

/-- **THE BRACKET PARTITION OF A CORNER.**  The twenty triples of a `(6,3)`
corner split into four channels — the dominator, the nine two-inside triples,
the nine informative triples and the complement — whose closed forms total the
whole unit bracket budget, scaled by `(1+λ)²`.

Written with `A_ef = 1 + e_e + e_f − t_g(1+λ)`, the identity is a consequence
of the heavy-excess sum alone: substituting `λ = e_x + e_y + e_z` makes it a
polynomial identity.  Read against the sibling `Gtz.bracket_budget`, whose
total is exactly one, this says the GLOBAL bracket budget carries NO
information at a corner beyond `Gtz.corner_heavyExcess_sum`. -/
theorem corner_bracket_partition (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (1 + lam) ^ 2 * (D.weight x * D.weight y * D.weight z * (1 + lam)
        + D.weight x * D.weight y
          * (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
        + D.weight x * D.weight z
          * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
        + D.weight y * D.weight z
          * (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam)))
      + (1 + lam) * (D.weight x
            * ((1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
                * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
              - heavyExcess D y * heavyExcess D z)
          + D.weight y
            * ((1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
                * (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
              - heavyExcess D x * heavyExcess D z)
          + D.weight z
            * ((1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
                * (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
              - heavyExcess D x * heavyExcess D y))
      + ((1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
            * (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
            * (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
          - 2 * (heavyExcess D x * heavyExcess D y * heavyExcess D z)
          - (1 + heavyExcess D x + heavyExcess D y - D.weight z * (1 + lam))
            * (heavyExcess D x * heavyExcess D y)
          - (1 + heavyExcess D x + heavyExcess D z - D.weight y * (1 + lam))
            * (heavyExcess D x * heavyExcess D z)
          - (1 + heavyExcess D y + heavyExcess D z - D.weight x * (1 + lam))
            * (heavyExcess D y * heavyExcess D z))
      = (1 + lam) ^ 2 := by
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hsum : heavyExcess D x + heavyExcess D y + heavyExcess D z = lam := by
    have h := corner_heavyExcess_sum D C hcard hlam hunit hgap
    rw [hC, sum_triple_eq hxy hxz hyz] at h
    linarith [h]
  rw [← hsum]
  ring

/-! ## 5. The inside wedges of a corner -/

/-- **THE INSIDE WEDGE OF A CORNER.**  The sibling `Gtz.pair_bracket_mass` reads
the bracket mass of a pair as its wedge.  At a corank-two corner that wedge is
pinned by the two heavy excesses:

  `ℓ_xℓ_y − P_xy² = 1 + e_x + e_y` .

The rank-one gap makes the pair minor of the excesses vanish, and the wedge
collapses onto their sum. -/
theorem corner_inside_pair_wedge_eq (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    leverageOf (D.atom e) * leverageOf (D.atom f) - atomPairing D e f ^ 2
      = 1 + heavyExcess D e + heavyExcess D f := by
  have hminor := corner_inside_pairMinor_eq_zero D C hcard hlam hunit hgap he hf hef
  have hle : leverageOf (D.atom e) = 1 + heavyExcess D e := by
    simp only [heavyExcess]; ring
  have hlf : leverageOf (D.atom f) = 1 + heavyExcess D f := by
    simp only [heavyExcess]; ring
  rw [hle, hlf]
  linear_combination hminor

/-- **A CORNER HAS NO PARALLEL INSIDE PAIR.**  Every inside wedge of a
corank-two corner is at least one, because the heavy excesses are nonnegative.
Primitivity of the dominator is FREE at a corner: the hinge's conclusion can
never be found inside it. -/
theorem corner_one_le_inside_pair_wedge (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    1 ≤ leverageOf (D.atom e) * leverageOf (D.atom f) - atomPairing D e f ^ 2 := by
  have hwedge := corner_inside_pair_wedge_eq D C hcard hlam hunit hgap he hf hef
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hee := corner_heavyExcess_axis D C hcard hlam hunit hgap he
  have hef' := corner_heavyExcess_axis D C hcard hlam hunit hgap hf
  have h1 : 0 ≤ heavyExcess D e := by
    nlinarith [hee, sq_nonneg (D.atom e ⬝ᵥ u), hlam, hpos]
  have h2 : 0 ≤ heavyExcess D f := by
    nlinarith [hef', sq_nonneg (D.atom f ⬝ᵥ u), hlam, hpos]
  linarith [hwedge, h1, h2]

end Gtz

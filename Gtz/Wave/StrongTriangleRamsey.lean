/-
# The strong triangle: why branch B needs SIX atoms, and what six forces

Branch B is the case of the `(6,3)` hinge in which every atom is strictly heavy and every
pair is admissible.  It is the case with no witness to point at, because a parallel pair is
never admissible, so a branch-B design carries none and the hinge's conclusion must be
reached by contradiction.

Two things landed on the same day make that possible, and this module composes them.

## The analytic half

`Gtz.branchB_exists_strongPair` reads a PAIR inequality out of the sign of a triple's gap
determinant: at a branch-B tie every triple `{x,y,z}` has a pair whose squared pairing
clears a quarter of the product of its two excesses,

  `x_i * x_j ≤ 4 * ⟨g_i,g_j⟩²` ,   with `x_c = ℓ_c - 1` .

Call such a pair STRONG.  The constant is sharp at the regular tetrahedron.  This is the
step the campaign's graph programme was always missing: at a tie every live triple has
nonpositive gap determinant BY HYPOTHESIS, so combinatorics alone delivers the family of
triples and never a sign — but the strong-pair theorem converts that hypothesis into a
statement about a single pair, and a statement about pairs is exactly what a graph can
count.

## The combinatorial half, and why the size is six

Strongness is a symmetric relation on the six atoms, and the analytic half says NO triple
is entirely weak.  By `R(3,3) = 6` — landed as
`Gtz.exists_monochromaticTriple_of_pairPredicate` — every pair predicate on six points has
a monochromatic triple.  It cannot be the weak one.  Hence

  **`Gtz.branchB_exists_strong_triangle`: a branch-B `(6,3)` tie carries three atoms that
  are PAIRWISE strong.**

The size is load-bearing and not an artifact.  At five atoms the pentagon splits the ten
pairs into two triangle-free halves
(`Gtz.exists_cliqueFree_three_and_compl_cliqueFree_three_five`), so no monochromatic
triangle is forced and the argument fails — which is the same place the hinge itself fails,
since `Gtz.not_hingeHoldsAtSize_five_three` refutes it at five by the diamond.  This is a
combinatorial reason for the five-six gap, alongside the conic count of
`Gtz.sizeGap_at_rank_three`.

## What the triangle costs, in weights

Strongness is about directions, and Parseval is about weights.  The landed pairing cap
`Gtz.pairing_cap` joins them: multiplying strongness by the two weights and feeding the cap
gives, with `a_c = t_c * x_c` the weighted excess and `s_c = t_c * ℓ_c` the share
(`Gtz.strongPair_weight_cap`),

  **`a_i * a_j ≤ 4 * (1 - s_i) * (1 - s_j)`** ,

and over the triangle the three of them multiply to
(`Gtz.strongTriangle_weight_product_cap`)

  **`a_i * a_j * a_k ≤ 8 * (1 - s_i) * (1 - s_j) * (1 - s_k)`** .

These are the first inequalities in the campaign that tie the strong-pair geometry to the
weight budgets `Σ a_c = 2`, `Σ s_c = 3`, `Σ t_c = 1`.  The shares are strictly below one at
a tie (`Gtz.share_lt_one_of_isTie`), so both right sides are positive and the caps are not
vacuous.
-/
import Mathlib
import Gtz.Wave.BranchBStrongPair
import Gtz.Wave.CornerAdmissibleGateway
import Gtz.Design.DominationGates
import Gtz.Design.StratumTieFreeClasses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Strongness, named -/

/-- **A STRONG PAIR.**  Its squared pairing clears a quarter of the product of the two
leverage excesses.  This is the conclusion `Gtz.branchB_exists_strongPair` delivers for one
pair of every triple. -/
def StrongPair (a b : Fin 3 → ℝ) : Prop :=
  (leverageOf a - 1) * (leverageOf b - 1) ≤ 4 * (a ⬝ᵥ b) ^ 2

theorem strongPair_comm {a b : Fin 3 → ℝ} (h : StrongPair a b) : StrongPair b a := by
  rw [StrongPair, dotProduct_comm]
  rw [StrongPair] at h
  linarith [h]

/-- Every triple of a branch-B tie carries a strong pair, in the named vocabulary. -/
theorem branchB_exists_strongPair' (D : WeightedDesign m 3) (htie : IsTie D) (hm : 2 ≤ m)
    (hall : ∀ e f : Fin m, f ≠ e → AdmissiblePair (D.atom e) (D.atom f))
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    StrongPair (D.atom x) (D.atom y) ∨ StrongPair (D.atom x) (D.atom z)
      ∨ StrongPair (D.atom y) (D.atom z) :=
  branchB_exists_strongPair D htie hm hall hxy hxz hyz

/-! ## 2. Strongness in weight currency

The pairing cap turns a statement about directions into one about the weight budgets. -/

/-- **A STRONG PAIR CAPS THE PRODUCT OF ITS WEIGHTED EXCESSES.**  Multiplying strongness by
the two weights and feeding `Gtz.pairing_cap`:

  `(t_i x_i) * (t_j x_j) ≤ 4 * (1 - t_i ℓ_i) * (1 - t_j ℓ_j)` .

No tie and no admissibility: only the strong pair and Parseval. -/
theorem strongPair_weight_cap (D : WeightedDesign m 3) {i j : Fin m} (hij : i ≠ j)
    (hstrong : StrongPair (D.atom i) (D.atom j)) :
    (D.weight i * (leverageOf (D.atom i) - 1)) * (D.weight j * (leverageOf (D.atom j) - 1))
      ≤ 4 * ((1 - D.weight i * leverageOf (D.atom i))
        * (1 - D.weight j * leverageOf (D.atom j))) := by
  have hcap := pairing_cap D hij
  have hti := D.weight_pos i
  have htj := D.weight_pos j
  rw [StrongPair] at hstrong
  have hmono : D.weight i * D.weight j
        * ((leverageOf (D.atom i) - 1) * (leverageOf (D.atom j) - 1))
      ≤ D.weight i * D.weight j * (4 * (D.atom i ⬝ᵥ D.atom j) ^ 2) :=
    mul_le_mul_of_nonneg_left hstrong (le_of_lt (mul_pos hti htj))
  nlinarith [hcap, hmono]

/-! ## 3. The strong triangle

`R(3,3) = 6` applied to strongness.  This is the main statement of the module. -/

/-- **A BRANCH-B `(6,3)` TIE CARRIES A STRONG TRIANGLE.**  Three atoms, pairwise strong.

No triple of a branch-B tie is entirely weak (`Gtz.branchB_exists_strongPair`), so the
monochromatic triple that `R(3,3) = 6` forces cannot be the weak one.  The size six is
load-bearing: at five atoms the pentagon defeats the dichotomy. -/
theorem branchB_exists_strong_triangle (D : WeightedDesign 6 3) (htie : IsTie D)
    (hall : ∀ e f : Fin 6, f ≠ e → AdmissiblePair (D.atom e) (D.atom f)) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c)
        ∧ StrongPair (D.atom b) (D.atom c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hbranch⟩ :=
    exists_monochromaticTriple_of_pairPredicate
      (fun i j : Fin 6 => StrongPair (D.atom i) (D.atom j)) (id : Fin 6 → Fin 6)
  simp only [id_eq] at hbranch
  rcases hbranch with hstrong | ⟨hwa, hwb, hwc⟩
  · exact ⟨a, b, c, hab, hac, hbc, hstrong.1, hstrong.2.1, hstrong.2.2⟩
  · exfalso
    rcases branchB_exists_strongPair' D htie (by norm_num) hall hab hac hbc with h | h | h
    · exact hwa h
    · exact hwb h
    · exact hwc h

/-! ## 4. What the triangle costs -/

/-- **THE TRIANGLE'S THREE WEIGHT CAPS.**  Each of the three pairs pays
`Gtz.strongPair_weight_cap`. -/
theorem branchB_strong_triangle_weight_caps (D : WeightedDesign 6 3) (htie : IsTie D)
    (hall : ∀ e f : Fin 6, f ≠ e → AdmissiblePair (D.atom e) (D.atom f)) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (D.weight a * (leverageOf (D.atom a) - 1))
          * (D.weight b * (leverageOf (D.atom b) - 1))
        ≤ 4 * ((1 - D.weight a * leverageOf (D.atom a))
          * (1 - D.weight b * leverageOf (D.atom b))) ∧
      (D.weight a * (leverageOf (D.atom a) - 1))
          * (D.weight c * (leverageOf (D.atom c) - 1))
        ≤ 4 * ((1 - D.weight a * leverageOf (D.atom a))
          * (1 - D.weight c * leverageOf (D.atom c))) ∧
      (D.weight b * (leverageOf (D.atom b) - 1))
          * (D.weight c * (leverageOf (D.atom c) - 1))
        ≤ 4 * ((1 - D.weight b * leverageOf (D.atom b))
          * (1 - D.weight c * leverageOf (D.atom c))) := by
  obtain ⟨a, b, c, hab, hac, hbc, hsab, hsac, hsbc⟩ :=
    branchB_exists_strong_triangle D htie hall
  exact ⟨a, b, c, hab, hac, hbc, strongPair_weight_cap D hab hsab,
    strongPair_weight_cap D hac hsac, strongPair_weight_cap D hbc hsbc⟩

/-- **THE PRODUCT FORM.**  Multiplying the three caps of a strong triangle and taking the
square root of both sides, the product of the three weighted excesses is at most eight times
the product of the three weight slacks.  Stated without a square root: the squares compare,
and both sides are nonnegative. -/
theorem strongTriangle_weight_product_cap {ea eb ec sa sb sc : ℝ}
    (hea : 0 ≤ ea) (heb : 0 ≤ eb) (hec : 0 ≤ ec)
    (hsa : 0 < sa) (hsb : 0 < sb) (hsc : 0 < sc)
    (hab : ea * eb ≤ 4 * (sa * sb)) (hac : ea * ec ≤ 4 * (sa * sc))
    (hbc : eb * ec ≤ 4 * (sb * sc)) :
    (ea * eb * ec) ^ 2 ≤ (8 * (sa * sb * sc)) ^ 2 := by
  have hstep : (ea * eb) * ((ea * ec) * (eb * ec)) ≤ (4 * (sa * sb))
      * ((4 * (sa * sc)) * (4 * (sb * sc))) := by
    have h1 : (ea * ec) * (eb * ec) ≤ (4 * (sa * sc)) * (4 * (sb * sc)) :=
      mul_le_mul hac hbc (by positivity) (by positivity)
    exact mul_le_mul hab h1 (by positivity) (by positivity)
  nlinarith [hstep]

/-- **THE TRIANGLE'S PRODUCT CAP AT A BRANCH-B TIE.**  All three excesses are positive and
all three slacks are positive, so the product form applies. -/
theorem branchB_strong_triangle_product_cap (D : WeightedDesign 6 3) (htie : IsTie D)
    (hall : ∀ e f : Fin 6, f ≠ e → AdmissiblePair (D.atom e) (D.atom f)) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ((D.weight a * (leverageOf (D.atom a) - 1))
          * (D.weight b * (leverageOf (D.atom b) - 1))
          * (D.weight c * (leverageOf (D.atom c) - 1))) ^ 2
        ≤ (8 * ((1 - D.weight a * leverageOf (D.atom a))
            * (1 - D.weight b * leverageOf (D.atom b))
            * (1 - D.weight c * leverageOf (D.atom c)))) ^ 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, hcapAB, hcapAC, hcapBC⟩ :=
    branchB_strong_triangle_weight_caps D htie hall
  have hheavy := branchB_of_forall_admissible D (by norm_num) hall
  have hexc : ∀ e : Fin 6, 0 ≤ D.weight e * (leverageOf (D.atom e) - 1) := by
    intro e
    exact mul_nonneg (D.weight_pos e).le (by linarith [hheavy e])
  have hslack : ∀ e : Fin 6, 0 < 1 - D.weight e * leverageOf (D.atom e) := by
    intro e
    linarith [share_lt_one_of_isTie (by norm_num) D htie e]
  exact ⟨a, b, c, hab, hac, hbc,
    strongTriangle_weight_product_cap (hexc a) (hexc b) (hexc c)
      (hslack a) (hslack b) (hslack c) hcapAB hcapAC hcapBC⟩

/-! ## 5. The admissibility dichotomy, with no branch hypothesis

Ramsey does not care which relation it is fed.  Applied to ADMISSIBILITY it splits every
six-atom design of rank three into two cases with no tie and no branch assumed, and the
first case feeds the strong-pair theorem directly. -/

/-- **EVERY SIX-ATOM DESIGN HAS AN ALL-ADMISSIBLE OR AN ALL-INADMISSIBLE TRIANGLE.**  Pure
`R(3,3) = 6` on the admissibility relation.  No tie, no heaviness, no branch. -/
theorem exists_admissible_or_inadmissible_triangle (D : WeightedDesign 6 3) :
    (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        AdmissiblePair (D.atom a) (D.atom b) ∧ AdmissiblePair (D.atom a) (D.atom c)
          ∧ AdmissiblePair (D.atom b) (D.atom c))
      ∨ (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ¬ AdmissiblePair (D.atom a) (D.atom b) ∧ ¬ AdmissiblePair (D.atom a) (D.atom c)
          ∧ ¬ AdmissiblePair (D.atom b) (D.atom c)) := by
  obtain ⟨a, b, c, hab, hac, hbc, hbranch⟩ :=
    exists_monochromaticTriple_of_pairPredicate
      (fun i j : Fin 6 => AdmissiblePair (D.atom i) (D.atom j)) (id : Fin 6 → Fin 6)
  simp only [id_eq] at hbranch
  rcases hbranch with hgood | hbad
  · exact Or.inl ⟨a, b, c, hab, hac, hbc, hgood.1, hgood.2.1, hgood.2.2⟩
  · exact Or.inr ⟨a, b, c, hab, hac, hbc, hbad.1, hbad.2.1, hbad.2.2⟩

/-- **THE ALL-HEAVY DICHOTOMY.**  At a `(6,3)` tie whose atoms are all strictly heavy,
either some triple is entirely inadmissible, or some triple is entirely admissible AND
carries a strong pair.  The second alternative is the one the strong-pair theorem reaches,
and it needs no branch-B hypothesis — only the admissibility of the triangle Ramsey hands
back. -/
theorem isTie_allHeavy_inadmissible_triangle_or_strongPair (D : WeightedDesign 6 3)
    (htie : IsTie D) (hheavy : ∀ e : Fin 6, 1 < leverageOf (D.atom e)) :
    (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ¬ AdmissiblePair (D.atom a) (D.atom b) ∧ ¬ AdmissiblePair (D.atom a) (D.atom c)
          ∧ ¬ AdmissiblePair (D.atom b) (D.atom c))
      ∨ (∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        AdmissiblePair (D.atom a) (D.atom b) ∧ AdmissiblePair (D.atom a) (D.atom c)
          ∧ AdmissiblePair (D.atom b) (D.atom c)
          ∧ (StrongPair (D.atom a) (D.atom b) ∨ StrongPair (D.atom a) (D.atom c)
              ∨ StrongPair (D.atom b) (D.atom c))) := by
  rcases exists_admissible_or_inadmissible_triangle D with
    ⟨a, b, c, hab, hac, hbc, hadAB, hadAC, hadBC⟩ | hbad
  · refine Or.inr ⟨a, b, c, hab, hac, hbc, hadAB, hadAC, hadBC, ?_⟩
    exact exists_strongPair_of_isTie_of_allHeavy D htie hheavy hab hac hbc hadAB
  · exact Or.inl hbad

/-! ## 6. The triangle is a genuine restriction

Two atoms of the triangle share a strong partner, so branch B cannot have every atom in at
most one strong pair — the strong graph has a vertex of degree at least two. -/

/-- **SOME ATOM OF A BRANCH-B TIE SITS IN TWO STRONG PAIRS.** -/
theorem branchB_exists_two_strong_partners (D : WeightedDesign 6 3) (htie : IsTie D)
    (hall : ∀ e f : Fin 6, f ≠ e → AdmissiblePair (D.atom e) (D.atom f)) :
    ∃ a b c : Fin 6, b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      StrongPair (D.atom a) (D.atom b) ∧ StrongPair (D.atom a) (D.atom c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hsab, hsac, -⟩ :=
    branchB_exists_strong_triangle D htie hall
  exact ⟨a, b, c, Ne.symm hab, Ne.symm hac, hbc, hsab, hsac⟩

end Gtz

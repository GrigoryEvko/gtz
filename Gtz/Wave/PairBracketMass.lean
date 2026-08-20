/-
# The pair bracket mass: the local bridge between the two budgets

The bracket budget totals the weighted squared brackets of a design over all
triples, the wedge budget totals the weighted wedges over all pairs.  This
module lands the LOCAL law that carries one into the other, exactly, at
every pair:

  `Σ_c t_at_bt_c·[abc]² = t_at_b·w_{ab}`   (`Gtz.pair_bracket_mass`)

— the bracket mass of the pair `{a,b}` is its wedge mass.  The sum runs over
ALL labels: the two degenerate terms vanish by themselves.  The proof is
Parseval read at the cross product: `[abc] = ⟨g_a × g_b, g_c⟩`, so the sum is
the design's own quadratic form at `g_a × g_b`, which Parseval evaluates as
the squared length of the cross product — and Lagrange makes that the wedge.

Three consequences, each new and each in the currencies of the hinge.

* **The pair mass IS the pair minor** (`Gtz.pair_bracket_mass_eq_blockDet`):
  the same number is the `2×2` principal minor of the design's projection.
  The hinge's conclusion becomes a statement about the bracket budget —
  `Gtz.hasParallelPair_iff_exists_pair_bracket_mass_zero`: a design carries a
  parallel pair exactly when SOME pair carries NO bracket mass, that is, when
  every bracket through that pair vanishes.

* **The contraction cap** (`Gtz.pair_bracket_mass_le_leverage`): the pair mass
  is at most either endpoint's weighted leverage, hence at most one.  The
  `2×2` block of the projection is a contraction and its determinant is below
  its diagonal.

* **THE PAIR TIE CAP** (`Gtz.isTie_lightest_pair_bracket_mass_cap`): at a tie,
  the two LIGHTEST atoms obey

    `t_at_b·w_{ab} ≤ 1 − t_a − t_b` ,

  strictly sharper than the free cap by the two weights themselves.  Each of
  the `m − 2` triples through the pair pays its own heaviest member by the
  contraction tax, that member is the third atom because the pair is
  lightest, and the simplex sums the payments.  [MEASURED: the pair identity
  is exact to `9e-16` over 45000 pairs, and the cap is EXACTLY TIGHT at the
  tetrahedral tie, where both sides are one half.]
-/
import Gtz.Wave.BracketContractionTax
import Gtz.Design.TripleGramSylvester
import Gtz.Reduction.SplitTransfer
import Gtz.Design.SphereExistence
import Gtz.Wave.CoweightedMemberLedger
import Gtz.Wave.PencilWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The bracket as a cross pairing -/

/-- The bracket is the pairing of the cross product with the third slot. -/
theorem tripleBracket_eq_cross_dot (u v w : Fin 3 → ℝ) :
    tripleBracket u v w = crossProduct u v ⬝ᵥ w := by
  simp only [tripleBracket_eq, cross_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 2. The pair bracket mass -/

/-- **THE PAIR BRACKET MASS.**  The weighted squared brackets through a pair
total the pair's weighted wedge:

  `Σ_c t_at_bt_c·[abc]² = t_at_b·(ℓ_aℓ_b − ⟨g_a,g_b⟩²)` .

The two degenerate terms vanish by themselves, so the sum may run over all
labels.  Parseval, read at the cross product. -/
theorem pair_bracket_mass (D : WeightedDesign m 3) (a b : Fin m) :
    ∑ c, D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      = D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2)) := by
  classical
  set n : Fin 3 → ℝ := crossProduct (D.atom a) (D.atom b) with hn
  -- every bracket through the pair is the cross pairing
  have hbr : ∀ c, atomBracket D a b c = n ⬝ᵥ D.atom c := fun c => by
    rw [atomBracket, tripleBracket_eq_cross_dot, hn]
  -- Parseval evaluates the design's form at the cross product
  have hpars : ∑ c, D.weight c * (n ⬝ᵥ D.atom c) ^ 2 = n ⬝ᵥ n := by
    have hform : n ⬝ᵥ ((∑ c, D.weight c • atomMatrix (D.atom c)) *ᵥ n)
        = n ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ n) := by rw [D.isParseval]
    rw [Matrix.one_mulVec] at hform
    rw [← hform, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun c _ => (quadForm_smul_atomMatrix _ _ _).symm
  -- Lagrange: the squared cross length is the wedge
  have hlag : n ⬝ᵥ n = leverageOf (D.atom a) * leverageOf (D.atom b)
      - atomPairing D a b ^ 2 := by
    rw [hn, cross_dot_cross, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct,
      atomPairing, dotProduct_comm (D.atom b) (D.atom a)]
    ring
  calc ∑ c, D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      = D.weight a * (D.weight b * ∑ c, D.weight c * (n ⬝ᵥ D.atom c) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hbr c]
    _ = D.weight a * (D.weight b * (n ⬝ᵥ n)) := by rw [hpars]
    _ = _ := by rw [hlag]

/-- **THE PAIR MASS IS THE PAIR MINOR.**  The bracket mass of a pair is the
`2×2` principal minor of the design's projection at that pair — the same
number the pair-minor bridge reads as the hinge's conclusion. -/
theorem pair_bracket_mass_eq_blockDet (D : WeightedDesign m 3) (a b : Fin m) :
    ∑ c, D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      = projectionOfDesign D a a * projectionOfDesign D b b
        - projectionOfDesign D a b ^ 2 := by
  rw [pair_bracket_mass, projectionOfDesign_diagonal, projectionOfDesign_diagonal,
    sq_projectionOfDesign_apply, atomPairing]
  ring

/-! ## 3. The hinge in the budget language -/

/-- **THE HINGE'S CONCLUSION IS A ZERO OF THE BRACKET BUDGET.**  A design
carries a parallel pair exactly when some pair carries no bracket mass — when
every bracket through that pair vanishes.  The wedge vanishes exactly at
proportionality, and the weights are positive. -/
theorem hasParallelPair_iff_exists_pair_bracket_mass_zero (D : WeightedDesign m 3) :
    HasParallelPair D ↔ ∃ a b : Fin m, a ≠ b ∧
      ∑ c, D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)) = 0 := by
  constructor
  · rintro ⟨kept, drop, ratio, hne, hpar⟩
    refine ⟨kept, drop, hne, ?_⟩
    rw [pair_bracket_mass]
    have hzero : leverageOf (D.atom kept) * leverageOf (D.atom drop)
        - atomPairing D kept drop ^ 2 = 0 := by
      rw [leverageOf_eq_dotProduct, leverageOf_eq_dotProduct, atomPairing, hpar]
      simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [hzero, mul_zero, mul_zero]
  · rintro ⟨a, b, hne, hzero⟩
    rw [pair_bracket_mass] at hzero
    have hwedge : leverageOf (D.atom a) * leverageOf (D.atom b)
        - atomPairing D a b ^ 2 = 0 := by
      have ha := D.weight_pos a
      have hb := D.weight_pos b
      by_contra hcon
      exact hcon (by
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd h ha.ne'
        · rcases mul_eq_zero.mp h with h2 | h2
          · exact absurd h2 hb.ne'
          · exact h2)
    -- a vanishing wedge is a vanishing cross product, hence proportionality
    have hcross : crossProduct (D.atom a) (D.atom b) = 0 := by
      have hnn : crossProduct (D.atom a) (D.atom b)
          ⬝ᵥ crossProduct (D.atom a) (D.atom b) = 0 := by
        rw [cross_dot_cross, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct,
          dotProduct_comm (D.atom b) (D.atom a)]
        rw [atomPairing] at hwedge
        linarith [hwedge]
      by_contra hne0
      exact absurd hnn (ne_of_gt (dotProduct_self_pos hne0))
    exact hasParallelPair_of_crossProduct_atom_eq_zero D hne hcross

/-! ## 4. The contraction cap of the pair mass -/

/-- **THE PAIR MASS IS CAPPED BY EITHER LEVERAGE.**  The `2×2` block of the
projection is positive semidefinite with diagonal at most one, so its
determinant is at most either weighted leverage, hence at most one. -/
theorem pair_bracket_mass_le_leverage (D : WeightedDesign m 3) (a b : Fin m) :
    ∑ c, D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      ≤ D.weight a * leverageOf (D.atom a) := by
  rw [pair_bracket_mass]
  have hb := parseval_weight_leverage_le_one D b
  rw [← leverageOf_eq_dotProduct] at hb
  have hcs : atomPairing D a b ^ 2
      ≤ leverageOf (D.atom a) * leverageOf (D.atom b) := by
    rw [atomPairing, leverageOf_eq_dotProduct, leverageOf_eq_dotProduct]
    have h := dotProduct_sq_le_mul (D.atom a) (D.atom b)
    nlinarith [h]
  have hlev : 0 ≤ leverageOf (D.atom a) := by
    rw [leverageOf]
    positivity
  have hwa := (D.weight_pos a).le
  have h1 : 0 ≤ D.weight a * leverageOf (D.atom a) := mul_nonneg hwa hlev
  have hstep : D.weight a * (D.weight b * (leverageOf (D.atom a) * leverageOf (D.atom b)))
      ≤ D.weight a * leverageOf (D.atom a) := by
    nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 - D.weight b * leverageOf (D.atom b))]
  nlinarith [hstep,
    mul_nonneg (mul_nonneg hwa (D.weight_pos b).le) (sq_nonneg (atomPairing D a b))]

/-! ## 5. The lightest pair and the tie cap -/

/-- Every design of at least two atoms carries a LIGHTEST PAIR: two distinct
atoms whose weights are both at most the weight of every other atom. -/
theorem exists_lightest_pair (D : WeightedDesign m 3) (hm : 2 ≤ m) :
    ∃ a b : Fin m, a ≠ b ∧ ∀ c, c ≠ a → c ≠ b →
      D.weight a ≤ D.weight c ∧ D.weight b ≤ D.weight c := by
  classical
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, -, hamin⟩ := Finset.exists_min_image Finset.univ D.weight hne
  have hrest : (Finset.univ.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, hbmem, hbmin⟩ := Finset.exists_min_image (Finset.univ.erase a) D.weight hrest
  have hab : a ≠ b := fun h => (Finset.mem_erase.mp hbmem).1 h.symm
  refine ⟨a, b, hab, fun c hca hcb => ⟨hamin c (Finset.mem_univ c), ?_⟩⟩
  exact hbmin c (Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩)

/-- **THE PAIR TIE CAP.**  At a tie, a pair whose two weights are at most
every other weight obeys

  `t_at_b·w_{ab} ≤ 1 − t_a − t_b` .

Every triple through the pair pays one member weight by the contraction tax,
and because the pair is lightest that member may be taken to be the third
atom.  The simplex then sums the payments.  Strictly sharper than the free
contraction cap, by the two weights themselves. -/
theorem isTie_lightest_pair_bracket_mass_cap (D : WeightedDesign m 3)
    (htie : IsTie D) {a b : Fin m} (hab : a ≠ b)
    (hlight : ∀ c, c ≠ a → c ≠ b →
      D.weight a ≤ D.weight c ∧ D.weight b ≤ D.weight c) :
    D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2))
      ≤ 1 - D.weight a - D.weight b := by
  classical
  set pair : Finset (Fin m) := {a, b} with hpair
  -- every triple through the pair pays the third atom's weight
  have hterm : ∀ c ∈ Finset.univ \ pair,
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
        ≤ D.weight c := by
    intro c hc
    rw [Finset.mem_sdiff, hpair, Finset.mem_insert, Finset.mem_singleton] at hc
    have hca : c ≠ a := fun h => hc.2 (Or.inl h)
    have hcb : c ≠ b := fun h => hc.2 (Or.inr h)
    obtain ⟨member, hmem, hle⟩ :=
      isTie_bracket_tax D htie hab (Ne.symm hca) (Ne.symm hcb)
    obtain ⟨hla, hlb⟩ := hlight c hca hcb
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
  -- the degenerate terms vanish
  have hdeg : ∀ c ∈ pair,
      D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)) = 0 := by
    intro c hc
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hc
    have hzero : atomBracket D a b c = 0 := by
      rcases hc with rfl | rfl
      · rw [atomBracket, tripleBracket_swapLeft]
        rw [tripleBracket_eq_zero_of_repeatRight]
        ring
      · rw [atomBracket, tripleBracket_eq_zero_of_repeatRight]
    rw [hzero]
    ring
  -- split the identity along the pair
  have hsplit : ∑ c, D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      = ∑ c ∈ Finset.univ \ pair,
          D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ pair),
      Finset.sum_eq_zero hdeg, add_zero]
  have hweights : ∑ c ∈ Finset.univ \ pair, D.weight c
      = 1 - D.weight a - D.weight b := by
    have hsum : ∑ c ∈ Finset.univ \ pair, D.weight c + ∑ c ∈ pair, D.weight c
        = ∑ c, D.weight c := Finset.sum_sdiff (Finset.subset_univ pair)
    rw [D.weight_sum_one, hpair, Finset.sum_pair hab] at hsum
    linarith
  have hchain := Finset.sum_le_sum hterm
  rw [← hsplit, pair_bracket_mass, hweights] at hchain
  exact hchain

/-- **THE PAIR TIE CAP AT THE LIGHTEST PAIR.**  Every `(m,3)` tie carries a
pair whose weighted wedge is at most one minus the pair's own weight. -/
theorem isTie_exists_pair_bracket_mass_cap (D : WeightedDesign m 3)
    (htie : IsTie D) (hm : 2 ≤ m) :
    ∃ a b : Fin m, a ≠ b ∧
      D.weight a * (D.weight b
          * (leverageOf (D.atom a) * leverageOf (D.atom b)
            - atomPairing D a b ^ 2))
        ≤ 1 - D.weight a - D.weight b := by
  obtain ⟨a, b, hab, hlight⟩ := exists_lightest_pair D hm
  exact ⟨a, b, hab, isTie_lightest_pair_bracket_mass_cap D htie hab hlight⟩

end Gtz

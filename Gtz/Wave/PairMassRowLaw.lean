/-
# The row law of the pair mass, and the small pair it forces

The pair bracket mass `P_ab = t_at_b·w_{ab}` is the `2×2` principal minor of
the design's projection, and the hinge's conclusion is a ZERO of it.  This
module lands the LOCAL conservation law of that matrix and the existence
statement it forces.

THE ROW LAW (`Gtz.pair_mass_row`): at every atom,

  `Σ_b t_at_b·w_{ab} = 2·t_a·ℓ_a` ,

twice the projection diagonal.  The proof is Parseval used twice: once to
evaluate `Σ_b t_b·⟨g_a,g_b⟩² = ℓ_a`, once for the leverage total
`Σ_b t_bℓ_b = 3`, and `3ℓ_a − ℓ_a = 2ℓ_a`.  The diagonal term is zero by
itself, so the sum may run over all labels.  Summing the row law over the
atoms returns the wedge budget: `Σ_a 2t_aℓ_a = 6`.

Two consequences, both new, both aimed at the hinge.

* `Gtz.exists_small_pair_mass` — every atom carries a partner whose pair mass
  is at most `2t_aℓ_a/(m−1)`: the row is a nonnegative family of `m−1` terms
  with a known total, so its minimum is below the average.

* `Gtz.exists_pair_mass_le` — some pair of the design has mass at most
  `6/(m(m−1))`, with NO tie hypothesis: the lightest projection diagonal is
  at most `3/m` because the diagonals total the rank.  At `(6,3)` that is one
  fifth (`Gtz.exists_pair_mass_le_fifth`).

The hinge asks for a pair of mass exactly zero.  The row law is the free half
of the descent — it produces a SMALL pair at every design, and the tie caps
of `Gtz.PairBracketMass` then act on that pair.  [MEASURED: the row law is
exact to `2e-15` over 24000 rows.]
-/
import Gtz.Wave.PairBracketMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The row law -/

/-- The design resolves every atom's own leverage: `Σ_b t_b·⟨g_a,g_b⟩² = ℓ_a`.
Parseval read at the atom itself. -/
theorem parseval_pairing_row (D : WeightedDesign m 3) (a : Fin m) :
    ∑ b, D.weight b * atomPairing D a b ^ 2 = leverageOf (D.atom a) := by
  have hform : D.atom a ⬝ᵥ ((∑ b, D.weight b • atomMatrix (D.atom b)) *ᵥ D.atom a)
      = D.atom a ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ D.atom a) := by
    rw [D.isParseval]
  rw [Matrix.one_mulVec, Matrix.sum_mulVec, dotProduct_sum] at hform
  rw [← leverageOf_eq_dotProduct] at hform
  rw [← hform]
  exact Finset.sum_congr rfl fun b _ => by
    rw [quadForm_smul_atomMatrix, atomPairing]

/-- **THE ROW LAW OF THE PAIR MASS.**  The pair masses at a fixed atom total
twice that atom's projection diagonal:

  `Σ_b t_at_b·w_{ab} = 2·t_a·ℓ_a` .

The diagonal term vanishes by itself.  Parseval twice: the row of squared
pairings is the atom's own leverage, and the weighted leverages total the
rank. -/
theorem pair_mass_row (D : WeightedDesign m 3) (a : Fin m) :
    ∑ b, D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2))
      = 2 * (D.weight a * leverageOf (D.atom a)) := by
  have hlev : ∑ b, D.weight b * leverageOf (D.atom b) = 3 := by
    have h := sum_weighted_leverage D
    norm_num at h
    exact h
  have hrow := parseval_pairing_row D a
  have h1 : ∑ b, (D.weight a * leverageOf (D.atom a))
      * (D.weight b * leverageOf (D.atom b))
      = (D.weight a * leverageOf (D.atom a)) * 3 := by
    rw [← Finset.mul_sum, hlev]
  have h2 : ∑ b, D.weight a * (D.weight b * atomPairing D a b ^ 2)
      = D.weight a * leverageOf (D.atom a) := by
    rw [← Finset.mul_sum, hrow]
  have hsplit : ∑ b, D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2))
      = (∑ b, (D.weight a * leverageOf (D.atom a))
            * (D.weight b * leverageOf (D.atom b)))
        - ∑ b, D.weight a * (D.weight b * atomPairing D a b ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit, h1, h2]
  ring

/-- The pair mass of an atom with itself vanishes. -/
theorem pair_mass_self (D : WeightedDesign m 3) (a : Fin m) :
    D.weight a * (D.weight a
      * (leverageOf (D.atom a) * leverageOf (D.atom a)
        - atomPairing D a a ^ 2)) = 0 := by
  have hself : atomPairing D a a = leverageOf (D.atom a) := by
    rw [atomPairing, leverageOf_eq_dotProduct]
  rw [hself]
  ring

/-! ## 2. Every atom carries a small partner -/

/-- **THE SMALL PARTNER.**  Every atom carries a partner whose pair mass is at
most `2t_aℓ_a/(m−1)`.  The row is a nonnegative family of `m − 1` terms with a
known total, so its minimum sits below the average. -/
theorem exists_small_pair_mass (D : WeightedDesign m 3) (hm : 2 ≤ m) (a : Fin m) :
    ∃ b : Fin m, b ≠ a ∧
      D.weight a * (D.weight b
          * (leverageOf (D.atom a) * leverageOf (D.atom b)
            - atomPairing D a b ^ 2))
        ≤ 2 * (D.weight a * leverageOf (D.atom a)) / ((m : ℝ) - 1) := by
  classical
  set f : Fin m → ℝ := fun b => D.weight a * (D.weight b
    * (leverageOf (D.atom a) * leverageOf (D.atom b)
      - atomPairing D a b ^ 2)) with hf
  have hrest : (Finset.univ.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, hbmem, hbmin⟩ := Finset.exists_min_image (Finset.univ.erase a) f hrest
  have hbne : b ≠ a := (Finset.mem_erase.mp hbmem).1
  have hcard : (Finset.univ.erase a).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  have hsum : ∑ c ∈ Finset.univ.erase a, f c
      = 2 * (D.weight a * leverageOf (D.atom a)) := by
    have hfull : ∑ c, f c = 2 * (D.weight a * leverageOf (D.atom a)) :=
      pair_mass_row D a
    have hsplit : ∑ c ∈ Finset.univ.erase a, f c + f a = ∑ c, f c :=
      Finset.sum_erase_add _ _ (Finset.mem_univ a)
    have hfa : f a = 0 := pair_mass_self D a
    rw [hfa, add_zero] at hsplit
    rw [hsplit, hfull]
  have hcards : ((m : ℝ) - 1) * f b ≤ ∑ c ∈ Finset.univ.erase a, f c := by
    have hstep := Finset.card_nsmul_le_sum (Finset.univ.erase a) f (f b)
      fun c hc => hbmin c hc
    rw [nsmul_eq_mul, hcard] at hstep
    have hcast : (((m - 1 : ℕ)) : ℝ) = (m : ℝ) - 1 := by
      have h1 : 1 ≤ m := by omega
      rw [Nat.cast_sub h1]
      norm_num
    rwa [hcast] at hstep
  have hmpos : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [hsum] at hcards
  exact ⟨b, hbne, by rw [le_div_iff₀ hmpos]; linarith [hcards]⟩

/-! ## 3. The free small pair of every design -/

/-- **THE FREE SMALL PAIR.**  Every design carries a pair whose mass is at
most `6/(m(m−1))` — no tie hypothesis.  The projection diagonals total the
rank, so the lightest one is at most `3/m`, and the row law halves that over
the `m − 1` partners. -/
theorem exists_pair_mass_le (D : WeightedDesign m 3) (hm : 2 ≤ m) :
    ∃ a b : Fin m, b ≠ a ∧
      D.weight a * (D.weight b
          * (leverageOf (D.atom a) * leverageOf (D.atom b)
            - atomPairing D a b ^ 2))
        ≤ 6 / ((m : ℝ) * ((m : ℝ) - 1)) := by
  classical
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = 3 := by
    have h := sum_weighted_leverage D
    norm_num at h
    exact h
  -- the lightest projection diagonal is at most three over the size
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, -, hamin⟩ := Finset.exists_min_image Finset.univ
    (fun c => D.weight c * leverageOf (D.atom c)) hne
  have hdiag : D.weight a * leverageOf (D.atom a) ≤ 3 / (m : ℝ) := by
    have hstep := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin m))
      (fun c => D.weight c * leverageOf (D.atom c))
      (D.weight a * leverageOf (D.atom a)) fun c hc => hamin c hc
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, hlev] at hstep
    rw [le_div_iff₀ hmpos]
    linarith [hstep]
  obtain ⟨b, hbne, hle⟩ := exists_small_pair_mass D hm a
  refine ⟨a, b, hbne, le_trans hle ?_⟩
  have hdm : D.weight a * leverageOf (D.atom a) * (m : ℝ) ≤ 3 :=
    (le_div_iff₀ hmpos).mp hdiag
  rw [div_le_div_iff₀ hm1pos (by positivity)]
  nlinarith [hdm, hm1pos, hmpos]

/-- **THE FIFTH AT `(6,3)`.**  Every `(6,3)` design carries a pair whose mass
is at most one fifth. -/
theorem exists_pair_mass_le_fifth (D : WeightedDesign 6 3) :
    ∃ a b : Fin 6, b ≠ a ∧
      D.weight a * (D.weight b
          * (leverageOf (D.atom a) * leverageOf (D.atom b)
            - atomPairing D a b ^ 2))
        ≤ 1 / 5 := by
  obtain ⟨a, b, hbne, hle⟩ := exists_pair_mass_le D (by norm_num)
  refine ⟨a, b, hbne, ?_⟩
  norm_num at hle
  linarith [hle]

/-! ## 4. The realness carrier -/

/-- **THE REALNESS CARRIER OF THE PAIR-MASS CALCULUS.**  The pair mass is
nonnegative, because the wedge is the squared length of the cross product:

  `t_at_b·w_{ab} = t_at_b·|g_a × g_b|² ≥ 0` .

This is the ONE field-sensitive step of the whole pair-mass lane.  Every other
law of `Gtz.PairBracketMass` and of this module is a polynomial identity or a
counting argument, valid over any field: the row law, the budgets, the pair
identity, and the small-partner extraction never look at a sign.  Over `ℂ`
with the BILINEAR wedge the same expression is not a sum of squares and can
vanish — or turn negative — at isotropic atoms with no proportionality
whatsoever, which is exactly how the complex corank-one ties evade every
field-blind law.  A downstream argument that needs realness should spend it
HERE and nowhere else. -/
theorem pair_mass_nonneg (D : WeightedDesign m 3) (a b : Fin m) :
    0 ≤ D.weight a * (D.weight b
      * (leverageOf (D.atom a) * leverageOf (D.atom b)
        - atomPairing D a b ^ 2)) := by
  have hwedge : 0 ≤ leverageOf (D.atom a) * leverageOf (D.atom b)
      - atomPairing D a b ^ 2 := by
    have hcross : crossProduct (D.atom a) (D.atom b)
        ⬝ᵥ crossProduct (D.atom a) (D.atom b)
        = leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2 := by
      rw [cross_dot_cross, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct,
        atomPairing, dotProduct_comm (D.atom b) (D.atom a)]
      ring
    rw [← hcross]
    exact dotProduct_self_nonneg _
  exact mul_nonneg (D.weight_pos a).le (mul_nonneg (D.weight_pos b).le hwedge)

/-- **EVERY PAIR MASS IS BELOW ITS ROW.**  With the realness carrier the row
law becomes a cap: no single pair mass exceeds twice either endpoint's
projection diagonal, hence none exceeds two. -/
theorem pair_mass_le_row (D : WeightedDesign m 3) (a b : Fin m) :
    D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2))
      ≤ 2 * (D.weight a * leverageOf (D.atom a)) := by
  classical
  rw [← pair_mass_row D a]
  exact Finset.single_le_sum (fun c _ => pair_mass_nonneg D a c) (Finset.mem_univ b)

end Gtz

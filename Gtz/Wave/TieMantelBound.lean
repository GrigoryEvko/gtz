import Gtz.Wave.TieGraphTrichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The Mantel bound of a tie, and the flat corner

Two results, one combinatorial and one exact.

## The Mantel bound

The tie trichotomy makes admissibility an EDGE property and heaviness a
VERTEX property, so a tie is a statement about a graph.  Extremal graph
theory then applies, and at four vertices it is a finite check: a graph on
the six edges of `K₄` that contains no triangle has at most four edges
(`Gtz.mantel_four`, by decision procedure over all `64` edge sets).

Hence `Gtz.isTie_heavyFour_admissible_card_le_four`: at a tie, four heavy
atoms with no flat triple admit at most FOUR of their six pairs — so at
least two pairs are inadmissible (`Gtz.isTie_heavyFour_two_inadmissible`).
Five admissible pairs would complete a live triangle, and the tie forbids
it.

## The flat corner

The second invariant of a triple gap is exactly the pair minor sum
(`Gtz.secondInvariant_gap_eq_pairMinor_sum`).  A `Z1` corner gap is a
nonnegative multiple of a single atom, so it has RANK ONE, and the second
invariant of a rank-one form vanishes.  Therefore
`Gtz.corner_pairMinor_sum_eq_zero`: on the whole corner family, at every
scale, the pair minor sum is EXACTLY zero.

Combined with the bracket identity this pins the corner bracket with no
inequality at all (`Gtz.corner_bracket_eq_leverageSum_sub_two`):

  `[C]² = ℓ_x + ℓ_y + ℓ_z − 2` .

Measured for the record: the pair minor sum is `0` at every corner scale
and `9` at the tetrahedral tie, so this law separates corner ties from
tetrahedral ties rather than holding vacuously across both.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The second invariant is the pair minor sum -/

/-- **THE SECOND INVARIANT OF A TRIPLE GAP IS ITS PAIR MINOR SUM.**  The
middle coefficient of the gap's characteristic polynomial is the sum of the
three pair-local Sylvester minors. -/
theorem secondInvariant_gap_eq_pairMinor_sum (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)) ^ 2
        - Matrix.trace ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
          * (subsetSum D ({x, y, z} : Finset (Fin m)) - 1))) / 2
      = pairGapMinor (D.atom x) (D.atom y)
        + pairGapMinor (D.atom x) (D.atom z)
        + pairGapMinor (D.atom y) (D.atom z) := by
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y)
        + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  rw [hsum, pairGapMinor, pairGapMinor, pairGapMinor]
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- **A RANK-ONE FORM HAS NO SECOND INVARIANT.**  The middle coefficient of
the characteristic polynomial of a scaled atom vanishes. -/
theorem secondInvariant_smul_atomMatrix (lam : ℝ) (u : Fin 3 → ℝ) :
    ((Matrix.trace (lam • atomMatrix u)) ^ 2
        - Matrix.trace ((lam • atomMatrix u) * (lam • atomMatrix u))) / 2
      = 0 := by
  simp [Matrix.trace_fin_three, Matrix.mul_apply, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_three, dotProduct]
  ring

/-! ## 2. The flat corner -/

/-- **THE CORNER PAIR MINOR SUM VANISHES.**  A `Z1` corner gap is a scaled
atom, so it has rank one and no second invariant.  On the whole corner
family, at every scale, the three pair minors of the inside triple sum to
EXACTLY zero. -/
theorem corner_pairMinor_sum_eq_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    pairGapMinor (D.atom x) (D.atom y)
      + pairGapMinor (D.atom x) (D.atom z)
      + pairGapMinor (D.atom y) (D.atom z) = 0 := by
  rw [← secondInvariant_gap_eq_pairMinor_sum D hxy hxz hyz, hgap,
    secondInvariant_smul_atomMatrix]

/-- **THE CORNER BRACKET IS PINNED WITH NO INEQUALITY.**  At a corner of a
tie the squared bracket of the inside triple is the leverage total less
two, exactly. -/
theorem corner_bracket_eq_leverageSum_sub_two (D : WeightedDesign m 3)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    atomBracket D x y z ^ 2
      = leverageOf (D.atom x) + leverageOf (D.atom y)
        + leverageOf (D.atom z) - 2 := by
  rw [corner_bracket_identity D htie hxy hxz hyz hlam hgap,
    corner_pairMinor_sum_eq_zero D hxy hxz hyz hgap, add_zero]

/-! ## 3. The Mantel bound at four vertices -/

/-- The six edge slots of a four-set: `0 = ab`, `1 = ac`, `2 = ad`,
`3 = bc`, `4 = bd`, `5 = cd`. -/
def triangleEdges : Fin 4 → Finset (Fin 6)
  | 0 => {0, 1, 3}
  | 1 => {0, 2, 4}
  | 2 => {1, 2, 5}
  | 3 => {3, 4, 5}

/-- **MANTEL AT FOUR VERTICES.**  A set of edges of `K₄` containing no
triangle has at most four of the six edges.  A finite check over all `64`
edge sets — extremal graph theory as a decision procedure. -/
theorem mantel_four (S : Finset (Fin 6))
    (hfree : ∀ t : Fin 4, ¬ (triangleEdges t ⊆ S)) : S.card ≤ 4 := by
  revert hfree
  revert S
  decide

/-! ## 4. The tie's Mantel bound -/

/-- The admissible edge set of an ordered four-set, indexed by edge slot. -/
noncomputable def admissibleEdges (D : WeightedDesign m 3) (a b c d : Fin m) :
    Finset (Fin 6) := by
  classical
  exact Finset.univ.filter fun e =>
    match e with
    | 0 => AdmissiblePair (D.atom a) (D.atom b)
    | 1 => AdmissiblePair (D.atom a) (D.atom c)
    | 2 => AdmissiblePair (D.atom a) (D.atom d)
    | 3 => AdmissiblePair (D.atom b) (D.atom c)
    | 4 => AdmissiblePair (D.atom b) (D.atom d)
    | 5 => AdmissiblePair (D.atom c) (D.atom d)

theorem mem_admissibleEdges (D : WeightedDesign m 3) (a b c d : Fin m)
    (e : Fin 6) :
    e ∈ admissibleEdges D a b c d ↔
      (match e with
        | 0 => AdmissiblePair (D.atom a) (D.atom b)
        | 1 => AdmissiblePair (D.atom a) (D.atom c)
        | 2 => AdmissiblePair (D.atom a) (D.atom d)
        | 3 => AdmissiblePair (D.atom b) (D.atom c)
        | 4 => AdmissiblePair (D.atom b) (D.atom d)
        | 5 => AdmissiblePair (D.atom c) (D.atom d)) := by
  classical
  rw [admissibleEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

/-- **THE MANTEL BOUND OF A TIE.**  At a tie, four heavy atoms with no flat
triple admit at most FOUR of their six pairs.  A fifth admissible pair
would complete a triangle whose three atoms are heavy and whose three pairs
are admissible — a live triple — and a tie makes every live triple flat. -/
theorem isTie_heavyFour_admissible_card_le_four (D : WeightedDesign m 3)
    (htie : IsTie D) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hha : HeavyAtom D a) (hhb : HeavyAtom D b) (hhc : HeavyAtom D c)
    (hhd : HeavyAtom D d)
    (hsharp : 0 < tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      ∧ 0 < tripleGapDet (D.atom a) (D.atom b) (D.atom d)
      ∧ 0 < tripleGapDet (D.atom a) (D.atom c) (D.atom d)
      ∧ 0 < tripleGapDet (D.atom b) (D.atom c) (D.atom d)) :
    (admissibleEdges D a b c d).card ≤ 4 := by
  classical
  obtain ⟨sabc, sabd, sacd, sbcd⟩ := hsharp
  refine mantel_four _ (fun t hsub => ?_)
  have hmem : ∀ e : Fin 6, e ∈ triangleEdges t →
      e ∈ admissibleEdges D a b c d := fun e he => hsub he
  fin_cases t
  · -- the triangle `abc`: edges 0, 1, 3
    have e0 := (mem_admissibleEdges D a b c d 0).mp (hmem 0 (by decide))
    have e1 := (mem_admissibleEdges D a b c d 1).mp (hmem 1 (by decide))
    have e3 := (mem_admissibleEdges D a b c d 3).mp (hmem 3 (by decide))
    exact absurd (isTie_live_gapDet_nonpos D htie hab hac hbc
      ⟨hha, hhb, hhc, e0, e1, e3⟩) (not_le.mpr sabc)
  · -- the triangle `abd`: edges 0, 2, 4
    have e0 := (mem_admissibleEdges D a b c d 0).mp (hmem 0 (by decide))
    have e2 := (mem_admissibleEdges D a b c d 2).mp (hmem 2 (by decide))
    have e4 := (mem_admissibleEdges D a b c d 4).mp (hmem 4 (by decide))
    exact absurd (isTie_live_gapDet_nonpos D htie hab had hbd
      ⟨hha, hhb, hhd, e0, e2, e4⟩) (not_le.mpr sabd)
  · -- the triangle `acd`: edges 1, 2, 5
    have e1 := (mem_admissibleEdges D a b c d 1).mp (hmem 1 (by decide))
    have e2 := (mem_admissibleEdges D a b c d 2).mp (hmem 2 (by decide))
    have e5 := (mem_admissibleEdges D a b c d 5).mp (hmem 5 (by decide))
    exact absurd (isTie_live_gapDet_nonpos D htie hac had hcd
      ⟨hha, hhc, hhd, e1, e2, e5⟩) (not_le.mpr sacd)
  · -- the triangle `bcd`: edges 3, 4, 5
    have e3 := (mem_admissibleEdges D a b c d 3).mp (hmem 3 (by decide))
    have e4 := (mem_admissibleEdges D a b c d 4).mp (hmem 4 (by decide))
    have e5 := (mem_admissibleEdges D a b c d 5).mp (hmem 5 (by decide))
    exact absurd (isTie_live_gapDet_nonpos D htie hbc hbd hcd
      ⟨hhb, hhc, hhd, e3, e4, e5⟩) (not_le.mpr sbcd)

/-- **TWO PAIRS ARE INADMISSIBLE.**  The complement reading of the Mantel
bound: at a tie, four heavy atoms with no flat triple carry at least two
inadmissible pairs among their six. -/
theorem isTie_heavyFour_two_inadmissible (D : WeightedDesign m 3)
    (htie : IsTie D) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hha : HeavyAtom D a) (hhb : HeavyAtom D b) (hhc : HeavyAtom D c)
    (hhd : HeavyAtom D d)
    (hsharp : 0 < tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      ∧ 0 < tripleGapDet (D.atom a) (D.atom b) (D.atom d)
      ∧ 0 < tripleGapDet (D.atom a) (D.atom c) (D.atom d)
      ∧ 0 < tripleGapDet (D.atom b) (D.atom c) (D.atom d)) :
    2 ≤ (admissibleEdges D a b c d)ᶜ.card := by
  classical
  have hbound := isTie_heavyFour_admissible_card_le_four D htie hab hac had
    hbc hbd hcd hha hhb hhc hhd hsharp
  have hcompl : (admissibleEdges D a b c d)ᶜ.card
      = 6 - (admissibleEdges D a b c d).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  omega

end Gtz

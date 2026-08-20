import Gtz.Wave.TripleGramChart
import Gtz.Wave.DominatorWedgeFloor
import Gtz.Wave.KOneBracketLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The tie as a graph condition

The landed Gram criterion decides strict domination by three Sylvester
minors of the chart gap.  Those minors are LOCAL in a way the campaign has
never exploited: the first is ATOM-local (one leverage), the second is
PAIR-local (`Gtz.pairGapMinor`, which mentions no third atom), and only the
third sees the whole triple.  This module turns that locality into a graph
statement on the six atoms of a design.

Write an atom HEAVY when its leverage exceeds one, a pair ADMISSIBLE when
its pair minor is positive (the landed `Gtz.AdmissiblePair`), and call a
triple LIVE when all three atoms are heavy and all three pairs admissible.

* `Gtz.posDef_subsetSum_iff_live_and_gapDet` — THE SYMMETRIC SYLVESTER
  CRITERION: a triple dominates strictly exactly when it is live and its
  gap determinant is positive.  Not the leading minors — all of them.
* `Gtz.isTie_triple_trichotomy` — at a tie every triple carries a light
  atom, or an inadmissible pair, or a nonpositive gap determinant.  The
  tie condition is now a statement about a vertex-and-edge-labelled graph.
* `Gtz.isTie_live_gapDet_nonpos` — every LIVE triangle of a tie has
  nonpositive gap determinant.
* `Gtz.isTie_heavyFour_admissible_gapDet_nonpos` — the four-vertex
  saturation: if four atoms are pairwise admissible and all heavy, then at
  a tie ALL FOUR of their triples have nonpositive gap determinant.  Four
  simultaneous polynomial inequalities in the dot products of four atoms,
  from the tie alone.

The second half is the exact law of the dominating triple.

* `Gtz.dominating_triple_gapDet_eq_zero` — THE EXACT ZERO: the dominating
  triple of a tie has gap determinant EXACTLY zero.  Weak domination makes
  the gap positive semidefinite, hence its determinant nonnegative; the tie
  forbids positive definiteness, and a positive semidefinite form with
  positive determinant is positive definite.  The tie therefore lives on
  the hypersurface `tripleGapDet = 0`, a polynomial equation in six dot
  products.
* `Gtz.dominating_triple_bracket_identity` — with the determinant gone the
  shift expansion is an IDENTITY: the squared bracket of the dominating
  triple is its leverage total minus two plus its pair minor sum.
* `Gtz.dominating_triple_pairMinor_sum_nonneg` — hence the landed sharp
  bracket floor says exactly that the pair minor sum is nonnegative, and
  `Gtz.dominating_triple_bracket_sharp_iff` records the equivalence.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Heavy atoms, admissible pairs, live triples -/

/-- An atom is HEAVY when its leverage exceeds one — the first Sylvester
minor of its chart gap slot. -/
def HeavyAtom (D : WeightedDesign m 3) (c : Fin m) : Prop :=
  1 < leverageOf (D.atom c)

/-- A triple is LIVE when all three atoms are heavy and all three pairs are
admissible: every Sylvester minor below the top one is positive. -/
def LiveTriple (D : WeightedDesign m 3) (x y z : Fin m) : Prop :=
  HeavyAtom D x ∧ HeavyAtom D y ∧ HeavyAtom D z
    ∧ AdmissiblePair (D.atom x) (D.atom y)
    ∧ AdmissiblePair (D.atom x) (D.atom z)
    ∧ AdmissiblePair (D.atom y) (D.atom z)

/-- **THE SYMMETRIC SYLVESTER CRITERION.**  A triple dominates strictly
exactly when it is live and its gap determinant is positive.  The forward
direction spends the landed rotation and swap criteria, so no slot is
privileged. -/
theorem posDef_subsetSum_iff_live_and_gapDet (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ LiveTriple D x y z
        ∧ 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  constructor
  · intro hpd
    obtain ⟨hlev, _, hdet⟩ :=
      (subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mp hpd
    obtain ⟨pxy, pxz, pyz⟩ :=
      forall_pairGapMinor_pos_of_subsetSum_posDef D x y z hxy hxz hyz hpd
    have hchart := (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mp hpd
    have hy : 1 < leverageOf (D.atom y) := by
      have hd : 0 < (tripleGram (D.atom x) (D.atom y) (D.atom z) - 1) 1 1 :=
        hchart.diag_pos
      rw [gap_one_one] at hd
      linarith [hd]
    have hz : 1 < leverageOf (D.atom z) := by
      have hd : 0 < (tripleGram (D.atom x) (D.atom y) (D.atom z) - 1) 2 2 :=
        hchart.diag_pos
      rw [gap_two_two] at hd
      linarith [hd]
    exact ⟨⟨by rw [HeavyAtom]; linarith [hlev], by rw [HeavyAtom]; linarith [hy],
      by rw [HeavyAtom]; linarith [hz], pxy, pxz, pyz⟩, hdet⟩
  · rintro ⟨⟨hx, _, _, pxy, _, _⟩, hdet⟩
    refine (subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mpr
      ⟨?_, pxy, hdet⟩
    rw [HeavyAtom] at hx
    linarith [hx]

/-! ## 2. The trichotomy of a tie -/

/-- **THE TRICHOTOMY.**  At a tie every triple carries a light atom, or an
inadmissible pair, or a nonpositive gap determinant.  Every clause is a
polynomial sign condition on dot products, and the first two are local to a
single atom and a single pair. -/
theorem isTie_triple_trichotomy (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ LiveTriple D x y z
      ∨ tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_le] at hcon
  exact htie.2 _ (card_triple_eq hxy hxz hyz)
    ((posDef_subsetSum_iff_live_and_gapDet D x y z hxy hxz hyz).mpr
      ⟨hcon.1, hcon.2⟩)

/-- **EVERY LIVE TRIANGLE OF A TIE IS FLAT.**  A live triple at a tie has
nonpositive gap determinant. -/
theorem isTie_live_gapDet_nonpos (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hlive : LiveTriple D x y z) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 :=
  (isTie_triple_trichotomy D htie hxy hxz hyz).resolve_left (not_not.mpr hlive)

/-- **THE FOUR-VERTEX SATURATION.**  Four heavy atoms that are pairwise
admissible carry four live triples, so at a tie ALL FOUR of their gap
determinants are nonpositive.  Four simultaneous polynomial inequalities in
the dot products of four atoms, forced by the tie alone. -/
theorem isTie_heavyFour_admissible_gapDet_nonpos (D : WeightedDesign m 3)
    (htie : IsTie D) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hha : HeavyAtom D a) (hhb : HeavyAtom D b) (hhc : HeavyAtom D c)
    (hhd : HeavyAtom D d)
    (pab : AdmissiblePair (D.atom a) (D.atom b))
    (pac : AdmissiblePair (D.atom a) (D.atom c))
    (pad : AdmissiblePair (D.atom a) (D.atom d))
    (pbc : AdmissiblePair (D.atom b) (D.atom c))
    (pbd : AdmissiblePair (D.atom b) (D.atom d))
    (pcd : AdmissiblePair (D.atom c) (D.atom d)) :
    tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0
      ∧ tripleGapDet (D.atom a) (D.atom b) (D.atom d) ≤ 0
      ∧ tripleGapDet (D.atom a) (D.atom c) (D.atom d) ≤ 0
      ∧ tripleGapDet (D.atom b) (D.atom c) (D.atom d) ≤ 0 :=
  ⟨isTie_live_gapDet_nonpos D htie hab hac hbc ⟨hha, hhb, hhc, pab, pac, pbc⟩,
   isTie_live_gapDet_nonpos D htie hab had hbd ⟨hha, hhb, hhd, pab, pad, pbd⟩,
   isTie_live_gapDet_nonpos D htie hac had hcd ⟨hha, hhc, hhd, pac, pad, pcd⟩,
   isTie_live_gapDet_nonpos D htie hbc hbd hcd ⟨hhb, hhc, hhd, pbc, pbd, pcd⟩⟩

/-! ## 3. The exact zero of the dominating triple -/

/-- **A POSITIVE SEMIDEFINITE FORM WITH POSITIVE DETERMINANT IS POSITIVE
DEFINITE.**  Every eigenvalue is nonnegative and their product is positive,
so none of them vanishes. -/
theorem posDef_of_posSemidef_of_det_pos {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hdet : 0 < A.det) :
    A.PosDef := by
  classical
  rw [hA.1.posDef_iff_eigenvalues_pos]
  intro i
  rcases eq_or_lt_of_le (hA.eigenvalues_nonneg i) with hzero | hpos
  · exfalso
    have hprod : A.det = ∏ j, hA.1.eigenvalues j := hA.1.det_eq_prod_eigenvalues
    have hvanish : (∏ j, hA.1.eigenvalues j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero.symm
    rw [hprod, hvanish] at hdet
    exact lt_irrefl 0 hdet
  · exact hpos

/-- **THE EXACT ZERO.**  The dominating triple of a tie has gap determinant
EXACTLY zero.  Weak domination makes the gap positive semidefinite, so its
determinant is nonnegative; and a positive semidefinite `3×3` form with
positive determinant is positive definite, which the tie forbids.  The tie
therefore lives on the polynomial hypersurface `tripleGapDet = 0`. -/
theorem dominating_triple_gapDet_eq_zero (D : WeightedDesign m 3)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) = 0 := by
  classical
  have hpsd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef := hdom
  have hdet : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).det
      = tripleGapDet (D.atom x) (D.atom y) (D.atom z) :=
    subsetSum_gapDet_eq_tripleGapDet D x y z hxy hxz hyz
  have hnn : 0 ≤ tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
    rw [← hdet]
    exact hpsd.det_nonneg
  rcases eq_or_lt_of_le hnn with heq | hpos
  · exact heq.symm
  · exfalso
    refine htie.2 _ (card_triple_eq hxy hxz hyz) ?_
    refine posDef_of_posSemidef_of_det_pos hpsd ?_
    rw [hdet]
    exact hpos

/-! ## 4. The bracket identity of the dominating triple -/

/-- **THE BRACKET IDENTITY.**  With the gap determinant gone, the shift
expansion of the dominating triple is an IDENTITY:

  `[C]² = ℓ_x + ℓ_y + ℓ_z − 2 + (p_{xy} + p_{xz} + p_{yz})` ,

the leverage total less two plus the pair minor sum.  No inequality is
spent: the tie supplies the vanishing determinant, and the second invariant
of the gap is exactly the pair minor sum. -/
theorem dominating_triple_bracket_identity (D : WeightedDesign m 3)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    atomBracket D x y z ^ 2
      = leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)
          - 2
        + (pairGapMinor (D.atom x) (D.atom y)
          + pairGapMinor (D.atom x) (D.atom z)
          + pairGapMinor (D.atom y) (D.atom z)) := by
  classical
  set G : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({x, y, z} : Finset (Fin m)) - 1 with hG
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y)
        + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  -- the shifted determinant is the squared bracket
  have hshift := det_shift_one G
  have hone : G + 1 = subsetSum D ({x, y, z} : Finset (Fin m)) := by
    rw [hG]; abel
  have hdetbr : (subsetSum D ({x, y, z} : Finset (Fin m))).det
      = atomBracket D x y z ^ 2 := by
    rw [hsum, det_tripleSum_eq_bracket_sq, atomBracket]
  rw [hone, hdetbr] at hshift
  -- the trace of the gap is the leverage total less three
  have htrG : Matrix.trace G
      = leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)
        - 3 := by
    rw [hG, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hsum,
      Matrix.trace_add, Matrix.trace_add, trace_atomMatrix, trace_atomMatrix,
      trace_atomMatrix]
    norm_num
  -- the second invariant of the gap is the pair minor sum
  have he2 : ((Matrix.trace G) ^ 2 - Matrix.trace (G * G)) / 2
      = pairGapMinor (D.atom x) (D.atom y)
        + pairGapMinor (D.atom x) (D.atom z)
        + pairGapMinor (D.atom y) (D.atom z) := by
    rw [hG, hsum, pairGapMinor, pairGapMinor, pairGapMinor]
    simp [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply,
      leverageOf, dotProduct, Fin.sum_univ_three]
    ring
  -- and the top invariant vanishes at a tie
  have hdet0 : G.det = 0 := by
    rw [hG, subsetSum_gapDet_eq_tripleGapDet D x y z hxy hxz hyz]
    exact dominating_triple_gapDet_eq_zero D htie hxy hxz hyz hdom
  rw [he2, htrG, hdet0] at hshift
  linarith [hshift]

/-- **THE PAIR MINOR SUM OF A TIE IS NONNEGATIVE.**  The landed sharp
bracket floor of a weak dominator says exactly this, once the bracket
identity is in hand. -/
theorem dominating_triple_pairMinor_sum_nonneg (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin 6))) :
    0 ≤ pairGapMinor (D.atom x) (D.atom y)
      + pairGapMinor (D.atom x) (D.atom z)
      + pairGapMinor (D.atom y) (D.atom z) := by
  have hid := dominating_triple_bracket_identity D htie hxy hxz hyz hdom
  have hfloor := dominator_bracket_floor_sharp D hxy hxz hyz hdom
  linarith [hid, hfloor]

/-- **THE SHARP FLOOR IS THE PAIR MINOR SUM.**  At the dominating triple of
a tie the landed sharp bracket floor and the nonnegativity of the pair minor
sum are the SAME statement — the floor spends no slack there. -/
theorem dominating_triple_bracket_sharp_iff (D : WeightedDesign m 3)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 2
        ≤ atomBracket D x y z ^ 2)
      ↔ 0 ≤ pairGapMinor (D.atom x) (D.atom y)
        + pairGapMinor (D.atom x) (D.atom z)
        + pairGapMinor (D.atom y) (D.atom z) := by
  rw [dominating_triple_bracket_identity D htie hxy hxz hyz hdom]
  constructor <;> intro h <;> linarith [h]

/-! ## 5. The corner instance -/

/-- **THE CORNER TRIPLE IS FLAT.**  The `Z1` corner triple of a tie has gap
determinant zero: its gap is a nonnegative multiple of a rank-one atom, so
it dominates weakly, and the exact zero applies. -/
theorem corner_triple_gapDet_eq_zero (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) = 0 := by
  refine dominating_triple_gapDet_eq_zero D htie hxy hxz hyz ?_
  show (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef
  rw [hgap]
  exact (posSemidef_atomMatrix u).smul hlam

/-- **THE CORNER BRACKET IDENTITY.**  At a `Z1` corner the squared bracket
of the inside triple is the leverage total less two plus the pair minor
sum — with the erased atom unit and orthogonal to the other two, this reads
the corner scale directly. -/
theorem corner_bracket_identity (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    atomBracket D x y z ^ 2
      = leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)
          - 2
        + (pairGapMinor (D.atom x) (D.atom y)
          + pairGapMinor (D.atom x) (D.atom z)
          + pairGapMinor (D.atom y) (D.atom z)) := by
  refine dominating_triple_bracket_identity D htie hxy hxz hyz ?_
  show (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosSemidef
  rw [hgap]
  exact (posSemidef_atomMatrix u).smul hlam

end Gtz

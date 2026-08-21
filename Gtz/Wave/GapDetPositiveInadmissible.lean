/-
# A positive gap determinant at a tie makes all three pairs inadmissible

The landed Sylvester criterion decides strict domination by an ORDERED chain:
`l_a > 1`, then `q_ab > 0`, then `D_abc > 0`.  A tie refuses the conclusion, so
at a tie the chain must break somewhere.  If the atoms are strictly heavy the
first link holds, and if the gap determinant is positive the third link holds, so
the SECOND link breaks:

  **`Gtz.forall_pairGapMinor_nonpos_of_gapDet_pos`:  at a tie, a triple whose
  atoms are strictly heavy and whose gap determinant is positive has ALL THREE of
  its pair minors nonpositive.**

All three, not one: the chain can be started at any of the three atoms and read
through any of the three pairs, and the gap determinant is symmetric
(`Gtz.tripleGapDet_swap`, `Gtz.tripleGapDet_rotate`).

## What it buys at `(6,3)`

Question 7.5(b) of the survey asks whether an inadmissible pair of a boundary
system is parallel.  Granting it, the theorem above turns one positive gap
determinant into a PARALLEL PAIR, which is the survey's hinge for that design:

  **`Gtz.exists_parallel_pair_of_q75b_of_gapDet_pos`** .

So at a strictly heavy `(6,3)` tie the hinge follows from Question 7.5(b) at any
triple whose gap determinant is positive.  The contrapositive is the branch-B
picture the campaign already knows, now proved rather than assumed:

  **`Gtz.tripleGapDet_nonpos_of_admissible_of_heavy`:  at a strictly heavy tie
  whose pairs are all admissible, EVERY triple has nonpositive gap
  determinant.**

## The volume reading, and the size-six consequence

The landed third-invariant identity writes the gap determinant in volume
vocabulary,

  `D_abc = V − W + L − 1` ,   `V = [g_a,g_b,g_c]²` ,
  `W = w_ab + w_ac + w_bc` ,  `L = l_a + l_b + l_c` ,

so a nonpositive gap determinant is a CEILING on the squared volume,
`V ≤ W − L + 1`.  Against the volume floor
`Gtz.exists_sq_tripleBracket_ge_sixThree`, which says some triple of a `(6,3)`
design has `V ≥ 27/20`, the two meet:

  **`Gtz.exists_areaSum_ge_leverageSum_add_of_admissible_sixThree`:  a strictly
  heavy `(6,3)` tie with all pair minors positive carries a triple with**
  `w_ab + w_ac + w_bc ≥ l_a + l_b + l_c + 7/20` .

The constant `7/20` is `27/C(6,3) − 1` and it is positive exactly because
`C(6,3) = 20 < 27`.  At `(5,3)` the same reading gives `17/10`
(`Gtz.exists_areaSum_ge_leverageSum_add_of_admissible_fiveThree`), and at `(7,3)`
the floor drops below one and the argument is silent.  So this is a necessary
condition on branch B — Question 7.5(a) of the survey — whose constant carries
the size.

[MEASURED, exact rational arithmetic on the `(5,3)` diamond.  Every one of its
ten pair minors is positive (minimum `3/4`) and every one of its ten atoms is
strictly heavy, so it sits in branch B, and every one of its ten gap
determinants is `0` or `−10` — nonpositive, as the theorem requires.  Its
squared-area sums and leverage sums are `W = 20, L = 17/2` at `{0,1,2}` and
`W = 55/2, L = 39/4` at `{1,2,3}`, so `W − L = 23/2` and `W − L = 71/4`, both
far above the `17/10` the size-five reading demands.  The bound is therefore
correct and not tight at the diamond.]
-/
import Gtz.Wave.VolumeFloorSizeSix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The gap determinant is symmetric -/

/-- Exchanging the last two atoms leaves the gap determinant alone. -/
theorem tripleGapDet_swap (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleGapDet leftVec rightVec midVec = tripleGapDet leftVec midVec rightVec := by
  simp only [tripleGapDet, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- Rotating the three atoms leaves the gap determinant alone. -/
theorem tripleGapDet_rotate (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleGapDet midVec rightVec leftVec = tripleGapDet leftVec midVec rightVec := by
  simp only [tripleGapDet, leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-! ## 2. The producer -/

/-- **THE SECOND LINK BREAKS.**  At a design where a triple fails to dominate
strictly, strict heaviness supplies the first link of the Sylvester chain and a
positive gap determinant supplies the third, so the pair minor between the first
two atoms is nonpositive. -/
theorem pairGapMinor_nonpos_of_gapDet_pos (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : 1 < leverageOf (D.atom x))
    (hnostrict : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef)
    (hgap : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    pairGapMinor (D.atom x) (D.atom y) ≤ 0 := by
  by_contra hcon
  push Not at hcon
  refine hnostrict ?_
  rw [subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz,
    tripleGram_posDef_iff_pairVocabulary]
  exact ⟨by linarith, hcon, hgap⟩

/-- **ALL THREE PAIRS OF SUCH A TRIPLE ARE INADMISSIBLE.**  The chain reads
through any of the three pairs, and the gap determinant does not notice the
relabelling. -/
theorem forall_pairGapMinor_nonpos_of_gapDet_pos (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavyX : 1 < leverageOf (D.atom x)) (hheavyY : 1 < leverageOf (D.atom y))
    (hnostrict : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef)
    (hgap : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    pairGapMinor (D.atom x) (D.atom y) ≤ 0
      ∧ pairGapMinor (D.atom x) (D.atom z) ≤ 0
      ∧ pairGapMinor (D.atom y) (D.atom z) ≤ 0 := by
  refine ⟨pairGapMinor_nonpos_of_gapDet_pos D hxy hxz hyz hheavyX hnostrict hgap, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    refine hnostrict ?_
    rw [subsetSum_posDef_iff_tripleGram_swap D x y z hxy hxz hyz,
      tripleGram_posDef_iff_pairVocabulary]
    exact ⟨by linarith, hcon, by rwa [tripleGapDet_swap]⟩
  · by_contra hcon
    push Not at hcon
    refine hnostrict ?_
    rw [subsetSum_posDef_iff_tripleGram_rotate D x y z hxy hxz hyz,
      tripleGram_posDef_iff_pairVocabulary]
    exact ⟨by linarith, hcon, by rwa [tripleGapDet_rotate]⟩

/-! ## 3. The hinge from Question 7.5(b) -/

/-- **ONE POSITIVE GAP DETERMINANT PLUS QUESTION 7.5(b) IS A PARALLEL PAIR.**  At a
strictly heavy tie, a triple with positive gap determinant carries an
inadmissible pair, and the question turns that pair parallel.  At `(6,3)` a
parallel pair is exactly the survey's hinge for that design. -/
theorem exists_parallel_pair_of_q75b_of_gapDet_pos (D : WeightedDesign m 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnostrict : ∀ C : Finset (Fin m), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (hq75b : ∀ p q : Fin m, p ≠ q → pairGapMinor (D.atom p) (D.atom q) ≤ 0 →
      crossNormSq (D.atom p) (D.atom q) = 0)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hgap : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    ∃ p q : Fin m, p ≠ q ∧ crossNormSq (D.atom p) (D.atom q) = 0 := by
  classical
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hinadm := pairGapMinor_nonpos_of_gapDet_pos D hxy hxz hyz (hheavy x)
    (hnostrict _ hcard) hgap
  exact ⟨x, y, hxy, hq75b x y hxy hinadm⟩

/-! ## 4. Branch B: every gap determinant is nonpositive -/

/-- **THE BRANCH-B CEILING.**  At a strictly heavy tie whose pairs are all
admissible, every triple has nonpositive gap determinant.  This is the
contrapositive of the producer, and it is what the campaign's branch B assumes
about its own triples. -/
theorem tripleGapDet_nonpos_of_admissible_of_heavy (D : WeightedDesign m 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnostrict : ∀ C : Finset (Fin m), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (hadmissible : ∀ p q : Fin m, p ≠ q → 0 < pairGapMinor (D.atom p) (D.atom q))
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hinadm := pairGapMinor_nonpos_of_gapDet_pos D hxy hxz hyz (hheavy x)
    (hnostrict _ hcard) hcon
  exact absurd hinadm (not_le.mpr (hadmissible x y hxy))

/-- **THE BRANCH-B CEILING IN VOLUME VOCABULARY.**  A nonpositive gap determinant
caps the squared volume by the squared-area sum less the leverage sum plus
one. -/
theorem sq_tripleBracket_le_of_admissible_of_heavy (D : WeightedDesign m 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnostrict : ∀ C : Finset (Fin m), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (hadmissible : ∀ p q : Fin m, p ≠ q → 0 < pairGapMinor (D.atom p) (D.atom q))
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
      ≤ (crossNormSq (D.atom x) (D.atom y) + crossNormSq (D.atom x) (D.atom z)
          + crossNormSq (D.atom y) (D.atom z))
        - (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)) + 1 := by
  have hceiling := tripleGapDet_nonpos_of_admissible_of_heavy D hheavy hnostrict hadmissible
    hxy hxz hyz
  have hthird := tripleGapDet_eq_thirdInvariant (D.atom x) (D.atom y) (D.atom z)
  rw [triplePairAreaSum, tripleLeverageSum] at hthird
  linarith

/-! ## 5. The size-six consequence -/

/-- **BRANCH B AT `(6,3)` CARRIES A WIDE TRIPLE.**  The volume floor gives a triple
with squared volume at least `27/20`, and the branch-B ceiling turns that into a
gap of `7/20` between the triple's squared-area sum and its leverage sum.  The
constant is `27/C(6,3) − 1`, positive exactly because `C(6,3) = 20 < 27`. -/
theorem exists_areaSum_ge_leverageSum_add_of_admissible_sixThree (D : WeightedDesign 6 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnostrict : ∀ C : Finset (Fin 6), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (hadmissible : ∀ p q : Fin 6, p ≠ q → 0 < pairGapMinor (D.atom p) (D.atom q)) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ leverageOf (D.atom a) + leverageOf (D.atom b) + leverageOf (D.atom c) + 7 / 20
        ≤ crossNormSq (D.atom a) (D.atom b) + crossNormSq (D.atom a) (D.atom c)
          + crossNormSq (D.atom b) (D.atom c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hvolume⟩ := exists_sq_tripleBracket_ge_sixThree D
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  have hceiling := sq_tripleBracket_le_of_admissible_of_heavy D hheavy hnostrict hadmissible
    hab hac hbc
  linarith

/-- **BRANCH B AT `(5,3)` CARRIES A WIDER TRIPLE.**  The same reading with
`27/C(5,3) − 1 = 17/10`. -/
theorem exists_areaSum_ge_leverageSum_add_of_admissible_fiveThree (D : WeightedDesign 5 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnostrict : ∀ C : Finset (Fin 5), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (hadmissible : ∀ p q : Fin 5, p ≠ q → 0 < pairGapMinor (D.atom p) (D.atom q)) :
    ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ leverageOf (D.atom a) + leverageOf (D.atom b) + leverageOf (D.atom c) + 17 / 10
        ≤ crossNormSq (D.atom a) (D.atom b) + crossNormSq (D.atom a) (D.atom c)
          + crossNormSq (D.atom b) (D.atom c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hvolume⟩ := exists_sq_tripleBracket_ge_fiveThree D
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  have hceiling := sq_tripleBracket_le_of_admissible_of_heavy D hheavy hnostrict hadmissible
    hab hac hbc
  linarith

/-- **THE FIRST TWO SYLVESTER INVARIANTS TOTAL AT LEAST THE SIZE CONSTANT.**
Rewriting the squared areas as pair minors, the wide triple of a branch-B `(6,3)`
tie has `e₁ + e₂ ≥ 7/20`, where `e₁ = l_a + l_b + l_c − 3` and
`e₂ = q_ab + q_ac + q_bc`.  Equivalently, the triple's whole Sylvester overshoot
is carried by its first two invariants, because branch B forces the third to be
nonpositive. -/
theorem exists_pairMinorSum_ge_of_admissible_sixThree (D : WeightedDesign 6 3)
    (hheavy : ∀ c, 1 < leverageOf (D.atom c))
    (hnostrict : ∀ C : Finset (Fin 6), C.card = 3 → ¬ (subsetSum D C - 1).PosDef)
    (hadmissible : ∀ p q : Fin 6, p ≠ q → 0 < pairGapMinor (D.atom p) (D.atom q)) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ 7 / 20
        ≤ (leverageOf (D.atom a) + leverageOf (D.atom b) + leverageOf (D.atom c) - 3)
          + (pairGapMinor (D.atom a) (D.atom b) + pairGapMinor (D.atom a) (D.atom c)
            + pairGapMinor (D.atom b) (D.atom c)) := by
  obtain ⟨a, b, c, hab, hac, hbc, hwide⟩ :=
    exists_areaSum_ge_leverageSum_add_of_admissible_sixThree D hheavy hnostrict hadmissible
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [pairGapMinor_eq_crossNormSq, pairGapMinor_eq_crossNormSq, pairGapMinor_eq_crossNormSq]
  linarith

end Gtz

import Gtz.Wave.CellHDowndateLaws
import Gtz.Design.PlaneBranchComplementSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The insertion and downdate ledgers, and what they say about the tie graph

`Gtz.sum_weighted_downdate_det` totals the weighted rank-one DOWNDATES of any
subset gap and lands on `det − e₂`.  Its mirror totals the weighted rank-one
INSERTIONS and lands on `det + e₂`.  Together they are one duality:

  **`Σ_c t_c [det(A + a_c a_cᵀ) + det(A − a_c a_cᵀ)] = 2 det A`**
  **`Σ_c t_c [det(A + a_c a_cᵀ) − det(A − a_c a_cᵀ)] = 2 e₂(A)`**

for EVERY real `3 x 3` matrix `A` and every weighted design — no subset, no
positivity, no invertibility.  The determinant is the even part of the insertion
ledger and the second invariant is its odd part.

## The two specialisations that matter

The insertion ledger is worth most when `A` is the gap of a SMALL set, because
then the inserted determinants are the objects the tie graph is built from.

**At one atom** the inserted determinants are the pair gap determinants, and a
pair gap determinant is minus the pair minor
(`Gtz.det_pairGap_eq_neg_pairGapMinor`).  So the ledger reads
(`Gtz.sum_weight_mul_pairGapMinor`):

  **`Σ_c t_c · pairGapMinor a a_c = ℓ_a − 2`** .

This is the PER-VERTEX refinement of the landed pair-minor budget: weighting the
law by `t_a` and summing over `a` gives `3 − 2 = 1` back.  Where the budget says
the whole graph carries admissible mass one, this says each vertex carries
`ℓ_a − 2`, so **admissibility is a function of leverage**.

**At one pair** the inserted determinants are the triple gap determinants, and
the ledger reads (`Gtz.sum_weight_mul_tripleGapDet_through_pair`):

  **`Σ_c t_c · det(S_{ab} − 1 + a_c a_cᵀ) = 2 − ℓ_a − ℓ_b`** .

The weighted triple-determinant mass through a pair depends on NOTHING but the
pair's two leverages — not on the angle between them, not on the other atoms.

## The producers

Both laws produce, and neither names what it produces.

* `Gtz.exists_pairGapMinor_pos_of_leverage` — if `ℓ_a − 2 + t_a(2ℓ_a − 1) > 0`
  then some atom `c ≠ a` has `0 < pairGapMinor a a_c`: the vertex `a` has an
  ADMISSIBLE EDGE.  The self term is subtracted exactly, `pairGapMinor a a =
  1 − 2ℓ_a`, so the criterion is sharp.
  [MEASURED: the criterion fired at 168198 random designs of sizes four to seven
  and an admissible partner existed at every one, zero failures.]
* `Gtz.exists_tripleGapDet_pos_through_pair` — the same for the pair law, with
  the two doubled-atom determinants subtracted exactly.  Its conclusion is a
  triple gap determinant, which the ordered Sylvester criterion promotes to
  strict domination as soon as the base pair is admissible and heavy.

## Why this is aimed at the theorem

`GtzWeighted 6 3` fails only at a design where no triple dominates.  The second
producer says a pair whose leverage total is small enough must carry a triple
with positive gap determinant; the first says a vertex whose leverage is large
enough must carry an admissible edge.  The two pull in opposite directions on
the same scalar, and the pair-minor budget forces the graph to hold admissible
mass exactly one.  That is the shape a Mantel argument consumes.

[MEASURED: all four ledger identities reproduce at rank error `6.2e-09` or
better over six thousand random designs of sizes three to nine.]
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The insertion ledger and the duality

The rank-one insertion update `Gtz.det_add_atomMatrix_fin_three` is landed; this
section spends it against Parseval. -/

/-- **THE INSERTION LEDGER.**  For every real `3 x 3` matrix and every weighted
design, the weighted total of the rank-one insertions is `det + e₂`.  The mirror
of `Gtz.sum_weighted_downdate_det`. -/
theorem sum_weighted_insertion_det (D : WeightedDesign m 3)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c, D.weight c * (A + atomMatrix (D.atom c)).det
      = A.det + secondInvariantOfThree A := by
  have hterm : ∀ c : Fin m,
      D.weight c * (A + atomMatrix (D.atom c)).det
        = D.weight c * A.det
          + D.weight c * dotProduct (D.atom c) (A.adjugate *ᵥ D.atom c) := by
    intro c; rw [det_add_atomMatrix_fin_three]; ring
  calc ∑ c, D.weight c * (A + atomMatrix (D.atom c)).det
      = (∑ c, D.weight c * A.det)
          + ∑ c, D.weight c * dotProduct (D.atom c) (A.adjugate *ᵥ D.atom c) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => hterm c
    _ = A.det + Matrix.trace A.adjugate := by
        rw [sum_weight_mul_reading_eq_trace D A.adjugate, ← Finset.sum_mul,
          D.weight_sum_one, one_mul]
    _ = A.det + secondInvariantOfThree A := by
        rw [trace_adjugate_eq_secondInvariantOfThree]

/-- The general downdate ledger at an arbitrary matrix, freed from the subset
form it was first proved in. -/
theorem sum_weighted_downdate_det_general (D : WeightedDesign m 3)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c, D.weight c * (A - atomMatrix (D.atom c)).det
      = A.det - secondInvariantOfThree A := by
  have hterm : ∀ c : Fin m,
      D.weight c * (A - atomMatrix (D.atom c)).det
        = D.weight c * A.det
          - D.weight c * dotProduct (D.atom c) (A.adjugate *ᵥ D.atom c) := by
    intro c; rw [det_sub_atomMatrix_fin_three]; ring
  calc ∑ c, D.weight c * (A - atomMatrix (D.atom c)).det
      = (∑ c, D.weight c * A.det)
          - ∑ c, D.weight c * dotProduct (D.atom c) (A.adjugate *ᵥ D.atom c) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => hterm c
    _ = A.det - Matrix.trace A.adjugate := by
        rw [sum_weight_mul_reading_eq_trace D A.adjugate, ← Finset.sum_mul,
          D.weight_sum_one, one_mul]
    _ = A.det - secondInvariantOfThree A := by
        rw [trace_adjugate_eq_secondInvariantOfThree]

/-- **THE DETERMINANT IS THE EVEN PART.**  Insertion plus downdate, weighted over
the design, doubles the determinant and forgets the second invariant. -/
theorem sum_weighted_insertion_add_downdate (D : WeightedDesign m 3)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c, D.weight c
        * ((A + atomMatrix (D.atom c)).det + (A - atomMatrix (D.atom c)).det)
      = 2 * A.det := by
  have hsplit : ∑ c, D.weight c
      * ((A + atomMatrix (D.atom c)).det + (A - atomMatrix (D.atom c)).det)
      = (∑ c, D.weight c * (A + atomMatrix (D.atom c)).det)
        + ∑ c, D.weight c * (A - atomMatrix (D.atom c)).det := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, sum_weighted_insertion_det, sum_weighted_downdate_det_general]; ring

/-- **THE SECOND INVARIANT IS THE ODD PART.** -/
theorem sum_weighted_insertion_sub_downdate (D : WeightedDesign m 3)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c, D.weight c
        * ((A + atomMatrix (D.atom c)).det - (A - atomMatrix (D.atom c)).det)
      = 2 * secondInvariantOfThree A := by
  have hsplit : ∑ c, D.weight c
      * ((A + atomMatrix (D.atom c)).det - (A - atomMatrix (D.atom c)).det)
      = (∑ c, D.weight c * (A + atomMatrix (D.atom c)).det)
        - ∑ c, D.weight c * (A - atomMatrix (D.atom c)).det := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, sum_weighted_insertion_det, sum_weighted_downdate_det_general]; ring

/-! ## 3. The two small gaps in closed form -/

/-- **A PAIR GAP DETERMINANT IS MINUS THE PAIR MINOR.**  Hypothesis-free. -/
theorem det_pairGap_eq_neg_pairGapMinor (a b : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b - 1).det = -pairGapMinor a b := by
  simp [Matrix.det_fin_three, pairGapMinor, leverageOf, atomMatrix,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- The single-atom gap totals `2 − ℓ` under the ledger. -/
theorem singleGap_det_add_secondInvariant (a : Fin 3 → ℝ) :
    (atomMatrix a - 1).det + secondInvariantOfThree (atomMatrix a - 1)
      = 2 - leverageOf a := by
  simp [Matrix.det_fin_three, secondInvariantOfThree, leverageOf, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_three]
  ring

/-- The pair gap totals `2 − ℓ_a − ℓ_b` under the ledger. -/
theorem pairGap_det_add_secondInvariant (a b : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b - 1).det
        + secondInvariantOfThree (atomMatrix a + atomMatrix b - 1)
      = 2 - leverageOf a - leverageOf b := by
  simp [Matrix.det_fin_three, secondInvariantOfThree, leverageOf, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_three]
  ring

/-! ## 4. The per-vertex law -/

/-- **THE PER-VERTEX PAIR-MINOR LAW.**  The weighted total of the pair minors at
one atom is that atom's leverage less two.

This refines the pair-minor budget: weighting by `t_a` and summing over `a` gives
`Σ t_a ℓ_a − 2 = 3 − 2 = 1` back.  Admissible mass at a vertex is a function of
its leverage alone. -/
theorem sum_weight_mul_pairGapMinor (D : WeightedDesign m 3) (a : Fin m) :
    ∑ c, D.weight c * pairGapMinor (D.atom a) (D.atom c)
      = leverageOf (D.atom a) - 2 := by
  have hins := sum_weighted_insertion_det D (atomMatrix (D.atom a) - 1)
  have hterm : ∀ c : Fin m,
      D.weight c * (atomMatrix (D.atom a) - 1 + atomMatrix (D.atom c)).det
        = -(D.weight c * pairGapMinor (D.atom a) (D.atom c)) := by
    intro c
    have hre : atomMatrix (D.atom a) - 1 + atomMatrix (D.atom c)
        = atomMatrix (D.atom a) + atomMatrix (D.atom c) - 1 := by abel
    rw [hre, det_pairGap_eq_neg_pairGapMinor]; ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, singleGap_det_add_secondInvariant] at hins
  have hneg : ∑ c, -(D.weight c * pairGapMinor (D.atom a) (D.atom c))
      = -∑ c, D.weight c * pairGapMinor (D.atom a) (D.atom c) := by
    rw [Finset.sum_neg_distrib]
  rw [hneg] at hins
  linarith

/-- The self term of the per-vertex law, in closed form. -/
theorem pairGapMinor_self (a : Fin 3 → ℝ) :
    pairGapMinor a a = 1 - 2 * leverageOf a := by
  simp only [pairGapMinor, leverageOf, dotProduct, Fin.sum_univ_three]; ring

/-- **A HEAVY ENOUGH VERTEX HAS AN ADMISSIBLE EDGE.**  With the self term
subtracted exactly, a positive residue forces some OTHER atom to be an
admissible partner — and names none of them.

[MEASURED: fired at 168198 random designs of sizes four to seven with zero
failures.] -/
theorem exists_pairGapMinor_pos_of_leverage (D : WeightedDesign m 3) (a : Fin m)
    (hpos : 0 < leverageOf (D.atom a) - 2
      + D.weight a * (2 * leverageOf (D.atom a) - 1)) :
    ∃ c, c ≠ a ∧ 0 < pairGapMinor (D.atom a) (D.atom c) := by
  by_contra hcon
  push_neg at hcon
  have hsplit : (∑ c ∈ Finset.univ.erase a,
      D.weight c * pairGapMinor (D.atom a) (D.atom c))
      + D.weight a * pairGapMinor (D.atom a) (D.atom a)
      = ∑ c, D.weight c * pairGapMinor (D.atom a) (D.atom c) :=
    Finset.sum_erase_add _ _ (Finset.mem_univ a)
  rw [sum_weight_mul_pairGapMinor, pairGapMinor_self] at hsplit
  have hnp : ∑ c ∈ Finset.univ.erase a,
      D.weight c * pairGapMinor (D.atom a) (D.atom c) ≤ 0 :=
    Finset.sum_nonpos fun c hc =>
      mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le
        (hcon c (Finset.ne_of_mem_erase hc))
  nlinarith [hsplit, hnp]

/-! ## 5. The per-pair law -/

/-- **THE PER-PAIR TRIPLE-DETERMINANT LAW.**  The weighted total of the triple
gap determinants through a pair is two less the pair's leverage total.

Nothing else survives: not the angle between the two atoms, not the positions of
the remaining atoms. -/
theorem sum_weight_mul_tripleGapDet_through_pair (D : WeightedDesign m 3)
    (a b : Fin m) :
    ∑ c, D.weight c
        * (atomMatrix (D.atom a) + atomMatrix (D.atom b) - 1
            + atomMatrix (D.atom c)).det
      = 2 - leverageOf (D.atom a) - leverageOf (D.atom b) := by
  rw [sum_weighted_insertion_det D (atomMatrix (D.atom a) + atomMatrix (D.atom b) - 1),
    pairGap_det_add_secondInvariant]

/-- **A LIGHT ENOUGH PAIR CARRIES A POSITIVE TRIPLE.**  With the two doubled-atom
terms subtracted exactly, a positive residue forces some atom outside the pair to
close a triple of positive gap determinant — and names none of them.

Where the base pair is admissible and heavy the ordered Sylvester criterion
promotes that determinant to strict domination, so the conclusion is a dominating
triple and the design is no tie. -/
theorem exists_tripleGapDet_pos_through_pair (D : WeightedDesign m 3)
    {a b : Fin m} (hab : b ≠ a)
    (hpos : D.weight a
          * (atomMatrix (D.atom a) + atomMatrix (D.atom b) - 1
              + atomMatrix (D.atom a)).det
        + D.weight b
          * (atomMatrix (D.atom a) + atomMatrix (D.atom b) - 1
              + atomMatrix (D.atom b)).det
      < 2 - leverageOf (D.atom a) - leverageOf (D.atom b)) :
    ∃ c, c ≠ a ∧ c ≠ b
      ∧ 0 < (atomMatrix (D.atom a) + atomMatrix (D.atom b) - 1
              + atomMatrix (D.atom c)).det := by
  classical
  by_contra hcon
  push_neg at hcon
  set f : Fin m → ℝ := fun c => D.weight c
    * (atomMatrix (D.atom a) + atomMatrix (D.atom b) - 1
        + atomMatrix (D.atom c)).det with hf
  have hbmem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab, Finset.mem_univ b⟩
  have h1 : (∑ c ∈ Finset.univ.erase a, f c) + f a = ∑ c, f c :=
    Finset.sum_erase_add _ _ (Finset.mem_univ a)
  have h2 : (∑ c ∈ (Finset.univ.erase a).erase b, f c) + f b
      = ∑ c ∈ Finset.univ.erase a, f c :=
    Finset.sum_erase_add _ _ hbmem
  have hnp : ∑ c ∈ (Finset.univ.erase a).erase b, f c ≤ 0 := by
    refine Finset.sum_nonpos fun c hc => ?_
    have hcb : c ≠ b := Finset.ne_of_mem_erase hc
    have hca : c ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    exact mul_nonpos_of_nonneg_of_nonpos (D.weight_pos c).le (hcon c hca hcb)
  have htot : ∑ c, f c = 2 - leverageOf (D.atom a) - leverageOf (D.atom b) :=
    sum_weight_mul_tripleGapDet_through_pair D a b
  rw [hf] at h1 h2 hnp htot
  linarith [h1, h2, hnp, htot, hpos]

end Gtz

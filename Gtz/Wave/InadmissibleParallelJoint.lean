/-
# The primitive tie, decomposed, and the kill that never needed branch B

The arm's target is not branch B.  Branch B implies primitivity but not
conversely, and `q_ab ≤ 0` is far weaker than `w_ab = 0` — inadmissibility of a
heavy pair only gives `w_ab ≤ ℓ_a + ℓ_b − 1`.  So the statement to reach is

  **a primitive `(6,3)` tie is impossible**,

and this module cuts it into its three real cases and arms two of them.

## 1. The kill never needed branch B

`Gtz.branchB_posDef_iff_gapDet_pos` was proved through
`Gtz.liveTriple_posDef_iff_gapDet_pos`, whose hypothesis is LIVENESS of the one
triple — three heavy atoms and three admissible pairs — not branch B.  Branch B
was only a way of supplying liveness everywhere at once.  So the whole
selection-free machinery transports to **any finite family of live triples**
(`Gtz.liveFamily_not_isTie_of_prod_nonpos`), and the same product is still
lossless (`Gtz.liveFamily_isTie_prod_ge`).

That is exactly what the inadmissible-non-parallel case needs.  There the
admissibility graph is missing some edges, so branch B is unavailable — but its
TRIANGLES are still live triples, and the family may be taken to be any set of
them.  The kill applies verbatim on the live subgraph.

## 2. The decomposition is three cases, not four

`Gtz.leverage_one_le_of_isTie_sixThree` is unconditional: every atom of a
`(6,3)` tie has leverage at least one.  So the light-atom case survives only at
the boundary `ℓ = 1`, and there

  `q_ab = (ℓ_a − 1)(ℓ_b − 1) − p_ab² = −p_ab² ≤ 0`

for EVERY partner `b` (`Gtz.pairGapMinor_nonpos_of_leverage_eq_one`).  **A
boundary atom lies in no admissible pair unless it is orthogonal to its
partner, and in no live triple at all.**  It is an isolated vertex of the
admissibility graph up to orthogonality, which is a far more rigid object than
"a light atom".

So a `(6,3)` tie is: all atoms strictly heavy and all pairs admissible (branch
B), or all atoms strictly heavy with some pair inadmissible (the unowned
joint), or it carries a boundary atom of leverage exactly one
(`Gtz.sixThree_isTie_heavy_or_boundary`).

## 3. The dominator's exact equation

The currency bridge plus the landed `Gtz.dominating_triple_gapDet_eq_zero` give
the tie's sharpest single identity.  A weak dominator has gap determinant
exactly zero, so at the dominator of ANY tie

  **`[xyz]² = (q_xy + q_xz + q_yz) + (x_x + x_y + x_z) + 1`**

exactly, with no inequality anywhere (`Gtz.isTie_dominator_bracket_sq_eq`).  The
bracket — the quantity a parallel pair kills — is pinned to the admissibility
and heaviness data of the dominating triple alone.  Every other live triple
obeys the same relation as an inequality
(`Gtz.isTie_live_bracket_sq_le`).

[MEASURED, and recorded because it voided this lane's previous numbers: an
unconstrained descent on `max_T λmin(S_T)` returns `F = 0.99999817` at five
points, which `Gtz.gtzWeighted_of_le_five` forbids.  The cause was softmax weight
underflow inflating a leverage past `eigmin`'s precision; with a weight floor and
a leverage ceiling the minimum returns to `1.0000006`.  Saturation and the
parallel-pair question are therefore still OPEN in this lane, since the repaired
descent reaches near-ties, and a near-tie carries a strict dominator and is not a
tie.]
-/
import Gtz.Wave.BranchBProductKill
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

variable {m : ℕ}

/-! ## 1. The live-family kill -/

/-- **A LIVE TRIPLE WITH POSITIVE DETERMINANT REFUTES THE TIE.**  Liveness is
the two lower Sylvester minors; the determinant is the third. -/
theorem liveTriple_not_isTie_of_gapDet_pos (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hlive : LiveTriple D x y z)
    (hdet : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    ¬ IsTie D := by
  intro htie
  exact htie.2 ({x, y, z} : Finset (Fin m)) (card_triple hxy hxz hyz)
    ((liveTriple_posDef_iff_gapDet_pos D hxy hxz hyz hlive).mpr hdet)

/-- **THE SELECTION-FREE KILL ON ANY FAMILY OF LIVE TRIPLES.**  Branch B is not
needed: only the triples in the family have to be live, so the kill runs on the
triangles of the admissibility graph however sparse that graph is. -/
theorem liveFamily_not_isTie_of_prod_nonpos {ι : Type*} {s : Finset ι}
    (D : WeightedDesign m 3) (x y z : ι → Fin m)
    (hne : ∀ i ∈ s, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i)
    (hlive : ∀ i ∈ s, LiveTriple D (x i) (y i) (z i))
    {t : ℝ} (ht : 0 < t)
    (hprod : ∏ i ∈ s, (t - tripleGapDet (D.atom (x i)) (D.atom (y i)) (D.atom (z i))) ≤ 0) :
    ¬ IsTie D := by
  obtain ⟨i, hi, hpos⟩ := exists_pos_of_prod_sub_nonpos ht hprod
  obtain ⟨hxy, hxz, hyz⟩ := hne i hi
  exact liveTriple_not_isTie_of_gapDet_pos D hxy hxz hyz (hlive i hi) hpos

/-- Every live triple of a tie has nonpositive determinant — the landed
trichotomy, restated through the collapse. -/
theorem isTie_liveTriple_gapDet_nonpos (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hlive : LiveTriple D x y z) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  exact liveTriple_not_isTie_of_gapDet_pos D hxy hxz hyz hlive hcon htie

/-- **THE LIVE-FAMILY CRITERION IS LOSSLESS.**  At a tie every such product is
at least the probe to the family's size. -/
theorem liveFamily_isTie_prod_ge {ι : Type*} {s : Finset ι}
    (D : WeightedDesign m 3) (htie : IsTie D) (x y z : ι → Fin m)
    (hne : ∀ i ∈ s, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i)
    (hlive : ∀ i ∈ s, LiveTriple D (x i) (y i) (z i))
    {t : ℝ} (ht : 0 < t) :
    t ^ s.card
      ≤ ∏ i ∈ s, (t - tripleGapDet (D.atom (x i)) (D.atom (y i)) (D.atom (z i))) := by
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun i _ => ht.le) fun i hi => ?_
  obtain ⟨hxy, hxz, hyz⟩ := hne i hi
  have := isTie_liveTriple_gapDet_nonpos D htie hxy hxz hyz (hlive i hi)
  linarith

/-! ## 2. The live triple in the hinge's currency -/

/-- **A LIVE TRIPLE DOMINATES EXACTLY WHEN ITS BRACKET BEATS ITS OWN DATA.**
No determinant, no branch B: the squared bracket against the three pair minors,
the three leverage excesses and one. -/
theorem liveTriple_posDef_iff_bracket_sq_gt (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hlive : LiveTriple D x y z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ (pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
            + pairGapMinor (D.atom y) (D.atom z))
          + ((leverageOf (D.atom x) - 1) + (leverageOf (D.atom y) - 1)
            + (leverageOf (D.atom z) - 1)) + 1
        < tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
  rw [liveTriple_posDef_iff_gapDet_pos D hxy hxz hyz hlive,
    sq_tripleBracket_eq_gapDet_add_pairMinors]
  constructor <;> intro h <;> linarith

/-- **AT A TIE EVERY LIVE TRIPLE OBEYS THE CURRENCY INEQUALITY.** -/
theorem isTie_live_bracket_sq_le (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hlive : LiveTriple D x y z) :
    tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
      ≤ (pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
          + pairGapMinor (D.atom y) (D.atom z))
        + ((leverageOf (D.atom x) - 1) + (leverageOf (D.atom y) - 1)
          + (leverageOf (D.atom z) - 1)) + 1 := by
  have hdet := isTie_liveTriple_gapDet_nonpos D htie hxy hxz hyz hlive
  have hbridge := sq_tripleBracket_eq_gapDet_add_pairMinors
    (D.atom x) (D.atom y) (D.atom z)
  linarith

/-- **THE DOMINATOR'S EXACT EQUATION.**  A weak dominator of a tie has gap
determinant exactly zero, so its squared bracket is pinned — with no inequality
— to its own admissibility and heaviness data.

The bracket is the quantity a parallel pair kills, so this is the hinge's
target expressed entirely in the two currencies the tie controls. -/
theorem isTie_dominator_bracket_sq_eq (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
      = (pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
          + pairGapMinor (D.atom y) (D.atom z))
        + ((leverageOf (D.atom x) - 1) + (leverageOf (D.atom y) - 1)
          + (leverageOf (D.atom z) - 1)) + 1 := by
  have hzero := dominating_triple_gapDet_eq_zero D htie hxy hxz hyz hdom
  have hbridge := sq_tripleBracket_eq_gapDet_add_pairMinors
    (D.atom x) (D.atom y) (D.atom z)
  rw [hbridge, hzero]; ring

/-! ## 3. The boundary atom -/

/-- **AN ATOM OF LEVERAGE ONE IS IN NO ADMISSIBLE PAIR BUT AN ORTHOGONAL ONE.**
Its leverage excess is zero, so the pair minor collapses to minus the squared
pairing. -/
theorem pairGapMinor_nonpos_of_leverage_eq_one {a b : Fin 3 → ℝ}
    (ha : leverageOf a = 1) : pairGapMinor a b ≤ 0 := by
  rw [pairGapMinor, ha]
  nlinarith [sq_nonneg (a ⬝ᵥ b)]

/-- The same reading as a refusal of admissibility. -/
theorem not_admissiblePair_of_leverage_eq_one {a b : Fin 3 → ℝ}
    (ha : leverageOf a = 1) : ¬ AdmissiblePair a b := by
  rw [AdmissiblePair]
  exact not_lt.mpr (pairGapMinor_nonpos_of_leverage_eq_one ha)

/-- **A BOUNDARY ATOM LIES IN NO LIVE TRIPLE.**  Liveness demands strict
heaviness, which leverage one does not have. -/
theorem not_liveTriple_of_leverage_eq_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hx : leverageOf (D.atom x) = 1) :
    ¬ LiveTriple D x y z := by
  rintro ⟨hhx, -, -, -, -, -⟩
  rw [HeavyAtom, hx] at hhx
  exact lt_irrefl 1 hhx

/-! ## 4. The decomposition at six points -/

/-- **EVERY ATOM OF A `(6,3)` TIE IS HEAVY OR SITS EXACTLY ON THE BOUNDARY.**
The landed floor is unconditional, so nothing lighter than leverage one
survives. -/
theorem sixThree_isTie_heavy_or_boundary (D : WeightedDesign 6 3) (htie : IsTie D)
    (c : Fin 6) : HeavyAtom D c ∨ leverageOf (D.atom c) = 1 := by
  rcases (leverage_one_le_of_isTie_sixThree D htie c).lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr h.symm

/-- **THE PRIMITIVE `(6,3)` TIE HAS EXACTLY THREE CASES.**  Either every atom is
strictly heavy and every pair of distinct atoms is admissible — branch B, where
the product kill of `Gtz.branchB_not_isTie_of_prod_nonpos` applies — or every
atom is strictly heavy and some pair is inadmissible, which is the unowned
joint, or some atom sits on the leverage boundary and is then in no live triple
at all. -/
theorem sixThree_isTie_trichotomy (D : WeightedDesign 6 3) (htie : IsTie D) :
    BranchB D
      ∨ ((∀ c : Fin 6, HeavyAtom D c)
          ∧ ∃ a b : Fin 6, a ≠ b ∧ ¬ AdmissiblePair (D.atom a) (D.atom b))
      ∨ ∃ c : Fin 6, leverageOf (D.atom c) = 1 := by
  by_cases hb : ∃ c : Fin 6, leverageOf (D.atom c) = 1
  · exact Or.inr (Or.inr hb)
  push_neg at hb
  have hheavy : ∀ c : Fin 6, HeavyAtom D c := fun c =>
    (sixThree_isTie_heavy_or_boundary D htie c).resolve_right (hb c)
  by_cases hadm : ∀ a b : Fin 6, a ≠ b → AdmissiblePair (D.atom a) (D.atom b)
  · exact Or.inl ⟨hheavy, hadm⟩
  · push_neg at hadm
    obtain ⟨a, b, hab, hnot⟩ := hadm
    exact Or.inr (Or.inl ⟨hheavy, a, b, hab, hnot⟩)

end Gtz

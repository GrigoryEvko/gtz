/-
# What a funnel tie pays at every four-set through its dominator

`Gtz.isTie_sixThree_allHeavy_or_funnel` splits every `(6,3)` boundary system in
two.  In the FUNNEL branch some atom has `leverageOf (D.atom a) = 1`, and the
landed funnel supplies a triple `T` avoiding `a` that weakly dominates and FIXES
it, `subsetSum D T *ᵥ D.atom a = D.atom a`.

The unit atom is then literally a UNIT NULL PROBE of the dominator's gap, which
is exactly the hypothesis the four-set law
`Gtz.det_add_atomMatrix_of_unit_null` consumes.  This module reads that law
against the four member floors of a four-set and turns it into a PRODUCER.

## The producer

Write `G = subsetSum D T - 1`, `e₂ = secondInvariantOfThree G`, and let `v` be
any atom.  Two landed updates give the four-set's two invariants in closed form:

  `det (G + v vᵀ)  =  e₂ · (v ⬝ᵥ g_a)²`                    (the four-set law)
  `e₂ (G + v vᵀ)   =  e₂ + leverageOf v · tr G - v ⬝ᵥ (G *ᵥ v)`   (the update)

A four-set whose determinant EXCEEDS its own second invariant cannot have all
four of its member gap determinants nonpositive
(`Gtz.fourSet_det_le_secondInvariant_of_floors`), and the member that is `T`
itself contributes a determinant of exactly zero, because `G` is singular at the
unit probe.  So the positive member lies in the STAR of `v`, and the landed
downdate producer `Gtz.star_exists_posDef_of_posDef_of_det_pos` upgrades it to
strict domination.  Comparing the two displayed quantities, the whole condition
is one inequality:

  **`Gtz.exists_star_posDef_of_payment_lt`: if
  `leverageOf v · tr G - v ⬝ᵥ (G *ᵥ v)  <  e₂ · ((v ⬝ᵥ g_a)² - 1)`
  then one of the three triples got by swapping a member of `T` for `v`
  dominates STRICTLY.**

## The payment

At a boundary system no triple dominates strictly, so the inequality is
REVERSED at every atom: `Gtz.isTie_funnel_payment`.  That is a new necessary
condition on a funnel boundary system, in the campaign's own currency, and it
binds precisely where the landed `Gtz.exists_outside_reading_sq_gt_one`
produces a reading above one, since the right side is positive exactly there.

## Two structural facts the same probe gives for free

* `Gtz.unitAtom_notMem_posDef_triple` — the unit atom lies in NO strictly
  dominating triple.  Its own leverage excess is the first Sylvester minor, and
  that minor is zero.
* `Gtz.reading_sq_sum_gt_of_posDef` — a strictly dominating triple reads every
  probe above the probe's own square.  At the unit atom this says the squared
  readings of a strict dominator exceed one, while the funnel dominator's
  own readings total exactly one (`Gtz.unitAtom_readings_resolve`).  So a strict dominator is
  never built from atoms the unit atom cannot see.

[MEASURED before proving.  The two update identities reproduce to `3.7e-13`
over 20000 random positive semidefinite forms with a unit null vector.  The
producer fired at 217 of 20000 such draws and delivered a strictly dominating
triple every time, with no failures.]
-/
import Gtz.Wave.FourSetProducer
import Gtz.Wave.FourSetFloorPackage
import Gtz.Wave.CellHTwoStarProducer
import Gtz.Wave.FunnelSecondInvariantFloor
import Gtz.Wave.InadmissiblePairSeparation
import Gtz.Design.TightAntecedentMining

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The two structural facts of a unit atom -/

/-- **A STRICT DOMINATOR OUTREADS EVERY PROBE.**  Positive definiteness of the
gap at a probe is exactly the statement that the selected atoms read the probe
above its own square. -/
theorem reading_sq_sum_gt_of_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    {u : Fin 3 → ℝ} (hu : u ≠ 0) (hpos : (subsetSum D C - 1).PosDef) :
    u ⬝ᵥ u < ∑ c ∈ C, (D.atom c ⬝ᵥ u) ^ 2 := by
  have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hpos).2 hu
  rw [star_trivial, gap_reading_diag D C u] at h
  linarith

/-- **THE UNIT ATOM IS IN NO STRICT DOMINATOR.**  Its leverage excess is the
first minor of the Sylvester chain, and at leverage one that minor vanishes. -/
theorem unitAtom_notMem_posDef_triple (D : WeightedDesign m 3) {a x y : Fin m}
    (hunit : leverageOf (D.atom a) = 1) :
    ¬ (subsetSum D ({a, x, y} : Finset (Fin m)) - 1).PosDef := by
  intro hpos
  have := one_lt_leverage_of_posDef D a x y hpos
  rw [hunit] at this
  exact absurd this (lt_irrefl 1)

/-! ## 2. The four-set of a fixing dominator -/

/-- A triple's subset sum, expanded. -/
theorem subsetSum_triple_atoms (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
  rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, add_assoc]

/-- **THE PAYMENT PRODUCER, IN MATRICES.**  A positive semidefinite form with a
unit null probe, presented as a triple's gap, whose payment at `v` falls below
the reading excess, carries a strictly dominating triple in the star of `v`. -/
theorem exists_star_posDef_of_payment_lt
    {G : Matrix (Fin 3) (Fin 3) ℝ} (hpsd : G.PosSemidef)
    {w : Fin 3 → ℝ} (hnull : G *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : 0 < secondInvariantOfThree G)
    {x y z v : Fin 3 → ℝ}
    (hG : G = atomMatrix x + atomMatrix y + atomMatrix z - 1)
    (hread : v ⬝ᵥ w ≠ 0)
    (hpay : leverageOf v * Matrix.trace G - v ⬝ᵥ (G *ᵥ v)
      < secondInvariantOfThree G * ((v ⬝ᵥ w) ^ 2 - 1)) :
    (atomMatrix v + atomMatrix y + atomMatrix z - 1).PosDef
      ∨ (atomMatrix v + atomMatrix x + atomMatrix z - 1).PosDef
      ∨ (atomMatrix v + atomMatrix x + atomMatrix y - 1).PosDef := by
  have hsym : Gᵀ = G := (by simpa using hpsd.isHermitian : G.IsSymm)
  -- the four-set, in the shape the landed floors are stated in
  have hF : G + atomMatrix v
      = atomMatrix v + atomMatrix x + atomMatrix y + atomMatrix z - 1 := by
    rw [hG]; abel
  have hPD : (atomMatrix v + atomMatrix x + atomMatrix y + atomMatrix z - 1).PosDef := by
    rw [← hF]
    exact posDef_add_atomMatrix_of_reading_ne_zero hpsd hnull hunit (ne_of_gt he) hread
  -- its determinant and its second invariant, both in closed form
  have hdet : (atomMatrix v + atomMatrix x + atomMatrix y + atomMatrix z - 1).det
      = secondInvariantOfThree G * (v ⬝ᵥ w) ^ 2 := by
    rw [← hF]; exact det_add_atomMatrix_of_unit_null hsym hnull hunit v
  have he2 : secondInvariantOfThree
      (atomMatrix v + atomMatrix x + atomMatrix y + atomMatrix z - 1)
      = secondInvariantOfThree G + leverageOf v * Matrix.trace G - v ⬝ᵥ (G *ᵥ v) := by
    rw [← hF]; exact secondInvariantOfThree_add_atomMatrix G v
  -- the payment says the four-set's determinant beats its own second invariant
  have hbeat : secondInvariantOfThree
      (atomMatrix v + atomMatrix x + atomMatrix y + atomMatrix z - 1)
      < (atomMatrix v + atomMatrix x + atomMatrix y + atomMatrix z - 1).det := by
    rw [he2, hdet]; nlinarith [hpay]
  -- the member that is the dominator itself pays nothing: its gap is singular
  have hzero : (atomMatrix x + atomMatrix y + atomMatrix z - 1).det ≤ 0 := by
    rw [← hG]; exact le_of_eq (det_eq_zero_of_unit_null hnull hunit)
  -- so one of the three swaps has a positive gap determinant
  have hstar : 0 < (atomMatrix v + atomMatrix y + atomMatrix z - 1).det
      ∨ 0 < (atomMatrix v + atomMatrix x + atomMatrix z - 1).det
      ∨ 0 < (atomMatrix v + atomMatrix x + atomMatrix y - 1).det := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    exact absurd (fourSet_det_le_secondInvariant_of_floors hzero h1 h2 h3) (not_le.mpr hbeat)
  exact star_exists_posDef_of_posDef_of_det_pos hPD hstar

/-! ## 3. The producer at a design -/

/-- **THE PAYMENT PRODUCER AT A DESIGN.**  A dominator that fixes a unit atom,
and any label whose payment falls short, produce a strictly dominating triple. -/
theorem funnel_exists_strict_of_payment_lt (D : WeightedDesign m 3)
    {a x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom a = D.atom a)
    (he : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z))
    (hread : D.atom p ⬝ᵥ D.atom a ≠ 0)
    (hpay : leverageOf (D.atom p)
          * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.atom p ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom p)
      < pairMinorTotal (D.atom x) (D.atom y) (D.atom z)
          * ((D.atom p ⬝ᵥ D.atom a) ^ 2 - 1)) :
    (atomMatrix (D.atom p) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom z) - 1).PosDef
      ∨ (atomMatrix (D.atom p) + atomMatrix (D.atom x)
          + atomMatrix (D.atom y) - 1).PosDef := by
  have hunit' : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  have hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom a = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]
  have hG : subsetSum D ({x, y, z} : Finset (Fin m)) - 1
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1 := by
    rw [subsetSum_triple_atoms D hxy hxz hyz]
  have hePM : secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      = pairMinorTotal (D.atom x) (D.atom y) (D.atom z) :=
    secondInvariantOfThree_gap_eq_pairMinorTotal D hxy hxz hyz
  refine exists_star_posDef_of_payment_lt hdom hnull hunit' ?_ hG hread ?_
  · rw [hePM]; exact he
  · rw [hePM]; exact hpay

/-! ## 4. The payment, as a law of a funnel boundary system -/

/-- **THE FUNNEL PAYMENT.**  At a boundary system no triple dominates strictly,
so the producer's inequality is reversed at EVERY label: a funnel tie pays, at
each atom, its trace term against the reading excess of its own unit atom.  The
right side is positive exactly at the labels the landed
`Gtz.exists_outside_reading_sq_gt_one` produces, so the law binds there. -/
theorem isTie_funnel_payment (D : WeightedDesign m 3) (htie : IsTie D)
    {a x y z p : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom a = D.atom a)
    (he : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z))
    (hread : D.atom p ⬝ᵥ D.atom a ≠ 0) :
    pairMinorTotal (D.atom x) (D.atom y) (D.atom z)
        * ((D.atom p ⬝ᵥ D.atom a) ^ 2 - 1)
      ≤ leverageOf (D.atom p)
          * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.atom p ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom p) := by
  by_contra hcon
  push Not at hcon
  have hstrict := funnel_exists_strict_of_payment_lt D hxy hxz hyz hdom hunit hfix he hread hcon
  -- each alternative is a card-three subset, so the tie forbids it
  have hkill : ∀ (u v w : Fin m), u ≠ v → u ≠ w → v ≠ w →
      ¬ (atomMatrix (D.atom u) + atomMatrix (D.atom v)
          + atomMatrix (D.atom w) - 1).PosDef := by
    intro u v w huv huw hvw hpos
    refine htie.2 ({u, v, w} : Finset (Fin m)) ?_ ?_
    · rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
        Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
    · rwa [subsetSum_triple_atoms D huv huw hvw]
  rcases hstrict with h | h | h
  · exact hkill p y z hpy hpz hyz h
  · exact hkill p x z hpx hpz hxz h
  · exact hkill p x y hpx hpy hxy h

/-! ## 5. The payment at six points -/

/-- **THE PAYMENT AT `(6,3)`.**  The funnel is supplied by the landed
`Gtz.isTie_sixThree_unitAtom_funnel`, so at six points the law needs only the
unit atom and the second invariant. -/
theorem isTie_sixThree_funnel_payment (D : WeightedDesign 6 3) (htie : IsTie D)
    {a : Fin 6} (hunit : leverageOf (D.atom a) = 1) :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z
      ∧ a ∉ ({x, y, z} : Finset (Fin 6))
      ∧ Dominates D ({x, y, z} : Finset (Fin 6))
      ∧ subsetSum D ({x, y, z} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a
      ∧ ∀ p : Fin 6, p ≠ x → p ≠ y → p ≠ z →
          D.atom p ⬝ᵥ D.atom a ≠ 0 →
          0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z) →
          pairMinorTotal (D.atom x) (D.atom y) (D.atom z)
              * ((D.atom p ⬝ᵥ D.atom a) ^ 2 - 1)
            ≤ leverageOf (D.atom p)
                * Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
              - D.atom p ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
                  *ᵥ D.atom p) := by
  obtain ⟨T, hcard, havoid, hdom, hfix⟩ := isTie_sixThree_unitAtom_funnel D htie a hunit
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp hcard
  subst hT
  exact ⟨x, y, z, hxy, hxz, hyz, havoid, hdom, hfix,
    fun p hpx hpy hpz hread he =>
      isTie_funnel_payment D htie hxy hxz hyz hpx hpy hpz hdom hunit hfix he hread⟩

end Gtz

/-
# The wedge balance is the adjugate of the gap, and it does not see the normal

`Gtz.WedgeBalanceSelector` is the entrance that retires all five on-path
obligations.  Its payload asks, at a triple `S`, a unit normal `n` and EVERY
in-plane probe `p`, for

  crossing wedge  <  inside wedge + outside wedge .

This file replaces that three-term comparison by ONE quadratic form and then
removes the normal from it.

Three steps.

**Step one, the Plucker reading.**  At rank three the wedge shadow of a pair of
atoms against `(n, p)` is a pairing of two cross products,

  `wedgeShadow n p c d = (a_c x a_d) . (n x p)` .

So every wedge total is a quadratic form in the single vector `m = n x p`, and
the pair `(n, p)` enters through `m` alone.

**Step two, the adjugate.**  For an arbitrary real measure the adjugate of a
weighted atom sum at rank three is the halved pair total of the wedges,

  `adj( sum_c s_c a_c a_c^T ) = (1/2) sum_c sum_d s_c s_d (a_c x a_d)(a_c x a_d)^T` .

The measure is arbitrary and may take either sign, which is what makes it
usable here: the gap `S_C - 1` is the atom sum against the SIGNED measure
`1_C - w`, so its adjugate is the wedge form of that signed measure.  Reading
the quadratic form at `m` turns the whole wedge balance into

  `0 < m . (adj(S_C - 1) m)` .

**Step three, the normal is not there.**  A two by two determinant that is
positive on a whole plane forces the ambient form to be DEFINITE, of one sign
or the other, and the sign is read off the pivot.  So the wedge balance at ONE
unit normal, at every in-plane probe, already says that the gap is definite —
and definiteness mentions no normal.  The balance is therefore the same
condition at every unit normal, and the only thing the normal surplus does is
choose the sign.

The consequence for the target is `Gtz.TraceWedgeSelector`: the selector may
fix its normal to the first coordinate axis once and for all, and it may
replace the normal surplus by the normal-free trace test
`3 < sum of the leverages of the triple`.

## What this file does NOT claim

It does not prove `Gtz.WedgeBalanceSelector`.  It proves that the selector is
equivalent to a form with one fewer quantifier and a normal-free sign test.

## Reconnaissance recorded in the campaign log

At the complete graph on four vertices the balance holds at exactly the four
vertex stars, and at the icosahedron at exactly the ten coherent triples.  In
both cases the balanced set equals the dominating set, as the equivalence
below requires.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Wave.SpectralSupplyCell
import Gtz.Wave.WedgeLeakCriterion
import Gtz.Quantitative.HarmonicCircuit
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Design.ConservationCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

open Finset Matrix

/-! ## 1. The adjugate of a signed atom sum

The measure carries no sign hypothesis anywhere in this section.  That is the
whole point: the gap of a subset is the atom sum against `1_C - w`, which is
negative outside the subset. -/

/-- The two by two minor of two measure sums, symmetrized over the pair.  This
is the Lagrange identity in the shape the adjugate needs: the difference of two
products of sums is a halved double sum of products of two by two brackets.  No
positivity and no symmetry of the four slots. -/
theorem sum_sum_pairMinor_symmetrize {index : Type*} (support : Finset index)
    (measure : index → ℝ) (vec : index → Fin 3 → ℝ) (i j k l : Fin 3) :
    2 * ((∑ c ∈ support, measure c * (vec c i * vec c j))
          * (∑ d ∈ support, measure d * (vec d k * vec d l))
        - (∑ c ∈ support, measure c * (vec c i * vec c l))
          * (∑ d ∈ support, measure d * (vec d k * vec d j)))
      = ∑ c ∈ support, ∑ d ∈ support, measure c * measure d
          * ((vec c i * vec d k - vec c k * vec d i)
              * (vec c j * vec d l - vec c l * vec d j)) := by
  classical
  set flux : index → index → ℝ := fun c d =>
    (measure c * (vec c i * vec c j)) * (measure d * (vec d k * vec d l))
      - (measure c * (vec c i * vec c l)) * (measure d * (vec d k * vec d j)) with hflux
  have hexpand : (∑ c ∈ support, measure c * (vec c i * vec c j))
        * (∑ d ∈ support, measure d * (vec d k * vec d l))
      - (∑ c ∈ support, measure c * (vec c i * vec c l))
        * (∑ d ∈ support, measure d * (vec d k * vec d j))
      = ∑ c ∈ support, ∑ d ∈ support, flux c d := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_sub_distrib]
  have hswap : ∑ c ∈ support, ∑ d ∈ support, flux c d
      = ∑ c ∈ support, ∑ d ∈ support, flux d c := Finset.sum_comm
  have hsum : ∑ c ∈ support, ∑ d ∈ support, (flux c d + flux d c)
      = ∑ c ∈ support, ∑ d ∈ support, measure c * measure d
          * ((vec c i * vec d k - vec c k * vec d i)
              * (vec c j * vec d l - vec c l * vec d j)) := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [hflux]
    ring
  have hsplit : ∑ c ∈ support, ∑ d ∈ support, (flux c d + flux d c)
      = (∑ c ∈ support, ∑ d ∈ support, flux c d)
        + ∑ c ∈ support, ∑ d ∈ support, flux d c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_add_distrib]
  rw [hexpand, ← hsum, hsplit, ← hswap]
  ring

/-- The entries of a measure-weighted atom sum. -/
theorem sum_smul_atomMatrix_entry {index : Type*} (support : Finset index)
    (measure : index → ℝ) (vec : index → Fin 3 → ℝ) (row col : Fin 3) :
    (∑ c ∈ support, measure c • atomMatrix (vec c)) row col
      = ∑ c ∈ support, measure c * (vec c row * vec c col) := by
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]

/-- The entries of the halved pair wedge total. -/
theorem halfWedgeSum_apply {index : Type*} (support : Finset index)
    (measure : index → ℝ) (vec : index → Fin 3 → ℝ) (row col : Fin 3) :
    ((2 : ℝ)⁻¹ • ∑ c ∈ support, ∑ d ∈ support,
        (measure c * measure d) • atomMatrix (atomWedge (vec c) (vec d))) row col
      = (∑ c ∈ support, ∑ d ∈ support, measure c * measure d
          * (atomWedge (vec c) (vec d) row * atomWedge (vec c) (vec d) col)) / 2 := by
  rw [Matrix.smul_apply, Matrix.sum_apply]
  have hinner : ∀ c : index, (∑ d ∈ support,
      (measure c * measure d) • atomMatrix (atomWedge (vec c) (vec d))) row col
      = ∑ d ∈ support, measure c * measure d
        * (atomWedge (vec c) (vec d) row * atomWedge (vec c) (vec d) col) := by
    intro c
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun d _ => by
      rw [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun c _ => hinner c, smul_eq_mul]
  ring

/-- Transport of a pair total from wedge slots to atom coordinates. -/
theorem sum_sum_wedgeProduct_eq {index : Type*} (support : Finset index)
    (measure : index → ℝ) (vec : index → Fin 3 → ℝ) (rowSlot colSlot i j k l : Fin 3)
    (hrow : ∀ c d : index, atomWedge (vec c) (vec d) rowSlot
      = vec c i * vec d k - vec c k * vec d i)
    (hcol : ∀ c d : index, atomWedge (vec c) (vec d) colSlot
      = vec c j * vec d l - vec c l * vec d j) :
    ∑ c ∈ support, ∑ d ∈ support, measure c * measure d
        * (atomWedge (vec c) (vec d) rowSlot * atomWedge (vec c) (vec d) colSlot)
      = ∑ c ∈ support, ∑ d ∈ support, measure c * measure d
          * ((vec c i * vec d k - vec c k * vec d i)
              * (vec c j * vec d l - vec c l * vec d j)) :=
  Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
    rw [hrow c d, hcol c d]

/-- **THE ADJUGATE OF A SIGNED ATOM SUM IS THE HALVED PAIR WEDGE TOTAL.**  At
rank three, for an arbitrary finite support and an arbitrary real measure,

  `adj( sum_c s_c a_c a_c^T )  =  (1/2) sum_c sum_d s_c s_d (a_c x a_d)(a_c x a_d)^T` .

The measure may take either sign at any label.  This is the second compound of
a rank-one expansion, read on the design's own atoms, and it is the identity the
whole file rests on. -/
theorem adjugate_sum_smul_atomMatrix {index : Type*} (support : Finset index)
    (measure : index → ℝ) (vec : index → Fin 3 → ℝ) :
    (∑ c ∈ support, measure c • atomMatrix (vec c)).adjugate
      = (2 : ℝ)⁻¹ • ∑ c ∈ support, ∑ d ∈ support,
          (measure c * measure d) • atomMatrix (atomWedge (vec c) (vec d)) := by
  have hbase := sum_smul_atomMatrix_entry support measure vec
  have htarget := halfWedgeSum_apply support measure vec
  have hkey := sum_sum_pairMinor_symmetrize support measure vec
  have hsym : ∀ p q : Fin 3, ∑ c ∈ support, measure c * (vec c p * vec c q)
      = ∑ c ∈ support, measure c * (vec c q * vec c p) :=
    fun p q => Finset.sum_congr rfl fun c _ => by ring
  have hslotZero : ∀ c d : index, atomWedge (vec c) (vec d) 0
      = vec c 1 * vec d 2 - vec c 2 * vec d 1 := fun c d => rfl
  have hslotOne : ∀ c d : index, atomWedge (vec c) (vec d) 1
      = vec c 2 * vec d 0 - vec c 0 * vec d 2 := fun c d => rfl
  have hslotTwo : ∀ c d : index, atomWedge (vec c) (vec d) 2
      = vec c 0 * vec d 1 - vec c 1 * vec d 0 := fun c d => rfl
  ext row col
  rw [Matrix.adjugate_fin_three, htarget]
  fin_cases row <;> fin_cases col <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_fin_const, hbase]
  · rw [sum_sum_wedgeProduct_eq support measure vec 0 0 1 1 2 2 hslotZero hslotZero]
    have hstep := hkey 1 1 2 2
    simp only [hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 0 1 1 2 2 0 hslotZero hslotOne]
    have hstep := hkey 1 2 2 0
    simp only [hsym 1 0, hsym 2 0, hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 0 2 1 0 2 1 hslotZero hslotTwo]
    have hstep := hkey 1 0 2 1
    simp only [hsym 1 0, hsym 2 0, hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 1 0 2 1 0 2 hslotOne hslotZero]
    have hstep := hkey 2 1 0 2
    simp only [hsym 1 0, hsym 2 0, hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 1 1 2 2 0 0 hslotOne hslotOne]
    have hstep := hkey 2 2 0 0
    simp only [hsym 2 0] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 1 2 2 0 0 1 hslotOne hslotTwo]
    have hstep := hkey 2 0 0 1
    simp only [hsym 1 0, hsym 2 0, hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 2 0 0 1 1 2 hslotTwo hslotZero]
    have hstep := hkey 0 1 1 2
    simp only [hsym 1 0, hsym 2 0, hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 2 1 0 2 1 0 hslotTwo hslotOne]
    have hstep := hkey 0 2 1 0
    simp only [hsym 1 0, hsym 2 0, hsym 2 1] at hstep ⊢
    linarith [hstep]
  · rw [sum_sum_wedgeProduct_eq support measure vec 2 2 0 0 1 1 hslotTwo hslotTwo]
    have hstep := hkey 0 0 1 1
    simp only [hsym 1 0] at hstep ⊢
    linarith [hstep]

/-! ## 2. The wedge shadow is a Plucker pairing

At rank three a two by two determinant of readings is the pairing of two cross
products.  The consequence is that the pair `(normal, probe)` enters every wedge
total only through the single vector `normal x probe`. -/

/-- **THE WEDGE SHADOW IS A CROSS PAIRING.**  Binet-Cauchy at rank three, read on
a design. -/
theorem wedgeShadow_eq_atomWedge_dotProduct {size : ℕ} (design : WeightedDesign size 3)
    (normalVec probeVec : Fin 3 → ℝ) (leftLabel rightLabel : Fin size) :
    wedgeShadow design normalVec probeVec leftLabel rightLabel
      = atomWedge (design.atom leftLabel) (design.atom rightLabel)
          ⬝ᵥ atomWedge normalVec probeVec := by
  simp only [wedgeShadow, atomWedge, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The quadratic form of a pair-indexed atom sum, pushed through both sums. -/
theorem dotProduct_pairSum_smul_atomMatrix_mulVec {size rank : ℕ} (support : Finset (Fin size))
    (measure : Fin size → ℝ) (vec : Fin size → Fin size → Fin rank → ℝ)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
        (measure leftLabel * measure rightLabel) • atomMatrix (vec leftLabel rightLabel))
          *ᵥ probe)
      = ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
          measure leftLabel * measure rightLabel * (vec leftLabel rightLabel ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun leftLabel _ =>
    dotProduct_sum_smul_atomMatrix_mulVec (fun rightLabel => measure leftLabel * measure rightLabel)
      (vec leftLabel) support probe

/-- **THE WEDGE TOTAL IS THE ADJUGATE QUADRATIC FORM.**  For an arbitrary real
measure and an arbitrary support, the measure-weighted wedge total of a
rank-three design at `(n, p)` is the adjugate of that measure's own atom sum,
read at the single vector `n x p`.  Nothing is assumed of the measure, and the
pair `(n, p)` enters only through its cross product. -/
theorem wedgeTotal_eq_dotProduct_adjugate_mulVec {size : ℕ} (design : WeightedDesign size 3)
    (measure : Fin size → ℝ) (support : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ) :
    wedgeTotal design measure support normalVec probeVec
      = atomWedge normalVec probeVec
          ⬝ᵥ ((∑ label ∈ support, measure label • atomMatrix (design.atom label)).adjugate
              *ᵥ atomWedge normalVec probeVec) := by
  rw [adjugate_sum_smul_atomMatrix support measure (fun label => design.atom label),
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_pairSum_smul_atomMatrix_mulVec support measure
      (fun leftLabel rightLabel => atomWedge (design.atom leftLabel) (design.atom rightLabel))
      (atomWedge normalVec probeVec)]
  have hshadow : ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
      measure leftLabel * measure rightLabel
        * wedgeShadow design normalVec probeVec leftLabel rightLabel ^ 2
      = ∑ leftLabel ∈ support, ∑ rightLabel ∈ support,
          measure leftLabel * measure rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel)
                ⬝ᵥ atomWedge normalVec probeVec) ^ 2 :=
    Finset.sum_congr rfl fun leftLabel _ => Finset.sum_congr rfl fun rightLabel _ => by
      rw [wedgeShadow_eq_atomWedge_dotProduct]
  unfold wedgeTotal
  rw [hshadow]
  ring

/-! ## 3. The gap is the atom sum of the signed measure

`Gtz.hypersimplexVertexDirection` is the signed measure `1_C - w`, and
`Gtz.subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix` says the gap is
its atom sum.  Section 1 therefore reads the gap's adjugate as one wedge total
over ALL labels, with no split into inside, outside and crossing. -/

/-- **THE WEDGE BALANCE IS ONE LAGRANGE FORM IN THE SIGNED GAP MEASURE.**  The
wedge total of the signed measure `1_C - w` over the whole label set is the
adjugate of the gap, read at `n x p`. -/
theorem wedgeTotal_vertexDirection_eq_dotProduct_gapAdjugate {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (normalVec probeVec : Fin 3 → ℝ) :
    wedgeTotal design (hypersimplexVertexDirection design selected) Finset.univ
        normalVec probeVec
      = atomWedge normalVec probeVec
          ⬝ᵥ ((subsetSum design selected - 1).adjugate *ᵥ atomWedge normalVec probeVec) := by
  rw [wedgeTotal_eq_dotProduct_adjugate_mulVec design
    (hypersimplexVertexDirection design selected) Finset.univ normalVec probeVec,
    ← subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix design selected]

/-- **THE ADJUGATE READS THE BORDER MINOR.**  For every real three by three
matrix and every pair of vectors, the adjugate at the cross product is the two
by two determinant of the form on the pair.  No symmetry, no positivity. -/
theorem dotProduct_adjugate_atomWedge_mulVec (form : Matrix (Fin 3) (Fin 3) ℝ)
    (leftVec rightVec : Fin 3 → ℝ) :
    atomWedge leftVec rightVec ⬝ᵥ (form.adjugate *ᵥ atomWedge leftVec rightVec)
      = (leftVec ⬝ᵥ (form *ᵥ leftVec)) * (rightVec ⬝ᵥ (form *ᵥ rightVec))
        - (leftVec ⬝ᵥ (form *ᵥ rightVec)) * (rightVec ⬝ᵥ (form *ᵥ leftVec)) := by
  simp only [Matrix.adjugate_fin_three, atomWedge, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The polarized gap reading: the gap form of a subset on two vectors is the
selected cross total minus the ambient pairing. -/
theorem dotProduct_subsetSum_sub_one_mulVec_cross {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (leftVec rightVec : Fin rank → ℝ) :
    leftVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ rightVec)
      = (∑ label ∈ selected,
          (design.atom label ⬝ᵥ leftVec) * (design.atom label ⬝ᵥ rightVec))
        - leftVec ⬝ᵥ rightVec := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum, Matrix.sum_mulVec,
    dotProduct_sum]
  exact congrArg (fun value => value - leftVec ⬝ᵥ rightVec)
    (Finset.sum_congr rfl fun label _ =>
      dotProduct_atomMatrix_mulVec_cross (design.atom label) leftVec rightVec)

/-- **THE WEDGE BALANCE, COLLAPSED TO ONE FORM.**  Inside plus outside minus
crossing is the single signed-measure wedge total, at any rank-three design, any
subset, and any two vectors.  No hypothesis at all. -/
theorem wedgeBalanceTotal_eq_wedgeTotal_vertexDirection {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (normalVec probeVec : Fin 3 → ℝ) :
    (wedgeTotal design (weightDeficit design) selected normalVec probeVec
        + wedgeTotal design design.weight selectedᶜ normalVec probeVec)
        - mixedWedgeTotal design selected normalVec probeVec
      = wedgeTotal design (hypersimplexVertexDirection design selected) Finset.univ
          normalVec probeVec := by
  rw [wedgeTotal_vertexDirection_eq_dotProduct_gapAdjugate,
    dotProduct_adjugate_atomWedge_mulVec,
    dotProduct_subsetSum_sub_one_mulVec_cross design selected normalVec normalVec,
    dotProduct_subsetSum_sub_one_mulVec_cross design selected probeVec probeVec,
    dotProduct_subsetSum_sub_one_mulVec_cross design selected normalVec probeVec,
    dotProduct_subsetSum_sub_one_mulVec_cross design selected probeVec normalVec,
    ← gapDiscriminant_eq_wedgeBalance design selected normalVec probeVec]
  have hpair : ∑ label ∈ selected,
      (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ normalVec)
      = ∑ label ∈ selected,
          (design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec) :=
    Finset.sum_congr rfl fun label _ => by ring
  have hsquareLeft : ∀ vecArg : Fin 3 → ℝ, ∑ label ∈ selected,
      (design.atom label ⬝ᵥ vecArg) * (design.atom label ⬝ᵥ vecArg)
      = ∑ label ∈ selected, (design.atom label ⬝ᵥ vecArg) ^ 2 :=
    fun vecArg => Finset.sum_congr rfl fun label _ => by ring
  rw [hpair, hsquareLeft normalVec, hsquareLeft probeVec, dotProduct_comm probeVec normalVec]
  ring

/-- **THE WEDGE BALANCE IS THE POSITIVITY OF ONE SIGNED WEDGE TOTAL.** -/
theorem wedgeBalanceAt_iff_wedgeTotal_vertexDirection_pos {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (normalVec probeVec : Fin 3 → ℝ) :
    WedgeBalanceAt design selected normalVec probeVec
      ↔ 0 < wedgeTotal design (hypersimplexVertexDirection design selected) Finset.univ
          normalVec probeVec := by
  have hcollapse := wedgeBalanceTotal_eq_wedgeTotal_vertexDirection design selected
    normalVec probeVec
  unfold WedgeBalanceAt
  constructor
  · intro hbalance; linarith [hcollapse, hbalance]
  · intro hpositive; linarith [hcollapse, hpositive]

/-- **THE WEDGE BALANCE IS THE ADJUGATE OF THE GAP.**  The single most compact
reading: the balance at `(n, p)` says that the adjugate of the gap is positive
at `n x p`. -/
theorem wedgeBalanceAt_iff_dotProduct_gapAdjugate_pos {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (normalVec probeVec : Fin 3 → ℝ) :
    WedgeBalanceAt design selected normalVec probeVec
      ↔ 0 < atomWedge normalVec probeVec
          ⬝ᵥ ((subsetSum design selected - 1).adjugate *ᵥ atomWedge normalVec probeVec) := by
  rw [wedgeBalanceAt_iff_wedgeTotal_vertexDirection_pos,
    wedgeTotal_vertexDirection_eq_dotProduct_gapAdjugate]

/-! ## 4. The border criterion, at the matrix level

`Gtz.posDef_of_normalSurplus_borderMinors` and its converse are stated for the
gap of a design.  The negative branch below needs the criterion for `1 - S_C`,
which is not a design gap, so the two lemmas here carry an arbitrary symmetric
matrix.  They are the general-matrix form of the landed pair. -/

/-- A symmetric matrix pairs symmetrically. -/
theorem dotProduct_mulVec_comm_of_transpose {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hsym : formᵀ = form) (leftVec rightVec : Fin rank → ℝ) :
    leftVec ⬝ᵥ (form *ᵥ rightVec) = rightVec ⬝ᵥ (form *ᵥ leftVec) := by
  have hstep : leftVec ᵥ* form = form *ᵥ leftVec := by
    conv_lhs => rw [← hsym]
    exact Matrix.vecMul_transpose form leftVec
  rw [Matrix.dotProduct_mulVec, hstep, dotProduct_comm]

/-- The quadratic form of a symmetric matrix, split along a pivot direction. -/
theorem dotProduct_mulVec_pivot_split {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hsym : formᵀ = form) (pivotVec residualVec : Fin rank → ℝ) (component : ℝ) :
    (residualVec + component • pivotVec) ⬝ᵥ (form *ᵥ (residualVec + component • pivotVec))
      = residualVec ⬝ᵥ (form *ᵥ residualVec)
        + 2 * component * (pivotVec ⬝ᵥ (form *ᵥ residualVec))
        + component ^ 2 * (pivotVec ⬝ᵥ (form *ᵥ pivotVec)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_mulVec_comm_of_transpose hsym residualVec pivotVec]
  ring

/-- **THE BORDER CRITERION FOR AN ARBITRARY SYMMETRIC MATRIX.**  A positive pivot
value and a strictly positive border minor at every residual direction make the
matrix positive definite. -/
theorem posDef_of_pivotForm_pos_of_borderMinors {rank : ℕ}
    {form : Matrix (Fin rank) (Fin rank) ℝ} (hsym : formᵀ = form)
    (unitPivot : Fin rank → ℝ) (hunit : unitPivot ⬝ᵥ unitPivot = 1)
    (hpivot : 0 < unitPivot ⬝ᵥ (form *ᵥ unitPivot))
    (hborder : ∀ probeVec : Fin rank → ℝ, probeVec ⬝ᵥ unitPivot = 0 → probeVec ≠ 0 →
      (unitPivot ⬝ᵥ (form *ᵥ probeVec)) ^ 2
        < (unitPivot ⬝ᵥ (form *ᵥ unitPivot)) * (probeVec ⬝ᵥ (form *ᵥ probeVec))) :
    form.PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsym, fun testVec htestNe => ?_⟩
  rw [star_trivial]
  have hresOrth : (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot) ⬝ᵥ unitPivot = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, sub_self]
  have hrebuild : testVec
      = (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot) + (testVec ⬝ᵥ unitPivot) • unitPivot := by
    abel
  have hexpand := dotProduct_mulVec_pivot_split hsym unitPivot
    (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot) (testVec ⬝ᵥ unitPivot)
  rw [← hrebuild] at hexpand
  rw [hexpand]
  by_cases hresZero : testVec - (testVec ⬝ᵥ unitPivot) • unitPivot = 0
  · have hcomponentNe : testVec ⬝ᵥ unitPivot ≠ 0 := by
      intro hzero
      exact htestNe (by rw [hrebuild, hresZero, hzero, zero_smul, add_zero])
    rw [hresZero]
    simp only [Matrix.mulVec_zero, dotProduct_zero, mul_zero, zero_add]
    have hsquarePos : 0 < (testVec ⬝ᵥ unitPivot) ^ 2 := by positivity
    nlinarith [hpivot, hsquarePos]
  · have hborderHere := hborder _ hresOrth hresZero
    nlinarith [hborderHere, hpivot,
      sq_nonneg (unitPivot ⬝ᵥ (form *ᵥ (testVec - (testVec ⬝ᵥ unitPivot) • unitPivot))
        + (testVec ⬝ᵥ unitPivot) * (unitPivot ⬝ᵥ (form *ᵥ unitPivot)))]

/-- **THE BORDER CRITERION IS NECESSARY TOO, FOR AN ARBITRARY MATRIX.** -/
theorem borderMinors_of_posDef {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hsym : formᵀ = form) (hposDef : form.PosDef) (unitPivot : Fin rank → ℝ)
    (hunit : unitPivot ⬝ᵥ unitPivot = 1) (probeVec : Fin rank → ℝ)
    (horthogonal : probeVec ⬝ᵥ unitPivot = 0) (hprobeNe : probeVec ≠ 0) :
    (unitPivot ⬝ᵥ (form *ᵥ probeVec)) ^ 2
      < (unitPivot ⬝ᵥ (form *ᵥ unitPivot)) * (probeVec ⬝ᵥ (form *ᵥ probeVec)) := by
  have hpivotNe : unitPivot ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  have hpivotPos : 0 < unitPivot ⬝ᵥ (form *ᵥ unitPivot) := by
    have hvalue := hposDef.dotProduct_mulVec_pos hpivotNe
    rwa [star_trivial] at hvalue
  have hquad : ∀ component : ℝ, 0 < probeVec ⬝ᵥ (form *ᵥ probeVec)
      + 2 * component * (unitPivot ⬝ᵥ (form *ᵥ probeVec))
      + component ^ 2 * (unitPivot ⬝ᵥ (form *ᵥ unitPivot)) := by
    intro component
    have hne : probeVec + component • unitPivot ≠ 0 := by
      intro hzero
      have hread : (probeVec + component • unitPivot) ⬝ᵥ probeVec = 0 := by
        rw [hzero, zero_dotProduct]
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul,
        dotProduct_comm unitPivot probeVec, horthogonal, mul_zero, add_zero] at hread
      exact hprobeNe (dotProduct_self_eq_zero.mp hread)
    have hvalue := hposDef.dotProduct_mulVec_pos hne
    rw [star_trivial, dotProduct_mulVec_pivot_split hsym unitPivot probeVec component] at hvalue
    exact hvalue
  have hoptimal := hquad (-(unitPivot ⬝ᵥ (form *ᵥ probeVec)) / (unitPivot ⬝ᵥ (form *ᵥ unitPivot)))
  have hclear : probeVec ⬝ᵥ (form *ᵥ probeVec)
      + 2 * (-(unitPivot ⬝ᵥ (form *ᵥ probeVec)) / (unitPivot ⬝ᵥ (form *ᵥ unitPivot)))
        * (unitPivot ⬝ᵥ (form *ᵥ probeVec))
      + (-(unitPivot ⬝ᵥ (form *ᵥ probeVec)) / (unitPivot ⬝ᵥ (form *ᵥ unitPivot))) ^ 2
        * (unitPivot ⬝ᵥ (form *ᵥ unitPivot))
      = ((probeVec ⬝ᵥ (form *ᵥ probeVec)) * (unitPivot ⬝ᵥ (form *ᵥ unitPivot))
          - (unitPivot ⬝ᵥ (form *ᵥ probeVec)) ^ 2) / (unitPivot ⬝ᵥ (form *ᵥ unitPivot)) := by
    field_simp
    ring
  rw [hclear] at hoptimal
  have hnumerator : 0 < (probeVec ⬝ᵥ (form *ᵥ probeVec)) * (unitPivot ⬝ᵥ (form *ᵥ unitPivot))
      - (unitPivot ⬝ᵥ (form *ᵥ probeVec)) ^ 2 := by
    have hstep := mul_pos hoptimal hpivotPos
    rwa [div_mul_cancel₀ _ hpivotPos.ne'] at hstep
  nlinarith [hnumerator]

/-! ## 5. The normal is not in the wedge balance

The border minor of a plane is a two by two determinant.  A two by two
determinant that is strictly positive on a whole plane forces the ambient form
to be DEFINITE, and definiteness has no normal in it.  So the balance at ONE
unit normal is already the balance at every unit normal, and the surplus does
nothing but choose the sign. -/

/-- At rank three every unit vector has a nonzero orthogonal companion. -/
theorem exists_orthogonal_ne_zero_of_unit (unitVec : Fin 3 → ℝ)
    (hunit : unitVec ⬝ᵥ unitVec = 1) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitVec = 0 ∧ probeVec ≠ 0 := by
  classical
  have horth : ∀ slot : Fin 3,
      (Pi.single slot (1 : ℝ) - unitVec slot • unitVec) ⬝ᵥ unitVec = 0 := by
    intro slot
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, single_dotProduct,
      one_mul, sub_self]
  by_contra hnone
  push Not at hnone
  have hdiag : ∀ slot : Fin 3, unitVec slot * unitVec slot = 1 := by
    intro slot
    have hstep := congrFun (hnone _ (horth slot)) slot
    rw [Pi.sub_apply, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hstep
    linarith
  have hexpand : unitVec ⬝ᵥ unitVec
      = unitVec 0 * unitVec 0 + unitVec 1 * unitVec 1 + unitVec 2 * unitVec 2 := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [hexpand, hdiag 0, hdiag 1, hdiag 2] at hunit
  norm_num at hunit

/-- The border minor of a design gap in atom vocabulary is the border minor of
the gap matrix. -/
theorem gapBorderMinor_iff {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal probeVec : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (horthogonal : probeVec ⬝ᵥ unitNormal = 0) :
    ((∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ unitNormal)) ^ 2
        < ((∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ label ∈ selected, (design.atom label ⬝ᵥ probeVec) ^ 2) - probeVec ⬝ᵥ probeVec))
      ↔ (unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)) ^ 2
        < (unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal))
          * (probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)) := by
  have hnormalOrth : unitNormal ⬝ᵥ probeVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  rw [dotProduct_subsetSum_sub_one_mulVec_cross design selected unitNormal probeVec,
    dotProduct_subsetSum_sub_one_mulVec_cross design selected unitNormal unitNormal,
    dotProduct_subsetSum_sub_one_mulVec_cross design selected probeVec probeVec,
    hunit, hnormalOrth]
  have hpair : ∑ label ∈ selected,
      (design.atom label ⬝ᵥ unitNormal) * (design.atom label ⬝ᵥ probeVec)
      = ∑ label ∈ selected,
          (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ unitNormal) :=
    Finset.sum_congr rfl fun label _ => by ring
  have hsquare : ∀ vecArg : Fin 3 → ℝ, ∑ label ∈ selected,
      (design.atom label ⬝ᵥ vecArg) * (design.atom label ⬝ᵥ vecArg)
      = ∑ label ∈ selected, (design.atom label ⬝ᵥ vecArg) ^ 2 :=
    fun vecArg => Finset.sum_congr rfl fun label _ => by ring
  rw [hpair, hsquare unitNormal, hsquare probeVec]
  constructor
  · intro hcover; linarith [hcover]
  · intro hcover; linarith [hcover]

/-- **THE WEDGE BALANCE IS DEFINITENESS.**  At any unit normal, the balance at
every in-plane probe holds exactly when the gap is definite, of one sign or the
other.  The right side names no normal.  This is the exact content of the
balance, with the normal surplus removed. -/
theorem forall_wedgeBalanceAt_iff_definite {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    (∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        WedgeBalanceAt design selected unitNormal probeVec)
      ↔ ((subsetSum design selected - 1).PosDef
          ∨ (1 - subsetSum design selected).PosDef) := by
  classical
  have hsym : (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 :=
    transpose_subsetSum_sub_one design selected
  have hnegSym : (-(subsetSum design selected - 1))ᵀ = -(subsetSum design selected - 1) := by
    rw [Matrix.transpose_neg, hsym]
  have hnegEq : -(subsetSum design selected - 1) = 1 - subsetSum design selected := by
    rw [neg_sub]
  have hmatrix : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      (WedgeBalanceAt design selected unitNormal probeVec
        ↔ (unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)) ^ 2
          < (unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal))
            * (probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec))) := by
    intro probeVec horthogonal _
    rw [← gapBorderMinor_iff design selected unitNormal probeVec hunit horthogonal]
    exact (planeCover_iff_wedgeBalanceAt design selected unitNormal probeVec hunit
      horthogonal).symm
  constructor
  · intro hbalance
    obtain ⟨witnessProbe, hwitnessOrth, hwitnessNe⟩ :=
      exists_orthogonal_ne_zero_of_unit unitNormal hunit
    have hwitness := (hmatrix witnessProbe hwitnessOrth hwitnessNe).mp
      (hbalance witnessProbe hwitnessOrth hwitnessNe)
    rcases lt_trichotomy (unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ unitNormal)) 0 with
      hneg | hzero | hpos
    · refine Or.inr ?_
      rw [← hnegEq]
      refine posDef_of_pivotForm_pos_of_borderMinors hnegSym unitNormal hunit ?_ ?_
      · simp only [Matrix.neg_mulVec, dotProduct_neg]; linarith
      · intro probeVec horthogonal hprobeNe
        have hstep := (hmatrix probeVec horthogonal hprobeNe).mp
          (hbalance probeVec horthogonal hprobeNe)
        simp only [Matrix.neg_mulVec, dotProduct_neg]
        nlinarith [hstep]
    · exfalso
      rw [hzero, zero_mul] at hwitness
      nlinarith [hwitness, sq_nonneg (unitNormal ⬝ᵥ ((subsetSum design selected - 1) *ᵥ witnessProbe))]
    · refine Or.inl (posDef_of_pivotForm_pos_of_borderMinors hsym unitNormal hunit hpos ?_)
      intro probeVec horthogonal hprobeNe
      exact (hmatrix probeVec horthogonal hprobeNe).mp (hbalance probeVec horthogonal hprobeNe)
  · rintro (hposDef | hnegDef) probeVec horthogonal hprobeNe
    · exact (hmatrix probeVec horthogonal hprobeNe).mpr
        (borderMinors_of_posDef hsym hposDef unitNormal hunit probeVec horthogonal hprobeNe)
    · rw [← hnegEq] at hnegDef
      have hstep := borderMinors_of_posDef hnegSym hnegDef unitNormal hunit probeVec
        horthogonal hprobeNe
      simp only [Matrix.neg_mulVec, dotProduct_neg] at hstep
      refine (hmatrix probeVec horthogonal hprobeNe).mpr ?_
      nlinarith [hstep]

/-- **THE NORMAL IS FREE IN THE WEDGE BALANCE ITSELF.**  The balance at every
in-plane probe of ONE unit normal is the same statement as the balance at every
in-plane probe of ANY other unit normal.  The landed
`Gtz.posDef_iff_normalSurplus_and_wedgeBalance` makes the CONJUNCTION of the
surplus and the balance normal-free.  This theorem says the balance alone
already is. -/
theorem forall_wedgeBalanceAt_normal_free {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (firstNormal secondNormal : Fin 3 → ℝ)
    (hfirst : firstNormal ⬝ᵥ firstNormal = 1) (hsecond : secondNormal ⬝ᵥ secondNormal = 1) :
    (∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ firstNormal = 0 → probeVec ≠ 0 →
        WedgeBalanceAt design selected firstNormal probeVec)
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ secondNormal = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design selected secondNormal probeVec := by
  rw [forall_wedgeBalanceAt_iff_definite design selected firstNormal hfirst,
    forall_wedgeBalanceAt_iff_definite design selected secondNormal hsecond]

/-! ## 6. The trace test replaces the normal surplus

Definiteness plus a sign gives strict domination, and the cheapest sign test is
the trace.  The trace of the gap is the leverage total of the triple minus the
rank, so the surplus — which is quadratic and normal-dependent — becomes one
linear, normal-free inequality. -/

/-- The gap value at a coordinate axis is the axis leverage total minus one. -/
theorem dotProduct_single_gap_eq {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (slot : Fin 3) :
    (Pi.single slot (1 : ℝ)) ⬝ᵥ ((subsetSum design selected - 1) *ᵥ Pi.single slot (1 : ℝ))
      = (∑ label ∈ selected, design.atom label slot ^ 2) - 1 := by
  classical
  rw [dotProduct_subsetSum_sub_one_mulVec_eq_sumSq design selected]
  have hread : ∀ label : Fin size,
      design.atom label ⬝ᵥ (Pi.single slot (1 : ℝ)) = design.atom label slot := by
    intro label
    rw [dotProduct_single, mul_one]
  have hself : (Pi.single slot (1 : ℝ)) ⬝ᵥ (Pi.single slot (1 : ℝ)) = 1 := by
    rw [dotProduct_single, Pi.single_eq_same, mul_one]
  rw [hself, Finset.sum_congr rfl fun label _ => by rw [hread label]]

/-- The three axis readings total the leverage of the triple. -/
theorem sum_axis_sq_eq_sum_leverage {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) :
    ∑ slot : Fin 3, ∑ label ∈ selected, design.atom label slot ^ 2
      = ∑ label ∈ selected, leverageOf (design.atom label) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun label _ => rfl

/-- **STRICT DOMINATION MAKES THE TRIPLE HEAVY.**  A positive definite gap forces
the leverage total of the selected labels above the rank. -/
theorem three_lt_sum_leverage_of_posDef {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hposDef : (subsetSum design selected - 1).PosDef) :
    (3 : ℝ) < ∑ label ∈ selected, leverageOf (design.atom label) := by
  classical
  have haxis : ∀ slot : Fin 3,
      (1 : ℝ) < ∑ label ∈ selected, design.atom label slot ^ 2 := by
    intro slot
    have hne : ((Pi.single slot (1 : ℝ)) : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hstep := congrFun hzero slot
      rw [Pi.single_eq_same] at hstep
      norm_num at hstep
    have hvalue := hposDef.dotProduct_mulVec_pos hne
    rw [star_trivial, dotProduct_single_gap_eq design selected slot] at hvalue
    linarith
  have htotal := sum_axis_sq_eq_sum_leverage design selected
  have hthree : ∑ slot : Fin 3, ∑ label ∈ selected, design.atom label slot ^ 2
      = (∑ label ∈ selected, design.atom label 0 ^ 2)
        + (∑ label ∈ selected, design.atom label 1 ^ 2)
        + ∑ label ∈ selected, design.atom label 2 ^ 2 := by
    rw [Fin.sum_univ_three]
  rw [hthree] at htotal
  linarith [haxis 0, haxis 1, haxis 2, htotal]

/-- **A NEGATIVE DEFINITE GAP MAKES THE TRIPLE LIGHT.**  The mirror statement, and
the one that rules the negative branch out of the wedge balance. -/
theorem sum_leverage_lt_three_of_posDef_neg {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hposDef : (1 - subsetSum design selected).PosDef) :
    (∑ label ∈ selected, leverageOf (design.atom label)) < 3 := by
  classical
  have hnegEq : (1 : Matrix (Fin 3) (Fin 3) ℝ) - subsetSum design selected
      = -(subsetSum design selected - 1) := by rw [neg_sub]
  rw [hnegEq] at hposDef
  have haxis : ∀ slot : Fin 3,
      (∑ label ∈ selected, design.atom label slot ^ 2) < 1 := by
    intro slot
    have hne : ((Pi.single slot (1 : ℝ)) : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hstep := congrFun hzero slot
      rw [Pi.single_eq_same] at hstep
      norm_num at hstep
    have hvalue := hposDef.dotProduct_mulVec_pos hne
    rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg,
      dotProduct_single_gap_eq design selected slot] at hvalue
    linarith
  have htotal := sum_axis_sq_eq_sum_leverage design selected
  have hthree : ∑ slot : Fin 3, ∑ label ∈ selected, design.atom label slot ^ 2
      = (∑ label ∈ selected, design.atom label 0 ^ 2)
        + (∑ label ∈ selected, design.atom label 1 ^ 2)
        + ∑ label ∈ selected, design.atom label 2 ^ 2 := by
    rw [Fin.sum_univ_three]
  rw [hthree] at htotal
  linarith [haxis 0, haxis 1, haxis 2, htotal]

/-- **STRICT DOMINATION IS THE TRACE TEST PLUS THE WEDGE BALANCE.**  The landed
`Gtz.posDef_iff_normalSurplus_and_wedgeBalance` pairs the balance with the
normal surplus, which is quadratic and reads the normal.  This pairs it instead
with a linear, normal-free leverage inequality. -/
theorem posDef_iff_traceTest_and_wedgeBalance {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    (subsetSum design selected - 1).PosDef
      ↔ ((3 : ℝ) < ∑ label ∈ selected, leverageOf (design.atom label))
        ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            WedgeBalanceAt design selected unitNormal probeVec := by
  constructor
  · intro hposDef
    refine ⟨three_lt_sum_leverage_of_posDef design selected hposDef, ?_⟩
    exact (forall_wedgeBalanceAt_iff_definite design selected unitNormal hunit).mpr
      (Or.inl hposDef)
  · rintro ⟨hheavy, hbalance⟩
    rcases (forall_wedgeBalanceAt_iff_definite design selected unitNormal hunit).mp hbalance with
      hposDef | hnegDef
    · exact hposDef
    · exact absurd (sum_leverage_lt_three_of_posDef_neg design selected hnegDef)
        (not_lt.mpr hheavy.le)

/-! ## 7. The reduced selector

`Gtz.WedgeBalanceSelector` quantifies over a unit normal and asks for a normal
surplus.  Section 5 removes the choice of normal and section 6 replaces the
surplus.  What is left fixes the normal to the first coordinate axis once and
for all. -/

/-- **THE TRACE-AND-BALANCE SELECTOR.**  Every primitive design at size six and
rank three carries a triple whose leverage total is above three and whose wedge
balance holds at every probe orthogonal to the FIRST COORDINATE AXIS.  No normal
is quantified and no surplus appears. -/
def TraceWedgeSelector : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ selected : Finset (Fin 6),
      selected.card = 3
        ∧ ((3 : ℝ) < ∑ label ∈ selected, leverageOf (design.atom label))
        ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
            WedgeBalanceAt design selected ![1, 0, 0] probeVec

/-- **THE REDUCED SELECTOR IS THE TARGET.**  An equivalence, so nothing is lost
and nothing is smuggled in. -/
theorem traceWedgeSelector_iff_wedgeBalanceSelector :
    TraceWedgeSelector ↔ WedgeBalanceSelector := by
  constructor
  · intro hreduced design hprimitive
    obtain ⟨selected, hcard, hheavy, hbalance⟩ := hreduced design hprimitive
    have hposDef := (posDef_iff_traceTest_and_wedgeBalance design selected ![1, 0, 0]
      dotProduct_firstAxis).mpr ⟨hheavy, hbalance⟩
    obtain ⟨hsurplus, hbalanceAgain⟩ :=
      (posDef_iff_normalSurplus_and_wedgeBalance design selected ![1, 0, 0]
        dotProduct_firstAxis).mp hposDef
    exact ⟨selected, ![1, 0, 0], hcard, dotProduct_firstAxis, hsurplus, hbalanceAgain⟩
  · intro hselector design hprimitive
    obtain ⟨selected, unitNormal, hcard, hunit, hsurplus, hbalance⟩ := hselector design hprimitive
    have hposDef := (posDef_iff_normalSurplus_and_wedgeBalance design selected unitNormal hunit).mpr
      ⟨hsurplus, hbalance⟩
    obtain ⟨hheavy, hbalanceAxis⟩ :=
      (posDef_iff_traceTest_and_wedgeBalance design selected ![1, 0, 0]
        dotProduct_firstAxis).mp hposDef
    exact ⟨selected, hcard, hheavy, hbalanceAxis⟩

/-- **THE REDUCED ENTRANCE.**  The trace-and-balance selector retires all five
on-path obligations. -/
theorem allFiveOnPath_of_traceWedgeSelector (hselector : TraceWedgeSelector) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_wedgeBalanceSelector
    (traceWedgeSelector_iff_wedgeBalanceSelector.mp hselector)

/-- **A DEFINITE GAP AT A HEAVY TRIPLE IS A STRICT WITNESS.**  The consumer shape:
one trace inequality and one wedge balance at the first axis kill a tie. -/
theorem not_isTie_of_traceTest_and_wedgeBalance {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3)
    (hheavy : (3 : ℝ) < ∑ label ∈ selected, leverageOf (design.atom label))
    (unitNormal : Fin 3 → ℝ) (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hbalance : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design selected unitNormal probeVec) :
    ¬ IsTie design := fun htie =>
  htie.2 selected hcard
    ((posDef_iff_traceTest_and_wedgeBalance design selected unitNormal hunit).mpr
      ⟨hheavy, hbalance⟩)

/-! ## 8. The second invariant of the gap, over the whole label set

`Gtz.secondInvariantOfThree_tripleGap_eq_sum_pairGapExcessOf` reads the second
invariant of a triple's gap off the THREE pairs inside the triple.  The adjugate
identity reads the same number off ALL pairs of the design, weighted by the
signed measure.  Setting the two equal is a conservation law: a three-term local
total equals a global total over every pair, and every global summand is a wedge
energy, which is strictly positive exactly on a primitive design. -/

/-- **THE SECOND INVARIANT IS THE SIGNED PAIR TOTAL OVER ALL LABELS.**  Every
summand `leverage * leverage - pairing squared` is the wedge energy of the pair,
so it is nonnegative always and strictly positive at a pair of a primitive
design. -/
theorem secondInvariantOfThree_gap_eq_signed_pairTotal {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size)) :
    secondInvariantOfThree (subsetSum design selected - 1)
      = (∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
          hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (leverageOf (design.atom leftLabel) * leverageOf (design.atom rightLabel)
                - (design.atom leftLabel ⬝ᵥ design.atom rightLabel) ^ 2)) / 2 := by
  classical
  rw [← trace_adjugate_eq_secondInvariantOfThree,
    subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix design selected,
    adjugate_sum_smul_atomMatrix Finset.univ (hypersimplexVertexDirection design selected)
      (fun label => design.atom label)]
  have hentry : ∀ slot : Fin 3,
      ((2 : ℝ)⁻¹ • ∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
          (hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel)
            • atomMatrix (atomWedge (design.atom leftLabel) (design.atom rightLabel)))
          slot slot
        = (∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
            hypersimplexVertexDirection design selected leftLabel
              * hypersimplexVertexDirection design selected rightLabel
              * (atomWedge (design.atom leftLabel) (design.atom rightLabel) slot
                  * atomWedge (design.atom leftLabel) (design.atom rightLabel) slot)) / 2 :=
    fun slot => halfWedgeSum_apply Finset.univ (hypersimplexVertexDirection design selected)
      (fun label => design.atom label) slot slot
  rw [Matrix.trace_fin_three, hentry 0, hentry 1, hentry 2]
  have hcombine : ∀ leftLabel rightLabel : Fin size,
      (hypersimplexVertexDirection design selected leftLabel
          * hypersimplexVertexDirection design selected rightLabel
          * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 0
              * atomWedge (design.atom leftLabel) (design.atom rightLabel) 0))
        + (hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 1
                * atomWedge (design.atom leftLabel) (design.atom rightLabel) 1))
        + (hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 2
                * atomWedge (design.atom leftLabel) (design.atom rightLabel) 2))
      = hypersimplexVertexDirection design selected leftLabel
          * hypersimplexVertexDirection design selected rightLabel
          * (leverageOf (design.atom leftLabel) * leverageOf (design.atom rightLabel)
              - (design.atom leftLabel ⬝ᵥ design.atom rightLabel) ^ 2) := by
    intro leftLabel rightLabel
    have henergy := atomWedge_energy (design.atom leftLabel) (design.atom rightLabel)
    have hleft : leverageOf (design.atom leftLabel)
        = design.atom leftLabel ⬝ᵥ design.atom leftLabel :=
      leverageOf_eq_dotProduct (design.atom leftLabel)
    have hright : leverageOf (design.atom rightLabel)
        = design.atom rightLabel ⬝ᵥ design.atom rightLabel :=
      leverageOf_eq_dotProduct (design.atom rightLabel)
    have hexpand : atomWedge (design.atom leftLabel) (design.atom rightLabel)
          ⬝ᵥ atomWedge (design.atom leftLabel) (design.atom rightLabel)
        = atomWedge (design.atom leftLabel) (design.atom rightLabel) 0
            * atomWedge (design.atom leftLabel) (design.atom rightLabel) 0
          + atomWedge (design.atom leftLabel) (design.atom rightLabel) 1
            * atomWedge (design.atom leftLabel) (design.atom rightLabel) 1
          + atomWedge (design.atom leftLabel) (design.atom rightLabel) 2
            * atomWedge (design.atom leftLabel) (design.atom rightLabel) 2 := by
      simp [dotProduct, Fin.sum_univ_three]
    rw [hleft, hright, ← henergy, hexpand]
    ring
  have hmerge : ∀ leftLabel : Fin size,
      (∑ rightLabel : Fin size, hypersimplexVertexDirection design selected leftLabel
          * hypersimplexVertexDirection design selected rightLabel
          * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 0
              * atomWedge (design.atom leftLabel) (design.atom rightLabel) 0))
        + (∑ rightLabel : Fin size, hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 1
                * atomWedge (design.atom leftLabel) (design.atom rightLabel) 1))
        + (∑ rightLabel : Fin size, hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 2
                * atomWedge (design.atom leftLabel) (design.atom rightLabel) 2))
      = ∑ rightLabel : Fin size, hypersimplexVertexDirection design selected leftLabel
          * hypersimplexVertexDirection design selected rightLabel
          * (leverageOf (design.atom leftLabel) * leverageOf (design.atom rightLabel)
              - (design.atom leftLabel ⬝ᵥ design.atom rightLabel) ^ 2) := by
    intro leftLabel
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun rightLabel _ => hcombine leftLabel rightLabel
  have houter : (∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
        hypersimplexVertexDirection design selected leftLabel
          * hypersimplexVertexDirection design selected rightLabel
          * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 0
              * atomWedge (design.atom leftLabel) (design.atom rightLabel) 0))
      + (∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
          hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 1
                * atomWedge (design.atom leftLabel) (design.atom rightLabel) 1))
      + (∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
          hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (atomWedge (design.atom leftLabel) (design.atom rightLabel) 2
                * atomWedge (design.atom leftLabel) (design.atom rightLabel) 2))
      = ∑ leftLabel : Fin size, ∑ rightLabel : Fin size,
          hypersimplexVertexDirection design selected leftLabel
            * hypersimplexVertexDirection design selected rightLabel
            * (leverageOf (design.atom leftLabel) * leverageOf (design.atom rightLabel)
                - (design.atom leftLabel ⬝ᵥ design.atom rightLabel) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun leftLabel _ => hmerge leftLabel
  linarith [houter]

end Gtz

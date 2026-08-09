/-
# FIRST-TOUCH RIGIDITY at a boundary pair — and the refutation of the briefed sign

A pair of labels `(i, j)` sits on the **live boundary** when the two by two leading
minor of `Gram - I` at that pair vanishes, `pairGapExcessOf D i j = 0`, while the
first atom is heavy, `0 < heavyExcess D i`.  This file settles what the tie leg
`discriminantTie` does at every completion of such a pair.

## THE HEADLINE IS SIGN-FLIPPED RELATIVE TO THE BRIEF

The briefed conclusion was "there EXISTS a label `c` with `discriminantTie`
strictly POSITIVE".  That is FALSE, and this file proves the exact opposite in
full generality.  The tree's `Gtz.discriminantTie` satisfies, with
`Q := pairAdjugateForm`,

    discriminantTie D c i j = heavyExcess D c * pairGapExcessOf D i j - Q(atom c),

so at `pairGapExcessOf D i j = 0` the tie leg is `-Q(atom c)`, and the perfect
square of `heavyExcess_mul_pairAdjugateForm` makes `Q` NONNEGATIVE.  The brief
resolved the "up to sign" the wrong way.  The tree's own shipped row law
`Gtz.sum_weight_mul_discriminantTie` independently certifies the minus: averaging
gives `-(u_i + u_j)`, which the opposite sign convention would render `+(u_i + u_j)`.

`boundaryPairDesign` below is an explicit weighted `(4,3)` design, all data
rational, whose pair `(3, 0)` meets EVERY briefed hypothesis — heavy first atom,
non-parallel atoms, zero pair gap excess — and at which no completion whatsoever
has a positive tie leg.  So the refutation is not vacuous.

## What IS true, and is proved here without hypotheses beyond the design axioms

* `heavyExcess_mul_discriminantTie_eq_pairGapExcessOf_mul_sub_sq` — THE MASTER
  IDENTITY, no hypotheses at all:

      u_i * discriminantTie D c i j
        = pairGapExcessOf D i j * pairGapExcessOf D i c - (firstTouchNormal . atom c)^2

  where `firstTouchNormal D i j := <g_i,g_j> * g_i - u_i * g_j`.  The tie leg is a
  product of two pair minors MINUS a square; everything below is a reading of it.
* `discriminantTie_nonpos_of_pairGapExcessOf_eq_zero` — at a boundary pair the tie
  leg is nonpositive at EVERY completion, the pair's own members included.
* `discriminantTie_eq_zero_iff_firstTouchNormal_dotProduct_eq_zero` — the equality
  locus is exactly the plane orthogonal to the first-touch normal.
* `exists_offPair_neg_discriminantTie_of_pairGapExcessOf_eq_zero` — THE HEADLINE.
  Some GENUINE completion (distinct from both pair members) has strictly negative
  tie leg.  The brief routed this through non-parallelism of the pair; that
  hypothesis is NOT needed — the design axioms give the normal's nonvanishing for
  free, because `firstTouchNormal . g_j = -(E + u_i)`, which is `-u_i` at `E = 0`.
* `sq_firstTouchNormal_dotProduct_le_of_dominates` — the quantitative rigidity cap:
  in a DOMINATING triple the third atom's deviation from the first-touch plane is
  bounded by the product of the two pair minors through `i`.  At a boundary pair
  the bound is zero, so the completion is pinned to the plane; and
  `exists_offPair_not_dominates_of_pairGapExcessOf_eq_zero` exhibits an atom off it.
* `surplusForm_neg_of_pairGapExcessOf_eq_zero` — THE SIGN COMPANION, wired to the
  landed `Gtz.sum_offPair_weight_mul_discriminantTie` of
  `Gtz/Quantitative/TieRowLaw.lean`.  The briefed contradiction ("a heavy design
  with a live-boundary pair and a nonpositive off-pair average is impossible") is
  also refuted: the off-pair average at a boundary pair is FORCED nonpositive, in
  fact strictly negative.  What the wiring buys instead is a new barrier — the
  surplus form is strictly negative at every boundary pair, with no `AllHeavy` and
  no weight-concentration hypothesis, so the landed positive criterion
  `Gtz.exists_pos_discriminantTie_of_pos_surplusForm` can never fire there.

Nothing here is landed in the tree; this file is a scratch deliverable.
-/
import Gtz.Design.GeneralRankAveraging
import Gtz.Quantitative.TieRowLaw
import Gtz.Quantitative.PositivstellensatzRankThree
import Gtz.Design.RhoNormalForm
import Gtz.Reduction.RealVolumeFloor
import Gtz.Core.Sanity
import Gtz.Certificates.CollarChartReplay
import Gtz.Design.LeverageBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## Part 1 — the first-touch normal of an ordered pair -/

/-- **The first-touch normal** of the ordered pair `(i, j)`:
`<g_i, g_j> * g_i - (|g_i|^2 - 1) * g_j`.  It is the direction that detects the
degeneracy of the pair's gap minor: `heavyExcess_mul_pairAdjugateForm` shows the
pair's adjugate form is this normal's squared pairing plus the pair minor times
the first atom's squared pairing, so at a vanishing minor the adjugate form is a
pure square in this normal. -/
def firstTouchNormal (design : WeightedDesign size 3) (firstLabel secondLabel : Fin size) :
    Fin 3 → ℝ :=
  atomPairing design firstLabel secondLabel • design.atom firstLabel
    - heavyExcess design firstLabel • design.atom secondLabel

/-- The normal pairs against an arbitrary probe through the pair's two projections. -/
theorem firstTouchNormal_dotProduct (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) (probeVec : Fin 3 → ℝ) :
    firstTouchNormal design firstLabel secondLabel ⬝ᵥ probeVec
      = atomPairing design firstLabel secondLabel * (design.atom firstLabel ⬝ᵥ probeVec)
        - heavyExcess design firstLabel * (design.atom secondLabel ⬝ᵥ probeVec) := by
  simp [firstTouchNormal, sub_dotProduct, smul_dotProduct]

/-- The normal against an atom, in the six scalars of the triple. -/
theorem firstTouchNormal_dotProduct_atom (design : WeightedDesign size 3)
    (firstLabel secondLabel pivotLabel : Fin size) :
    firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel
      = atomPairing design firstLabel secondLabel * atomPairing design firstLabel pivotLabel
        - heavyExcess design firstLabel * atomPairing design secondLabel pivotLabel :=
  firstTouchNormal_dotProduct design firstLabel secondLabel (design.atom pivotLabel)

/-- Against the pair's FIRST member the normal returns the pairing itself. -/
theorem firstTouchNormal_dotProduct_atom_first (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) :
    firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom firstLabel
      = atomPairing design firstLabel secondLabel := by
  simp only [firstTouchNormal_dotProduct_atom, heavyExcess, atomPairing,
    leverageOf_eq_dotProduct, dotProduct_comm (design.atom secondLabel) (design.atom firstLabel)]
  ring

/-- Against the pair's SECOND member the normal returns minus the pair minor
shifted by the first excess.  This is the step that makes non-parallelism
unnecessary: at a boundary pair the value is `-u_i`, nonzero as soon as `u_i` is. -/
theorem firstTouchNormal_dotProduct_atom_second (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) :
    firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom secondLabel
      = -(pairGapExcessOf design firstLabel secondLabel + heavyExcess design firstLabel) := by
  simp only [firstTouchNormal_dotProduct_atom, pairGapExcessOf, gapExcessOf, gapPairingOf,
    heavyExcess, atomPairing, leverageOf_eq_dotProduct]
  ring

/-- The normal's squared length, in the pair's own scalars. -/
theorem firstTouchNormal_dotProduct_self (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) :
    firstTouchNormal design firstLabel secondLabel
        ⬝ᵥ firstTouchNormal design firstLabel secondLabel
      = heavyExcess design firstLabel * pairGapExcessOf design firstLabel secondLabel
        + atomPairing design firstLabel secondLabel ^ 2
        + heavyExcess design firstLabel ^ 2 := by
  rw [firstTouchNormal_dotProduct design firstLabel secondLabel
      (firstTouchNormal design firstLabel secondLabel),
    dotProduct_comm (design.atom firstLabel) (firstTouchNormal design firstLabel secondLabel),
    dotProduct_comm (design.atom secondLabel) (firstTouchNormal design firstLabel secondLabel),
    firstTouchNormal_dotProduct_atom_first, firstTouchNormal_dotProduct_atom_second]
  ring

/-! ## Part 2 — the adjugate form and the master identity -/

/-- **The pair's adjugate form** at a probe: the quadratic form of the adjugate of
the pair's gap minor, evaluated at the probe's two projections.  Written out,
`u_j * A^2 - 2 p A B + u_i * B^2` with `A = <g_i, x>`, `B = <g_j, x>`. -/
def pairAdjugateForm (design : WeightedDesign size 3) (firstLabel secondLabel : Fin size)
    (probeVec : Fin 3 → ℝ) : ℝ :=
  heavyExcess design secondLabel * (design.atom firstLabel ⬝ᵥ probeVec) ^ 2
    - 2 * atomPairing design firstLabel secondLabel
        * (design.atom firstLabel ⬝ᵥ probeVec) * (design.atom secondLabel ⬝ᵥ probeVec)
    + heavyExcess design firstLabel * (design.atom secondLabel ⬝ᵥ probeVec) ^ 2

/-- **THE COMPLETED SQUARE, at an arbitrary probe and with no hypotheses.**
`u_i` times the adjugate form is the normal's squared pairing plus the pair minor
times the first atom's squared pairing.  At a vanishing pair minor the adjugate
form is therefore a pure square divided by `u_i` — that is the whole of "first
touch". -/
theorem heavyExcess_mul_pairAdjugateForm (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) (probeVec : Fin 3 → ℝ) :
    heavyExcess design firstLabel * pairAdjugateForm design firstLabel secondLabel probeVec
      = (firstTouchNormal design firstLabel secondLabel ⬝ᵥ probeVec) ^ 2
        + pairGapExcessOf design firstLabel secondLabel
            * (design.atom firstLabel ⬝ᵥ probeVec) ^ 2 := by
  rw [firstTouchNormal_dotProduct]
  simp only [pairAdjugateForm, pairGapExcessOf, gapExcessOf, gapPairingOf, heavyExcess,
    atomPairing, leverageOf_eq_dotProduct]
  ring

/-- **THE SIGN, spelled out.**  The tie leg is the pivot's excess times the pair
minor MINUS the pair's adjugate form at the pivot atom — not plus, and not the
other way round.  Every claim in this file that contradicts the brief descends
from this one `ring` identity. -/
theorem discriminantTie_eq_heavyExcess_mul_pairGapExcessOf_sub_pairAdjugateForm
    (design : WeightedDesign size 3) (pivotLabel firstLabel secondLabel : Fin size) :
    discriminantTie design pivotLabel firstLabel secondLabel
      = heavyExcess design pivotLabel * pairGapExcessOf design firstLabel secondLabel
        - pairAdjugateForm design firstLabel secondLabel (design.atom pivotLabel) := by
  simp only [discriminantTie, pairAdjugateForm, pairGapExcessOf, gapExcessOf, gapPairingOf,
    heavyExcess, atomPairing, leverageOf_eq_dotProduct,
    dotProduct_comm (design.atom pivotLabel) (design.atom firstLabel),
    dotProduct_comm (design.atom pivotLabel) (design.atom secondLabel)]

/-- **THE MASTER IDENTITY.**  No hypotheses whatsoever: the first atom's excess
times the tie leg is the product of the two pair minors through that atom, minus
the squared pairing of the first-touch normal against the pivot atom.

This is the Desnanot-Jacobi reading of `det(Gram - I)` anchored at `firstLabel`;
the tree's own `schurDet_eq_excess_mul_tie` is the same fact anchored at the pivot
slot, but it is `private`, so the identity is re-derived here by `ring` rather
than spent. -/
theorem heavyExcess_mul_discriminantTie_eq_pairGapExcessOf_mul_sub_sq
    (design : WeightedDesign size 3) (pivotLabel firstLabel secondLabel : Fin size) :
    heavyExcess design firstLabel * discriminantTie design pivotLabel firstLabel secondLabel
      = pairGapExcessOf design firstLabel secondLabel
          * pairGapExcessOf design firstLabel pivotLabel
        - (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2 := by
  rw [firstTouchNormal_dotProduct_atom]
  simp only [pairGapExcessOf, gapExcessOf, gapPairingOf, discriminantTie, heavyExcess,
    atomPairing, dotProduct_comm (design.atom pivotLabel) (design.atom firstLabel),
    dotProduct_comm (design.atom pivotLabel) (design.atom secondLabel)]
  ring

/-! ## Part 2b — the sign, certified against the tree's own shipped row law

The bridge above says `discriminantTie = u_c * E - Q`.  Averaging it against the
design's weights must reproduce `Gtz.sum_weight_mul_discriminantTie`, which is
`-(u_i + u_j)`.  It does, and it pins the sign: with the opposite convention the
average would come out `+(u_i + u_j)`, contradicting a shipped theorem whenever the
two excesses do not cancel.  The aggregate below is the identity that carries the
check. -/

/-- The weighted excesses of a rank-three design total `2`. -/
theorem sum_weight_mul_heavyExcess (design : WeightedDesign size 3) :
    ∑ pivotLabel, design.weight pivotLabel * heavyExcess design pivotLabel = 2 := by
  have hshipped := sum_weight_mul_gapExcessOf design
  simp only [gapExcessOf_eq_heavyExcess] at hshipped
  rw [hshipped]
  norm_num

/-- **THE ADJUGATE AGGREGATE.**  The weighted average of the pair's adjugate form
over the atoms is `2 E + u_i + u_j`, for every design, every pair and every weight
vector.  Together with the bridge this REPRODUCES the shipped row law
`Gtz.sum_weight_mul_discriminantTie`, which is what certifies the minus sign. -/
theorem sum_weight_mul_pairAdjugateForm_atom (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) :
    ∑ pivotLabel, design.weight pivotLabel
        * pairAdjugateForm design firstLabel secondLabel (design.atom pivotLabel)
      = 2 * pairGapExcessOf design firstLabel secondLabel
        + heavyExcess design firstLabel + heavyExcess design secondLabel := by
  have hbridge : ∀ pivotLabel : Fin size,
      design.weight pivotLabel
          * pairAdjugateForm design firstLabel secondLabel (design.atom pivotLabel)
        = pairGapExcessOf design firstLabel secondLabel
            * (design.weight pivotLabel * heavyExcess design pivotLabel)
          - design.weight pivotLabel
              * discriminantTie design firstLabel secondLabel pivotLabel := by
    intro pivotLabel
    rw [discriminantTie_rotate design firstLabel secondLabel pivotLabel,
      discriminantTie_eq_heavyExcess_mul_pairGapExcessOf_sub_pairAdjugateForm]
    ring
  rw [Finset.sum_congr rfl fun pivotLabel _ => hbridge pivotLabel, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_weight_mul_heavyExcess,
    sum_weight_mul_discriminantTie design firstLabel secondLabel]
  ring

/-! ## Part 3 — the boundary pair: universal nonpositivity and the equality locus -/

/-- At a boundary pair the master identity collapses to minus a square. -/
theorem heavyExcess_mul_discriminantTie_of_pairGapExcessOf_eq_zero
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) (pivotLabel : Fin size) :
    heavyExcess design firstLabel * discriminantTie design pivotLabel firstLabel secondLabel
      = -(firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2 := by
  rw [heavyExcess_mul_discriminantTie_eq_pairGapExcessOf_mul_sub_sq, hboundary, zero_mul,
    zero_sub]

/-- **THE UNIVERSAL CAP.**  At a boundary pair with heavy first atom the tie leg is
nonpositive at EVERY completion — including the two degenerate ones that repeat a
pair member.  This is the exact negation of the briefed conclusion. -/
theorem discriminantTie_nonpos_of_pairGapExcessOf_eq_zero (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) (pivotLabel : Fin size) :
    discriminantTie design pivotLabel firstLabel secondLabel ≤ 0 := by
  by_contra hpositive
  have hproduct : 0 < heavyExcess design firstLabel
      * discriminantTie design pivotLabel firstLabel secondLabel :=
    mul_pos hheavy (not_le.mp hpositive)
  rw [heavyExcess_mul_discriminantTie_of_pairGapExcessOf_eq_zero design hboundary] at hproduct
  linarith [sq_nonneg (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel)]

/-- **THE SUB-BOUNDARY CAP.**  The nonpositivity survives past the boundary: as soon
as the anchored pair minor is nonpositive and the cross minor through the anchor is
nonnegative, the tie leg is nonpositive.  The boundary case is `hpairNonpos` at
equality; a dominating triple always supplies `hcrossNonneg`. -/
theorem discriminantTie_nonpos_of_pairGapExcessOf_nonpos (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hheavy : 0 < heavyExcess design firstLabel)
    (hpairNonpos : pairGapExcessOf design firstLabel secondLabel ≤ 0) (pivotLabel : Fin size)
    (hcrossNonneg : 0 ≤ pairGapExcessOf design firstLabel pivotLabel) :
    discriminantTie design pivotLabel firstLabel secondLabel ≤ 0 := by
  by_contra hpositive
  have hproduct : 0 < heavyExcess design firstLabel
      * discriminantTie design pivotLabel firstLabel secondLabel :=
    mul_pos hheavy (not_le.mp hpositive)
  rw [heavyExcess_mul_discriminantTie_eq_pairGapExcessOf_mul_sub_sq] at hproduct
  nlinarith [sq_nonneg (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel),
    hpairNonpos, hcrossNonneg]

/-- A boundary pair is a genuine positive-semidefinite boundary: the partner's excess
cannot be negative once the anchor is heavy and the minor vanishes. -/
theorem heavyExcess_second_nonneg_of_pairGapExcessOf_eq_zero (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    0 ≤ heavyExcess design secondLabel := by
  rw [pairGapExcessOf, gapExcessOf_eq_heavyExcess, gapExcessOf_eq_heavyExcess,
    gapPairingOf_eq_atomPairing] at hboundary
  by_contra hnegative
  have hproduct : heavyExcess design firstLabel * heavyExcess design secondLabel < 0 :=
    mul_neg_of_pos_of_neg hheavy (not_le.mp hnegative)
  nlinarith [sq_nonneg (atomPairing design firstLabel secondLabel)]

/-- **THE EQUALITY LOCUS.**  At a boundary pair the tie leg vanishes at exactly the
completions lying in the plane orthogonal to the first-touch normal. -/
theorem discriminantTie_eq_zero_iff_firstTouchNormal_dotProduct_eq_zero
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) (pivotLabel : Fin size) :
    discriminantTie design pivotLabel firstLabel secondLabel = 0
      ↔ firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel = 0 := by
  have hkey := heavyExcess_mul_discriminantTie_of_pairGapExcessOf_eq_zero design hboundary
    pivotLabel
  constructor
  · intro hvanishes
    rw [hvanishes, mul_zero] at hkey
    exact sq_eq_zero_iff.mp (by linarith)
  · intro horthogonal
    rw [horthogonal] at hkey
    have hmulZero : heavyExcess design firstLabel
        * discriminantTie design pivotLabel firstLabel secondLabel = 0 := by
      rw [hkey]; ring
    exact (mul_eq_zero.mp hmulZero).resolve_left hheavy.ne'

/-- The strict companion of the equality locus. -/
theorem discriminantTie_neg_iff_firstTouchNormal_dotProduct_ne_zero
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) (pivotLabel : Fin size) :
    discriminantTie design pivotLabel firstLabel secondLabel < 0
      ↔ firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel ≠ 0 := by
  have hlocus := discriminantTie_eq_zero_iff_firstTouchNormal_dotProduct_eq_zero design hheavy
    hboundary pivotLabel
  constructor
  · intro hnegative horthogonal
    rw [hlocus.mpr horthogonal] at hnegative
    exact lt_irrefl 0 hnegative
  · intro hoffPlane
    rcases lt_or_eq_of_le (discriminantTie_nonpos_of_pairGapExcessOf_eq_zero design hheavy
      hboundary pivotLabel) with hstrict | hequal
    · exact hstrict
    · exact absurd (hlocus.mp hequal) hoffPlane

/-! ## Part 4 — Parseval produces a genuine off-pair witness -/

/-- Two distinct labels can only exist when the design has at least two atoms. -/
theorem two_le_size_of_labels_ne {firstLabel secondLabel : Fin size}
    (hdistinct : firstLabel ≠ secondLabel) : 2 ≤ size := by
  have hcard : 1 < Fintype.card (Fin size) :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨firstLabel, secondLabel, hdistinct⟩
  rw [Fintype.card_fin] at hcard
  omega

/-- Parseval, read at the first-touch normal. -/
theorem sum_weight_mul_sq_firstTouchNormal_dotProduct (design : WeightedDesign size 3)
    (firstLabel secondLabel : Fin size) :
    ∑ pivotLabel, design.weight pivotLabel
        * (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2
      = heavyExcess design firstLabel * pairGapExcessOf design firstLabel secondLabel
        + atomPairing design firstLabel secondLabel ^ 2
        + heavyExcess design firstLabel ^ 2 := by
  rw [← firstTouchNormal_dotProduct_self design firstLabel secondLabel,
    dotProduct_self_eq_sum_weight_mul_sq design (firstTouchNormal design firstLabel secondLabel)]
  exact Finset.sum_congr rfl fun pivotLabel _ => by
    rw [dotProduct_comm (design.atom pivotLabel) (firstTouchNormal design firstLabel secondLabel)]

/-- Peeling the pair's own two labels off the Parseval sum leaves an exact
expression in the pair's data — at any pair minor, boundary or not. -/
theorem sum_offPair_weight_mul_sq_firstTouchNormal_dotProduct (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel) :
    ∑ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel, design.weight pivotLabel
        * (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2
      = heavyExcess design firstLabel * pairGapExcessOf design firstLabel secondLabel
          + atomPairing design firstLabel secondLabel ^ 2
          + heavyExcess design firstLabel ^ 2
        - design.weight firstLabel * atomPairing design firstLabel secondLabel ^ 2
        - design.weight secondLabel
            * (pairGapExcessOf design firstLabel secondLabel
                + heavyExcess design firstLabel) ^ 2 := by
  classical
  have hsecondMember : secondLabel ∈ Finset.univ.erase firstLabel :=
    Finset.mem_erase.mpr ⟨Ne.symm hdistinct, Finset.mem_univ secondLabel⟩
  have hpeelFirst := Finset.add_sum_erase (Finset.univ : Finset (Fin size))
    (fun pivotLabel => design.weight pivotLabel
      * (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2)
    (Finset.mem_univ firstLabel)
  have hpeelSecond := Finset.add_sum_erase (Finset.univ.erase firstLabel)
    (fun pivotLabel => design.weight pivotLabel
      * (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2)
    hsecondMember
  have htotal := sum_weight_mul_sq_firstTouchNormal_dotProduct design firstLabel secondLabel
  rw [firstTouchNormal_dotProduct_atom_first] at hpeelFirst
  rw [firstTouchNormal_dotProduct_atom_second] at hpeelSecond
  rw [← hpeelSecond] at hpeelFirst
  linear_combination hpeelFirst + htotal

/-- **THE OFF-PAIR MASS IS STRICTLY POSITIVE.**  At a boundary pair with heavy first
atom the genuine completions carry positive Parseval mass against the first-touch
normal.  No non-parallelism hypothesis: the second pair member alone contributes
`u_i^2 (1 - t_j)`, and every weight of a design with two labels is below one. -/
theorem sum_offPair_weight_mul_sq_firstTouchNormal_dotProduct_pos
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hdistinct : firstLabel ≠ secondLabel) (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    0 < ∑ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel, design.weight pivotLabel
        * (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2 := by
  rw [sum_offPair_weight_mul_sq_firstTouchNormal_dotProduct design hdistinct, hboundary]
  have htwoLabels : 2 ≤ size := two_le_size_of_labels_ne hdistinct
  have hfirstWeight := weight_lt_one design htwoLabels firstLabel
  have hsecondWeight := weight_lt_one design htwoLabels secondLabel
  have hpairingTerm : 0 ≤ atomPairing design firstLabel secondLabel ^ 2
      * (1 - design.weight firstLabel) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hexcessTerm : 0 < heavyExcess design firstLabel ^ 2 * (1 - design.weight secondLabel) :=
    mul_pos (pow_pos hheavy 2) (by linarith)
  nlinarith [hpairingTerm, hexcessTerm]

/-- **THE WITNESS.**  At a boundary pair with heavy first atom some GENUINE
completion — a label distinct from both pair members — lies off the first-touch
plane. -/
theorem exists_offPair_firstTouchNormal_dotProduct_ne_zero (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    ∃ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
      firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel ≠ 0 := by
  by_contra hnone
  have hallOnPlane : ∀ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
      firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel = 0 := by
    intro pivotLabel hmember
    by_contra hoffPlane
    exact hnone ⟨pivotLabel, hmember, hoffPlane⟩
  have hvanishes : ∑ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
      design.weight pivotLabel
        * (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2 = 0 :=
    Finset.sum_eq_zero fun pivotLabel hmember => by rw [hallOnPlane pivotLabel hmember]; ring
  have hpositive := sum_offPair_weight_mul_sq_firstTouchNormal_dotProduct_pos design hdistinct
    hheavy hboundary
  linarith

/-! ## Part 5 — the headline, and the refutation in general form -/

/-- **FIRST-TOUCH RIGIDITY.**  A pair on the live boundary whose first atom is heavy
has a GENUINE completion at which the tie leg is strictly NEGATIVE.

The brief asked for strictly POSITIVE and routed the argument through
non-parallelism of the pair.  Both are wrong: the sign is negative, and
non-parallelism is unnecessary. -/
theorem exists_offPair_neg_discriminantTie_of_pairGapExcessOf_eq_zero
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hdistinct : firstLabel ≠ secondLabel) (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    ∃ pivotLabel : Fin size, pivotLabel ≠ firstLabel ∧ pivotLabel ≠ secondLabel
      ∧ discriminantTie design pivotLabel firstLabel secondLabel < 0 := by
  obtain ⟨pivotLabel, hmember, hoffPlane⟩ :=
    exists_offPair_firstTouchNormal_dotProduct_ne_zero design hdistinct hheavy hboundary
  exact ⟨pivotLabel, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmember),
    Finset.ne_of_mem_erase hmember,
    (discriminantTie_neg_iff_firstTouchNormal_dotProduct_ne_zero design hheavy hboundary
      pivotLabel).mpr hoffPlane⟩

/-- **THE BRIEFED CONCLUSION, REFUTED IN GENERAL.**  Under exactly the briefed
hypotheses (heavy first atom, vanishing pair minor) NO completion whatsoever — off
pair, on pair, parallel or not — has a strictly positive tie leg. -/
theorem not_exists_pos_discriminantTie_of_pairGapExcessOf_eq_zero
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    ¬ ∃ pivotLabel : Fin size, 0 < discriminantTie design pivotLabel firstLabel secondLabel := by
  rintro ⟨pivotLabel, hpositive⟩
  exact absurd (discriminantTie_nonpos_of_pairGapExcessOf_eq_zero design hheavy hboundary
    pivotLabel) (not_le.mpr hpositive)

/-! ## Part 6 — what domination is allowed to do at a boundary pair -/

/-- A dominating triple has nonnegative tie leg: the tie leg IS the gap
determinant, and a positive semidefinite matrix has nonnegative determinant.  No
heaviness anywhere. -/
theorem nonneg_discriminantTie_of_dominates (design : WeightedDesign size 3)
    {pivotLabel firstLabel secondLabel : Fin size} (hpivotFirst : pivotLabel ≠ firstLabel)
    (hpivotSecond : pivotLabel ≠ secondLabel) (hpairDistinct : firstLabel ≠ secondLabel)
    (hdominates : Dominates design {pivotLabel, firstLabel, secondLabel}) :
    0 ≤ discriminantTie design pivotLabel firstLabel secondLabel := by
  rw [← det_subsetSum_sub_one_eq_discriminantTie design hpivotFirst hpivotSecond hpairDistinct]
  exact Matrix.PosSemidef.det_nonneg hdominates

/-- **THE QUANTITATIVE RIGIDITY CAP.**  In a dominating triple the third atom's
deviation from the first-touch plane of a heavy-anchored pair is bounded by the
product of the two pair minors through the anchor.  Domination pins the geometry,
and the bound degenerates to zero exactly on the boundary. -/
theorem sq_firstTouchNormal_dotProduct_le_of_dominates (design : WeightedDesign size 3)
    {pivotLabel firstLabel secondLabel : Fin size} (hpivotFirst : pivotLabel ≠ firstLabel)
    (hpivotSecond : pivotLabel ≠ secondLabel) (hpairDistinct : firstLabel ≠ secondLabel)
    (hheavy : 0 < heavyExcess design firstLabel)
    (hdominates : Dominates design {pivotLabel, firstLabel, secondLabel}) :
    (firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel) ^ 2
      ≤ pairGapExcessOf design firstLabel secondLabel
          * pairGapExcessOf design firstLabel pivotLabel := by
  have hmaster := heavyExcess_mul_discriminantTie_eq_pairGapExcessOf_mul_sub_sq design pivotLabel
    firstLabel secondLabel
  have hnonneg := nonneg_discriminantTie_of_dominates design hpivotFirst hpivotSecond
    hpairDistinct hdominates
  linarith [mul_nonneg hheavy.le hnonneg]

/-- **THE PINNING.**  A completion that dominates a boundary pair must lie in the
plane orthogonal to the first-touch normal. -/
theorem firstTouchNormal_dotProduct_eq_zero_of_dominates (design : WeightedDesign size 3)
    {pivotLabel firstLabel secondLabel : Fin size} (hpivotFirst : pivotLabel ≠ firstLabel)
    (hpivotSecond : pivotLabel ≠ secondLabel) (hpairDistinct : firstLabel ≠ secondLabel)
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0)
    (hdominates : Dominates design {pivotLabel, firstLabel, secondLabel}) :
    firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel = 0 := by
  have hcap := sq_firstTouchNormal_dotProduct_le_of_dominates design hpivotFirst hpivotSecond
    hpairDistinct hheavy hdominates
  rw [hboundary, zero_mul] at hcap
  exact sq_eq_zero_iff.mp (le_antisymm hcap (sq_nonneg _))

/-- The contrapositive: an atom off the first-touch plane cannot complete a
boundary pair to a dominating triple. -/
theorem not_dominates_of_firstTouchNormal_dotProduct_ne_zero (design : WeightedDesign size 3)
    {pivotLabel firstLabel secondLabel : Fin size} (hpivotFirst : pivotLabel ≠ firstLabel)
    (hpivotSecond : pivotLabel ≠ secondLabel) (hpairDistinct : firstLabel ≠ secondLabel)
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0)
    (hoffPlane : firstTouchNormal design firstLabel secondLabel ⬝ᵥ design.atom pivotLabel ≠ 0) :
    ¬ Dominates design {pivotLabel, firstLabel, secondLabel} := fun hdominates =>
  hoffPlane (firstTouchNormal_dotProduct_eq_zero_of_dominates design hpivotFirst hpivotSecond
    hpairDistinct hheavy hboundary hdominates)

/-- **THE BOUNDARY PAIR IS NEVER UNIVERSALLY COMPLETABLE.**  Some genuine completion
of a heavy-anchored boundary pair fails to dominate. -/
theorem exists_offPair_not_dominates_of_pairGapExcessOf_eq_zero (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    ∃ pivotLabel : Fin size, pivotLabel ≠ firstLabel ∧ pivotLabel ≠ secondLabel
      ∧ ¬ Dominates design {pivotLabel, firstLabel, secondLabel} := by
  obtain ⟨pivotLabel, hmember, hoffPlane⟩ :=
    exists_offPair_firstTouchNormal_dotProduct_ne_zero design hdistinct hheavy hboundary
  have hpivotFirst : pivotLabel ≠ firstLabel :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmember)
  have hpivotSecond : pivotLabel ≠ secondLabel := Finset.ne_of_mem_erase hmember
  exact ⟨pivotLabel, hpivotFirst, hpivotSecond,
    not_dominates_of_firstTouchNormal_dotProduct_ne_zero design hpivotFirst hpivotSecond
      hdistinct hheavy hboundary hoffPlane⟩

/-! ## Part 7 — the sign companion, wired to the landed tie row law -/

/-- The off-pair weighted average of the tie leg at a heavy-anchored boundary pair
is strictly NEGATIVE.  Every genuine completion contributes nonpositively and the
Parseval witness contributes strictly negatively. -/
theorem sum_offPair_weight_mul_discriminantTie_neg_of_pairGapExcessOf_eq_zero
    (design : WeightedDesign size 3) {firstLabel secondLabel : Fin size}
    (hdistinct : firstLabel ≠ secondLabel) (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    ∑ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
        design.weight pivotLabel
          * discriminantTie design firstLabel secondLabel pivotLabel < 0 := by
  obtain ⟨witnessLabel, hmember, hoffPlane⟩ :=
    exists_offPair_firstTouchNormal_dotProduct_ne_zero design hdistinct hheavy hboundary
  have hnonpos : ∀ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
      design.weight pivotLabel * discriminantTie design firstLabel secondLabel pivotLabel ≤ 0 := by
    intro pivotLabel _
    rw [discriminantTie_rotate design firstLabel secondLabel pivotLabel]
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos pivotLabel).le
      (discriminantTie_nonpos_of_pairGapExcessOf_eq_zero design hheavy hboundary pivotLabel)
  have hwitness : design.weight witnessLabel
      * discriminantTie design firstLabel secondLabel witnessLabel < 0 := by
    rw [discriminantTie_rotate design firstLabel secondLabel witnessLabel]
    exact mul_neg_of_pos_of_neg (design.weight_pos witnessLabel)
      ((discriminantTie_neg_iff_firstTouchNormal_dotProduct_ne_zero design hheavy hboundary
        witnessLabel).mpr hoffPlane)
  calc ∑ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
          design.weight pivotLabel * discriminantTie design firstLabel secondLabel pivotLabel
      < ∑ _pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel, (0 : ℝ) :=
        Finset.sum_lt_sum hnonpos ⟨witnessLabel, hmember, hwitness⟩
    _ = 0 := Finset.sum_const_zero

/-- **THE SIGN COMPANION, in the tree's surplus vocabulary.**  At every
heavy-anchored boundary pair the surplus form of
`Gtz.sum_offPair_weight_mul_discriminantTie` is strictly negative — with NO
`Gtz.AllHeavy` and no weight-concentration hypothesis, which is what distinguishes
this from the landed barriers of `Gtz/Quantitative/TieRowLaw.lean`.

Consequence: the landed positive criterion
`Gtz.exists_pos_discriminantTie_of_pos_surplusForm` can never fire at a boundary
pair, since its hypothesis is exactly this quantity being strictly positive. -/
theorem surplusForm_neg_of_pairGapExcessOf_eq_zero (design : WeightedDesign size 3)
    {firstLabel secondLabel : Fin size} (hdistinct : firstLabel ≠ secondLabel)
    (hheavy : 0 < heavyExcess design firstLabel)
    (hboundary : pairGapExcessOf design firstLabel secondLabel = 0) :
    heavyExcess design secondLabel * shareSurplus design firstLabel
        + heavyExcess design firstLabel * shareSurplus design secondLabel
        - 2 * atomPairing design firstLabel secondLabel ^ 2
            * (design.weight firstLabel + design.weight secondLabel) < 0 := by
  have hsum := sum_offPair_weight_mul_discriminantTie_neg_of_pairGapExcessOf_eq_zero design
    hdistinct hheavy hboundary
  rwa [sum_offPair_weight_mul_discriminantTie design hdistinct] at hsum

/-! ## Part 8 — an explicit rational witness, so the refutation is not vacuous

The four atoms `(1,0,0)`, `(5/4,3,0)`, `(5/4,-3,0)`, `(0,0,4)` with weights
`119/144`, `1/18`, `1/18`, `1/16` form a genuine weighted `(4,3)` design.  Its pair
`(3, 0)` has `heavyExcess = 15 > 0` at label `3`, orthogonal hence NON-PARALLEL
atoms, and `pairGapExcessOf = 0` — every briefed hypothesis, in full.  Both genuine
completions carry tie leg `-375/16`. -/

/-- The four atoms of the witness design. -/
noncomputable def boundaryAtom : Fin 4 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![5 / 4, 3, 0], ![5 / 4, -3, 0], ![0, 0, 4]]

/-- The four weights of the witness design. -/
noncomputable def boundaryWeight : Fin 4 → ℝ :=
  ![119 / 144, 1 / 18, 1 / 18, 1 / 16]

/-- **The witness**: a weighted `(4,3)` design carrying a heavy-anchored boundary
pair, with entirely rational data. -/
noncomputable def boundaryPairDesign : WeightedDesign 4 3 where
  atom := boundaryAtom
  weight := boundaryWeight
  weight_pos := by intro atomLabel; fin_cases atomLabel <;> simp [boundaryWeight]
  weight_sum_one := by
    simp [Fin.sum_univ_four, boundaryWeight]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_four, smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [boundaryAtom, boundaryWeight] <;> norm_num

theorem boundaryPairDesign_leverageOf_three : leverageOf (boundaryPairDesign.atom 3) = 16 := by
  simp [leverageOf, boundaryPairDesign, boundaryAtom, Fin.sum_univ_three]
  norm_num

theorem boundaryPairDesign_leverageOf_zero : leverageOf (boundaryPairDesign.atom 0) = 1 := by
  simp [leverageOf, boundaryPairDesign, boundaryAtom, Fin.sum_univ_three]

theorem boundaryPairDesign_leverageOf_one :
    leverageOf (boundaryPairDesign.atom 1) = 169 / 16 := by
  simp [leverageOf, boundaryPairDesign, boundaryAtom, Fin.sum_univ_three]
  norm_num

theorem boundaryPairDesign_heavyExcess_three : heavyExcess boundaryPairDesign 3 = 15 := by
  rw [heavyExcess, boundaryPairDesign_leverageOf_three]; norm_num

theorem boundaryPairDesign_heavyExcess_zero : heavyExcess boundaryPairDesign 0 = 0 := by
  rw [heavyExcess, boundaryPairDesign_leverageOf_zero]; norm_num

theorem boundaryPairDesign_heavyExcess_one : heavyExcess boundaryPairDesign 1 = 153 / 16 := by
  rw [heavyExcess, boundaryPairDesign_leverageOf_one]; norm_num

theorem boundaryPairDesign_atomPairing_three_zero : atomPairing boundaryPairDesign 3 0 = 0 := by
  simp [atomPairing, boundaryPairDesign, boundaryAtom, dotProduct, Fin.sum_univ_three]

theorem boundaryPairDesign_atomPairing_one_zero :
    atomPairing boundaryPairDesign 1 0 = 5 / 4 := by
  simp [atomPairing, boundaryPairDesign, boundaryAtom, dotProduct, Fin.sum_univ_three]

theorem boundaryPairDesign_atomPairing_one_three : atomPairing boundaryPairDesign 1 3 = 0 := by
  simp [atomPairing, boundaryPairDesign, boundaryAtom, dotProduct, Fin.sum_univ_three]

/-- The anchor of the witness pair is heavy. -/
theorem boundaryPairDesign_heavyExcess_three_pos : 0 < heavyExcess boundaryPairDesign 3 := by
  rw [boundaryPairDesign_heavyExcess_three]; norm_num

/-- **The witness pair sits exactly on the live boundary.** -/
theorem boundaryPairDesign_pairGapExcessOf_three_zero :
    pairGapExcessOf boundaryPairDesign 3 0 = 0 := by
  rw [pairGapExcessOf, gapExcessOf_eq_heavyExcess, gapExcessOf_eq_heavyExcess,
    gapPairingOf_eq_atomPairing, boundaryPairDesign_heavyExcess_zero,
    boundaryPairDesign_atomPairing_three_zero]
  ring

/-- The witness pair is NON-PARALLEL, in the orientation "second is a multiple of
first": the third coordinate separates them. -/
theorem boundaryPairDesign_atom_zero_ne_smul_three (ratio : ℝ) :
    boundaryPairDesign.atom 0 ≠ ratio • boundaryPairDesign.atom 3 := by
  intro hparallel
  have hcoord := congrFun hparallel 0
  simp [boundaryPairDesign, boundaryAtom] at hcoord

/-- The witness pair is NON-PARALLEL in the other orientation too. -/
theorem boundaryPairDesign_atom_three_ne_smul_zero (ratio : ℝ) :
    boundaryPairDesign.atom 3 ≠ ratio • boundaryPairDesign.atom 0 := by
  intro hparallel
  have hcoord := congrFun hparallel 2
  simp [boundaryPairDesign, boundaryAtom] at hcoord

/-- One tie leg computed from the raw atom coordinates, independently of every
identity in this file — the arithmetic cross-check on the refutation. -/
theorem boundaryPairDesign_discriminantTie_one_three_zero :
    discriminantTie boundaryPairDesign 1 3 0 = -(375 / 16) := by
  rw [discriminantTie, boundaryPairDesign_heavyExcess_one, boundaryPairDesign_heavyExcess_three,
    boundaryPairDesign_heavyExcess_zero, boundaryPairDesign_atomPairing_three_zero,
    boundaryPairDesign_atomPairing_one_three, boundaryPairDesign_atomPairing_one_zero]
  norm_num

/-- **THE REFUTATION, CONCRETELY.**  On a design meeting every briefed hypothesis in
full — heavy anchor, non-parallel atoms, zero pair gap excess — there is NO label
whose tie leg against the boundary pair is positive. -/
theorem boundaryPairDesign_not_exists_pos_discriminantTie :
    ¬ ∃ pivotLabel : Fin 4, 0 < discriminantTie boundaryPairDesign pivotLabel 3 0 :=
  not_exists_pos_discriminantTie_of_pairGapExcessOf_eq_zero boundaryPairDesign
    boundaryPairDesign_heavyExcess_three_pos boundaryPairDesign_pairGapExcessOf_three_zero

/-- The corrected headline fires on the witness. -/
theorem boundaryPairDesign_exists_offPair_neg_discriminantTie :
    ∃ pivotLabel : Fin 4, pivotLabel ≠ 3 ∧ pivotLabel ≠ 0
      ∧ discriminantTie boundaryPairDesign pivotLabel 3 0 < 0 :=
  exists_offPair_neg_discriminantTie_of_pairGapExcessOf_eq_zero boundaryPairDesign
    (by decide) boundaryPairDesign_heavyExcess_three_pos
    boundaryPairDesign_pairGapExcessOf_three_zero

/-- The domination consequence fires on the witness. -/
theorem boundaryPairDesign_exists_offPair_not_dominates :
    ∃ pivotLabel : Fin 4, pivotLabel ≠ 3 ∧ pivotLabel ≠ 0
      ∧ ¬ Dominates boundaryPairDesign {pivotLabel, 3, 0} :=
  exists_offPair_not_dominates_of_pairGapExcessOf_eq_zero boundaryPairDesign
    (by decide) boundaryPairDesign_heavyExcess_three_pos
    boundaryPairDesign_pairGapExcessOf_three_zero

/-- The sign companion fires on the witness. -/
theorem boundaryPairDesign_surplusForm_neg :
    heavyExcess boundaryPairDesign 0 * shareSurplus boundaryPairDesign 3
        + heavyExcess boundaryPairDesign 3 * shareSurplus boundaryPairDesign 0
        - 2 * atomPairing boundaryPairDesign 3 0 ^ 2
            * (boundaryPairDesign.weight 3 + boundaryPairDesign.weight 0) < 0 :=
  surplusForm_neg_of_pairGapExcessOf_eq_zero boundaryPairDesign (by decide)
    boundaryPairDesign_heavyExcess_three_pos boundaryPairDesign_pairGapExcessOf_three_zero

end Gtz

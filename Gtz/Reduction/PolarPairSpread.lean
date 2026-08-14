/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarIteratedDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The pair spread and the survivor Schur kill

The set deletion of `Gtz.PolarIteratedDeletion` prices a deleted set by the
TRACE of its weighted plane Gram.  The sharp price is the largest eigenvalue,
and for a PAIR that eigenvalue has a division-free certificate: a bound `S`
caps the pair form exactly when `S` caps the two weighted shadows and the
product of the two deficits covers the squared shadow pairing.  This file lands
that certificate and everything it opens.

## 1. The pair reading bound

`Gtz.pairReading_le`: two vectors, two positive weights, and a bound `S` with
the three polynomial conditions cap the weighted pair reading at every probe.
The proof is elementary: one Cauchy-Schwarz at a combined vector, and one
scalar core (`Gtz.pairReading_core`).  No eigenvalue, no square root, no
spectral theorem.  `Gtz.pairReading_lt` is the strict form.

## 2. The spread cover under trace admissibility alone

`Gtz.exists_polarSetDeletionCover_spreadTotal` removes the DEBT hypothesis
from the sharp set deletion cover: the composed lift needs only the running
total `Σ_T weight * planeShadowSq < 1`, and the margin needs only the spread.
At the uniform deciding cell the debt condition refuses every nonempty set,
but the trace admissibility accepts every pair.  Thus
`Gtz.not_isTie_of_polarSpreadTilt` fires strictly more frequently than the
banked set deletion kill, and `Gtz.not_isTie_of_pairSpreadCertificate` is its
division-free pair instance.

## 3. The residual, narrowed a fourth time

The forward reading `Gtz.exists_heavy_survivor_of_isTie_spread` is free at
every tie.  `Gtz.PolarSpreadSurvivorHeavy` bundles it,
`Gtz.polarSetDeletionHeavy_of_polarSpreadSurvivorHeavy` shows that it carries
the banked bundle, and `Gtz.PolarTiltSelectionSpread` is the residual with the
fourth bundle.  Every consumer of the shipped residual runs on it, the `(5,3)`
instance stays FALSE, and the diamond guardrail stays checked.

## 4. The survivor Schur kill at the deciding cell

At `(6,3)` the complement of a pole and a pair is a TRIPLE, and full Parseval
turns a pair spread bound into a plane cover by that triple.  When the triple
also carries pole mass above the pole's own leverage, and the coupling vector
stays below the Schur budget, the TRIPLE ITSELF dominates strictly
(`Gtz.posDef_of_polarSurplusSchur`).  The kill
`Gtz.not_isTie_of_survivorSchur_six_three` needs NO predecessor rank, NO
primitivity and NO overshooting pole.  Its contrapositive
`Gtz.tie_survivorSchur_six_three` is a new unconditional law of every tie of
the deciding cell: it reads the pole components of the survivors, which no
banked polar kill does.

The uniform pentagon datum blocks the deletion tools at every set size, but a
probe shows that the realized pentagon design always carries a strictly
dominating triple with margin `(10 - 3 * sqrt 5)/5`.  The pentagon is a
phantom: it is never a tie, and the survivor Schur kill is the certificate
shape that reaches it.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the pair reading bound

The scalar core is one signed AM-GM step, and the vector statement is one
Cauchy-Schwarz at the combined vector.  Both are division free. -/

section PairReading

variable {dim : ℕ}

/-- **THE SCALAR CORE OF THE PAIR BOUND.**  Two deficits that cover the squared
coupling cap the cross term by the two weighted squares. -/
theorem pairReading_core {wa wb A B C u v : ℝ} (hwa : 0 < wa) (hwb : 0 < wb)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hdet : wa * wb * C ^ 2 ≤ A * B) :
    2 * wa * wb * C * u * v ≤ wa * u ^ 2 * A + wb * v ^ 2 * B := by
  rcases eq_or_lt_of_le hA with hAzero | hApos
  · have hCzero : C = 0 := by
      have hprod : 0 < wa * wb := mul_pos hwa hwb
      have hCsq : wa * wb * C ^ 2 ≤ 0 := by rw [← hAzero, zero_mul] at hdet; exact hdet
      by_contra hCne
      exact absurd hCsq (not_le.mpr (mul_pos hprod (by positivity)))
    rw [hCzero]
    have hleft : 0 ≤ wa * u ^ 2 * A := mul_nonneg (by positivity) hA
    have hright : 0 ≤ wb * v ^ 2 * B := mul_nonneg (by positivity) hB
    linarith
  · nlinarith [mul_nonneg hwa.le (sq_nonneg (A * u - wb * C * v)),
      mul_nonneg (mul_nonneg hwb.le (sq_nonneg v)) (sub_nonneg.mpr hdet), hApos]

/-- **THE STRICT SCALAR CORE.**  With strict deficits and a strict determinant
condition, a nonzero reading makes the cap strict. -/
theorem pairReading_core_lt {wa wb A B C u v : ℝ} (hwa : 0 < wa) (hwb : 0 < wb)
    (hA : 0 < A) (_hB : 0 < B) (hdet : wa * wb * C ^ 2 < A * B)
    (hne : u ≠ 0 ∨ v ≠ 0) :
    2 * wa * wb * C * u * v < wa * u ^ 2 * A + wb * v ^ 2 * B := by
  rcases eq_or_ne v 0 with hv | hv
  · rcases hne with hu | hvne
    · rw [hv]
      have hpos : 0 < wa * u ^ 2 * A := by positivity
      nlinarith [hpos]
    · exact absurd hv hvne
  · nlinarith [mul_nonneg hwa.le (sq_nonneg (A * u - wb * C * v)),
      mul_pos (mul_pos hwb (by positivity : (0:ℝ) < v ^ 2)) (sub_pos.mpr hdet), hA]

/-- **THE PAIR READING BOUND.**  A bound `S` with the three division-free
conditions caps the weighted pair reading at EVERY probe.  This is the sharp
`2 × 2` spread fact of the polar lane, with no eigenvalue in the statement. -/
theorem pairReading_le (x y probe : Fin dim → ℝ) {wa wb S : ℝ}
    (hwa : 0 < wa) (hwb : 0 < wb)
    (hSa : wa * (x ⬝ᵥ x) ≤ S) (hSb : wb * (y ⬝ᵥ y) ≤ S)
    (hdet : wa * wb * (x ⬝ᵥ y) ^ 2 ≤ (S - wa * (x ⬝ᵥ x)) * (S - wb * (y ⬝ᵥ y))) :
    wa * (x ⬝ᵥ probe) ^ 2 + wb * (y ⬝ᵥ probe) ^ 2 ≤ S * (probe ⬝ᵥ probe) := by
  set u : ℝ := x ⬝ᵥ probe with hu
  set v : ℝ := y ⬝ᵥ probe with hv
  set combo : Fin dim → ℝ := (wa * u) • x + (wb * v) • y with hcombo
  have hcomboProbe : combo ⬝ᵥ probe = wa * u ^ 2 + wb * v ^ 2 := by
    rw [hcombo, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← hu, ← hv]
    ring
  have hcomboSelf : combo ⬝ᵥ combo
      = wa ^ 2 * u ^ 2 * (x ⬝ᵥ x) + 2 * wa * wb * u * v * (x ⬝ᵥ y)
        + wb ^ 2 * v ^ 2 * (y ⬝ᵥ y) := by
    rw [hcombo]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm y x]
    ring
  have hcore := pairReading_core (A := S - wa * (x ⬝ᵥ x)) (B := S - wb * (y ⬝ᵥ y))
    (C := x ⬝ᵥ y) (u := u) (v := v) hwa hwb (by linarith) (by linarith) hdet
  have hkey : combo ⬝ᵥ combo ≤ S * (wa * u ^ 2 + wb * v ^ 2) := by
    rw [hcomboSelf]
    nlinarith [hcore]
  have hcs : (combo ⬝ᵥ probe) ^ 2 ≤ (combo ⬝ᵥ combo) * (probe ⬝ᵥ probe) :=
    dotProduct_sq_le_mul_self combo probe
  have hPnonneg : 0 ≤ probe ⬝ᵥ probe := selfDotProduct_nonneg probe
  have hSnonneg : 0 ≤ S :=
    le_trans (mul_nonneg hwa.le (selfDotProduct_nonneg x)) hSa
  have hEnonneg : 0 ≤ wa * u ^ 2 + wb * v ^ 2 := by positivity
  rcases eq_or_lt_of_le hEnonneg with hEzero | hEpos
  · rw [← hEzero]
    exact mul_nonneg hSnonneg hPnonneg
  · have hchain : (wa * u ^ 2 + wb * v ^ 2) ^ 2
        ≤ S * (wa * u ^ 2 + wb * v ^ 2) * (probe ⬝ᵥ probe) := by
      calc (wa * u ^ 2 + wb * v ^ 2) ^ 2 = (combo ⬝ᵥ probe) ^ 2 := by rw [hcomboProbe]
        _ ≤ (combo ⬝ᵥ combo) * (probe ⬝ᵥ probe) := hcs
        _ ≤ S * (wa * u ^ 2 + wb * v ^ 2) * (probe ⬝ᵥ probe) :=
            mul_le_mul_of_nonneg_right hkey hPnonneg
    have hshuffle : (wa * u ^ 2 + wb * v ^ 2) * (wa * u ^ 2 + wb * v ^ 2)
        ≤ (S * (probe ⬝ᵥ probe)) * (wa * u ^ 2 + wb * v ^ 2) := by nlinarith [hchain]
    exact le_of_mul_le_mul_right hshuffle hEpos

/-- **THE STRICT PAIR READING BOUND.**  With strict conditions and a probe of
positive energy, the cap is strict.  A cover consumer reads it as a strict
domination. -/
theorem pairReading_lt (x y probe : Fin dim → ℝ) {wa wb S : ℝ}
    (hwa : 0 < wa) (hwb : 0 < wb)
    (hSa : wa * (x ⬝ᵥ x) < S) (hSb : wb * (y ⬝ᵥ y) < S)
    (hdet : wa * wb * (x ⬝ᵥ y) ^ 2 < (S - wa * (x ⬝ᵥ x)) * (S - wb * (y ⬝ᵥ y)))
    (hprobe : 0 < probe ⬝ᵥ probe) :
    wa * (x ⬝ᵥ probe) ^ 2 + wb * (y ⬝ᵥ probe) ^ 2 < S * (probe ⬝ᵥ probe) := by
  set gapA : ℝ := S - wa * (x ⬝ᵥ x) with hgapA
  set gapB : ℝ := S - wb * (y ⬝ᵥ y) with hgapB
  have hgapApos : 0 < gapA := by rw [hgapA]; linarith
  have hgapBpos : 0 < gapB := by rw [hgapB]; linarith
  set slack : ℝ := min (min (gapA / 2) (gapB / 2))
    ((gapA * gapB - wa * wb * (x ⬝ᵥ y) ^ 2) / (gapA + gapB)) with hslack
  have hdenPos : 0 < gapA + gapB := by linarith
  have hslackPos : 0 < slack := by
    rw [hslack]
    refine lt_min (lt_min (by linarith) (by linarith)) ?_
    rw [hgapA, hgapB] at *
    exact div_pos (by linarith [hdet]) hdenPos
  have hslackA : slack ≤ gapA / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hslackB : slack ≤ gapB / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hslackDet : slack * (gapA + gapB)
      ≤ gapA * gapB - wa * wb * (x ⬝ᵥ y) ^ 2 := by
    have hmin : slack ≤ (gapA * gapB - wa * wb * (x ⬝ᵥ y) ^ 2) / (gapA + gapB) := by
      rw [hslack]; exact min_le_right _ _
    calc slack * (gapA + gapB)
        ≤ ((gapA * gapB - wa * wb * (x ⬝ᵥ y) ^ 2) / (gapA + gapB)) * (gapA + gapB) :=
          mul_le_mul_of_nonneg_right hmin hdenPos.le
      _ = gapA * gapB - wa * wb * (x ⬝ᵥ y) ^ 2 := by field_simp
  have hstep := pairReading_le x y probe hwa hwb
    (S := S - slack) (by rw [hgapA] at hslackA; linarith) (by rw [hgapB] at hslackB; linarith)
    (by
      have hshape : (S - slack - wa * (x ⬝ᵥ x)) * (S - slack - wb * (y ⬝ᵥ y))
          = gapA * gapB - slack * (gapA + gapB) + slack ^ 2 := by
        rw [hgapA, hgapB]; ring
      rw [hshape]
      nlinarith [hslackDet, sq_nonneg slack])
  have hgain : (S - slack) * (probe ⬝ᵥ probe) < S * (probe ⬝ᵥ probe) := by
    nlinarith [hslackPos, hprobe]
  linarith

end PairReading

/-! ## Part 2: the shadow vector and the shadow pairing

The plane shadow of an atom is an explicit ambient vector.  Its length is the
banked `Gtz.planeShadowSq`, its pairing with a polar probe is the plain atom
reading, and the pairing of two shadows is a new division-free quantity. -/

section ShadowVector

variable {size rank : ℕ}

/-- **THE PLANE SHADOW VECTOR.**  The component of an atom orthogonal to the
pole, as an ambient vector. -/
noncomputable def planeShadowVec (design : WeightedDesign size rank)
    (pole label : Fin size) : Fin rank → ℝ :=
  design.atom label
    - ((design.atom label ⬝ᵥ design.atom pole) / (design.atom pole ⬝ᵥ design.atom pole))
      • design.atom pole

/-- A polar probe reads the shadow as the plain atom. -/
theorem planeShadowVec_dotProduct_polar (design : WeightedDesign size rank)
    (pole label : Fin size) {probe : Fin rank → ℝ}
    (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    planeShadowVec design pole label ⬝ᵥ probe = design.atom label ⬝ᵥ probe := by
  rw [planeShadowVec, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    dotProduct_comm (design.atom pole) probe, hprobe, mul_zero, sub_zero]

/-- The shadow's length is the plane shadow energy. -/
theorem planeShadowVec_dotProduct_self (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (label : Fin size) :
    planeShadowVec design pole label ⬝ᵥ planeShadowVec design pole label
      = planeShadowSq design pole label := by
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [planeShadowVec, planeShadowSq]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (design.atom pole) (design.atom label)]
  field_simp
  ring

/-- **THE SHADOW PAIRING.**  The overlap of two atoms after the pole component
is removed from each. -/
noncomputable def planeShadowPairing (design : WeightedDesign size rank)
    (pole first second : Fin size) : ℝ :=
  design.atom first ⬝ᵥ design.atom second
    - (design.atom first ⬝ᵥ design.atom pole) * (design.atom second ⬝ᵥ design.atom pole)
      / (design.atom pole ⬝ᵥ design.atom pole)

/-- The pairing of the two shadow vectors is the shadow pairing. -/
theorem planeShadowVec_dotProduct_pair (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (first second : Fin size) :
    planeShadowVec design pole first ⬝ᵥ planeShadowVec design pole second
      = planeShadowPairing design pole first second := by
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [planeShadowVec, planeShadowVec, planeShadowPairing]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  rw [dotProduct_comm (design.atom pole) (design.atom second)]
  ring

/-- The diagonal of the shadow pairing is the plane shadow energy. -/
theorem planeShadowPairing_self (design : WeightedDesign size rank)
    (pole label : Fin size) :
    planeShadowPairing design pole label label = planeShadowSq design pole label := by
  rw [planeShadowPairing, planeShadowSq]
  ring

/-- **THE PAIR SPREAD FROM THE CERTIFICATE.**  A bound `S` with the three
division-free shadow conditions caps the weighted pair reading at every polar
probe.  This supplies the sharp spread hypothesis of the set deletion at a
deleted PAIR. -/
theorem pair_polarSpread_of_certificate (design : WeightedDesign size rank)
    {pole first second : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second) {S : ℝ}
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second)) :
    ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      ∑ q ∈ ({first, second} : Finset (Fin size)),
          design.weight q * (design.atom q ⬝ᵥ probe) ^ 2
        ≤ S * (probe ⬝ᵥ probe) := by
  intro probe hprobe
  rw [Finset.sum_pair hne]
  have hstep := pairReading_le (S := S) (planeShadowVec design pole first)
    (planeShadowVec design pole second) probe (design.weight_pos first)
    (design.weight_pos second)
    (by rw [planeShadowVec_dotProduct_self design hpole first]; exact hSfirst)
    (by rw [planeShadowVec_dotProduct_self design hpole second]; exact hSsecond)
    (by rw [planeShadowVec_dotProduct_self design hpole first,
        planeShadowVec_dotProduct_self design hpole second,
        planeShadowVec_dotProduct_pair design hpole first second]
        exact hdet)
  rwa [planeShadowVec_dotProduct_polar design pole first hprobe,
    planeShadowVec_dotProduct_polar design pole second hprobe] at hstep

end ShadowVector

/-! ## Part 3: the spread cover under trace admissibility alone

The banked sharp cover consumes the DEBT condition, which the deciding cell
refuses at every nonempty set.  The composed lift never needed it: the running
total below one is the only admissibility the induction spends. -/

section SpreadTotal

variable {size rank : ℕ}

/-- **THE POLAR SET DELETION COVER AT A SPREAD BOUND, UNDER TRACE ADMISSIBILITY
ALONE.**  The debt hypothesis of the banked sharp cover is replaced by the
running total, which is strictly weaker.  The margin comes from the spread. -/
theorem exists_polarSetDeletionCover_spreadTotal (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (htotal : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1)
    {spread : ℝ}
    (hspread : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ probe) ^ 2
        ≤ spread * (probe ⬝ᵥ probe))
    {margin : ℝ} (hmarginPos : 0 < margin)
    (hmarginLt : margin < spreadDeletionMargin design pole deleted spread) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1
      ∧ pole ∉ covering ∧ (∀ q ∈ deleted, q ∉ covering)
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hcardPos : 1 ≤ deleted.card := Finset.card_pos.mpr hnonempty
  have hfree : 0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q :=
    setDeletion_free_mass_pos design hpole (by omega)
  have hmarginDen : (0 : ℝ) < 1 + margin := by linarith
  have hnumPos : (0 : ℝ) < 1 - spread := by
    rw [spreadDeletionMargin, lt_sub_iff_add_lt, lt_div_iff₀ hfree] at hmarginLt
    nlinarith [hmarginLt, hfree, hmarginPos]
  set cap : ℝ := (1 - spread) / (1 + margin) with hcapDef
  have hcapPos : 0 < cap := by rw [hcapDef]; exact div_pos hnumPos hmarginDen
  have hcapGt : 1 - design.weight pole - ∑ q ∈ deleted, design.weight q < cap := by
    rw [hcapDef, lt_div_iff₀ hmarginDen]
    rw [spreadDeletionMargin, lt_sub_iff_add_lt, lt_div_iff₀ hfree] at hmarginLt
    nlinarith [hmarginLt]
  obtain ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, hcover⟩ :=
    exists_polarSetDeletionCover hrank hpredecessor design hlong hnonempty hpole hroom htotal
      hcapPos hcapGt
  refine ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, fun probe hprobe => ?_⟩
  have hstep := hcover probe hprobe
  have hcauchy := hspread probe hprobe
  have hbase : (1 - spread) * (probe ⬝ᵥ probe)
      ≤ cap * ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
    nlinarith [hstep, hcauchy]
  have hmul := mul_le_mul_of_nonneg_right hbase hmarginDen.le
  have hcapMul : cap * (∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) * (1 + margin)
      = (1 - spread) * ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [hcapDef]; field_simp
  have hshape : (1 - spread) * (probe ⬝ᵥ probe) * (1 + margin)
      = (1 - spread) * ((1 + margin) * (probe ⬝ᵥ probe)) := by ring
  rw [hcapMul, hshape] at hmul
  exact le_of_mul_le_mul_left hmul hnumPos

/-- **THE SPREAD KILL UNDER TRACE ADMISSIBILITY.**  A tie carries no admissible
set with a spread below the pooled weight whose survivors all stay below the
spread tilt budget. -/
theorem not_isTie_of_polarSpreadTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (htotal : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1)
    {spread : ℝ}
    (hspread : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ probe) ^ 2
        ≤ spread * (probe ⬝ᵥ probe))
    (hbeat : spread < design.weight pole + ∑ q ∈ deleted, design.weight q)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < spreadDeletionMargin design pole deleted spread
          * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design := by
  classical
  intro htie
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hgapPos : (0 : ℝ) < (design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1) := by nlinarith [hlong, hleveragePos]
  have hcardPos : 1 ≤ deleted.card := Finset.card_pos.mpr hnonempty
  have hfree : 0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q :=
    setDeletion_free_mass_pos design hpole (by omega)
  have hsharpPos : 0 < spreadDeletionMargin design pole deleted spread :=
    spreadDeletionMargin_pos design hfree hbeat
  have hshape : spreadDeletionMargin design pole deleted spread
        * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      = spreadDeletionMargin design pole deleted spread
        * ((design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) := by ring
  rw [hshape] at hbudget
  obtain ⟨margin, hmarginPos, hmarginLt, hmarginBudget⟩ :=
    exists_margin_below_sharp hsharpPos hgapPos hbudget
  obtain ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, hcover⟩ :=
    exists_polarSetDeletionCover_spreadTotal hrank hpredecessor design hlong hnonempty hpole
      hroom htotal hspread hmarginPos hmarginLt
  have htiltSum : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
      ≤ ((rank : ℝ) - 1) * tiltCap := by
    have hbound : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
        ≤ ∑ _label ∈ covering, tiltCap := by
      refine Finset.sum_le_sum fun label hlabel => ?_
      exact htilt label (fun heq => hpoleNotMem (heq ▸ hlabel))
        (fun hmem => hdeletedNotMem label hmem hlabel)
    have hcardCast : ((covering.card : ℕ) : ℝ) = (rank : ℝ) - 1 := by
      rw [hcard]
      have hone : (1 : ℕ) ≤ rank := by omega
      push_cast [Nat.cast_sub hone]
      ring
    calc ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
        ≤ ∑ _label ∈ covering, tiltCap := hbound
      _ = (covering.card : ℝ) * tiltCap := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((rank : ℝ) - 1) * tiltCap := by rw [hcardCast]
  have htiltStrict : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
      < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    have hstep : margin * ((design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1))
        = margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by ring
    rw [← hstep]
    linarith [hmarginBudget]
  have hposDef := posDef_insert_of_polarCover design hpoleNotMem hlong hmarginPos hcover
    htiltStrict
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hpoleNotMem, hcard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- **THE FORWARD READING OF THE SPREAD KILL.**  Every tie leaves, at every
admissible set and every spread below the pooled weight, a survivor whose
squared pairing already spends the spread budget. -/
theorem exists_heavy_survivor_of_isTie_spread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (htotal : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1)
    {spread : ℝ}
    (hspread : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ probe) ^ 2
        ≤ spread * (probe ⬝ᵥ probe))
    (hbeat : spread < design.weight pole + ∑ q ∈ deleted, design.weight q) :
    ∃ label : Fin size, label ≠ pole ∧ label ∉ deleted
      ∧ spreadDeletionMargin design pole deleted spread
            * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  classical
  by_contra hcontra
  have hstrict : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2
        < spreadDeletionMargin design pole deleted spread
            * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    intro label hlabelPole hlabelNot
    by_contra hbig
    exact hcontra ⟨label, hlabelPole, hlabelNot, not_lt.mp hbig⟩
  have hcardPos : 1 ≤ deleted.card := Finset.card_pos.mpr hnonempty
  have hadmissible : ((Finset.univ : Finset (Fin size)) \ insert pole deleted).Nonempty := by
    rw [← Finset.card_pos, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
      Finset.card_insert_of_notMem hpole]
    omega
  obtain ⟨top, htopMem, htopMax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Fin size)) \ insert pole deleted)
    (fun label => (design.atom label ⬝ᵥ design.atom pole) ^ 2) hadmissible
  have htopOut : top ∉ insert pole deleted := (Finset.mem_sdiff.mp htopMem).2
  have htopPole : top ≠ pole := fun heq => htopOut (by rw [heq]; exact Finset.mem_insert_self _ _)
  have htopDeleted : top ∉ deleted := fun hmem => htopOut (Finset.mem_insert_of_mem hmem)
  refine not_isTie_of_polarSpreadTilt hrank hpredecessor design hlong hnonempty hpole hroom
    htotal hspread hbeat (tiltCap := (design.atom top ⬝ᵥ design.atom pole) ^ 2)
    (fun label hlabelPole hlabelNot => ?_) (hstrict top htopPole htopDeleted) htie
  exact htopMax label (Finset.mem_sdiff.mpr ⟨Finset.mem_univ label, fun hmem => by
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hlabelPole heq
    · exact hlabelNot hmem'⟩)

/-- **THE PAIR SPREAD KILL, DIVISION FREE.**  A tie carries no pair with the
sharp certificate, trace admissibility, and survivors below the spread budget.
At the uniform deciding cell the certificate reads: the two shadow directions
are close to orthogonal. -/
theorem not_isTie_of_pairSpreadCertificate (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole first second : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hne : first ≠ second) (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    (hroom : rank + 2 ≤ size)
    (htotal : design.weight first * planeShadowSq design pole first
        + design.weight second * planeShadowSq design pole second < 1)
    {S : ℝ}
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hbeat : S < design.weight pole + (design.weight first + design.weight second))
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ≠ first → label ≠ second →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < spreadDeletionMargin design pole ({first, second} : Finset (Fin size)) S
          * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design := by
  classical
  have hpoleNot : pole ∉ ({first, second} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hfirstPole heq.symm
    · exact hsecondPole (Finset.mem_singleton.mp hmem').symm
  have hcard : ({first, second} : Finset (Fin size)).card = 2 := Finset.card_pair hne
  refine not_isTie_of_polarSpreadTilt hrank hpredecessor design hlong
    ⟨first, Finset.mem_insert_self _ _⟩ hpoleNot (by rw [hcard]; exact hroom)
    (by rw [Finset.sum_pair hne]; exact htotal)
    (pair_polarSpread_of_certificate design (by linarith) hne hSfirst hSsecond hdet)
    (by rw [Finset.sum_pair hne]; exact hbeat)
    (fun label hlabelPole hlabelNot => htilt label hlabelPole
      (fun heq => hlabelNot (heq ▸ Finset.mem_insert_self _ _))
      (fun heq => hlabelNot (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
    hbudget

end SpreadTotal

/-! ## Part 4: the free spread fact, and the residual narrowed a fourth time

The forward reading of the spread kill is free at every tie, and it carries the
banked set deletion fact.  The residual with the fourth bundle is weaker than
every shipped residual, and every consumer runs on it. -/

section SpreadResidual

variable {size rank : ℕ}

/-- **THE FREE SPREAD FACT.**  What a tie supplies at an overshooting pole: at
every admissible set and every spread below the pooled weight, some survivor is
already heavy against the spread budget. -/
def PolarSpreadSurvivorHeavy (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  ∀ deleted : Finset (Fin size), deleted.Nonempty → pole ∉ deleted →
    rank + deleted.card ≤ size →
    (∑ q ∈ deleted, design.weight q * planeShadowSq design pole q) < 1 →
    ∀ spread : ℝ,
      (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
        ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ probe) ^ 2
          ≤ spread * (probe ⬝ᵥ probe)) →
      spread < design.weight pole + ∑ q ∈ deleted, design.weight q →
      ∃ label : Fin size, label ≠ pole ∧ label ∉ deleted
        ∧ spreadDeletionMargin design pole deleted spread
              * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)
            ≤ ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2

/-- **THE SPREAD FACT IS FREE AT EVERY TIE.** -/
theorem polarSpreadSurvivorHeavy_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    PolarSpreadSurvivorHeavy design pole :=
  fun _deleted hnonempty hpole hroom htotal _spread hspread hbeat =>
    exists_heavy_survivor_of_isTie_spread hrank hpredecessor design htie hlong hnonempty hpole
      hroom htotal hspread hbeat

/-- **THE SPREAD FACT CARRIES THE SET DELETION FACT.**  At the trace spread the
margin is the banked set deletion margin, and the debt condition supplies both
the admissibility and the beat.  Thus the fourth bundle strictly extends the
third. -/
theorem polarSetDeletionHeavy_of_polarSpreadSurvivorHeavy
    (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    (hheavy : PolarSpreadSurvivorHeavy design pole) :
    PolarSetDeletionHeavy design pole := by
  intro deleted hnonempty hpoleNot hroom hdeletable
  have htotal : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1 :=
    setDeletion_total_lt_one design hpoleNot hdeletable
  have hbeat : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q
      < design.weight pole + ∑ q ∈ deleted, design.weight q := by
    have hdebt := hdeletable
    rw [planeShadowDebt_eq] at hdebt
    linarith
  have hstep := hheavy deleted hnonempty hpoleNot hroom htotal
    (∑ q ∈ deleted, design.weight q * planeShadowSq design pole q)
    (fun _probe hprobe => sum_weight_polarPairing_sq_le design hpole deleted hprobe) hbeat
  obtain ⟨label, hlabelPole, hlabelNot, hlabelHeavy⟩ := hstep
  refine ⟨label, hlabelPole, hlabelNot, ?_⟩
  rw [setDeletionMargin_eq_spread]
  exact hlabelHeavy

/-- **THE FOUR-BUNDLE TILT RESIDUAL.**  `Gtz.PolarTiltSelectionSetDeletion`
with the free spread fact handed to it as well.  It is weaker than every
shipped residual, and every consumer of them runs on this one. -/
def PolarTiltSelectionSpread (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    PolarDeletionHeavy design pole →
    PolarSetDeletionHeavy design pole →
    PolarSpreadSurvivorHeavy design pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The four-bundle residual is weaker than the thrice-narrowed one. -/
theorem polarTiltSelectionSpread_of_polarTiltSelectionSetDeletion
    (htilt : PolarTiltSelectionSetDeletion size rank) :
    PolarTiltSelectionSpread size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget hheavy hset _hspread hmargin
    hcard hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hheavy hset hmargin hcard
      hnotMem hcover

/-- The four-bundle residual is weaker than the twice-narrowed one. -/
theorem polarTiltSelectionSpread_of_polarTiltSelectionDeletion
    (htilt : PolarTiltSelectionDeletion size rank) :
    PolarTiltSelectionSpread size rank :=
  polarTiltSelectionSpread_of_polarTiltSelectionSetDeletion
    (polarTiltSelectionSetDeletion_of_polarTiltSelectionDeletion htilt)

/-- The four-bundle residual is weaker than the shipped one. -/
theorem polarTiltSelectionSpread_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionSpread size rank :=
  polarTiltSelectionSpread_of_polarTiltSelectionSetDeletion
    (polarTiltSelectionSetDeletion_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE FOUR-BUNDLE RESIDUAL.**  All four bundles are theorems
at a tie, thus the fourth narrowing costs nothing downstream either. -/
theorem hingeHoldsAtSize_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong
      (polarSaturationBudget_of_isTie hrank hpredecessor design htie hlong)
      (polarDeletionHeavy_of_isTie hrank hpredecessor design htie hlong hroom)
      (polarSetDeletionHeavy_of_isTie hrank hpredecessor design htie hlong)
      (polarSpreadSurvivorHeavy_of_isTie hrank hpredecessor design htie hlong)
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover
    hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the four-bundle one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltSpread (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd
    (hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE FOUR-BUNDLE RESIDUAL.** -/
theorem polarTiltSpread_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSpread size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltSpread hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltSpread hrank hpredecessor hroom htilt⟩

/-! ### The registry obligations, on the four-bundle residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltSpread
    (htilt : ∀ rank : ℕ, 4 ≤ rank →
      PolarTiltSelectionSpread (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltSpread (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltSpread
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionSpread size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltSpread (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one four-bundle residual per cell. -/
theorem sharpWindowHinge_of_polarTiltSpread
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionSpread size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltSpread (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltSpread (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionSpread (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltSpread (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionSpread (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltSpread (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionSpread (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltSpread hrank hpredecessor hroom htilt

end SpreadResidual

/-! ## Part 5: the survivor Schur kill

Full Parseval turns a pair spread bound into a plane cover by the surviving
labels.  When the survivors also carry pole mass above the pole's leverage and
a small coupling vector, the survivors dominate strictly BY THEMSELVES.  No
predecessor rank, no primitivity, no overshooting hypothesis is spent. -/

section SurvivorSchur

variable {size rank : ℕ}

/-- **THE COUPLING VECTOR OF A SET.**  The pairing-weighted sum of the shadow
vectors.  Its length prices the off-diagonal block of the set's Schur test. -/
noncomputable def polarCouplingVec (design : WeightedDesign size rank) (pole : Fin size)
    (selected : Finset (Fin size)) : Fin rank → ℝ :=
  ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) • planeShadowVec design pole c

/-- The coupling vector reads a polar probe through the plain atoms. -/
theorem polarCouplingVec_dotProduct (design : WeightedDesign size rank)
    (pole : Fin size) (selected : Finset (Fin size)) {probe : Fin rank → ℝ}
    (hprobe : probe ⬝ᵥ design.atom pole = 0) :
    polarCouplingVec design pole selected ⬝ᵥ probe
      = ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) * (design.atom c ⬝ᵥ probe) := by
  rw [polarCouplingVec, sum_dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_dotProduct, smul_eq_mul, planeShadowVec_dotProduct_polar design pole c hprobe]

/-- **THE SCHUR DOMINATION OF A SET WITH POLE SURPLUS.**  A set that covers the
pole's orthogonal hyperplane with a positive excess, carries squared pairings
above the pole's own leverage, and keeps its coupling vector below the Schur
budget, dominates strictly.  The pole is only a direction here: nothing about
its weight or its leverage cap is used. -/
theorem posDef_of_polarSurplusSchur (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {selected : Finset (Fin size)} {excess : ℝ}
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + excess) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (hschur : polarCouplingVec design pole selected ⬝ᵥ polarCouplingVec design pole selected
        < excess * ((∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    (subsetSum design selected - 1).PosDef := by
  classical
  have hpoleNe : design.atom pole ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hpole
    exact lt_irrefl 0 hpole
  set leverage : ℝ := design.atom pole ⬝ᵥ design.atom pole with hleverage
  set root : ℝ := Real.sqrt leverage with hroot
  have hrootPos : 0 < root := Real.sqrt_pos.mpr hpole
  have hrootSq : root ^ 2 = leverage := Real.sq_sqrt hpole.le
  set unitNormal : Fin rank → ℝ := root⁻¹ • design.atom pole with hunitNormal
  have hunit : unitNormal ⬝ᵥ unitNormal = 1 := unit_of_ne_zero (design.atom pole) hpoleNe
  have hreadNormal : ∀ c : Fin size, design.atom c ⬝ᵥ unitNormal
      = root⁻¹ * (design.atom c ⬝ᵥ design.atom pole) := by
    intro c
    rw [hunitNormal, dotProduct_smul, smul_eq_mul]
  have hLne : leverage ≠ 0 := ne_of_gt hpole
  have hsumShape : ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2
      = (∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2) / leverage := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hreadNormal c, mul_pow, inv_pow, hrootSq, ← div_eq_inv_mul]
  have hsurplus : 1 < ∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2 := by
    rw [hsumShape, lt_div_iff₀ hpole, one_mul]
    exact hz
  refine posDef_of_normalSurplus_hyperplaneCover design selected unitNormal hunit hsurplus ?_
  intro probe hprobeNormal hprobeNe
  have hprobePole : probe ⬝ᵥ design.atom pole = 0 := by
    rw [hunitNormal, dotProduct_smul, smul_eq_mul] at hprobeNormal
    rcases mul_eq_zero.mp hprobeNormal with hbad | hgood
    · exact absurd hbad (inv_ne_zero (ne_of_gt hrootPos))
    · exact hgood
  have hprobePos : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hprobeNe
  set couple : Fin rank → ℝ := polarCouplingVec design pole selected with hcouple
  have hcoupleRead : ∑ c ∈ selected,
      (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)
      = root⁻¹ * (couple ⬝ᵥ probe) := by
    rw [hcouple, polarCouplingVec_dotProduct design pole selected hprobePole, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hreadNormal c]
    ring
  set pairMass : ℝ := ∑ c ∈ selected, (design.atom c ⬝ᵥ design.atom pole) ^ 2 with hpairMass
  have hgapPos : 0 < pairMass - leverage := by rw [hpairMass, hleverage]; linarith
  have hcs : (couple ⬝ᵥ probe) ^ 2 ≤ (couple ⬝ᵥ couple) * (probe ⬝ᵥ probe) :=
    dotProduct_sq_le_mul_self couple probe
  have hcov := hcover probe hprobePole
  have hfinal : (couple ⬝ᵥ probe) ^ 2
      < (pairMass - leverage)
        * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
    have hstepOne := mul_lt_mul_of_pos_right hschur hprobePos
    have hstepTwo : (pairMass - leverage) * (excess * (probe ⬝ᵥ probe))
        ≤ (pairMass - leverage)
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
      refine mul_le_mul_of_nonneg_left ?_ hgapPos.le
      linarith [hcov]
    nlinarith [hcs, hstepOne, hstepTwo]
  have hLinvPos : (0 : ℝ) < leverage⁻¹ := inv_pos.mpr hpole
  calc (∑ c ∈ selected, (design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ unitNormal)) ^ 2
      = leverage⁻¹ * (couple ⬝ᵥ probe) ^ 2 := by
        rw [hcoupleRead, mul_pow, inv_pow, hrootSq]
    _ < leverage⁻¹ * ((pairMass - leverage)
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) :=
        mul_lt_mul_of_pos_left hfinal hLinvPos
    _ = ((∑ c ∈ selected, (design.atom c ⬝ᵥ unitNormal) ^ 2) - 1)
          * ((∑ c ∈ selected, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
        rw [hsumShape]
        field_simp

/-- **THE COMPLEMENT COVER FROM A PAIR CERTIFICATE.**  Full Parseval reads a
polar probe through every label, the pole reads zero, and the pair certificate
caps the pair.  What is left is a plane cover by the complement, with an excess
priced by one weight cap. -/
theorem complementPair_polarCover (design : WeightedDesign size rank)
    {pole first second : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second)
    (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    {S wcap excess : ℝ} (hwcapPos : 0 < wcap)
    (hwcap : ∀ c : Fin size, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap)
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hexcess : wcap * (1 + excess) ≤ 1 - S) :
    ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + excess) * (probe ⬝ᵥ probe)
        ≤ ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ probe) ^ 2 := by
  classical
  intro probe hprobe
  have hparseval : probe ⬝ᵥ probe
      = ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [dotProduct_eq_sum_weight_mul_pair design probe probe]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hpoleTerm : design.weight pole * (design.atom pole ⬝ᵥ probe) ^ 2 = 0 := by
    rw [dotProduct_comm, hprobe]
    ring
  have hmemFirst : first ∈ Finset.univ.erase pole :=
    Finset.mem_erase.mpr ⟨hfirstPole, Finset.mem_univ first⟩
  have hmemSecond : second ∈ (Finset.univ.erase pole).erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_erase.mpr ⟨hsecondPole, Finset.mem_univ second⟩⟩
  have hsplitPole : ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = design.weight pole * (design.atom pole ⬝ᵥ probe) ^ 2
        + ∑ c ∈ Finset.univ.erase pole, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ pole)).symm
  have hsplitFirst : ∑ c ∈ Finset.univ.erase pole,
        design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = design.weight first * (design.atom first ⬝ᵥ probe) ^ 2
        + ∑ c ∈ (Finset.univ.erase pole).erase first,
            design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 :=
    (Finset.add_sum_erase _ _ hmemFirst).symm
  have hsplitSecond : ∑ c ∈ (Finset.univ.erase pole).erase first,
        design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = design.weight second * (design.atom second ⬝ᵥ probe) ^ 2
        + ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 :=
    (Finset.add_sum_erase _ _ hmemSecond).symm
  have hpair := pair_polarSpread_of_certificate design hpole hne hSfirst hSsecond hdet
    probe hprobe
  rw [Finset.sum_pair hne] at hpair
  have htail : (1 - S) * (probe ⬝ᵥ probe)
      ≤ ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    nlinarith [hparseval, hsplitPole, hsplitFirst, hsplitSecond, hpoleTerm, hpair]
  have hunweight : ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
        design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ wcap * ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hcSecond : c ≠ second := Finset.ne_of_mem_erase hc
    have hcRest := Finset.mem_of_mem_erase hc
    have hcFirst : c ≠ first := Finset.ne_of_mem_erase hcRest
    have hcPole : c ≠ pole := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcRest)
    exact mul_le_mul_of_nonneg_right (hwcap c hcPole hcFirst hcSecond) (sq_nonneg _)
  have hPnonneg : 0 ≤ probe ⬝ᵥ probe := selfDotProduct_nonneg probe
  have hchain : wcap * ((1 + excess) * (probe ⬝ᵥ probe))
      ≤ wcap * ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
          (design.atom c ⬝ᵥ probe) ^ 2 := by
    calc wcap * ((1 + excess) * (probe ⬝ᵥ probe))
        = (wcap * (1 + excess)) * (probe ⬝ᵥ probe) := by ring
      _ ≤ (1 - S) * (probe ⬝ᵥ probe) := mul_le_mul_of_nonneg_right hexcess hPnonneg
      _ ≤ ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := htail
      _ ≤ wcap * ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ probe) ^ 2 := hunweight
  exact le_of_mul_le_mul_left hchain hwcapPos

end SurvivorSchur

/-! ## Part 6: the deciding cell

At `(6,3)` the complement of a pole and a pair is a NAMED triple of card three.
The Schur domination of that triple is a kill with no predecessor rank, and its
contrapositive is a new unconditional law of every tie. -/

section SixThree

/-- **THE SURVIVOR SCHUR KILL AT THE DECIDING CELL.**  A `(6,3)` tie carries no
pole and pair with the sharp pair certificate at a complement whose pole mass
beats the leverage and whose coupling vector stays below the Schur budget.  NO
predecessor rank, NO primitivity, and NO overshooting pole are consumed. -/
theorem not_isTie_of_survivorSchur_six_three (design : WeightedDesign 6 3)
    {pole first second : Fin 6}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second)
    (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    {S wcap excess : ℝ} (hwcapPos : 0 < wcap)
    (hwcap : ∀ c : Fin 6, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap)
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hexcess : wcap * (1 + excess) ≤ 1 - S)
    (hz : design.atom pole ⬝ᵥ design.atom pole
        < ∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ design.atom pole) ^ 2)
    (hschur : polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
          ⬝ᵥ polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
        < excess * ((∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
              (design.atom c ⬝ᵥ design.atom pole) ^ 2)
            - design.atom pole ⬝ᵥ design.atom pole)) :
    ¬ IsTie design := by
  classical
  intro htie
  have hcover := complementPair_polarCover design hpole hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess
  have hposDef := posDef_of_polarSurplusSchur design hpole hcover hz hschur
  have hmemFirst : first ∈ Finset.univ.erase pole :=
    Finset.mem_erase.mpr ⟨hfirstPole, Finset.mem_univ first⟩
  have hmemSecond : second ∈ (Finset.univ.erase pole).erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_erase.mpr ⟨hsecondPole, Finset.mem_univ second⟩⟩
  have hcard : (((Finset.univ.erase pole).erase first).erase second).card = 3 := by
    rw [Finset.card_erase_of_mem hmemSecond, Finset.card_erase_of_mem hmemFirst,
      Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ, Fintype.card_fin]
  exact htie.2 _ hcard hposDef

/-- **THE SURVIVOR SCHUR LAW OF EVERY TIE OF THE DECIDING CELL.**  At every
`(6,3)` tie, every pole, every pair with the sharp certificate, and every
priced excess: the complement triple keeps its pole mass at or below the
leverage, or its coupling vector spends the whole Schur budget.  This is the
first polar law that reads the pole components of the SURVIVORS. -/
theorem tie_survivorSchur_six_three (design : WeightedDesign 6 3) (htie : IsTie design)
    {pole first second : Fin 6}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) (hne : first ≠ second)
    (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    {S wcap excess : ℝ} (hwcapPos : 0 < wcap)
    (hwcap : ∀ c : Fin 6, c ≠ pole → c ≠ first → c ≠ second → design.weight c ≤ wcap)
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hexcess : wcap * (1 + excess) ≤ 1 - S) :
    (∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
        (design.atom c ⬝ᵥ design.atom pole) ^ 2)
      ≤ design.atom pole ⬝ᵥ design.atom pole
    ∨ excess * ((∑ c ∈ ((Finset.univ.erase pole).erase first).erase second,
            (design.atom c ⬝ᵥ design.atom pole) ^ 2)
          - design.atom pole ⬝ᵥ design.atom pole)
        ≤ polarCouplingVec design pole (((Finset.univ.erase pole).erase first).erase second)
          ⬝ᵥ polarCouplingVec design pole
            (((Finset.univ.erase pole).erase first).erase second) := by
  by_contra hcontra
  rw [not_or, not_le, not_le] at hcontra
  exact not_isTie_of_survivorSchur_six_three design hpole hne hfirstPole hsecondPole hwcapPos
    hwcap hSfirst hSsecond hdet hexcess hcontra.1 hcontra.2 htie

/-- The pair spread kill at rank three, with the previous rank discharged. -/
theorem not_isTie_of_pairSpreadCertificate_three {size : ℕ} (design : WeightedDesign size 3)
    {pole first second : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hne : first ≠ second) (hfirstPole : first ≠ pole) (hsecondPole : second ≠ pole)
    (hroom : 5 ≤ size)
    (htotal : design.weight first * planeShadowSq design pole first
        + design.weight second * planeShadowSq design pole second < 1)
    {S : ℝ}
    (hSfirst : design.weight first * planeShadowSq design pole first ≤ S)
    (hSsecond : design.weight second * planeShadowSq design pole second ≤ S)
    (hdet : design.weight first * design.weight second
          * planeShadowPairing design pole first second ^ 2
        ≤ (S - design.weight first * planeShadowSq design pole first)
          * (S - design.weight second * planeShadowSq design pole second))
    (hbeat : S < design.weight pole + (design.weight first + design.weight second))
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ≠ first → label ≠ second →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : 2 * tiltCap
      < spreadDeletionMargin design pole ({first, second} : Finset (Fin size)) S
          * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design :=
  not_isTie_of_pairSpreadCertificate (by norm_num) gtz_rank_two design hlong hne hfirstPole
    hsecondPole (by omega) htotal hSfirst hSsecond hdet hbeat htilt (by push_cast; linarith)

/-- **THE DECIDING CELL OF RANK THREE FROM THE FOUR-BUNDLE RESIDUAL ALONE.** -/
theorem hingeHoldsAtSize_six_three_of_polarTiltSpread
    (htilt : PolarTiltSelectionSpread 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltSpread (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the four-bundle residual. -/
theorem thresholdArms_rank_three_of_polarTiltSpread
    (htilt : PolarTiltSelectionSpread 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltSpread htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL, FROM THE FOUR-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltSpread
    (htilt : PolarTiltSelectionSpread 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltSpread htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE, FROM THE FOUR-BUNDLE RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltSpread
    (htilt : PolarTiltSelectionSpread 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltSpread htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE FOUR-BUNDLE RESIDUAL IS FALSE AT `(5,3)`.**  The calibration
transports through the fourth narrowing too, because the spread fact is free at
every tie of five labels of rank three. -/
theorem not_polarTiltSelectionSpread_five_three :
    ¬ PolarTiltSelectionSpread 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltSpread (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it
does not touch the four-bundle residual, and the last-stage Prop stays
refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltSpread :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionSpread 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionSpread_five_three⟩

end SixThree

/-! ## Part 7: the cross moment

Parseval contracted once rebuilds any vector from its weighted readings.  Read
along the pole it makes the pairing-weighted shadow vectors of ALL labels add
to zero: the plane first moment of the pole readings vanishes.  This is the
constraint that couples the shadow directions to the weights, and it pins the
coupling of a survivor set to the data of its complement. -/

section CrossMoment

variable {size rank : ℕ}

/-- **THE FRAME RECONSTRUCTION.**  The weighted read-and-rebuild of any vector
is the vector itself.  Parseval contracted once, as a vector identity. -/
theorem sum_weight_read_smul_atom (design : WeightedDesign size rank)
    (vec : Fin rank → ℝ) :
    ∑ c, (design.weight c * (design.atom c ⬝ᵥ vec)) • design.atom c = vec := by
  funext coord
  have hread := dotProduct_eq_sum_weight_mul_pair design (Pi.single coord 1) vec
  rw [single_dotProduct, one_mul] at hread
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hread]
  exact Finset.sum_congr rfl fun c _ => by rw [dotProduct_single, mul_one]; ring

/-- The pole casts no shadow on its own plane. -/
theorem planeShadowVec_self_pole (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    planeShadowVec design pole pole = 0 := by
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  rw [planeShadowVec, div_self hne, one_smul, sub_self]

/-- **THE CROSS MOMENT VANISHES.**  The pairing-weighted shadow vectors of all
labels add to the zero vector.  This is the off-diagonal block of Parseval
read along the pole. -/
theorem sum_weight_pairing_smul_planeShadowVec (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    ∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
        • planeShadowVec design pole c = 0 := by
  have hne : design.atom pole ⬝ᵥ design.atom pole ≠ 0 := ne_of_gt hpole
  have hrecon := sum_weight_read_smul_atom design (design.atom pole)
  have hmass := sum_weight_polarPairing_sq design pole
  calc ∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
        • planeShadowVec design pole c
      = (∑ c, (design.weight c * (design.atom c ⬝ᵥ design.atom pole)) • design.atom c)
        - (∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
            * (design.atom c ⬝ᵥ design.atom pole / (design.atom pole ⬝ᵥ design.atom pole)))
          • design.atom pole := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by
          rw [planeShadowVec, smul_sub, smul_smul]
    _ = 0 := by
        rw [hrecon]
        have hsum : ∑ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
            * (design.atom c ⬝ᵥ design.atom pole / (design.atom pole ⬝ᵥ design.atom pole))
            = 1 := by
          have hshape : ∀ c, design.weight c * (design.atom c ⬝ᵥ design.atom pole)
              * (design.atom c ⬝ᵥ design.atom pole / (design.atom pole ⬝ᵥ design.atom pole))
              = design.weight c * (design.atom c ⬝ᵥ design.atom pole) ^ 2
                / (design.atom pole ⬝ᵥ design.atom pole) := fun c => by ring
          rw [Finset.sum_congr rfl fun c _ => hshape c, ← Finset.sum_div, hmass,
            div_self hne]
        rw [hsum, one_smul, sub_self]

/-- The non-pole cross moment also vanishes, because the pole's own term is
the zero vector. -/
theorem sum_erase_weight_pairing_smul_planeShadowVec (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    ∑ c ∈ Finset.univ.erase pole,
        (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
          • planeShadowVec design pole c = 0 := by
  have hall := sum_weight_pairing_smul_planeShadowVec design hpole
  have hpoleTerm : (design.weight pole * (design.atom pole ⬝ᵥ design.atom pole))
      • planeShadowVec design pole pole = (0 : Fin rank → ℝ) := by
    rw [planeShadowVec_self_pole design hpole, smul_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pole), hpoleTerm, zero_add] at hall
  exact hall

/-- **THE SURVIVORS READ THE DELETED SET.**  On every set of non-pole labels,
the weighted coupling of the survivors is MINUS the weighted coupling of the
set.  At the deciding cell this pins the coupling of the survivor triple to
the deleted pair's own data. -/
theorem sum_sdiff_weight_pairing_smul_planeShadowVec (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hsub : deleted ⊆ Finset.univ.erase pole) :
    ∑ c ∈ Finset.univ.erase pole \ deleted,
        (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
          • planeShadowVec design pole c
      = - ∑ c ∈ deleted,
          (design.weight c * (design.atom c ⬝ᵥ design.atom pole))
            • planeShadowVec design pole c := by
  have herase := sum_erase_weight_pairing_smul_planeShadowVec design hpole
  rw [← Finset.sum_sdiff hsub] at herase
  exact eq_neg_of_add_eq_zero_left herase

end CrossMoment

end Gtz

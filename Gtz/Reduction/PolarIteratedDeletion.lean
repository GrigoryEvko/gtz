/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.PolarDeletionWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The iterated deletion: a covering set that avoids a whole named SET

`Gtz.exists_polarDeletionCover` steers the covering set of the pole's orthogonal
hyperplane away from ONE named atom.  One atom is not enough at the deciding
cell, and the three measured misses of the single deletion are all misses by a
constant factor.  This file deletes a SET.

## 1. The composition is free, and the shares cancel

Each deletion is the rank-one shear `Gtz.shear`.  Composing the deletions of a
set `T` gives a map `lift` with ONE law:

  `lift y ⬝ᵥ lift y = y ⬝ᵥ y - Σ_{q ∈ T} weight q * (atom q ⬝ᵥ y)²`.

The composed map removes EXACTLY the deleted atoms, with the ORIGINAL weights
and the ORIGINAL atoms.  No sheared length appears in the law, because the
renormalization of each step cancels the share of the step before it.
`Gtz.DeletionData` carries that law together with the reading law
`design.atom c ⬝ᵥ lift y = gain * (atom c ⬝ᵥ y)` and the weight law
`design.weight c * gain² = weight c`.

## 2. The set condition, and it is the trace of the deleted Gram

`Gtz.exists_deletionData` builds the data of every deleted set under ONE
hypothesis: `Σ_{q ∈ T} weight q * |atom q|² < 1`.  The step needs the deleted
atom of the CURRENT design to stay below the cap, and
`Gtz.DeletionData.unsaturated` proves that from the running total alone.  Thus
the bookkeeping of the sheared lengths never reaches the statement.

## 3. The cover, and the deletion debt

`Gtz.exists_polarSetDeletionCover` is the payoff: a covering set of the pole's
orthogonal hyperplane of card `rank - 1` that avoids the pole AND every label of
`T`, with the factor

  `(1 - Σ_T weight q * planeShadowSq) / (1 - weight pole - Σ_T weight q)`.

The factor beats one exactly when the DELETION DEBT
`Gtz.planeShadowDebt = Σ_T weight q * (planeShadowSq - 1)` stays below the
pole's weight.  `Gtz.sum_weight_planeShadowDebt` prices the whole debt:

  `Σ_{c ≠ pole} weight c * (planeShadowSq - 1) = rank - 2 + weight pole`.

Thus a set is deletable exactly when its SURVIVORS carry debt more than
`rank - 2` (`Gtz.deletableSet_iff_survivor_debt`), and the full non-pole set is
never deletable.

## 4. What the set deletion kills, and where it stops

`Gtz.not_isTie_of_deletableSetTilt` closes every tie that carries a deletable
set whose survivors are all below the tilt budget, and
`Gtz.PolarSetDeletionHeavy` is that fact read forwards.  It is free at every
tie, thus `Gtz.PolarTiltSelectionSetDeletion` narrows the residual a third time.

`Gtz.card_survivor_lower_bound_of_deletable` prices the STOP: when every label
of a design carries debt at least `debtFloor`, a deletable set leaves at least
`(rank - 2)/debtFloor` survivors.  At the uniform deciding cell of rank three
that forces the deleted set to be EMPTY, thus the iterated deletion does not
cross the deciding cell by itself.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the inverse shear, and two small facts about the dot product

The whitening shear and the unwhitening shear are inverse in BOTH orders, and
the file needs both directions: one to read a cover back at the plain probe, one
to see that the composed map is onto. -/

section ShearInverse

variable {dim : ℕ}

/-- The self dot product of a real vector is never negative. -/
theorem selfDotProduct_nonneg (vec : Fin dim → ℝ) : 0 ≤ vec ⬝ᵥ vec :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- **A MARGIN STRICTLY BELOW THE SHARP ONE THAT STILL BEATS A BUDGET.**  One
maximum, and no limit argument. -/
theorem exists_margin_below_sharp {sharp bound gap : ℝ} (hsharpPos : 0 < sharp)
    (hgapPos : 0 < gap) (hbudget : bound < sharp * gap) :
    ∃ margin : ℝ, 0 < margin ∧ margin < sharp ∧ bound < margin * gap := by
  set need : ℝ := bound / gap with hneed
  have hneedLt : need < sharp := by rw [hneed, div_lt_iff₀ hgapPos]; exact hbudget
  set margin : ℝ := (max need 0 + sharp) / 2 with hmargin
  have hmaxLt : max need 0 < sharp := max_lt hneedLt hsharpPos
  have hmaxNonneg : 0 ≤ max need 0 := le_max_right _ _
  have hneedLe : need ≤ max need 0 := le_max_left _ _
  refine ⟨margin, by rw [hmargin]; linarith, by rw [hmargin]; linarith, ?_⟩
  have hstep : need < margin := by rw [hmargin]; linarith
  rw [hneed, div_lt_iff₀ hgapPos] at hstep
  linarith

/-- **THE TWO SHEARS ARE INVERSE IN THE OTHER ORDER TOO.**  The composed gain of
`Gtz.shear_shear` is symmetric in the two gains, thus the proof of
`Gtz.whiten_unwhiten` transports with the roles exchanged.  This direction is
what makes the composed lift ONTO. -/
theorem unwhiten_whiten {scale : ℝ} {axis : Fin dim → ℝ}
    (hunsat : scale * (axis ⬝ᵥ axis) < 1) (probe : Fin dim → ℝ) :
    shear (unwhitenGain scale axis) axis (shear (whitenGain scale axis) axis probe) = probe := by
  set energy : ℝ := axis ⬝ᵥ axis with henergy
  set root : ℝ := Real.sqrt (1 - scale * energy) with hroot
  have hrootPos : 0 < root := sqrt_deficit_pos hunsat
  have hwhite : whitenGain scale axis * energy = root⁻¹ - 1 := whitenGain_mul_self scale axis
  have hunwhite : unwhitenGain scale axis * energy = root - 1 := unwhitenGain_mul_self scale axis
  rw [shear_shear]
  refine shear_eq_self_of_gain_mul_self_eq_zero ?_ probe
  rw [← henergy]
  have hexpand : (unwhitenGain scale axis + whitenGain scale axis
        + unwhitenGain scale axis * whitenGain scale axis * energy) * energy
      = unwhitenGain scale axis * energy + whitenGain scale axis * energy
        + (unwhitenGain scale axis * energy) * (whitenGain scale axis * energy) := by ring
  rw [hexpand, hwhite, hunwhite]
  have hrootNe : root ≠ 0 := ne_of_gt hrootPos
  field_simp
  ring

end ShearInverse

/-! ## Part 2: the data of a deleted set

The composition of the deletions of a set is described by four laws.  Carrying
them as a structure is what makes the induction over the deleted set possible:
each law is preserved by one more deletion, and no law mentions a sheared
length. -/

section DeletionData

variable {size dim : ℕ}

/-- **THE DATA OF A DELETED SET.**  A design in which the pole and every label of
`T` read as the zero atom, together with the composed lift of the deletions.

The four laws are the whole content of the iterated deletion:

- `weight_law` — the weights of the survivors are the original ones divided by
  the squared gain
- `read_law` — a survivor reads the lift as the original atom, scaled by the gain
- `length_law` — the lift removes EXACTLY the deleted atoms, with the ORIGINAL
  weights and atoms
- `section_law` — the lift is onto. -/
structure DeletionData (base : WeightedDesign size dim) (pole : Fin size)
    (deleted : Finset (Fin size)) where
  /-- The design that the deletions produce. -/
  design : WeightedDesign size dim
  /-- The composed unwhitening map, from the base probes to the design probes. -/
  lift : (Fin dim → ℝ) → (Fin dim → ℝ)
  /-- A right inverse of the lift. -/
  drop : (Fin dim → ℝ) → (Fin dim → ℝ)
  /-- The composed scale of the deletions. -/
  gain : ℝ
  gain_pos : 0 < gain
  atom_pole : design.atom pole = 0
  atom_deleted : ∀ label ∈ deleted, design.atom label = 0
  weight_law : ∀ label, label ≠ pole → label ∉ deleted →
    design.weight label * gain ^ 2 = base.weight label
  read_law : ∀ label, label ≠ pole → label ∉ deleted → ∀ probe : Fin dim → ℝ,
    design.atom label ⬝ᵥ lift probe = gain * (base.atom label ⬝ᵥ probe)
  length_law : ∀ probe : Fin dim → ℝ, lift probe ⬝ᵥ lift probe
    = probe ⬝ᵥ probe - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ probe) ^ 2
  section_law : ∀ vec : Fin dim → ℝ, lift (drop vec) = vec

/-- **THE EMPTY DELETION.**  The base design itself, with the identity lift and
gain one.  It is the start of the induction, and its gain records that no
renormalization has happened. -/
def emptyDeletionData (base : WeightedDesign size dim) {pole : Fin size}
    (hdead : base.atom pole = 0) : DeletionData base pole ∅ where
  design := base
  lift := id
  drop := id
  gain := 1
  gain_pos := one_pos
  atom_pole := hdead
  atom_deleted := fun _ hmem => absurd hmem (Finset.notMem_empty _)
  weight_law := fun _ _ _ => by ring
  read_law := fun _ _ _ _ => by rw [id_eq, one_mul]
  length_law := fun _ => by rw [id_eq, Finset.sum_empty, sub_zero]
  section_law := fun _ => rfl

@[simp] theorem emptyDeletionData_gain (base : WeightedDesign size dim) {pole : Fin size}
    (hdead : base.atom pole = 0) : (emptyDeletionData base hdead).gain = 1 := rfl

@[simp] theorem emptyDeletionData_design (base : WeightedDesign size dim) {pole : Fin size}
    (hdead : base.atom pole = 0) : (emptyDeletionData base hdead).design = base := rfl

/-- **THE STEP IS ADMISSIBLE AS SOON AS THE RUNNING TOTAL IS.**  The next
deletion needs the named atom of the CURRENT design to stay below the leverage
cap.  That is not a statement about the original data, but the four laws price
it: the sheared energy of a label is capped by its own energy divided by the
free part of the running total. -/
theorem DeletionData.unsaturated {base : WeightedDesign size dim} {pole : Fin size}
    {deleted : Finset (Fin size)} (data : DeletionData base pole deleted)
    {label : Fin size} (hne : label ≠ pole) (hnotMem : label ∉ deleted)
    (htotal : base.weight label * (base.atom label ⬝ᵥ base.atom label)
        + ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q) < 1) :
    data.design.weight label * (data.design.atom label ⬝ᵥ data.design.atom label) < 1 := by
  classical
  set target : Fin dim → ℝ := data.design.atom label with htarget
  set source : Fin dim → ℝ := data.drop target with hsource
  have hnonneg : ∀ q ∈ deleted, 0 ≤ base.weight q * (base.atom q ⬝ᵥ source) ^ 2 :=
    fun q _ => mul_nonneg (base.weight_pos q).le (sq_nonneg _)
  have hthetaNonneg : 0 ≤ ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q) :=
    Finset.sum_nonneg fun q _ => mul_nonneg (base.weight_pos q).le (selfDotProduct_nonneg _)
  have hlabelNonneg : 0 ≤ base.weight label * (base.atom label ⬝ᵥ base.atom label) :=
    mul_nonneg (base.weight_pos label).le (selfDotProduct_nonneg _)
  have hthetaLt : (∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q)) < 1 := by
    linarith
  have hlift : data.lift source = target := data.section_law target
  have hlength : target ⬝ᵥ target
      = source ⬝ᵥ source - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ source) ^ 2 := by
    rw [← hlift]
    exact data.length_law source
  have hread : target ⬝ᵥ target = data.gain * (base.atom label ⬝ᵥ source) := by
    have hstep := data.read_law label hne hnotMem source
    rw [hlift, ← htarget] at hstep
    exact hstep
  -- every deleted atom is priced by Cauchy-Schwarz against the source
  have hshadow : ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ source) ^ 2
      ≤ (∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q)) * (source ⬝ᵥ source) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun q _ => ?_
    have hcauchy := dotProduct_sq_le_mul_self (base.atom q) source
    have hweight := (base.weight_pos q).le
    calc base.weight q * (base.atom q ⬝ᵥ source) ^ 2
        ≤ base.weight q * ((base.atom q ⬝ᵥ base.atom q) * (source ⬝ᵥ source)) :=
          mul_le_mul_of_nonneg_left hcauchy hweight
      _ = base.weight q * (base.atom q ⬝ᵥ base.atom q) * (source ⬝ᵥ source) := by ring
  have hsourceBound : (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
      * (source ⬝ᵥ source) ≤ target ⬝ᵥ target := by
    rw [hlength]; nlinarith [hshadow]
  have hcauchyLabel : (base.atom label ⬝ᵥ source) ^ 2
      ≤ (base.atom label ⬝ᵥ base.atom label) * (source ⬝ᵥ source) :=
    dotProduct_sq_le_mul_self (base.atom label) source
  have hsquare : (target ⬝ᵥ target) ^ 2
      = data.gain ^ 2 * (base.atom label ⬝ᵥ source) ^ 2 := by rw [hread]; ring
  have htargetNonneg : 0 ≤ target ⬝ᵥ target := selfDotProduct_nonneg target
  have hgainSq : 0 < data.gain ^ 2 := pow_pos data.gain_pos 2
  have hweightLaw : data.design.weight label * data.gain ^ 2 = base.weight label :=
    data.weight_law label hne hnotMem
  have hdesignWeight := data.design.weight_pos label
  rcases eq_or_lt_of_le htargetNonneg with hzero | hpos
  · rw [htarget] at hzero
    rw [← hzero, mul_zero]
    norm_num
  · -- the squared energy is capped, thus the energy is capped
    have hchain : (target ⬝ᵥ target) ^ 2
        ≤ data.gain ^ 2 * ((base.atom label ⬝ᵥ base.atom label) * (source ⬝ᵥ source)) := by
      rw [hsquare]
      exact mul_le_mul_of_nonneg_left hcauchyLabel hgainSq.le
    have hlabelEnergy : 0 ≤ base.atom label ⬝ᵥ base.atom label := selfDotProduct_nonneg _
    have hthetaPos : (0 : ℝ)
        < 1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q) := by linarith
    have hcoeffNonneg : 0 ≤ data.gain ^ 2 * (base.atom label ⬝ᵥ base.atom label) :=
      mul_nonneg hgainSq.le hlabelEnergy
    have hleft : (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
        * (target ⬝ᵥ target) ^ 2
        ≤ (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
          * (data.gain ^ 2 * ((base.atom label ⬝ᵥ base.atom label) * (source ⬝ᵥ source))) :=
      mul_le_mul_of_nonneg_left hchain hthetaPos.le
    have hright : (data.gain ^ 2 * (base.atom label ⬝ᵥ base.atom label))
        * ((1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
          * (source ⬝ᵥ source))
        ≤ (data.gain ^ 2 * (base.atom label ⬝ᵥ base.atom label)) * (target ⬝ᵥ target) :=
      mul_le_mul_of_nonneg_left hsourceBound hcoeffNonneg
    have hstep : ((1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
          * (target ⬝ᵥ target)) * (target ⬝ᵥ target)
        ≤ (data.gain ^ 2 * (base.atom label ⬝ᵥ base.atom label)) * (target ⬝ᵥ target) := by
      nlinarith [hleft, hright]
    have hkey : (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
        * (target ⬝ᵥ target)
        ≤ data.gain ^ 2 * (base.atom label ⬝ᵥ base.atom label) :=
      le_of_mul_le_mul_right hstep hpos
    have hfinal : data.design.weight label * (target ⬝ᵥ target)
        * (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
        ≤ base.weight label * (base.atom label ⬝ᵥ base.atom label) := by
      have hscaled := mul_le_mul_of_nonneg_left hkey hdesignWeight.le
      calc data.design.weight label * (target ⬝ᵥ target)
              * (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
          = data.design.weight label
            * ((1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
              * (target ⬝ᵥ target)) := by ring
        _ ≤ data.design.weight label
            * (data.gain ^ 2 * (base.atom label ⬝ᵥ base.atom label)) := hscaled
        _ = base.weight label * (base.atom label ⬝ᵥ base.atom label) := by
            rw [← hweightLaw]; ring
    nlinarith [hfinal, hdesignWeight, hpos, hthetaLt]

end DeletionData

/-! ## Part 3: one more deletion

The step takes the data of a deleted set and one more label, and it produces the
data of the enlarged set.  Every law is preserved by a two-line computation,
because the composed lift is the old lift followed by ONE more unwhitening
shear. -/

section DeletionStep

variable {size dim : ℕ}

/-- The weight the deleted design leaves with the pole. -/
theorem deletePairDesign_weight_dead (D : WeightedDesign size dim) {dead live : Fin size}
    {share : ℝ} (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1) :
    (deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat).weight dead
      = share := by
  show (if dead = dead then share else _) = share
  rw [if_pos rfl]

/-- A label that already reads as the zero atom stays zero after one more
deletion. -/
theorem deletePairDesign_atom_of_eq_zero (D : WeightedDesign size dim) {dead live : Fin size}
    {share : ℝ} (hne : live ≠ dead) (hdead : D.atom dead = 0)
    (hshare : 0 < share) (hshareLt : 2 * share < D.weight dead + D.weight live)
    (hpairLt : D.weight dead + D.weight live < 1)
    (hunsat : D.weight live * (D.atom live ⬝ᵥ D.atom live) < 1)
    {label : Fin size} (hlabelDead : label ≠ dead) (hlabelLive : label ≠ live)
    (hzero : D.atom label = 0) :
    (deletePairDesign D dead live share hne hdead hshare hshareLt hpairLt hunsat).atom label
      = 0 := by
  show (if label = dead then (0 : Fin dim → ℝ)
      else if label = live then 0
      else Real.sqrt (deleteScaleSq D dead live share)
        • shear (whitenGain (D.weight live) (D.atom live)) (D.atom live) (D.atom label)) = 0
  rw [if_neg hlabelDead, if_neg hlabelLive, hzero, shear_zero_probe, smul_zero]

/-- **ONE MORE DELETION.**  Given the data of a deleted set and a label outside
it, the enlarged set has data too, and its squared gain is capped by any value
that beats the old one after the label's weight is removed.

The share of the step is chosen inside the proof by one minimum, thus the caller
never sees it. -/
theorem exists_deletionData_step (hsize : 3 ≤ size) {base : WeightedDesign size dim}
    {pole : Fin size} {deleted : Finset (Fin size)} (data : DeletionData base pole deleted)
    {label : Fin size} (hne : label ≠ pole) (hnotMem : label ∉ deleted)
    (htotal : base.weight label * (base.atom label ⬝ᵥ base.atom label)
        + ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q) < 1)
    {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : data.gain ^ 2 * (1 - data.design.weight pole) - base.weight label < cap) :
    ∃ next : DeletionData base pole (insert label deleted), next.gain ^ 2 ≤ cap := by
  classical
  set D := data.design with hD
  have hunsat : D.weight label * (D.atom label ⬝ᵥ D.atom label) < 1 :=
    data.unsaturated hne hnotMem htotal
  have hpairLt : D.weight pole + D.weight label < 1 :=
    weight_pair_lt_one D (fun heq => hne heq.symm) hsize
  have hgainSq : 0 < data.gain ^ 2 := pow_pos data.gain_pos 2
  have hweightLaw : D.weight label * data.gain ^ 2 = base.weight label :=
    data.weight_law label hne hnotMem
  have hpolePos := D.weight_pos pole
  have hlivePos := D.weight_pos label
  have hfree : (0 : ℝ) < 1 - D.weight pole - D.weight label := by linarith
  -- the target of the step, and the share that reaches it
  set target : ℝ := data.gain ^ 2 * (1 - D.weight pole - D.weight label) with htarget
  have hshapeCap : data.gain ^ 2 * (1 - D.weight pole) - base.weight label = target := by
    rw [htarget, ← hweightLaw]; ring
  have htargetLt : target < cap := by rw [← hshapeCap]; exact hcap
  have htargetPos : 0 < target := by rw [htarget]; exact mul_pos hgainSq hfree
  set share : ℝ := min ((cap - target) / (4 * cap)) ((D.weight pole + D.weight label) / 4)
    with hshareDef
  have hsharePos : 0 < share := by
    rw [hshareDef]
    exact lt_min (div_pos (by linarith) (by linarith)) (by linarith)
  have hshareQuarter : share ≤ (D.weight pole + D.weight label) / 4 := by
    rw [hshareDef]; exact min_le_right _ _
  have hshareLt : 2 * share < D.weight pole + D.weight label := by linarith
  have hshareSmall : share ≤ (cap - target) / (4 * cap) := by
    rw [hshareDef]; exact min_le_left _ _
  have hdenPos : (0 : ℝ) < 1 - 2 * share := by linarith
  set scaleSq : ℝ := deleteScaleSq D pole label share with hscaleSq
  have hscalePos : 0 < scaleSq := by
    rw [hscaleSq, deleteScaleSq]
    exact div_pos hfree hdenPos
  have hscaleRoot : Real.sqrt scaleSq ^ 2 = scaleSq := Real.sq_sqrt hscalePos.le
  set nextDesign := deletePairDesign D pole label share hne data.atom_pole
    hsharePos hshareLt hpairLt hunsat with hnextDesign
  set stepGain : ℝ := whitenGain (D.weight label) (D.atom label) with hstepGain
  set stepBack : ℝ := unwhitenGain (D.weight label) (D.atom label) with hstepBack
  refine ⟨{ design := nextDesign
            lift := fun probe => shear stepBack (D.atom label) (data.lift probe)
            drop := fun vec => data.drop (shear stepGain (D.atom label) vec)
            gain := Real.sqrt scaleSq * data.gain
            gain_pos := mul_pos (Real.sqrt_pos.mpr hscalePos) data.gain_pos
            atom_pole := ?_
            atom_deleted := ?_
            weight_law := ?_
            read_law := ?_
            length_law := ?_
            section_law := ?_ }, ?_⟩
  · rw [hnextDesign]
    exact deletePairDesign_atom_dead D hne data.atom_pole hsharePos hshareLt hpairLt hunsat
  · intro other hother
    by_cases hotherPole : other = pole
    · rw [hotherPole, hnextDesign]
      exact deletePairDesign_atom_dead D hne data.atom_pole hsharePos
        hshareLt hpairLt hunsat
    · rcases Finset.mem_insert.mp hother with heq | hmem
      · rw [heq, hnextDesign]
        exact deletePairDesign_atom_live D hne data.atom_pole hsharePos
          hshareLt hpairLt hunsat
      · have hotherLive : other ≠ label := fun heq => hnotMem (heq ▸ hmem)
        rw [hnextDesign]
        exact deletePairDesign_atom_of_eq_zero D hne data.atom_pole
          hsharePos hshareLt hpairLt hunsat hotherPole hotherLive (data.atom_deleted other hmem)
  · intro other hotherPole hotherNotMem
    have hotherLive : other ≠ label := fun heq => hotherNotMem (by
      rw [heq]; exact Finset.mem_insert_self _ _)
    have hotherDeleted : other ∉ deleted := fun hmem => hotherNotMem (Finset.mem_insert_of_mem hmem)
    have hweightNext : nextDesign.weight other
        = D.weight other * ((1 - 2 * share) / (1 - D.weight pole - D.weight label)) := by
      rw [hnextDesign]
      exact deletePairDesign_weight_of_ne D hne data.atom_pole hsharePos
        hshareLt hpairLt hunsat hotherPole hotherLive
    have hbase : D.weight other * data.gain ^ 2 = base.weight other :=
      data.weight_law other hotherPole hotherDeleted
    have hshape : nextDesign.weight other * (Real.sqrt scaleSq * data.gain) ^ 2
        = D.weight other * data.gain ^ 2 := by
      rw [hweightNext, mul_pow, hscaleRoot, hscaleSq, deleteScaleSq]
      field_simp
    rw [hshape, hbase]
  · intro other hotherPole hotherNotMem probe
    have hotherLive : other ≠ label := fun heq => hotherNotMem (by
      rw [heq]; exact Finset.mem_insert_self _ _)
    have hotherDeleted : other ∉ deleted := fun hmem => hotherNotMem (Finset.mem_insert_of_mem hmem)
    have hstep : nextDesign.atom other ⬝ᵥ shear stepBack (D.atom label) (data.lift probe)
        = Real.sqrt scaleSq
          * (D.atom other ⬝ᵥ shear stepGain (D.atom label)
              (shear stepBack (D.atom label) (data.lift probe))) := by
      rw [hnextDesign]
      exact deletePairDesign_atom_dotProduct D hne data.atom_pole
        hsharePos hshareLt hpairLt hunsat hotherPole hotherLive _
    rw [hstep, hstepGain, hstepBack, whiten_unwhiten hunsat,
      data.read_law other hotherPole hotherDeleted probe]
    ring
  · intro probe
    have hunwhiten := unwhiten_dotProduct hunsat (data.lift probe) (data.lift probe)
    rw [hstepBack, hunwhiten, data.length_law probe,
      data.read_law label hne hnotMem probe, Finset.sum_insert hnotMem]
    have hscale : D.weight label * (data.gain * (base.atom label ⬝ᵥ probe)
        * (data.gain * (base.atom label ⬝ᵥ probe)))
        = base.weight label * (base.atom label ⬝ᵥ probe) ^ 2 := by
      rw [← hweightLaw]; ring
    rw [hscale]
    ring
  · intro vec
    rw [data.section_law (shear stepGain (D.atom label) vec), hstepBack, hstepGain,
      unwhiten_whiten hunsat]
  · -- the squared gain of the step
    have hvalue : (Real.sqrt scaleSq * data.gain) ^ 2 = scaleSq * data.gain ^ 2 := by
      rw [mul_pow, hscaleRoot]
    have hshape : scaleSq * data.gain ^ 2 = target / (1 - 2 * share) := by
      rw [hscaleSq, deleteScaleSq, htarget]
      ring
    rw [hvalue, hshape, div_le_iff₀ hdenPos]
    have hcapShare : 4 * cap * share ≤ cap - target := by
      have hstep := mul_le_mul_of_nonneg_left hshareSmall (by linarith : (0:ℝ) ≤ 4 * cap)
      calc 4 * cap * share ≤ 4 * cap * ((cap - target) / (4 * cap)) := hstep
        _ = cap - target := by field_simp
    nlinarith [hcapShare, hcapPos, hsharePos]

end DeletionStep

/-! ## Part 4: the deletion of a whole set

The induction over the deleted set carries one number: the squared gain.  Its
limit is the SURVIVING WEIGHT MASS `1 - weight pole - Σ_T weight q`, and the
statement asks only that the caller name a value above that limit. -/

section DeletionSet

variable {size dim : ℕ}

/-- **THE SURVIVING WEIGHT MASS IS NEVER NEGATIVE.**  The pole together with the
deleted labels never carries more than the whole weight of the design. -/
theorem weight_insert_le_one (design : WeightedDesign size dim) {pole : Fin size}
    {deleted : Finset (Fin size)} (hpole : pole ∉ deleted) :
    design.weight pole + ∑ q ∈ deleted, design.weight q ≤ 1 := by
  classical
  have hsplit : ∑ q ∈ insert pole deleted, design.weight q
      = design.weight pole + ∑ q ∈ deleted, design.weight q := Finset.sum_insert hpole
  have hgrow : ∑ q ∈ insert pole deleted, design.weight q ≤ ∑ q, design.weight q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun q _ _ => (design.weight_pos q).le
  rw [design.weight_sum_one] at hgrow
  linarith [hsplit ▸ hgrow]

/-- **THE DATA OF EVERY DELETED SET.**  Under one hypothesis on the total
weighted energy of the deleted labels, every nonempty set of labels outside the
pole carries deletion data whose squared gain is as close to the surviving
weight mass as the caller asks. -/
theorem exists_deletionData (hsize : 3 ≤ size) (base : WeightedDesign size dim)
    {pole : Fin size} (hdead : base.atom pole = 0) :
    ∀ deleted : Finset (Fin size), ∀ label : Fin size, label ∉ deleted → label ≠ pole →
      pole ∉ deleted →
      (∑ q ∈ insert label deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q) < 1) →
      ∀ cap : ℝ, 0 < cap →
        1 - base.weight pole - ∑ q ∈ insert label deleted, base.weight q < cap →
        ∃ data : DeletionData base pole (insert label deleted), data.gain ^ 2 ≤ cap := by
  classical
  intro deleted
  induction deleted using Finset.induction_on with
  | empty =>
      intro label _ hne _ htotal cap hcapPos hcap
      refine exists_deletionData_step hsize (emptyDeletionData base hdead) hne
        (Finset.notMem_empty label) ?_ hcapPos ?_
      · rw [Finset.sum_insert (Finset.notMem_empty label), Finset.sum_empty] at htotal
        rw [Finset.sum_empty]
        linarith
      · rw [emptyDeletionData_gain, emptyDeletionData_design, one_pow, one_mul]
        rw [Finset.sum_insert (Finset.notMem_empty label), Finset.sum_empty] at hcap
        linarith
  | insert first rest hfirst ih =>
      intro label hlabel hne hpole htotal cap hcapPos hcap
      have hlabelFirst : label ≠ first := fun heq =>
        hlabel (by rw [heq]; exact Finset.mem_insert_self _ _)
      have hlabelRest : label ∉ rest := fun hmem =>
        hlabel (Finset.mem_insert_of_mem hmem)
      have hfirstPole : first ≠ pole := fun heq =>
        hpole (by rw [← heq]; exact Finset.mem_insert_self _ _)
      have hpoleRest : pole ∉ rest := fun hmem => hpole (Finset.mem_insert_of_mem hmem)
      have hnonnegAll : ∀ q : Fin size, 0 ≤ base.weight q * (base.atom q ⬝ᵥ base.atom q) :=
        fun q => mul_nonneg (base.weight_pos q).le (selfDotProduct_nonneg _)
      -- the running total of the smaller set, and the total with the new label
      have hsplit : ∑ q ∈ insert label (insert first rest),
            base.weight q * (base.atom q ⬝ᵥ base.atom q)
          = base.weight label * (base.atom label ⬝ᵥ base.atom label)
            + ∑ q ∈ insert first rest, base.weight q * (base.atom q ⬝ᵥ base.atom q) :=
        Finset.sum_insert hlabel
      have hinnerTotal : ∑ q ∈ insert first rest,
          base.weight q * (base.atom q ⬝ᵥ base.atom q) < 1 := by
        rw [hsplit] at htotal
        linarith [hnonnegAll label]
      -- the weight mass, and the intermediate cap
      set outerMass : ℝ := 1 - base.weight pole
        - ∑ q ∈ insert label (insert first rest), base.weight q with houterMass
      set innerMass : ℝ := 1 - base.weight pole
        - ∑ q ∈ insert first rest, base.weight q with hinnerMass
      have hmassSplit : innerMass = outerMass + base.weight label := by
        rw [houterMass, hinnerMass, Finset.sum_insert hlabel]; ring
      have hpoleOuter : pole ∉ insert label (insert first rest) := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem'
        · exact hne heq.symm
        · exact hpole hmem'
      have houterNonneg : 0 ≤ outerMass := by
        rw [houterMass]
        linarith [weight_insert_le_one base hpoleOuter]
      set slack : ℝ := (cap - outerMass) / 2 with hslack
      have hslackPos : 0 < slack := by rw [hslack]; linarith
      set innerCap : ℝ := innerMass + slack with hinnerCap
      have hinnerCapGt : innerMass < innerCap := by rw [hinnerCap]; linarith
      have hinnerCapPos : 0 < innerCap := by
        rw [hinnerCap, hmassSplit]
        linarith [base.weight_pos label]
      obtain ⟨inner, hinnerGain⟩ := ih first hfirst hfirstPole hpoleRest hinnerTotal innerCap
        hinnerCapPos hinnerCapGt
      refine exists_deletionData_step hsize inner hne (by
        intro hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem'
        · exact hlabelFirst heq
        · exact hlabelRest hmem') ?_ hcapPos ?_
      · rw [hsplit] at htotal
        linarith
      · have hpoleWeight := inner.design.weight_pos pole
        have hgainSq : 0 < inner.gain ^ 2 := pow_pos inner.gain_pos 2
        have hstep : inner.gain ^ 2 * (1 - inner.design.weight pole)
            ≤ inner.gain ^ 2 := by nlinarith [hpoleWeight, hgainSq]
        have hchain : inner.gain ^ 2 * (1 - inner.design.weight pole) - base.weight label
            ≤ innerCap - base.weight label := by linarith
        have hvalue : innerCap - base.weight label = outerMass + slack := by
          rw [hinnerCap, hmassSplit]; ring
        rw [hvalue] at hchain
        have : outerMass + slack < cap := by rw [hslack]; linarith
        linarith

/-- **THE DELETION COVER OF A SET.**  Under the previous rank, every design with
a dead pole and a nonempty deleted set of total weighted energy below one carries
`dim` labels, NEITHER the pole NOR any deleted label, that cover the identity
with the factor

  `(1 - Σ_T weight q * |atom q|²) / cap`

at every `cap` above the surviving weight mass. -/
theorem exists_setDeletionCover (hpredecessor : GtzWeightedAll dim) (hsize : 3 ≤ size)
    (base : WeightedDesign size dim) {pole : Fin size} (hdead : base.atom pole = 0)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : dim + 1 + deleted.card ≤ size)
    (htotal : ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q) < 1)
    {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : 1 - base.weight pole - ∑ q ∈ deleted, base.weight q < cap) :
    ∃ covering : Finset (Fin size), covering.card = dim ∧ pole ∉ covering
      ∧ (∀ q ∈ deleted, q ∉ covering)
      ∧ ∀ probe : Fin dim → ℝ,
          ((1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q)) / cap)
              * (probe ⬝ᵥ probe)
            ≤ ∑ c ∈ covering, (base.atom c ⬝ᵥ probe) ^ 2 := by
  classical
  obtain ⟨label, hlabel⟩ := hnonempty
  have hlabelPole : label ≠ pole := fun heq => hpole (heq ▸ hlabel)
  have hrestore : insert label (deleted.erase label) = deleted :=
    Finset.insert_erase hlabel
  have hdataStep := exists_deletionData hsize base hdead (deleted.erase label) label
    (Finset.notMem_erase label deleted) hlabelPole
    (fun hmem => hpole (Finset.mem_of_mem_erase hmem))
    (by rw [hrestore]; exact htotal) cap hcapPos (by rw [hrestore]; exact hcap)
  rw [hrestore] at hdataStep
  obtain ⟨data, hgain⟩ := hdataStep
  -- the previous rank returns a covering of the deleted design
  obtain ⟨rawCovering, hrawCard, hrawDominates⟩ := hpredecessor size data.design
  set forbidden : Finset (Fin size) := insert pole deleted with hforbidden
  have hforbiddenCard : forbidden.card = deleted.card + 1 := by
    rw [hforbidden, Finset.card_insert_of_notMem hpole]
  have hcomplementCard : (Finset.univ \ forbidden).card = size - (deleted.card + 1) := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hforbiddenCard]
  have hsubset : rawCovering \ forbidden ⊆ Finset.univ \ forbidden :=
    Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl _)
  have hsmallCard : (rawCovering \ forbidden).card ≤ dim :=
    le_trans (Finset.card_le_card Finset.sdiff_subset) (le_of_eq hrawCard)
  have hbigCard : dim ≤ (Finset.univ \ forbidden).card := by rw [hcomplementCard]; omega
  obtain ⟨covering, hcoverSup, hcoverSub, hcoverCard⟩ :=
    Finset.exists_subsuperset_card_eq hsubset hsmallCard hbigCard
  have hpoleNotMem : pole ∉ covering := fun hmem => by
    have := (Finset.mem_sdiff.mp (hcoverSub hmem)).2
    exact this (by rw [hforbidden]; exact Finset.mem_insert_self _ _)
  have hdeletedNotMem : ∀ q ∈ deleted, q ∉ covering := by
    intro q hq hmem
    have := (Finset.mem_sdiff.mp (hcoverSub hmem)).2
    exact this (by rw [hforbidden]; exact Finset.mem_insert_of_mem hq)
  refine ⟨covering, hcoverCard, hpoleNotMem, hdeletedNotMem, fun probe => ?_⟩
  -- read the domination of the deleted design at the lifted probe
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hrawDominates).2 (data.lift probe)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form, Matrix.one_mulVec] at hform
  have hzeroOut : ∀ c ∈ rawCovering, c ∉ rawCovering \ forbidden →
      (data.design.atom c ⬝ᵥ data.lift probe) ^ 2 = 0 := by
    intro c hmem hnot
    have hin : c ∈ forbidden := by
      by_contra hout
      exact hnot (Finset.mem_sdiff.mpr ⟨hmem, hout⟩)
    rw [hforbidden] at hin
    rcases Finset.mem_insert.mp hin with heq | hmemDeleted
    · rw [heq, data.atom_pole, zero_dotProduct]; ring
    · rw [data.atom_deleted c hmemDeleted, zero_dotProduct]; ring
  have hshrink : ∑ c ∈ rawCovering, (data.design.atom c ⬝ᵥ data.lift probe) ^ 2
      = ∑ c ∈ rawCovering \ forbidden, (data.design.atom c ⬝ᵥ data.lift probe) ^ 2 :=
    (Finset.sum_subset Finset.sdiff_subset hzeroOut).symm
  have hread : ∀ c ∈ rawCovering \ forbidden,
      (data.design.atom c ⬝ᵥ data.lift probe) ^ 2
        = data.gain ^ 2 * (base.atom c ⬝ᵥ probe) ^ 2 := by
    intro c hmem
    have hout : c ∉ forbidden := (Finset.mem_sdiff.mp hmem).2
    have hcPole : c ≠ pole := fun heq => hout (by
      rw [hforbidden, heq]; exact Finset.mem_insert_self _ _)
    have hcDeleted : c ∉ deleted := fun hmemDeleted => hout (by
      rw [hforbidden]; exact Finset.mem_insert_of_mem hmemDeleted)
    rw [data.read_law c hcPole hcDeleted probe, mul_pow]
  rw [hshrink, Finset.sum_congr rfl hread, ← Finset.mul_sum] at hform
  have hgrow : ∑ c ∈ rawCovering \ forbidden, (base.atom c ⬝ᵥ probe) ^ 2
      ≤ ∑ c ∈ covering, (base.atom c ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcoverSup fun c _ _ => sq_nonneg _
  have hgainSq : 0 < data.gain ^ 2 := pow_pos data.gain_pos 2
  have hfloor : (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
      * (probe ⬝ᵥ probe) ≤ data.lift probe ⬝ᵥ data.lift probe := by
    rw [data.length_law probe]
    have hcauchy : ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ probe) ^ 2
        ≤ (∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q)) * (probe ⬝ᵥ probe) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun q _ => ?_
      have hstep := dotProduct_sq_le_mul_self (base.atom q) probe
      have hweight := (base.weight_pos q).le
      calc base.weight q * (base.atom q ⬝ᵥ probe) ^ 2
          ≤ base.weight q * ((base.atom q ⬝ᵥ base.atom q) * (probe ⬝ᵥ probe)) :=
            mul_le_mul_of_nonneg_left hstep hweight
        _ = base.weight q * (base.atom q ⬝ᵥ base.atom q) * (probe ⬝ᵥ probe) := by ring
    linarith
  have hchain : (1 - ∑ q ∈ deleted, base.weight q * (base.atom q ⬝ᵥ base.atom q))
      * (probe ⬝ᵥ probe)
      ≤ data.gain ^ 2 * ∑ c ∈ covering, (base.atom c ⬝ᵥ probe) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_left hgrow hgainSq.le
    linarith [hform, hfloor]
  have hspreadNonneg : 0 ≤ ∑ c ∈ covering, (base.atom c ⬝ᵥ probe) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcapChain : data.gain ^ 2 * ∑ c ∈ covering, (base.atom c ⬝ᵥ probe) ^ 2
      ≤ cap * ∑ c ∈ covering, (base.atom c ⬝ᵥ probe) ^ 2 :=
    mul_le_mul_of_nonneg_right hgain hspreadNonneg
  rw [div_mul_eq_mul_div, div_le_iff₀ hcapPos]
  linarith

end DeletionSet

/-! ## Part 5: the polar set deletion cover

The pole reads as the ZERO atom of the plane restriction, thus the whole set
deletion applies to the plane restriction verbatim.  The plane energy of a label
is its plane shadow, thus the set condition is a statement about the shadows of
the deleted labels alone. -/

section PolarSet

variable {size rank : ℕ}

/-- **THE POLAR SET DELETION COVER.**  Under the previous rank, every design with
an overshooting pole and a named nonempty set of other labels carries `rank - 1`
atoms, NEITHER the pole NOR any named label, that cover the pole's orthogonal
hyperplane with the factor

  `(1 - Σ_T weight q * planeShadowSq) / cap`

at every `cap` above the surviving weight mass.  This is the tool of the ledger
at full strength: the covering set is steered away from a whole SET. -/
theorem exists_polarSetDeletionCover (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (htotal : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1)
    {cap : ℝ} (hcapPos : 0 < cap)
    (hcap : 1 - design.weight pole - ∑ q ∈ deleted, design.weight q < cap) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1
      ∧ pole ∉ covering ∧ (∀ q ∈ deleted, q ∉ covering)
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          ((1 - ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q) / cap)
              * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hpos : 0 < rank := by omega
  have hcardPos : 1 ≤ deleted.card := Finset.card_pos.mpr hnonempty
  have hsize : 3 ≤ size := by omega
  have hpoleNe := atom_ne_zero_of_one_lt_selfDotProduct design hlong
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  set unitNormal : Fin rank → ℝ :=
    (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹ • design.atom pole with hunitNormal
  have hunit : unitNormal ⬝ᵥ unitNormal = 1 := unit_of_ne_zero (design.atom pole) hpoleNe
  set frame := householderFrame hpos unitNormal with hframe
  have horthonormal := householderFrame_orthonormal hpos unitNormal
  have hrootPos : 0 < Real.sqrt (design.atom pole ⬝ᵥ design.atom pole) :=
    Real.sqrt_pos.mpr hleveragePos
  have hrootSq : Real.sqrt (design.atom pole ⬝ᵥ design.atom pole) ^ 2
      = design.atom pole ⬝ᵥ design.atom pole := Real.sq_sqrt hleveragePos.le
  have hnormalRead : ∀ vec : Fin rank → ℝ, vec ⬝ᵥ unitNormal
      = (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹ * (vec ⬝ᵥ design.atom pole) := by
    intro vec
    rw [hunitNormal, dotProduct_smul, smul_eq_mul]
  have hpoleFlat : ∀ index, design.atom pole ⬝ᵥ frame index = 0 := by
    intro index
    have hread := householderFrame_dotProduct_normal hpos hunit index
    rw [hnormalRead (householderFrame hpos unitNormal index)] at hread
    rcases mul_eq_zero.mp hread with hinv | hdot
    · exact absurd hinv (by positivity)
    · rw [dotProduct_comm]
      exact hdot
  set restricted := subspaceRestriction design frame horthonormal with hrestricted
  have hdead : restricted.atom pole = 0 := by
    funext index
    exact hpoleFlat index
  have hweightRead : ∀ label : Fin size, restricted.weight label = design.weight label :=
    fun _ => rfl
  -- the plane energy of a label is its plane shadow
  have hshadow : ∀ label : Fin size,
      restricted.atom label ⬝ᵥ restricted.atom label = planeShadowSq design pole label := by
    intro label
    have hexpand : restricted.atom label ⬝ᵥ restricted.atom label
        = ∑ index, (design.atom label ⬝ᵥ householderFrame hpos unitNormal index)
            * (design.atom label ⬝ᵥ householderFrame hpos unitNormal index) := rfl
    rw [hexpand, sum_householderFrame_read_mul hpos hunit (design.atom label) (design.atom label),
      hnormalRead (design.atom label), planeShadowSq]
    have hsquare : (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹
          * (design.atom label ⬝ᵥ design.atom pole)
        * ((Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹
          * (design.atom label ⬝ᵥ design.atom pole))
        = (design.atom label ⬝ᵥ design.atom pole) ^ 2
          / (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole)) ^ 2 := by
      field_simp
    rw [hsquare, hrootSq]
  have htotalRestricted : ∑ q ∈ deleted,
      restricted.weight q * (restricted.atom q ⬝ᵥ restricted.atom q) < 1 := by
    rw [Finset.sum_congr rfl fun q _ => by rw [hweightRead q, hshadow q]]
    exact htotal
  have hcapRestricted : 1 - restricted.weight pole - ∑ q ∈ deleted, restricted.weight q < cap := by
    rw [hweightRead pole, Finset.sum_congr rfl fun q _ => hweightRead q]
    exact hcap
  have hroomRestricted : (rank - 1) + 1 + deleted.card ≤ size := by omega
  obtain ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, hcover⟩ :=
    exists_setDeletionCover hpredecessor hsize restricted hdead hnonempty hpole hroomRestricted
      htotalRestricted hcapPos hcapRestricted
  refine ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, fun probe hprobe => ?_⟩
  have hprobeNormal : probe ⬝ᵥ unitNormal = 0 := by
    rw [hnormalRead probe, hprobe, mul_zero]
  set planeProbe : Fin (rank - 1) → ℝ := fun index => probe ⬝ᵥ frame index with hplaneProbe
  have hplaneLength : planeProbe ⬝ᵥ planeProbe = probe ⬝ᵥ probe := by
    have hexpand : planeProbe ⬝ᵥ planeProbe
        = ∑ index, (probe ⬝ᵥ householderFrame hpos unitNormal index)
            * (probe ⬝ᵥ householderFrame hpos unitNormal index) := rfl
    rw [hexpand, sum_householderFrame_read_mul hpos hunit probe probe, hprobeNormal]
    ring
  have hplaneRead : ∀ label : Fin size,
      restricted.atom label ⬝ᵥ planeProbe = design.atom label ⬝ᵥ probe := by
    intro label
    have hexpand : restricted.atom label ⬝ᵥ planeProbe
        = ∑ index, (design.atom label ⬝ᵥ householderFrame hpos unitNormal index)
            * (probe ⬝ᵥ householderFrame hpos unitNormal index) := rfl
    rw [hexpand, sum_householderFrame_read_mul hpos hunit (design.atom label) probe,
      hprobeNormal, mul_zero, sub_zero]
  have hstep := hcover planeProbe
  rw [hplaneLength, Finset.sum_congr rfl fun q _ => by rw [hweightRead q, hshadow q]] at hstep
  calc ((1 - ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q) / cap)
        * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ covering, (restricted.atom label ⬝ᵥ planeProbe) ^ 2 := hstep
    _ = ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 :=
        Finset.sum_congr rfl fun label _ => by rw [hplaneRead label]

/-! ## Part 6: the deletion debt, the set margin, and the sharp cover

The whole set deletion is priced by ONE number: the DEBT of the deleted set.
The cover beats the identity exactly when the debt stays below the pole's own
weight, and the margin it achieves is any value below the sharp one. -/

/-- **THE DELETION DEBT OF A SET.**  The weighted plane shadows of the deleted
labels, each measured against one unit. -/
noncomputable def planeShadowDebt (design : WeightedDesign size rank) (pole : Fin size)
    (deleted : Finset (Fin size)) : ℝ :=
  ∑ q ∈ deleted, design.weight q * (planeShadowSq design pole q - 1)

/-- The debt is the weighted shadow total minus the weight of the deleted set. -/
theorem planeShadowDebt_eq (design : WeightedDesign size rank) (pole : Fin size)
    (deleted : Finset (Fin size)) :
    planeShadowDebt design pole deleted
      = (∑ q ∈ deleted, design.weight q * planeShadowSq design pole q)
        - ∑ q ∈ deleted, design.weight q := by
  rw [planeShadowDebt, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- **THE SHARP MARGIN OF A SET DELETION.** -/
noncomputable def setDeletionMargin (design : WeightedDesign size rank) (pole : Fin size)
    (deleted : Finset (Fin size)) : ℝ :=
  (1 - ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q)
      / (1 - design.weight pole - ∑ q ∈ deleted, design.weight q) - 1

/-- **A DELETABLE SET NEVER SATURATES THE PLANE.**  The trace condition of the
set deletion follows from the debt condition alone, because the pole and the
deleted labels never carry the whole weight. -/
theorem setDeletion_total_lt_one (design : WeightedDesign size rank) {pole : Fin size}
    {deleted : Finset (Fin size)} (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1 := by
  have hmass := weight_insert_le_one design hpole
  rw [planeShadowDebt_eq] at hdeletable
  linarith

/-- **THE SURVIVING MASS IS POSITIVE WHEN A SURVIVOR EXISTS.** -/
theorem setDeletion_free_mass_pos (design : WeightedDesign size rank)
    {pole : Fin size} {deleted : Finset (Fin size)} (hpole : pole ∉ deleted)
    (hroom : deleted.card + 1 < size) :
    0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q := by
  classical
  have hsub : insert pole deleted ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr fun heq => ?_
    have hcard : (insert pole deleted).card = deleted.card + 1 :=
      Finset.card_insert_of_notMem hpole
    have huniv : (Finset.univ : Finset (Fin size)).card = size := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [heq, huniv] at hcard
    omega
  obtain ⟨other, _hotherUniv, hotherNot⟩ := Finset.exists_of_ssubset hsub
  have hsplit : ∑ q ∈ insert pole deleted, design.weight q
      = design.weight pole + ∑ q ∈ deleted, design.weight q := Finset.sum_insert hpole
  have hstep : ∑ q ∈ insert other (insert pole deleted), design.weight q
      ≤ ∑ q, design.weight q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun q _ _ => (design.weight_pos q).le
  have hinsert : ∑ q ∈ insert other (insert pole deleted), design.weight q
      = design.weight other + ∑ q ∈ insert pole deleted, design.weight q :=
    Finset.sum_insert hotherNot
  rw [design.weight_sum_one] at hstep
  rw [hinsert, hsplit] at hstep
  linarith [design.weight_pos other]

/-- **THE SET MARGIN IS POSITIVE EXACTLY AT A DELETABLE SET.** -/
theorem setDeletionMargin_pos (design : WeightedDesign size rank) {pole : Fin size}
    {deleted : Finset (Fin size)}
    (hfree : 0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    0 < setDeletionMargin design pole deleted := by
  rw [planeShadowDebt_eq] at hdeletable
  rw [setDeletionMargin, sub_pos, lt_div_iff₀ hfree, one_mul]
  linarith

/-- **THE POLAR SET DELETION COVER, AT EVERY MARGIN BELOW THE SHARP ONE.**  The
cap of the set deletion is chosen by the margin, thus the caller names the margin
and never sees the shares. -/
theorem exists_polarSetDeletionCover_margin (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    {margin : ℝ} (hmarginPos : 0 < margin)
    (hmarginLt : margin < setDeletionMargin design pole deleted) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1
      ∧ pole ∉ covering ∧ (∀ q ∈ deleted, q ∉ covering)
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have htotal : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q < 1 :=
    setDeletion_total_lt_one design hpole hdeletable
  have hmass := weight_insert_le_one design hpole
  have hcardPos : 1 ≤ deleted.card := Finset.card_pos.mpr hnonempty
  have hsize : 3 ≤ size := by omega
  -- a surviving label exists, thus the surviving mass is positive
  have hfree : 0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q :=
    setDeletion_free_mass_pos design hpole (by omega)
  set cap : ℝ := (1 - ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q) / (1 + margin)
    with hcapDef
  have hnumPos : (0 : ℝ)
      < 1 - ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q := by linarith
  have hmarginDen : (0 : ℝ) < 1 + margin := by linarith
  have hcapPos : 0 < cap := by rw [hcapDef]; exact div_pos hnumPos hmarginDen
  have hcapGt : 1 - design.weight pole - ∑ q ∈ deleted, design.weight q < cap := by
    rw [hcapDef, lt_div_iff₀ hmarginDen]
    rw [setDeletionMargin, lt_sub_iff_add_lt, lt_div_iff₀ hfree] at hmarginLt
    nlinarith [hmarginLt]
  obtain ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, hcover⟩ :=
    exists_polarSetDeletionCover hrank hpredecessor design hlong hnonempty hpole hroom htotal
      hcapPos hcapGt
  refine ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, fun probe hprobe => ?_⟩
  have hfactor : (1 - ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q) / cap
      = 1 + margin := by
    rw [hcapDef, div_div_eq_mul_div, div_eq_iff (ne_of_gt hnumPos)]
    ring
  have hstep := hcover probe hprobe
  rwa [hfactor] at hstep

/-! ## Part 7: what the set deletion kills

The producer, the kill and the forward reading are the set forms of the single
deletion laws.  Each one is strictly stronger, because the covering set is
steered away from a whole set at once. -/

/-- **THE STRICT DOMINATOR THE SET DELETION PRODUCES.**  When a set is deletable
and every SURVIVOR stays below the tilt cap, the pole together with the deleted
cover beats the identity strictly. -/
theorem exists_dominating_of_deletableSetTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hgapPos : (0 : ℝ) < (design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1) := by nlinarith [hlong, hleveragePos]
  have hsharpPos : 0 < setDeletionMargin design pole deleted := by
    by_contra hnonpos
    rw [not_lt] at hnonpos
    have hleft : 0 ≤ ((rank : ℝ) - 1) * tiltCap := by
      have hrankCast : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
      have hcapNonneg : 0 ≤ tiltCap := by
        have hchoice : ∃ label : Fin size, label ≠ pole ∧ label ∉ deleted := by
          by_contra hnone
          have hall : ∀ label : Fin size, label = pole ∨ label ∈ deleted := by
            intro label
            by_contra hlabel
            exact hnone ⟨label, fun heq => hlabel (Or.inl heq),
              fun hmem => hlabel (Or.inr hmem)⟩
          have hcover : (Finset.univ : Finset (Fin size)) ⊆ insert pole deleted := by
            intro label _
            rcases hall label with heq | hmem
            · rw [heq]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem hmem
          have hcardBound : (Finset.univ : Finset (Fin size)).card ≤ deleted.card + 1 := by
            calc (Finset.univ : Finset (Fin size)).card ≤ (insert pole deleted).card :=
                  Finset.card_le_card hcover
              _ = deleted.card + 1 := Finset.card_insert_of_notMem hpole
          rw [Finset.card_univ, Fintype.card_fin] at hcardBound
          omega
        obtain ⟨label, hlabelPole, hlabelNot⟩ := hchoice
        exact le_trans (sq_nonneg _) (htilt label hlabelPole hlabelNot)
      nlinarith [hrankCast, hcapNonneg]
    nlinarith [hbudget, hgapPos, hnonpos, hleft]
  -- one maximum picks a margin strictly below the sharp one that still beats the budget
  set sharp : ℝ := setDeletionMargin design pole deleted with hsharp
  set need : ℝ := ((rank : ℝ) - 1) * tiltCap
    / ((design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1)) with hneed
  have hneedLt : need < sharp := by
    rw [hneed, div_lt_iff₀ hgapPos]
    have hshape : sharp * ((design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1))
        = sharp * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by ring
    rw [hshape]
    exact hbudget
  set margin : ℝ := (max need 0 + sharp) / 2 with hmarginDef
  have hmaxLt : max need 0 < sharp := max_lt hneedLt hsharpPos
  have hmaxNonneg : 0 ≤ max need 0 := le_max_right _ _
  have hmarginPos : 0 < margin := by rw [hmarginDef]; linarith
  have hmarginLt : margin < sharp := by rw [hmarginDef]; linarith
  have hmarginNeed : need < margin := by
    have hle : need ≤ max need 0 := le_max_left _ _
    rw [hmarginDef]; linarith
  have hbudgetMargin : ((rank : ℝ) - 1) * tiltCap
      < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    rw [hneed, div_lt_iff₀ hgapPos] at hmarginNeed
    nlinarith [hmarginNeed]
  obtain ⟨covering, hcard, hpoleNotMem, hdeletedNotMem, hcover⟩ :=
    exists_polarSetDeletionCover_margin hrank hpredecessor design hlong hnonempty hpole hroom
      hdeletable hmarginPos hmarginLt
  -- the covering avoids the pole and every deleted label, thus its tilt is capped
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
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by linarith
  have hposDef := posDef_insert_of_polarCover design hpoleNotMem hlong hmarginPos hcover htiltStrict
  refine exists_card_eq_posDef design ?_ hposDef
  rw [Finset.card_insert_of_notMem hpoleNotMem, hcard]
  omega

/-- **THE SET DELETION KILL.**  No tie carries a deletable set whose survivors
are all below the tilt budget. -/
theorem not_isTie_of_deletableSetTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : ((rank : ℝ) - 1) * tiltCap
      < setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ := exists_dominating_of_deletableSetTilt hrank hpredecessor
    design hlong hnonempty hpole hroom hdeletable htilt hbudget
  exact htie.2 selected hcard hposDef

/-- **THE FORWARD READING, SHARP.**  Every tie carries, at every overshooting
pole and every DELETABLE set, a SURVIVOR whose squared pairing against the pole
already spends the whole set deletion budget. -/
theorem exists_heavy_survivor_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    ∃ label : Fin size, label ≠ pole ∧ label ∉ deleted
      ∧ setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  classical
  by_contra hcontra
  have hstrict : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2
        < setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    intro label hlabelPole hlabelNot
    by_contra hbig
    exact hcontra ⟨label, hlabelPole, hlabelNot, not_lt.mp hbig⟩
  -- the surviving labels are a nonempty finite set, thus the tilt has a maximum
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
  refine not_isTie_of_deletableSetTilt hrank hpredecessor design hlong hnonempty hpole hroom
    hdeletable (tiltCap := (design.atom top ⬝ᵥ design.atom pole) ^ 2)
    (fun label hlabelPole hlabelNot => ?_) (hstrict top htopPole htopDeleted) htie
  exact htopMax label (Finset.mem_sdiff.mpr ⟨Finset.mem_univ label, fun hmem => by
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hlabelPole heq
    · exact hlabelNot hmem'⟩)

/-! ## Part 8: the debt ledger

The deletion debt of the WHOLE non-pole set is an exact identity, thus the debt
of a deleted set and the debt of its survivors add up to a known number.  That
turns the deletion condition into a statement about the SURVIVORS, and it prices
exactly how far the iteration can go. -/

/-- **THE DEBT OF THE WHOLE NON-POLE SET, EXACTLY.**  It is the plane shadow mass
minus the free weight, thus it depends on the design only through the rank and
the pole's own weight. -/
theorem sum_weight_planeShadowDebt (design : WeightedDesign size rank) (pole : Fin size)
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    planeShadowDebt design pole (Finset.univ.erase pole)
      = (rank : ℝ) - 2 + design.weight pole := by
  classical
  have hmass : ∑ c ∈ Finset.univ.erase pole, design.weight c = 1 - design.weight pole := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ pole), design.weight_sum_one]
  rw [planeShadowDebt_eq, sum_weight_planeShadowSq_erase design pole hpole, hmass]
  ring

/-- **THE DEBT SPLITS ACROSS A DELETED SET AND ITS SURVIVORS.** -/
theorem planeShadowDebt_add_survivors (design : WeightedDesign size rank) (pole : Fin size)
    {deleted : Finset (Fin size)} (hsub : deleted ⊆ Finset.univ.erase pole) :
    planeShadowDebt design pole (Finset.univ.erase pole \ deleted)
        + planeShadowDebt design pole deleted
      = planeShadowDebt design pole (Finset.univ.erase pole) := by
  classical
  rw [planeShadowDebt, planeShadowDebt, planeShadowDebt]
  exact Finset.sum_sdiff hsub

/-- **A SET IS DELETABLE EXACTLY WHEN ITS SURVIVORS CARRY DEBT ABOVE `rank - 2`.**
This is the sharpest form of the whole tool: the deletion never mentions the
deleted labels, only what stays. -/
theorem deletableSet_iff_survivor_debt (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hsub : deleted ⊆ Finset.univ.erase pole) :
    planeShadowDebt design pole deleted < design.weight pole
      ↔ (rank : ℝ) - 2 < planeShadowDebt design pole (Finset.univ.erase pole \ deleted) := by
  have hsplit := planeShadowDebt_add_survivors design pole hsub
  rw [sum_weight_planeShadowDebt design pole hpole] at hsplit
  constructor
  · intro hlt; linarith
  · intro hlt; linarith

/-- **THE WHOLE NON-POLE SET IS NEVER DELETABLE.**  A design of rank at least two
always keeps survivors, because the debt of everything already reaches the
pole's own weight. -/
theorem not_deletableSet_erase_pole (design : WeightedDesign size rank) {pole : Fin size}
    (hrank : 2 ≤ rank) (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) :
    ¬ (planeShadowDebt design pole (Finset.univ.erase pole) < design.weight pole) := by
  rw [sum_weight_planeShadowDebt design pole hpole, not_lt]
  have hcast : (2 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  linarith

/-- **HOW MANY SURVIVORS A DELETION MUST LEAVE.**  When every non-pole label
carries debt at most `debtCap`, a deletable set leaves at least `(rank - 2)/debtCap`
survivors.  This is the exact price of the iteration: a small per-label debt
forces a large survivor set, thus a SMALL deleted set. -/
theorem card_survivor_lower_bound_of_deletable (design : WeightedDesign size rank)
    {pole : Fin size} (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hsub : deleted ⊆ Finset.univ.erase pole)
    {debtCap : ℝ}
    (hcap : ∀ c : Fin size, c ≠ pole → design.weight c * (planeShadowSq design pole c - 1)
      ≤ debtCap)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    (rank : ℝ) - 2 < ((Finset.univ.erase pole \ deleted).card : ℝ) * debtCap := by
  classical
  have hsurvivor := (deletableSet_iff_survivor_debt design hpole hsub).mp hdeletable
  have hbound : planeShadowDebt design pole (Finset.univ.erase pole \ deleted)
      ≤ ((Finset.univ.erase pole \ deleted).card : ℝ) * debtCap := by
    rw [planeShadowDebt]
    calc ∑ c ∈ Finset.univ.erase pole \ deleted,
          design.weight c * (planeShadowSq design pole c - 1)
        ≤ ∑ _c ∈ Finset.univ.erase pole \ deleted, debtCap := by
          refine Finset.sum_le_sum fun c hc => ?_
          exact hcap c (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hc).1)
      _ = ((Finset.univ.erase pole \ deleted).card : ℝ) * debtCap := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- **A SET OF SHORT SHADOWS IS ALWAYS DELETABLE.**  No hypothesis beyond the
positivity of the weights is spent. -/
theorem deletableSet_of_planeShadowSq_le_one (design : WeightedDesign size rank)
    (pole : Fin size) {deleted : Finset (Fin size)}
    (hshadow : ∀ q ∈ deleted, planeShadowSq design pole q ≤ 1) :
    planeShadowDebt design pole deleted < design.weight pole := by
  have hnonpos : planeShadowDebt design pole deleted ≤ 0 := by
    rw [planeShadowDebt]
    refine Finset.sum_nonpos fun q hq => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos q).le (by linarith [hshadow q hq])
  linarith [design.weight_pos pole]

/-- **A SET OF HEAVY TILT IS ALWAYS DELETABLE.**  The set form of the pairing the
selection needs: the labels a covering set must be steered AWAY from are exactly
the labels the deletion is permitted to remove.  The only input is the leverage
cap of the design. -/
theorem deletableSet_of_tilt_heavy (design : WeightedDesign size rank) {pole : Fin size}
    (hpole : 0 < design.atom pole ⬝ᵥ design.atom pole) {deleted : Finset (Fin size)}
    (hheavy : (design.atom pole ⬝ᵥ design.atom pole)
        * ((deleted.card : ℝ) - (∑ q ∈ deleted, design.weight q) - design.weight pole)
      < ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ design.atom pole) ^ 2) :
    planeShadowDebt design pole deleted < design.weight pole := by
  classical
  have hcapSum : ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ design.atom q)
      ≤ (deleted.card : ℝ) := by
    calc ∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ design.atom q)
        ≤ ∑ _q ∈ deleted, (1 : ℝ) :=
          Finset.sum_le_sum fun q _ => weight_mul_selfDotProduct_le_one design q
      _ = (deleted.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hexpand : ∑ q ∈ deleted, design.weight q * planeShadowSq design pole q
      = (∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ design.atom q))
        - (∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ design.atom pole) ^ 2)
          / (design.atom pole ⬝ᵥ design.atom pole) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [planeShadowSq]; ring
  have hstep : (deleted.card : ℝ) - (∑ q ∈ deleted, design.weight q) - design.weight pole
      < (∑ q ∈ deleted, design.weight q * (design.atom q ⬝ᵥ design.atom pole) ^ 2)
        / (design.atom pole ⬝ᵥ design.atom pole) := by
    rw [lt_div_iff₀ hpole, mul_comm]
    exact hheavy
  rw [planeShadowDebt_eq, hexpand]
  linarith

/-! ## Part 9: the residual, narrowed a third time

The set deletion law is a theorem at every tie, thus its contrapositive is a FREE
fact that a tie hands to the residual.  Adding it makes the residual strictly
weaker while every consumer still runs on it. -/

/-- **THE FREE SET DELETION FACT.**  What a tie supplies at an overshooting pole:
at every deletable SET some survivor is already heavy. -/
def PolarSetDeletionHeavy (design : WeightedDesign size rank) (pole : Fin size) : Prop :=
  ∀ deleted : Finset (Fin size), deleted.Nonempty → pole ∉ deleted →
    rank + deleted.card ≤ size →
    planeShadowDebt design pole deleted < design.weight pole →
      ∃ label : Fin size, label ≠ pole ∧ label ∉ deleted
        ∧ setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)
            ≤ ((rank : ℝ) - 1) * (design.atom label ⬝ᵥ design.atom pole) ^ 2

/-- **THE SET DELETION FACT IS FREE AT EVERY TIE.** -/
theorem polarSetDeletionHeavy_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    PolarSetDeletionHeavy design pole :=
  fun _deleted hnonempty hpole hroom hdeletable =>
    exists_heavy_survivor_of_isTie hrank hpredecessor design htie hlong hnonempty hpole hroom
      hdeletable

/-- **THE THRICE-NARROWED TILT RESIDUAL.**  `Gtz.PolarTiltSelectionDeletion` with
the set deletion fact handed to it as well.  It is weaker than every shipped
residual, and every consumer of them runs on this one. -/
def PolarTiltSelectionSetDeletion (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    PolarSaturationBudget design pole →
    PolarDeletionHeavy design pole →
    PolarSetDeletionHeavy design pole →
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

/-- The thrice-narrowed residual is weaker than the twice-narrowed one. -/
theorem polarTiltSelectionSetDeletion_of_polarTiltSelectionDeletion
    (htilt : PolarTiltSelectionDeletion size rank) :
    PolarTiltSelectionSetDeletion size rank :=
  fun design pole covering margin hprimitive htie hlong hbudget hheavy _hset hmargin hcard
    hnotMem hcover =>
    htilt design pole covering margin hprimitive htie hlong hbudget hheavy hmargin hcard hnotMem
      hcover

/-- The thrice-narrowed residual is weaker than the once-narrowed one. -/
theorem polarTiltSelectionSetDeletion_of_polarTiltSelectionUnsaturated
    (htilt : PolarTiltSelectionUnsaturated size rank) :
    PolarTiltSelectionSetDeletion size rank :=
  polarTiltSelectionSetDeletion_of_polarTiltSelectionDeletion
    (polarTiltSelectionDeletion_of_polarTiltSelectionUnsaturated htilt)

/-- The thrice-narrowed residual is weaker than the shipped one. -/
theorem polarTiltSelectionSetDeletion_of_polarTiltSelection
    (htilt : PolarTiltSelection size rank) : PolarTiltSelectionSetDeletion size rank :=
  polarTiltSelectionSetDeletion_of_polarTiltSelectionDeletion
    (polarTiltSelectionDeletion_of_polarTiltSelection htilt)

/-- **THE HINGE FROM THE THRICE-NARROWED RESIDUAL.**  All three bundles are
theorems at a tie, thus the third narrowing costs nothing downstream either. -/
theorem hingeHoldsAtSize_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : HingeHoldsAtSize size rank := by
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
      hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### Every consumer of the shipped residual, on the thrice-narrowed one -/

/-- Arm (i). -/
theorem stressFreeArmAt_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : StressFreeArmAt size rank :=
  fun design _hfree htie =>
    hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt design htie

/-- Arm (ii). -/
theorem balancedArmAt_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt design htie

/-- Arm (iii). -/
theorem degenerateArmAt_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt design htie

/-- The partial-support sub-arm. -/
theorem balancedPartialSupportArmAt_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt design htie

/-- The full-support sub-arm. -/
theorem balancedFullSupportArmAt_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt design htie

/-- The repaired degenerate cover. -/
theorem degenerateHyperplaneCover_of_polarTiltSetDeletion (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) : DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd
    (hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE COLLAPSE, ON THE THRICE-NARROWED RESIDUAL.** -/
theorem polarTiltSetDeletion_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ size)
    (htilt : PolarTiltSelectionSetDeletion size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ BalancedFullSupportArmAt size rank ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTiltSetDeletion hrank hpredecessor hroom htilt,
    stressFreeArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt,
    balancedArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt,
    degenerateArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt,
    balancedPartialSupportArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt,
    balancedFullSupportArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt,
    degenerateHyperplaneCover_of_polarTiltSetDeletion hrank hpredecessor hroom htilt⟩

/-! ### The forced cover: when the deletion leaves exactly `rank - 1` survivors

A deleted set of `size - rank` labels leaves exactly `rank - 1` survivors, thus
the selection of the previous rank has NO CHOICE: the covering set IS the
surviving set.  On that branch the residual is removed outright. -/

/-- **THE FORCED COVER.**  A deletable set of `size - rank` labels leaves exactly
`rank - 1` survivors, and those survivors ARE the cover. -/
theorem exists_forcedCover_of_deleteComplement (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hcard : deleted.card + rank = size)
    (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    {margin : ℝ} (hmarginPos : 0 < margin)
    (hmarginLt : margin < setDeletionMargin design pole deleted) :
    (Finset.univ \ insert pole deleted).card = rank - 1
      ∧ pole ∉ Finset.univ \ insert pole deleted
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ Finset.univ \ insert pole deleted,
                (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hforbiddenCard : (insert pole deleted).card = deleted.card + 1 :=
    Finset.card_insert_of_notMem hpole
  have hsurvivorCard : (Finset.univ \ insert pole deleted).card = rank - 1 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hforbiddenCard]
    omega
  have hpoleOut : pole ∉ Finset.univ \ insert pole deleted := by
    intro hmem
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_self _ _)
  obtain ⟨covering, hcoverCard, hcoverPole, hcoverDeleted, hcover⟩ :=
    exists_polarSetDeletionCover_margin hrank hpredecessor design hlong hnonempty hpole
      (by omega) hdeletable hmarginPos hmarginLt
  have hsubset : covering ⊆ Finset.univ \ insert pole deleted := by
    intro label hlabel
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ label, fun hmem => ?_⟩
    rcases Finset.mem_insert.mp hmem with heq | hmemDeleted
    · exact hcoverPole (heq ▸ hlabel)
    · exact hcoverDeleted label hmemDeleted hlabel
  have hforced : covering = Finset.univ \ insert pole deleted :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hsurvivorCard, hcoverCard])
  refine ⟨hsurvivorCard, hpoleOut, fun probe hprobe => ?_⟩
  rw [← hforced]
  exact hcover probe hprobe

/-- **THE FORCED COVER KILL.**  A tie carries no deletable set of `size - rank`
labels whose survivors together stay below the set deletion budget.  No
selection is left in this statement: the survivors are NAMED. -/
theorem not_isTie_of_forcedCover (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hcard : deleted.card + rank = size)
    (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    (htilt : ∑ label ∈ Finset.univ \ insert pole deleted,
          (design.atom label ⬝ᵥ design.atom pole) ^ 2
        < setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design := by
  classical
  intro htie
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hgapPos : (0 : ℝ) < (design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1) := by nlinarith [hlong, hleveragePos]
  have hfree : 0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q :=
    setDeletion_free_mass_pos design hpole (by omega)
  have hsharpPos : 0 < setDeletionMargin design pole deleted :=
    setDeletionMargin_pos design hfree hdeletable
  have hshape : setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      = setDeletionMargin design pole deleted
        * ((design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) := by ring
  rw [hshape] at htilt
  obtain ⟨margin, hmarginPos, hmarginLt, hmarginBudget⟩ :=
    exists_margin_below_sharp hsharpPos hgapPos htilt
  obtain ⟨hcardSurvivor, hpoleOut, hcover⟩ := exists_forcedCover_of_deleteComplement hrank
    hpredecessor design hlong hcard hnonempty hpole hdeletable hmarginPos hmarginLt
  have htiltStrict : ∑ label ∈ Finset.univ \ insert pole deleted,
        (design.atom label ⬝ᵥ design.atom pole) ^ 2
      < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by
    have hstep : margin * ((design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1))
        = margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1) := by ring
    rw [← hstep]
    exact hmarginBudget
  have hposDef := posDef_insert_of_polarCover design hpoleOut hlong hmarginPos hcover htiltStrict
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hpoleOut, hcardSurvivor]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- **THE FORCED COVER, READ FORWARDS.**  At every tie, every deletable set of
`size - rank` labels leaves survivors that TOGETHER already spend the whole set
deletion budget. -/
theorem exists_heavy_forcedCover_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hcard : deleted.card + rank = size)
    (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ ∑ label ∈ Finset.univ \ insert pole deleted,
          (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  by_contra hsmall
  rw [not_le] at hsmall
  exact not_isTie_of_forcedCover hrank hpredecessor design hlong hcard hnonempty hpole hdeletable
    hsmall htie

/-- **THE ORTHOGONAL SURVIVOR KILL.**  When the WHOLE tilt of the pole sits on a
deletable set, the survivors are orthogonal to the pole and the tilt budget is
spent on nothing.  This is the set form of the concentrated tilt kill, and it
needs no computation of any plane shadow. -/
theorem not_isTie_of_orthogonalSurvivors (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : rank + deleted.card ≤ size)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    (horthogonal : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      design.atom label ⬝ᵥ design.atom pole = 0) :
    ¬ IsTie design := by
  have hleveragePos : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hfree : 0 < 1 - design.weight pole - ∑ q ∈ deleted, design.weight q :=
    setDeletion_free_mass_pos design hpole (by omega)
  have hsharpPos : 0 < setDeletionMargin design pole deleted :=
    setDeletionMargin_pos design hfree hdeletable
  refine not_isTie_of_deletableSetTilt hrank hpredecessor design hlong hnonempty hpole hroom
    hdeletable (tiltCap := 0) (fun label hlabelPole hlabelNot => ?_) ?_
  · rw [horthogonal label hlabelPole hlabelNot]
    norm_num
  · rw [mul_zero]
    exact mul_pos (mul_pos hsharpPos hleveragePos) (by linarith)

/-! ### The registry obligations, on the thrice-narrowed residual -/

/-- The threshold cell obligation of the registry. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTiltSetDeletion
    (htilt : ∀ rank : ℕ, 4 ≤ rank →
      PolarTiltSelectionSetDeletion (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  have hroom : rank + 1 ≤ rank * (rank + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (rank + 1) * 2 ≤ (rank + 1) * rank := Nat.mul_le_mul_left _ (by omega)
      _ = rank * (rank + 1) := Nat.mul_comm _ _
  exact hingeHoldsAtSize_of_polarTiltSetDeletion (by omega) hpredecessor hroom (htilt rank hrank)
    design htie

/-- The sub-threshold band obligation of the registry. -/
theorem subThresholdBandHinge_of_polarTiltSetDeletion
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelectionSetDeletion size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTiltSetDeletion (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh) design htie

/-- The whole sharp window, from one thrice-narrowed residual per cell. -/
theorem sharpWindowHinge_of_polarTiltSetDeletion
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelectionSetDeletion size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTiltSetDeletion (by omega) hpredecessor (by omega)
    (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTiltSetDeletion (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionSetDeletion (thresholdSize rank) rank) :
    ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTiltSetDeletion (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionSetDeletion (thresholdSize rank) rank) :
    ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTiltSetDeletion (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hroom : rank + 1 ≤ thresholdSize rank)
    (htilt : PolarTiltSelectionSetDeletion (thresholdSize rank) rank) :
    ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTiltSetDeletion hrank hpredecessor hroom htilt

end PolarSet

/-! ## Part 10: rank three, the forced pair, and the calibration

At the deciding cell of rank three the covering set has card TWO and there are
five labels other than the pole.  Deleting THREE of them leaves exactly two
survivors, thus the selection of the previous rank has NO CHOICE at all: the
covering pair IS the surviving pair. -/

section RankThree

/-- **THE FORCED PAIR AT THE DECIDING CELL OF RANK THREE.**  A deletable set of
three labels leaves exactly two survivors, and those two ARE the covering pair.
The selection residual is removed outright on this branch. -/
theorem exists_forcedPair_of_deleteThree (design : WeightedDesign 6 3) {pole : Fin 6}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin 6)} (hcard : deleted.card = 3) (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    {margin : ℝ} (hmarginPos : 0 < margin)
    (hmarginLt : margin < setDeletionMargin design pole deleted) :
    (Finset.univ \ insert pole deleted).card = 2
      ∧ pole ∉ Finset.univ \ insert pole deleted
      ∧ ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ Finset.univ \ insert pole deleted,
                (design.atom label ⬝ᵥ probe) ^ 2 :=
  exists_forcedCover_of_deleteComplement (rank := 3) (by norm_num) gtz_rank_two design hlong
    (by omega) (Finset.card_pos.mp (by omega)) hpole hdeletable hmarginPos hmarginLt

/-- **THE FORCED PAIR KILL.**  At the deciding cell of rank three, a tie carries
no deletable set of three labels whose two survivors together stay below the set
deletion budget. -/
theorem not_isTie_of_forcedPair_six_three (design : WeightedDesign 6 3) {pole : Fin 6}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin 6)} (hcard : deleted.card = 3) (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    (htilt : ∑ label ∈ Finset.univ \ insert pole deleted,
          (design.atom label ⬝ᵥ design.atom pole) ^ 2
        < setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design :=
  not_isTie_of_forcedCover (rank := 3) (by norm_num) gtz_rank_two design hlong (by omega)
    (Finset.card_pos.mp (by omega)) hpole hdeletable htilt

/-- The set deletion kill at rank three, with the previous rank discharged. -/
theorem not_isTie_of_deletableSetTilt_three {size : ℕ} (design : WeightedDesign size 3)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin size)} (hnonempty : deleted.Nonempty) (hpole : pole ∉ deleted)
    (hroom : 3 + deleted.card ≤ size)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole)
    {tiltCap : ℝ}
    (htilt : ∀ label : Fin size, label ≠ pole → label ∉ deleted →
      (design.atom label ⬝ᵥ design.atom pole) ^ 2 ≤ tiltCap)
    (hbudget : 2 * tiltCap
      < setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    ¬ IsTie design :=
  not_isTie_of_deletableSetTilt (by norm_num) gtz_rank_two design hlong hnonempty hpole hroom
    hdeletable htilt (by push_cast; linarith)

/-- **THE DECIDING CELL OF RANK THREE FROM THE THRICE-NARROWED RESIDUAL ALONE.** -/
theorem hingeHoldsAtSize_six_three_of_polarTiltSetDeletion
    (htilt : PolarTiltSelectionSetDeletion 6 3) : HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTiltSetDeletion (by norm_num) gtz_rank_two (by norm_num) htilt

/-- The three rank-three arms from the thrice-narrowed residual. -/
theorem thresholdArms_rank_three_of_polarTiltSetDeletion
    (htilt : PolarTiltSelectionSetDeletion 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 := by
  have hhinge := hingeHoldsAtSize_six_three_of_polarTiltSetDeletion htilt
  exact ⟨fun design _hfree htie => hhinge design htie,
    fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie,
    fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie⟩

/-- **THE DECIDING CELL, FROM THE THRICE-NARROWED RESIDUAL ALONE.** -/
theorem gtzWeighted_six_three_of_polarTiltSetDeletion
    (htilt : PolarTiltSelectionSetDeletion 6 3) : GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltSetDeletion htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **ALL OF RANK THREE, FROM THE THRICE-NARROWED RESIDUAL ALONE.** -/
theorem gtzWeightedAll_three_of_polarTiltSetDeletion
    (htilt : PolarTiltSelectionSetDeletion 6 3) : GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTiltSetDeletion htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- **THE THRICE-NARROWED RESIDUAL IS FALSE AT `(5,3)`.**  The calibration
transports through the third narrowing too, because the set deletion fact is free
at every tie of five labels of rank three. -/
theorem not_polarTiltSelectionSetDeletion_five_three :
    ¬ PolarTiltSelectionSetDeletion 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTiltSetDeletion (by norm_num) gtz_rank_two (by norm_num) htilt)

/-- **THE GUARDRAIL.**  The `(6,3)` tie in the tree is not primitive, thus it does
not touch the thrice-narrowed residual, and the last-stage Prop stays refuted. -/
theorem sixSplitDiamondDesign_spares_polarTiltSetDeletion :
    ¬ RankSuccShrinks 6 3 ∧ IsTie sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ PolarTiltSelectionSetDeletion 5 3 :=
  ⟨not_rankSuccShrinks_six_three, sixSplitDiamondDesign_isTie,
    not_isPrimitiveDesign_sixSplitDiamondDesign, not_polarTiltSelectionSetDeletion_five_three⟩

/-- **THE FORCED PAIR, READ FORWARDS.**  At every tie of the deciding cell of
rank three, every deletable set of three labels leaves a PAIR of survivors that
together already spend the whole set deletion budget.  This is the sharpest
unconditional law the deletion supplies, because the two survivors are NAMED: no
selection is left. -/
theorem exists_heavy_survivor_pair_of_isTie_six_three (design : WeightedDesign 6 3)
    (htie : IsTie design) {pole : Fin 6}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin 6)} (hcard : deleted.card = 3) (hpole : pole ∉ deleted)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    setDeletionMargin design pole deleted * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ ∑ label ∈ Finset.univ \ insert pole deleted,
          (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  exact exists_heavy_forcedCover_of_isTie (rank := 3) (by norm_num) gtz_rank_two design htie
    hlong (by omega) (Finset.card_pos.mp (by omega)) hpole hdeletable

/-- **THE SINGLE DELETION IS THE ONE-LABEL SET DELETION.**  The debt of a single
label is its own weighted shadow deficit, thus the set condition reads exactly as
the landed one-atom condition. -/
theorem planeShadowDebt_singleton {size rank : ℕ} (design : WeightedDesign size rank)
    (pole drop : Fin size) :
    planeShadowDebt design pole {drop}
      = design.weight drop * planeShadowSq design pole drop - design.weight drop := by
  rw [planeShadowDebt, Finset.sum_singleton]
  ring

/-- The one-label set condition and the landed single deletion condition are the
same inequality. -/
theorem deletableSet_singleton_iff {size rank : ℕ} (design : WeightedDesign size rank)
    (pole drop : Fin size) :
    planeShadowDebt design pole {drop} < design.weight pole
      ↔ design.weight drop * planeShadowSq design pole drop
          < design.weight pole + design.weight drop := by
  rw [planeShadowDebt_singleton]
  constructor
  · intro hlt; linarith
  · intro hlt; linarith

/-- **THE DEBT LEDGER AT THE DECIDING CELL OF RANK THREE.**  Six labels of rank
three: the whole non-pole debt is exactly `1 + weight pole`, the whole non-pole
set is never deletable, and a deletable set leaves survivors that carry more than
ONE unit of debt. -/
theorem sixThree_debt_ledger (design : WeightedDesign 6 3) {pole : Fin 6}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    planeShadowDebt design pole (Finset.univ.erase pole) = 1 + design.weight pole
      ∧ ¬ (planeShadowDebt design pole (Finset.univ.erase pole) < design.weight pole)
      ∧ ∀ deleted : Finset (Fin 6), deleted ⊆ Finset.univ.erase pole →
          planeShadowDebt design pole deleted < design.weight pole →
            1 < planeShadowDebt design pole (Finset.univ.erase pole \ deleted) := by
  have hpole : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  refine ⟨by rw [sum_weight_planeShadowDebt design pole hpole]; norm_num,
    not_deletableSet_erase_pole design (by norm_num) hpole, fun deleted hsub hdeletable => ?_⟩
  have hstep := (deletableSet_iff_survivor_debt design hpole hsub).mp hdeletable
  push_cast at hstep
  linarith

/-- **THE MEASURED STOP OF THE ITERATION AT RANK THREE.**  When every non-pole
label carries debt at most `debtCap`, a deletable set leaves more than
`1 / debtCap` survivors.  At the uniform deciding cell every label carries debt
`7/30`, thus a deletable set leaves more than four survivors of the five, that is
the deleted set is EMPTY.  The iterated deletion does not cross the deciding cell
by itself. -/
theorem sixThree_card_survivor_bound (design : WeightedDesign 6 3) {pole : Fin 6}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {deleted : Finset (Fin 6)} (hsub : deleted ⊆ Finset.univ.erase pole)
    {debtCap : ℝ}
    (hcap : ∀ c : Fin 6, c ≠ pole → design.weight c * (planeShadowSq design pole c - 1) ≤ debtCap)
    (hdeletable : planeShadowDebt design pole deleted < design.weight pole) :
    1 < ((Finset.univ.erase pole \ deleted).card : ℝ) * debtCap := by
  have hpole : (0 : ℝ) < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hstep := card_survivor_lower_bound_of_deletable design hpole hsub hcap hdeletable
  push_cast at hstep
  linarith

end RankThree

end Gtz

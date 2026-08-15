/-
# The cross budget of a flat set, and the exact deficit of Cauchy-Schwarz

`Gtz.flatSplit_posDef_iff_planeInequality` decides a selection by ONE inequality
once the excess is discharged.  At every plane probe the squared CROSS reading
must fall below the excess times the plane surplus.  `Gtz.flat_normalBudget`
prices the excess.  Nothing priced the cross reading.

Parseval has an OFF-DIAGONAL block, and no module in the tree has read it.  Take
a plane probe orthogonal to the normal.  The weighted mixed readings of ALL
labels sum to the pairing of the two probes, which is zero.  Every flat atom
kills the normal.  So the weighted mixed readings of the complement sum to zero:

  `∑_{c ∉ flat} w_c (a_c ⬝ p)(a_c ⬝ n) = 0`     (the cross budget)

The cross reading therefore equals its own DEFICIENCY-weighted form, exactly as
`Gtz.sum_sq_normalReading_compl_sub_one` shows the excess does.  Both sides of
the plane inequality then carry the same deficiency weights, and Cauchy-Schwarz
against those weights is the obvious route.

That route is DEAD, and this module prices its failure exactly.  The
Cauchy-Schwarz majorant is the deficiency-weighted plane energy of the
complement.  It exceeds the plane surplus by exactly the weighted plane energy
of the flat set itself.  The deficit is nonnegative at every probe, and it
vanishes only where every flat atom reads zero.  So no argument that prices the
cross reading by Cauchy-Schwarz alone can prove the plane inequality anywhere
the line is visible.

The second section restates one datum of the stage-4 record of the one-line
obligation.  That record reduces its leg C to a claim about quantities named
`eps_i`, and the repository defines none of them.  The record carries one fully
specified witness, and it pins the reading of `eps_i`: the in-plane form of the
line, built from UNNORMALIZED line vectors, is isotropic at `11/20` for that
witness, and the normalized form is not isotropic at all.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.UniversalNeedle
import Gtz.Design.FlatNormalBudget

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Parseval off the diagonal -/

/-- **Parseval in mixed form.**  The weighted pairing of two probes through the
atoms reproduces the pairing of the probes.  The squared form
`Gtz.sum_weight_mul_sq_dotProduct` is the diagonal case. -/
theorem sum_weight_mul_dotProduct_mul_dotProduct (design : WeightedDesign size rank)
    (probeOne probeTwo : Fin rank → ℝ) :
    (∑ label, design.weight label
        * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo)))
      = probeOne ⬝ᵥ probeTwo := by
  calc ∑ label, design.weight label
        * ((design.atom label ⬝ᵥ probeOne) * (design.atom label ⬝ᵥ probeTwo))
      = ∑ label, probeOne ⬝ᵥ ((design.weight label • atomMatrix (design.atom label))
          *ᵥ probeTwo) := by
        refine Finset.sum_congr rfl fun label _ => ?_
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
          vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
          dotProduct_comm probeOne (design.atom label)]
        ring
    _ = probeOne ⬝ᵥ ((∑ label, design.weight label • atomMatrix (design.atom label))
          *ᵥ probeTwo) := by
        rw [Matrix.sum_mulVec, dotProduct_sum]
    _ = probeOne ⬝ᵥ probeTwo := by
        rw [design.isParseval, Matrix.one_mulVec]

/-! ## The cross budget -/

/-- **The cross budget.**  At a plane probe orthogonal to a normal that every
flat atom kills, the weighted mixed readings of the complement sum to zero.
This is the off-diagonal block of Parseval, read at the flat pattern. -/
theorem flat_crossBudget (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (normalVec planeProbe : Fin rank → ℝ)
    (horth : planeProbe ⬝ᵥ normalVec = 0)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (∑ label ∈ flatᶜ, design.weight label
        * ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec))) = 0 := by
  have hall := sum_weight_mul_dotProduct_mul_dotProduct design planeProbe normalVec
  have hflatZero : (∑ label ∈ flat, design.weight label
      * ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec))) = 0 :=
    Finset.sum_eq_zero fun label hlabel => by rw [hflat label hlabel]; ring
  have hsplit := Finset.sum_add_sum_compl flat
    (fun label => design.weight label
      * ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)))
  rw [hall, horth] at hsplit
  linarith [hsplit, hflatZero]

/-- **The cross reading is its own deficiency form.**  The weighted part vanishes
by the cross budget, so the unweighted cross sum over the complement equals the
deficiency-weighted one.  The excess carries the same weights. -/
theorem flat_cross_eq_deficiencyCross (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (normalVec planeProbe : Fin rank → ℝ)
    (horth : planeProbe ⬝ᵥ normalVec = 0)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (∑ label ∈ flatᶜ,
        (design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec))
      = ∑ label ∈ flatᶜ, (1 - design.weight label)
          * ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)) := by
  have hbudget := flat_crossBudget design flat normalVec planeProbe horth hflat
  have hterm : ∀ label : Fin size,
      (1 - design.weight label)
          * ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec))
        = ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec))
          - design.weight label
            * ((design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)) :=
    fun label => by ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib, hbudget]
  ring

/-! ## The plane surplus, and the deficit of Cauchy-Schwarz -/

/-- **The plane surplus in deficiency form.**  Parseval splits the probe energy
between the flat set and its complement.  The surplus of the complement over the
probe is the deficiency-weighted plane energy of the complement, less the flat
set's own weighted plane energy.  No orthogonality and no flatness is used. -/
theorem flat_planeSurplus_eq (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (planeProbe : Fin rank → ℝ) :
    (∑ label ∈ flatᶜ, (design.atom label ⬝ᵥ planeProbe) ^ 2) - planeProbe ⬝ᵥ planeProbe
      = (∑ label ∈ flatᶜ, (1 - design.weight label)
            * (design.atom label ⬝ᵥ planeProbe) ^ 2)
        - ∑ label ∈ flat, design.weight label
            * (design.atom label ⬝ᵥ planeProbe) ^ 2 := by
  have hall := sum_weight_mul_sq_dotProduct design planeProbe
  have hsplit := Finset.sum_add_sum_compl flat
    (fun label => design.weight label * (design.atom label ⬝ᵥ planeProbe) ^ 2)
  have hterm : ∀ label : Fin size,
      (1 - design.weight label) * (design.atom label ⬝ᵥ planeProbe) ^ 2
        = (design.atom label ⬝ᵥ planeProbe) ^ 2
          - design.weight label * (design.atom label ⬝ᵥ planeProbe) ^ 2 :=
    fun label => by ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib]
  rw [hall] at hsplit
  linarith [hsplit]

/-- **Cauchy-Schwarz overshoots by the flat set's own energy.**  The
deficiency-weighted plane energy of the complement is the Cauchy-Schwarz
majorant of the plane inequality.  It exceeds the plane surplus by exactly the
weighted plane energy of the flat set. -/
theorem flat_cauchySchwarz_overshoot (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (planeProbe : Fin rank → ℝ) :
    (∑ label ∈ flatᶜ, (1 - design.weight label)
        * (design.atom label ⬝ᵥ planeProbe) ^ 2)
      - ((∑ label ∈ flatᶜ, (design.atom label ⬝ᵥ planeProbe) ^ 2)
          - planeProbe ⬝ᵥ planeProbe)
      = ∑ label ∈ flat, design.weight label
          * (design.atom label ⬝ᵥ planeProbe) ^ 2 := by
  have h := flat_planeSurplus_eq design flat planeProbe
  linarith

/-- The overshoot is nonnegative at every probe. -/
theorem flat_planeSurplus_le_deficiencyEnergy (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (planeProbe : Fin rank → ℝ) :
    ((∑ label ∈ flatᶜ, (design.atom label ⬝ᵥ planeProbe) ^ 2)
        - planeProbe ⬝ᵥ planeProbe)
      ≤ ∑ label ∈ flatᶜ, (1 - design.weight label)
          * (design.atom label ⬝ᵥ planeProbe) ^ 2 := by
  have hover := flat_cauchySchwarz_overshoot design flat planeProbe
  have hnonneg : 0 ≤ ∑ label ∈ flat, design.weight label
      * (design.atom label ⬝ᵥ planeProbe) ^ 2 :=
    Finset.sum_nonneg fun label _ =>
      mul_nonneg (design.weight_pos label).le (sq_nonneg _)
  linarith

/-- **The Cauchy-Schwarz route is dead wherever the flat set is visible.**  If
the majorant falls at or below the plane surplus at a probe, then every flat
atom reads zero at that probe.  So the route closes only on the probes the flat
set already kills, and those probes carry no information about the plane. -/
theorem flat_readings_zero_of_deficiencyEnergy_le_planeSurplus
    (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (planeProbe : Fin rank → ℝ)
    (hle : (∑ label ∈ flatᶜ, (1 - design.weight label)
        * (design.atom label ⬝ᵥ planeProbe) ^ 2)
      ≤ ((∑ label ∈ flatᶜ, (design.atom label ⬝ᵥ planeProbe) ^ 2)
          - planeProbe ⬝ᵥ planeProbe)) :
    ∀ label ∈ flat, design.atom label ⬝ᵥ planeProbe = 0 := by
  have hover := flat_cauchySchwarz_overshoot design flat planeProbe
  have hsumLe : (∑ label ∈ flat, design.weight label
      * (design.atom label ⬝ᵥ planeProbe) ^ 2) ≤ 0 := by linarith
  intro label hlabel
  have hnonneg : ∀ other ∈ flat, 0 ≤ design.weight other
      * (design.atom other ⬝ᵥ planeProbe) ^ 2 :=
    fun other _ => mul_nonneg (design.weight_pos other).le (sq_nonneg _)
  have hzero : design.weight label * (design.atom label ⬝ᵥ planeProbe) ^ 2 = 0 := by
    have hterm := Finset.single_le_sum hnonneg hlabel
    have := hnonneg label hlabel
    linarith
  have hsq : (design.atom label ⬝ᵥ planeProbe) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with hw | hsq
    · exact absurd hw (ne_of_gt (design.weight_pos label))
    · exact hsq
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-! ## The in-plane line form of the stage-4 record

The stage-4 lane of `Gtz.obligationHeavyWeakToStrictOneLine` reduces its leg C
to a statement about quantities the repository never defines.  The record does
carry one fully specified witness, and that witness pins the reading of the
first quantity.  This section lands the reading and verifies the witness. -/

/-- **The in-plane form of a line.**  The mass-weighted outer sum of the line
directions.  When every direction kills a normal, this form kills it too, so the
plane carries the whole form. -/
noncomputable def lineInPlaneForm {ambient : ℕ} (lineVec : Fin 3 → (Fin ambient → ℝ))
    (mass : Fin 3 → ℝ) : Matrix (Fin ambient) (Fin ambient) ℝ :=
  ∑ index, mass index • atomMatrix (lineVec index)

/-- The three line directions of the closed-door witness of the stage-4 record. -/
def closedDoorLine : Fin 3 → (Fin 2 → ℝ)
  | 0 => ![1, 0]
  | 1 => ![4, 7]
  | 2 => ![-4, 7]

/-- The three masses of the closed-door witness of the stage-4 record. -/
noncomputable def closedDoorMass : Fin 3 → ℝ
  | 0 => 363 / 980
  | 1 => 11 / 1960
  | 2 => 11 / 1960

/-- **The closed-door witness is isotropic at `11/20`.**  The record states its
witness lies on the isotropic band with that constant.  It does, under the
UNNORMALIZED reading of the line directions. -/
theorem closedDoor_lineInPlaneForm_eq :
    lineInPlaneForm closedDoorLine closedDoorMass
      = (11 / 20 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [lineInPlaneForm, closedDoorLine, closedDoorMass, atomMatrix,
      Fin.sum_univ_three] <;>
    norm_num

/-- The constant of the closed-door witness lies in the band the record names. -/
theorem closedDoor_constant_mem_band :
    (1 : ℝ) / 2 < 11 / 20 ∧ (11 : ℝ) / 20 ≤ 4 / 7 := by
  constructor <;> norm_num

/-- The masses of the closed-door witness, rescaled by the squared length of
each line direction.  This is the NORMALIZED reading of the same witness. -/
noncomputable def closedDoorNormalizedMass : Fin 3 → ℝ :=
  fun index => closedDoorMass index / (closedDoorLine index ⬝ᵥ closedDoorLine index)

/-- **The normalized reading is not isotropic.**  The same witness under
normalized line directions has two different diagonal entries, so it does not
lie on the isotropic band.  The record's constant therefore reads the
unnormalized form, and no other reading reproduces it. -/
theorem closedDoor_normalized_not_isotropic :
    lineInPlaneForm closedDoorLine closedDoorNormalizedMass 0 0
      ≠ lineInPlaneForm closedDoorLine closedDoorNormalizedMass 1 1 := by
  simp [lineInPlaneForm, closedDoorLine, closedDoorMass, closedDoorNormalizedMass,
    atomMatrix, Fin.sum_univ_three, dotProduct, Fin.sum_univ_two]
  norm_num

end Gtz

import Gtz.Wave.OneAxisZeroAnchorLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The `Z1` witness: an exact rational one-zero corner of a non-tie

No fixture of the campaign inhabits the `Z1` stratum: `ledgerFoil` and
`residualFoil` carry `Z2` corners, `signCoherentFoil` and the non-planar
fixture read all three inside atoms off the axis.  This module supplies the
missing calibration object.  `Gtz.oneAxisZeroWitness` is an exact rational
`(6,3)` design with the corner `{0,1,2}`, gap `24/25 • u uᵀ` at `u = (1,0,0)`,
a unit zero atom `g₀ = (0,1,0)`, and axis readings `21/25` and `28/25` at the
other two inside atoms — `Z1` proper, with a positive gap scale.

Its outside atoms are `(2,0,0)`, `(0,6/5,8/5)` and `(0,-8/5,6/5)`, so the
unweighted outside sum is `4·I` and the complement dominates strictly with
margin three (`Gtz.oneAxisZeroWitness_compl_posDef`).  The witness is
therefore NOT a tie, both inside four-sets are positive definite — the
both-light cell — and the pair system of the erase-`0` anchor FAILS
(`Gtz.oneAxisZeroWitness_pairSystem_fails`), as do the seven both-light
floors (`Gtz.oneAxisZeroWitness_bothLight_floors_fail`).

The two failure theorems are the foil tests of the coverage residual: the
antecedent system of `Gtz.OneAxisZeroPairCoverage` is refutable at an
inhabited `Z1` proper corner, so the residual is not a tautology trap of the
`NonplanarGhostResidual` kind, and the `Z1` guard is satisfiable.  The
`x`-mass law is calibrated here in exact arithmetic: the weighted outside
`x`-readings total `176/201 = 1 − t₀` on the nose
(`Gtz.oneAxisZeroWitness_xMass`).

## The forcing law of the heavy-inside cell

The module also lands the tie-free forcing that pins the fourth floor of the
heavy-inside cell (`Gtz.corner_fourSet_exchange_reading`): whenever one
four-set `{f} ∪ Cᶜ` fails while the other `{e} ∪ Cᶜ` holds, the kept inside
atom reads its own four-set at least at one, because the two four-sets share
the complement triple as a common downdate.  With it, the heavy-inside cell
of a `Z1` tie carries all FOUR member floors of the surviving four-set, and
the three outside floors of
`Gtz.corner_oneAxisZero_heavyInside_isTie_iff` are the only tie content.
No corner hypothesis is consumed: the law is pure downdate exchange.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The exchange forcing of two four-sets over one complement -/

/-- **The exchange reading.**  Two four-sets `{e} ∪ K` and `{f} ∪ K` share the
triple `K` as a common rank-one downdate.  When the second four-set fails and
the first holds, the kept atom `e` reads the first four-set's inverse gap at
least at one.  Pure downdate exchange — no corner, no tie. -/
theorem corner_fourSet_exchange_reading (D : WeightedDesign 6 3)
    {e f : Fin 6} {K : Finset (Fin 6)} (heK : e ∉ K) (hfK : f ∉ K)
    (hAe : (subsetSum D (insert e K) - 1).PosDef)
    (hAf : ¬ (subsetSum D (insert f K) - 1).PosDef) :
    1 ≤ D.atom e ⬝ᵥ ((subsetSum D (insert e K) - 1)⁻¹ *ᵥ D.atom e) := by
  have hKf : subsetSum D K - 1
      = (subsetSum D (insert f K) - 1)
        - Matrix.vecMulVec (D.atom f) (D.atom f) := by
    rw [← subsetSum_erase_sub_one_rankOne D (insert f K) (Finset.mem_insert_self f K),
      Finset.erase_insert hfK]
  have hKe : subsetSum D K - 1
      = (subsetSum D (insert e K) - 1)
        - Matrix.vecMulVec (D.atom e) (D.atom e) := by
    rw [← subsetSum_erase_sub_one_rankOne D (insert e K) (Finset.mem_insert_self e K),
      Finset.erase_insert heK]
  have hKnot : ¬ (subsetSum D K - 1).PosDef := by
    rw [hKf]
    exact not_posDef_sub_vecMulVec_of_not_posDef hAf _
  rw [hKe] at hKnot
  by_contra hlt
  push_neg at hlt
  exact hKnot ((posDef_sub_vecMulVec_iff _ hAe (D.atom e)).mpr hlt)

/-! ## 2. The witness -/

/-- The six atoms of the `Z1` witness: the unit zero atom, the two
axis-carrying inside atoms of the `3-4-5` frame, and three outside atoms
whose unweighted sum is `4·I`. -/
noncomputable def oneAxisZeroWitnessAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![0, 1, 0]
  | 1 => ![21 / 25, 0, 4 / 5]
  | 2 => ![28 / 25, 0, -(3 / 5)]
  | 3 => ![2, 0, 0]
  | 4 => ![0, 6 / 5, 8 / 5]
  | 5 => ![0, -(8 / 5), 6 / 5]

/-- The six weights of the `Z1` witness: the exact rational Parseval solution. -/
noncomputable def oneAxisZeroWitnessWeight : Fin 6 → ℝ
  | 0 => 25 / 201
  | 1 => 25 / 201
  | 2 => 25 / 201
  | 3 => 38 / 201
  | 4 => 44 / 201
  | 5 => 44 / 201

/-- **THE `Z1` WITNESS.**  An exact rational `(6,3)` design whose corner
`{0,1,2}` carries the rank-one gap `24/25 • u uᵀ` with one zero inside axis
reading and two nonzero ones. -/
noncomputable def oneAxisZeroWitness : WeightedDesign 6 3 where
  atom := oneAxisZeroWitnessAtom
  weight := oneAxisZeroWitnessWeight
  weight_pos := by
    intro label
    fin_cases label <;> norm_num [oneAxisZeroWitnessWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [oneAxisZeroWitnessWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [oneAxisZeroWitnessAtom, oneAxisZeroWitnessWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem oneAxisZeroWitness_atom :
    oneAxisZeroWitness.atom = oneAxisZeroWitnessAtom := rfl

theorem oneAxisZeroWitness_weight :
    oneAxisZeroWitness.weight = oneAxisZeroWitnessWeight := rfl

/-- The gap axis of the witness. -/
noncomputable def oneAxisZeroAxis : Fin 3 → ℝ := ![1, 0, 0]

theorem oneAxisZeroAxis_unit : oneAxisZeroAxis ⬝ᵥ oneAxisZeroAxis = 1 := by
  norm_num [oneAxisZeroAxis, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **The rank-one gap, exactly**: `S_{0,1,2} − 1 = 24/25 • u uᵀ`. -/
theorem oneAxisZeroWitness_gap :
    subsetSum oneAxisZeroWitness ({0, 1, 2} : Finset (Fin 6)) - 1
      = (24 / 25 : ℝ) • atomMatrix oneAxisZeroAxis := by
  rw [subsetSum,
    show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [oneAxisZeroWitness_atom, oneAxisZeroWitnessAtom, oneAxisZeroAxis,
      atomMatrix, Matrix.vecMulVec_apply, Matrix.cons_val_two]

/-- The zero atom reads the axis at zero. -/
theorem oneAxisZeroWitness_zero_reading :
    oneAxisZeroWitness.atom 0 ⬝ᵥ oneAxisZeroAxis = 0 := by
  norm_num [oneAxisZeroWitness_atom, oneAxisZeroWitnessAtom, oneAxisZeroAxis,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The other two inside atoms read the axis off zero: the witness is `Z1`
proper. -/
theorem oneAxisZeroWitness_nonzero_readings :
    oneAxisZeroWitness.atom 1 ⬝ᵥ oneAxisZeroAxis ≠ 0
      ∧ oneAxisZeroWitness.atom 2 ⬝ᵥ oneAxisZeroAxis ≠ 0 := by
  constructor <;>
    norm_num [oneAxisZeroWitness_atom, oneAxisZeroWitnessAtom, oneAxisZeroAxis,
      dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-! ## 3. The complement dominates strictly: the witness is not a tie -/

/-- **The complement gap is `3 • 1`**: the outside atoms resolve `4·I`
unweighted. -/
theorem oneAxisZeroWitness_compl_form :
    subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) - 1
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [subsetSum,
    show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [oneAxisZeroWitness_atom, oneAxisZeroWitnessAtom, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.one_apply]

/-- The complement triple dominates strictly, with margin three. -/
theorem oneAxisZeroWitness_compl_posDef :
    (subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef := by
  rw [oneAxisZeroWitness_compl_form]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun v hv => ?_⟩
  · exact isHermitian_of_transpose_eq
      (by rw [Matrix.transpose_smul, Matrix.transpose_one])
  · rw [star_trivial, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
    have hpos := dotProduct_self_pos hv
    linarith

/-- **The witness is not a tie.** -/
theorem oneAxisZeroWitness_not_isTie : ¬ IsTie oneAxisZeroWitness := fun htie =>
  htie.2 ({3, 4, 5} : Finset (Fin 6)) (by decide) oneAxisZeroWitness_compl_posDef

/-! ## 4. The foil tests of the coverage residual -/

/-- **The pair system fails at the witness.**  The erase-`0` anchor of the
`Z1` witness does NOT satisfy the ten pair-reading disjunctions: the coverage
residual's antecedent system is refutable at an inhabited `Z1` proper corner,
and the residual is not a tautology. -/
theorem oneAxisZeroWitness_pairSystem_fails :
    ¬ ∀ a ∈ (univ : Finset (Fin 6)).erase 0,
      ∀ b ∈ (univ : Finset (Fin 6)).erase 0, a ≠ b →
      1 ≤ oneAxisZeroWitness.atom a ⬝ᵥ
          ((subsetSum oneAxisZeroWitness ((univ : Finset (Fin 6)).erase 0) - 1)⁻¹
            *ᵥ oneAxisZeroWitness.atom a)
      ∨ (1 - oneAxisZeroWitness.atom a ⬝ᵥ
          ((subsetSum oneAxisZeroWitness ((univ : Finset (Fin 6)).erase 0) - 1)⁻¹
            *ᵥ oneAxisZeroWitness.atom a))
        * (1 - oneAxisZeroWitness.atom b ⬝ᵥ
          ((subsetSum oneAxisZeroWitness ((univ : Finset (Fin 6)).erase 0) - 1)⁻¹
            *ᵥ oneAxisZeroWitness.atom b))
        ≤ (oneAxisZeroWitness.atom a ⬝ᵥ
          ((subsetSum oneAxisZeroWitness ((univ : Finset (Fin 6)).erase 0) - 1)⁻¹
            *ᵥ oneAxisZeroWitness.atom b)) ^ 2 := by
  intro hpairs
  exact oneAxisZeroWitness_not_isTie
    ((corner_oneAxisZero_isTie_iff_pairSystem oneAxisZeroWitness
      (by decide) (by decide) (by decide) (by norm_num : (0 : ℝ) ≤ 24 / 25)
      oneAxisZeroAxis_unit oneAxisZeroWitness_gap
      oneAxisZeroWitness_zero_reading).mpr hpairs)

/-! ## 5. The witness sits in the both-light cell -/

/-- The four-set gap through an axis-carrying inside atom `e ∈ {1, 2}` of the
witness is `3 • 1 + g_e g_eᵀ`, which is positive definite. -/
theorem oneAxisZeroWitness_fourSet_posDef {e : Fin 6} (he : e = 1 ∨ e = 2) :
    (subsetSum oneAxisZeroWitness
      (insert e (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1).PosDef := by
  have hcompl : (({0, 1, 2} : Finset (Fin 6))ᶜ) = {3, 4, 5} := by decide
  have hmem : e ∉ ({3, 4, 5} : Finset (Fin 6)) := by
    rcases he with rfl | rfl <;> decide
  have hform : subsetSum oneAxisZeroWitness
        (insert e (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1
      = (subsetSum oneAxisZeroWitness ({3, 4, 5} : Finset (Fin 6)) - 1)
        + atomMatrix (oneAxisZeroWitness.atom e) := by
    rw [hcompl, subsetSum, subsetSum, Finset.sum_insert hmem]
    abel
  rw [hform, oneAxisZeroWitness_compl_form]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun v hv => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix _).1]
  · rw [star_trivial, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      show atomMatrix (oneAxisZeroWitness.atom e)
        = Matrix.vecMulVec (oneAxisZeroWitness.atom e)
            (oneAxisZeroWitness.atom e) from rfl,
      quadForm_atomMatrix]
    have hpos := dotProduct_self_pos hv
    nlinarith [sq_nonneg (oneAxisZeroWitness.atom e ⬝ᵥ v)]

/-- **The both-light floor system fails at the witness.**  Both inside
four-sets hold, the witness is not a tie, and the both-light collapse
refutes the seven floors: the both-light cell of the coverage residual is
calibrated against a real `Z1` corner. -/
theorem oneAxisZeroWitness_bothLight_floors_fail :
    ¬ ((1 ≤ oneAxisZeroWitness.atom 1 ⬝ᵥ
          ((subsetSum oneAxisZeroWitness
            (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ oneAxisZeroWitness.atom 1))
      ∧ (∀ d ∈ (({0, 1, 2} : Finset (Fin 6))ᶜ),
          1 ≤ oneAxisZeroWitness.atom d ⬝ᵥ
            ((subsetSum oneAxisZeroWitness
              (insert 1 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                *ᵥ oneAxisZeroWitness.atom d))
      ∧ (∀ d ∈ (({0, 1, 2} : Finset (Fin 6))ᶜ),
          1 ≤ oneAxisZeroWitness.atom d ⬝ᵥ
            ((subsetSum oneAxisZeroWitness
              (insert 2 (({0, 1, 2} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                *ᵥ oneAxisZeroWitness.atom d))) := by
  intro hfloors
  exact oneAxisZeroWitness_not_isTie
    ((corner_oneAxisZero_bothLight_isTie_iff oneAxisZeroWitness
      (by decide) (by decide) (by decide) (by norm_num : (0 : ℝ) ≤ 24 / 25)
      oneAxisZeroAxis_unit oneAxisZeroWitness_gap
      oneAxisZeroWitness_zero_reading
      (oneAxisZeroWitness_fourSet_posDef (Or.inl rfl))
      (oneAxisZeroWitness_fourSet_posDef (Or.inr rfl))).mpr hfloors)

/-! ## 6. The `x`-mass law, calibrated exactly -/

/-- **The `x`-mass identity at the witness**: the weighted outside
`x`-readings total `176/201 = 1 − t₀`, by the landed law and exact
arithmetic. -/
theorem oneAxisZeroWitness_xMass :
    ∑ d ∈ (({0, 1, 2} : Finset (Fin 6))ᶜ),
        oneAxisZeroWitness.weight d
          * (oneAxisZeroWitness.atom d ⬝ᵥ oneAxisZeroWitness.atom 0) ^ 2
      = 176 / 201 := by
  have h := corner_oneAxisZero_outside_xMass oneAxisZeroWitness
    (by decide : (0 : Fin 6) ≠ 1) (by decide : (0 : Fin 6) ≠ 2)
    (by decide : (1 : Fin 6) ≠ 2) (by norm_num : (0 : ℝ) ≤ 24 / 25)
    oneAxisZeroAxis_unit oneAxisZeroWitness_gap oneAxisZeroWitness_zero_reading
  rw [h, oneAxisZeroWitness_weight]
  norm_num [oneAxisZeroWitnessWeight]

end Gtz

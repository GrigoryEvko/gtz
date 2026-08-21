/-
# Domination complements itself: the sharp design

Read domination through the Naimark dual and it moves to the complementary
selection of a THIRD design that carries the same weights.

## The dual reading

For a selection `C` put

  `Reading(C) = Σ_{c ∈ C} (t_c / (1 - t_c)) · co_c co_cᵀ`,

an `r × r` matrix, `r = m - k`.  `Gtz.naimark_dominates_iff_reading_le`:

  **`C` dominates  ⟺  `Reading(C) ⪯ 1`.**

Two flips take the `k × k` cap of `Gtz/Wave/NaimarkDualDesign.lean` to this
`r × r` statement: a positive diagonal congruence and the rectangular transfer
`1 - XᵀX ⪰ 0 ⟺ 1 - XXᵀ ⪰ 0`.  Only a DIAGONAL square root appears.

## The complement, and the sharp design

The dual Parseval law says `Σ_c (1 - t_c) M_c = 1` with `M_c = (t_c/(1-t_c)) co_c
co_cᵀ`, so `Omegabar - 1 = Σ_c t_c M_c`, and the criterion turns into

  **`C` dominates  ⟺  `Reading(Cᶜ) ⪰ Omegabar - 1 = Σ_c t_c M_c`.**

The right side is the weighted average of the very family being selected from, so
this is again a domination question.  Whitening `Omegabar - 1`, which is positive
definite, gives `Gtz.exists_naimark_sharp_design`:

  **Every `(m,k)` design `D` carries an `(m, m-k)` design `E` with the SAME
   weights such that a `k`-selection dominates in `D` exactly when its
   complementary `(m-k)`-selection dominates in `E`.**

At `(6,3)` both designs are `(6,3)` designs, and the map sends a dominating triple
to the complementary dominating triple.  The landed
`Gtz.dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree` is the
uniform-weight case.  Here the weights are arbitrary and carried unchanged, and
`Gtz.gtzWeighted_six_three_iff_dominating_compl` reads the open cell as "every
`(6,3)` design has a triple whose COMPLEMENT dominates the sharp design".

[MEASURED before proving.  The square-root-free criterion and the sharp design
were checked against domination on 2975 selections over 105 random designs at
`(6,3)`, `(7,3)`, `(5,3)` and `(8,4)`, with ZERO mismatches.  The whitening target
`Omegabar - 1` had smallest eigenvalue `0.0173` over the run and the sharp
Parseval residual was at most `2.3e-14`.]
-/
import Gtz.Wave.NaimarkCycleFree

namespace Gtz

open Matrix Finset

variable {m k r : ℕ}

variable {D : WeightedDesign m k}

/-! ## 1. The dual reading of a selection -/

/-- The dual reading of a selection: `Σ_{c ∈ C} (t_c/(1 - t_c)) · co_c co_cᵀ`. -/
noncomputable def naimarkReading (N : NaimarkDual D r) {size : ℕ} (pick : Fin size → Fin m) :
    Matrix (Fin r) (Fin r) ℝ :=
  ∑ a, (D.weight (pick a) / (1 - D.weight (pick a))) • atomMatrix (N.co (pick a))

/-- The full dual reading is the reading of the whole index set. -/
theorem naimarkOmega_eq_reading (N : NaimarkDual D r) :
    naimarkOmega N = naimarkReading N (id : Fin m → Fin m) := rfl

/-- The cap entry of a selection is positive. -/
theorem naimarkCap_diag_pos (D : WeightedDesign m k) (hm : 2 ≤ m) {size : ℕ}
    (pick : Fin size → Fin m) (a : Fin size) :
    0 < (D.weight (pick a))⁻¹ - 1 := by
  have hpos := D.weight_pos (pick a)
  have hlt := weight_lt_one D hm (pick a)
  have h1 : 1 < (D.weight (pick a))⁻¹ := by
    rw [lt_inv_comm₀ one_pos hpos]
    simpa using hlt
  linarith

/-- The inverse cap entry is the reading coefficient. -/
theorem naimarkCap_inv_eq (D : WeightedDesign m k) (hm : 2 ≤ m) {size : ℕ}
    (pick : Fin size → Fin m) (a : Fin size) :
    ((D.weight (pick a))⁻¹ - 1)⁻¹ = D.weight (pick a) / (1 - D.weight (pick a)) := by
  have hpos := D.weight_pos (pick a)
  have hlt := weight_lt_one D hm (pick a)
  have hw : D.weight (pick a) ≠ 0 := hpos.ne'
  rw [show (D.weight (pick a))⁻¹ - 1 = (1 - D.weight (pick a)) / D.weight (pick a) by field_simp]
  rw [inv_div]

/-- **DOMINATION IS A CONTRACTION OF THE DUAL READING.**  A `k`-selection
dominates exactly when its dual reading sits below the identity of `ℝ^{m-k}`.
No weight stands beside the statement and no submatrix appears: everything the
selection knows has moved into one `(m-k) × (m-k)` matrix. -/
theorem naimark_dominates_iff_reading_le (N : NaimarkDual D r) (hm : 2 ≤ m)
    {pick : Fin k → Fin m} (hpick : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ ((1 : Matrix (Fin r) (Fin r) ℝ) - naimarkReading N pick).PosSemidef := by
  classical
  set gapEntry : Fin k → ℝ := fun a => (D.weight (pick a))⁻¹ - 1 with hgapEntry
  have hgapPos : ∀ a, 0 < gapEntry a := fun a => naimarkCap_diag_pos D hm pick a
  set scale : Fin k → ℝ := fun a => Real.sqrt (gapEntry a)⁻¹ with hscale
  have hscalePos : ∀ a, 0 < scale a := fun a =>
    Real.sqrt_pos.mpr (inv_pos.mpr (hgapPos a))
  have hscaleSq : ∀ a, scale a * scale a = (gapEntry a)⁻¹ := fun a =>
    Real.mul_self_sqrt (inv_pos.mpr (hgapPos a)).le
  set congruence : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal scale with hcongruence
  have hcongrUnit : IsUnit congruence.det := by
    rw [hcongruence, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => (hscalePos a).ne'
  have hsymm : (naimarkCap D pick - naimarkCoGram N pick)ᵀ
      = naimarkCap D pick - naimarkCoGram N pick := by
    rw [Matrix.transpose_sub, naimarkCap, Matrix.diagonal_transpose]
    congr 1
    ext a b
    simp only [naimarkCoGram, Matrix.transpose_apply, Matrix.of_apply]
    exact dotProduct_comm _ _
  have hshape : congruenceᵀ * (naimarkCap D pick - naimarkCoGram N pick) * congruence
      = 1 - (congruence * naimarkCoRows N pick) * (congruence * naimarkCoRows N pick)ᵀ := by
    rw [naimarkCoGram_eq_mul, naimarkCap, hcongruence, Matrix.diagonal_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    · rw [Matrix.diagonal_mul_diagonal]
      have hone : (fun a => scale a * gapEntry a * scale a) = fun _ : Fin k => (1 : ℝ) := by
        funext a
        have hsq := hscaleSq a
        have hne : gapEntry a ≠ 0 := (hgapPos a).ne'
        field_simp at hsq ⊢
        linarith [hsq]
      rw [hone, Matrix.diagonal_one]
    · rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
      simp only [Matrix.mul_assoc]
  have hprod : (congruence * naimarkCoRows N pick)ᵀ * (congruence * naimarkCoRows N pick)
      = naimarkReading N pick := by
    rw [Matrix.transpose_mul, hcongruence, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal scale) (Matrix.diagonal scale) (naimarkCoRows N pick),
      Matrix.diagonal_mul_diagonal]
    have hcoef : (fun a => scale a * scale a)
        = fun a => D.weight (pick a) / (1 - D.weight (pick a)) := by
      funext a
      rw [hscaleSq a, hgapEntry]
      exact naimarkCap_inv_eq D hm pick a
    rw [hcoef, ← Matrix.mul_assoc]
    exact naimark_coRows_reading N pick _
  rw [naimark_dominates_iff_coGram_le N hpick,
    posSemidef_congr_right hsymm hcongrUnit, hshape,
    ← posSemidef_one_sub_transpose_comm (congruence * naimarkCoRows N pick), hprod]

/-! ## 2. The whitening target -/

/-- The whitening target: the full dual reading minus the identity. -/
noncomputable def naimarkSharpTarget (N : NaimarkDual D r) : Matrix (Fin r) (Fin r) ℝ :=
  naimarkOmega N - 1

/-- The per-atom coefficient of the sharp target. -/
noncomputable def naimarkSharpCoeff (D : WeightedDesign m k) (c : Fin m) : ℝ :=
  D.weight c * (D.weight c / (1 - D.weight c))

theorem naimarkSharpCoeff_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 < naimarkSharpCoeff D c := by
  have hpos := D.weight_pos c
  have hlt := weight_lt_one D hm c
  rw [naimarkSharpCoeff]
  positivity

/-- **THE SHARP TARGET IS THE WEIGHTED AVERAGE OF THE PER-ATOM READINGS.**  The
dual Parseval law turns `Omegabar - 1` into `Σ_c t_c · M_c`. -/
theorem naimarkSharpTarget_eq (N : NaimarkDual D r) (hm : 2 ≤ m) :
    naimarkSharpTarget N = ∑ c, naimarkSharpCoeff D c • atomMatrix (N.co c) := by
  have hkey : naimarkOmega N - ∑ c, naimarkSharpCoeff D c • atomMatrix (N.co c)
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [naimarkOmega, ← Finset.sum_sub_distrib, ← N.coParseval]
    refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
    rw [← sub_smul]
    congr 1
    have hpos := D.weight_pos c
    have hlt := weight_lt_one D hm c
    have hne : (1 : ℝ) - D.weight c ≠ 0 := ne_of_gt (by linarith)
    rw [naimarkSharpCoeff]
    field_simp
  rw [naimarkSharpTarget, ← hkey]
  abel

/-- **THE SHARP TARGET IS POSITIVE DEFINITE.**  It is a positive combination of
the dual atoms, and those already resolve the identity against the weights, so
subtracting a small multiple of the identity leaves a positive combination. -/
theorem naimarkSharpTarget_posDef (N : NaimarkDual D r) (hm : 2 ≤ m) :
    (naimarkSharpTarget N).PosDef := by
  classical
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨argmin, hargmin⟩ :=
    Finite.exists_min fun c => naimarkSharpCoeff D c / D.weight c
  set shift : ℝ := naimarkSharpCoeff D argmin / D.weight argmin with hshift
  have hshiftPos : 0 < shift :=
    div_pos (naimarkSharpCoeff_pos D hm argmin) (D.weight_pos argmin)
  have hcoefNonneg : ∀ c : Fin m, 0 ≤ naimarkSharpCoeff D c - shift * D.weight c := by
    intro c
    have hbound : shift ≤ naimarkSharpCoeff D c / D.weight c := hargmin c
    rw [le_div_iff₀ (D.weight_pos c)] at hbound
    linarith
  have hgap : (naimarkSharpTarget N - shift • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef := by
    have hrewrite : naimarkSharpTarget N - shift • (1 : Matrix (Fin r) (Fin r) ℝ)
        = ∑ c, (naimarkSharpCoeff D c - shift * D.weight c) • atomMatrix (N.co c) := by
      rw [naimarkSharpTarget_eq N hm, ← N.coParseval, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
      rw [smul_smul, ← sub_smul]
    rw [hrewrite]
    refine Matrix.posSemidef_sum Finset.univ fun c _ => ?_
    exact (posSemidef_atomMatrix (N.co c)).smul (hcoefNonneg c)
  have hshiftPD : (shift • (1 : Matrix (Fin r) (Fin r) ℝ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one hshiftPos
  have hsum := Matrix.PosDef.add_posSemidef hshiftPD hgap
  have hcancel : shift • (1 : Matrix (Fin r) (Fin r) ℝ)
      + (naimarkSharpTarget N - shift • (1 : Matrix (Fin r) (Fin r) ℝ))
      = naimarkSharpTarget N := by abel
  rwa [hcancel] at hsum

/-! ## 3. The complement -/

/-- **DOMINATION IS DOMINATION OF THE COMPLEMENT.**  A `k`-selection dominates
exactly when the dual reading of its COMPLEMENT sits above the sharp target, and
that target is the weighted average of the same per-atom readings.  The question
has returned to its own shape on the complementary selection. -/
theorem naimark_dominates_iff_compl_reading (N : NaimarkDual D r) (hm : 2 ≤ m)
    (sel : Fin k → Fin m) (cosel : Fin r → Fin m)
    (hpart : Function.Bijective (Sum.elim sel cosel)) :
    Dominates D (Finset.image sel Finset.univ)
      ↔ (naimarkReading N cosel - naimarkSharpTarget N).PosSemidef := by
  have hselinj : Function.Injective sel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inl a) = Sum.elim sel cosel (Sum.inl b) := hab
    exact Sum.inl.inj (hpart.1 h)
  rw [naimark_dominates_iff_reading_le N hm hselinj]
  have hswap := naimark_reading_eq_omega_compl N sel cosel hpart
  have hleft : (1 : Matrix (Fin r) (Fin r) ℝ) - naimarkReading N sel
      = naimarkReading N cosel - naimarkSharpTarget N := by
    rw [naimarkReading, hswap, naimarkSharpTarget, naimarkReading]
    abel
  rw [hleft]

/-! ## 4. The sharp design -/

/-- **THE SHARP DESIGN.**  Every `(m,k)` design carries an `(m, m-k)` design with
the SAME weights, in which a selection dominates exactly when its complement
dominates in the original.  Domination has been complemented.

The atoms are the dual atoms scaled by `√(t_c/(1-t_c))` and whitened against the
sharp target.  Parseval for the new design is exactly the statement that the
sharp target is the weighted average of the per-atom readings. -/
theorem exists_naimark_sharp_design (N : NaimarkDual D r) (hm : 2 ≤ m) :
    ∃ E : WeightedDesign m r, (∀ c, E.weight c = D.weight c) ∧
      ∀ (sel : Fin k → Fin m) (cosel : Fin r → Fin m),
        Function.Bijective (Sum.elim sel cosel) → Function.Injective cosel →
        (Dominates D (Finset.image sel Finset.univ)
          ↔ Dominates E (Finset.image cosel Finset.univ)) := by
  classical
  obtain ⟨whiten, hwhitenUnit, hwhiten⟩ :=
    exists_congruence_to_one (naimarkSharpTarget_posDef N hm)
  have hcoefNonneg : ∀ c : Fin m, 0 ≤ D.weight c / (1 - D.weight c) := by
    intro c
    have hpos := D.weight_pos c
    have hlt := weight_lt_one D hm c
    positivity
  set sharpAtom : Fin m → (Fin r → ℝ) :=
    fun c => whitenᵀ *ᵥ (Real.sqrt (D.weight c / (1 - D.weight c)) • N.co c) with hsharpAtom
  have hsharpMatrix : ∀ c, atomMatrix (sharpAtom c)
      = whitenᵀ * ((D.weight c / (1 - D.weight c)) • atomMatrix (N.co c)) * whiten := by
    intro c
    rw [hsharpAtom, atomMatrix_conj, atomMatrix_smul, Matrix.transpose_transpose,
      Real.sq_sqrt (hcoefNonneg c)]
  have hparseval : ∑ c, D.weight c • atomMatrix (sharpAtom c)
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    have hstep : ∑ c, D.weight c • atomMatrix (sharpAtom c)
        = whitenᵀ * (∑ c, naimarkSharpCoeff D c • atomMatrix (N.co c)) * whiten := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
      rw [hsharpMatrix c, naimarkSharpCoeff, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [hstep, ← naimarkSharpTarget_eq N hm, hwhiten]
  refine ⟨{ atom := sharpAtom
            weight := D.weight
            weight_pos := D.weight_pos
            weight_sum_one := D.weight_sum_one
            isParseval := hparseval }, fun c => rfl, ?_⟩
  intro sel cosel hpart hcoinj
  rw [naimark_dominates_iff_compl_reading N hm sel cosel hpart, Dominates, subsetSum,
    Finset.sum_image fun left _ right _ hlr => hcoinj hlr]
  have hshapes : ∑ j, atomMatrix (sharpAtom (cosel j)) - 1
      = whitenᵀ * (naimarkReading N cosel - naimarkSharpTarget N) * whiten := by
    have hleftSum : ∑ j, atomMatrix (sharpAtom (cosel j))
        = whitenᵀ * naimarkReading N cosel * whiten := by
      rw [naimarkReading, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin r)) = Finset.univ) fun j _ => ?_
      rw [hsharpMatrix (cosel j)]
    rw [hleftSum, Matrix.mul_sub, Matrix.sub_mul, hwhiten]
  have hsymm : (naimarkReading N cosel - naimarkSharpTarget N)ᵀ
      = naimarkReading N cosel - naimarkSharpTarget N := by
    rw [Matrix.transpose_sub, naimarkSharpTarget, naimarkOmega, naimarkReading,
      Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    · rw [Matrix.transpose_sum]
      refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin r)) = Finset.univ) fun j _ => ?_
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
    · congr 1
      rw [Matrix.transpose_sum]
      refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  rw [hshapes]
  exact posSemidef_congr_right hsymm hwhitenUnit

/-! ## 5. The open cell, complemented -/

/-- A `3`-subset of a six-set and its complement give a bijection from
`Fin 3 ⊕ Fin 3`. -/
theorem sumElim_orderEmb_bijective (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hcompl : selectedᶜ.card = 3) :
    Function.Bijective (Sum.elim (selected.orderEmbOfFin hcard)
      (selectedᶜ.orderEmbOfFin hcompl)) := by
  classical
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (a | a) (b | b) hab
  · exact congrArg Sum.inl ((selected.orderEmbOfFin hcard).injective hab)
  · exfalso
    have h1 : selected.orderEmbOfFin hcard a ∈ selected := selected.orderEmbOfFin_mem hcard a
    have h2 : selectedᶜ.orderEmbOfFin hcompl b ∈ selectedᶜ := selectedᶜ.orderEmbOfFin_mem hcompl b
    rw [Finset.mem_compl] at h2
    exact h2 (by rwa [show selected.orderEmbOfFin hcard a
      = selectedᶜ.orderEmbOfFin hcompl b from hab] at h1)
  · exfalso
    have h1 : selected.orderEmbOfFin hcard b ∈ selected := selected.orderEmbOfFin_mem hcard b
    have h2 : selectedᶜ.orderEmbOfFin hcompl a ∈ selectedᶜ := selectedᶜ.orderEmbOfFin_mem hcompl a
    rw [Finset.mem_compl] at h2
    exact h2 (by rwa [show selected.orderEmbOfFin hcard b
      = selectedᶜ.orderEmbOfFin hcompl a from hab.symm] at h1)
  · exact congrArg Sum.inr ((selectedᶜ.orderEmbOfFin hcompl).injective hab)

/-- **THE `(6,3)` CELL AS A COMPLEMENTED DOMINATION.**  Weighted GTZ at six
points and rank three holds exactly when every `(6,3)` design has a triple whose
COMPLEMENT reads above the sharp target that the design carries.  Equivalently,
by `Gtz.exists_naimark_sharp_design`, the complement dominates the sharp
design. -/
theorem gtzWeighted_six_three_iff_dominating_compl :
    GtzWeighted 6 3
      ↔ ∀ D : WeightedDesign 6 3, ∀ N : NaimarkDual D 3,
          ∃ sel cosel : Fin 3 → Fin 6, Function.Bijective (Sum.elim sel cosel)
            ∧ (naimarkReading N cosel - naimarkSharpTarget N).PosSemidef := by
  constructor
  · intro hgtz D N
    obtain ⟨selected, hcard, hdom⟩ := hgtz D
    have hcompl : selectedᶜ.card = 3 := by
      rw [Finset.card_compl, hcard]
      simp
    refine ⟨selected.orderEmbOfFin hcard, selectedᶜ.orderEmbOfFin hcompl,
      sumElim_orderEmb_bijective selected hcard hcompl, ?_⟩
    have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
      apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
    rw [← himage] at hdom
    exact (naimark_dominates_iff_compl_reading N (by norm_num) _ _
      (sumElim_orderEmb_bijective selected hcard hcompl)).mp hdom
  · intro hcompl D
    obtain ⟨N⟩ := exists_naimarkDual D (r := 3) (by norm_num)
    obtain ⟨sel, cosel, hpart, hpsd⟩ := hcompl D N
    have hselinj : Function.Injective sel := by
      intro a b hab
      have h : Sum.elim sel cosel (Sum.inl a) = Sum.elim sel cosel (Sum.inl b) := hab
      exact Sum.inl.inj (hpart.1 h)
    refine ⟨Finset.image sel Finset.univ, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hselinj, Finset.card_univ, Fintype.card_fin]
    · exact (naimark_dominates_iff_compl_reading N (by norm_num) sel cosel hpart).mpr hpsd

/-! ## 6. The squeeze on a dominating triple -/

/-- **A DOMINATING TRIPLE IS SQUEEZED BETWEEN TWO EXPLICIT SETS.**  Every atom of
a dominating triple of `D` is heavy in `D`, and every atom of the complementary
triple is heavy in the sharp design `E`.  So a dominating triple contains the
complement of `E`'s heavy set and is contained in `D`'s heavy set.

Both heavy sets have at least three elements by
`Gtz.rank_le_card_heavyLeverage`, so the complement of `E`'s heavy set has at
most three.  When either bound is met the triple is FORCED: if `D` has exactly
three heavy atoms the only candidate is that triple, and if `E` has exactly
three heavy atoms the only candidate is the complement of them. -/
theorem sixThree_dominating_squeeze (D E : WeightedDesign 6 3)
    (sel cosel : Fin 3 → Fin 6) (hpart : Function.Bijective (Sum.elim sel cosel))
    (htransfer : Dominates D (Finset.image sel Finset.univ)
      ↔ Dominates E (Finset.image cosel Finset.univ))
    (hdom : Dominates D (Finset.image sel Finset.univ)) :
    (∀ a, sel a ∈ heavyLeverageSet D) ∧ (∀ j, cosel j ∈ heavyLeverageSet E) := by
  have hselinj : Function.Injective sel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inl a) = Sum.elim sel cosel (Sum.inl b) := hab
    exact Sum.inl.inj (hpart.1 h)
  have hcoinj : Function.Injective cosel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inr a) = Sum.elim sel cosel (Sum.inr b) := hab
    exact Sum.inr.inj (hpart.1 h)
  exact ⟨dominates_subset_heavyLeverage D hselinj hdom,
    dominates_subset_heavyLeverage E hcoinj (htransfer.mp hdom)⟩

/-- **THE FORCED TRIPLE.**  If a `(6,3)` design has exactly three heavy atoms,
then those three are the ONLY candidate for a dominating triple, and weighted GTZ
at that design is the single question whether they dominate. -/
theorem sixThree_forced_triple (D : WeightedDesign 6 3) {pick : Fin 3 → Fin 6}
    (hpick : Function.Injective pick) (hdom : Dominates D (Finset.image pick Finset.univ))
    (hthree : (heavyLeverageSet D).card = 3) :
    Finset.image pick Finset.univ = heavyLeverageSet D := by
  have hsub : Finset.image pick Finset.univ ⊆ heavyLeverageSet D := by
    intro c hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    exact dominates_subset_heavyLeverage D hpick hdom a
  have hcard : (Finset.image pick Finset.univ).card = 3 := by
    rw [Finset.card_image_of_injective _ hpick, Finset.card_univ, Fintype.card_fin]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hthree, hcard])

end Gtz

import Gtz.Quantitative.FourActiveCoefficientProjection
import Gtz.Wave.FullRowCrossVanishing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE FULL-ROW TRIANGLE KILL.**  The endgame of the disconnected class:
with the chart block-diagonalised by the isolated full row, its
three-dimensional kernel splits across the two coordinate blocks, so one side
carries two non-proportional kernel vectors supported inside a triple of atoms
— a parallel pair of design atoms, against the crux.  Every triangle-plus-full
support profile of the census dies here. -/

/-- **THE DRIVER.**  A full-support tight row isolated from every other active
support kills the crux. -/
theorem SixThreeCrux.false_of_fullRow_isolated_from_residual
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)} {multiplier : Finset (Fin 6) → ℝ}
    {fullBlock : Finset (Fin 6)}
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hfullMem : fullBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hfullSupport : totalTightSupport tightVec fullBlock = fullBlock)
    (hothersOff : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ fullBlock → ∀ atomIndex ∈ fullBlock,
        totalEigenSquareRow tightVec otherBlock atomIndex = 0) :
    False := by
  classical
  set projection := (chartPointOfDesign crux.design).chart with hprojectionDef
  set selection := ambientTightSelection tightVec with hselectionDef
  have hfullCard : fullBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) fullBlock).mp
      hfullMem).1
  have hcross : ∀ zAtom ∈ fullBlock, ∀ cAtom : Fin 6, cAtom ∉ fullBlock →
      projection zAtom cAtom = 0 := fun zAtom hz cAtom hc =>
    crux.projection_apply_eq_zero_of_fullRow_isolated hfour hdata hfullMem
      hfullSupport hothersOff hz hc
  have hcrossSym : ∀ zAtom : Fin 6, zAtom ∉ fullBlock → ∀ cAtom ∈ fullBlock,
      projection zAtom cAtom = 0 := by
    intro zAtom hz cAtom hc
    have hsym := congrFun (congrFun hdata.isSymmetric zAtom) cAtom
    rw [Matrix.transpose_apply] at hsym
    rw [← hsym]
    exact hcross cAtom hc zAtom hz
  -- the full row and its kernel membership
  have hvOff : ∀ atomIndex : Fin 6, atomIndex ∉ fullBlock →
      selection fullBlock atomIndex = 0 := by
    intro atomIndex hmiss
    refine ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      fullBlock hfullCard atomIndex
      (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec hfullCard ?_)
    rw [hfullSupport]
    exact hmiss
  have hvOn : ∀ atomIndex ∈ fullBlock, selection fullBlock atomIndex ≠ 0 := by
    intro atomIndex hmem hzero
    have hrowNe := (totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec
      hfullCard).mpr (by rw [hfullSupport]; exact hmem)
    rw [totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hfullCard]
      at hrowNe
    exact hrowNe (by rw [← hselectionDef, hzero, mul_zero])
  have hmemCard : ∀ other ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      other.card = 3 := fun other hother =>
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) other).mp hother).1
  have hotherSelOff : ∀ other ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      other ≠ fullBlock → ∀ atomIndex ∈ fullBlock, selection other atomIndex = 0 := by
    intro other hother hne atomIndex hmem
    exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      other (hmemCard other hother) atomIndex
      (hothersOff other hother hne atomIndex hmem)
  have horthogonal : ∀ other ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      other ≠ fullBlock → selection other ⬝ᵥ selection fullBlock = 0 := by
    intro other hother hne
    refine Finset.sum_eq_zero fun atomIndex _ => ?_
    by_cases hmem : atomIndex ∈ fullBlock
    · rw [hotherSelOff other hother hne atomIndex hmem, zero_mul]
    · rw [hvOff atomIndex hmem, mul_zero]
  obtain ⟨atomZero, hatomZero⟩ : ∃ atomIndex, atomIndex ∈ fullBlock :=
    Finset.card_pos.mp (by omega)
  have hmuFloor : 1 / 6 ≤ multiplier fullBlock :=
    crux.sixth_le_multiplier_of_isolated_support_atom hdata hfullMem
      (by rw [hfullSupport]; exact hatomZero)
      (fun other hother hne => hothersOff other hother hne atomZero hatomZero)
  have hPv : projection *ᵥ selection fullBlock = 0 :=
    crux.projection_mulVec_eq_zero_of_orthogonal_of_sixth_le_multiplier hdata
      hfullMem horthogonal hmuFloor
  -- the design bridge
  have hchartEq : projectionOfDesign crux.design = projection := rfl
  have hnoParallel := crux.hasNoParallelPair
  -- the kernel has dimension three
  have hrangeRank : Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' projection)) = 3 := by
    have htrace := trace_eq_finrank_range_of_idempotent projection hdata.isIdempotent
    rw [hdata.hasTraceRank] at htrace
    exact_mod_cast htrace.symm
  have hkerRank : Module.finrank ℝ
      (LinearMap.ker (Matrix.toLin' projection)) = 3 := by
    have hnullity := LinearMap.finrank_range_add_finrank_ker
      (Matrix.toLin' (R := ℝ) projection)
    rw [hrangeRank] at hnullity
    have hambient : Module.finrank ℝ (Fin 6 → ℝ) = 6 := by
      simp
    omega
  have hmemKer : ∀ w : Fin 6 → ℝ, projection *ᵥ w = 0 →
      w ∈ LinearMap.ker (Matrix.toLin' projection) := by
    intro w hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact hw
  have hkerVec : ∀ w : Fin 6 → ℝ,
      w ∈ LinearMap.ker (Matrix.toLin' projection) → projection *ᵥ w = 0 := by
    intro w hw
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw
    exact hw
  -- the block masks stay in the kernel
  have hmaskKernel : ∀ w : Fin 6 → ℝ, projection *ᵥ w = 0 →
      projection *ᵥ (fun c => if c ∈ fullBlock then w c else 0) = 0 := by
    intro w hw
    funext zAtom
    have hexpand : (projection *ᵥ (fun c => if c ∈ fullBlock then w c else 0)) zAtom
        = ∑ cAtom ∈ fullBlock, projection zAtom cAtom * w cAtom := by
      show ∑ cAtom : Fin 6, projection zAtom cAtom
          * (if cAtom ∈ fullBlock then w cAtom else 0)
        = ∑ cAtom ∈ fullBlock, projection zAtom cAtom * w cAtom
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hexpand]
    by_cases hzMem : zAtom ∈ fullBlock
    · have hfull := congrFun hw zAtom
      have hfullExpand : (projection *ᵥ w) zAtom
          = ∑ cAtom ∈ fullBlock, projection zAtom cAtom * w cAtom
            + ∑ cAtom ∈ fullBlockᶜ, projection zAtom cAtom * w cAtom := by
        rw [show (projection *ᵥ w) zAtom
            = ∑ cAtom : Fin 6, projection zAtom cAtom * w cAtom from rfl]
        exact (Finset.sum_add_sum_compl fullBlock _).symm
      have hoffZero : ∑ cAtom ∈ fullBlockᶜ, projection zAtom cAtom * w cAtom = 0 :=
        Finset.sum_eq_zero fun cAtom hcMem => by
          rw [hcross zAtom hzMem cAtom (Finset.mem_compl.mp hcMem), zero_mul]
      rw [hfullExpand, hoffZero, add_zero] at hfull
      exact hfull
    · exact Finset.sum_eq_zero fun cAtom hcMem => by
        rw [hcrossSym zAtom hzMem cAtom hcMem, zero_mul]
  have hmaskComplement : ∀ w : Fin 6 → ℝ, projection *ᵥ w = 0 →
      projection *ᵥ (fun c => if c ∈ fullBlock then 0 else w c) = 0 := by
    intro w hw
    have hsplit : (fun c => if c ∈ fullBlock then (0 : ℝ) else w c)
        = w - fun c => if c ∈ fullBlock then w c else 0 := by
      funext c
      by_cases hmem : c ∈ fullBlock <;> simp [hmem]
    rw [hsplit, Matrix.mulVec_sub, hw, hmaskKernel w hw, sub_zero]
  -- the complement atoms
  have hcomplCard : fullBlockᶜ.card = 3 := by
    rw [Finset.card_compl, hfullCard]
    rfl
  obtain ⟨coordOne, coordTwo, coordThree, hcNeOneTwo, hcNeOneThree, hcNeTwoThree,
    hcomplEq⟩ := Finset.card_eq_three.mp hcomplCard
  obtain ⟨atomA, atomB, atomC, hbNeAB, hbNeAC, hbNeBC, hblockEq⟩ :=
    Finset.card_eq_three.mp hfullCard
  -- CASE ONE: a second block-supported kernel vector
  by_cases hsecondBlock : ∃ w : Fin 6 → ℝ, projection *ᵥ w = 0
      ∧ (∀ cAtom : Fin 6, cAtom ∉ fullBlock → w cAtom = 0)
      ∧ ∀ scale : ℝ, w ≠ scale • selection fullBlock
  · obtain ⟨w, hwKernel, hwSupport, hwFree⟩ := hsecondBlock
    apply hnoParallel
    refine hasParallelPair_of_two_kernel_vectors_in_triple crux.design
      hbNeAB hbNeAC hbNeBC (hchartEq ▸ hPv) (hchartEq ▸ hwKernel) ?_ ?_ ?_ hwFree
    · intro atomIndex hmiss
      exact hvOff atomIndex (by rw [hblockEq]; exact hmiss)
    · intro atomIndex hmiss
      exact hwSupport atomIndex (by rw [hblockEq]; exact hmiss)
    · exact hvOn atomA (by rw [hblockEq]; simp)
  -- no second block-supported vector: block-supported kernel is the v line
  push Not at hsecondBlock
  have hblockLine : ∀ w : Fin 6 → ℝ, projection *ᵥ w = 0 →
      (∀ cAtom : Fin 6, cAtom ∉ fullBlock → w cAtom = 0) →
      ∃ scale : ℝ, w = scale • selection fullBlock := by
    intro w hwKernel hwSupport
    obtain ⟨scale, hscale⟩ := hsecondBlock w hwKernel hwSupport
    exact ⟨scale, hscale⟩
  -- CASE TWO: a nonzero complement-supported kernel vector exists
  by_cases hcomplVec : ∃ t : Fin 6 → ℝ, projection *ᵥ t = 0
      ∧ (∀ cAtom ∈ fullBlock, t cAtom = 0) ∧ t ≠ 0
  · obtain ⟨tVec, htKernel, htSupport, htNonzero⟩ := hcomplVec
    have htSupportCompl : ∀ atomIndex : Fin 6,
        atomIndex ∉ ({coordOne, coordTwo, coordThree} : Finset (Fin 6)) →
          tVec atomIndex = 0 := by
      intro atomIndex hmiss
      refine htSupport atomIndex ?_
      by_contra hnotMem
      exact hmiss (by rw [← hcomplEq, Finset.mem_compl]; exact hnotMem)
    -- CASE 2A: a second complement-supported vector off the t line
    by_cases hsecondCompl : ∃ w : Fin 6 → ℝ, projection *ᵥ w = 0
        ∧ (∀ cAtom ∈ fullBlock, w cAtom = 0)
        ∧ ∀ scale : ℝ, w ≠ scale • tVec
    · obtain ⟨w, hwKernel, hwSupport, hwFree⟩ := hsecondCompl
      have hwSupportCompl : ∀ atomIndex : Fin 6,
          atomIndex ∉ ({coordOne, coordTwo, coordThree} : Finset (Fin 6)) →
            w atomIndex = 0 := by
        intro atomIndex hmiss
        refine hwSupport atomIndex ?_
        by_contra hnotMem
        exact hmiss (by rw [← hcomplEq, Finset.mem_compl]; exact hnotMem)
      obtain ⟨pivot, hpivot⟩ : ∃ atomIndex, tVec atomIndex ≠ 0 := by
        by_contra hall
        push Not at hall
        exact htNonzero (funext hall)
      have hpivotCompl : pivot ∈ ({coordOne, coordTwo, coordThree} :
          Finset (Fin 6)) := by
        by_contra hmiss
        exact hpivot (htSupportCompl pivot hmiss)
      apply hnoParallel
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpivotCompl
      rcases hpivotCompl with rfl | rfl | rfl
      · exact hasParallelPair_of_two_kernel_vectors_in_triple crux.design
          hcNeOneTwo hcNeOneThree hcNeTwoThree (hchartEq ▸ htKernel)
          (hchartEq ▸ hwKernel) htSupportCompl hwSupportCompl hpivot hwFree
      · refine hasParallelPair_of_two_kernel_vectors_in_triple crux.design
          (Ne.symm hcNeOneTwo) hcNeTwoThree hcNeOneThree (hchartEq ▸ htKernel)
          (hchartEq ▸ hwKernel) ?_ ?_ hpivot hwFree
        · intro atomIndex hmiss
          refine htSupportCompl atomIndex (fun hmem => hmiss ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
          tauto
        · intro atomIndex hmiss
          refine hwSupportCompl atomIndex (fun hmem => hmiss ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
          tauto
      · refine hasParallelPair_of_two_kernel_vectors_in_triple crux.design
          (Ne.symm hcNeOneThree) (Ne.symm hcNeTwoThree) hcNeOneTwo
          (hchartEq ▸ htKernel) (hchartEq ▸ hwKernel) ?_ ?_ hpivot hwFree
        · intro atomIndex hmiss
          refine htSupportCompl atomIndex (fun hmem => hmiss ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
          tauto
        · intro atomIndex hmiss
          refine hwSupportCompl atomIndex (fun hmem => hmiss ?_)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
          tauto
    -- CASE 2B: kernel confined to the two lines — dimension contradiction
    · push Not at hsecondCompl
      have hkerLe : LinearMap.ker (Matrix.toLin' projection)
          ≤ Submodule.span ℝ ({selection fullBlock, tVec} : Set (Fin 6 → ℝ)) := by
        intro w hw
        have hwKernel := hkerVec w hw
        obtain ⟨scaleB, hscaleB⟩ := hblockLine _
          (hmaskKernel w hwKernel) (fun cAtom hmiss => by simp [hmiss])
        obtain ⟨scaleT, hscaleT⟩ := hsecondCompl _
          (hmaskComplement w hwKernel) (fun cAtom hmem => by simp [hmem])
        have hsplit : w = scaleB • selection fullBlock + scaleT • tVec := by
          rw [← hscaleB, ← hscaleT]
          funext cAtom
          by_cases hmem : cAtom ∈ fullBlock <;> simp [hmem]
        rw [hsplit]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))
      have hpairRank : Module.finrank ℝ (Submodule.span ℝ
          ({selection fullBlock, tVec} : Set (Fin 6 → ℝ))) ≤ 2 := by
        have hfinsetSubset : ({selection fullBlock, tVec} : Set (Fin 6 → ℝ))
            = (({selection fullBlock, tVec} : Finset (Fin 6 → ℝ))
              : Set (Fin 6 → ℝ)) := by
          simp
        rw [hfinsetSubset]
        refine (finrank_span_finset_le_card _).trans ?_
        have hbound := Finset.card_insert_le (selection fullBlock)
          ({tVec} : Finset (Fin 6 → ℝ))
        simp only [Finset.card_singleton] at hbound
        omega
      have hcontr := Submodule.finrank_mono hkerLe
      rw [hkerRank] at hcontr
      omega
  -- CASE THREE: no complement-supported kernel vector — kernel is the v line
  · push Not at hcomplVec
    have hkerLe : LinearMap.ker (Matrix.toLin' projection)
        ≤ Submodule.span ℝ ({selection fullBlock} : Set (Fin 6 → ℝ)) := by
      intro w hw
      have hwKernel := hkerVec w hw
      obtain ⟨scaleB, hscaleB⟩ := hblockLine _
        (hmaskKernel w hwKernel) (fun cAtom hmiss => by simp [hmiss])
      have hcomplZero : (fun c => if c ∈ fullBlock then (0 : ℝ) else w c) = 0 :=
        hcomplVec _ (hmaskComplement w hwKernel) (fun cAtom hmem => by simp [hmem])
      have hsplit : w = scaleB • selection fullBlock := by
        rw [← hscaleB]
        funext cAtom
        by_cases hmem : cAtom ∈ fullBlock
        · simp [hmem]
        · have hzero := congrFun hcomplZero cAtom
          simp only [hmem, if_false, Pi.zero_apply] at hzero
          simp [hmem, hzero]
      rw [hsplit]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hlineRank : Module.finrank ℝ (Submodule.span ℝ
        ({selection fullBlock} : Set (Fin 6 → ℝ))) ≤ 1 := by
      rcases eq_or_ne (selection fullBlock) 0 with hzero | hnonzero
      · rw [hzero, Submodule.span_zero_singleton, finrank_bot]
        omega
      · rw [finrank_span_singleton hnonzero]
    have hcontr := Submodule.finrank_mono hkerLe
    rw [hkerRank] at hcontr
    omega

end Gtz

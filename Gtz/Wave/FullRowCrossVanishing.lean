import Gtz.Wave.ResidualRowSpanHarvest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE FULL ROW BLOCK-DIAGONALISES THE CHART.**  When one active block
carries a full-support tight row whose atoms meet no other active support, the
isolated-row core annihilates the row under the projection.  The commutation
identity then reads, entry by entry: against the invertible residual row
system, every captured residual row vanishes on the full block, and since the
residual rows span the off-block coordinate space, the chart's cross block
vanishes outright.  This is the block-diagonalisation half of the full-row
triangle kill; the kernel-splitting endgame consumes its conclusion. -/

/-- **CROSS-BLOCK VANISHING.**  The chart entries between the full block and
its complement vanish. -/
theorem SixThreeCrux.projection_apply_eq_zero_of_fullRow_isolated
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
        totalEigenSquareRow tightVec otherBlock atomIndex = 0)
    {zAtom cAtom : Fin 6} (hzMem : zAtom ∈ fullBlock) (hcMiss : cAtom ∉ fullBlock) :
    (chartPointOfDesign crux.design).chart zAtom cAtom = 0 := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign crux.design) with hfamilyDef
  set projection := (chartPointOfDesign crux.design).chart with hprojectionDef
  set selection := ambientTightSelection tightVec with hselectionDef
  have hfullCard : fullBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) fullBlock).mp
      hfullMem).1
  have hmemCard : ∀ other ∈ family, other.card = 3 := fun other hother =>
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) other).mp hother).1
  have hvOff : ∀ atomIndex : Fin 6, atomIndex ∉ fullBlock →
      selection fullBlock atomIndex = 0 := by
    intro atomIndex hmiss
    refine ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      fullBlock hfullCard atomIndex
      (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec hfullCard ?_)
    rw [hfullSupport]
    exact hmiss
  have hotherSelOff : ∀ other ∈ family, other ≠ fullBlock →
      ∀ atomIndex ∈ fullBlock, selection other atomIndex = 0 := by
    intro other hother hne atomIndex hmem
    exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      other (hmemCard other hother) atomIndex
      (hothersOff other hother hne atomIndex hmem)
  have horthogonal : ∀ other ∈ family, other ≠ fullBlock →
      selection other ⬝ᵥ selection fullBlock = 0 := by
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
  -- residual enumeration
  have heraseCard : (family.erase fullBlock).card = 3 := by
    rw [Finset.card_erase_of_mem hfullMem, hfour]
  obtain ⟨blockOne, blockTwo, blockThree, hneOneTwo, hneOneThree, hneTwoThree,
    heraseEq⟩ := Finset.card_eq_three.mp heraseCard
  have hmemEraseOne : blockOne ∈ family.erase fullBlock := by
    rw [heraseEq]; simp
  have hmemEraseTwo : blockTwo ∈ family.erase fullBlock := by
    rw [heraseEq]; simp
  have hmemEraseThree : blockThree ∈ family.erase fullBlock := by
    rw [heraseEq]; simp
  have hmemOne : blockOne ∈ family := Finset.mem_of_mem_erase hmemEraseOne
  have hmemTwo : blockTwo ∈ family := Finset.mem_of_mem_erase hmemEraseTwo
  have hmemThree : blockThree ∈ family := Finset.mem_of_mem_erase hmemEraseThree
  have hneOneFull : blockOne ≠ fullBlock := Finset.ne_of_mem_erase hmemEraseOne
  have hneTwoFull : blockTwo ≠ fullBlock := Finset.ne_of_mem_erase hmemEraseTwo
  have hneThreeFull : blockThree ≠ fullBlock := Finset.ne_of_mem_erase hmemEraseThree
  have hfullNotMemTriple : fullBlock ∉ ({blockOne, blockTwo, blockThree} :
      Finset (Finset (Fin 6))) := by
    intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with heq | heq | heq
    · exact hneOneFull heq.symm
    · exact hneTwoFull heq.symm
    · exact hneThreeFull heq.symm
  have hfamilyList : family = insert fullBlock {blockOne, blockTwo, blockThree} := by
    rw [← heraseEq, Finset.insert_erase hfullMem]
  -- the residual span floor and independence
  have hspanFloor := crux.three_le_finrank_span_erase_of_card_four hdata hfullMem
  have himageEq : ((family.erase fullBlock).image selection : Finset (Fin 6 → ℝ))
      = {selection blockOne, selection blockTwo, selection blockThree} := by
    rw [heraseEq, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  have hsetEq : (({selection blockOne, selection blockTwo, selection blockThree}
      : Finset (Fin 6 → ℝ)) : Set (Fin 6 → ℝ))
      = Set.range ![selection blockOne, selection blockTwo, selection blockThree] := by
    ext row
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨index, rfl⟩
      fin_cases index
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hrangeFloor : 3 ≤ Module.finrank ℝ (Submodule.span ℝ
      (Set.range ![selection blockOne, selection blockTwo, selection blockThree])) := by
    rw [← hsetEq, ← himageEq]
    exact hspanFloor
  have hindependent : LinearIndependent ℝ
      ![selection blockOne, selection blockTwo, selection blockThree] :=
    linearIndependent_iff_card_le_finrank_span.mpr (by
      simpa [Set.finrank] using hrangeFloor)
  have hmuPos := crux.activeWeight_pos_of_identity_family_card_four hdata hfour
  -- the captured residual rows vanish on the full block
  have hcapturedOff : ∀ wAtom ∈ fullBlock,
      (projection *ᵥ selection blockOne) wAtom = 0
      ∧ (projection *ᵥ selection blockTwo) wAtom = 0
      ∧ (projection *ᵥ selection blockThree) wAtom = 0 := by
    intro wAtom hwMem
    have hcombination : ∀ yAtom : Fin 6,
        multiplier blockOne * (projection *ᵥ selection blockOne) wAtom
            * selection blockOne yAtom
          + multiplier blockTwo * (projection *ᵥ selection blockTwo) wAtom
            * selection blockTwo yAtom
          + multiplier blockThree * (projection *ᵥ selection blockThree) wAtom
            * selection blockThree yAtom = 0 := by
      intro yAtom
      by_cases hyMem : yAtom ∈ fullBlock
      · rw [hotherSelOff blockOne hmemOne hneOneFull yAtom hyMem,
          hotherSelOff blockTwo hmemTwo hneTwoFull yAtom hyMem,
          hotherSelOff blockThree hmemThree hneThreeFull yAtom hyMem]
        ring
      · have hcommute := congrFun (congrFun hdata.assembly_commutes wAtom) yAtom
        have hrowW : ∀ dAtom : Fin 6,
            chartMultiplierAssembly family multiplier selection wAtom dAtom
              = multiplier fullBlock * selection fullBlock wAtom
                  * selection fullBlock dAtom := by
          intro dAtom
          rw [chartMultiplierAssembly_apply, hfamilyList,
            Finset.sum_insert hfullNotMemTriple,
            Finset.sum_insert (by simp [hneOneTwo, hneOneThree]),
            Finset.sum_insert (by simp [hneTwoThree]), Finset.sum_singleton,
            hotherSelOff blockOne hmemOne hneOneFull wAtom hwMem,
            hotherSelOff blockTwo hmemTwo hneTwoFull wAtom hwMem,
            hotherSelOff blockThree hmemThree hneThreeFull wAtom hwMem]
          ring
        have hcolY : ∀ dAtom : Fin 6,
            chartMultiplierAssembly family multiplier selection dAtom yAtom
              = multiplier blockOne * selection blockOne dAtom
                  * selection blockOne yAtom
                + multiplier blockTwo * selection blockTwo dAtom
                  * selection blockTwo yAtom
                + multiplier blockThree * selection blockThree dAtom
                  * selection blockThree yAtom := by
          intro dAtom
          rw [chartMultiplierAssembly_apply, hfamilyList,
            Finset.sum_insert hfullNotMemTriple,
            Finset.sum_insert (by simp [hneOneTwo, hneOneThree]),
            Finset.sum_insert (by simp [hneTwoThree]), Finset.sum_singleton,
            hvOff yAtom hyMem]
          ring
        have hrhsZero : (chartMultiplierAssembly family multiplier selection
            * projection) wAtom yAtom = 0 := by
          rw [Matrix.mul_apply]
          have hterm : ∀ dAtom : Fin 6,
              chartMultiplierAssembly family multiplier selection wAtom dAtom
                  * projection dAtom yAtom
                = multiplier fullBlock * selection fullBlock wAtom
                    * (selection fullBlock dAtom * projection dAtom yAtom) := by
            intro dAtom
            rw [hrowW dAtom]
            ring
          rw [Finset.sum_congr rfl fun dAtom _ => hterm dAtom, ← Finset.mul_sum]
          have hPvY : ∑ dAtom : Fin 6,
              selection fullBlock dAtom * projection dAtom yAtom = 0 := by
            have hvec : ∑ dAtom : Fin 6,
                selection fullBlock dAtom * projection dAtom yAtom
                = (projectionᵀ *ᵥ selection fullBlock) yAtom := by
              simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
              exact Finset.sum_congr rfl fun dAtom _ => by ring
            rw [hvec, hdata.isSymmetric, hPv]
            rfl
          rw [hPvY, mul_zero]
        have hlhs : (projection * chartMultiplierAssembly family multiplier selection)
            wAtom yAtom
            = multiplier blockOne * (projection *ᵥ selection blockOne) wAtom
                * selection blockOne yAtom
              + multiplier blockTwo * (projection *ᵥ selection blockTwo) wAtom
                * selection blockTwo yAtom
              + multiplier blockThree * (projection *ᵥ selection blockThree) wAtom
                * selection blockThree yAtom := by
          rw [Matrix.mul_apply]
          have hterm : ∀ dAtom : Fin 6,
              projection wAtom dAtom
                  * chartMultiplierAssembly family multiplier selection dAtom yAtom
                = multiplier blockOne * (projection wAtom dAtom
                      * selection blockOne dAtom) * selection blockOne yAtom
                  + multiplier blockTwo * (projection wAtom dAtom
                      * selection blockTwo dAtom) * selection blockTwo yAtom
                  + multiplier blockThree * (projection wAtom dAtom
                      * selection blockThree dAtom) * selection blockThree yAtom := by
            intro dAtom
            rw [hcolY dAtom]
            ring
          rw [Finset.sum_congr rfl fun dAtom _ => hterm dAtom]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          have hgroup : ∀ residualBlock : Finset (Fin 6),
              ∑ dAtom : Fin 6, multiplier residualBlock * (projection wAtom dAtom
                  * selection residualBlock dAtom) * selection residualBlock yAtom
                = multiplier residualBlock
                    * (projection *ᵥ selection residualBlock) wAtom
                    * selection residualBlock yAtom := by
            intro residualBlock
            have hmul : (projection *ᵥ selection residualBlock) wAtom
                = ∑ dAtom : Fin 6, projection wAtom dAtom
                    * selection residualBlock dAtom := rfl
            rw [hmul, Finset.mul_sum, Finset.sum_mul]
          rw [hgroup blockOne, hgroup blockTwo, hgroup blockThree]
        rw [hlhs, hrhsZero] at hcommute
        exact hcommute
    have hsumZero : ∑ index : Fin 3,
        (![multiplier blockOne * (projection *ᵥ selection blockOne) wAtom,
            multiplier blockTwo * (projection *ᵥ selection blockTwo) wAtom,
            multiplier blockThree * (projection *ᵥ selection blockThree) wAtom] index)
          • (![selection blockOne, selection blockTwo, selection blockThree] index)
        = 0 := by
      rw [Fin.sum_univ_three]
      funext yAtom
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply]
      linear_combination hcombination yAtom
    have hallZero := Fintype.linearIndependent_iff.mp hindependent _ hsumZero
    have hzeroOne := hallZero 0
    have hzeroTwo := hallZero 1
    have hzeroThree := hallZero 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hzeroOne hzeroTwo hzeroThree
    refine ⟨?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp hzeroOne with hmu | hcap
      · exact absurd hmu (ne_of_gt (hmuPos blockOne hmemOne))
      · exact hcap
    · rcases mul_eq_zero.mp hzeroTwo with hmu | hcap
      · exact absurd hmu (ne_of_gt (hmuPos blockTwo hmemTwo))
      · exact hcap
    · rcases mul_eq_zero.mp hzeroThree with hmu | hcap
      · exact absurd hmu (ne_of_gt (hmuPos blockThree hmemThree))
      · exact hcap
  -- the complement coordinates and the singles sandwich
  have hcomplCard : fullBlockᶜ.card = 3 := by
    rw [Finset.card_compl, hfullCard]
    rfl
  obtain ⟨coordOne, coordTwo, coordThree, hcNeOneTwo, hcNeOneThree, hcNeTwoThree,
    hcomplEq⟩ := Finset.card_eq_three.mp hcomplCard
  have hcoordMissOne : coordOne ∉ fullBlock := by
    rw [← Finset.mem_compl, hcomplEq]; simp
  have hcoordMissTwo : coordTwo ∉ fullBlock := by
    rw [← Finset.mem_compl, hcomplEq]; simp
  have hcoordMissThree : coordThree ∉ fullBlock := by
    rw [← Finset.mem_compl, hcomplEq]; simp
  have hoffRepr : ∀ vector : Fin 6 → ℝ, (∀ atom ∈ fullBlock, vector atom = 0) →
      vector = vector coordOne • Pi.single coordOne (1 : ℝ)
        + vector coordTwo • Pi.single coordTwo 1
        + vector coordThree • Pi.single coordThree 1 := by
    intro vector hvector
    funext atom
    by_cases hatomMem : atom ∈ fullBlock
    · have hneOne : atom ≠ coordOne := fun h => hcoordMissOne (h ▸ hatomMem)
      have hneTwo : atom ≠ coordTwo := fun h => hcoordMissTwo (h ▸ hatomMem)
      have hneThree : atom ≠ coordThree := fun h => hcoordMissThree (h ▸ hatomMem)
      simp [hvector atom hatomMem, hneOne, hneTwo, hneThree]
    · have hatomCompl : atom ∈ ({coordOne, coordTwo, coordThree} :
          Finset (Fin 6)) := by
        rw [← hcomplEq, Finset.mem_compl]
        exact hatomMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hatomCompl
      rcases hatomCompl with rfl | rfl | rfl
      · simp [hcNeOneTwo, hcNeOneThree]
      · simp [Ne.symm hcNeOneTwo, hcNeTwoThree]
      · simp [Ne.symm hcNeOneThree, Ne.symm hcNeTwoThree]
  have hsinglesSpan : Submodule.span ℝ
      (Set.range ![selection blockOne, selection blockTwo, selection blockThree])
      ≤ Submodule.span ℝ (Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ)) := by
    rw [Submodule.span_le]
    rintro row ⟨index, rfl⟩
    have hoff : ∀ atom ∈ fullBlock,
        (![selection blockOne, selection blockTwo, selection blockThree] index)
          atom = 0 := by
      intro atom hatomMem
      fin_cases index
      · exact hotherSelOff blockOne hmemOne hneOneFull atom hatomMem
      · exact hotherSelOff blockTwo hmemTwo hneTwoFull atom hatomMem
      · exact hotherSelOff blockThree hmemThree hneThreeFull atom hatomMem
    have hmemFirst : Pi.single coordOne (1 : ℝ) ∈ Submodule.span ℝ
        (Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ)) := Submodule.subset_span ⟨0, rfl⟩
    have hmemSecond : Pi.single coordTwo (1 : ℝ) ∈ Submodule.span ℝ
        (Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ)) := Submodule.subset_span ⟨1, rfl⟩
    have hmemThird : Pi.single coordThree (1 : ℝ) ∈ Submodule.span ℝ
        (Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ)) := Submodule.subset_span ⟨2, rfl⟩
    rw [SetLike.mem_coe, hoffRepr _ hoff]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hmemFirst) (Submodule.smul_mem _ _ hmemSecond))
      (Submodule.smul_mem _ _ hmemThird)
  have hsinglesFinset : (({Pi.single coordOne (1 : ℝ), Pi.single coordTwo 1,
      Pi.single coordThree 1} : Finset (Fin 6 → ℝ)) : Set (Fin 6 → ℝ))
      = Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ) := by
    ext row
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨index, rfl⟩
      fin_cases index
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hsinglesRank : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ))) ≤ 3 := by
    rw [← hsinglesFinset]
    refine (finrank_span_finset_le_card _).trans ?_
    refine (Finset.card_insert_le _ _).trans ?_
    have hbound := Finset.card_insert_le (Pi.single coordTwo (1 : ℝ))
      ({Pi.single coordThree 1} : Finset (Fin 6 → ℝ))
    simp only [Finset.card_singleton] at hbound
    omega
  have hspanEq : Submodule.span ℝ
      (Set.range ![selection blockOne, selection blockTwo, selection blockThree])
      = Submodule.span ℝ (Set.range (![Pi.single coordOne 1, Pi.single coordTwo 1, Pi.single coordThree 1] : Fin 3 → Fin 6 → ℝ)) := by
    refine Submodule.eq_of_le_of_finrank_le hsinglesSpan ?_
    exact le_trans hsinglesRank hrangeFloor
  -- the single at the target coordinate lies in the residual span
  have hcAtomCompl : cAtom ∈ ({coordOne, coordTwo, coordThree} :
      Finset (Fin 6)) := by
    rw [← hcomplEq, Finset.mem_compl]
    exact hcMiss
  have hsingleMem : Pi.single cAtom (1 : ℝ) ∈ Submodule.span ℝ
      (Set.range ![selection blockOne, selection blockTwo, selection blockThree]) := by
    rw [hspanEq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcAtomCompl
    rcases hcAtomCompl with rfl | rfl | rfl
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
    · exact Submodule.subset_span ⟨2, rfl⟩
  obtain ⟨weights, hweights⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hsingleMem
  have happly : (projection *ᵥ Pi.single cAtom (1 : ℝ)) zAtom = 0 := by
    rw [← hweights]
    have hexpandSum : (∑ index : Fin 3, weights index
        • ![selection blockOne, selection blockTwo, selection blockThree] index)
        = weights 0 • selection blockOne + weights 1 • selection blockTwo
          + weights 2 • selection blockThree := by
      rw [Fin.sum_univ_three]
      rfl
    rw [hexpandSum, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    obtain ⟨hcapOne, hcapTwo, hcapThree⟩ := hcapturedOff zAtom hzMem
    simp [Pi.add_apply, Pi.smul_apply, hcapOne, hcapTwo, hcapThree]
  rw [Matrix.mulVec_single] at happly
  simpa using happly

end Gtz

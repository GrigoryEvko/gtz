import Gtz.Quantitative.StrongStationarityIndexFloor
import Gtz.Quantitative.SevenThreeMaxVolume
import Gtz.Reduction.ExchangeInvariant
import Gtz.Corner.CornerFiber
import Gtz.Reduction.DiagonalRungs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-- The vector which is one off `block` and zero on `block`. -/
def complementIndicator (block : Finset (Fin 6)) : Fin 6 → ℝ :=
  fun atomIndex => if atomIndex ∈ block then 0 else 1

/-- The three coordinate axes on `block`, together with the indicator of its complement. -/
def blockComplementBasis (block : Finset (Fin 6)) :
    Option { atomIndex // atomIndex ∈ block } → (Fin 6 → ℝ) :=
  fun label => label.casesOn' (complementIndicator block)
    (fun atomIndex => Pi.single atomIndex.1 (1 : ℝ))

/-- `span(e_i, i in block) + span(1_{blockᶜ})`. -/
def blockComplementSpan (block : Finset (Fin 6)) : Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ (Set.range (blockComplementBasis block))

theorem blockComplementSpan_eq_sup (block : Finset (Fin 6)) :
    blockComplementSpan block =
      Submodule.span ℝ (Set.range fun atomIndex : { atomIndex // atomIndex ∈ block } =>
        Pi.single atomIndex.1 (1 : ℝ)) ⊔
      Submodule.span ℝ ({complementIndicator block} : Set (Fin 6 → ℝ)) := by
  classical
  have hrange : Set.range (blockComplementBasis block) =
      Set.range (fun atomIndex : { atomIndex // atomIndex ∈ block } =>
        Pi.single atomIndex.1 (1 : ℝ)) ∪ {complementIndicator block} := by
    ext vec
    constructor
    · rintro ⟨label, rfl⟩
      cases label with
      | none => exact Set.mem_union_right _ (Set.mem_singleton _)
      | some atomIndex => exact Set.mem_union_left _ ⟨atomIndex, rfl⟩
    · intro hmem
      rcases Set.mem_union _ _ _ |>.mp hmem with ⟨atomIndex, rfl⟩ | hindicator
      · exact ⟨some atomIndex, rfl⟩
      · rw [Set.mem_singleton_iff] at hindicator
        exact ⟨none, hindicator.symm⟩
  rw [blockComplementSpan, hrange, Submodule.span_union]

/-- Vectors whose coordinates are constant away from `block`. -/
def constantOffBlockSubmodule (block : Finset (Fin 6)) : Submodule ℝ (Fin 6 → ℝ) where
  carrier := { vec | ∀ first, first ∉ block → ∀ second, second ∉ block →
    vec first = vec second }
  zero_mem' := by simp
  add_mem' := by
    rintro left right hleft hright first hfirst second hsecond
    simp only [Pi.add_apply]
    rw [hleft first hfirst second hsecond, hright first hfirst second hsecond]
  smul_mem' := by
    rintro scale vec hvec first hfirst second hsecond
    simp only [Pi.smul_apply]
    rw [hvec first hfirst second hsecond]

theorem blockComplementSpan_le_constantOffBlockSubmodule (block : Finset (Fin 6)) :
    blockComplementSpan block ≤ constantOffBlockSubmodule block := by
  classical
  rw [blockComplementSpan, Submodule.span_le]
  rintro vec ⟨label, rfl⟩
  cases label with
  | none =>
      intro first hfirst second hsecond
      change complementIndicator block first = complementIndicator block second
      simp [complementIndicator, hfirst, hsecond]
  | some atomIndex =>
      intro first hfirst second hsecond
      have hfirstNe : first ≠ atomIndex.1 := by
        intro heq
        exact hfirst (heq ▸ atomIndex.2)
      have hsecondNe : second ≠ atomIndex.1 := by
        intro heq
        exact hsecond (heq ▸ atomIndex.2)
      change (Pi.single atomIndex.1 (1 : ℝ) : Fin 6 → ℝ) first =
        (Pi.single atomIndex.1 (1 : ℝ) : Fin 6 → ℝ) second
      rw [Pi.single_apply, if_neg hfirstNe,
        Pi.single_apply, if_neg hsecondNe]

theorem eq_on_complement_of_mem_blockComplementSpan (block : Finset (Fin 6))
    {vec : Fin 6 → ℝ} (hvec : vec ∈ blockComplementSpan block)
    {first second : Fin 6} (hfirst : first ∉ block) (hsecond : second ∉ block) :
    vec first = vec second :=
  blockComplementSpan_le_constantOffBlockSubmodule block hvec first hfirst second hsecond

theorem linearIndependent_blockComplementBasis (block : Finset (Fin 6))
    (hcard : block.card = 3) :
    LinearIndependent ℝ (blockComplementBasis block) := by
  classical
  let coordinateBasis : { atomIndex // atomIndex ∈ block } → (Fin 6 → ℝ) :=
    fun atomIndex => Pi.single atomIndex.1 (1 : ℝ)
  have hcoordinate : LinearIndependent ℝ coordinateBasis := by
    change LinearIndependent ℝ
      ((fun atomIndex : Fin 6 => Pi.single atomIndex (1 : ℝ)) ∘
        (fun atomIndex : { atomIndex // atomIndex ∈ block } => atomIndex.1))
    exact (Pi.linearIndependent_single_one (Fin 6) ℝ).comp
      (fun atomIndex : { atomIndex // atomIndex ∈ block } => atomIndex.1)
      Subtype.val_injective
  have hcomplCard : blockᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨outside, houtside⟩ : blockᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have houtsideNotMem : outside ∉ block := Finset.mem_compl.mp houtside
  have hspanKer : Submodule.span ℝ (Set.range coordinateBasis)
      ≤ LinearMap.ker (LinearMap.proj outside : (Fin 6 → ℝ) →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    rintro vec ⟨atomIndex, rfl⟩
    change coordinateBasis atomIndex outside = 0
    change (Pi.single atomIndex.1 (1 : ℝ) : Fin 6 → ℝ) outside = 0
    rw [Pi.single_apply]
    have hne : atomIndex.1 ≠ outside := by
      intro heq
      apply houtsideNotMem
      rw [← heq]
      exact atomIndex.2
    rw [if_neg hne.symm]
  have hindicatorNotMem : complementIndicator block
      ∉ Submodule.span ℝ (Set.range coordinateBasis) := by
    intro hmem
    have hzero := hspanKer hmem
    rw [LinearMap.mem_ker] at hzero
    change complementIndicator block outside = 0 at hzero
    rw [complementIndicator, if_neg houtsideNotMem] at hzero
    norm_num at hzero
  unfold blockComplementBasis
  exact hcoordinate.option hindicatorNotMem

theorem finrank_blockComplementSpan (block : Finset (Fin 6)) (hcard : block.card = 3) :
    Module.finrank ℝ (blockComplementSpan block) = 4 := by
  rw [blockComplementSpan,
    finrank_span_eq_card (linearIndependent_blockComplementBasis block hcard),
    Fintype.card_option, Fintype.card_coe, hcard]

theorem complementIndicator_eq_one_sub_sum_single (block : Finset (Fin 6)) :
    complementIndicator block =
      (fun _atomIndex : Fin 6 => (1 : ℝ))
        - ∑ atomIndex : { atomIndex // atomIndex ∈ block },
            Pi.single atomIndex.1 (1 : ℝ) := by
  classical
  funext atomIndex
  by_cases hmem : atomIndex ∈ block
  · rw [complementIndicator, if_pos hmem, Pi.sub_apply]
    have hsum : (∑ chosen : { atomIndex // atomIndex ∈ block },
        (Pi.single chosen.1 (1 : ℝ) : Fin 6 → ℝ) atomIndex) = 1 := by
      rw [Finset.sum_eq_single ⟨atomIndex, hmem⟩]
      · rw [Pi.single_eq_same]
      · intro other _ hne
        rw [Pi.single_apply, if_neg]
        exact fun heq => hne (Subtype.ext heq.symm)
      · simp
    rw [Finset.sum_apply, hsum, sub_self]
  · rw [complementIndicator, if_neg hmem, Pi.sub_apply, Finset.sum_apply]
    have hsum : (∑ chosen : { atomIndex // atomIndex ∈ block },
        (Pi.single chosen.1 (1 : ℝ) : Fin 6 → ℝ) atomIndex) = 0 := by
      refine Finset.sum_eq_zero fun chosen _ => ?_
      rw [Pi.single_apply, if_neg]
      exact fun heq => hmem (heq ▸ chosen.2)
    rw [hsum, sub_zero]

/-- Four rows whose span contains the three axes of `block` and whose weighted assembly
is uniform have exactly the expected four-dimensional row span. -/
theorem rowSpan_eq_blockComplementSpan_of_four_of_axes_of_balanced
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin 4 → (Fin 6 → ℝ)) (multiplier : Fin 4 → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin 4, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row)) :
    Submodule.span ℝ (Set.range row) = blockComplementSpan block := by
  classical
  let rowSpan := Submodule.span ℝ (Set.range row)
  let uniform : Fin 6 → ℝ := fun _ => 1 / 6
  have huniformEq : (∑ label : Fin 4, multiplier label • row label) = uniform := by
    funext atomIndex
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, uniform]
    exact hassembly atomIndex
  have huniformMem : uniform ∈ rowSpan := by
    rw [← huniformEq]
    exact Submodule.sum_mem rowSpan fun label _ =>
      Submodule.smul_mem rowSpan _ (Submodule.subset_span ⟨label, rfl⟩)
  have honeMem : (fun _atomIndex : Fin 6 => (1 : ℝ)) ∈ rowSpan := by
    have hscaled := Submodule.smul_mem rowSpan (6 : ℝ) huniformMem
    convert hscaled using 1
    funext atomIndex
    simp only [Pi.smul_apply, uniform, smul_eq_mul]
    norm_num
  have hindicatorMem : complementIndicator block ∈ rowSpan := by
    rw [complementIndicator_eq_one_sub_sum_single]
    exact Submodule.sub_mem rowSpan honeMem
      (Submodule.sum_mem rowSpan fun atomIndex _ => haxes atomIndex.1 atomIndex.2)
  have htargetLe : blockComplementSpan block ≤ rowSpan := by
    rw [blockComplementSpan, Submodule.span_le]
    rintro vec ⟨label, rfl⟩
    cases label with
    | none => exact hindicatorMem
    | some atomIndex => exact haxes atomIndex.1 atomIndex.2
  have hrowRank : Module.finrank ℝ rowSpan ≤ 4 := by
    calc
      Module.finrank ℝ rowSpan
          ≤ (Set.range row).toFinset.card := finrank_span_le_card (Set.range row)
      _ ≤ 4 := by
        rw [Set.toFinset_range]
        exact (Finset.card_image_le).trans_eq (by simp)
  have heq : blockComplementSpan block = rowSpan :=
    Submodule.eq_of_le_of_finrank_le htargetLe (by
      rw [finrank_blockComplementSpan block hcard]
      exact hrowRank)
  exact heq.symm

/-- The same span theorem with the row count exposed as a parameter. -/
theorem rowSpan_eq_blockComplementSpan_of_card_four_of_axes_of_balanced
    {count : ℕ} (hcount : count = 4)
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin count → (Fin 6 → ℝ)) (multiplier : Fin count → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin count, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row)) :
    Submodule.span ℝ (Set.range row) = blockComplementSpan block := by
  subst count
  exact rowSpan_eq_blockComplementSpan_of_four_of_axes_of_balanced block hcard row multiplier
    hassembly haxes

/-- In the four-row situation, every row is constant on the complementary triple. -/
theorem row_eq_on_complement_of_four_of_axes_of_balanced
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin 4 → (Fin 6 → ℝ)) (multiplier : Fin 4 → ℝ)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin 4, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row))
    (label : Fin 4) {first second : Fin 6}
    (hfirst : first ∉ block) (hsecond : second ∉ block) :
    row label first = row label second := by
  have hrow : row label ∈ Submodule.span ℝ (Set.range row) :=
    Submodule.subset_span ⟨label, rfl⟩
  rw [rowSpan_eq_blockComplementSpan_of_four_of_axes_of_balanced block hcard row multiplier
    hassembly haxes] at hrow
  exact eq_on_complement_of_mem_blockComplementSpan block hrow hfirst hsecond

/-- If each of the four rows is a probability row supported on a three-element active
block, the constant assembly forces one active block to be exactly `blockᶜ`; its row is
uniform there. Nonnegativity is not needed for this conclusion. -/
theorem exists_complementBlock_uniformRow_of_four_of_axes_of_balanced
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin 4 → (Fin 6 → ℝ)) (multiplier : Fin 4 → ℝ)
    (activeBlock : Fin 4 → Finset (Fin 6))
    (hactiveCard : ∀ label, (activeBlock label).card = 3)
    (hsupport : ∀ label atomIndex, atomIndex ∉ activeBlock label →
      row label atomIndex = 0)
    (hprobability : ∀ label, ∑ atomIndex, row label atomIndex = 1)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin 4, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row)) :
    ∃ label : Fin 4, activeBlock label = blockᶜ ∧
      row label = fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3 := by
  classical
  have hcomplCard : blockᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨outside, houtsideCompl⟩ : blockᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have houtside : outside ∉ block := Finset.mem_compl.mp houtsideCompl
  obtain ⟨label, hlabelNonzero⟩ : ∃ label : Fin 4, row label outside ≠ 0 := by
    by_contra hnone
    have hallZero : ∀ label : Fin 4, row label outside = 0 := by
      intro candidate
      by_contra hne
      exact hnone ⟨candidate, hne⟩
    have hpoint := hassembly outside
    simp_rw [hallZero, mul_zero] at hpoint
    norm_num at hpoint
  have hconstant : ∀ atomIndex, atomIndex ∉ block →
      row label atomIndex = row label outside := by
    intro atomIndex hnotMem
    exact row_eq_on_complement_of_four_of_axes_of_balanced block hcard row multiplier
      hassembly haxes label hnotMem houtside
  have hcomplSubset : blockᶜ ⊆ activeBlock label := by
    intro atomIndex hmemCompl
    have hnotMem : atomIndex ∉ block := Finset.mem_compl.mp hmemCompl
    by_contra hnotActive
    have hzero := hsupport label atomIndex hnotActive
    have heq := hconstant atomIndex hnotMem
    rw [hzero] at heq
    exact hlabelNonzero heq.symm
  have hactiveEq : activeBlock label = blockᶜ := by
    exact (Finset.eq_of_subset_of_card_le hcomplSubset (by
      rw [hactiveCard label, hcomplCard])).symm
  have hsumCompl : ∑ atomIndex ∈ blockᶜ, row label atomIndex = 1 := by
    calc
      ∑ atomIndex ∈ blockᶜ, row label atomIndex
          = ∑ atomIndex : Fin 6, row label atomIndex := by
              apply Finset.sum_subset (Finset.subset_univ blockᶜ)
              intro atomIndex _ hnotCompl
              apply hsupport label atomIndex
              rw [hactiveEq]
              exact hnotCompl
      _ = 1 := hprobability label
  have hsumConstant : ∑ atomIndex ∈ blockᶜ, row label atomIndex
      = blockᶜ.card * row label outside := by
    rw [Finset.sum_congr rfl fun atomIndex hmem =>
      hconstant atomIndex (Finset.mem_compl.mp hmem), Finset.sum_const, nsmul_eq_mul]
  have hvalue : row label outside = 1 / 3 := by
    rw [hsumConstant, hcomplCard] at hsumCompl
    norm_num at hsumCompl ⊢
    linarith
  refine ⟨label, hactiveEq, ?_⟩
  funext atomIndex
  by_cases hmem : atomIndex ∈ block
  · rw [if_pos hmem]
    apply hsupport label atomIndex
    rw [hactiveEq]
    intro hmemCompl
    exact (Finset.mem_compl.mp hmemCompl) hmem
  · rw [if_neg hmem, hconstant atomIndex hmem, hvalue]

/-- Count-parameter wrapper for an enumerated active family of cardinality four. -/
theorem exists_complementBlock_uniformRow_of_card_four_of_axes_of_balanced
    {count : ℕ} (hcount : count = 4)
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin count → (Fin 6 → ℝ)) (multiplier : Fin count → ℝ)
    (activeBlock : Fin count → Finset (Fin 6))
    (hactiveCard : ∀ label, (activeBlock label).card = 3)
    (hsupport : ∀ label atomIndex, atomIndex ∉ activeBlock label →
      row label atomIndex = 0)
    (hprobability : ∀ label, ∑ atomIndex, row label atomIndex = 1)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin count, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row)) :
    ∃ label : Fin count, activeBlock label = blockᶜ ∧
      row label = fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3 := by
  subst count
  exact exists_complementBlock_uniformRow_of_four_of_axes_of_balanced block hcard row multiplier
    activeBlock hactiveCard hsupport hprobability hassembly haxes

/-- The complement row is unique when the four blocks are distinct.  The assembly at any
complement coordinate then pins its multiplier to one half, and every other row vanishes
on the whole complementary triple. -/
theorem exists_complementBlock_uniformRow_multiplier_half_of_four_of_axes_of_balanced
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin 4 → (Fin 6 → ℝ)) (multiplier : Fin 4 → ℝ)
    (activeBlock : Fin 4 → Finset (Fin 6))
    (hblockInjective : Function.Injective activeBlock)
    (hactiveCard : ∀ label, (activeBlock label).card = 3)
    (hsupport : ∀ label atomIndex, atomIndex ∉ activeBlock label →
      row label atomIndex = 0)
    (hprobability : ∀ label, ∑ atomIndex, row label atomIndex = 1)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin 4, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row)) :
    ∃ label : Fin 4,
      activeBlock label = blockᶜ
        ∧ row label = (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3)
        ∧ multiplier label = 1 / 2
        ∧ ∀ otherLabel ≠ label, ∀ atomIndex, atomIndex ∉ block →
            row otherLabel atomIndex = 0 := by
  classical
  obtain ⟨label, hlabelBlock, hlabelRow⟩ :=
    exists_complementBlock_uniformRow_of_four_of_axes_of_balanced block hcard row multiplier
      activeBlock hactiveCard hsupport hprobability hassembly haxes
  have hcomplCard : blockᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hotherZero : ∀ otherLabel ≠ label, ∀ atomIndex, atomIndex ∉ block →
      row otherLabel atomIndex = 0 := by
    intro otherLabel hotherNe atomIndex hatomOutside
    have hotherBlockNe : activeBlock otherLabel ≠ blockᶜ := by
      intro heq
      exact hotherNe (hblockInjective (heq.trans hlabelBlock.symm))
    have hnotSubset : ¬ blockᶜ ⊆ activeBlock otherLabel := by
      intro hsubset
      have heq := Finset.eq_of_subset_of_card_le hsubset (by
        rw [hactiveCard otherLabel, hcomplCard])
      exact hotherBlockNe heq.symm
    obtain ⟨missingAtom, hmissingCompl, hmissingNotActive⟩ := Finset.not_subset.mp hnotSubset
    have hmissingOutside : missingAtom ∉ block := Finset.mem_compl.mp hmissingCompl
    have hmissingZero := hsupport otherLabel missingAtom hmissingNotActive
    have hconstant := row_eq_on_complement_of_four_of_axes_of_balanced block hcard row multiplier
      hassembly haxes otherLabel hatomOutside hmissingOutside
    rw [hmissingZero] at hconstant
    exact hconstant
  have hcomplNonempty : blockᶜ.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨outside, houtsideCompl⟩ := hcomplNonempty
  have houtside : outside ∉ block := Finset.mem_compl.mp houtsideCompl
  have hpoint := hassembly outside
  rw [Finset.sum_eq_single label] at hpoint
  · have hrowValue : row label outside = 1 / 3 := by
      rw [congrFun hlabelRow outside, if_neg houtside]
    rw [hrowValue] at hpoint
    refine ⟨label, hlabelBlock, hlabelRow, ?_, hotherZero⟩
    norm_num at hpoint
    linarith
  · intro otherLabel _ hotherNe
    rw [hotherZero otherLabel hotherNe outside houtside, mul_zero]
  · simp

/-- Count-indexed wrapper used when an active family is enumerated by `Fin family.card`. -/
theorem exists_complementBlock_uniformRow_multiplier_half_of_card_four_of_axes_of_balanced
    {count : ℕ} (hcount : count = 4)
    (block : Finset (Fin 6)) (hcard : block.card = 3)
    (row : Fin count → (Fin 6 → ℝ)) (multiplier : Fin count → ℝ)
    (activeBlock : Fin count → Finset (Fin 6))
    (hblockInjective : Function.Injective activeBlock)
    (hactiveCard : ∀ label, (activeBlock label).card = 3)
    (hsupport : ∀ label atomIndex, atomIndex ∉ activeBlock label →
      row label atomIndex = 0)
    (hprobability : ∀ label, ∑ atomIndex, row label atomIndex = 1)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ label : Fin count, multiplier label * row label atomIndex = 1 / 6)
    (haxes : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row)) :
    ∃ label : Fin count,
      activeBlock label = blockᶜ
        ∧ row label = (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3)
        ∧ multiplier label = 1 / 2
        ∧ ∀ otherLabel ≠ label, ∀ atomIndex, atomIndex ∉ block →
            row otherLabel atomIndex = 0 := by
  subst count
  exact exists_complementBlock_uniformRow_multiplier_half_of_four_of_axes_of_balanced
    block hcard row multiplier activeBlock hblockInjective hactiveCard hsupport hprobability
      hassembly haxes

/-- An eigen-square row has total mass equal to the squared norm of its block vector. -/
theorem sum_eigenSquareRow_eq_dotProduct {size rank : ℕ}
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    (vec : Fin rank → ℝ) :
    ∑ atomIndex, eigenSquareRow selected hcard vec atomIndex = vec ⬝ᵥ vec := by
  classical
  rw [dotProduct]
  simp only [eigenSquareRow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun blockIndex _ => ?_
  rw [Finset.sum_eq_single (selected.orderEmbOfFin hcard blockIndex)]
  · simp [pow_two]
  · intro otherAtom _ hne
    rw [if_neg (Ne.symm hne)]
  · simp

/-! ## The actual four-active crux weld -/

/-- If the second-order row-span witness has full three-point support and the active family
has exactly four blocks, one of those blocks is its complement.  The complementary squared
tight row is uniform, its multiplier is `1/2`, and every other active squared row vanishes
on the complementary triple. -/
theorem SixThreeCrux.exists_complement_uniformRow_multiplier_half_of_four_of_witnessSupportThree
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block : Finset (Fin 6))
    (hunit : ∀ selected : Finset (Fin 6), selected.card = 3 →
      tightVec selected ⬝ᵥ tightVec selected = 1)
    (hassembly : ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹)
    (hblock : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (haxes : ∀ atomIndex ∈ totalTightSupport tightVec block,
      Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (totalEigenSquareRow tightVec))
    (hsupportCard : (totalTightSupport tightVec block).card = 3)
    (hfamilyCard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ complementBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      complementBlock = blockᶜ
        ∧ totalEigenSquareRow tightVec complementBlock =
          (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3)
        ∧ multiplier complementBlock = 1 / 2
        ∧ ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
          otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
            totalEigenSquareRow tightVec otherBlock atomIndex = 0 := by
  classical
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  let row : Fin family.card → (Fin 6 → ℝ) := fun label =>
    totalEigenSquareRow tightVec (family.equivFin.symm label).1
  let finiteMultiplier : Fin family.card → ℝ := fun label =>
    multiplier (family.equivFin.symm label).1
  let activeBlock : Fin family.card → Finset (Fin 6) := fun label =>
    (family.equivFin.symm label).1
  have hblockCard : block.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hblock).1
  have hsupportEq : totalTightSupport tightVec block = block := by
    exact Finset.eq_of_subset_of_card_le (totalTightSupport_subset tightVec hblockCard) (by
      rw [hblockCard, hsupportCard])
  have hblockInjective : Function.Injective activeBlock := by
    intro first second heq
    apply (family.equivFin.symm.injective)
    exact Subtype.ext heq
  have hactiveCard : ∀ label, (activeBlock label).card = 3 := by
    intro label
    exact ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design)
      (family.equivFin.symm label).1).mp (family.equivFin.symm label).2).1
  have hsupport : ∀ label atomIndex, atomIndex ∉ activeBlock label →
      row label atomIndex = 0 := by
    intro label atomIndex hnotMem
    have hcard := hactiveCard label
    dsimp only [row, activeBlock]
    rw [totalEigenSquareRow_of_card tightVec hcard]
    exact eigenSquareRow_eq_zero_of_notMem hcard _ hnotMem
  have hprobability : ∀ label, ∑ atomIndex, row label atomIndex = 1 := by
    intro label
    have hcard := hactiveCard label
    dsimp only [row]
    rw [totalEigenSquareRow_of_card tightVec hcard,
      sum_eigenSquareRow_eq_dotProduct, hunit _ hcard]
  have hassemblyFin : ∀ atomIndex : Fin 6,
      ∑ label : Fin family.card, finiteMultiplier label * row label atomIndex = 1 / 6 := by
    intro atomIndex
    calc
      ∑ label : Fin family.card, finiteMultiplier label * row label atomIndex
          = ∑ selected : {selected // selected ∈ family},
              multiplier selected.1 * totalEigenSquareRow tightVec selected.1 atomIndex := by
                exact (family.equivFin.symm.sum_comp
                  (fun selected : {selected // selected ∈ family} =>
                    multiplier selected.1 *
                      totalEigenSquareRow tightVec selected.1 atomIndex))
      _ = ∑ selected ∈ family,
            multiplier selected * totalEigenSquareRow tightVec selected atomIndex := by
              exact (Finset.sum_subtype family (fun selected => Iff.rfl)
                (fun selected => multiplier selected *
                  totalEigenSquareRow tightVec selected atomIndex)).symm
      _ = 1 / 6 := by
            simpa [one_div] using hassembly atomIndex
  have hrange : Set.range row = Set.range
      (fun selected : {selected // selected ∈ family} =>
        totalEigenSquareRow tightVec selected.1) := by
    ext candidate
    constructor
    · rintro ⟨label, rfl⟩
      exact ⟨family.equivFin.symm label, rfl⟩
    · rintro ⟨selected, rfl⟩
      exact ⟨family.equivFin selected, by
        simp only [row, Equiv.symm_apply_apply]⟩
  have haxesFin : ∀ atomIndex ∈ block,
      Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ (Set.range row) := by
    intro atomIndex hatom
    have haxis := haxes atomIndex (hsupportEq.symm ▸ hatom)
    change Pi.single atomIndex (1 : ℝ) ∈ Submodule.span ℝ
      (Set.range fun selected : {selected // selected ∈ family} =>
        totalEigenSquareRow tightVec selected.1) at haxis
    rwa [hrange]
  obtain ⟨label, hlabelBlock, hlabelRow, hlabelMultiplier, hotherZero⟩ :=
    exists_complementBlock_uniformRow_multiplier_half_of_card_four_of_axes_of_balanced
      hfamilyCard block hblockCard row finiteMultiplier activeBlock hblockInjective hactiveCard
        hsupport hprobability hassemblyFin haxesFin
  let complementBlock : Finset (Fin 6) := activeBlock label
  have hcomplementMem : complementBlock ∈ family := (family.equivFin.symm label).2
  refine ⟨complementBlock, hcomplementMem, hlabelBlock, hlabelRow, hlabelMultiplier, ?_⟩
  intro otherBlock hotherMem hotherNe atomIndex hatomOutside
  let otherLabel : Fin family.card := family.equivFin ⟨otherBlock, hotherMem⟩
  have hotherLabelNe : otherLabel ≠ label := by
    intro heq
    apply hotherNe
    change otherBlock = activeBlock label
    have hsubtypeEq : (⟨otherBlock, hotherMem⟩ : {selected // selected ∈ family}) =
        family.equivFin.symm label := by
      apply family.equivFin.injective
      simpa only [Equiv.apply_symm_apply, otherLabel] using heq
    exact congrArg Subtype.val hsubtypeEq
  have hzero := hotherZero otherLabel hotherLabelNe atomIndex hatomOutside
  simpa only [row, otherLabel, Equiv.symm_apply_apply] using hzero

/-- The total eigen-square row is the pointwise square of the corresponding ambient tight
selection on every card-three block. -/
theorem totalEigenSquareRow_eq_ambientTightSelection_mul_self
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (atomIndex : Fin 6) :
    totalEigenSquareRow tightVec selected atomIndex
      = ambientTightSelection tightVec selected atomIndex
          * ambientTightSelection tightVec selected atomIndex := by
  have hrestriction : tightVec selected = fun blockIndex =>
      ambientTightSelection tightVec selected (selected.orderEmbOfFin hcard blockIndex) := by
    funext blockIndex
    rw [ambientTightSelection, dif_pos hcard,
      selectionInjection_mulVec_apply (selected.orderEmbOfFin hcard).injective]
  have hselectionSupport : ∀ otherAtom : Fin 6, otherAtom ∉ selected →
      ambientTightSelection tightVec selected otherAtom = 0 := by
    intro otherAtom hnotMem
    rw [ambientTightSelection, dif_pos hcard]
    exact selectionInjection_mulVec_eq_zero_of_notMem _ _ fun blockIndex heq =>
      hnotMem (heq ▸ selected.orderEmbOfFin_mem hcard blockIndex)
  rw [totalEigenSquareRow_of_card tightVec hcard, hrestriction]
  exact eigenSquareRow_eq_mul_self_of_support hcard _ hselectionSupport atomIndex

/-- The stationary assembly diagonal, rewritten for the squared rows belonging to an
ambient tight-vector family. -/
theorem SixThreeCrux.assembly_totalEigenSquareRow_of_stationaryAmbient
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec)) :
    ∀ atomIndex : Fin 6,
      ∑ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
        multiplier selected * totalEigenSquareRow tightVec selected atomIndex
          = (((6 : ℕ) : ℝ))⁻¹ := by
  intro atomIndex
  exact assemblyDiagonal_of_isChartStationaryData_of_rowEq hdata
    (totalEigenSquareRow tightVec) (by
      intro selected hmember rowIndex
      have hcard : selected.card = 3 :=
        ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp hmember).1
      rw [totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hcard]) atomIndex

/-- The uniform complementary row forces an exact block decomposition of the assembled
multiplier: all cross entries vanish, and the complementary principal block is precisely
one half of the rank-one projector generated by that tight direction. -/
theorem chartMultiplierAssembly_blockSplit_of_complement_multiplier_half
    (family : Finset (Finset (Fin 6)))
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block complementBlock : Finset (Fin 6))
    (hmemberCard : ∀ selected ∈ family, selected.card = 3)
    (hcomplementMem : complementBlock ∈ family)
    (hcomplementEq : complementBlock = blockᶜ)
    (hcomplementMultiplier : multiplier complementBlock = 1 / 2)
    (hotherZero : ∀ otherBlock ∈ family, otherBlock ≠ complementBlock →
      ∀ atomIndex, atomIndex ∉ block →
        totalEigenSquareRow tightVec otherBlock atomIndex = 0) :
    (∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
      (chartMultiplierAssembly family multiplier (ambientTightSelection tightVec)
          inside outside = 0
        ∧ chartMultiplierAssembly family multiplier (ambientTightSelection tightVec)
          outside inside = 0))
      ∧ ∀ (first : Fin 6), first ∉ block → ∀ (second : Fin 6), second ∉ block →
        chartMultiplierAssembly family multiplier (ambientTightSelection tightVec)
            first second =
          (1 / 2) * ambientTightSelection tightVec complementBlock first
            * ambientTightSelection tightVec complementBlock second := by
  classical
  have hcomplementCard : complementBlock.card = 3 :=
    hmemberCard complementBlock hcomplementMem
  have hselectionSupport : ∀ selected ∈ family, ∀ atomIndex,
      atomIndex ∉ selected → ambientTightSelection tightVec selected atomIndex = 0 := by
    intro selected hselected atomIndex hnotMem
    have hcard := hmemberCard selected hselected
    rw [ambientTightSelection, dif_pos hcard]
    exact selectionInjection_mulVec_eq_zero_of_notMem _ _ fun blockIndex heq =>
      hnotMem (heq ▸ selected.orderEmbOfFin_mem hcard blockIndex)
  have hzeroOfRow : ∀ selected ∈ family, ∀ atomIndex,
      totalEigenSquareRow tightVec selected atomIndex = 0 →
        ambientTightSelection tightVec selected atomIndex = 0 := by
    intro selected hselected atomIndex hrowZero
    have hcard := hmemberCard selected hselected
    rw [totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hcard] at hrowZero
    exact (mul_self_eq_zero.mp hrowZero)
  have hcomplementInsideZero : ∀ atomIndex ∈ block,
      ambientTightSelection tightVec complementBlock atomIndex = 0 := by
    intro atomIndex hinside
    apply hselectionSupport complementBlock hcomplementMem atomIndex
    rw [hcomplementEq]
    exact fun hmem => (Finset.mem_compl.mp hmem) hinside
  have hotherOutsideZero : ∀ otherBlock ∈ family, otherBlock ≠ complementBlock →
      ∀ atomIndex, atomIndex ∉ block →
        ambientTightSelection tightVec otherBlock atomIndex = 0 := by
    intro otherBlock hotherMem hotherNe atomIndex houtside
    exact hzeroOfRow otherBlock hotherMem atomIndex
      (hotherZero otherBlock hotherMem hotherNe atomIndex houtside)
  constructor
  · intro inside hinside outside houtside
    constructor
    · rw [chartMultiplierAssembly_apply]
      refine Finset.sum_eq_zero fun selected hselected => ?_
      by_cases heq : selected = complementBlock
      · subst selected
        rw [hcomplementInsideZero inside hinside, zero_mul, mul_zero]
      · simp [hotherOutsideZero selected hselected heq outside houtside]
    · rw [chartMultiplierAssembly_apply]
      refine Finset.sum_eq_zero fun selected hselected => ?_
      by_cases heq : selected = complementBlock
      · subst selected
        simp [hcomplementInsideZero inside hinside]
      · rw [hotherOutsideZero selected hselected heq outside houtside, zero_mul, mul_zero]
  · intro first hfirst second hsecond
    rw [chartMultiplierAssembly_apply, Finset.sum_eq_single complementBlock]
    · rw [hcomplementMultiplier]
      ring
    · intro otherBlock hotherMem hotherNe
      rw [hotherOutsideZero otherBlock hotherMem hotherNe first hfirst, zero_mul, mul_zero]
    · exact fun hnotMem => (hnotMem hcomplementMem).elim

/-- **THE FOUR-ACTIVE SECOND-ORDER FORK.**  Use the landed crux row-span witness, but
reselect its multiplier through strong stationarity so that the same squared rows carry
the full commuting stationary datum.  Its selected support is then either a pair, or the
support-three branch has the exact complementary block, uniform complementary row and
half multiplier. -/
theorem SixThreeCrux.exists_stationary_supportTwo_or_complement_of_four
    (crux : SixThreeCrux)
    (hfamilyCard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        Matrix.mulVec ((chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)) (tightVec selected)
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ (∀ atomIndex ∈ totalTightSupport tightVec block,
          Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
            (chartArgmaxFamily (chartPointOfDesign crux.design))
            (totalEigenSquareRow tightVec))
      ∧ ((totalTightSupport tightVec block).card = 2
        ∨ (totalTightSupport tightVec block).card = 3
          ∧ ∃ complementBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
            complementBlock = blockᶜ
              ∧ totalEigenSquareRow tightVec complementBlock =
                (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3)
              ∧ multiplier complementBlock = 1 / 2
              ∧ ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0) := by
  classical
  obtain ⟨tightVec, _oldMultiplier, block, hunit, hEigen, _oldAssembly, hblock,
    hsupportTwo, haxes⟩ :=
    crux.exists_argmax_supportTwo_coordinateSingles_mem_finiteRowSpan
  let selection : Finset (Fin 6) → (Fin 6 → ℝ) := ambientTightSelection tightVec
  have hselection : ∀ selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      IsChartTightDirection (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design)) selected
        (selection selected) := by
    intro selected hmember
    exact isChartTightDirection_ambientTightSelection crux tightVec hunit hEigen hmember
  obtain ⟨multiplier, hdata⟩ :=
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
      crux.isChartStrongStationaryData selection hselection
  have hassembly := crux.assembly_totalEigenSquareRow_of_stationaryAmbient
    tightVec multiplier hdata
  have hblockCard : block.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) block).mp hblock).1
  have hsupportUpper : (totalTightSupport tightVec block).card ≤ 3 := by
    calc
      (totalTightSupport tightVec block).card ≤ block.card :=
        Finset.card_le_card (totalTightSupport_subset tightVec hblockCard)
      _ = 3 := hblockCard
  refine ⟨tightVec, multiplier, block, hunit, hEigen, hdata, hblock, haxes, ?_⟩
  by_cases hsupportThree : (totalTightSupport tightVec block).card = 3
  · right
    exact ⟨hsupportThree,
      crux.exists_complement_uniformRow_multiplier_half_of_four_of_witnessSupportThree
        tightVec multiplier block hunit hassembly hblock haxes hsupportThree hfamilyCard⟩
  · left
    omega

/-! ## The positive-definite assembly-block branch -/

/-- In dimension three, subtracting a positive-definite form from its trace times the
identity remains positive definite. -/
theorem posDef_trace_smul_one_sub_of_three
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hform : form.PosDef) :
    (Matrix.trace form • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form).PosDef := by
  have hpsd :
      (Matrix.trace form • (1 : Matrix (Fin 3) (Fin 3) ℝ) - form).PosSemidef :=
    posSemidef_trace_smul_one_sub_of_three hform.posSemidef
  refine hpsd.posDef_iff_det_ne_zero.mpr ?_
  have htrace : Matrix.trace form =
      ∑ eigenIndex, hform.isHermitian.eigenvalues eigenIndex := by
    simpa using hform.isHermitian.trace_eq_sum_eigenvalues
  have hfactor : ∀ eigenIndex : Fin 3,
      0 < Matrix.trace form - hform.isHermitian.eigenvalues eigenIndex := by
    intro eigenIndex
    have hzero := hform.eigenvalues_pos (0 : Fin 3)
    have hone := hform.eigenvalues_pos (1 : Fin 3)
    have htwo := hform.eigenvalues_pos (2 : Fin 3)
    rw [htrace, Fin.sum_univ_three]
    fin_cases eigenIndex <;> simp_all <;> linarith
  have hproduct :
      0 < ∏ eigenIndex : Fin 3,
        (Matrix.trace form - hform.isHermitian.eigenvalues eigenIndex) :=
    Finset.prod_pos fun eigenIndex _ => hfactor eigenIndex
  rw [prod_level_sub_eigenvalues hform.isHermitian (Matrix.trace form)] at hproduct
  exact ne_of_gt hproduct

theorem eq_zero_of_posDef_mul_eq_zero_three
    {left right : Matrix (Fin 3) (Fin 3) ℝ} (hleft : left.PosDef)
    (hproduct : left * right = 0) :
    right = 0 := by
  apply hleft.isUnit.mul_left_cancel
  simpa using hproduct

theorem half_atomMatrix_sq {vector : Fin 3 → ℝ}
    (hunit : vector ⬝ᵥ vector = 1) :
    ((1 / 2 : ℝ) • atomMatrix vector) * ((1 / 2 : ℝ) • atomMatrix vector)
      = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • atomMatrix vector) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    atomMatrix_mul_atomMatrix, hunit, one_smul]
  simp only [atomMatrix, smul_smul]

/-- A positive-definite trace-half block cannot intertwine with a rank-one
half-projector. -/
theorem eq_zero_of_posDef_trace_half_of_mul_eq_mul_half_atomMatrix
    {left cross : Matrix (Fin 3) (Fin 3) ℝ} {vector : Fin 3 → ℝ}
    (hleft : left.PosDef) (htrace : Matrix.trace left = 1 / 2)
    (hunit : vector ⬝ᵥ vector = 1)
    (hcommutes : left * cross = cross * ((1 / 2 : ℝ) • atomMatrix vector)) :
    cross = 0 := by
  let right : Matrix (Fin 3) (Fin 3) ℝ := (1 / 2 : ℝ) • atomMatrix vector
  have hrightSq : right * right = (1 / 2 : ℝ) • right := by
    exact half_atomMatrix_sq hunit
  have hleftTwice : left * (left * cross) = left * ((1 / 2 : ℝ) • cross) := by
    calc
      left * (left * cross) = left * (cross * right) := by rw [hcommutes]
      _ = (left * cross) * right := by rw [Matrix.mul_assoc]
      _ = (cross * right) * right := by rw [hcommutes]
      _ = cross * (right * right) := by rw [Matrix.mul_assoc]
      _ = cross * ((1 / 2 : ℝ) • right) := by rw [hrightSq]
      _ = (1 / 2 : ℝ) • (cross * right) := by rw [Matrix.mul_smul]
      _ = (1 / 2 : ℝ) • (left * cross) := by rw [hcommutes]
      _ = left * ((1 / 2 : ℝ) • cross) := by rw [Matrix.mul_smul]
  have hhalf : left * cross = (1 / 2 : ℝ) • cross := by
    exact hleft.isUnit.mul_left_cancel hleftTwice
  let complement := Matrix.trace left • (1 : Matrix (Fin 3) (Fin 3) ℝ) - left
  have hcomplement : complement.PosDef := posDef_trace_smul_one_sub_of_three hleft
  have hzero : complement * cross = 0 := by
    change (Matrix.trace left • (1 : Matrix (Fin 3) (Fin 3) ℝ) - left) * cross = 0
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, htrace, hhalf, sub_self]
  exact eq_zero_of_posDef_mul_eq_zero_three hcomplement hzero

/-- Split a six-coordinate sum over a block and its complement. -/
theorem sum_univ_eq_sum_block_add_sum_compl
    (block : Finset (Fin 6)) (summand : Fin 6 → ℝ) :
    ∑ atomIndex, summand atomIndex =
      ∑ atomIndex ∈ block, summand atomIndex
        + ∑ atomIndex ∈ blockᶜ, summand atomIndex := by
  rw [← Finset.sum_union disjoint_compl_right]
  simp

/-- A globally commuting pair with a block-diagonal second factor satisfies the expected
off-diagonal block intertwining equation.  The right block is supplied entrywise as a
rank-one half-projector. -/
theorem submatrix_intertwines_half_atomMatrix_of_commutes_of_blockSplit
    (projection assembly : Matrix (Fin 6) (Fin 6) ℝ)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3)
    (vector : Fin 6 → ℝ)
    (hcommutes : projection * assembly = assembly * projection)
    (hcross : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        assembly inside outside = 0 ∧ assembly outside inside = 0)
    (hright : ∀ (first : Fin 6), first ∉ block →
      ∀ (second : Fin 6), second ∉ block →
        assembly first second = (1 / 2) * vector first * vector second) :
    (assembly.submatrix (block.orderEmbOfFin hblockCard)
        (block.orderEmbOfFin hblockCard))
        * (projection.submatrix (block.orderEmbOfFin hblockCard)
          (blockᶜ.orderEmbOfFin hcomplementCard))
      = (projection.submatrix (block.orderEmbOfFin hblockCard)
          (blockᶜ.orderEmbOfFin hcomplementCard))
        * ((1 / 2 : ℝ) • atomMatrix
          (fun complementIndex =>
            vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex))) := by
  classical
  let blockPick := block.orderEmbOfFin hblockCard
  let complementPick := blockᶜ.orderEmbOfFin hcomplementCard
  have hblockMem : ∀ blockIndex, blockPick blockIndex ∈ block := by
    intro blockIndex
    exact Finset.orderEmbOfFin_mem block hblockCard blockIndex
  have hcomplementNotMem : ∀ complementIndex, complementPick complementIndex ∉ block := by
    intro complementIndex
    exact Finset.mem_compl.mp
      (Finset.orderEmbOfFin_mem blockᶜ hcomplementCard complementIndex)
  have hXiPCollapse : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        (∑ atomIndex, assembly inside atomIndex * projection atomIndex outside)
          = ∑ atomIndex ∈ block,
              assembly inside atomIndex * projection atomIndex outside := by
    intro inside hinside outside houtside
    rw [sum_univ_eq_sum_block_add_sum_compl block]
    have hzero : (∑ atomIndex ∈ blockᶜ,
        assembly inside atomIndex * projection atomIndex outside) = 0 := by
      refine Finset.sum_eq_zero fun atomIndex hatom => ?_
      rw [(hcross inside hinside atomIndex (Finset.mem_compl.mp hatom)).1, zero_mul]
    rw [hzero, add_zero]
  have hPXiCollapse : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        (∑ atomIndex, projection inside atomIndex * assembly atomIndex outside)
          = ∑ atomIndex ∈ blockᶜ,
              projection inside atomIndex * assembly atomIndex outside := by
    intro inside hinside outside houtside
    rw [sum_univ_eq_sum_block_add_sum_compl block]
    have hzero : (∑ atomIndex ∈ block,
        projection inside atomIndex * assembly atomIndex outside) = 0 := by
      refine Finset.sum_eq_zero fun atomIndex hatom => ?_
      rw [(hcross atomIndex hatom outside houtside).1, mul_zero]
    rw [hzero, zero_add]
  ext blockIndex complementIndex
  have hglobal := congrFun (congrFun hcommutes (blockPick blockIndex))
    (complementPick complementIndex)
  simp only [Matrix.mul_apply] at hglobal
  have hintertwine :
      (∑ atomIndex ∈ block,
          assembly (blockPick blockIndex) atomIndex
            * projection atomIndex (complementPick complementIndex))
        = ∑ atomIndex ∈ blockᶜ,
            projection (blockPick blockIndex) atomIndex
              * assembly atomIndex (complementPick complementIndex) := by
    rw [← hXiPCollapse (blockPick blockIndex) (hblockMem blockIndex)
      (complementPick complementIndex) (hcomplementNotMem complementIndex),
      ← hPXiCollapse (blockPick blockIndex) (hblockMem blockIndex)
        (complementPick complementIndex) (hcomplementNotMem complementIndex)]
    exact hglobal.symm
  have hintertwineFin :
      (∑ otherIndex : Fin 3,
          assembly (blockPick blockIndex) (blockPick otherIndex)
            * projection (blockPick otherIndex) (complementPick complementIndex))
        = ∑ otherIndex : Fin 3,
            projection (blockPick blockIndex) (complementPick otherIndex)
              * assembly (complementPick otherIndex) (complementPick complementIndex) := by
    calc
      ∑ otherIndex : Fin 3,
          assembly (blockPick blockIndex) (blockPick otherIndex)
            * projection (blockPick otherIndex) (complementPick complementIndex)
          = ∑ atomIndex ∈ block,
              assembly (blockPick blockIndex) atomIndex
                * projection atomIndex (complementPick complementIndex) := by
              simpa only [blockPick] using sum_orderEmbOfFin_eq_sum block hblockCard
                (fun atomIndex => assembly (blockPick blockIndex) atomIndex
                  * projection atomIndex (complementPick complementIndex))
      _ = ∑ atomIndex ∈ blockᶜ,
            projection (blockPick blockIndex) atomIndex
              * assembly atomIndex (complementPick complementIndex) := hintertwine
      _ = ∑ otherIndex : Fin 3,
            projection (blockPick blockIndex) (complementPick otherIndex)
              * assembly (complementPick otherIndex) (complementPick complementIndex) := by
              simpa only [complementPick] using
                (sum_orderEmbOfFin_eq_sum blockᶜ hcomplementCard
                  (fun atomIndex => projection (blockPick blockIndex) atomIndex
                    * assembly atomIndex (complementPick complementIndex))).symm
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  calc
    ∑ otherIndex : Fin 3,
        assembly (blockPick blockIndex) (blockPick otherIndex)
          * projection (blockPick otherIndex) (complementPick complementIndex)
        = ∑ otherIndex : Fin 3,
          projection (blockPick blockIndex) (complementPick otherIndex)
            * assembly (complementPick otherIndex) (complementPick complementIndex) :=
          hintertwineFin
    _ = ∑ otherIndex : Fin 3,
          projection (blockPick blockIndex) (complementPick otherIndex)
            * ((1 / 2) * vector (complementPick otherIndex)
              * vector (complementPick complementIndex)) := by
          refine Finset.sum_congr rfl fun otherIndex _ => ?_
          rw [hright (complementPick otherIndex) (hcomplementNotMem otherIndex)
            (complementPick complementIndex) (hcomplementNotMem complementIndex)]
    _ = ∑ otherIndex : Fin 3,
          projection (blockPick blockIndex) (complementPick otherIndex)
            * (1 / 2 *
              (vector (complementPick otherIndex) * vector (complementPick complementIndex))) := by
          apply Finset.sum_congr rfl
          intro otherIndex _
          ring

/-- The positive-definite half-trace block kills the projection's cross block once global
commutation has been localized. -/
theorem projectionCross_eq_zero_of_posDef_of_commutes_of_blockSplit
    (projection assembly : Matrix (Fin 6) (Fin 6) ℝ)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3)
    (vector : Fin 6 → ℝ)
    (hcommutes : projection * assembly = assembly * projection)
    (hcross : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        assembly inside outside = 0 ∧ assembly outside inside = 0)
    (hright : ∀ (first : Fin 6), first ∉ block →
      ∀ (second : Fin 6), second ∉ block →
        assembly first second = (1 / 2) * vector first * vector second)
    (hleftPosDef : (assembly.submatrix (block.orderEmbOfFin hblockCard)
      (block.orderEmbOfFin hblockCard)).PosDef)
    (hleftTrace : Matrix.trace (assembly.submatrix (block.orderEmbOfFin hblockCard)
      (block.orderEmbOfFin hblockCard)) = 1 / 2)
    (hvectorUnit : (fun complementIndex =>
        vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
      (fun complementIndex =>
        vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1) :
    projection.submatrix (block.orderEmbOfFin hblockCard)
        (blockᶜ.orderEmbOfFin hcomplementCard) = 0 := by
  apply eq_zero_of_posDef_trace_half_of_mul_eq_mul_half_atomMatrix
    hleftPosDef hleftTrace hvectorUnit
  exact submatrix_intertwines_half_atomMatrix_of_commutes_of_blockSplit
    projection assembly block hblockCard hcomplementCard vector hcommutes hcross hright

/-- A constant `1/6` diagonal gives trace `1/2` on every three-coordinate principal
block. -/
theorem trace_submatrix_eq_half_of_card_three_of_diagonal_sixth
    (assembly : Matrix (Fin 6) (Fin 6) ℝ)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hdiagonal : ∀ atomIndex : Fin 6,
      assembly atomIndex atomIndex = (((6 : ℕ) : ℝ))⁻¹) :
    Matrix.trace (assembly.submatrix (block.orderEmbOfFin hblockCard)
      (block.orderEmbOfFin hblockCard)) = 1 / 2 := by
  rw [Matrix.trace, Fin.sum_univ_three]
  change assembly (block.orderEmbOfFin hblockCard 0) (block.orderEmbOfFin hblockCard 0)
      + assembly (block.orderEmbOfFin hblockCard 1) (block.orderEmbOfFin hblockCard 1)
      + assembly (block.orderEmbOfFin hblockCard 2) (block.orderEmbOfFin hblockCard 2) = 1 / 2
  rw [hdiagonal, hdiagonal, hdiagonal]
  norm_num

/-- Restricting a unit vector supported on the complementary triple preserves its norm. -/
theorem dotProduct_complementRestriction_eq_one_of_unit_of_zero_on_block
    (block : Finset (Fin 6)) (hcomplementCard : blockᶜ.card = 3)
    (vector : Fin 6 → ℝ) (hunit : vector ⬝ᵥ vector = 1)
    (hzero : ∀ atomIndex ∈ block, vector atomIndex = 0) :
    (fun complementIndex =>
        vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
      (fun complementIndex =>
        vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1 := by
  rw [dotProduct]
  rw [dotProduct] at hunit
  have hsplit := sum_univ_eq_sum_block_add_sum_compl block
    (fun atomIndex => vector atomIndex * vector atomIndex)
  have hblockZero : (∑ atomIndex ∈ block,
      vector atomIndex * vector atomIndex) = 0 := by
    refine Finset.sum_eq_zero fun atomIndex hatom => ?_
    rw [hzero atomIndex hatom, zero_mul]
  rw [hsplit, hblockZero, zero_add] at hunit
  calc
    ∑ complementIndex : Fin 3,
        vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)
          * vector (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)
        = ∑ atomIndex ∈ blockᶜ,
            vector atomIndex * vector atomIndex := by
              exact sum_orderEmbOfFin_eq_sum blockᶜ hcomplementCard
                (fun atomIndex => vector atomIndex * vector atomIndex)
    _ = 1 := hunit

/-- **POSITIVE-DEFINITE FOUR-ACTIVE EXIT.**  In the support-three complementary-block
branch, if the three-row assembly on the selected block is positive definite, stationary
commutation forces the chart projection itself to split across the selected triple and
its complement. -/
theorem SixThreeCrux.projectionCross_eq_zero_of_complement_of_assemblyBlock_posDef
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block complementBlock : Finset (Fin 6))
    (hblockCard : block.card = 3) (hcomplementCard : blockᶜ.card = 3)
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hcomplementMem : complementBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementEq : complementBlock = blockᶜ)
    (hcomplementMultiplier : multiplier complementBlock = 1 / 2)
    (hotherZero : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
        totalEigenSquareRow tightVec otherBlock atomIndex = 0)
    (hleftPosDef :
      ((chartMultiplierAssembly
        (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier
        (ambientTightSelection tightVec)).submatrix
          (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard)).PosDef) :
    (chartPointOfDesign crux.design).chart.submatrix
        (block.orderEmbOfFin hblockCard)
        (blockᶜ.orderEmbOfFin hcomplementCard) = 0 := by
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  let selection := ambientTightSelection tightVec
  let assembly := chartMultiplierAssembly family multiplier selection
  have hmemberCard : ∀ selected ∈ family, selected.card = 3 := by
    intro selected hselected
    exact ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) selected).mp
      hselected).1
  obtain ⟨hcross, hright⟩ :=
    chartMultiplierAssembly_blockSplit_of_complement_multiplier_half family tightVec
      multiplier block complementBlock hmemberCard hcomplementMem hcomplementEq
        hcomplementMultiplier hotherZero
  have hleftTrace : Matrix.trace
      (assembly.submatrix (block.orderEmbOfFin hblockCard)
        (block.orderEmbOfFin hblockCard)) = 1 / 2 := by
    apply trace_submatrix_eq_half_of_card_three_of_diagonal_sixth
    intro atomIndex
    exact hdata.assembly_diagonal atomIndex
  have hcomplementUnit : selection complementBlock ⬝ᵥ selection complementBlock = 1 :=
    hdata.tightDir_unit complementBlock hcomplementMem
  have hcomplementZeroOnBlock : ∀ atomIndex ∈ block,
      selection complementBlock atomIndex = 0 := by
    intro atomIndex hatom
    apply hdata.tightDir_support complementBlock hcomplementMem atomIndex
    dsimp only [id]
    rw [hcomplementEq]
    exact fun hmem => (Finset.mem_compl.mp hmem) hatom
  have hrestrictedUnit :
      (fun complementIndex => selection complementBlock
          (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
        (fun complementIndex => selection complementBlock
          (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1 :=
    dotProduct_complementRestriction_eq_one_of_unit_of_zero_on_block block
      hcomplementCard (selection complementBlock) hcomplementUnit hcomplementZeroOnBlock
  apply projectionCross_eq_zero_of_posDef_of_commutes_of_blockSplit
    (chartPointOfDesign crux.design).chart assembly block hblockCard hcomplementCard
      (selection complementBlock) hdata.assembly_commutes hcross hright
  · exact hleftPosDef
  · exact hleftTrace
  · exact hrestrictedUnit

/-- Subtracting the diagonal weight matrix does not change a cross block between a triple
and its complement. -/
theorem chartPointGap_cross_eq_zero_of_chart_cross_eq_zero
    (point : ChartPoint 6 3)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3)
    (hchartCross : point.chart.submatrix (block.orderEmbOfFin hblockCard)
      (blockᶜ.orderEmbOfFin hcomplementCard) = 0) :
    (chartPointGap point).submatrix (block.orderEmbOfFin hblockCard)
      (blockᶜ.orderEmbOfFin hcomplementCard) = 0 := by
  ext blockIndex complementIndex
  have hchartEntry := congrFun (congrFun hchartCross blockIndex) complementIndex
  simp only [Matrix.submatrix_apply, Matrix.zero_apply] at hchartEntry
  have hblockMem := Finset.orderEmbOfFin_mem block hblockCard blockIndex
  have hcomplementMem := Finset.orderEmbOfFin_mem blockᶜ hcomplementCard complementIndex
  have hne : block.orderEmbOfFin hblockCard blockIndex ≠
      blockᶜ.orderEmbOfFin hcomplementCard complementIndex := by
    intro heq
    exact (Finset.mem_compl.mp hcomplementMem) (heq ▸ hblockMem)
  simp only [Matrix.submatrix_apply, chartPointGap, Matrix.sub_apply,
    Matrix.diagonal_apply, hne, if_false, sub_zero, Matrix.zero_apply]
  exact hchartEntry


end Gtz

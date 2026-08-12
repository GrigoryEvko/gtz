import Gtz.Wave.GtzEFourRowSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- A card-three local tight vector whose total support also has card three is
nonzero at every atom of its block after ambient injection. -/
theorem ambientTightSelection_ne_zero_of_mem_of_support_card_three
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hsupportCard : (totalTightSupport tightVec block).card = 3)
    {atomIndex : Fin 6} (hmem : atomIndex ∈ block) :
    ambientTightSelection tightVec block atomIndex ≠ 0 := by
  classical
  have hsupportEq : totalTightSupport tightVec block = block := by
    apply Finset.eq_of_subset_of_card_le
    · exact totalTightSupport_subset tightVec hblockCard
    · rw [hsupportCard, hblockCard]
  have hmemSupport : atomIndex ∈ totalTightSupport tightVec block := by
    rw [hsupportEq]
    exact hmem
  rw [totalTightSupport_of_card tightVec hblockCard] at hmemSupport
  obtain ⟨blockIndex, hblockIndex, hindexEq⟩ := Finset.mem_image.mp hmemSupport
  have hlocal : tightVec block blockIndex ≠ 0 :=
    (Finset.mem_filter.mp hblockIndex).2
  rw [ambientTightSelection, dif_pos hblockCard, ← hindexEq,
    selectionInjection_mulVec_apply (block.orderEmbOfFin hblockCard).injective]
  exact hlocal

/-- A uniform `1/3` complementary square row is nonzero on every atom outside
the selected block. -/
theorem ambientTightSelection_ne_zero_of_uniform_complement_row
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (block complementBlock : Finset (Fin 6))
    (hcomplementCard : complementBlock.card = 3)
    (hrow : totalEigenSquareRow tightVec complementBlock =
      (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3))
    {atomIndex : Fin 6} (hnotMem : atomIndex ∉ block) :
    ambientTightSelection tightVec complementBlock atomIndex ≠ 0 := by
  intro hzero
  have hentry := congrFun hrow atomIndex
  rw [totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec
      hcomplementCard atomIndex,
    if_neg hnotMem, hzero, zero_mul] at hentry
  norm_num at hentry


end Gtz

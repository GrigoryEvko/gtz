import Gtz.Design.PivotBalanceLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Stall confinement

A *stall* is a positive-definite selection each of whose labels carries chart
ladder pivot at least one.  No single deletion from a stall keeps positive
definiteness.  The pointer window of a K4 pivot wall is exactly a four-label
stall, so every statement here reads directly at the wall.

The module proves that a stall confines positive definiteness away from its own
subsets, and spends the law at the K4 pivot wall.

* `not_posDef_directionChartGap_erase_of_pivot_ge_one` — one deletion from a
  stalled label never keeps positive definiteness.
* `not_posDef_directionChartGap_of_subset_of_stall` — a subset one label
  smaller than a stall is never positive definite.
* `exists_notMem_of_posDef_of_stall` — a positive-definite selection one label
  smaller than a stall carries a label outside that stall.
* `kFourPivotWall_winner_escapes_window` — at a K4 pivot wall every positive
  definite spanning tree carries a label outside the pointer window.  The
  window holds four of the six labels, so the winner meets the two-label
  complement: the atlas search at a pivot wall never has to read a cell inside
  the window.
-/

namespace Gtz

/-- A stalled label cannot be deleted: its pivot is at least one, and the
ladder rung equates deletion with a pivot below one. -/
theorem not_posDef_directionChartGap_erase_of_pivot_ge_one {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    {stalled : Finset (Fin size)}
    (hpd : (directionChartGap direction point.mass point.weight stalled).PosDef)
    {label : Fin size} (hmem : label ∈ stalled)
    (hpivot : 1 ≤ chartLadderPivot direction point.mass point.weight
      stalled label) :
    ¬ (directionChartGap direction point.mass point.weight
        (stalled.erase label)).PosDef := by
  intro hcontra
  have hlt := (posDef_directionChartGap_erase_iff direction point.mass
    point.weight point.mass_pos point.weight_pos stalled hmem hpd).mp hcontra
  linarith

/-- **STALL CONFINEMENT.**  A subset one label smaller than a stall is exactly
a single deletion from that stall, so it is never positive definite. -/
theorem not_posDef_directionChartGap_of_subset_of_stall {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    {stalled sub : Finset (Fin size)}
    (hpd : (directionChartGap direction point.mass point.weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot direction point.mass point.weight stalled label)
    (hsub : sub ⊆ stalled) (hcard : sub.card + 1 = stalled.card) :
    ¬ (directionChartGap direction point.mass point.weight sub).PosDef := by
  have hne : sub ≠ stalled := by
    intro heq
    rw [heq] at hcard
    omega
  have hss : sub ⊂ stalled := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  obtain ⟨drop, hdropMem, hdropNot⟩ := Finset.exists_of_ssubset hss
  have hsubErase : sub ⊆ stalled.erase drop := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, hsub hx⟩
    rintro rfl
    exact hdropNot hx
  have hcardErase : (stalled.erase drop).card = sub.card := by
    rw [Finset.card_erase_of_mem hdropMem]
    omega
  have heq : sub = stalled.erase drop :=
    Finset.eq_of_subset_of_card_le hsubErase (le_of_eq hcardErase)
  rw [heq]
  exact not_posDef_directionChartGap_erase_of_pivot_ge_one direction point hpd
    hdropMem (hstall drop hdropMem)

/-- A positive-definite selection one label smaller than a stall must leave the
stall: it carries a label the stall does not hold. -/
theorem exists_notMem_of_posDef_of_stall {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    {stalled sub : Finset (Fin size)}
    (hpd : (directionChartGap direction point.mass point.weight stalled).PosDef)
    (hstall : ∀ label ∈ stalled,
      1 ≤ chartLadderPivot direction point.mass point.weight stalled label)
    (hcard : sub.card + 1 = stalled.card)
    (hsel : (directionChartGap direction point.mass point.weight sub).PosDef) :
    ∃ label ∈ sub, label ∉ stalled := by
  by_contra hcontra
  have hsub : sub ⊆ stalled := by
    intro x hx
    by_contra hxn
    exact hcontra ⟨x, hx, hxn⟩
  exact not_posDef_directionChartGap_of_subset_of_stall direction point hpd
    hstall hsub hcard hsel

/-- **THE PIVOT WALL CONFINES ITS WINNERS.**  At a K4 pivot wall the pointer
window is a four-label stall, so every positive-definite spanning tree carries
a label outside that window.  The window holds four of the six labels: the
winner therefore meets the two-label complement, and no atlas cell supported
inside the window can fire. -/
theorem kFourPivotWall_winner_escapes_window (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} (htree : tree ∈ kFourSpanningTreeList)
    (hwall : KFourTreeWindowAllPivotWallData point tree) :
    ∃ pointer : Fin 6, pointer ∉ tree ∧
      (directionChartGap kFourDirection point.mass point.weight
        (insert pointer tree)).PosDef ∧
      ∀ winner : Finset (Fin 6), winner.card = 3 →
        (directionChartGap kFourDirection point.mass point.weight
          winner).PosDef →
        ∃ label ∈ winner, label ∉ insert pointer tree := by
  obtain ⟨pointer, hpointer, hpdWindow, hstall⟩ := hwall
  refine ⟨pointer, hpointer, hpdWindow, ?_⟩
  intro winner hcard hwinner
  have hwindowCard : (insert pointer tree).card = 4 := by
    rw [Finset.card_insert_of_notMem hpointer, kFourSpanningTree_card tree htree]
  exact exists_notMem_of_posDef_of_stall kFourDirection point hpdWindow hstall
    (by rw [hcard, hwindowCard]) hwinner

end Gtz

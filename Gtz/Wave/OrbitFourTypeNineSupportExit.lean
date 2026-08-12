import Gtz.Wave.OrbitFourAlignedZeroDetExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- Ambient support of a multiplier-weighted active tight column. -/
noncomputable def orbitFourWeightedColumnSupport
    (B : Matrix (Fin 6) (Fin 4) ℝ) (label : Fin 4) : Finset (Fin 6) :=
  Finset.univ.filter fun atomIndex => B atomIndex label ≠ 0

theorem orbitFourWeightedColumnSupport_mem_iff
    (B : Matrix (Fin 6) (Fin 4) ℝ) (label : Fin 4) (atomIndex : Fin 6) :
    atomIndex ∈ orbitFourWeightedColumnSupport B label
      ↔ B atomIndex label ≠ 0 := by
  simp [orbitFourWeightedColumnSupport]

theorem orbitFourWeightedColumn_eq_zero_of_not_mem
    (B : Matrix (Fin 6) (Fin 4) ℝ) (label : Fin 4) (atomIndex : Fin 6)
    (hnot : atomIndex ∉ orbitFourWeightedColumnSupport B label) :
    B atomIndex label = 0 := by
  simpa [orbitFourWeightedColumnSupport] using hnot

theorem orbitFourWeightedColumn_ne_zero_of_mem
    (B : Matrix (Fin 6) (Fin 4) ℝ) (label : Fin 4) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ orbitFourWeightedColumnSupport B label) :
    B atomIndex label ≠ 0 := by
  simpa [orbitFourWeightedColumnSupport] using hmem

/-- **CANONICAL TYPE-NINE SUPPORT LEAF CLOSED.**  No coordinate choices are
part of the interface: the exact support pattern alone constructs the six row
forms and all required nonzero entries. -/
theorem SixThreeCrux.false_of_orbitFour_typeNineSupports
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = orbitFourFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (hsupportZero : orbitFourWeightedColumnSupport
      (orbitFourWeightedTightColumns multiplier tightDir) 0 = {1, 2})
    (hsupportOne : orbitFourWeightedColumnSupport
      (orbitFourWeightedTightColumns multiplier tightDir) 1 = {0, 1, 3})
    (hsupportTwo : orbitFourWeightedColumnSupport
      (orbitFourWeightedTightColumns multiplier tightDir) 2 = {0, 2, 3})
    (hsupportThree : orbitFourWeightedColumnSupport
      (orbitFourWeightedTightColumns multiplier tightDir) 3 = {1, 4, 5}) : False := by
  classical
  let B := orbitFourWeightedTightColumns multiplier tightDir
  change orbitFourWeightedColumnSupport B 0 = {1, 2} at hsupportZero
  change orbitFourWeightedColumnSupport B 1 = {0, 1, 3} at hsupportOne
  change orbitFourWeightedColumnSupport B 2 = {0, 2, 3} at hsupportTwo
  change orbitFourWeightedColumnSupport B 3 = {1, 4, 5} at hsupportThree
  have hzero (label : Fin 4) (atomIndex : Fin 6)
      (hnot : atomIndex ∉ orbitFourWeightedColumnSupport B label) :
      B atomIndex label = 0 :=
    orbitFourWeightedColumn_eq_zero_of_not_mem B label atomIndex hnot
  have hnonzero (label : Fin 4) (atomIndex : Fin 6)
      (hmem : atomIndex ∈ orbitFourWeightedColumnSupport B label) :
      B atomIndex label ≠ 0 :=
    orbitFourWeightedColumn_ne_zero_of_mem B label atomIndex hmem
  have h00 : B 0 0 = 0 := hzero 0 0 (by rw [hsupportZero]; decide)
  have h30 : B 3 0 = 0 := hzero 0 3 (by rw [hsupportZero]; decide)
  have h40 : B 4 0 = 0 := hzero 0 4 (by rw [hsupportZero]; decide)
  have h50 : B 5 0 = 0 := hzero 0 5 (by rw [hsupportZero]; decide)
  have h20 : B 2 0 ≠ 0 := hnonzero 0 2 (by rw [hsupportZero]; decide)
  have h01 : B 0 1 ≠ 0 := hnonzero 1 0 (by rw [hsupportOne]; decide)
  have h11 : B 1 1 ≠ 0 := hnonzero 1 1 (by rw [hsupportOne]; decide)
  have h21 : B 2 1 = 0 := hzero 1 2 (by rw [hsupportOne]; decide)
  have h31 : B 3 1 ≠ 0 := hnonzero 1 3 (by rw [hsupportOne]; decide)
  have h41 : B 4 1 = 0 := hzero 1 4 (by rw [hsupportOne]; decide)
  have h51 : B 5 1 = 0 := hzero 1 5 (by rw [hsupportOne]; decide)
  have h02 : B 0 2 ≠ 0 := hnonzero 2 0 (by rw [hsupportTwo]; decide)
  have h12 : B 1 2 = 0 := hzero 2 1 (by rw [hsupportTwo]; decide)
  have h22 : B 2 2 ≠ 0 := hnonzero 2 2 (by rw [hsupportTwo]; decide)
  have h32 : B 3 2 ≠ 0 := hnonzero 2 3 (by rw [hsupportTwo]; decide)
  have h42 : B 4 2 = 0 := hzero 2 4 (by rw [hsupportTwo]; decide)
  have h52 : B 5 2 = 0 := hzero 2 5 (by rw [hsupportTwo]; decide)
  have h03 : B 0 3 = 0 := hzero 3 0 (by rw [hsupportThree]; decide)
  have h13 : B 1 3 ≠ 0 := hnonzero 3 1 (by rw [hsupportThree]; decide)
  have h23 : B 2 3 = 0 := hzero 3 2 (by rw [hsupportThree]; decide)
  have h33 : B 3 3 = 0 := hzero 3 3 (by rw [hsupportThree]; decide)
  have h43 : B 4 3 ≠ 0 := hnonzero 3 4 (by rw [hsupportThree]; decide)
  have h53 : B 5 3 ≠ 0 := hnonzero 3 5 (by rw [hsupportThree]; decide)
  let x := B 1 0
  let y := B 2 0
  let a := B 0 1
  let r := B 0 2
  let b := B 1 1
  let c := B 3 1
  let f := B 3 2
  let e := B 2 2
  let h := B 1 3
  let k := B 4 3
  let z := B 5 3
  have hrowZero : B 0 = (![0, a, r, 0] : Fin 4 → ℝ) := by
    funext label
    fin_cases label <;> simp [a, r, h00, h03]
  have hrowOne : B 1 = (![x, b, 0, h] : Fin 4 → ℝ) := by
    funext label
    fin_cases label <;> simp [x, b, h, h12]
  have hrowTwo : B 2 = (![y, 0, e, 0] : Fin 4 → ℝ) := by
    funext label
    fin_cases label <;> simp [y, e, h21, h23]
  have hrowThree : B 3 = (![0, c, f, 0] : Fin 4 → ℝ) := by
    funext label
    fin_cases label <;> simp [c, f, h30, h33]
  have hrowFour : B 4 = (![0, 0, 0, k] : Fin 4 → ℝ) := by
    funext label
    fin_cases label <;> simp [k, h40, h41, h42]
  have hrowFive : B 5 = (![0, 0, 0, z] : Fin 4 → ℝ) := by
    funext label
    fin_cases label <;> simp [z, h50, h51, h52]
  exact crux.false_of_orbitFour_typeNineRows hfamily hdata
    hrowZero hrowOne hrowTwo hrowThree hrowFour hrowFive
    h01 h02 h31 h20 h11 h22 h43 h53


end Gtz

import Gtz.Design.LivePairRefusalStrata
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.KFourChartClosure
import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# A `(6,3)` tie whose leverages are NOT uniform

Every `(6,3)` tie fixture the tree carried before this one is uniform at
leverage `3`: `tetraDesign` is the regular tetrahedron, and `splitTetraAtom` is
`tetraAtom ∘ splitTetraDirIndex`, so `splitTetraDesign` inherits
`tetraAtom_dot_self`.  Consequently every criterion calibrated against the
tree's tie fixtures has only ever been calibrated on the EQUAL-LEVERAGE locus,
and a criterion that silently assumes equal leverage would pass every soundness
gate in the campaign.

This file removes that blind spot.  The design here is an exact tie whose
leverages are `19/3` three times and `4/3` three times.  Its three light atoms
are literally EQUAL, so it is a clone configuration and is not line-free — that
is deliberate, and it is why the fixture is admissible as a soundness gate but
not as an antecedent witness.

`Gtz/LinAlg/EigenvalueSubdifferential.lean` already observed IN PROSE that an
unequal-leverage `(6,3)` tie exists, obtained by splitting `sharpDesign`'s atoms
`0` and `1` to leverages `(4/3, 4/3, 19/3, 19/3, 19/3, 19/3)`.  That design was
never mechanized, and its leverage multiset differs from this one (four heavy
and two light, against three and three), so this fixture is not that one.

**Why the determinant cannot be the certificate, and this design proves it.**
The subset `{3,4,5}` has gap determinant `+3`, strictly POSITIVE, and is still
not positive definite: the three light atoms are equal, so that gap is a
rank-one perturbation of `-1` with inertia `(1, 0, 2)`.  Any test reading only
the determinant accepts `{3,4,5}` and is unsound.  The twenty certificates
below are therefore Rayleigh probes, not determinants.
-/

namespace Gtz

open Matrix

/-- The six atoms: three cyclic rotations of `(4/3, 4/3, -5/3)` at leverage
`19/3`, then the direction `(2/3, 2/3, 2/3)` three times at leverage `4/3`. -/
noncomputable def nonUniformLeverageTieAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![4 / 3, 4 / 3, -(5 / 3)]
  | 1 => ![-(5 / 3), 4 / 3, 4 / 3]
  | 2 => ![4 / 3, -(5 / 3), 4 / 3]
  | 3 => ![2 / 3, 2 / 3, 2 / 3]
  | 4 => ![2 / 3, 2 / 3, 2 / 3]
  | 5 => ![2 / 3, 2 / 3, 2 / 3]

/-- Weight `1/9` on each heavy atom and `2/9` on each light atom. -/
noncomputable def nonUniformLeverageTieWeight : Fin 6 → ℝ
  | 0 => 1 / 9
  | 1 => 1 / 9
  | 2 => 1 / 9
  | 3 => 2 / 9
  | 4 => 2 / 9
  | 5 => 2 / 9

/-- The fixture as a weighted `(6,3)` design.  Parseval is exact: the three
heavy atoms contribute `57/81` on the diagonal and `-24/81` off it, the three
light atoms contribute `24/81` everywhere, and the off-diagonal cancels. -/
noncomputable def nonUniformLeverageTieDesign : WeightedDesign 6 3 where
  atom := nonUniformLeverageTieAtom
  weight := nonUniformLeverageTieWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [nonUniformLeverageTieWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [nonUniformLeverageTieWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [nonUniformLeverageTieAtom, nonUniformLeverageTieWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem nonUniformLeverageTieDesign_atom :
    nonUniformLeverageTieDesign.atom = nonUniformLeverageTieAtom := rfl

theorem nonUniformLeverageTieDesign_weight :
    nonUniformLeverageTieDesign.weight = nonUniformLeverageTieWeight := rfl

/-- **The leverage profile: three atoms at `19/3` and three at `4/3`.** -/
theorem nonUniformLeverageTieDesign_leverage (label : Fin 6) :
    leverageOf (nonUniformLeverageTieDesign.atom label)
      = if label.val < 3 then 19 / 3 else 4 / 3 := by
  fin_cases label <;>
    norm_num [leverageOf, nonUniformLeverageTieDesign, nonUniformLeverageTieAtom,
      Fin.sum_univ_three, Matrix.cons_val_two]

/-- **The leverages are NOT uniform** — the property that makes this fixture
worth carrying, in the form a soundness gate consumes directly. -/
theorem nonUniformLeverageTieDesign_leverage_ne :
    leverageOf (nonUniformLeverageTieDesign.atom 0)
      ≠ leverageOf (nonUniformLeverageTieDesign.atom 3) := by
  rw [nonUniformLeverageTieDesign_leverage 0, nonUniformLeverageTieDesign_leverage 3]
  norm_num

/-- The three light atoms are literally equal: a clone configuration, so the
fixture is NOT line-free. -/
theorem nonUniformLeverageTieDesign_light_atoms_eq :
    nonUniformLeverageTieDesign.atom 3 = nonUniformLeverageTieDesign.atom 4
      ∧ nonUniformLeverageTieDesign.atom 4 = nonUniformLeverageTieDesign.atom 5 :=
  ⟨rfl, rfl⟩

/-- The Rayleigh value of a triple gap is the three squared pairings less the
squared probe norm.  Stated at general `size` and needing only distinctness. -/
theorem dotProduct_tripleGap_mulVec {size : ℕ} (design : WeightedDesign size 3)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum design {first, second, third} - 1) *ᵥ probe)
      = (design.atom first ⬝ᵥ probe) ^ 2 + (design.atom second ⬝ᵥ probe) ^ 2
        + (design.atom third ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
  rw [subsetSum_triple design hfirstSecond hfirstThird hsecondThird,
    Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Matrix.add_mulVec,
    Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    dotProduct_atomMatrix_mulVec_eq_sq, dotProduct_atomMatrix_mulVec_eq_sq,
    dotProduct_atomMatrix_mulVec_eq_sq]

/-- The base gap is the circulant with diagonal `16/3` and off-diagonal `-8/3`. -/
theorem nonUniformLeverageTieDesign_baseTripleGap_form :
    subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6)) - 1
      = !![16 / 3, -(8 / 3), -(8 / 3); -(8 / 3), 16 / 3, -(8 / 3);
          -(8 / 3), -(8 / 3), 16 / 3] := by
  rw [subsetSum_triple nonUniformLeverageTieDesign (by decide) (by decide) (by decide)]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, atomMatrix,
      Matrix.one_fin_three, Matrix.cons_val_two] <;> norm_num

/-- The base gap is singular. -/
theorem nonUniformLeverageTieDesign_baseTripleGap_det :
    (subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6)) - 1).det = 0 := by
  rw [nonUniformLeverageTieDesign_baseTripleGap_form, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **WEAK DOMINATION** at the base triple, from the exact sum of squares
`(8/3) [(x - y)^2 + (y - z)^2 + (x - z)^2]`. -/
theorem nonUniformLeverageTieDesign_dominates_baseTriple :
    Dominates nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (nonUniformLeverageTieDesign.atom label)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, nonUniformLeverageTieDesign_baseTripleGap_form]
    have hform : probeVec ⬝ᵥ
        ((!![16 / 3, -(8 / 3), -(8 / 3); -(8 / 3), 16 / 3, -(8 / 3);
            -(8 / 3), -(8 / 3), 16 / 3] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probeVec)
        = 8 / 3 * ((probeVec 0 - probeVec 1) ^ 2 + (probeVec 1 - probeVec 2) ^ 2
            + (probeVec 0 - probeVec 2) ^ 2) := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
      ring
    rw [hform]
    positivity

theorem nonUniformLeverageTieDesign_tightDirection_ne_zero :
    (![1, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry : (![1, 1, 1] : Fin 3 → ℝ) 0 = 0 := by rw [hzero]; rfl
  norm_num at hentry

/-- The base gap annihilates `(1,1,1)`: an explicit tight direction. -/
theorem nonUniformLeverageTieDesign_isTightDirection :
    IsTightDirectionOf nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6)) ![1, 1, 1] := by
  show (![1, 1, 1] : Fin 3 → ℝ) ⬝ᵥ
    ((subsetSum nonUniformLeverageTieDesign ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ ![1, 1, 1]) = 0
  rw [nonUniformLeverageTieDesign_baseTripleGap_form]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- **The determinant is blind here, and this is the witness.**  The gap of the
three equal light atoms has determinant `+3`, strictly positive, while its
inertia is `(1, 0, 2)`. -/
theorem nonUniformLeverageTieDesign_lightTripleGap_det :
    (subsetSum nonUniformLeverageTieDesign ({3, 4, 5} : Finset (Fin 6)) - 1).det = 3 := by
  rw [subsetSum_triple nonUniformLeverageTieDesign (by decide) (by decide) (by decide)]
  have hform : atomMatrix (nonUniformLeverageTieDesign.atom 3)
      + atomMatrix (nonUniformLeverageTieDesign.atom 4)
      + atomMatrix (nonUniformLeverageTieDesign.atom 5) - 1
      = !![1 / 3, 4 / 3, 4 / 3; 4 / 3, 1 / 3, 4 / 3; 4 / 3, 4 / 3, 1 / 3] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, atomMatrix,
        Matrix.one_fin_three, Matrix.cons_val_two] <;> norm_num
  rw [hform, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **NO CARD-THREE SUBSET DOMINATES STRICTLY.**  Each of the twenty subsets is
killed by an explicit Rayleigh probe with entries in `{-1, 0, 1}`; seven probes
suffice.  The ten subsets carrying at least two heavy atoms are tight (Rayleigh
value exactly `0`); the ten carrying at least two of the equal light atoms are
rank-deficient (Rayleigh value `-2`). -/
theorem nonUniformLeverageTieDesign_not_posDef_cardThree
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ¬ (subsetSum nonUniformLeverageTieDesign selected - 1).PosDef := by
  have hmem : selected ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)) := by
    simp [Finset.mem_powersetCard, hcard]
  have hprobeNe : ∀ (probe : Fin 3 → ℝ) (slot : Fin 3), probe slot ≠ 0 → probe ≠ 0 := by
    intro probe slot hslot hzero
    exact hslot (by rw [hzero]; rfl)
  -- One reusable killer: a probe of nonpositive Rayleigh value refutes strictness.
  have hkill : ∀ (first second third : Fin 6) (probe : Fin 3 → ℝ),
      first ≠ second → first ≠ third → second ≠ third → probe ≠ 0 →
      (nonUniformLeverageTieDesign.atom first ⬝ᵥ probe) ^ 2
          + (nonUniformLeverageTieDesign.atom second ⬝ᵥ probe) ^ 2
          + (nonUniformLeverageTieDesign.atom third ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe ≤ 0 →
      ¬ (subsetSum nonUniformLeverageTieDesign
          ({first, second, third} : Finset (Fin 6)) - 1).PosDef := by
    intro first second third probe hfirstSecond hfirstThird hsecondThird hprobe hvalue
    refine not_posDef_of_dotProduct_mulVec_nonpos _ probe hprobe ?_
    rw [dotProduct_tripleGap_mulVec nonUniformLeverageTieDesign
      hfirstSecond hfirstThird hsecondThird]
    exact hvalue
  have hOneOneOne : (![1, 1, 1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneZeroOne : (![1, 0, 1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hZeroOneOne : (![0, 1, 1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 1 (by norm_num)
  have hOneOneZero : (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneNegOneZero : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hZeroOneNegOne : (![0, 1, -1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 1 (by norm_num)
  have hOneZeroNegOne : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  rcases cardThreeFinsetsOfSix_enumeration selected hmem with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact hkill 0 1 2 ![1, 1, 1] (by decide) (by decide) (by decide) hOneOneOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 1 3 ![1, 0, 1] (by decide) (by decide) (by decide) hOneZeroOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 1 4 ![1, 0, 1] (by decide) (by decide) (by decide) hOneZeroOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 1 5 ![1, 0, 1] (by decide) (by decide) (by decide) hOneZeroOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 2 3 ![0, 1, 1] (by decide) (by decide) (by decide) hZeroOneOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 2 4 ![0, 1, 1] (by decide) (by decide) (by decide) hZeroOneOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 2 5 ![0, 1, 1] (by decide) (by decide) (by decide) hZeroOneOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 3 4 ![1, -1, 0] (by decide) (by decide) (by decide) hOneNegOneZero (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 3 5 ![1, -1, 0] (by decide) (by decide) (by decide) hOneNegOneZero (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 4 5 ![1, -1, 0] (by decide) (by decide) (by decide) hOneNegOneZero (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 2 3 ![1, 1, 0] (by decide) (by decide) (by decide) hOneOneZero (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 2 4 ![1, 1, 0] (by decide) (by decide) (by decide) hOneOneZero (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 2 5 ![1, 1, 0] (by decide) (by decide) (by decide) hOneOneZero (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 3 4 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 3 5 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 4 5 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 2 3 4 ![1, 0, -1] (by decide) (by decide) (by decide) hOneZeroNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 2 3 5 ![1, 0, -1] (by decide) (by decide) (by decide) hOneZeroNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 2 4 5 ![1, 0, -1] (by decide) (by decide) (by decide) hOneZeroNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 3 4 5 ![1, 0, -1] (by decide) (by decide) (by decide) hOneZeroNegOne (by
      norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])

/-- **THE FIXTURE IS AN EXACT TIE.**  The base triple dominates weakly and no
card-three subset dominates strictly. -/
theorem nonUniformLeverageTieDesign_isTie : IsTie nonUniformLeverageTieDesign :=
  ⟨⟨({0, 1, 2} : Finset (Fin 6)), by decide,
      nonUniformLeverageTieDesign_dominates_baseTriple⟩,
    nonUniformLeverageTieDesign_not_posDef_cardThree⟩

end Gtz

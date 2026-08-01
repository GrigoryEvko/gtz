/-
# The Veronese dichotomy between the two fields, and a stress-free complex `(7,3)`

The stress-walk reduction (`Gtz/Reduction/StressWalk.lean`,
`Gtz/Reduction/StressConditionalWalk.lean`) runs on one count: seven rank-one
SYMMETRIC `3 x 3` matrices cannot be independent, because `dim_R Sym_3(R) = 6`.
Both files record, as ORIENTATION PROSE, that the count has no complex analogue --
`dim_R Herm_3(C) = 9` and `7 < 9`, so seven complex atoms need carry no stress at
all.  Each hedges honestly (`not mechanized in this file`, `not a theorem of this
file`).  This file supplies the two theorems the hedges point at.

## What is here

**THE REAL HALF.**  `Gtz.span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent`:
six linearly independent Veronese images at rank three SPAN the symmetric matrices.
Independence therefore upgrades to a basis, because `dim_R Sym_3(R) = 6` on the nose.
`Gtz.SixThreeCrux.span_veronese_eq_symmetricSubmodule` reads that at a crux, where
the shipped `Gtz.SixThreeCrux.linearIndependent_veronese` supplies the hypothesis.

**THE COMPLEX HALF.**  `Gtz.span_complexAtom_hermitianSpanAtom`: NINE explicit
Veronese images span the Hermitians, so the rank-one Hermitians really do reach all
nine real dimensions and the gap is not an artifact of comparing rank-one images
against a larger space.  `Gtz.exists_mem_hermitianSubmodule_notMem_span_of_six` and
its Veronese form `Gtz.exists_complexAtom_notMem_span_complexAtom_of_six` then say
that SIX matrices never span -- the exact converse of the real half.

**THE WITNESS.**  `Gtz.stressFreeSevenDesign` is a complex `(7,3)` design with
rational weights and Gaussian-rational atoms whose seven Veronese images are
linearly independent over `R`:
`Gtz.exists_complexWeightedDesign_sevenThree_stress_eq_zero`.  A complex `(7,3)`
design can carry NO STRESS, so the real reduction's mechanism is not merely
unproved over `C` -- it is absent.

## The witness, and why it is not the obvious one

A stress is a real dependency `Sum_c stress_c g_c g_c^* = 0`, so a design whose
atoms contain two disjoint tight frames automatically carries one (their scaled
difference).  That kills the natural candidates: an orthonormal basis together
with any tight frame, and the two-MUB family, both of which self-destruct this way.
The atoms below avoid it by cancelling the three off-diagonal blocks SEPARATELY and
by three different mechanisms -- a complex triple whose `(0,1)` pairings sit at
three directions surrounding the origin, and two antipodal real pairs for `(0,2)`
and `(1,2)` -- so no sub-family resolves a multiple of the identity except the whole.

    atom      (1,1,0)  (1,-1-i,0)  (1,-1+i,0)  (3,0,3)  (3,0,-3)  (0,1,1/2)  (0,1,-1/2)
    weight     1/11      1/22        1/22       1/22     1/22       4/11       4/11

The pairing directions of the first three are `(1,0)`, `(-1,1)` and `(-1,-1)`, which
surround the origin with weights `2 : 1 : 1`; the scales `3` and `1/2` are what make
the weights sum to one with the atoms Gaussian-rational, so no square root appears.

## PROVENANCE

`dim_R Herm_3(C) = 9` is NOT proved here.  It is the shipped, tracked
`Gtz.finrank_hermitianSubmodule` (`Gtz/Quantitative/RankTwoRealnessCount.lean`),
together with `Gtz.two_mul_finrank_symmetricSubmodule` for the real side; this file
consumes both.  What was genuinely missing is the VERONESE layer on top: that the
rank-one images attain those dimensions, and that a complex `(7,3)` DESIGN can be
stress-free.

## WHAT THIS DOES NOT DO

It does not touch `Gtz.GtzWeighted 6 3`, and it cannot: everything below is a
statement about `C`, where weighted GTZ at rank three is already FALSE
(`Gtz.complexGtzWeighted_iff_size_le_rank_add_one`).  Its content is negative --
it says which real mechanism does NOT transport, and thereby that a closing proof
must consume realness somewhere the stress walk does not.

The witness is ONE design.  Nothing here says a GENERIC complex `(7,3)` design is
stress-free (measured elsewhere at the Hesse-SIC configuration, not mechanized), and
nothing here bounds how many complex `(7,3)` designs do carry a stress.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.Complex.ComplexWitness
import Gtz.Quantitative.RankTwoRealnessCount
import Gtz.Quantitative.SixThreeStressExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Complex

/-! ## A finrank bound on the span of a finite family -/

/-- The span of a `Fin count`-indexed family has rank at most `count`.  Ambient-generic:
`Gtz.le_card_of_linearIndependent_mem_span` (`Gtz/Quantitative/ChartSecondOrder.lean`)
carries this same step inline at its lines 241-247, but fixed to the ambient
`Fin ambient -> R`; the matrices below are not of that shape. -/
theorem finrank_span_range_le {Ambient : Type*} [AddCommGroup Ambient] [Module ℝ Ambient]
    {count : ℕ} (family : Fin count → Ambient) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range family)) ≤ count := by
  classical
  refine (finrank_span_le_card (R := ℝ) (Set.range family)).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le.trans (by simp)

/-! ## The real half: six independent Veronese images are a basis of the symmetrics -/

/-- A real Veronese image is symmetric. -/
theorem atomMatrix_mem_symmetricSubmodule {rank : ℕ} (vector : Fin rank → ℝ) :
    atomMatrix vector ∈ symmetricSubmodule rank := by
  rw [mem_symmetricSubmodule_iff]
  exact transpose_eq_of_isHermitian (posSemidef_atomMatrix vector).1

/-- **THE REAL HALF OF THE DICHOTOMY.**  Six linearly independent Veronese images at
rank three SPAN the symmetric matrices: `dim_R Sym_3(R) = 6` on the nose, so
independence upgrades to a basis. -/
theorem span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent
    (atoms : Fin 6 → (Fin 3 → ℝ))
    (hindependent : LinearIndependent ℝ fun atomIndex => atomMatrix (atoms atomIndex)) :
    Submodule.span ℝ (Set.range fun atomIndex => atomMatrix (atoms atomIndex))
      = symmetricSubmodule 3 := by
  have hsymmetric : Module.finrank ℝ (symmetricSubmodule 3) = 6 := by
    have hdouble := two_mul_finrank_symmetricSubmodule 3
    omega
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨atomIndex, rfl⟩
    exact atomMatrix_mem_symmetricSubmodule _
  · rw [finrank_span_eq_card hindependent, Fintype.card_fin, hsymmetric]

/-- At a `(6,3)` crux the six Veronese images are a BASIS of `Sym_3(R)`: the shipped
`Gtz.SixThreeCrux.linearIndependent_veronese` plus the dimension count. -/
theorem SixThreeCrux.span_veronese_eq_symmetricSubmodule (crux : SixThreeCrux) :
    Submodule.span ℝ (Set.range fun atomIndex => atomMatrix (crux.design.atom atomIndex))
      = symmetricSubmodule 3 :=
  span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent _ crux.linearIndependent_veronese

/-! ## The complex half: nine Veronese images span, so six never can -/

/-- Nine complex directions in `C^3`.  Their Veronese images are the standard real
basis of the Hermitians: three diagonal, three real off-diagonal, three imaginary. -/
def hermitianSpanAtom : Fin 9 → (Fin 3 → ℂ) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![1, 1, 0], ![1, 0, 1], ![0, 1, 1],
    ![1, Complex.I, 0], ![1, 0, Complex.I], ![0, 1, Complex.I]]

/-- A complex Veronese image is Hermitian. -/
theorem complexAtom_mem_hermitianSubmodule {rank : ℕ} (vector : Fin rank → ℂ) :
    complexAtom vector ∈ hermitianSubmodule rank := by
  rw [mem_hermitianSubmodule_iff]
  exact conjTranspose_complexAtom rank vector

/-- The nine Veronese images are linearly independent OVER THE REALS.  Each of the six
off-diagonal real coordinates is private to one atom, and the three diagonal atoms mop
up what is left. -/
theorem linearIndependent_complexAtom_hermitianSpanAtom :
    LinearIndependent ℝ fun index : Fin 9 => complexAtom (hermitianSpanAtom index) := by
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum
  have entry : ∀ rowIndex colIndex : Fin 3,
      (∑ index, coeff index • complexAtom (hermitianSpanAtom index)) rowIndex colIndex = 0 := by
    intro rowIndex colIndex
    rw [hsum]; rfl
  have offZeroOne := entry 0 1
  have offZeroTwo := entry 0 2
  have offOneTwo := entry 1 2
  have diagZeroZero := entry 0 0
  have diagOneOne := entry 1 1
  have diagTwoTwo := entry 2 2
  simp [Matrix.sum_apply, Matrix.smul_apply, complexAtom, Matrix.vecMulVec_apply,
    Fin.sum_univ_succ, hermitianSpanAtom, Complex.ext_iff, Complex.real_smul]
    at offZeroOne offZeroTwo offOneTwo diagZeroZero diagOneOne diagTwoTwo
  obtain ⟨hthree, hsix⟩ := offZeroOne
  obtain ⟨hfour, hseven⟩ := offZeroTwo
  obtain ⟨hfive, height⟩ := offOneTwo
  rw [hthree, hfour, hsix, hseven] at diagZeroZero
  rw [hthree, hfive, hsix, height] at diagOneOne
  rw [hfour, hfive, hseven, height] at diagTwoTwo
  intro index
  fin_cases index <;> simp_all

/-- **NINE VERONESE IMAGES SPAN THE HERMITIANS.**  Over `C` the rank-one Hermitians
reach every Hermitian matrix, and it takes `rank ^ 2 = 9` of them -- against the
`rank * (rank + 1) / 2 = 6` that suffice over `R`. -/
theorem span_complexAtom_hermitianSpanAtom :
    Submodule.span ℝ (Set.range fun index : Fin 9 => complexAtom (hermitianSpanAtom index))
      = hermitianSubmodule 3 := by
  have hhermitian : Module.finrank ℝ (hermitianSubmodule 3) = 9 := by
    rw [finrank_hermitianSubmodule]; norm_num
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨index, rfl⟩
    exact complexAtom_mem_hermitianSubmodule _
  · rw [finrank_span_eq_card linearIndependent_complexAtom_hermitianSpanAtom,
      Fintype.card_fin, hhermitian]

/-- **THE COMPLEX HALF OF THE DICHOTOMY.**  SIX matrices never span the Hermitians:
`9 = dim_R Herm_3(C) > 6`.  Over `R` six Veronese images can be a basis of the
symmetrics; over `C` no six matrices whatsoever reach every Hermitian. -/
theorem exists_mem_hermitianSubmodule_notMem_span_of_six
    (family : Fin 6 → Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ target ∈ hermitianSubmodule 3, target ∉ Submodule.span ℝ (Set.range family) := by
  have hnotle : ¬ hermitianSubmodule 3 ≤ Submodule.span ℝ (Set.range family) := by
    intro hle
    have hhermitian : Module.finrank ℝ (hermitianSubmodule 3) = 9 := by
      rw [finrank_hermitianSubmodule]; norm_num
    have hmono := Submodule.finrank_mono (R := ℝ) hle
    have hcount := finrank_span_range_le family
    omega
  rw [SetLike.not_le_iff_exists] at hnotle
  exact hnotle

/-- The same at the Veronese level, which is where the dichotomy bites: whatever six
complex directions one picks, one of the nine reference images escapes their real
span.  Over `R` the corresponding statement is FALSE -- six independent Veronese
images span everything (`Gtz.span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent`). -/
theorem exists_complexAtom_notMem_span_complexAtom_of_six (atoms : Fin 6 → (Fin 3 → ℂ)) :
    ∃ index : Fin 9, complexAtom (hermitianSpanAtom index)
      ∉ Submodule.span ℝ (Set.range fun atomIndex => complexAtom (atoms atomIndex)) := by
  by_contra hcontra
  have hmem : ∀ index : Fin 9, complexAtom (hermitianSpanAtom index)
      ∈ Submodule.span ℝ (Set.range fun atomIndex => complexAtom (atoms atomIndex)) :=
    fun index => not_not.mp (not_exists.mp hcontra index)
  obtain ⟨target, htarget, hnotmem⟩ :=
    exists_mem_hermitianSubmodule_notMem_span_of_six
      fun atomIndex => complexAtom (atoms atomIndex)
  refine hnotmem ?_
  rw [← span_complexAtom_hermitianSpanAtom] at htarget
  refine Submodule.span_le.mpr ?_ htarget
  rintro _ ⟨index, rfl⟩
  exact hmem index

/-! ## A complex `(7,3)` design that carries no stress -/

/-- The seven atoms of the stress-free complex design.  Gaussian-rational throughout;
the scales `3` and `1/2` are what let the weights sum to one without a square root. -/
noncomputable def stressFreeSevenAtom : Fin 7 → (Fin 3 → ℂ) :=
  ![![1, 1, 0], ![1, -1 - Complex.I, 0], ![1, -1 + Complex.I, 0],
    ![3, 0, 3], ![3, 0, -3], ![0, 1, 1/2], ![0, 1, -1/2]]

/-- The seven weights.  The `2 : 1 : 1` on the complex triple is what cancels its
three pairing directions; the two real pairs cancel antipodally at equal weight. -/
noncomputable def stressFreeSevenWeight : Fin 7 → ℝ :=
  ![1/11, 1/22, 1/22, 1/22, 1/22, 4/11, 4/11]

theorem stressFreeSevenWeight_pos : ∀ atomIndex, 0 < stressFreeSevenWeight atomIndex := by
  intro atomIndex
  fin_cases atomIndex <;> norm_num [stressFreeSevenWeight]

theorem stressFreeSevenWeight_sum_one : ∑ atomIndex, stressFreeSevenWeight atomIndex = 1 := by
  simp [stressFreeSevenWeight, Fin.sum_univ_succ]
  norm_num

theorem stressFreeSevenParseval :
    ∑ atomIndex, ((stressFreeSevenWeight atomIndex : ℝ) : ℂ)
      • complexAtom (stressFreeSevenAtom atomIndex) = 1 := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Matrix.sum_apply, Matrix.smul_apply, complexAtom, Matrix.vecMulVec_apply,
      Fin.sum_univ_succ, stressFreeSevenAtom, stressFreeSevenWeight, Complex.ext_iff,
      Complex.real_smul, Complex.conj_ofNat] <;> norm_num

/-- **THE STRESS-FREE COMPLEX DESIGN**, at the size where the real walk manufactures
its stress. -/
noncomputable def stressFreeSevenDesign : ComplexWeightedDesign 7 3 where
  atom := stressFreeSevenAtom
  weight := stressFreeSevenWeight
  weight_pos := stressFreeSevenWeight_pos
  weight_sum_one := stressFreeSevenWeight_sum_one
  isParseval := stressFreeSevenParseval

@[simp] theorem stressFreeSevenDesign_atom :
    stressFreeSevenDesign.atom = stressFreeSevenAtom := rfl

/-- The seven Veronese images are linearly independent over `R`.  The three
off-diagonal blocks pin the three cancelling groups, and the three diagonal entries
then force every coefficient to zero. -/
theorem linearIndependent_complexAtom_stressFreeSevenAtom :
    LinearIndependent ℝ fun atomIndex : Fin 7 => complexAtom (stressFreeSevenAtom atomIndex) := by
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum
  have entry : ∀ rowIndex colIndex : Fin 3,
      (∑ atomIndex, coeff atomIndex • complexAtom (stressFreeSevenAtom atomIndex))
        rowIndex colIndex = 0 := by
    intro rowIndex colIndex
    rw [hsum]; rfl
  have offZeroOne := entry 0 1
  have offZeroTwo := entry 0 2
  have offOneTwo := entry 1 2
  have diagZeroZero := entry 0 0
  have diagOneOne := entry 1 1
  have diagTwoTwo := entry 2 2
  simp [Matrix.sum_apply, Matrix.smul_apply, complexAtom, Matrix.vecMulVec_apply,
    Fin.sum_univ_succ, stressFreeSevenAtom, Complex.ext_iff, Complex.real_smul,
    Complex.conj_ofNat]
    at offZeroOne offZeroTwo offOneTwo diagZeroZero diagOneOne diagTwoTwo
  obtain ⟨hpairingReal, hpairingImaginary⟩ := offZeroOne
  have hzero : coeff 0 = 0 := by linarith
  have hone : coeff 1 = 0 := by linarith
  have htwo : coeff 2 = 0 := by linarith
  have hthree : coeff 3 = 0 := by linarith
  have hfour : coeff 4 = 0 := by linarith
  have hfive : coeff 5 = 0 := by linarith
  have hsix : coeff 6 = 0 := by linarith
  intro atomIndex
  fin_cases atomIndex <;> assumption

/-- **THE WITNESS, at the design.**  Every real stress of `Gtz.stressFreeSevenDesign`
vanishes. -/
theorem stressFreeSevenDesign_stress_eq_zero (stress : Fin 7 → ℝ)
    (hstress : ∑ atomIndex, stress atomIndex
      • complexAtom (stressFreeSevenDesign.atom atomIndex) = 0) :
    stress = 0 := by
  funext atomIndex
  exact Fintype.linearIndependent_iff.mp
    linearIndependent_complexAtom_stressFreeSevenAtom stress hstress atomIndex

/-- **SEVEN COMPLEX ATOMS CARRY NO FORCED STRESS.**  There is a complex `(7,3)` design
whose only real stress is zero, so the dependency the real walk manufactures out of
`7 > 6 = dim_R Sym_3(R)` simply does not exist over `C`, where the count reads
`7 < 9 = dim_R Herm_3(C)`. -/
theorem exists_complexWeightedDesign_sevenThree_stress_eq_zero :
    ∃ design : ComplexWeightedDesign 7 3, ∀ stress : Fin 7 → ℝ,
      (∑ atomIndex, stress atomIndex • complexAtom (design.atom atomIndex) = 0) →
        stress = 0 :=
  ⟨stressFreeSevenDesign, stressFreeSevenDesign_stress_eq_zero⟩

/-! ## The two halves side by side, in the hypothesis shape the walk consumes -/

/-- **OVER `R`, EVERY SEVEN-FAMILY AT RANK THREE CARRIES A NONZERO STRESS.**  The
shipped `Gtz.exists_parsevalNullDirection` at `6 < 7`; restated here only so the
contrast below is a comparison of two theorems rather than of a theorem with prose. -/
theorem exists_nonzero_stress_atomMatrix_sevenThree (atoms : Fin 7 → (Fin 3 → ℝ)) :
    ∃ stress : Fin 7 → ℝ, stress ≠ 0
      ∧ (∑ atomIndex, stress atomIndex • atomMatrix (atoms atomIndex)) = 0 :=
  exists_parsevalNullDirection atoms (by norm_num)

/-- **OVER `C`, THIS SEVEN-ATOM DESIGN CARRIES NONE.**  Written in the exact shape of
the hypothesis pair `(hnonzero, hstress)` that the shipped stress-conditional walk
`Gtz.exists_dominating_sixThree_of_stress` consumes, so the failure of transport is a
direct comparison with `Gtz.exists_nonzero_stress_atomMatrix_sevenThree`. -/
theorem not_exists_nonzero_stress_stressFreeSevenDesign :
    ¬ ∃ stress : Fin 7 → ℝ, stress ≠ 0
      ∧ (∑ atomIndex, stress atomIndex
          • complexAtom (stressFreeSevenDesign.atom atomIndex)) = 0 := by
  rintro ⟨stress, hnonzero, hstress⟩
  exact hnonzero (stressFreeSevenDesign_stress_eq_zero stress hstress)

end Gtz

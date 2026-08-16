/-
# The coplanarity rigidity of branch (i)

A stress-free `(6,3)` design carries NO four atoms in a common plane.  The
obstruction is a product of two planes.

## The mechanism

Let a nonzero `normal` annihilate every atom outside a named pair.  Take a
nonzero `w` perpendicular to the two atoms of that pair.  The symmetric product
`Gtz.orthogonalPairConic normal w` has value `2 * (normal . g) * (w . g)` at a
direction `g`.  Outside the pair the first factor vanishes.  At the pair the
second factor vanishes.  So the conic annihilates all six directions.

`Gtz.stressFree_iff_no_conic_sixThree` turns that conic into a stress, so no
stress-free family admits such a normal.  Four coplanar atoms leave two labels
free, and the theorem applies with those two as the pair.

## Scope

Nothing here needs a design.  The statements read the atom family alone, and the
design-level corollaries only rename `design.atom`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StressFreeStratum
import Gtz.Wave.VeroneseWeightElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

/-! ## Part 1: the common perpendicular -/

/-- **TWO VECTORS OF THREE-SPACE HAVE A COMMON PERPENDICULAR.**  The three-by-three
matrix whose rows are the two vectors and zero is singular, so its kernel is
nontrivial. -/
theorem exists_commonPerp (first second : Fin 3 → ℝ) :
    ∃ perp : Fin 3 → ℝ, perp ≠ 0 ∧ perp ⬝ᵥ first = 0 ∧ perp ⬝ᵥ second = 0 := by
  classical
  set rowMatrix : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![first, second, 0] with hrowMatrix
  have hrow : ∀ colIndex, rowMatrix 2 colIndex = 0 := by
    intro colIndex
    simp [hrowMatrix]
  have hdet : rowMatrix.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 hrow
  obtain ⟨perp, hperpNe, hkernel⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := rowMatrix)).mpr hdet
  refine ⟨perp, hperpNe, ?_, ?_⟩
  · have hzero := congrFun hkernel 0
    have hentry : (rowMatrix *ᵥ perp) 0 = first ⬝ᵥ perp := by
      simp [Matrix.mulVec, hrowMatrix]
    rw [hentry] at hzero
    rw [dotProduct_comm]
    simpa using hzero
  · have hzero := congrFun hkernel 1
    have hentry : (rowMatrix *ᵥ perp) 1 = second ⬝ᵥ perp := by
      simp [Matrix.mulVec, hrowMatrix]
    rw [hentry] at hzero
    rw [dotProduct_comm]
    simpa using hzero

/-! ## Part 2: the pair conic without an orthogonality hypothesis -/

/-- **THE PAIR CONIC IS NONZERO WITHOUT ORTHOGONALITY.**  `Gtz.orthogonalPairConic_ne_zero`
needs the two vectors to be perpendicular.  Two nonzero vectors alone already
give a nonzero conic. -/
theorem orthogonalPairConic_ne_zero_of_ne_zero {normal probe : Fin 3 → ℝ}
    (hnormal : normal ≠ 0) (hprobe : probe ≠ 0) :
    orthogonalPairConic normal probe ≠ 0 := by
  intro hzero
  have hself : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  have hval := orthogonalPairConic_form normal probe probe
  rw [hzero, Matrix.zero_mulVec, dotProduct_zero] at hval
  have hprod : (normal ⬝ᵥ probe) * (probe ⬝ᵥ probe) = 0 := by linarith [hval]
  have horth : normal ⬝ᵥ probe = 0 := by
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact hleft
    · exact absurd hright (ne_of_gt hself)
  exact orthogonalPairConic_ne_zero hnormal hprobe horth hzero

/-! ## Part 3: a normal off a pair produces a conic -/

/-- **A COMMON NORMAL OFF A PAIR PUTS THE SIX DIRECTIONS ON A CONIC.**  Let a
nonzero `normal` read zero against every atom outside `{first, second}`.  Then a
nonzero symmetric form annihilates all six directions. -/
theorem exists_conic_of_common_normal_off_pair (atomFamily : Fin 6 → Fin 3 → ℝ)
    (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0) (first second : Fin 6)
    (hflat : ∀ label, label ≠ first → label ≠ second → atomFamily label ⬝ᵥ normal = 0) :
    ∃ conic : Matrix (Fin 3) (Fin 3) ℝ, conic ≠ 0 ∧ conicᵀ = conic
      ∧ ∀ label, atomFamily label ⬝ᵥ (conic *ᵥ atomFamily label) = 0 := by
  obtain ⟨perp, hperpNe, hperpFirst, hperpSecond⟩ :=
    exists_commonPerp (atomFamily first) (atomFamily second)
  refine ⟨orthogonalPairConic normal perp,
    orthogonalPairConic_ne_zero_of_ne_zero hnormal hperpNe,
    orthogonalPairConic_symm _ _, fun label => ?_⟩
  rw [orthogonalPairConic_form]
  by_cases hfirst : label = first
  · subst hfirst
    rw [hperpFirst]
    ring
  · by_cases hsecond : label = second
    · subst hsecond
      rw [hperpSecond]
      ring
    · have hzero : normal ⬝ᵥ atomFamily label = 0 := by
        rw [dotProduct_comm]
        exact hflat label hfirst hsecond
      rw [hzero]
      ring

/-! ## Part 4: branch (i) refuses such a normal -/

/-- **NO NONZERO NORMAL IS FLAT OFF A PAIR ON BRANCH (i).**  Some label outside
the pair reads nonzero against the normal. -/
theorem not_common_normal_off_pair_of_stressFree (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex)) = 0 →
        stressCoeff = 0)
    (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0) (first second : Fin 6) :
    ∃ label, label ≠ first ∧ label ≠ second ∧ atomFamily label ⬝ᵥ normal ≠ 0 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨conic, hconicNe, hconicSymm, hconicVanishes⟩ :=
    exists_conic_of_common_normal_off_pair atomFamily normal hnormal first second hcontra
  exact hconicNe ((stressFree_iff_no_conic_sixThree atomFamily).mp hstressFree conic
    hconicSymm hconicVanishes)

/-- **FIVE ATOMS NEVER SHARE A PLANE ON BRANCH (i)**: the pair collapses to one
label and the conic argument still runs. -/
theorem not_five_coplanar_of_stressFree (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex)) = 0 →
        stressCoeff = 0)
    (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0) (exempt : Fin 6) :
    ∃ label, label ≠ exempt ∧ atomFamily label ⬝ᵥ normal ≠ 0 := by
  obtain ⟨label, hfirst, _, hvalue⟩ :=
    not_common_normal_off_pair_of_stressFree atomFamily hstressFree normal hnormal exempt exempt
  exact ⟨label, hfirst, hvalue⟩

/-! ## Part 5: the design-level reading at four coplanar atoms -/

/-- The two labels a distinct quadruple of `Fin 6` leaves free. -/
theorem exists_pair_off_quadruple (a b c d : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ first second : Fin 6, ∀ label, label ≠ first → label ≠ second →
      label = a ∨ label = b ∨ label = c ∨ label = d := by
  classical
  set quad : Finset (Fin 6) := {a, b, c, d} with hquad
  have hcard : quad.card = 4 := by
    rw [hquad]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hcompl : (quadᶜ).card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨first, second, _, hpair⟩ := Finset.card_eq_two.mp hcompl
  refine ⟨first, second, fun label hfirst hsecond => ?_⟩
  have hmem : label ∈ quad := by
    by_contra hnot
    have : label ∈ quadᶜ := Finset.mem_compl.mpr hnot
    rw [hpair] at this
    rcases Finset.mem_insert.mp this with h | h
    · exact hfirst h
    · exact hsecond (Finset.mem_singleton.mp h)
  rw [hquad] at hmem
  rcases Finset.mem_insert.mp hmem with h | hmem
  · exact Or.inl h
  rcases Finset.mem_insert.mp hmem with h | hmem
  · exact Or.inr (Or.inl h)
  rcases Finset.mem_insert.mp hmem with h | hmem
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp hmem)))

/-- **BRANCH (i) HAS NO FOUR COPLANAR ATOMS.**  Four distinct atoms of a
stress-free family never read zero together against one nonzero normal. -/
theorem not_coplanar_quadruple_of_stressFree_atoms (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (atomFamily atomIndex)) = 0 →
        stressCoeff = 0)
    (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0)
    (a b c d : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ (atomFamily a ⬝ᵥ normal = 0 ∧ atomFamily b ⬝ᵥ normal = 0
        ∧ atomFamily c ⬝ᵥ normal = 0 ∧ atomFamily d ⬝ᵥ normal = 0) := by
  rintro ⟨hfa, hfb, hfc, hfd⟩
  obtain ⟨first, second, hcover⟩ := exists_pair_off_quadruple a b c d hab hac had hbc hbd hcd
  obtain ⟨label, hlabelFirst, hlabelSecond, hvalue⟩ :=
    not_common_normal_off_pair_of_stressFree atomFamily hstressFree normal hnormal first second
  rcases hcover label hlabelFirst hlabelSecond with h | h | h | h
  · exact hvalue (by rw [h]; exact hfa)
  · exact hvalue (by rw [h]; exact hfb)
  · exact hvalue (by rw [h]; exact hfc)
  · exact hvalue (by rw [h]; exact hfd)

/-- The same statement about a design. -/
theorem not_coplanar_quadruple_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0)
    (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0)
    (a b c d : Fin 6) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ (design.atom a ⬝ᵥ normal = 0 ∧ design.atom b ⬝ᵥ normal = 0
        ∧ design.atom c ⬝ᵥ normal = 0 ∧ design.atom d ⬝ᵥ normal = 0) :=
  not_coplanar_quadruple_of_stressFree_atoms design.atom hstressFree normal hnormal
    a b c d hab hac had hbc hbd hcd

end Gtz

/-
# Split-tetrahedron ties: exact ties need not carry a stress certificate

The four regular-tetrahedron directions (`tetraAtom`, with `|v_d|² = 3`,
`v_d ⬝ᵥ v_e = ±1` off/on the diagonal, `∑_d v_d v_dᵀ = 4·I`) generate a two-parameter
family of weighted `(6,3)` designs: keep directions `0, 1` with weight `1/4` each and
DUPLICATE directions `2, 3`, splitting each `1/4` arbitrarily between the two copies.
Parseval is inherited from the tetrahedron because duplicated copies carry the same
rank-one moment.

Every member of the family is an exact tie (`splitTetraDesign_isTie`):

  * the subset `{0,1,2}` dominates weakly — its gap `S_C − I` is the positive
    semidefinite sum of squares `(x₀−x₁)² + (x₀+x₂)² + (x₁+x₂)²`;
  * every 3-subset misses at least one direction `d` (four directions, three atoms),
    and the missed direction is a null direction of its gap: each atom pairs to
    `(±1)² = 1` with `v_d`, so `v_dᵀ S_C v_d = 3 = |v_d|²` — no subset dominates
    strictly.

An asymmetric split separates the stress certificate from the tie itself: duplicated
atoms pair identically against every direction family, so a certificate
`∑_i coeff_i ⟨g_c, dir_i⟩² = t_c` forces equal duplicate weights
(`noStressCertificate_of_duplicate_atoms`). Hence exact ties admitting NO stress
certificate exist (`exists_isTie_and_noStressCertificate`) — sharpening
`Gtz.Ties.DominationWithoutCertificate`, which separates the certificate from domination
only off ties. The certificate is an invariant of the merged design — the regular
tetrahedron `tetraDesign`, whose multiplier is `Λ = I/12`
(`tetra_no_separating_slope`) — not of the raw atom list.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.RayleighCertificate
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.StressCertificate

namespace Gtz

open Matrix

/-! ### Duplication rules out a certificate -/

/-- **A design with duplicated atoms of unequal weights has no stress certificate.**
Duplicated atoms pair identically against every direction family, so any reproducing
family `∑_i coeff_i ⟨g_c, dir_i⟩² = t_c` forces the duplicate weights to agree — no
sign condition on the coefficients is even needed. -/
theorem noStressCertificate_of_duplicate_atoms {m k : ℕ} (D : WeightedDesign m k)
    {c c' : Fin m} (hatom : D.atom c = D.atom c') (hweight : D.weight c ≠ D.weight c')
    {index : Type*} (family : Finset index) (dir : index → Fin k → ℝ)
    (coeff : index → ℝ)
    (hcert : ∀ e : Fin m,
      ∑ i ∈ family, coeff i * (D.atom e ⬝ᵥ dir i) ^ 2 = D.weight e) : False :=
  hweight ((hcert c).symm.trans (by rw [hatom]; exact hcert c'))

/-! ### The split-tetrahedron family -/

/-- Which tetrahedron direction each of the six atoms carries: directions `2` and `3`
are duplicated. -/
def splitTetraDirIndex : Fin 6 → Fin 4 := ![0, 1, 2, 2, 3, 3]

/-- The six atoms: the four tetrahedron directions with the last two duplicated. -/
def splitTetraAtom : Fin 6 → Fin 3 → ℝ := fun c => tetraAtom (splitTetraDirIndex c)

variable (splitA splitB : ℝ)

/-- The split-tetrahedron design: directions `0, 1` carry weight `1/4`; the duplicated
directions `2, 3` split their `1/4` as `splitA + (1/4 − splitA)` and
`splitB + (1/4 − splitB)`. -/
noncomputable def splitTetraDesign (hAPos : 0 < splitA) (hALt : splitA < 1/4)
    (hBPos : 0 < splitB) (hBLt : splitB < 1/4) : WeightedDesign 6 3 where
  atom := splitTetraAtom
  weight := ![1/4, 1/4, splitA, 1/4 - splitA, splitB, 1/4 - splitB]
  weight_pos := by
    intro c
    fin_cases c
    · exact (by norm_num : (0 : ℝ) < 1/4)
    · exact (by norm_num : (0 : ℝ) < 1/4)
    · exact hAPos
    · exact (by linarith : (0 : ℝ) < 1/4 - splitA)
    · exact hBPos
    · exact (by linarith : (0 : ℝ) < 1/4 - splitB)
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    ring
  isParseval := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, smul_eq_mul, splitTetraAtom, splitTetraDirIndex,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> simp [tetraAtom] <;> ring

variable (hAPos : 0 < splitA) (hALt : splitA < 1/4) (hBPos : 0 < splitB)
  (hBLt : splitB < 1/4)

@[simp] theorem splitTetraDesign_atom :
    (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom = splitTetraAtom := rfl

@[simp] theorem splitTetraDesign_weight :
    (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).weight
      = ![1/4, 1/4, splitA, 1/4 - splitA, splitB, 1/4 - splitB] := rfl

/-! ### The tetrahedron pairing facts -/

/-- An atom pairs to `±1` — squared, to `1` — with every tetrahedron direction it does
not carry: the atom IS a tetrahedron direction, so this is `tetraAtom_dot_sq_of_ne`
read along `splitTetraDirIndex`. -/
theorem splitTetraAtom_dot_sq_of_ne {c : Fin 6} {d : Fin 4}
    (hne : splitTetraDirIndex c ≠ d) :
    (splitTetraAtom c ⬝ᵥ tetraAtom d) ^ 2 = 1 :=
  tetraAtom_dot_sq_of_ne hne

/-- Three atoms cover at most three of the four tetrahedron directions. -/
theorem exists_unusedDir (atomOne atomTwo atomThree : Fin 6) :
    ∃ d : Fin 4, splitTetraDirIndex atomOne ≠ d ∧ splitTetraDirIndex atomTwo ≠ d ∧
      splitTetraDirIndex atomThree ≠ d := by
  decide +revert

/-! ### Every member of the family is an exact tie -/

/-- The gap of any 3-subset vanishes at every direction the subset does not carry:
each of the three atoms pairs to `(±1)² = 1` with the unused `v_d`, so
`v_dᵀ S_C v_d = 3 = |v_d|²`. -/
theorem splitTetra_gapForm_zero_of_unusedDir {C : Finset (Fin 6)} (hcard : C.card = 3)
    {d : Fin 4} (hunused : ∀ c ∈ C, splitTetraDirIndex c ≠ d) :
    tetraAtom d ⬝ᵥ
      ((subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) C - 1) *ᵥ
        tetraAtom d) = 0 := by
  rw [dominationGap_form]
  have hone : ∀ c ∈ C,
      ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom c ⬝ᵥ tetraAtom d) ^ 2
        = 1 := fun c hc => splitTetraAtom_dot_sq_of_ne (hunused c hc)
  rw [Finset.sum_congr rfl hone, Finset.sum_const, hcard, tetraAtom_dot_self,
    nsmul_eq_mul]
  norm_num

/-- **The subset `{0,1,2}` dominates weakly** — its gap is the sum of squares
`(x₀−x₁)² + (x₀+x₂)² + (x₁+x₂)²`. -/
theorem splitTetraDesign_dominates :
    Dominates (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) {0, 1, 2} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun c _ =>
      posSemidef_atomMatrix
        ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom c)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, dominationGap_form,
      show ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [splitTetraDesign_atom, splitTetraAtom, splitTetraDirIndex, tetraAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 2), sq_nonneg (x 1 + x 2)]

/-- **No 3-subset dominates strictly**: it misses some direction, and the gap form
vanishes there. -/
theorem splitTetraDesign_no_strictDominator :
    ∀ C : Finset (Fin 6), C.card = 3 →
      ¬(subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) C - 1).PosDef := by
  intro C hcard hpd
  obtain ⟨atomOne, atomTwo, atomThree, hOneTwo, hOneThree, hTwoThree, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  obtain ⟨d, hdOne, hdTwo, hdThree⟩ := exists_unusedDir atomOne atomTwo atomThree
  have hunused : ∀ c ∈ ({atomOne, atomTwo, atomThree} : Finset (Fin 6)),
      splitTetraDirIndex c ≠ d := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hdOne
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hdTwo
    · exact (Finset.mem_singleton.mp hc) ▸ hdThree
  have hzero := splitTetra_gapForm_zero_of_unusedDir splitA splitB hAPos hALt hBPos hBLt
    hcard hunused
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 (tetraAtom_ne_zero d)
  rw [star_trivial, hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **Every member of the split-tetrahedron family is an exact tie.** -/
theorem splitTetraDesign_isTie :
    IsTie (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) :=
  ⟨⟨{0, 1, 2}, by decide,
      splitTetraDesign_dominates splitA splitB hAPos hALt hBPos hBLt⟩,
    splitTetraDesign_no_strictDominator splitA splitB hAPos hALt hBPos hBLt⟩

/-! ### An asymmetric split kills the stress certificate -/

/-- **At an asymmetric split of direction `2` there is no stress certificate**: atoms
`2` and `3` are equal while their weights `splitA ≠ 1/4 − splitA` differ. -/
theorem splitTetraDesign_noStressCertificate (hAsym : splitA ≠ 1/8)
    {index : Type*} (family : Finset index) (dir : index → Fin 3 → ℝ)
    (coeff : index → ℝ)
    (hcert : ∀ c : Fin 6,
      ∑ i ∈ family, coeff i *
        ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom c ⬝ᵥ dir i) ^ 2
      = (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).weight c) : False := by
  refine noStressCertificate_of_duplicate_atoms
    (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) (c := 2) (c' := 3) rfl ?_
    family dir coeff hcert
  simp only [splitTetraDesign_weight, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  intro heq
  exact hAsym (by linarith)

/-- **Exact ties without stress certificates exist.** The split-tetrahedron design at
the asymmetric split `(1/6, 1/8)` is a genuine `(6,3)` tie admitting no stress
certificate: certificate existence is not a consequence of `IsTie` — it is an
invariant of the merged design, not of the raw atom list. -/
theorem exists_isTie_and_noStressCertificate :
    ∃ D : WeightedDesign 6 3, IsTie D ∧
      ∀ {index : Type*} (family : Finset index) (dir : index → Fin 3 → ℝ)
        (coeff : index → ℝ), (∀ i ∈ family, 0 ≤ coeff i) →
        (∀ c : Fin 6,
          ∑ i ∈ family, coeff i * (D.atom c ⬝ᵥ dir i) ^ 2 = D.weight c) → False := by
  refine ⟨splitTetraDesign (1/6) (1/8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), splitTetraDesign_isTie _ _ _ _ _ _, ?_⟩
  intro index family dir coeff _ hcert
  exact splitTetraDesign_noStressCertificate _ _ _ _ _ _ (by norm_num)
    family dir coeff hcert

end Gtz

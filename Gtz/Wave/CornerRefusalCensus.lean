import Gtz.Wave.RefusalConeGeometry
import Gtz.Wave.NoStressResidualSwapBrackets

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The refusal census of a corank-two corner: ten of the twenty refusals are free

A `(6,3)` tie refuses all twenty triples.  At a CORANK-TWO CORNER — a weak
dominator `C` whose gap is `S_C − 1 = lam·u uᵀ` — ten of those twenty refusals
carry no information at all, because the corner alone already forbids the
triple.  This module names the ten and proves them without any tie hypothesis.

## The mechanism

The gap of a triple that shares two atoms with `C` is one swap away from the
corner gap.  Write `T = (C \ {e}) ∪ {d}` with `e ∈ C` and `d ∉ C`.  Then

  `(S_T − 1) + g_e g_eᵀ = lam·u uᵀ + g_d g_dᵀ`   (`Gtz.subsetSum_swap`)

and the right side is a sum of TWO rank-one matrices in three dimensions, so its
determinant vanishes (`Gtz.det_smul_atomMatrix_three` at a zero third
coefficient).  A singular matrix carries a kernel vector `z`, and at `z` the
swapped gap reads `−(g_e·z)² ≤ 0`, so `S_T − 1` is not positive definite
(`Gtz.corner_swap_not_posDef`).  The dominator itself refuses for the same
reason with `g_d` absent (`Gtz.corner_self_not_posDef`).

## The census

Every triple with at least two atoms in the dominator therefore fails to
dominate strictly (`Gtz.corner_census_not_posDef`): that is `C` itself and the
nine one-swap triples, ten of the twenty.  Contrapositively, a strict dominator
of a corank-two corner shares AT MOST ONE atom with the dominator
(`Gtz.strictDominator_inter_card_le_one`), so the only candidates left are the
complement `Cᶜ` and the nine triples with one inside atom and two outside ones.

The tie condition therefore collapses at a corner
(`Gtz.isTie_iff_corner_refusals`): it is equivalent to the ten refusals of the
triples that share at most one atom with `C`.  Any certificate for the corner
must consume those ten and can never gain anything from the other ten.

## Where the size enters

The swap identity is size-free, so the census also holds at `(5,3)`.  What is
NOT size-free is the COUNT: at `(6,3)` the complement of the dominator has three
atoms, so nine triples carry one inside atom and two outside ones, while at
`(5,3)` the complement is a pair and only three such triples exist.  The corner
of a `(6,3)` tie is therefore constrained by nine one-inside refusals where the
`(5,3)` diamond has three.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. A nonpositive reading refutes positive definiteness -/

/-- A direction where a symmetric form reads nonpositive refutes positive
definiteness.  The converse of `Gtz.exists_refusal_direction`. -/
theorem not_posDef_of_nonpos_reading {M : Matrix (Fin 3) (Fin 3) ℝ}
    {z : Fin 3 → ℝ} (hz : z ≠ 0) (hread : z ⬝ᵥ (M *ᵥ z) ≤ 0) : ¬ M.PosDef := by
  intro hpd
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hz
  rw [star_trivial] at hpos
  linarith

/-! ## 2. Two rank-one atoms never fill three dimensions -/

/-- **A scaled atom plus an atom is singular.**  The specialisation of
`Gtz.det_smul_atomMatrix_three` at a vanishing third coefficient. -/
theorem det_atomPair_eq_zero (lam : ℝ) (u g : Fin 3 → ℝ) :
    (lam • atomMatrix u + atomMatrix g).det = 0 := by
  have h := det_smul_atomMatrix_three u g u lam 1 0
  rw [zero_smul, add_zero, one_smul] at h
  rw [h]
  ring

/-- **A scaled atom is singular.**  The corner gap itself. -/
theorem det_atomSingle_eq_zero (lam : ℝ) (u : Fin 3 → ℝ) :
    (lam • atomMatrix u).det = 0 := by
  have h := det_atomPair_eq_zero lam u (0 : Fin 3 → ℝ)
  have hzero : atomMatrix (0 : Fin 3 → ℝ) = 0 := by
    ext i j
    simp [atomMatrix, Matrix.vecMulVec_apply]
  rwa [hzero, add_zero] at h

/-- A singular three-by-three matrix carries a nonzero kernel vector. -/
theorem exists_kernel_of_det_eq_zero {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hdet : M.det = 0) : ∃ z : Fin 3 → ℝ, z ≠ 0 ∧ M *ᵥ z = 0 := by
  obtain ⟨z, hz, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact ⟨z, hz, hker⟩

/-! ## 3. The swap identity -/

/-- **The one-swap gap identity.**  Trading the inside atom `e` for the outside
atom `d` moves the dominator's atom sum by exactly those two atoms. -/
theorem subsetSum_swap (D : WeightedDesign m 3) (C : Finset (Fin m)) {e d : Fin m}
    (he : e ∈ C) (hd : d ∉ C) :
    subsetSum D (insert d (C.erase e)) + atomMatrix (D.atom e)
      = subsetSum D C + atomMatrix (D.atom d) := by
  classical
  have hnotmem : d ∉ C.erase e := fun hc => hd (Finset.mem_of_mem_erase hc)
  have hrest : atomMatrix (D.atom e) + ∑ c ∈ C.erase e, atomMatrix (D.atom c)
      = subsetSum D C := by
    rw [subsetSum]
    exact Finset.add_sum_erase C (fun c => atomMatrix (D.atom c)) he
  rw [subsetSum, Finset.sum_insert hnotmem, ← hrest]
  abel

/-! ## 4. The ten free refusals -/

/-- **The dominator of a corank-two corner never dominates strictly.**  Its gap
is a single scaled atom, hence singular. -/
theorem corner_self_not_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ¬ (subsetSum D C - 1).PosDef := by
  intro hpd
  have hdet := hpd.det_pos
  rw [hgap, det_atomSingle_eq_zero] at hdet
  exact lt_irrefl 0 hdet

/-- **A one-swap triple never dominates strictly.**  Adding back the dropped
inside atom turns the swapped gap into a sum of two rank-one atoms, which is
singular, and the kernel direction of that sum reads the swapped gap
nonpositively. -/
theorem corner_swap_not_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e d : Fin m} (he : e ∈ C) (hd : d ∉ C) :
    ¬ (subsetSum D (insert d (C.erase e)) - 1).PosDef := by
  classical
  set T : Finset (Fin m) := insert d (C.erase e) with hT
  have hpair : (subsetSum D T - 1) + atomMatrix (D.atom e)
      = lam • atomMatrix u + atomMatrix (D.atom d) := by
    have hswap := subsetSum_swap D C he hd
    rw [hT]
    have : subsetSum D C = 1 + lam • atomMatrix u := by rw [← hgap]; abel
    rw [show subsetSum D (insert d (C.erase e)) - 1 + atomMatrix (D.atom e)
        = subsetSum D (insert d (C.erase e)) + atomMatrix (D.atom e) - 1 from by abel,
      hswap, this]
    abel
  obtain ⟨z, hz, hker⟩ :=
    exists_kernel_of_det_eq_zero (det_atomPair_eq_zero lam u (D.atom d))
  refine not_posDef_of_nonpos_reading hz ?_
  have hread : z ⬝ᵥ (((subsetSum D T - 1) + atomMatrix (D.atom e)) *ᵥ z) = 0 := by
    rw [hpair, hker, dotProduct_zero]
  rw [Matrix.add_mulVec, dotProduct_add,
    show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e) from rfl,
    quadForm_atomMatrix] at hread
  nlinarith [sq_nonneg (D.atom e ⬝ᵥ z)]

/-! ## 5. The census -/

/-- A triple sharing two atoms with another triple is one swap away from it. -/
theorem eq_swap_of_card_inter_two {T C : Finset (Fin m)} (hT : T.card = 3)
    (hC : C.card = 3) (hint : (T ∩ C).card = 2) :
    ∃ e ∈ C, ∃ d ∉ C, T = insert d (C.erase e) := by
  classical
  have hTd : (T \ C).card = 1 := by
    have h := Finset.card_inter_add_card_sdiff T C
    omega
  have hCd : (C \ T).card = 1 := by
    have h := Finset.card_inter_add_card_sdiff C T
    rw [Finset.inter_comm] at h
    omega
  obtain ⟨d, hdset⟩ := Finset.card_eq_one.mp hTd
  obtain ⟨e, heset⟩ := Finset.card_eq_one.mp hCd
  have hdmem : d ∈ T \ C := by rw [hdset]; exact Finset.mem_singleton_self d
  have hemem : e ∈ C \ T := by rw [heset]; exact Finset.mem_singleton_self e
  have hdT : d ∈ T := (Finset.mem_sdiff.mp hdmem).1
  have hdC : d ∉ C := (Finset.mem_sdiff.mp hdmem).2
  have heC : e ∈ C := (Finset.mem_sdiff.mp hemem).1
  have heT : e ∉ T := (Finset.mem_sdiff.mp hemem).2
  refine ⟨e, heC, d, hdC, ?_⟩
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · exact Or.inr ⟨fun hxe => heT (hxe ▸ hx), hxC⟩
    · have hmem : x ∈ T \ C := Finset.mem_sdiff.mpr ⟨hx, hxC⟩
      rw [hdset] at hmem
      exact Or.inl (Finset.mem_singleton.mp hmem)
  · rintro (rfl | ⟨hxe, hxC⟩)
    · exact hdT
    · by_contra hxT
      have hmem : x ∈ C \ T := Finset.mem_sdiff.mpr ⟨hxC, hxT⟩
      rw [heset] at hmem
      exact hxe (Finset.mem_singleton.mp hmem)

/-- **The census.**  At a corank-two corner every triple that shares at least two
atoms with the dominator fails to dominate strictly, with no tie hypothesis.
That is the dominator itself and its nine one-swap neighbours: ten of the twenty
triples of a `(6,3)` design. -/
theorem corner_census_not_posDef (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hC : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (T : Finset (Fin m)) (hT : T.card = 3) (hshare : 2 ≤ (T ∩ C).card) :
    ¬ (subsetSum D T - 1).PosDef := by
  classical
  have hle : (T ∩ C).card ≤ 3 := by
    calc (T ∩ C).card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hT
  interval_cases h : (T ∩ C).card
  · -- two shared atoms: one swap away
    obtain ⟨e, heC, d, hdC, hTeq⟩ := eq_swap_of_card_inter_two hT hC h
    rw [hTeq]
    exact corner_swap_not_posDef D C hgap heC hdC
  · -- three shared atoms: the triple IS the dominator
    have hsub : T ∩ C ⊆ T := Finset.inter_subset_left
    have hTeq : T ∩ C = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hsubC : T ∩ C ⊆ C := Finset.inter_subset_right
    have hCeq : T ∩ C = C := Finset.eq_of_subset_of_card_le hsubC (by omega)
    rw [← hTeq, hCeq]
    exact corner_self_not_posDef D C hgap

/-- **A strict dominator of a corner is nearly disjoint from it.**  It shares at
most one atom with the corank-two dominator. -/
theorem strictDominator_inter_card_le_one (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hC : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (T : Finset (Fin m)) (hT : T.card = 3) (hstrict : (subsetSum D T - 1).PosDef) :
    (T ∩ C).card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  exact corner_census_not_posDef D C hC hgap T hT hcon hstrict

/-! ## 6. The tie collapses at a corner -/

/-- **The tie condition at a corank-two corner is ten refusals, not twenty.**  A
design with a corank-two corner ties exactly when the triples sharing at most one
atom with the dominator all fail to dominate strictly. -/
theorem isTie_iff_corner_refusals (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hC : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    IsTie D ↔ ∀ T : Finset (Fin m), T.card = 3 → (T ∩ C).card ≤ 1 →
      ¬ (subsetSum D T - 1).PosDef := by
  constructor
  · intro htie T hT _
    exact htie.2 T hT
  · intro hten
    refine ⟨⟨C, hC, ?_⟩, fun T hT => ?_⟩
    · rw [Dominates, hgap]
      exact (posSemidef_atomMatrix u).smul hlam
    · by_cases hshare : 2 ≤ (T ∩ C).card
      · exact corner_census_not_posDef D C hC hgap T hT hshare
      · exact hten T hT (by omega)


/-! ## 7. The pivot shadow: the outside minor gives way with no proviso -/

/-- The three outside atoms of a corank-two corner, named. -/
theorem exists_third_outside (C : Finset (Fin 6)) (hcompl : (Cᶜ : Finset (Fin 6)).card = 3)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    ∃ dThird : Fin 6, dThird ≠ d ∧ dThird ≠ d'
      ∧ (Cᶜ : Finset (Fin 6)) = insert d (insert d' {dThird}) := by
  classical
  have hd'erase : d' ∈ (Cᶜ : Finset (Fin 6)).erase d :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, hd'⟩
  have hcard1 : ((Cᶜ : Finset (Fin 6)).erase d).card = 2 := by
    rw [Finset.card_erase_of_mem hd, hcompl]
  have hcard2 : (((Cᶜ : Finset (Fin 6)).erase d).erase d').card = 1 := by
    rw [Finset.card_erase_of_mem hd'erase, hcard1]
  obtain ⟨dThird, hset⟩ := Finset.card_eq_one.mp hcard2
  have hmem : dThird ∈ ((Cᶜ : Finset (Fin 6)).erase d).erase d' := by
    rw [hset]; exact Finset.mem_singleton_self dThird
  refine ⟨dThird, ?_, Finset.ne_of_mem_erase hmem, ?_⟩
  · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)
  · rw [← hset, Finset.insert_erase hd'erase, Finset.insert_erase hd]

/-- **The outside pair minor of a corank-two corner gives way, with no proviso.**
Removing two outside atoms from the six-set gap leaves the corner atom plus one
outside atom, which is singular, so the depth-two criterion fails and the first
disjunct is closed by `Gtz.outside_pivot_le_one`.  This strengthens
`Gtz.outsidePivot_minor_vanishes'`, whose conclusion is void when the cross-mass
`E` vanishes — that is exactly the degenerate corner where the corner pivot
reaches one. -/
theorem outside_pivot_minor_nonpos (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    (1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d')
      ≤ sixSetPivot D d d' ^ 2 := by
  classical
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]; simp
  obtain ⟨dThird, hne1, hne2, hset⟩ := exists_third_outside C hcompl hd hd' hne
  have houtside : subsetSum D Cᶜ
      = atomMatrix (D.atom d) + (atomMatrix (D.atom d') + atomMatrix (D.atom dThird)) := by
    rw [subsetSum, hset, Finset.sum_insert (by simp [hne, Ne.symm hne1]),
      Finset.sum_insert (by simp [Ne.symm hne2]), Finset.sum_singleton]
  have hshape : (subsetSum D Finset.univ - 1)
        - Matrix.vecMulVec (D.atom d) (D.atom d)
        - Matrix.vecMulVec (D.atom d') (D.atom d')
      = lam • atomMatrix u + atomMatrix (D.atom dThird) := by
    rw [sixSetGap_eq_gapAtom_add_outside D C hgap, houtside,
      show atomMatrix (D.atom d) = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl,
      show atomMatrix (D.atom d') = Matrix.vecMulVec (D.atom d') (D.atom d') from rfl]
    abel
  have hnotpd : ¬ ((subsetSum D Finset.univ - 1)
      - Matrix.vecMulVec (D.atom d) (D.atom d)
      - Matrix.vecMulVec (D.atom d') (D.atom d')).PosDef := by
    rw [hshape]
    intro hpd
    have hdet := hpd.det_pos
    rw [det_atomPair_eq_zero] at hdet
    exact lt_irrefl 0 hdet
  have hsyl := (not_posDef_sub_two_vecMulVec_iff (subsetSum D Finset.univ - 1) hPD
    (D.atom d) (D.atom d')).mp hnotpd
  simp only [show ∀ p q : Fin 6,
    D.atom p ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom q) = sixSetPivot D p q from
      fun _ _ => rfl] at hsyl
  rcases hsyl with hone | hminor
  · have hcap : sixSetPivot D d d ≤ 1 := outside_pivot_le_one D C hlam hgap hPD hd
    have hzero : 1 - sixSetPivot D d d = 0 := by linarith
    rw [hzero, zero_mul]
    exact sq_nonneg _
  · exact hminor

end Gtz

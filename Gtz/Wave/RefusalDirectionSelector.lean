import Gtz.Wave.CornerPivotRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The refusal direction names the selector

At a `(6,3)` tie the complement triple `Cᶜ` is refused, so the complement gap
`S_{Cᶜ} − 1` is not positive definite and there is a REFUSAL DIRECTION: a
nonzero `z` with `zᵀ(S_{Cᶜ} − 1)z ≤ 0` (`Gtz.exists_refusal_direction`).  The
swap at the inside atom `e` against the ghost `f` is

  `S_{Cᶜ} − 1 + g_e g_eᵀ − g_f g_fᵀ`

(`Gtz.swap_eq_complementGap`), so reading it at a refusal direction gives one
line:

  **swap at `(e,f)` positive definite  ⟹  `(g_f·z)² < (g_e·z)²`**

(`Gtz.reading_lt_of_swapPD_of_refusal`).  A short ghost block at the selector
`e` therefore makes `e` the STRICT MAXIMISER of `|g_c·z|` over the inside triple
(`Gtz.ghostBlockShort_argmax_of_refusal`).  Two selectors cannot both be the
strict maximiser, which re-proves
`Gtz.not_ghostBlockShort_two_selectors` in three lines and, more usefully, tells
a producer WHICH inside atom to take: the one whose reading of the refusal
direction is largest.

The refusal direction is not a function of the blind coordinates — it is the
kernel data of the complement gap — so a selector rule built on it escapes the
blindness of the determinantal and leverage functionals.

## Corner corollaries

`Gtz.outsideDefect_eq_zero` prices the outside block of a corank-two corner as a
rank-one deflation.  Dividing by the cross mass turns the minor law into the
scalar rigidity `P_{dd'}² = (1 − P_dd)(1 − P_{d'd'})`
(`Gtz.outsidePivot_offDiag_sq`), and the sign of the off-diagonal is the sign of
`−η_dη_{d'}`, so the product of the three outside off-diagonal pivots is never
positive (`Gtz.outsidePivot_triple_product_nonpos`).
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Refusal directions -/

/-- **A refused triple has a refusal direction.**  A gap that is not positive
definite is nonpositive somewhere. -/
theorem exists_refusal_direction (D : WeightedDesign m 3) (T : Finset (Fin m))
    (hrefuse : ¬ (subsetSum D T - 1).PosDef) :
    ∃ z : Fin 3 → ℝ, z ≠ 0 ∧ z ⬝ᵥ ((subsetSum D T - 1) *ᵥ z) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  refine hrefuse (Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D T), fun z hz => ?_⟩)
  rw [star_trivial]
  exact hcon z hz

/-- The quadratic form of an atom matrix is the squared reading. -/
theorem quadForm_atomMatrix (a z : Fin 3 → ℝ) :
    z ⬝ᵥ (Matrix.vecMulVec a a *ᵥ z) = (a ⬝ᵥ z) ^ 2 := by
  rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm z a]
  ring

/-! ## 2. The swap read at a refusal direction -/

/-- **The swap in complement form.**  The swap at the inside atom `e` against the
ghost `f` adds the selector's atom to the complement gap and removes the
ghost's. -/
theorem swap_eq_complementGap (D : WeightedDesign m 3) (C : Finset (Fin m))
    {e f : Fin m} (he : e ∈ C) :
    (subsetSum D (insert e Cᶜ) - 1) - Matrix.vecMulVec (D.atom f) (D.atom f)
      = (subsetSum D Cᶜ - 1) + Matrix.vecMulVec (D.atom e) (D.atom e)
        - Matrix.vecMulVec (D.atom f) (D.atom f) := by
  classical
  have hnot : e ∉ Cᶜ := by simpa using he
  rw [subsetSum, Finset.sum_insert hnot, ← subsetSum,
    show atomMatrix (D.atom e) = Matrix.vecMulVec (D.atom e) (D.atom e) from rfl]
  abel

/-- **The refusal direction separates the selector from its ghost.**  If the swap
at `(e,f)` is positive definite then the selector reads every refusal direction
strictly harder than the ghost does. -/
theorem reading_lt_of_swapPD_of_refusal (D : WeightedDesign m 3) (C : Finset (Fin m))
    {e f : Fin m} (he : e ∈ C)
    (hswap : ((subsetSum D (insert e Cᶜ) - 1)
      - Matrix.vecMulVec (D.atom f) (D.atom f)).PosDef)
    {z : Fin 3 → ℝ} (hz : z ≠ 0)
    (hrefuse : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0) :
    (D.atom f ⬝ᵥ z) ^ 2 < (D.atom e ⬝ᵥ z) ^ 2 := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hswap).2 hz
  rw [star_trivial, swap_eq_complementGap D C he] at hpos
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    quadForm_atomMatrix, quadForm_atomMatrix] at hpos
  linarith

/-! ## 3. The selector is the strict maximiser -/

/-- **A short ghost block makes its selector the strict maximiser.**  At every
refusal direction of the complement triple, the selector's reading strictly
exceeds each ghost's. -/
theorem ghostBlockShort_argmax_of_refusal (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) {e f h : Fin 6} (he : e ∈ C) (hfh : f ≠ h)
    (herase : C.erase e = {f, h}) (hshort : GhostBlockShort D f h)
    {z : Fin 3 → ℝ} (hz : z ≠ 0)
    (hrefuse : z ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ z) ≤ 0) :
    (D.atom f ⬝ᵥ z) ^ 2 < (D.atom e ⬝ᵥ z) ^ 2
      ∧ (D.atom h ⬝ᵥ z) ^ 2 < (D.atom e ⬝ᵥ z) ^ 2 := by
  have hPD : (subsetSum D Finset.univ - 1).PosDef := sixSetGap_posDef_sixThree D
  have herase' : C.erase e = {h, f} := by rw [herase, Finset.pair_comm]
  have hswapf := (swapPD_iff_ghostBlock D C he hfh herase hPD).mpr
    ⟨hshort.1, hshort.2.2.1⟩
  have hswaph := (swapPD_iff_ghostBlock D C he (Ne.symm hfh) herase' hPD).mpr
    ⟨hshort.2.1, by rw [sixSetPivot_comm D h f]; exact hshort.2.2.2⟩
  exact ⟨reading_lt_of_swapPD_of_refusal D C he hswapf hz hrefuse,
    reading_lt_of_swapPD_of_refusal D C he hswaph hz hrefuse⟩

/-- **At a tie two selectors cannot both be short, read off one direction.**  The
refusal direction of the complement triple makes each short selector the strict
maximiser, and there is only one. -/
theorem not_ghostBlockShort_two_selectors_of_refusal (D : WeightedDesign 6 3)
    (htie : IsTie D) (C : Finset (Fin 6)) (hcard : C.card = 3) {e f h : Fin 6}
    (he : e ∈ C) (hf : f ∈ C) (hfh : f ≠ h) (heh : e ≠ h)
    (heraseE : C.erase e = {f, h}) (heraseF : C.erase f = {e, h})
    (hshortE : GhostBlockShort D f h) (hshortF : GhostBlockShort D e h) : False := by
  classical
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard]
    simp
  obtain ⟨z, hz, hrefuse⟩ := exists_refusal_direction D Cᶜ (htie.2 Cᶜ hcompl)
  have h1 := (ghostBlockShort_argmax_of_refusal D C he hfh heraseE hshortE hz hrefuse).1
  have h2 := (ghostBlockShort_argmax_of_refusal D C hf heh heraseF hshortF hz hrefuse).1
  linarith

/-! ## 4. The scalar rigidity of the outside block -/

/-- **The scalar rigidity.**  When the cross mass is positive, the outside
off-diagonal pivot is the geometric mean of the two co-pivots. -/
theorem outsidePivot_offDiag_sq (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hmass : 0 < gapCrossMass D C u)
    {d d' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hne : d ≠ d') :
    sixSetPivot D d d' ^ 2
      = (1 - sixSetPivot D d d) * (1 - sixSetPivot D d' d') := by
  have h := outsidePivot_minor_vanishes D C hcard hgap (sixSetGap_posDef_sixThree D)
    hd hd' hne
  have hsq : 0 < gapCrossMass D C u ^ 2 := by positivity
  have := mul_eq_zero.mp h
  rcases this with hz | hz
  · exact absurd hz (ne_of_gt hsq)
  · linarith

/-- **The sign law of the outside block.**  The product of the three outside
off-diagonal pivots is never positive: each is `−π_u η_dη_{d'}` times the inverse
cross mass, so the product carries a square. -/
theorem outsidePivot_triple_product_nonpos (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hself : 0 ≤ gapSelf D u)
    {d d' d'' : Fin 6} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) (hd'' : d'' ∈ Cᶜ)
    (h1 : d ≠ d') (h2 : d' ≠ d'') (h3 : d ≠ d'') :
    gapCrossMass D C u ^ 3
        * (sixSetPivot D d d' * sixSetPivot D d' d'' * sixSetPivot D d d'') ≤ 0 := by
  have e1 := outsidePivot_offDiag_rankOne D C hcard hgap (sixSetGap_posDef_sixThree D)
    hd hd' h1
  have e2 := outsidePivot_offDiag_rankOne D C hcard hgap (sixSetGap_posDef_sixThree D)
    hd' hd'' h2
  have e3 := outsidePivot_offDiag_rankOne D C hcard hgap (sixSetGap_posDef_sixThree D)
    hd hd'' h3
  have hprod : gapCrossMass D C u ^ 3
      * (sixSetPivot D d d' * sixSetPivot D d' d'' * sixSetPivot D d d'')
      = -(cornerPivot D lam u ^ 3
        * (gapCross D u d * gapCross D u d' * gapCross D u d'') ^ 2) := by
    have hx : gapCrossMass D C u ^ 3
        * (sixSetPivot D d d' * sixSetPivot D d' d'' * sixSetPivot D d d'')
        = (gapCrossMass D C u * sixSetPivot D d d')
          * (gapCrossMass D C u * sixSetPivot D d' d'')
          * (gapCrossMass D C u * sixSetPivot D d d'') := by ring
    rw [hx, e1, e2, e3]
    ring
  rw [hprod]
  have hpi : 0 ≤ cornerPivot D lam u := mul_nonneg hlam hself
  have : 0 ≤ cornerPivot D lam u ^ 3
      * (gapCross D u d * gapCross D u d' * gapCross D u d'') ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

end Gtz

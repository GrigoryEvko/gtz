/-
# Domination is a bound on the DEPENDENCIES of the atoms

The campaign reads domination in two charts.  `Gtz.dominates_iff_posSemidef_projectionBlock`
compares a principal block of `P = V Vᵀ` with `diag t`, and
`Gtz.dominates_iff_resolventForm_le` compares a block of the resolvent readings with the
identity.  Both look at the SELECTED labels through a `k x k` or `|C| x |C|` block.

This module reads domination on the other side of the design: on the linear DEPENDENCIES
of the atoms, where no block and no matrix inverse appear at all.

  **`Gtz.dominates_iff_dependencyBound`.**  For a `k`-subset `C` of a weighted design,

      Dominates D C   <->   for every `z` with `sum_c z_c * g_c = 0` ,
                            `sum_{c in C} z_c^2 / (t_c * (1 - t_c))  <=  sum_c z_c^2 / t_c` .

Equivalently, after moving the selected part of the right sum to the left,

      `sum_{c in C} z_c^2 / (1 - t_c)  <=  sum_{c not in C} z_c^2 / t_c`  ,

which is `Gtz.dominates_iff_dependencyBound_compl`.  Nothing but the weights and the
dependency coefficients occurs: the atoms enter only through WHICH vectors `z` are
dependencies.

## What it specializes to

At corank one the dependency space is a line, and the tree already knows its normalisation
`dep_c ^ 2 = t_c * u_c` (`Gtz.exists_dependency`, with `u_c = 1 - t_c * l_c` the co-share).
Feeding that single `z` into the criterion at `C = univ.erase d` turns the two sides into
`u_d` and `sum_{c != d} t_c * u_c / (1 - t_c)`, so the criterion reads

    `Sigma <= R_d`  ,   `R_c = u_c / (1 - t_c)` ,  `Sigma = sum_c t_c * R_c` ,

which is exactly the landed pair `Gtz.dominates_erase_of_coMean_le` and its converse.  So
the corank-one engine of `Gtz.Wave.CorankOneRigidity` is the one-dimensional case of this
criterion, and the criterion is what that engine looks like at every corank.

## The mechanism

Two facts, one general and one about designs.

* `Gtz.posSemidef_diagonal_sub_block_iff_kernelBound` is pure linear algebra about a
  SYMMETRIC IDEMPOTENT `Q`.  For any index map `pick` and any positive `scale`,

      `diag scale - Q[pick, pick] >= 0`
        <->  every `x` fixed by `Q` obeys `sum_slot x_(pick slot)^2 / scale slot <= sum_c x_c^2` .

  Both directions are the same three lines: name the quantity that appears on both sides
  of a Cauchy-Schwarz step, bound its square by the other side times itself, and divide.
  No eigenvalue, no rank, no inverse, and no square root of a matrix.

* For a design the relevant idempotent is `1 - P`, whose fixed vectors are exactly the
  kernel of `Vᵀ` (`Gtz.mulVec_coProjection_self_iff`), and `Vᵀ x = 0` says
  `sum_c x_c * sqrt(t_c) * g_c = 0`.  Substituting `z_c = sqrt(t_c) * x_c` turns that into
  a plain dependency and turns `1 / (1 - t_c)` into `1 / (t_c * (1 - t_c))`.

[MEASURED before proving, in double precision: over the cells `(4,3)`, `(5,3)`, `(6,3)`,
`(7,3)`, `(8,4)`, `(6,4)`, `(5,2)` and `(7,5)` the criterion agreed with domination on all
46250 subsets tested, and its strict form agreed with strict domination on all 34750
subsets tested, with no mismatch of either kind.]
-/
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.SchurRankOne
import Gtz.Wave.ResolventBlockCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. Spreading a selected vector out to the ambient index set -/

/-- Extend a vector indexed by the selection to the ambient index set by zero. -/
def dependencySpread {ambient size : ℕ} (pick : Fin size → Fin ambient)
    (selected : Fin size → ℝ) : Fin ambient → ℝ :=
  fun index => ∑ slot, if index = pick slot then selected slot else 0

/-- **THE TRANSFER LAW.**  Pairing a spread vector against anything reads the selection
only.  No injectivity is needed. -/
theorem dependencySpread_transfer {ambient size : ℕ} (pick : Fin size → Fin ambient)
    (selected : Fin size → ℝ) (probe : Fin ambient → ℝ) :
    ∑ index, dependencySpread pick selected index * probe index
      = ∑ slot, selected slot * probe (pick slot) := by
  simp only [dependencySpread, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun slot _ => ?_
  have hpoint : ∀ index : Fin ambient,
      (if index = pick slot then selected slot else 0) * probe index
        = if index = pick slot then selected slot * probe (pick slot) else 0 := by
    intro index
    by_cases hindex : index = pick slot
    · rw [if_pos hindex, if_pos hindex, hindex]
    · rw [if_neg hindex, if_neg hindex, zero_mul]
  rw [Finset.sum_congr rfl fun index _ => hpoint index]
  simp

/-- The quadratic form of a spread vector is the quadratic form of the principal block. -/
theorem dependencySpread_quadForm {ambient size : ℕ} (pick : Fin size → Fin ambient)
    (form : Matrix (Fin ambient) (Fin ambient) ℝ) (selected : Fin size → ℝ) :
    (dependencySpread pick selected) ⬝ᵥ (form *ᵥ (dependencySpread pick selected))
      = selected ⬝ᵥ ((form.submatrix pick pick) *ᵥ selected) := by
  set spread := dependencySpread pick selected with hspread
  have houter : spread ⬝ᵥ (form *ᵥ spread)
      = ∑ slot, selected slot * ((form *ᵥ spread) (pick slot)) := by
    rw [dotProduct]
    exact dependencySpread_transfer pick selected (form *ᵥ spread)
  have hinner : ∀ slot : Fin size,
      (form *ᵥ spread) (pick slot) = ∑ other, selected other * form (pick slot) (pick other) := by
    intro slot
    have hrow : (form *ᵥ spread) (pick slot)
        = ∑ index, spread index * form (pick slot) index := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun index _ => mul_comm _ _
    rw [hrow]
    exact dependencySpread_transfer pick selected (fun index => form (pick slot) index)
  rw [houter, dotProduct]
  refine Finset.sum_congr rfl fun slot _ => ?_
  rw [hinner slot]
  congr 1
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun other _ => by
    rw [Matrix.submatrix_apply]; exact mul_comm _ _

/-! ## 2. The criterion at a symmetric idempotent -/

/-- **THE BLOCK-VERSUS-KERNEL CRITERION.**  For a symmetric idempotent `Q`, a positive
`scale` and any index map, the block inequality `diag scale >= Q[pick, pick]` says exactly
that every vector FIXED by `Q` spends at most its own total square mass on the selected
coordinates, measured against `scale`.

Both directions are one Cauchy-Schwarz: the pairing of the fixed vector with the spread of
the selection appears on both sides, so its square is bounded by the other side times
itself, and dividing finishes. -/
theorem posSemidef_diagonal_sub_block_iff_kernelBound {ambient size : ℕ}
    {form : Matrix (Fin ambient) (Fin ambient) ℝ}
    (hsymm : formᵀ = form) (hidem : form * form = form)
    (pick : Fin size → Fin ambient) {scale : Fin size → ℝ}
    (hscale : ∀ slot, 0 < scale slot) :
    (Matrix.diagonal scale - form.submatrix pick pick).PosSemidef
      ↔ ∀ probe : Fin ambient → ℝ, form *ᵥ probe = probe →
          ∑ slot, probe (pick slot) ^ 2 / scale slot ≤ ∑ index, probe index ^ 2 := by
  have hblockSymm : (Matrix.diagonal scale - form.submatrix pick pick)ᵀ
      = Matrix.diagonal scale - form.submatrix pick pick := by
    rw [Matrix.transpose_sub, Matrix.diagonal_transpose, Matrix.transpose_submatrix, hsymm]
  have hdiagForm : ∀ selected : Fin size → ℝ,
      selected ⬝ᵥ (Matrix.diagonal scale *ᵥ selected) = ∑ slot, scale slot * selected slot ^ 2 := by
    intro selected
    rw [dotProduct]
    exact Finset.sum_congr rfl fun slot _ => by rw [Matrix.mulVec_diagonal]; ring
  rw [posSemidef_iff_quadForm_nonneg _ hblockSymm]
  constructor
  · -- the block inequality gives the kernel bound
    intro hblock probe hfix
    set selected : Fin size → ℝ := fun slot => probe (pick slot) / scale slot with hselected
    set total : ℝ := ∑ slot, probe (pick slot) ^ 2 / scale slot with htotal
    have htotalNonneg : 0 ≤ total :=
      Finset.sum_nonneg fun slot _ => div_nonneg (sq_nonneg _) (hscale slot).le
    have hdiagValue : selected ⬝ᵥ (Matrix.diagonal scale *ᵥ selected) = total := by
      rw [hdiagForm, htotal]
      refine Finset.sum_congr rfl fun slot _ => ?_
      simp only [hselected]
      field_simp
      try ring
    have hblockValue : selected ⬝ᵥ ((form.submatrix pick pick) *ᵥ selected) ≤ total := by
      have hstep := hblock selected
      rw [Matrix.sub_mulVec, dotProduct_sub, hdiagValue] at hstep
      linarith
    set spread := dependencySpread pick selected with hspread
    have hspreadQuad : spread ⬝ᵥ (form *ᵥ spread) ≤ total := by
      rw [hspread, dependencySpread_quadForm]; exact hblockValue
    have hpair : ∑ index, (form *ᵥ spread) index * probe index = total := by
      have hcomm : probe ⬝ᵥ (form *ᵥ spread) = spread ⬝ᵥ (form *ᵥ probe) :=
        dot_mulVec_comm hsymm probe spread
      have hleft : ∑ index, (form *ᵥ spread) index * probe index
          = probe ⬝ᵥ (form *ᵥ spread) := by
        rw [dotProduct]
        exact Finset.sum_congr rfl fun index _ => mul_comm _ _
      rw [hleft, hcomm, hfix, dotProduct, hspread,
        dependencySpread_transfer pick selected probe, htotal]
      refine Finset.sum_congr rfl fun slot _ => ?_
      simp only [hselected]
      field_simp
      try ring
    have hnormSq : ∑ index, ((form *ᵥ spread) index) ^ 2 = spread ⬝ᵥ (form *ᵥ spread) := by
      have hsquare : (form *ᵥ spread) ⬝ᵥ (form *ᵥ spread) = spread ⬝ᵥ (form *ᵥ spread) := by
        have hcomm : (form *ᵥ spread) ⬝ᵥ (form *ᵥ spread)
            = spread ⬝ᵥ (form *ᵥ (form *ᵥ spread)) :=
          dot_mulVec_comm hsymm (form *ᵥ spread) spread
        rw [hcomm, Matrix.mulVec_mulVec, hidem]
      rw [← hsquare, dotProduct]
      simp [pow_two]
    have hCS := sum_mul_sq_le Finset.univ (form *ᵥ spread) probe
    rw [hpair, hnormSq] at hCS
    rcases eq_or_lt_of_le htotalNonneg with hzero | hpos
    · rw [← hzero]
      exact Finset.sum_nonneg fun index _ => sq_nonneg _
    · nlinarith [hCS, hspreadQuad, hpos,
        Finset.sum_nonneg (fun index (_ : index ∈ Finset.univ) => sq_nonneg (probe index))]
  · -- the kernel bound gives the block inequality
    intro hkernel selected
    set spread := dependencySpread pick selected with hspread
    set image : Fin ambient → ℝ := form *ᵥ spread with himage
    have hfix : form *ᵥ image = image := by
      rw [himage, Matrix.mulVec_mulVec, hidem]
    set gap : ℝ := spread ⬝ᵥ (form *ᵥ spread) with hgap
    have hgapBlock : gap = selected ⬝ᵥ ((form.submatrix pick pick) *ᵥ selected) := by
      rw [hgap, hspread, dependencySpread_quadForm]
    have hnormSq : ∑ index, image index ^ 2 = gap := by
      have hsquare : image ⬝ᵥ image = gap := by
        have hcomm : image ⬝ᵥ image = spread ⬝ᵥ (form *ᵥ image) :=
          himage ▸ dot_mulVec_comm hsymm (form *ᵥ spread) spread
        rw [hcomm, himage, Matrix.mulVec_mulVec, hidem, hgap]
      rw [← hsquare, dotProduct]
      simp [pow_two]
    have hgapNonneg : 0 ≤ gap := by
      rw [← hnormSq]
      exact Finset.sum_nonneg fun index _ => sq_nonneg _
    have hpair : ∑ slot, selected slot * image (pick slot) = gap := by
      rw [hgap, dotProduct, hspread]
      exact (dependencySpread_transfer pick selected (form *ᵥ spread)).symm
    have hbound : ∑ slot, image (pick slot) ^ 2 / scale slot ≤ gap := by
      have := hkernel image hfix
      rw [hnormSq] at this
      exact this
    have hCS := sum_mul_sq_le Finset.univ
      (fun slot => Real.sqrt (scale slot) * selected slot)
      (fun slot => image (pick slot) / Real.sqrt (scale slot))
    have hmix : ∀ slot : Fin size,
        (Real.sqrt (scale slot) * selected slot) * (image (pick slot) / Real.sqrt (scale slot))
          = selected slot * image (pick slot) := by
      intro slot
      have hne : Real.sqrt (scale slot) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hscale slot))
      field_simp
      try ring
    have hleftSq : ∀ slot : Fin size,
        (Real.sqrt (scale slot) * selected slot) ^ 2 = scale slot * selected slot ^ 2 := by
      intro slot
      rw [mul_pow, Real.sq_sqrt (hscale slot).le]
    have hrightSq : ∀ slot : Fin size,
        (image (pick slot) / Real.sqrt (scale slot)) ^ 2 = image (pick slot) ^ 2 / scale slot := by
      intro slot
      rw [div_pow, Real.sq_sqrt (hscale slot).le]
    rw [Finset.sum_congr rfl fun slot _ => hmix slot,
      Finset.sum_congr rfl fun slot _ => hleftSq slot,
      Finset.sum_congr rfl fun slot _ => hrightSq slot, hpair] at hCS
    have hscaleSum : 0 ≤ ∑ slot, scale slot * selected slot ^ 2 :=
      Finset.sum_nonneg fun slot _ => mul_nonneg (hscale slot).le (sq_nonneg _)
    rw [Matrix.sub_mulVec, dotProduct_sub, hdiagForm, ← hgapBlock]
    rcases eq_or_lt_of_le hgapNonneg with hzero | hpos
    · rw [← hzero]; linarith
    · nlinarith [hCS, hbound, hpos, hscaleSum]

/-! ## 3. The criterion at a design -/

/-- The co-projection `1 - P` is symmetric. -/
theorem coProjectionForm_transpose (D : WeightedDesign m k) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D)ᵀ
      = 1 - projectionOfDesign D := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, projectionOfDesign_transpose]

/-- The co-projection `1 - P` is idempotent. -/
theorem coProjectionForm_mul_self (D : WeightedDesign m k) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D)
        * (1 - projectionOfDesign D)
      = 1 - projectionOfDesign D := by
  have hidem := projectionOfDesign_mul_self D
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hidem]
  abel

/-- **THE FIXED VECTORS OF THE CO-PROJECTION ARE THE DEPENDENCIES.**  A vector is fixed by
`1 - P` exactly when the scaled frame annihilates it, which says that the atoms, weighted
by the vector and by the square roots of the weights, cancel. -/
theorem mulVec_coProjection_self_iff (D : WeightedDesign m k) (probe : Fin m → ℝ) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D) *ᵥ probe = probe
      ↔ (scaledAtomRows D)ᵀ *ᵥ probe = 0 := by
  have hadjoint : ∀ w : Fin k → ℝ,
      probe ⬝ᵥ (scaledAtomRows D *ᵥ w) = ((scaledAtomRows D)ᵀ *ᵥ probe) ⬝ᵥ w := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hfixIff : ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D) *ᵥ probe = probe
      ↔ projectionOfDesign D *ᵥ probe = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    constructor
    · intro h; have := sub_eq_self.mp h; exact this
    · intro h; rw [h, sub_zero]
  rw [hfixIff]
  constructor
  · intro h
    have hquad : ((scaledAtomRows D)ᵀ *ᵥ probe) ⬝ᵥ ((scaledAtomRows D)ᵀ *ᵥ probe) = 0 := by
      rw [← hadjoint, Matrix.mulVec_mulVec, ← projectionOfDesign, h, dotProduct_zero]
    exact dotProduct_self_eq_zero.mp hquad
  · intro h
    rw [projectionOfDesign, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- The gap block of the primal chart is the co-projection block of the dual chart. -/
theorem projectionBlock_gap_eq_coProjection_gap (D : WeightedDesign m k)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    (projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun slot => D.weight (pick slot))
      = Matrix.diagonal (fun slot => 1 - D.weight (pick slot))
        - ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D).submatrix pick pick := by
  have hsub : ((1 : Matrix (Fin m) (Fin m) ℝ) - projectionOfDesign D).submatrix pick pick
      = 1 - (projectionOfDesign D).submatrix pick pick := by
    ext rowSlot colSlot
    rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.submatrix_apply]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hslot : rowSlot = colSlot
    · rw [if_pos hslot, if_pos (by rw [hslot])]
    · rw [if_neg hslot, if_neg fun hpick => hslot (hinj hpick)]
  have hdiagSplit : Matrix.diagonal (fun slot : Fin k => 1 - D.weight (pick slot))
      = 1 - Matrix.diagonal (fun slot : Fin k => D.weight (pick slot)) := by
    ext rowSlot colSlot
    by_cases hslot : rowSlot = colSlot
    · subst hslot
      rw [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq,
        Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hslot, Matrix.sub_apply, Matrix.one_apply_ne hslot,
        Matrix.diagonal_apply_ne _ hslot, sub_zero]
  rw [hdiagSplit, hsub]
  abel

/-- **DOMINATION IS A BOUND ON THE KERNEL OF THE SCALED FRAME.**  A `k`-subset dominates
exactly when every vector annihilated by the scaled frame spends, on the selected labels
and measured against the co-weights `1 - t_c`, at most its own total square mass. -/
theorem dominates_iff_kernelBound (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ ∀ probe : Fin m → ℝ, (scaledAtomRows D)ᵀ *ᵥ probe = 0 →
          ∑ slot, probe (pick slot) ^ 2 / (1 - D.weight (pick slot))
            ≤ ∑ index, probe index ^ 2 := by
  have hscale : ∀ slot : Fin k, 0 < 1 - D.weight (pick slot) := fun slot => by
    linarith [weight_lt_one D hm (pick slot)]
  rw [dominates_iff_posSemidef_projectionBlock D pick hinj,
    projectionBlock_gap_eq_coProjection_gap D pick hinj,
    posSemidef_diagonal_sub_block_iff_kernelBound (coProjectionForm_transpose D)
      (coProjectionForm_mul_self D) pick hscale]
  exact forall_congr' fun probe => by rw [mulVec_coProjection_self_iff]

/-- The kernel of the scaled frame is the set of linear dependencies, rescaled. -/
theorem transpose_scaledAtomRows_mulVec_eq_zero_iff (D : WeightedDesign m k)
    (probe : Fin m → ℝ) :
    (scaledAtomRows D)ᵀ *ᵥ probe = 0
      ↔ (∑ index, (Real.sqrt (D.weight index) * probe index) • D.atom index) = 0 := by
  have hpoint : ∀ coord : Fin k,
      ((scaledAtomRows D)ᵀ *ᵥ probe) coord
        = (∑ index, (Real.sqrt (D.weight index) * probe index) • D.atom index) coord := by
    intro coord
    rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [Matrix.transpose_apply, scaledAtomRows, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro hzero
    funext coord
    rw [← hpoint coord, hzero]
  · intro hzero
    funext coord
    rw [hpoint coord, hzero]

/-- **DOMINATION IS A BOUND ON THE DEPENDENCIES.**  A `k`-subset dominates exactly when
every linear dependency of the atoms obeys one weighted inequality, in which the atoms
themselves no longer appear. -/
theorem dominates_iff_dependencyBound (D : WeightedDesign m k) (hm : 2 ≤ m)
    (pick : Fin k → Fin m) (hinj : Function.Injective pick) :
    Dominates D (Finset.image pick Finset.univ)
      ↔ ∀ dep : Fin m → ℝ, (∑ index, dep index • D.atom index) = 0 →
          ∑ slot, dep (pick slot) ^ 2
              / (D.weight (pick slot) * (1 - D.weight (pick slot)))
            ≤ ∑ index, dep index ^ 2 / D.weight index := by
  have hsqrtPos : ∀ index : Fin m, 0 < Real.sqrt (D.weight index) := fun index =>
    Real.sqrt_pos.mpr (D.weight_pos index)
  have hsq : ∀ index : Fin m, Real.sqrt (D.weight index) ^ 2 = D.weight index := fun index =>
    Real.sq_sqrt (D.weight_pos index).le
  rw [dominates_iff_kernelBound D hm pick hinj]
  constructor
  · intro hkernel dep hdep
    have hzero : (scaledAtomRows D)ᵀ *ᵥ (fun index => dep index / Real.sqrt (D.weight index))
        = 0 := by
      rw [transpose_scaledAtomRows_mulVec_eq_zero_iff, ← hdep]
      refine Finset.sum_congr rfl fun index _ => ?_
      have hne : Real.sqrt (D.weight index) ≠ 0 := (hsqrtPos index).ne'
      congr 1
      field_simp
    have hstep := hkernel _ hzero
    calc ∑ slot, dep (pick slot) ^ 2
            / (D.weight (pick slot) * (1 - D.weight (pick slot)))
        = ∑ slot, (dep (pick slot) / Real.sqrt (D.weight (pick slot))) ^ 2
            / (1 - D.weight (pick slot)) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          rw [div_pow, hsq, div_div]
      _ ≤ ∑ index, (dep index / Real.sqrt (D.weight index)) ^ 2 := hstep
      _ = ∑ index, dep index ^ 2 / D.weight index := by
          refine Finset.sum_congr rfl fun index _ => ?_
          rw [div_pow, hsq]
  · intro hdepBound probe hprobe
    have hdep : (∑ index, (Real.sqrt (D.weight index) * probe index) • D.atom index) = 0 :=
      (transpose_scaledAtomRows_mulVec_eq_zero_iff D probe).mp hprobe
    have hstep := hdepBound _ hdep
    calc ∑ slot, probe (pick slot) ^ 2 / (1 - D.weight (pick slot))
        = ∑ slot, (Real.sqrt (D.weight (pick slot)) * probe (pick slot)) ^ 2
            / (D.weight (pick slot) * (1 - D.weight (pick slot))) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          rw [mul_pow, hsq, mul_div_mul_left _ _ (D.weight_pos (pick slot)).ne']
      _ ≤ ∑ index, (Real.sqrt (D.weight index) * probe index) ^ 2 / D.weight index := hstep
      _ = ∑ index, probe index ^ 2 := by
          refine Finset.sum_congr rfl fun index _ => ?_
          rw [mul_pow, hsq, mul_comm, mul_div_assoc, div_self (D.weight_pos index).ne',
            mul_one]

end Gtz

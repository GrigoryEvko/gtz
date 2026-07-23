/-
# The chord theorem's skeleton

Theorem S's three mechanizable bones, stripped of the convexity narrative.

**The chord functions.** `f_X(u) = (1 + ⟨u_X,u⟩)/2 − ν_X(1/2 + ⟨ξ,u⟩)` is
affine in `u`; tightness plus the focal conic make it vanish at the OTHER two
cluster directions (its zero line is the chord through them), and at its own
vertex it equals `1 − ν_X² > 0`.

**The vertex theorem.** The geometric step — the closed inscribed triangle
meets the circle only at its vertices — is here a two-line scalar argument:
for a unit convex combination of distinct unit vectors, subtracting
`|p|² = 1` from `(Σα)² = 1` leaves `Σ_{X<Y} α_Xα_Y(1 − ⟨u_X,u_Y⟩) = 0`, a sum
of nonnegative terms with strictly positive gaps, so at most one coefficient
survives and it is one. No convexity library, no strict-convexity axiom —
the circle's strict convexity IS the pairwise gap `⟨u_X,u_Y⟩ < 1`.
-/
import Mathlib
import Gtz.CertificateFrame

namespace Gtz

/-! ### The chord functions -/

/-- The chord function of cluster `X`, affine in the probe direction. -/
noncomputable def chordFn (clusterDir moment : Fin 2 → ℝ) (conicVal : ℝ)
    (probe : Fin 2 → ℝ) : ℝ :=
  (1 + clusterDir ⬝ᵥ probe) / 2 - conicVal * (1 / 2 + moment ⬝ᵥ probe)

/-- **The chord vanishes at the other clusters**: tightness plus the focal
conic annihilate `f_X` at `u_Y` — the zero line of `f_X` is the chord through
the other two cluster points. -/
theorem chordFn_vanishes {clusterDir otherDir moment : Fin 2 → ℝ}
    {conicValX conicValY : ℝ}
    (htight : (1 + clusterDir ⬝ᵥ otherDir) / 2 = conicValX * conicValY)
    (hconic : conicValY = 1 / 2 + moment ⬝ᵥ otherDir) :
    chordFn clusterDir moment conicValX otherDir = 0 := by
  rw [chordFn, htight, ← hconic]
  ring

/-- **The chord is positive at its own vertex**: `f_X(u_X) = 1 − ν_X²`. -/
theorem chordFn_at_vertex {clusterDir moment : Fin 2 → ℝ} {conicValX : ℝ}
    (hunit : clusterDir ⬝ᵥ clusterDir = 1)
    (hconic : conicValX = 1 / 2 + moment ⬝ᵥ clusterDir) :
    chordFn clusterDir moment conicValX clusterDir = 1 - conicValX ^ 2 := by
  rw [chordFn, hunit, ← hconic]
  ring

/-! ### The vertex theorem -/

/-- **The inscribed triangle meets the circle only at its vertices**: a UNIT
convex combination of three pairwise-distinct unit vectors is one of them.
Subtracting the squared-length identities kills every cross term against the
strictly positive gaps `1 − ⟨u_X,u_Y⟩`. -/
theorem inscribed_triangle_vertex
    {vertexA vertexB vertexC probe : Fin 2 → ℝ}
    {coefA coefB coefC : ℝ}
    (hunitA : vertexA ⬝ᵥ vertexA = 1) (hunitB : vertexB ⬝ᵥ vertexB = 1)
    (hunitC : vertexC ⬝ᵥ vertexC = 1) (hunitP : probe ⬝ᵥ probe = 1)
    (hgapAB : vertexA ⬝ᵥ vertexB < 1) (hgapAC : vertexA ⬝ᵥ vertexC < 1)
    (hgapBC : vertexB ⬝ᵥ vertexC < 1)
    (hnonnegA : 0 ≤ coefA) (hnonnegB : 0 ≤ coefB) (hnonnegC : 0 ≤ coefC)
    (hsum : coefA + coefB + coefC = 1)
    (hcombo : probe = coefA • vertexA + coefB • vertexB + coefC • vertexC) :
    probe = vertexA ∨ probe = vertexB ∨ probe = vertexC := by
  -- expand |p|² through the combination
  have hlen : coefA ^ 2 + coefB ^ 2 + coefC ^ 2
      + 2 * (coefA * coefB * (vertexA ⬝ᵥ vertexB))
      + 2 * (coefA * coefC * (vertexA ⬝ᵥ vertexC))
      + 2 * (coefB * coefC * (vertexB ⬝ᵥ vertexC)) = 1 := by
    have hexpand := hunitP
    rw [hcombo] at hexpand
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at hexpand
    rw [hunitA, hunitB, hunitC, dotProduct_comm vertexB vertexA,
      dotProduct_comm vertexC vertexA, dotProduct_comm vertexC vertexB]
      at hexpand
    nlinarith [hexpand]
  -- subtract (Σα)² = 1: the cross terms against the gaps vanish
  have hcross : coefA * coefB * (1 - vertexA ⬝ᵥ vertexB)
      + coefA * coefC * (1 - vertexA ⬝ᵥ vertexC)
      + coefB * coefC * (1 - vertexB ⬝ᵥ vertexC) = 0 := by
    nlinarith [hlen, hsum]
  -- each summand is nonnegative, so each product of coefficients vanishes
  have htermAB : coefA * coefB = 0 := by
    nlinarith [mul_nonneg hnonnegA hnonnegB, mul_nonneg hnonnegA hnonnegC,
      mul_nonneg hnonnegB hnonnegC, hgapAB, hgapAC, hgapBC, hcross]
  have htermAC : coefA * coefC = 0 := by
    nlinarith [mul_nonneg hnonnegA hnonnegB, mul_nonneg hnonnegA hnonnegC,
      mul_nonneg hnonnegB hnonnegC, hgapAB, hgapAC, hgapBC, hcross]
  have htermBC : coefB * coefC = 0 := by
    nlinarith [mul_nonneg hnonnegA hnonnegB, mul_nonneg hnonnegA hnonnegC,
      mul_nonneg hnonnegB hnonnegC, hgapAB, hgapAC, hgapBC, hcross]
  -- at most one coefficient survives, and the sum forces it to be one
  rcases eq_or_ne coefA 0 with hzeroA | hposA
  · rcases eq_or_ne coefB 0 with hzeroB | hposB
    · -- only C survives
      refine Or.inr (Or.inr ?_)
      have hone : coefC = 1 := by rw [hzeroA, hzeroB] at hsum; linarith
      rw [hcombo, hzeroA, hzeroB, hone, zero_smul, zero_smul, one_smul,
        zero_add, zero_add]
    · -- only B survives
      refine Or.inr (Or.inl ?_)
      have hzeroC : coefC = 0 := by
        rcases mul_eq_zero.mp htermBC with hb | hc
        · exact absurd hb hposB
        · exact hc
      have hone : coefB = 1 := by rw [hzeroA, hzeroC] at hsum; linarith
      rw [hcombo, hzeroA, hzeroC, hone, zero_smul, zero_smul, one_smul,
        zero_add, add_zero]
  · -- only A survives
    refine Or.inl ?_
    have hzeroB : coefB = 0 := by
      rcases mul_eq_zero.mp htermAB with ha | hb
      · exact absurd ha hposA
      · exact hb
    have hzeroC : coefC = 0 := by
      rcases mul_eq_zero.mp htermAC with ha | hc
      · exact absurd ha hposA
      · exact hc
    have hone : coefA = 1 := by rw [hzeroB, hzeroC] at hsum; linarith
    rw [hcombo, hzeroB, hzeroC, hone, zero_smul, zero_smul, one_smul,
      add_zero, add_zero]

/-! ### Affine determination -/

/-- An affine function vanishing at three affinely independent points
vanishes everywhere: the gradient dies on a spanning pair, then the constant
dies at any vertex. -/
theorem affine_vanishes_of_three {const : ℝ}
    {grad vertexA vertexB vertexC : Fin 2 → ℝ}
    (hindep : planarDet (vertexA - vertexC) (vertexB - vertexC) ≠ 0)
    (hatA : const + grad ⬝ᵥ vertexA = 0)
    (hatB : const + grad ⬝ᵥ vertexB = 0)
    (hatC : const + grad ⬝ᵥ vertexC = 0) :
    ∀ probe : Fin 2 → ℝ, const + grad ⬝ᵥ probe = 0 := by
  -- the gradient annihilates the two spanning differences
  have hdiffA : grad ⬝ᵥ (vertexA - vertexC) = 0 := by
    rw [dotProduct_sub]
    linarith
  have hdiffB : grad ⬝ᵥ (vertexB - vertexC) = 0 := by
    rw [dotProduct_sub]
    linarith
  -- Cramer: both gradient components vanish
  have hgradZero : grad = 0 := by
    have hexpandA : grad 0 * (vertexA - vertexC) 0
        + grad 1 * (vertexA - vertexC) 1 = 0 := by
      have := hdiffA
      simpa [dotProduct, Fin.sum_univ_two] using this
    have hexpandB : grad 0 * (vertexB - vertexC) 0
        + grad 1 * (vertexB - vertexC) 1 = 0 := by
      have := hdiffB
      simpa [dotProduct, Fin.sum_univ_two] using this
    have hdet : (vertexA - vertexC) 0 * (vertexB - vertexC) 1
        - (vertexA - vertexC) 1 * (vertexB - vertexC) 0 ≠ 0 := hindep
    have hfirst : grad 0 * ((vertexA - vertexC) 0 * (vertexB - vertexC) 1
        - (vertexA - vertexC) 1 * (vertexB - vertexC) 0) = 0 := by
      linear_combination (vertexB - vertexC) 1 * hexpandA
        - (vertexA - vertexC) 1 * hexpandB
    have hsecond : grad 1 * ((vertexA - vertexC) 0 * (vertexB - vertexC) 1
        - (vertexA - vertexC) 1 * (vertexB - vertexC) 0) = 0 := by
      linear_combination (vertexA - vertexC) 0 * hexpandB
        - (vertexB - vertexC) 0 * hexpandA
    have hzeroFst : grad 0 = 0 :=
      (mul_eq_zero.mp hfirst).resolve_right hdet
    have hzeroSnd : grad 1 = 0 :=
      (mul_eq_zero.mp hsecond).resolve_right hdet
    refine funext fun i => ?_
    fin_cases i
    · exact hzeroFst
    · exact hzeroSnd
  -- the constant then dies at any vertex
  have hconstZero : const = 0 := by
    rw [hgradZero, zero_dotProduct, add_zero] at hatC
    exact hatC
  intro probe
  rw [hgradZero, hconstZero, zero_dotProduct, add_zero]

/-! ### The full silence envelope -/

/-- **Theorem S**: at a pairwise-tight cluster triangle with a nondegenerate
inscribed triangle, any unit direction where all three chord functions are
nonnegative is one of the cluster directions. The normalized chord values are
the barycentric coordinates: both reconstruction identities are affine
functions of the probe vanishing at the three vertices, hence identically
zero by determination, and the vertex theorem finishes. -/
theorem chord_silence_envelope
    {vertexA vertexB vertexC probe moment : Fin 2 → ℝ}
    {conicA conicB conicC : ℝ}
    (hunitA : vertexA ⬝ᵥ vertexA = 1) (hunitB : vertexB ⬝ᵥ vertexB = 1)
    (hunitC : vertexC ⬝ᵥ vertexC = 1) (hunitP : probe ⬝ᵥ probe = 1)
    (hgapAB : vertexA ⬝ᵥ vertexB < 1) (hgapAC : vertexA ⬝ᵥ vertexC < 1)
    (hgapBC : vertexB ⬝ᵥ vertexC < 1)
    (hindep : planarDet (vertexA - vertexC) (vertexB - vertexC) ≠ 0)
    (hconicAtA : conicA = 1 / 2 + moment ⬝ᵥ vertexA)
    (hconicAtB : conicB = 1 / 2 + moment ⬝ᵥ vertexB)
    (hconicAtC : conicC = 1 / 2 + moment ⬝ᵥ vertexC)
    (hopenA : conicA ^ 2 < 1) (hopenB : conicB ^ 2 < 1)
    (hopenC : conicC ^ 2 < 1)
    (htightAB : (1 + vertexA ⬝ᵥ vertexB) / 2 = conicA * conicB)
    (htightAC : (1 + vertexA ⬝ᵥ vertexC) / 2 = conicA * conicC)
    (htightBC : (1 + vertexB ⬝ᵥ vertexC) / 2 = conicB * conicC)
    (hsilentA : 0 ≤ chordFn vertexA moment conicA probe)
    (hsilentB : 0 ≤ chordFn vertexB moment conicB probe)
    (hsilentC : 0 ≤ chordFn vertexC moment conicC probe) :
    probe = vertexA ∨ probe = vertexB ∨ probe = vertexC := by
  have hposA : (0 : ℝ) < 1 - conicA ^ 2 := by linarith
  have hposB : (0 : ℝ) < 1 - conicB ^ 2 := by linarith
  have hposC : (0 : ℝ) < 1 - conicC ^ 2 := by linarith
  -- the nine chord values at the vertices
  have hvalAA : chordFn vertexA moment conicA vertexA = 1 - conicA ^ 2 :=
    chordFn_at_vertex hunitA hconicAtA
  have hvalBB : chordFn vertexB moment conicB vertexB = 1 - conicB ^ 2 :=
    chordFn_at_vertex hunitB hconicAtB
  have hvalCC : chordFn vertexC moment conicC vertexC = 1 - conicC ^ 2 :=
    chordFn_at_vertex hunitC hconicAtC
  have hvalAB : chordFn vertexA moment conicA vertexB = 0 :=
    chordFn_vanishes htightAB hconicAtB
  have hvalAC : chordFn vertexA moment conicA vertexC = 0 :=
    chordFn_vanishes htightAC hconicAtC
  have hvalBA : chordFn vertexB moment conicB vertexA = 0 :=
    chordFn_vanishes
      (by rw [dotProduct_comm]; linear_combination htightAB) hconicAtA
  have hvalBC : chordFn vertexB moment conicB vertexC = 0 :=
    chordFn_vanishes htightBC hconicAtC
  have hvalCA : chordFn vertexC moment conicC vertexA = 0 :=
    chordFn_vanishes
      (by rw [dotProduct_comm]; linear_combination htightAC) hconicAtA
  have hvalCB : chordFn vertexC moment conicC vertexB = 0 :=
    chordFn_vanishes
      (by rw [dotProduct_comm]; linear_combination htightBC) hconicAtB
  -- shorthand for the barycentric candidates
  set coefOf : (Fin 2 → ℝ) → ℝ → ℝ → (Fin 2 → ℝ) → ℝ :=
    fun clusterDir conicVal gap dir =>
      chordFn clusterDir moment conicVal dir / gap with hcoefOf
  -- the affine presentation of each normalized chord value
  have haffine : ∀ (clusterDir : Fin 2 → ℝ) (conicVal gap : ℝ), gap ≠ 0
      → ∀ dir, chordFn clusterDir moment conicVal dir / gap
        = (1 / 2 - conicVal / 2) / gap
          + (gap⁻¹ • ((1 / 2 : ℝ) • clusterDir - conicVal • moment))
            ⬝ᵥ dir := by
    intro clusterDir conicVal gap hgap dir
    simp only [chordFn, smul_dotProduct, sub_dotProduct, smul_eq_mul,
      add_dotProduct]
    field_simp
    ring
  -- THE SUM IDENTITY: Σ α_X(dir) = 1 for every dir, by determination
  have hsumIdentity : ∀ dir : Fin 2 → ℝ,
      chordFn vertexA moment conicA dir / (1 - conicA ^ 2)
        + chordFn vertexB moment conicB dir / (1 - conicB ^ 2)
        + chordFn vertexC moment conicC dir / (1 - conicC ^ 2) = 1 := by
    -- affine data of the sum minus one
    set sumConst := (1 / 2 - conicA / 2) / (1 - conicA ^ 2)
      + (1 / 2 - conicB / 2) / (1 - conicB ^ 2)
      + (1 / 2 - conicC / 2) / (1 - conicC ^ 2) - 1 with hsumConst
    set sumGrad := (1 - conicA ^ 2)⁻¹
        • ((1 / 2 : ℝ) • vertexA - conicA • moment)
      + (1 - conicB ^ 2)⁻¹ • ((1 / 2 : ℝ) • vertexB - conicB • moment)
      + (1 - conicC ^ 2)⁻¹ • ((1 / 2 : ℝ) • vertexC - conicC • moment)
      with hsumGrad
    have hshape : ∀ dir : Fin 2 → ℝ,
        chordFn vertexA moment conicA dir / (1 - conicA ^ 2)
          + chordFn vertexB moment conicB dir / (1 - conicB ^ 2)
          + chordFn vertexC moment conicC dir / (1 - conicC ^ 2) - 1
        = sumConst + sumGrad ⬝ᵥ dir := by
      intro dir
      rw [hsumConst, hsumGrad,
        haffine vertexA conicA _ (ne_of_gt hposA) dir,
        haffine vertexB conicB _ (ne_of_gt hposB) dir,
        haffine vertexC conicC _ (ne_of_gt hposC) dir]
      simp only [add_dotProduct]
      ring
    have hzeroAll := affine_vanishes_of_three hindep
      (by rw [← hshape vertexA, hvalAA, hvalBA, hvalCA]
          field_simp
          ring)
      (by rw [← hshape vertexB, hvalBB, hvalAB, hvalCB]
          field_simp
          ring)
      (by rw [← hshape vertexC, hvalCC, hvalAC, hvalBC]
          field_simp
          ring)
    intro dir
    have := hshape dir
    rw [hzeroAll dir] at this
    linarith
  -- THE RECONSTRUCTION IDENTITY: Σ α_X(dir)·u_X = dir, coordinatewise
  have hcomboIdentity : ∀ dir : Fin 2 → ℝ, ∀ i : Fin 2,
      (chordFn vertexA moment conicA dir / (1 - conicA ^ 2)) * vertexA i
        + (chordFn vertexB moment conicB dir / (1 - conicB ^ 2)) * vertexB i
        + (chordFn vertexC moment conicC dir / (1 - conicC ^ 2)) * vertexC i
      = dir i := by
    intro dir i
    set comboConst := ((1 / 2 - conicA / 2) / (1 - conicA ^ 2)) * vertexA i
      + ((1 / 2 - conicB / 2) / (1 - conicB ^ 2)) * vertexB i
      + ((1 / 2 - conicC / 2) / (1 - conicC ^ 2)) * vertexC i
      with hcomboConst
    set comboGrad := vertexA i • ((1 - conicA ^ 2)⁻¹
        • ((1 / 2 : ℝ) • vertexA - conicA • moment))
      + vertexB i • ((1 - conicB ^ 2)⁻¹
        • ((1 / 2 : ℝ) • vertexB - conicB • moment))
      + vertexC i • ((1 - conicC ^ 2)⁻¹
        • ((1 / 2 : ℝ) • vertexC - conicC • moment))
      - Pi.single i 1 with hcomboGrad
    have hshape : ∀ probeDir : Fin 2 → ℝ,
        (chordFn vertexA moment conicA probeDir / (1 - conicA ^ 2))
            * vertexA i
          + (chordFn vertexB moment conicB probeDir / (1 - conicB ^ 2))
            * vertexB i
          + (chordFn vertexC moment conicC probeDir / (1 - conicC ^ 2))
            * vertexC i - probeDir i
        = comboConst + comboGrad ⬝ᵥ probeDir := by
      intro probeDir
      rw [hcomboConst, hcomboGrad,
        haffine vertexA conicA _ (ne_of_gt hposA) probeDir,
        haffine vertexB conicB _ (ne_of_gt hposB) probeDir,
        haffine vertexC conicC _ (ne_of_gt hposC) probeDir]
      simp only [add_dotProduct, sub_dotProduct, smul_dotProduct,
        smul_eq_mul, Pi.single_apply]
      have hsingle : Pi.single i (1 : ℝ) ⬝ᵥ probeDir = probeDir i := by
        simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq,
          Finset.mem_univ]
      rw [show (Pi.single i (1 : ℝ)) ⬝ᵥ probeDir = probeDir i from hsingle]
      ring
    have hzeroAll := affine_vanishes_of_three hindep
      (by rw [← hshape vertexA, hvalAA, hvalBA, hvalCA]
          field_simp
          ring)
      (by rw [← hshape vertexB, hvalBB, hvalAB, hvalCB]
          field_simp
          ring)
      (by rw [← hshape vertexC, hvalCC, hvalAC, hvalBC]
          field_simp
          ring)
    have := hshape dir
    rw [hzeroAll dir] at this
    linarith
  -- assemble the barycentric data and finish with the vertex theorem
  refine inscribed_triangle_vertex hunitA hunitB hunitC hunitP hgapAB hgapAC
    hgapBC (div_nonneg hsilentA hposA.le) (div_nonneg hsilentB hposB.le)
    (div_nonneg hsilentC hposC.le) (hsumIdentity probe) ?_
  funext i
  have hcoord := hcomboIdentity probe i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

end Gtz

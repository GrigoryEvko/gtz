/-
# The two-plane collapse: a unit atom in a boundary plane drags a third atom in

`Gtz.k2SixThree_parallel_or_boundary_plane` leaves one branch alive: the unit
atom lies in the plane of two atoms whose pair minor vanishes, with its own
readings as coordinates,

  `(g_d . g_a) g_d + (g_d' . g_a) g_d' = g_a` .

This module reads Parseval through that relation.  The result is that the plane
does not hold two atoms and a passenger — it holds FOUR:

  **`Gtz.twoPlane_bracket_eq_zero`: any atom that reads the unit atom at a
  nonzero value lies in the SAME plane as `g_d` and `g_d'`.**

## The mechanism, and why it costs nothing

Parseval as an operator at `g_a` (`Gtz.parseval_reproduces`) says the weighted
readings rebuild the probe.  At a unit atom the diagonal term is `t_a . g_a`,
and every atom blind to `g_a` drops out, so only the four labels `a, d, d', e`
survive (`Gtz.parseval_at_unitAtom_four_labels`).  Substituting the plane
relation for `g_a` on both sides and collecting leaves

  **`(g_d.g_a)(t_a + t_d - 1) g_d + (g_d'.g_a)(t_a + t_d' - 1) g_d'
      + t_e (g_e.g_a) g_e = 0`**

(`Gtz.unitAtom_plane_collapse_relation`), one `linear_combination` per
coordinate.  The last coefficient is a product of a positive weight and the
reading, so a live reading makes the relation nontrivial and the three atoms
dependent.

At `(6,3)` the reader is supplied for free: `Gtz.exists_outside_reading_sq_gt_one`
produces an atom outside the funnel dominator whose squared reading EXCEEDS one,
so it is live by a wide margin.  The blind labels are the two atoms orthogonal to
the unit atom, which is exactly the hypothesis `hcover` asks for.

## What this settles and what it does not

It settles the shape: `g_a` and `g_e` both lie in `span(g_d, g_d')`, so four of
the six atoms are coplanar and the whole component of Parseval normal to that
plane is carried by the remaining two.  It does NOT by itself refuse the
configuration.

[MEASURED, and the measurement names the shape a successor needs.  The collapsed
family was parametrised exactly — Parseval residual `1.0e-15`, and the recorded
consequences `q(g_d,g_d') = 0` and `bracket(g_d,g_d',g_e) = 0` reproduce to
`8e-17` rather than being imposed.  Over that family `max_T lambda_min(S_T - 1)`
never reached zero: `+0.257` over 30351 samples, `+0.081` under adversarial
descent at weight floor `0.05`.  So the configuration IS refused.  But the
margin tracks the floor linearly — `0.105, 0.041, 0.020, 0.008` at floors
`0.05, 0.02, 0.01, 0.004`, i.e. about twice the smallest weight — so no
certificate with a positive constant can exist, and any proof must consume
weight positivity.  No single triple does the work: each of the five triples
through the reader that carry the maximum can itself fall to `-1` elsewhere in
the family.]
-/
import Gtz.Wave.BlindMemberPlane
import Gtz.Ties.SpikeMatroidObstruction
import Gtz.Ties.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Parseval at a unit atom, with the blind labels removed -/

/-- **PARSEVAL AT A UNIT ATOM SEES FOUR LABELS.**  The weighted readings rebuild
the probe, the unit atom contributes its bare weight, and every label blind to
the atom drops out of the sum. -/
theorem parseval_at_unitAtom_four_labels (D : WeightedDesign m 3)
    {a d dp e : Fin m}
    (had : a ≠ d) (hadp : a ≠ dp) (hae : a ≠ e)
    (hddp : d ≠ dp) (hde : d ≠ e) (hdpe : dp ≠ e)
    (hunit : leverageOf (D.atom a) = 1)
    (hcover : ∀ c : Fin m, c ≠ a → c ≠ d → c ≠ dp → c ≠ e →
      D.atom c ⬝ᵥ D.atom a = 0) :
    D.weight a • D.atom a
        + (D.weight d * (D.atom d ⬝ᵥ D.atom a)) • D.atom d
        + (D.weight dp * (D.atom dp ⬝ᵥ D.atom a)) • D.atom dp
        + (D.weight e * (D.atom e ⬝ᵥ D.atom a)) • D.atom e = D.atom a := by
  classical
  have hself : D.atom a ⬝ᵥ D.atom a = 1 := by
    rw [dotProduct_self_eq_leverage]; exact hunit
  have hfull := parseval_reproduces D (D.atom a)
  have hsub : ∑ c ∈ ({a, d, dp, e} : Finset (Fin m)),
        (D.weight c * (D.atom c ⬝ᵥ D.atom a)) • D.atom c
      = ∑ c, (D.weight c * (D.atom c ⬝ᵥ D.atom a)) • D.atom c := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro c _ hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    rw [hcover c h1 h2 h3 h4, mul_zero, zero_smul]
  have hexpand : ∑ c ∈ ({a, d, dp, e} : Finset (Fin m)),
        (D.weight c * (D.atom c ⬝ᵥ D.atom a)) • D.atom c
      = D.weight a • D.atom a
        + (D.weight d * (D.atom d ⬝ᵥ D.atom a)) • D.atom d
        + (D.weight dp * (D.atom dp ⬝ᵥ D.atom a)) • D.atom dp
        + (D.weight e * (D.atom e ⬝ᵥ D.atom a)) • D.atom e := by
    rw [Finset.sum_insert (by simp [had, hadp, hae]),
      Finset.sum_insert (by simp [hddp, hde]),
      Finset.sum_insert (by simp [hdpe]),
      Finset.sum_singleton, hself, mul_one]
    abel
  rw [← hexpand, hsub]
  exact hfull

/-! ## 2. The collapse relation -/

/-- **THE COLLAPSE RELATION.**  Substituting the plane relation for the unit atom
on both sides of Parseval leaves a linear relation among the two plane atoms and
the reader.  One `linear_combination` per coordinate, no positivity. -/
theorem unitAtom_plane_collapse_relation (D : WeightedDesign m 3)
    {a d dp e : Fin m}
    (had : a ≠ d) (hadp : a ≠ dp) (hae : a ≠ e)
    (hddp : d ≠ dp) (hde : d ≠ e) (hdpe : dp ≠ e)
    (hunit : leverageOf (D.atom a) = 1)
    (hcover : ∀ c : Fin m, c ≠ a → c ≠ d → c ≠ dp → c ≠ e →
      D.atom c ⬝ᵥ D.atom a = 0)
    (hplane : (D.atom d ⬝ᵥ D.atom a) • D.atom d
      + (D.atom dp ⬝ᵥ D.atom a) • D.atom dp = D.atom a) :
    ((D.atom d ⬝ᵥ D.atom a) * (D.weight a + D.weight d - 1)) • D.atom d
        + ((D.atom dp ⬝ᵥ D.atom a) * (D.weight a + D.weight dp - 1)) • D.atom dp
        + (D.weight e * (D.atom e ⬝ᵥ D.atom a)) • D.atom e = 0 := by
  have hpar := parseval_at_unitAtom_four_labels D had hadp hae hddp hde hdpe hunit hcover
  funext i
  have hp := congrFun hpar i
  have hq := congrFun hplane i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hp hq ⊢
  linear_combination hp + (D.weight a - 1) * hq

/-! ## 3. Four atoms in one plane -/

/-- **THE READER JOINS THE PLANE.**  An atom whose reading of the unit atom is
nonzero is dependent on the two plane atoms, so it lies in their span. -/
theorem twoPlane_bracket_eq_zero (D : WeightedDesign m 3)
    {a d dp e : Fin m}
    (had : a ≠ d) (hadp : a ≠ dp) (hae : a ≠ e)
    (hddp : d ≠ dp) (hde : d ≠ e) (hdpe : dp ≠ e)
    (hunit : leverageOf (D.atom a) = 1)
    (hcover : ∀ c : Fin m, c ≠ a → c ≠ d → c ≠ dp → c ≠ e →
      D.atom c ⬝ᵥ D.atom a = 0)
    (hplane : (D.atom d ⬝ᵥ D.atom a) • D.atom d
      + (D.atom dp ⬝ᵥ D.atom a) • D.atom dp = D.atom a)
    (hlive : D.atom e ⬝ᵥ D.atom a ≠ 0) :
    tripleBracket (D.atom d) (D.atom dp) (D.atom e) = 0 := by
  refine EndpointSpike.tripleBracket_eq_zero_of_dependence _ _ _ _ _ _ ?_
    (unitAtom_plane_collapse_relation D had hadp hae hddp hde hdpe hunit hcover hplane)
  exact Or.inr (Or.inr (mul_ne_zero (ne_of_gt (D.weight_pos e)) hlive))

/-- **THE UNIT ATOM IS IN THE PLANE TOO.**  The plane relation is itself a
dependency, with the unit atom carried at coefficient one. -/
theorem unitAtom_plane_bracket_eq_zero (D : WeightedDesign m 3)
    {a d dp : Fin m}
    (hplane : (D.atom d ⬝ᵥ D.atom a) • D.atom d
      + (D.atom dp ⬝ᵥ D.atom a) • D.atom dp = D.atom a) :
    tripleBracket (D.atom a) (D.atom d) (D.atom dp) = 0 := by
  refine EndpointSpike.tripleBracket_eq_zero_of_dependence _ _ _ _
    (-(D.atom d ⬝ᵥ D.atom a)) (-(D.atom dp ⬝ᵥ D.atom a)) (Or.inl one_ne_zero) ?_
  funext i
  have hq := congrFun hplane i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hq ⊢
  linear_combination -hq

/-- **THE TWO-PLANE COLLAPSE.**  A unit atom trapped in the plane of two atoms
drags every live reader into the same plane: both `g_a` and `g_e` are dependent
on `g_d` and `g_d'`.  With `g_d`, `g_d'` independent this says four atoms of the
design are coplanar, and the whole component of Parseval normal to that plane is
carried by the remaining labels. -/
theorem twoPlane_collapse (D : WeightedDesign m 3)
    {a d dp e : Fin m}
    (had : a ≠ d) (hadp : a ≠ dp) (hae : a ≠ e)
    (hddp : d ≠ dp) (hde : d ≠ e) (hdpe : dp ≠ e)
    (hunit : leverageOf (D.atom a) = 1)
    (hcover : ∀ c : Fin m, c ≠ a → c ≠ d → c ≠ dp → c ≠ e →
      D.atom c ⬝ᵥ D.atom a = 0)
    (hplane : (D.atom d ⬝ᵥ D.atom a) • D.atom d
      + (D.atom dp ⬝ᵥ D.atom a) • D.atom dp = D.atom a)
    (hlive : D.atom e ⬝ᵥ D.atom a ≠ 0) :
    tripleBracket (D.atom a) (D.atom d) (D.atom dp) = 0
      ∧ tripleBracket (D.atom d) (D.atom dp) (D.atom e) = 0 :=
  ⟨unitAtom_plane_bracket_eq_zero D hplane,
    twoPlane_bracket_eq_zero D had hadp hae hddp hde hdpe hunit hcover hplane hlive⟩

/-! ## 4. The six labels of a `(6,3)` design -/

/-- Six pairwise distinct labels exhaust `Fin 6`. -/
theorem six_labels_cover {a y z d dp e : Fin 6}
    (h1 : a ≠ y) (h2 : a ≠ z) (h3 : a ≠ d) (h4 : a ≠ dp) (h5 : a ≠ e)
    (h6 : y ≠ z) (h7 : y ≠ d) (h8 : y ≠ dp) (h9 : y ≠ e)
    (h10 : z ≠ d) (h11 : z ≠ dp) (h12 : z ≠ e)
    (h13 : d ≠ dp) (h14 : d ≠ e) (h15 : dp ≠ e) :
    ({a, y, z, d, dp, e} : Finset (Fin 6)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3, h4, h5]),
    Finset.card_insert_of_notMem (by simp [h6, h7, h8, h9]),
    Finset.card_insert_of_notMem (by simp [h10, h11, h12]),
    Finset.card_insert_of_notMem (by simp [h13, h14]),
    Finset.card_insert_of_notMem (by simp [h15]),
    Finset.card_singleton]
  simp

/-- **THE BLIND LABELS COVER THE COMPLEMENT.**  With six distinct labels and the
two orthogonal atoms among them, every label outside the four that carry the
collapse is blind to the unit atom. -/
theorem blindReading_cover (D : WeightedDesign 6 3) {a y z d dp e : Fin 6}
    (h1 : a ≠ y) (h2 : a ≠ z) (h3 : a ≠ d) (h4 : a ≠ dp) (h5 : a ≠ e)
    (h6 : y ≠ z) (h7 : y ≠ d) (h8 : y ≠ dp) (h9 : y ≠ e)
    (h10 : z ≠ d) (h11 : z ≠ dp) (h12 : z ≠ e)
    (h13 : d ≠ dp) (h14 : d ≠ e) (h15 : dp ≠ e)
    (hoy : D.atom y ⬝ᵥ D.atom a = 0) (hoz : D.atom z ⬝ᵥ D.atom a = 0) :
    ∀ c : Fin 6, c ≠ a → c ≠ d → c ≠ dp → c ≠ e → D.atom c ⬝ᵥ D.atom a = 0 := by
  intro c hca hcd hcdp hce
  have hmem : c ∈ ({a, y, z, d, dp, e} : Finset (Fin 6)) := by
    rw [six_labels_cover h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15]
    exact Finset.mem_univ c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hca
  · exact hoy
  · exact hoz
  · exact absurd rfl hcd
  · exact absurd rfl hcdp
  · exact absurd rfl hce

/-! ## 5. The two-zeros case at `(6,3)`, assembled -/

/-- **THE TWO-ZEROS CASE COLLAPSES TO TWO PLANES.**  A boundary `(6,3)` system
carrying a unit atom orthogonal to two other atoms either has a collinear pair,
or four of its six atoms are coplanar: the unit atom and a live reader both lie
in the plane of the two remaining members of the funnel dominator.

The reader is not assumed — `Gtz.exists_outside_reading_sq_gt_one` produces an
atom outside the dominator whose squared reading exceeds one, and the two
orthogonal atoms are blind, so the reader is neither of them. -/
theorem k2SixThree_parallel_or_two_plane (D : WeightedDesign 6 3) (htie : IsTie D)
    {a y z : Fin 6} (hay : a ≠ y) (haz : a ≠ z) (hyz : y ≠ z)
    (hunit : leverageOf (D.atom a) = 1)
    (hoy : D.atom y ⬝ᵥ D.atom a = 0) (hoz : D.atom z ⬝ᵥ D.atom a = 0) :
    HasParallelPair D
      ∨ ∃ d dp e : Fin 6, d ≠ dp ∧ d ≠ e ∧ dp ≠ e
          ∧ a ≠ d ∧ a ≠ dp ∧ a ≠ e
          ∧ 1 < (D.atom e ⬝ᵥ D.atom a) ^ 2
          ∧ pairGapMinor (D.atom d) (D.atom dp) = 0
          ∧ tripleBracket (D.atom a) (D.atom d) (D.atom dp) = 0
          ∧ tripleBracket (D.atom d) (D.atom dp) (D.atom e) = 0 := by
  classical
  obtain ⟨T, hcard, havoid, -, hfix⟩ := isTie_sixThree_unitAtom_funnel D htie a hunit
  have hmeet := funnel_dominator_meets_orthogonal_pair D hay haz hyz hunit hoy hoz
    hcard havoid hfix
  -- the reader, from Parseval against the funnel budget
  obtain ⟨u, hua, huT, hread⟩ := exists_outside_reading_sq_gt_one D hunit hcard havoid hfix
  -- a blind member `b` of the dominator, with the other member `w` still in play
  have hwork : ∀ b w : Fin 6, b ∈ T → w ∉ T → w ≠ a → b ≠ w →
      D.atom b ⬝ᵥ D.atom a = 0 → D.atom w ⬝ᵥ D.atom a = 0 →
      (HasParallelPair D
        ∨ ∃ d dp e : Fin 6, d ≠ dp ∧ d ≠ e ∧ dp ≠ e
            ∧ a ≠ d ∧ a ≠ dp ∧ a ≠ e
            ∧ 1 < (D.atom e ⬝ᵥ D.atom a) ^ 2
            ∧ pairGapMinor (D.atom d) (D.atom dp) = 0
            ∧ tripleBracket (D.atom a) (D.atom d) (D.atom dp) = 0
            ∧ tripleBracket (D.atom d) (D.atom dp) (D.atom e) = 0) := by
    intro b w hbT hwT hwa hbw hb hw
    -- split the dominator as `{b, d, dp}`
    have hUcard : (T.erase b).card = 2 := by
      rw [Finset.card_erase_of_mem hbT, hcard]
    obtain ⟨d, dp, hddp, hU⟩ := Finset.card_eq_two.mp hUcard
    have hT : T = ({b, d, dp} : Finset (Fin 6)) := by
      rw [← Finset.insert_erase hbT, hU]
    have hdT : d ∈ T := by rw [hT]; simp
    have hdpT : dp ∈ T := by rw [hT]; simp
    have hbd : b ≠ d := by
      intro h; exact (Finset.notMem_erase b T) (hU ▸ (h ▸ (by simp : d ∈ ({d, dp} : Finset (Fin 6)))))
    have hbdp : b ≠ dp := by
      intro h; exact (Finset.notMem_erase b T) (hU ▸ (h ▸ (by simp : dp ∈ ({d, dp} : Finset (Fin 6)))))
    have had : a ≠ d := fun h => havoid (h ▸ hdT)
    have hadp : a ≠ dp := fun h => havoid (h ▸ hdpT)
    have hwd : w ≠ d := fun h => hwT (h ▸ hdT)
    have hwdp : w ≠ dp := fun h => hwT (h ▸ hdpT)
    -- the reader is neither blind label
    have hbu : b ≠ u := fun h => huT (h ▸ hbT)
    have hwu : w ≠ u := by
      intro h; rw [← h, hw] at hread; norm_num at hread
    have hdu : d ≠ u := fun h => huT (h ▸ hdT)
    have hdpu : dp ≠ u := fun h => huT (h ▸ hdpT)
    -- the plane and the vanishing pair minor
    have hfix' : subsetSum D ({b, d, dp} : Finset (Fin 6)) *ᵥ D.atom a = D.atom a := by
      rw [← hT]; exact hfix
    obtain ⟨hmin, hplane⟩ :=
      funnel_blind_member_plane_and_pairMinor D hbd hbdp hddp hunit hfix' hb
    have hcover := blindReading_cover D (a := a) (y := b) (z := w) (d := d) (dp := dp) (e := u)
      (Ne.symm (fun h => havoid (h ▸ hbT))) (Ne.symm hwa) had hadp (Ne.symm hua)
      hbw hbd hbdp hbu hwd hwdp hwu hddp hdu hdpu hb hw
    have hlive : D.atom u ⬝ᵥ D.atom a ≠ 0 := by
      intro h; rw [h] at hread; norm_num at hread
    obtain ⟨hbr1, hbr2⟩ := twoPlane_collapse D had hadp (Ne.symm hua) hddp hdu hdpu
      hunit hcover hplane hlive
    exact Or.inr ⟨d, dp, u, hddp, hdu, hdpu, had, hadp, Ne.symm hua, hread, hmin, hbr1, hbr2⟩
  by_cases hyT : y ∈ T
  · by_cases hzT : z ∈ T
    · -- both orthogonal atoms inside: two blind readings give the collinear pair
      refine Or.inl ?_
      have hpairSub : ({y, z} : Finset (Fin 6)) ⊆ T := by
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hyT
        · rw [Finset.mem_singleton] at hc; subst hc; exact hzT
      have hpairCard : ({y, z} : Finset (Fin 6)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      have hleft : (T \ ({y, z} : Finset (Fin 6))).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpairSub, hcard, hpairCard]
      obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hleft
      have hc₀mem : c₀ ∈ T \ ({y, z} : Finset (Fin 6)) := by
        rw [hc₀]; exact Finset.mem_singleton_self c₀
      refine unitAtom_parallel_of_two_readings_zero (m := 5) D havoid
        (Finset.mem_sdiff.mp hc₀mem).1 hfix ?_
      intro c hc hne
      by_cases hcy : c = y
      · rw [hcy]; exact hoy
      by_cases hcz : c = z
      · rw [hcz]; exact hoz
      · exact absurd (Finset.mem_singleton.mp
          (hc₀ ▸ Finset.mem_sdiff.mpr ⟨hc, by simp [hcy, hcz]⟩)) hne
    · exact hwork y z hyT hzT (Ne.symm haz) hyz hoy hoz
  · exact hwork z y (hmeet.resolve_left hyT) hyT (Ne.symm hay) (Ne.symm hyz) hoz hoy

end Gtz

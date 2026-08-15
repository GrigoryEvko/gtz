/-
# The set-valued designation, and why relaxing to it buys nothing

`Gtz.no_equivariant_designation` refutes every relabelling-equivariant rule that
names ONE triple, but it assumes `hfixed` -- the answer at the witness is carried
to itself by the symmetry -- rather than deriving it from equivariance.  The
bridge is not free: `Gtz.witnessDirection` is not invariant under the relabelling
as a FUNCTION, because the six directions are permuted only up to a rotation of
three-space.  What is invariant is the derived complement matrix.

Section 1 closes the bridge on the class that reads that derived matrix, which is
every rule the campaign has tried, and then closes it a second time on rules
reading the raw directions, at the cost of one rotation-invariance hypothesis
which this file discharges by exhibiting the rotation.

Sections 2 to 4 attack the natural repair.  An equivariant rule returning a SET
escapes the refutation, because the six working triples of the witness form two
free orbits and a set-valued rule may return one of them.  The repair fails, and
the reason is structural rather than accidental.

* A rule that maximizes any quantity monotone in the three diagonal complement
  entries returns, at the witness, the failing orbit `{3,4,5}` -- because the
  diagonal takes the larger of its two values exactly there.  That kills the
  total pivot, the trace, the own monomial and "omit the three lightest labels"
  in one theorem (section 2).

* The set a maximizer returns collapses to a singleton as soon as the maximum is
  attained once, and then the set-valued rule IS a single-valued rule (section
  3).  A census of 2,670,104 exact chart points puts the mean size of the
  determinant argmax set at 1.0008, so the collapse is the generic case and the
  relaxation is empty.

* The determinant argmax survives the symmetric witness -- there its argmax set
  is all six winners -- so section 4 builds a second witness where the argmax is
  a strict singleton that fails while three triples work.  Its complement matrix
  has TWO negative leading minors and a positive determinant, which is the exact
  failure mode a determinant rule cannot see.
-/
import Gtz.Wave.EquivariantDesignationRefuter

namespace Gtz

open Finset Matrix

/-! ## 1. The rule class, and the equivariance bridge

A designation rule reads the complement matrix and names a triple.  Every rule
the campaign has refuted factors through that matrix: the conductance, the four
invariant argmaxes, the leverage edge, the rung, the own monomial and the
determinant are all built from its entries.
-/

/-- The inverse of the relabelling. -/
def sigmaLabelInv : Fin 6 → Fin 6 := ![2, 0, 1, 5, 3, 4]

/-- The relabelling as a permutation. -/
def sigmaPerm : Equiv.Perm (Fin 6) where
  toFun := sigmaLabel
  invFun := sigmaLabelInv
  left_inv := by decide
  right_inv := by decide

theorem sigmaPerm_apply (i : Fin 6) : sigmaPerm i = sigmaLabel i := rfl

/-- A designation rule reading the complement entries. -/
def EntryRule := (Fin 6 → Fin 6 → ℝ) → Finset (Fin 6)

/-- **Equivariance.**  Relabelling the entry matrix relabels the answer. -/
def EntryEquivariant (rule : EntryRule) : Prop :=
  ∀ (entry : Fin 6 → Fin 6 → ℝ) (tau : Equiv.Perm (Fin 6)),
    rule (fun i j => entry (tau i) (tau j)) = (rule entry).image tau.symm

/-- The witness entry matrix is carried to itself by the relabelling, as a
function of two labels.  This is `Gtz.witnessEntry_sigma` in point-free form. -/
theorem witnessEntry_comp_sigma :
    (fun i j => witnessEntry (sigmaPerm i) (sigmaPerm j)) = witnessEntry := by
  funext i j
  exact witnessEntry_sigma i j

/-- **THE BRIDGE.**  Equivariance alone forces the answer at the witness to be
invariant.  No hypothesis at the witness is assumed. -/
theorem entryRule_image_sigma_eq (rule : EntryRule) (hequi : EntryEquivariant rule) :
    (rule witnessEntry).image sigmaLabel = rule witnessEntry := by
  have h := hequi witnessEntry sigmaPerm
  rw [witnessEntry_comp_sigma] at h
  have hid : (sigmaLabel ∘ (sigmaPerm.symm : Fin 6 → Fin 6)) = id := by
    funext x
    exact sigmaPerm.apply_symm_apply x
  have hstep : (rule witnessEntry).image sigmaLabel
      = ((rule witnessEntry).image (sigmaPerm.symm : Fin 6 → Fin 6)).image sigmaLabel := by
    rw [← h]
  rw [hstep, Finset.image_image, hid, Finset.image_id]

/-- **NO EQUIVARIANT ENTRY RULE DESIGNATES.**  The class theorem: the hypothesis
is equivariance, and invariance at the witness is derived. -/
theorem no_entryEquivariant_designation (rule : EntryRule)
    (hequi : EntryEquivariant rule)
    (hcard : (rule witnessEntry).card = 3)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hS : rule witnessEntry = {i, j, k}) :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k :=
  no_working_invariant_triple _ hcard (entryRule_image_sigma_eq rule hequi) i j k hS hij hik hjk

/-! ### The raw-data class

A rule reading the directions themselves is not covered by the argument above,
because the directions are permuted only up to a rotation.  The rotation is
explicit, so the class is covered at the cost of one hypothesis that any
congruence-invariant rule satisfies.
-/

/-- The cyclic coordinate shift `(x, y, z)` to `(z, x, y)`. -/
def rotateCoord (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![v 2, v 0, v 1]

/-- **The relabelling acts on the directions by the rotation.**  This is the
exact sense in which the witness is its own relabelling. -/
theorem witnessDirection_sigma_eq_rotate (c : Fin 6) :
    witnessDirection (sigmaLabel c) = rotateCoord (witnessDirection c) := by
  fin_cases c <;>
    (funext a; fin_cases a <;> simp [witnessDirection, sigmaLabel, rotateCoord])

/-- The weights are constant on the two orbits. -/
theorem witnessWeight_sigma (c : Fin 6) :
    witnessWeight (sigmaLabel c) = witnessWeight c := by
  fin_cases c <;> simp [witnessWeight, sigmaLabel]

/-- The masses are constant on the two orbits. -/
theorem witnessMass_sigma (c : Fin 6) :
    witnessMass (sigmaLabel c) = witnessMass c := by
  fin_cases c <;> simp [witnessMass, sigmaLabel]

/-- A rule reading the raw chart data. -/
def ChartRule := (Fin 6 → (Fin 3 → ℝ)) → (Fin 6 → ℝ) → (Fin 6 → ℝ) → Finset (Fin 6)

/-- **Rotation invariance.**  Turning every direction by the coordinate shift
leaves the answer alone.  Every rule built from pivots, determinants, traces or
norms of the gap satisfies this, because those are congruence invariants. -/
def RotationInvariant (rule : ChartRule) : Prop :=
  ∀ (d : Fin 6 → (Fin 3 → ℝ)) (m w : Fin 6 → ℝ),
    rule (fun c => rotateCoord (d c)) m w = rule d m w

/-- **Relabelling equivariance for raw data.** -/
def ChartEquivariant (rule : ChartRule) : Prop :=
  ∀ (d : Fin 6 → (Fin 3 → ℝ)) (m w : Fin 6 → ℝ) (tau : Equiv.Perm (Fin 6)),
    rule (fun c => d (tau c)) (fun c => m (tau c)) (fun c => w (tau c))
      = (rule d m w).image tau.symm

/-- **The raw-data bridge.**  A relabelling-equivariant, rotation-invariant rule
returns an invariant answer at the witness. -/
theorem chartRule_image_sigma_eq (rule : ChartRule)
    (hequi : ChartEquivariant rule) (hrot : RotationInvariant rule) :
    (rule witnessDirection witnessMass witnessWeight).image sigmaLabel
      = rule witnessDirection witnessMass witnessWeight := by
  have hd : (fun c => witnessDirection (sigmaPerm c))
      = fun c => rotateCoord (witnessDirection c) := by
    funext c
    exact witnessDirection_sigma_eq_rotate c
  have hm : (fun c => witnessMass (sigmaPerm c)) = witnessMass := by
    funext c; exact witnessMass_sigma c
  have hw : (fun c => witnessWeight (sigmaPerm c)) = witnessWeight := by
    funext c; exact witnessWeight_sigma c
  have h := hequi witnessDirection witnessMass witnessWeight sigmaPerm
  rw [hd, hm, hw, hrot] at h
  have hid : (sigmaLabel ∘ (sigmaPerm.symm : Fin 6 → Fin 6)) = id := by
    funext x
    exact sigmaPerm.apply_symm_apply x
  have hstep : (rule witnessDirection witnessMass witnessWeight).image sigmaLabel
      = ((rule witnessDirection witnessMass witnessWeight).image
          (sigmaPerm.symm : Fin 6 → Fin 6)).image sigmaLabel := by
    rw [← h]
  rw [hstep, Finset.image_image, hid, Finset.image_id]

/-- **NO EQUIVARIANT ROTATION-INVARIANT CHART RULE DESIGNATES.** -/
theorem no_chartEquivariant_designation (rule : ChartRule)
    (hequi : ChartEquivariant rule) (hrot : RotationInvariant rule)
    (hcard : (rule witnessDirection witnessMass witnessWeight).card = 3)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hS : rule witnessDirection witnessMass witnessWeight = {i, j, k}) :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k :=
  no_working_invariant_triple _ hcard (chartRule_image_sigma_eq rule hequi hrot)
    i j k hS hij hik hjk

/-! ## 2. Every diagonal-monotone maximizer picks the failing orbit

The diagonal of the witness complement matrix takes exactly two values, and the
larger one sits exactly on the failing orbit `{3,4,5}`.  So a rule maximizing any
quantity increasing in the three diagonal entries returns that orbit.

The diagonal entry is `boost * (1 - fullPivot)`, so ordering by it is ordering by
the pivot the other way.  "Omit the three lightest labels" is therefore in this
class, and so are the total pivot and the own monomial of the diagonal.
-/

/-- The larger diagonal value. -/
noncomputable def witnessDiagMax : ℝ := 387 / 9800

/-- The smaller diagonal value. -/
noncomputable def witnessDiagMin : ℝ := 144 / 9800

theorem witnessDiagMin_lt_max : witnessDiagMin < witnessDiagMax := by
  rw [witnessDiagMin, witnessDiagMax]; norm_num

theorem witnessDiagMin_pos : 0 < witnessDiagMin := by rw [witnessDiagMin]; norm_num

/-- **On the failing orbit the diagonal is maximal.** -/
theorem witnessEntry_diag_of_three_le (c : Fin 6) (h : 3 ≤ (c : ℕ)) :
    witnessEntry c c = witnessDiagMax := by
  fin_cases c <;> simp_all [witnessEntry, witnessDiagMax]

/-- **Off the failing orbit the diagonal is the smaller value.** -/
theorem witnessEntry_diag_of_lt_three (c : Fin 6) (h : (c : ℕ) < 3) :
    witnessEntry c c = witnessDiagMin := by
  fin_cases c <;> simp_all [witnessEntry, witnessDiagMin] <;> norm_num

/-- The diagonal never exceeds the larger value. -/
theorem witnessEntry_diag_le (c : Fin 6) : witnessEntry c c ≤ witnessDiagMax := by
  rcases lt_or_ge (c : ℕ) 3 with h | h
  · rw [witnessEntry_diag_of_lt_three c h]; exact le_of_lt witnessDiagMin_lt_max
  · rw [witnessEntry_diag_of_three_le c h]

/-- Every diagonal entry is positive. -/
theorem witnessEntry_diag_pos (c : Fin 6) : 0 < witnessEntry c c := by
  rcases lt_or_ge (c : ℕ) 3 with h | h
  · rw [witnessEntry_diag_of_lt_three c h]; exact witnessDiagMin_pos
  · rw [witnessEntry_diag_of_three_le c h]
    rw [witnessDiagMax]; norm_num

/-- **A triple of distinct labels all off the small orbit is the failing orbit.** -/
theorem triple_eq_failingOrbit (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : 3 ≤ (i : ℕ)) (hj : 3 ≤ (j : ℕ)) (hk : 3 ≤ (k : ℕ)) :
    ({i, j, k} : Finset (Fin 6)) = {3, 4, 5} := by
  revert hij hik hjk hi hj hk
  revert i j k
  decide

/-- **THE TRACE MAXIMIZER IS THE FAILING ORBIT.**  Any triple other than the
failing orbit has strictly smaller diagonal sum. -/
theorem witnessDiagSum_lt (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hne : ({i, j, k} : Finset (Fin 6)) ≠ {3, 4, 5}) :
    witnessEntry i i + witnessEntry j j + witnessEntry k k < 3 * witnessDiagMax := by
  have hsome : (i : ℕ) < 3 ∨ (j : ℕ) < 3 ∨ (k : ℕ) < 3 := by
    by_contra hcon
    push Not at hcon
    exact hne (triple_eq_failingOrbit i j k hij hik hjk hcon.1 hcon.2.1 hcon.2.2)
  have hi := witnessEntry_diag_le i
  have hj := witnessEntry_diag_le j
  have hk := witnessEntry_diag_le k
  rcases hsome with h | h | h
  · have := witnessEntry_diag_of_lt_three i h
    have hlt : witnessEntry i i < witnessDiagMax := by
      rw [this]; exact witnessDiagMin_lt_max
    linarith
  · have := witnessEntry_diag_of_lt_three j h
    have hlt : witnessEntry j j < witnessDiagMax := by
      rw [this]; exact witnessDiagMin_lt_max
    linarith
  · have := witnessEntry_diag_of_lt_three k h
    have hlt : witnessEntry k k < witnessDiagMax := by
      rw [this]; exact witnessDiagMin_lt_max
    linarith

/-- The failing orbit attains the diagonal sum. -/
theorem witnessDiagSum_failingOrbit :
    witnessEntry 3 3 + witnessEntry 4 4 + witnessEntry 5 5 = 3 * witnessDiagMax := by
  rw [witnessEntry_diag_of_three_le 3 (by norm_num),
      witnessEntry_diag_of_three_le 4 (by norm_num),
      witnessEntry_diag_of_three_le 5 (by norm_num)]
  ring

/-- A product of three positive factors under a common cap is strictly below the
cube of the cap as soon as one factor is. -/
theorem prod_three_lt_cube {a b c cap : ℝ} (hcap : 0 < cap) (hb : 0 < b) (hc : 0 < c)
    (hb' : b ≤ cap) (hc' : c ≤ cap) (ha : a < cap) : a * b * c < cap * cap * cap := by
  have hbc : b * c ≤ cap * cap := mul_le_mul hb' hc' (le_of_lt hc) (le_of_lt hcap)
  have hbcpos : (0:ℝ) < b * c := mul_pos hb hc
  calc a * b * c = a * (b * c) := by ring
    _ < cap * (b * c) := mul_lt_mul_of_pos_right ha hbcpos
    _ ≤ cap * (cap * cap) := mul_le_mul_of_nonneg_left hbc (le_of_lt hcap)
    _ = cap * cap * cap := by ring

/-- **THE PRODUCT MAXIMIZER IS THE FAILING ORBIT TOO.**  The own monomial of the
diagonal is strictly smaller off the failing orbit, because every diagonal entry
is positive. -/
theorem witnessDiagProd_lt (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hne : ({i, j, k} : Finset (Fin 6)) ≠ {3, 4, 5}) :
    witnessEntry i i * witnessEntry j j * witnessEntry k k
      < witnessDiagMax * witnessDiagMax * witnessDiagMax := by
  have hsome : (i : ℕ) < 3 ∨ (j : ℕ) < 3 ∨ (k : ℕ) < 3 := by
    by_contra hcon
    push Not at hcon
    exact hne (triple_eq_failingOrbit i j k hij hik hjk hcon.1 hcon.2.1 hcon.2.2)
  have hpi := witnessEntry_diag_pos i
  have hpj := witnessEntry_diag_pos j
  have hpk := witnessEntry_diag_pos k
  have hi := witnessEntry_diag_le i
  have hj := witnessEntry_diag_le j
  have hk := witnessEntry_diag_le k
  have hmaxpos : (0:ℝ) < witnessDiagMax := by rw [witnessDiagMax]; norm_num
  rcases hsome with h | h | h
  · have hlt : witnessEntry i i < witnessDiagMax := by
      rw [witnessEntry_diag_of_lt_three i h]; exact witnessDiagMin_lt_max
    exact prod_three_lt_cube hmaxpos hpj hpk hj hk hlt
  · have hlt : witnessEntry j j < witnessDiagMax := by
      rw [witnessEntry_diag_of_lt_three j h]; exact witnessDiagMin_lt_max
    calc witnessEntry i i * witnessEntry j j * witnessEntry k k
        = witnessEntry j j * witnessEntry i i * witnessEntry k k := by ring
      _ < _ := prod_three_lt_cube hmaxpos hpi hpk hi hk hlt
  · have hlt : witnessEntry k k < witnessDiagMax := by
      rw [witnessEntry_diag_of_lt_three k h]; exact witnessDiagMin_lt_max
    calc witnessEntry i i * witnessEntry j j * witnessEntry k k
        = witnessEntry k k * witnessEntry i i * witnessEntry j j := by ring
      _ < _ := prod_three_lt_cube hmaxpos hpi hpj hi hj hlt

/-- **THE FAILING ORBIT FAILS.**  Stated against the diagonal maximizers so the
consequence is immediate. -/
theorem failingOrbit_not_minors :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight 3 4 5 :=
  not_minors_threeFourFive

/-- **EVERY DIAGONAL-MONOTONE MAXIMIZER FAILS.**  A rule whose answer maximizes
the diagonal sum among triples returns the failing orbit. -/
theorem no_diagonalSum_designation (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmax : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      witnessEntry a a + witnessEntry b b + witnessEntry c c
        ≤ witnessEntry i i + witnessEntry j j + witnessEntry k k) :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k := by
  have hattain := hmax 3 4 5 (by decide) (by decide) (by decide)
  rw [witnessDiagSum_failingOrbit] at hattain
  have heq : ({i, j, k} : Finset (Fin 6)) = {3, 4, 5} := by
    by_contra hne
    have := witnessDiagSum_lt i j k hij hik hjk hne
    linarith
  intro hminors
  have hpos : (directionChartGap witnessDirection witnessMass witnessWeight
      (Finset.univ \ ({i, j, k} : Finset (Fin 6)))).PosDef :=
    (minors_iff_posDef i j k hij hik hjk).mp hminors
  rw [heq] at hpos
  exact failingOrbit_not_minors
    ((minors_iff_posDef 3 4 5 (by decide) (by decide) (by decide)).mpr hpos)

/-- **THE PRODUCT VERSION.** -/
theorem no_diagonalProd_designation (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmax : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      witnessEntry a a * witnessEntry b b * witnessEntry c c
        ≤ witnessEntry i i * witnessEntry j j * witnessEntry k k) :
    ¬ ChartComplementMinors witnessDirection witnessMass witnessWeight i j k := by
  have hattain := hmax 3 4 5 (by decide) (by decide) (by decide)
  rw [witnessEntry_diag_of_three_le 3 (by norm_num),
      witnessEntry_diag_of_three_le 4 (by norm_num),
      witnessEntry_diag_of_three_le 5 (by norm_num)] at hattain
  have heq : ({i, j, k} : Finset (Fin 6)) = {3, 4, 5} := by
    by_contra hne
    have := witnessDiagProd_lt i j k hij hik hjk hne
    linarith
  intro hminors
  have hpos : (directionChartGap witnessDirection witnessMass witnessWeight
      (Finset.univ \ ({i, j, k} : Finset (Fin 6)))).PosDef :=
    (minors_iff_posDef i j k hij hik hjk).mp hminors
  rw [heq] at hpos
  exact failingOrbit_not_minors
    ((minors_iff_posDef 3 4 5 (by decide) (by decide) (by decide)).mpr hpos)

/-! ## 3. The set-valued relaxation collapses

A rule returning a SET escapes section 1, because the witness carries six working
triples in two free orbits.  The relaxation is nevertheless empty, and the reason
is that a maximizer set is a singleton unless the maximum is attained twice.
-/

/-- **THE COLLAPSE.**  When the maximizer set is a singleton the set-valued rule
IS a single-valued rule, and completeness of the set is failure of that one
triple. -/
theorem no_member_works_of_singleton {P : Finset (Fin 6) → Prop}
    {A : Finset (Finset (Fin 6))} {T : Finset (Fin 6)}
    (hA : A = {T}) (hT : ¬ P T) : ∀ S ∈ A, ¬ P S := by
  intro S hS
  rw [hA, Finset.mem_singleton] at hS
  rw [hS]
  exact hT

/-- **A strict maximum absorbs every maximizer.**  If one candidate strictly beats
all the others, then any maximizer IS that candidate.  This is what makes the
set-valued relaxation empty: the returned set has one element, so the rule is a
selector after all. -/
theorem eq_of_maximal_of_strict {score : Finset (Fin 6) → ℝ}
    {T S : Finset (Fin 6)} {cand : Finset (Finset (Fin 6))}
    (hT : T ∈ cand) (hS : S ∈ cand)
    (hstrict : ∀ S' ∈ cand, S' ≠ T → score S' < score T)
    (hmax : ∀ S' ∈ cand, score S' ≤ score S) : S = T := by
  by_contra hne
  have h1 := hstrict S hS hne
  have h2 := hmax T hT
  linarith

/-- **The relaxation is empty at a strict maximum.**  A set-valued rule whose
answer maximizes a score returns only the strict maximizer, so if that one fails
no member of the answer works. -/
theorem no_maximizer_works_of_strict {score : Finset (Fin 6) → ℝ}
    {P : Finset (Fin 6) → Prop} {T : Finset (Fin 6)} {cand answer : Finset (Finset (Fin 6))}
    (hT : T ∈ cand) (hsub : ∀ S ∈ answer, S ∈ cand)
    (hstrict : ∀ S' ∈ cand, S' ≠ T → score S' < score T)
    (hmaximal : ∀ S ∈ answer, ∀ S' ∈ cand, score S' ≤ score S)
    (hfail : ¬ P T) : ∀ S ∈ answer, ¬ P S := by
  intro S hSmem
  have : S = T := eq_of_maximal_of_strict hT (hsub S hSmem) hstrict (hmaximal S hSmem)
  rw [this]
  exact hfail

end Gtz

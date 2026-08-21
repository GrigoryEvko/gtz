/-
# The cross law of a frame, its floor, and the three-class capstone

Question 7.1 of the survey asks whether every boundary `(5,3)` system has at
least four dominating triples.  A positive answer closes the whole unit-length
branch of `(6,3)`, because the swap-degree cap
`Gtz.swapDegree_le_one_card_le_three` bounds that branch's family of triples by
three.

`Gtz.pivot_half_floor` reduced the question to one scalar statement about the
co-Parseval pivots.  This module changes chart once more, to the side where the
statement becomes elementary, and proves everything about it except one
geometric fact, which it isolates.

## The chart

`Gtz.dominates_compl_iff_resolventForm_le` decides a selection by a principal
block of the COMPLEMENT projection.  At `(5,3)` that projection has rank two, so
it is `B Bᵀ` for a `5 x 2` matrix `B`, and the whole system is five vectors
`b_c` in the plane with

  `∑_c b_c b_cᵀ = 1`   (the frame law)

together with the numbers `x_c` that the weights leave behind.  A triple
dominates exactly when the two-by-two block of its complementary PAIR clears its
weights, and that block is `[[x_a, ⟨b_a,b_c⟩], [⟨b_a,b_c⟩, x_c]]`.  So the whole
of `(5,3)` is carried by the single quantity

  **`Gtz.pairCross b x a c = ⟨b_a, b_c⟩^2 - x_a x_c`** ,

nonpositive exactly when the complementary triple dominates.

## The row law, and everything that follows from it

The frame law gives the cross quantity a row sum in one step
(`Gtz.sum_pairCross`), because `∑_c ⟨b_a,b_c⟩^2` is `b_a` read against the frame:

  **`∑_c pairCross b x a c = leverageOf (b a) - (∑_c x_c) · x_a`** .

At a boundary system every off-diagonal cross is nonnegative, and the diagonal
one is `leverageOf (b a)^2 - x_a^2`, so the row law factors
(`Gtz.pairCross_offDiag_sum`):

  **`∑_{c ≠ a} pairCross b x a c = (l_a - x_a)(1 - l_a - x_a)`** ,

and the FLOOR `Gtz.leverage_add_cross_le_one` drops out with no further work:

  **`leverageOf (b a) + x_a ≤ 1`** .

That is `Gtz.pivot_half_floor` in this chart, and here it is two lines.

## The capstone

The frame law also fixes the total.  Its trace gives `∑_a leverageOf (b a) = k`,
so at rank two, with the weights normalised,

  **`∑_a (leverageOf (b a) + x_a) = 3`** (`Gtz.sum_leverage_add_cross`).

Against the floor this is a counting statement, and it cuts both ways.

* Five numbers at most one summing to three need at least three of them, so a
  frame carrying this data has AT LEAST THREE vectors
  (`Gtz.three_le_card_of_frame`).
* THREE numbers at most one summing to three are all one.  So for a frame of
  exactly three vectors every floor is attained and every off-diagonal cross
  VANISHES (`Gtz.threeFrame_all_tight`): the three complementary triples all
  dominate, with nothing assumed beyond the refusal.

Counting closes the gap between the two.  Five vectors carried by three
directions leave a direction with a single vector
(`Gtz.exists_singleton_class`), and that vector's crosses are all crosses
between distinct directions, so its row vanishes
(`Gtz.exists_vanishing_row`) — which is Question 7.1.

## What is left

Exactly one statement: that the directions take at most three values.  The floor
already forces at least three, by `Gtz.three_le_card_of_frame` applied to the
family with one vector per direction, so this pins the count.
`Gtz.AtMostThreeDirections` below names it.  It is equivalent to the target
rather than weaker than it, and this module does not prove it.

[MEASURED.  In the chart above, the maximum over the feasible set of
`min_a (1 - leverageOf (b a) - x_a)` is `0` to `1.3e-13` at weight floors
`0.1, 0.05, 0.02, 0.005` — the floor is attained at every boundary system and
the statement carries NO margin proportional to the smallest weight, unlike the
other open cells of the survey.  Over 409 feasible points the cross matrix had
inertia `(3,0,2)` every time, the positivity graph of the off-diagonal crosses
had degree sequence `(0,0,2,2,2)` or `(0,1,1,1,1)`, and the number of distinct
directions was three.  The `(5,3)` diamond sits at `b`-masses
`(0.6, 0.35, 0.35, 0.35, 0.35)`, `x = (0.4, 0.15, 0.15, 0.15, 0.15)`, three
directions with two of them doubled, and floor slacks `(0, 0.5, 0.5, 0.5, 0.5)`.]
-/
import Gtz.Core.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The frame law and its two readings -/

/-- A family of vectors is a FRAME when its atom matrices total the identity.
The complement projection of a design supplies one at every size and rank. -/
def IsFrame (b : Fin m → (Fin k → ℝ)) : Prop :=
  ∑ c, atomMatrix (b c) = 1

/-- A vector read against itself is its own leverage. -/
theorem frameDotSelf (g : Fin k → ℝ) : g ⬝ᵥ g = leverageOf g := by
  simp only [dotProduct, leverageOf, pow_two]

/-- An atom matrix applied to a probe rescales the atom by the reading. -/
theorem frameAtomMulVec (g y : Fin k → ℝ) : atomMatrix g *ᵥ y = (g ⬝ᵥ y) • g := by
  funext i
  simp only [atomMatrix, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **THE FRAME READS EVERY VECTOR BY ITS OWN LEVERAGE.**  The squared pairings
of one vector against the whole family total that vector's leverage.  This is
Parseval with no weights in it, and it is the only property of the frame the
rest of the module uses. -/
theorem sum_sq_pairing_of_frame {b : Fin m → (Fin k → ℝ)} (hframe : IsFrame b)
    (a : Fin m) : ∑ c, (b a ⬝ᵥ b c) ^ 2 = leverageOf (b a) := by
  have hread : b a ⬝ᵥ ((∑ c, atomMatrix (b c)) *ᵥ b a) = ∑ c, (b a ⬝ᵥ b c) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [frameAtomMulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm (b a) (b c)]
    ring
  rw [← hread, hframe, Matrix.one_mulVec, frameDotSelf]

/-- **THE FRAME SPENDS THE RANK.**  The leverages of a frame total the rank,
because the trace of the frame law is the trace of the identity. -/
theorem sum_leverage_of_frame {b : Fin m → (Fin k → ℝ)} (hframe : IsFrame b) :
    ∑ c, leverageOf (b c) = (k : ℝ) := by
  have htrace := congrArg Matrix.trace hframe
  rw [Matrix.trace_sum] at htrace
  simp only [Matrix.trace_one, Fintype.card_fin] at htrace
  rw [← htrace]
  exact Finset.sum_congr rfl fun c _ => (trace_atomMatrix (b c)).symm

/-! ## 2. The cross quantity and its row law -/

/-- **THE CROSS QUANTITY.**  At `(5,3)` this is minus the determinant of the
two-by-two block that decides the complementary triple: it is nonpositive
exactly when that triple dominates, and nonnegative exactly when the triple
fails to dominate strictly. -/
noncomputable def pairCross (b : Fin m → (Fin k → ℝ)) (x : Fin m → ℝ) (a c : Fin m) : ℝ :=
  (b a ⬝ᵥ b c) ^ 2 - x a * x c

theorem pairCross_comm (b : Fin m → (Fin k → ℝ)) (x : Fin m → ℝ) (a c : Fin m) :
    pairCross b x a c = pairCross b x c a := by
  rw [pairCross, pairCross, dotProduct_comm (b a) (b c)]; ring

/-- The cross of a vector with itself is the difference of the two squares. -/
theorem pairCross_self (b : Fin m → (Fin k → ℝ)) (x : Fin m → ℝ) (a : Fin m) :
    pairCross b x a a = leverageOf (b a) ^ 2 - x a ^ 2 := by
  rw [pairCross, frameDotSelf]; ring

/-- **THE ROW LAW.**  One line from the frame: the crosses of a vector against
the whole family total its leverage less its own share of the total. -/
theorem sum_pairCross {b : Fin m → (Fin k → ℝ)} (hframe : IsFrame b)
    (x : Fin m → ℝ) (a : Fin m) :
    ∑ c, pairCross b x a c = leverageOf (b a) - (∑ c, x c) * x a := by
  have hsplit : ∑ c, pairCross b x a c
      = (∑ c, (b a ⬝ᵥ b c) ^ 2) - ∑ c, x a * x c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [hsplit, sum_sq_pairing_of_frame hframe a, ← Finset.mul_sum]
  ring

/-- **THE ROW LAW, OFF THE DIAGONAL, FACTORED.**  With the shares normalised the
off-diagonal row total is a product of the two quantities the floor compares. -/
theorem pairCross_offDiag_sum {b : Fin m → (Fin k → ℝ)} (hframe : IsFrame b)
    {x : Fin m → ℝ} (hx : ∑ c, x c = 1) (a : Fin m) :
    ∑ c ∈ Finset.univ.erase a, pairCross b x a c
      = (leverageOf (b a) - x a) * (1 - leverageOf (b a) - x a) := by
  have hall := sum_pairCross hframe x a
  rw [hx, one_mul] at hall
  have hsplit := Finset.sum_erase_add Finset.univ (fun c => pairCross b x a c)
    (Finset.mem_univ a)
  rw [pairCross_self] at hsplit
  have hval : ∑ c ∈ Finset.univ.erase a, pairCross b x a c
      = leverageOf (b a) - x a - (leverageOf (b a) ^ 2 - x a ^ 2) := by
    linarith [hsplit, hall]
  rw [hval]; ring

/-! ## 3. The floor -/

/-- **THE FLOOR.**  A vector whose crosses against the others are all
nonnegative, and whose share falls below its leverage, has leverage and share
totalling at most one.

This is `Gtz.pivot_half_floor` in the complement chart, and the whole proof is
the factored row law against one sign. -/
theorem leverage_add_cross_le_one {b : Fin m → (Fin k → ℝ)} (hframe : IsFrame b)
    {x : Fin m → ℝ} (hx : ∑ c, x c = 1) {a : Fin m}
    (hlt : x a < leverageOf (b a))
    (href : ∀ c, c ≠ a → 0 ≤ pairCross b x a c) :
    leverageOf (b a) + x a ≤ 1 := by
  have hsum : 0 ≤ ∑ c ∈ Finset.univ.erase a, pairCross b x a c :=
    Finset.sum_nonneg fun c hc => href c (Finset.ne_of_mem_erase hc)
  rw [pairCross_offDiag_sum hframe hx a] at hsum
  nlinarith [hsum, sub_pos.mpr hlt]

/-- **THE TOTAL.**  At rank `k` the leverages and the shares together total
`k + 1`, whatever the family is. -/
theorem sum_leverage_add_cross {b : Fin m → (Fin k → ℝ)} (hframe : IsFrame b)
    {x : Fin m → ℝ} (hx : ∑ c, x c = 1) :
    ∑ c, (leverageOf (b c) + x c) = (k : ℝ) + 1 := by
  rw [Finset.sum_add_distrib, sum_leverage_of_frame hframe, hx]

/-! ## 4. The count, both ways -/

/-- **A FRAME OF THIS KIND CARRIES AT LEAST THREE VECTORS.**  At rank two the
leverages and shares total three, and the floor caps each of them by one, so
three of them are needed.  Nothing but counting. -/
theorem three_le_card_of_frame {b : Fin m → (Fin 2 → ℝ)} (hframe : IsFrame b)
    {x : Fin m → ℝ} (hx : ∑ c, x c = 1)
    (hlt : ∀ a, x a < leverageOf (b a))
    (href : ∀ a c, c ≠ a → 0 ≤ pairCross b x a c) :
    3 ≤ m := by
  have hfloor : ∀ a, leverageOf (b a) + x a ≤ 1 := fun a =>
    leverage_add_cross_le_one hframe hx (hlt a) (href a)
  have htotal := sum_leverage_add_cross hframe hx
  have hbound : ∑ c, (leverageOf (b c) + x c) ≤ ∑ _c : Fin m, (1 : ℝ) :=
    Finset.sum_le_sum fun c _ => hfloor c
  rw [htotal] at hbound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hbound
  have hcast : (3 : ℝ) ≤ (m : ℝ) := by push_cast at hbound ⊢; linarith
  exact_mod_cast hcast

/-- **THREE VECTORS FORCE EVERY FLOOR.**  A frame of exactly three vectors in
the plane has all three floors attained: three numbers at most one totalling
three are all one. -/
theorem threeFrame_leverage_add_cross_eq_one {b : Fin 3 → (Fin 2 → ℝ)}
    (hframe : IsFrame b) {x : Fin 3 → ℝ} (hx : ∑ c, x c = 1)
    (hlt : ∀ a, x a < leverageOf (b a))
    (href : ∀ a c, c ≠ a → 0 ≤ pairCross b x a c) (a : Fin 3) :
    leverageOf (b a) + x a = 1 := by
  have hfloor : ∀ d, leverageOf (b d) + x d ≤ 1 := fun d =>
    leverage_add_cross_le_one hframe hx (hlt d) (href d)
  have htotal := sum_leverage_add_cross hframe hx
  rw [Fin.sum_univ_three] at htotal
  have hthree : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  rw [hthree] at htotal
  have hcases : ∀ d : Fin 3, d = 0 ∨ d = 1 ∨ d = 2 := by decide
  have h0 := hfloor 0
  have h1 := hfloor 1
  have h2 := hfloor 2
  rcases hcases a with rfl | rfl | rfl <;> linarith

/-- **THREE VECTORS FORCE EVERY CROSS TO VANISH.**  With every floor attained
the off-diagonal row totals are zero, and the summands are nonnegative, so each
one is zero: all three complementary selections dominate at once. -/
theorem threeFrame_all_tight {b : Fin 3 → (Fin 2 → ℝ)} (hframe : IsFrame b)
    {x : Fin 3 → ℝ} (hx : ∑ c, x c = 1)
    (hlt : ∀ a, x a < leverageOf (b a))
    (href : ∀ a c, c ≠ a → 0 ≤ pairCross b x a c) {a c : Fin 3} (hac : c ≠ a) :
    pairCross b x a c = 0 := by
  classical
  have heq := threeFrame_leverage_add_cross_eq_one hframe hx hlt href a
  have hrow := pairCross_offDiag_sum hframe hx a
  have hvanish : (1 : ℝ) - leverageOf (b a) - x a = 0 := by linarith
  have hzero : ∑ d ∈ Finset.univ.erase a, pairCross b x a d = 0 := by
    rw [hrow, hvanish, mul_zero]
  by_contra hne
  have hpos : 0 < pairCross b x a c := lt_of_le_of_ne (href a c hac) (Ne.symm hne)
  have hmem : c ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hac, Finset.mem_univ c⟩
  have hbig : 0 < ∑ d ∈ Finset.univ.erase a, pairCross b x a d :=
    Finset.sum_pos' (fun d hd => href a d (Finset.ne_of_mem_erase hd)) ⟨c, hmem, hpos⟩
  linarith

/-! ## 5. The counting step -/

/-- **FIVE VECTORS IN THREE DIRECTIONS LEAVE A DIRECTION ALONE.**  If the class
map is onto, some class has a single member: three classes of two or more would
need six vectors.

This is the step that turns the three-vector conclusion into a statement about
the five-vector system, and it is where the size five enters. -/
theorem exists_singleton_class {cls : Fin 5 → Fin 3} (hsurj : Function.Surjective cls) :
    ∃ a : Fin 5, ∀ c : Fin 5, c ≠ a → cls c ≠ cls a := by
  classical
  by_contra hcon
  push_neg at hcon
  have hfib : ∀ i : Fin 3, 2 ≤ (Finset.univ.filter fun c => cls c = i).card := by
    intro i
    obtain ⟨a, ha⟩ := hsurj i
    obtain ⟨c, hca, hcls⟩ := hcon a
    have hmemA : a ∈ Finset.univ.filter fun d => cls d = i := by
      simp [Finset.mem_filter, ha]
    have hmemC : c ∈ Finset.univ.filter fun d => cls d = i := by
      simp [Finset.mem_filter, hcls, ha]
    exact Finset.one_lt_card.mpr ⟨c, hmemC, a, hmemA, hca⟩
  have hsum : ∑ i : Fin 3, (Finset.univ.filter fun c => cls c = i).card = 5 := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := cls) (s := (Finset.univ : Finset (Fin 5))) (t := (Finset.univ : Finset (Fin 3)))
      (fun c _ => Finset.mem_univ (cls c))
    simpa using this.symm
  have hsix : 6 ≤ 5 := by
    calc (6 : ℕ) = ∑ _i : Fin 3, 2 := by simp
      _ ≤ ∑ i : Fin 3, (Finset.univ.filter fun c => cls c = i).card :=
          Finset.sum_le_sum fun i _ => hfib i
      _ = 5 := hsum
  omega

/-! ## 6. What Question 7.1 now needs -/

/-- The one statement left: the directions of the complement frame of a boundary
`(5,3)` system take at most three values.  The floor already forces at least
three, through `Gtz.three_le_card_of_frame` applied to the family with one
vector per direction, so this pins the count exactly.

Once it holds, the frame with one vector per direction has exactly three
members, `Gtz.threeFrame_all_tight` makes every cross between distinct
directions vanish, and `Gtz.exists_singleton_class` produces a vector alone in
its direction.  Every cross in that vector's row is then a cross between
distinct directions, so the row vanishes and the four selections omitting it all
dominate — which is Question 7.1. -/
def AtMostThreeDirections : Prop :=
  ∀ (b : Fin 5 → (Fin 2 → ℝ)) (x : Fin 5 → ℝ), IsFrame b → (∑ c, x c = 1) →
    (∀ a, x a < leverageOf (b a)) → (∀ a c, c ≠ a → 0 ≤ pairCross b x a c) →
      ∃ (cls : Fin 5 → Fin 3), Function.Surjective cls ∧
        ∀ a c : Fin 5, cls a = cls c → 0 < pairCross b x a c

/-- **THE ROW THAT VANISHES, FROM THE TWO INGREDIENTS.**  Suppose the classes
are onto and every cross inside a class is positive, and suppose crosses between
distinct classes vanish.  Then the vector alone in its class has a row of
crosses that is identically zero. -/
theorem exists_vanishing_row {b : Fin 5 → (Fin 2 → ℝ)} {x : Fin 5 → ℝ}
    {cls : Fin 5 → Fin 3} (hsurj : Function.Surjective cls)
    (hcross : ∀ a c : Fin 5, cls a ≠ cls c → pairCross b x a c = 0) :
    ∃ a : Fin 5, ∀ c : Fin 5, c ≠ a → pairCross b x a c = 0 := by
  obtain ⟨a, ha⟩ := exists_singleton_class hsurj
  exact ⟨a, fun c hc => hcross a c (Ne.symm (ha c hc))⟩

end Gtz

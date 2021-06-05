--> check the documentation tab
-- tutorial exercises
import algebra.group
import algebra.ordered_ring
import algebra.ring
import analysis.special_functions.exp_log
import data.nat.gcd
import data.real.basic
import order.lattice
import tactic
import topology.metric_space.basic

section basics_2_1

#check mul_comm
#check mul_assoc

variables a b c d e f : ℝ

example : (c * b) * a = b * (a * c) :=
begin
  rw mul_assoc,
  rw mul_comm,
  rw mul_assoc,
end

example : a * (b * c) = b * (a * c) :=
begin
  rw mul_comm,
  rw mul_assoc,
  rw mul_comm a,
end

example (h : b * c = e * f ) : a * b * c * d = a * e * f * d :=
begin
  rw mul_assoc a b c,
  rw mul_assoc a e f,
  rw h,
end

#check sub_self

example (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw mul_comm at hyp,
  rw hyp' at hyp,
  rw sub_self at hyp,
  assumption
end

#check mul_add
#check add_mul
#check two_mul

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) : by
          rw [ add_mul, mul_add, mul_comm a b, mul_add ]
  ... = a * a + (b * a + a * b) + b * b : by
          rw [ add_assoc,  ←add_assoc (b*a), add_assoc (a*a) ]
  ... = a * a + 2 * (a * b) + b * b     : by
          rw [ mul_comm b, ←two_mul ]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * (c + d) + b * (c + d) : by rw add_mul
  ... = a*c + a*d + b*c + b*d : by rw [ mul_add, mul_add, ←add_assoc ]

#check pow_two a
#check mul_sub a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

example : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = (a + b) * a - (a + b) * b : by { rw mul_sub, }
  ... = a * a + a * b - (a + b) * b : by { rw add_mul, rw mul_comm b }
  ... = a * a - b * b : by { rw add_mul, rw ←add_sub, rw ←sub_sub, rw sub_self, rw add_sub, rw add_zero }
  ... = a^2 - b^2 : by { rw ←pow_two, rw ←pow_two }

end basics_2_1

section basics_2_2

variables {R : Type*} [ring R]

#check add_assoc

namespace my_ring

theorem add_zero (a : R) : a + 0 = a :=
by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 :=
by rw [add_comm, add_left_neg]

#check add_neg_cancel_left

theorem add_neg_cancel_right (a b : R) : a + b + -b = a :=
by rw [ add_assoc, add_comm, add_assoc, add_neg_cancel_left ]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
calc
  b = b + 0 : by rw add_zero
  ... = b + (a + -a) : by { rw add_right_neg, }
  ... = a + b + -a : by { rw ←add_assoc, rw add_comm b a, }
  ... = a + c + -a : by { rw h }
  ... = c : by { rw add_comm a c, rw add_neg_cancel_right, }

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
begin
  rw add_comm at h,
  rw add_comm c at h,
  exact add_left_cancel h,
end

theorem zero_mul (a : R) : 0 * a = 0 :=
begin
  have : 0 * a + 0 * a = 0 + 0 * a, {
    rw ←add_mul, rw add_zero, rw zero_add,
  },
  rw add_right_cancel this,
end

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
begin
  have : a + b = a + -a, {
    rw ←add_right_neg a at h,
    exact h
  },
  rw add_left_cancel this,
end

theorem eq_neg_of_add_eq_zero {a b : ℝ} (h : a + b = 0) : a = -b :=
begin
  have : a + b = -b + b, {
    rw ←add_left_neg b at h,
    exact h,
  },
  rw add_right_cancel this,
end

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero,
end

theorem neg_neg (a : R) : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_left_neg,
end

#check sub_eq_add_neg

theorem self_sub (a : R) : a - a = 0 :=
begin
  rw sub_eq_add_neg,
  rw add_right_neg,
end

end my_ring

#check @my_ring.add_zero
#check @add_zero

namespace my_group

variables (A : Type*) [add_group A]
variables {G : Type*} [group G]

lemma mul_inv_cancel_left {a b : G} :  a⁻¹ * a * b  = b :=
begin
  rw mul_left_inv,
  rw one_mul,
end

lemma mul_left_cancel {a b c : G} : a*b = a*c → b = c :=
begin
  intro h,
  calc
      b = 1 * b        : by rw one_mul
    ... = a⁻¹ * a * b  : by rw ←mul_left_inv a
    ... = a⁻¹ * a *  c : by rw [ mul_assoc, h, ←mul_assoc ]
    ... = c            : by rw [ mul_left_inv, one_mul ]
end

lemma mul_eq_left {a b : G} : a = b → ∀ c, c * a = c * b :=
begin
  intros h c,
  rewrite h,
end

lemma mul_eq_right {a b : G} : a = b → ∀ c, a * c = b * c :=
begin
  intros h c,
  rewrite h,
end

lemma left_inv_is_right_inv {a b c : G} : a*b = 1 → c*a = 1 → b = c :=
begin
  intros hab hac,
  rw ←one_mul (a * b) at hab,
  rw ←mul_left_inv c at hab,
  have : c⁻¹ * b = c⁻¹ * c, {
    rw mul_assoc at hab,
    rw ←mul_assoc c a b at hab,
    rw hac at hab,
    rw one_mul at hab,
    exact hab,
  },
  exact mul_left_cancel this,
end

lemma inv_of_inv {a : G} : (a⁻¹)⁻¹ = a :=
begin
  have inv_inv := mul_left_inv a⁻¹,
  have inv := mul_left_inv a,
  have := left_inv_is_right_inv inv inv_inv,
  rw ←this,
end

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  have := mul_left_inv a⁻¹,
  rw inv_of_inv at this,
  exact this,
end

theorem mul_one {a : G} : a * 1 = a :=
calc
  a * 1
      = a * a⁻¹ * a   : by rw [ ←mul_left_inv a, ←mul_assoc ]
  ... = 1 * a         : by { rw ←mul_right_inv, }
  ... = a             : by rw one_mul

#check left_inv_is_right_inv

theorem mul_inv_rev {a b : G} : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  have h_left_inv := mul_right_inv (a*b),
  have h_right_inv : b⁻¹ * a⁻¹ * (a * b)  = 1, {
    rw mul_assoc,
    rw ←mul_assoc a⁻¹ a b,
    rw mul_left_inv,
    rw one_mul,
    rw mul_left_inv,
  },
  exact left_inv_is_right_inv h_left_inv h_right_inv,
end

end my_group

end basics_2_2

section basics_2_3

open real

variables a b c d e : ℝ

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e :=
begin
  apply lt_trans, {
    exact lt_of_le_of_lt h₀ h₁,
  }, {
    exact lt_of_le_of_lt h₂ h₃,
  }
end

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add, {
    exact le_refl c,
  }, {
    apply exp_le_exp.mpr,
    apply add_le_add, {
      exact le_refl a,
    }, {
      exact h₀,
    },
  }
end

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { apply add_pos, norm_num, exact exp_pos a},
  have h₁ : 0 < 1 + exp b,
  { apply add_pos, norm_num, exact exp_pos b },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add,
  exact le_refl 1,
  apply exp_le_exp.mpr,
  exact h,
end

example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  apply sub_le_sub,
  exact le_refl c,
  apply exp_le_exp.mpr,
  exact h,
end

lemma test : 0 < 2 := by norm_num

#check le_div_iff
#check le_div_iff'

example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  apply abs_le'.mpr,
  split,
  apply (le_div_iff _).mpr,
  apply le_of_sub_nonneg,
  have : a ^ 2 + b ^ 2 - a * b * 2 = (a - b)^2, {
    ring
  },
  rw this,
  apply pow_two_nonneg,
  norm_num,
  apply (le_div_iff _).mpr,
  have : -(a * b) * 2 = -(2 * a * b), ring,
  rw this,
  apply neg_le_of_neg_le,
  apply neg_le_iff_add_nonneg.mpr,
  have sq : 2 * a * b + (a ^ 2 + b ^ 2) = (a + b)^2, {ring},
  rw sq,
  apply pow_two_nonneg,
  norm_num,
end

end basics_2_3

section basics_2_4

variables {a b c : ℝ}

example : max a b = max b a :=
begin
  apply le_antisymm,
  repeat {
    apply max_le,
    apply le_max_right,
    apply le_max_left,
  },
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm, {
    apply le_min,
    apply min_le_iff.mpr,
    apply or.inl,
    apply min_le_left,
    apply le_min,
    apply min_le_iff.mpr,
    apply or.inl,
    repeat { apply min_le_right },
  }, {
    repeat { apply le_min },
    apply min_le_left,
    apply min_le_iff.mpr,
    apply or.inr,
    apply min_le_left,
    apply min_le_iff.mpr,
    apply or.inr,
    apply min_le_right,
  }
end

lemma aux : ∀ a b c : ℝ, min a b + c ≤ min (a + c) (b + c) :=
begin
  intros a b c,
  apply le_min,
  apply add_le_add,
  apply min_le_left,
  exact le_refl c,
  apply add_le_add,
  apply min_le_right,
  exact le_refl c,
end

#check aux (a+c) (b+c) (-c)
#check add_neg_cancel_right

example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  apply aux,
  apply le_add_of_neg_add_le_right,
  rw add_comm,
  have h := aux (a+c) (b+c) (-c),
  apply le_trans h,
  have hac : (a + c + -c) = a, ring,
  have hbc : (b + c + -c) = b, ring,
  rw hac,
  rw hbc,
end

#check abs_add (a-b) b

example : abs a - abs b ≤ abs (a - b) :=
begin
  calc
    abs a - abs b
        = abs ((a - b) + b) - abs b : by { rw sub_add_cancel, }
    ... ≤ abs (a - b) + abs b - abs b : by { apply sub_le_sub_right, apply abs_add, }
    ... = abs (a - b) : by ring
end

variables m n w x y z : ℕ

example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  repeat {apply dvd_add},
  apply dvd_mul_of_dvd_right,
  apply dvd_mul_right,
  apply dvd_mul_right,
  apply dvd_trans h,
  apply dvd_mul_right,
end

open nat

example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  apply nat.dvd_gcd_iff.mpr,
  cases gcd_dvd m n,
  split, exact right, exact left,
  apply nat.dvd_gcd_iff.mpr,
  cases gcd_dvd n m,
  split, exact right, exact left,
end

end basics_2_4

section basics_2_5

variables {α : Type*} [lattice α]
variables x y z : α
variables a b c : α


#check x ⊓ y
#check inf_le_left

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  repeat {
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,
  },
end

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm, {
    apply le_inf,
    apply le_trans,
    apply inf_le_left,
    apply inf_le_left,
    apply le_inf,
    apply le_trans,
    apply inf_le_left,
    apply inf_le_right,
    apply inf_le_right,
  }, {
    apply le_inf,
    apply le_inf,
    apply inf_le_left,
    apply le_trans,
    apply inf_le_right,
    apply inf_le_left,
    apply le_trans,
    apply inf_le_right,
    apply inf_le_right,
  }
end

example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  repeat {
    apply sup_le,
    apply le_sup_right,
    apply le_sup_left,
  },
end

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm, {
    apply sup_le,
    apply sup_le,
    apply le_sup_left,
    apply le_trans,
    apply le_sup_left,
    exact z,
    apply le_sup_right,
    apply le_trans,
    apply le_sup_right,
    exact y,
    apply le_sup_right,
  }, {
    apply sup_le,
    apply le_trans,
    apply le_sup_left,
    exact y,
    apply le_sup_left,
    apply sup_le,
    apply le_trans,
    apply le_sup_right,
    exact x,
    apply le_sup_left,
    apply le_sup_right,
  },
end

example : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm, {
    apply inf_le_left,
  }, {
    apply le_inf,
    apply le_refl,
    apply le_sup_left,
  }
end

example : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm, {
    apply sup_le,
    apply le_refl,
    apply inf_le_left,
  }, {
    apply le_sup_left,
  }
end

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
begin
  have hcab := h c a b,
  have hbc : b ⊓ c = c ⊓ b, { apply inf_comm },
  apply le_antisymm, {
    rw inf_comm,
    rw hcab,
    rw inf_comm,
    rw hbc,
  }, {
    have : (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b), { apply inf_comm },
    rw this,
    rw hcab,
    rw inf_comm,
    rw hbc,
  }
end

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
begin
  have hcb : c ⊔ b = b ⊔ c, { apply sup_comm, },
  apply le_antisymm, {
    rw sup_comm,
    rw h c a b,
    rw sup_comm,
    rw hcb,
  }, {
    have : a ⊓ b ⊔ c = c ⊔ (a ⊓ b), { apply sup_comm, },
    rw this,
    rw h c a b,
    rw sup_comm,
    rw hcb,
  }
end

section ordered_ring

variables {R : Type*} [ordered_ring R]
variables u v w : R

#check add_le_add_left
#check mul_pos
#check mul_nonneg

lemma ex1 : u ≤ v → 0 ≤ v - u :=
begin
  intro huv,
  have := add_le_add_left huv (-u),
  rw add_comm at this,
  rw add_neg_self at this,
  rw add_comm at this,
  rw ←sub_eq_add_neg at this,
  exact this,
end

lemma ex2 : 0 ≤ v - u → u ≤ v :=
begin
  intro hvu,
  have := add_le_add_left hvu u,
  rw add_zero at this,
  rw add_comm at this,
  rw sub_eq_add_neg at this,
  rw add_assoc at this,
  rw neg_add_self at this,
  rw add_zero at this,
  exact this,
end

example (h : u ≤ v) (h' : 0 ≤ w) : u * w ≤ v * w :=
begin
  have hsub : 0 ≤ v - u, {
    exact ex1 u v h,
  },
  have hnn := mul_nonneg hsub h',
  rw sub_mul at hnn,
  have := ex2 (u*w) (v*w) hnn,
  exact this,
end

end ordered_ring

section metric_space

variables {X : Type*} [metric_space X]
variables p q r : X

#check dist_self p
#check dist_comm p q
#check dist_triangle p q r

example (x y : X) : 0 ≤ dist x y :=
begin
  have : 0 ≤ 2 * dist x y,
  calc
    0   = dist x x : by { rw ←dist_self x }
    ... ≤ dist x y + dist y x : by { apply dist_triangle x y x, }
    ... = dist x y + dist x y : by { rw dist_comm, }
    ... = 2 * dist x y : by ring,
  have lem : ∀ x : ℝ, 0 ≤ 2 * x → 0 ≤ x, {
    intros x Hx,
    have : x = 1/2 * (2 * x), ring,
    rw this,
    apply mul_nonneg,
    norm_num,
    exact Hx,
  },
  exact lem (dist x y) this,
end

end metric_space

end basics_2_5

section logic_3_1

lemma le_cancel_left {a b : ℝ} : a ≤ b ↔ 0 ≤ b - a :=
begin
  split,
  intro Hab,
  linarith,
  intro Hsub,
  linarith,
end

lemma le_cancel_right {a b : ℝ} : a ≤ b ↔ a - b ≤ 0 :=
begin
  split,
  intro Hab,
  linarith,
  intro Hsub,
  linarith,
end

lemma pos_mul_neg_lt_zero {a b : ℝ} : 0 < a → b ≤ 0 → a * b ≤ 0 :=
begin
  intros Ha Hb,
  have := (mul_le_mul_left Ha).mpr Hb,
  rw mul_zero at this,
  exact this,
end

lemma square_is_contraction_in_unit_interval {x : ℝ} :
  0 < x → x ≤ 1 → x^2 ≤ x
:=
begin
  intros Hx₀ Hx₁,
  rw le_cancel_right,
  have : x^2 - x = x * (x-1), by ring,
  rw this,
  apply pos_mul_neg_lt_zero,
  exact Hx₀,
  linarith,
end

lemma my_lemma : ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x*y) < ε :=
begin
  intros x y ε Hε₁ Hε₂ Hx Hy,
  calc
    abs (x * y)
        = abs x * abs y : by { apply abs_mul, }
    ... < ε * ε         : by { exact mul_lt_mul' (le_of_lt Hx) Hy (abs_nonneg _) Hε₁, }
    ... = ε^2           : by ring
    ... ≤ ε             : by { exact square_is_contraction_in_unit_interval Hε₁ Hε₂ }
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

example {a b : ℝ} {f g : ℝ → ℝ} (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  apply add_le_add,
  exact hfa x,
  exact hgb x,
end

example {f g : ℝ → ℝ} (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 :=
begin
  intro x,
  dsimp,
  apply mul_nonneg,
  exact nnf x,
  exact nng x,
end

example {a b : ℝ} {f g : ℝ → ℝ} (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
begin
  intro x,
  dsimp,
  apply mul_le_mul,
  exact hfa x,
  exact hfb x,
  exact nng x,
  exact nna,
end

lemma mul_le_cancel_left { x y z : ℝ}
  : x ≤ y → 0 ≤ z → z * x ≤ z * y :=
begin
  intros hxy hz,
  rw le_cancel_left,
  rw le_cancel_left at hxy,
  have : z * y - z * x = z * (y - x), by ring,
  rw this,
  apply mul_nonneg,
  exact hz,
  exact hxy,
end

example {c : ℝ} {f : ℝ → ℝ } (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ x y hxy, mul_le_cancel_left (mf hxy) nnc
-- begin
--   intros x y hxy,
--   dsimp,
--   apply mul_le_cancel_left,
--   exact mf hxy,
--   exact nnc,
-- end

example {f g : ℝ → ℝ} (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
λ x y hxy, mf (mg hxy)
-- begin
--   intros x y hxy,
--   dsimp,
--   apply mf,
--   apply mg,
--   exact hxy,
-- end

def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd  (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example {f g : ℝ → ℝ} (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
begin
  intro x,
  dsimp,
  rw of x,
  rw og x,
  ring,
end

example {f g : ℝ → ℝ} (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
begin
  intro x,
  dsimp,
  calc
    f x * g x = f (-x) * - g(-x) : by rw [ef, og]
    ... = - (f (-x) *  g (-x)) : by ring,
end

example {f g : ℝ → ℝ} (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
begin
  intro x,
  dsimp,
  rw og x,
  rw ef (-g (-x)),
  simp,
end


section subset

variables {α : Type*} (r s t : set α)

example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  intros hrs hst x hxr,
  have := hst (hrs hxr),
  exact this,
end

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
λ hrs hst _ hxr, hst $ hrs hxr

end subset

section set_sup

variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) : Prop := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
λ x hxs, le_trans (h x hxs) h'
-- begin
--   intros x hxs,
--   apply le_trans _ h',
--   exact h x hxs,
-- end

end set_sup

section injective

open function

-- this is probably not the proof they had in mind...
example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
  unfold injective,
  intros x y hxy,
  cases mul_eq_mul_left_iff.mp hxy with left right,
  exact left,
  exact absurd right h,
end

example {f g : ℝ → ℝ} (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) :=
λ x y hxy, injf (injg hxy)
-- begin
--   intros x y hxy,
--   apply injf,
--   apply injg,
--   exact hxy,
-- end

end injective

end logic_3_1

section logic_3_2

section has_bound

variables {f g : ℝ → ℝ}

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  intro x,
  dsimp,
  apply add_le_add,
  exact lbfa x,
  exact lbgb x,
end

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a ha,
  use (c * a),
  intro x,
  dsimp,
  apply mul_le_cancel_left,
  exact ha x,
  exact h,
end

end has_bound

section div_it

variables {a b c : ℕ}

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin
  rcases divab with ⟨ k₀, Hk₀ ⟩,
  rcases divac with ⟨ k₁, Hk₁ ⟩,
  use k₀ + k₁,
  rw Hk₀,
  rw Hk₁,
  ring,
end

end div_it

section surjective

open function

variables {f g : ℝ → ℝ}

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
λ b, ⟨ b / c, mul_div_cancel' _ h ⟩
-- begin
--   intro b,
--   use b / c,
--   dsimp,
--   apply mul_div_cancel',
--   exact h,
-- end

example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
  intro x,
  rcases surjg x with ⟨ v, Hv ⟩,
  rcases surjf v with ⟨ u, Hu ⟩,
  use u,
  dsimp,
  rw Hu,
  exact Hv,
end

end surjective

end logic_3_2

section logic_3_3

#check lt_irrefl

section bounds

variable { f : ℝ → ℝ }
variables {a b : ℝ}

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  rintro ⟨ u, Hu ⟩,
  unfold fn_lb at Hu,
  cases h u with v Hv,
  have := Hu v,
  linarith,
end

example : ¬ fn_has_ub (λ x, x) :=
begin
  rintro ⟨ N, HN ⟩,
  have := HN (N+1),
  dsimp at this,
  linarith,
end

example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  apply lt_of_not_ge,
  intro ageb,
  have problem : f a < f a,
  calc
    f a < f b : by { exact h' }
    ... ≤ f a : by { exact h ageb},
  exact lt_irrefl _ problem,
end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intro hf,
  have := hf h,
  have problem : f b < f b,
  calc
    f b < f a : by { exact h' }
    ... ≤ f b : by { exact hf h },
  exact lt_irrefl _ problem,
end

example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f, {
    intros x y hxy,
    calc
      f x = 0 : rfl
      ... ≤ 0 : by exact le_refl _
      ... = f y : rfl
  },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  -- is this really what they wanted?
  apply not_le_of_gt _ (h monof h'),
  exact 1,
  exact 0,
  norm_num,
end

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  apply le_of_not_gt,
  intro hx,
  have h' := h (x / 2) (by linarith),
  rw (le_div_iff _) at h',
  have : x * 2 ≤ x * 1,
  calc
    x * 2 ≤ x : by assumption
    ... = x * 1 : by {rw mul_one,},
  have problem : 2 ≤ 1, {
     linarith,
  },
  linarith,
  norm_num,
end

end bounds

end logic_3_3

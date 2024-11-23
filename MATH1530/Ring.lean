import Mathlib

namespace MATH1530

namespace Ring

theorem prop2_left {α : Type} [NonUnitalRing α]  {a b : α}
  : a * (-b) = -(a * b) := 
    by
      rw [←zero_add (-(a * b))]
      rw [←add_zero (a * (-b))]
      nth_rewrite 1 [Eq.symm (neg_add_cancel (a * b))]
      rw [add_comm (-(a * b)) (a * b)]
      rw [←add_assoc (a * -b) (a * b) (-(a * b))]
      apply congrArg₂ (.+.)
      · calc 
          a * (-b) + (a * b) = a * (-b + b) := by rw [left_distrib a (-b) b]
          _                  = a * 0        := by rw [neg_add_cancel b]
          _                  = 0            := by exact mul_zero a
      · rfl

theorem prop2_right {α : Type} [NonUnitalRing α]  {a b : α}
  : (-a) * (b) = -(a * b) := 
    by
      rw [←zero_add (-(a * b))]
      rw [←add_zero ((-a) * (b))]
      nth_rewrite 1 [Eq.symm (neg_add_cancel (a * b))]
      rw [add_comm (-(a * b)) (a * b)]
      rw [←add_assoc (-a * b) (a * b) (-(a * b))]

      show -a * b + a * b + -(a * b) = 0 + -(a * b)
      apply add_right_cancel_iff.mpr

      show -a * b + a * b = 0
      calc 
        (-a) * b + (a * b) = ((-a) + a) * b := by rw [right_distrib (-a) a b]
        _                  = 0 * b          := by rw [neg_add_cancel a]
        _                  = 0              := by exact zero_mul b

theorem prop3 {α : Type} [NonUnitalRing α] {a b : α}
  : (-a) * (-b) = a * b := 
    by 
      apply eq_of_sub_eq_zero
      calc 
        -a * -b - a * b = -(-a) * b - a * b    := by rw [Eq.trans prop2_left (Eq.symm prop2_right)]
        _               = -(-a) * b + -(a * b) := by rw [sub_eq_add_neg]
        _               = -(-a) * b + -a * b   := by rw [←prop2_right]
        _               = (-(-a) + -a) * b     := by rw [right_distrib]
        _               = 0 * b                := by rw [neg_add_cancel]
        _               = 0                    := by rw [zero_mul]

theorem prop4 {α : Type} [NonUnitalRing α] {a b c : α}
  : a * (b - c) = a * b - a * c :=
    calc 
      a * (b - c) = a * (b + -c)     := by rw [sub_eq_add_neg]
      _           = a * b + a * (-c) := by rw [left_distrib]
      _           = a * b + -(a * c) := by rw [prop2_left]
      _           = a * b - a * c    := by rw [←sub_eq_add_neg]


theorem unity_is_unique {α : Type} [NonUnitalRing α]
  (e₁ e₂ : α) 
  (e₁_is_unity : ∀a, a * e₁ = a ∧ e₁ * a = a)
  (e₂_is_unity : ∀a, a * e₂ = a ∧ e₂ * a = a)
  : e₁ = e₂ := 
    by
      rw [←(e₂_is_unity e₁).left]
      exact (e₁_is_unity e₂).right

theorem inverse_is_unique {α : Type} [Ring α] (a b c : α)
  (b_is_inv : a * b = 1 ∧ b * a = 1)
  (c_is_inv : a * c = 1 ∧ c * a = 1)
  : b = c :=
    by
      let ⟨ab, ba⟩ := b_is_inv
      let ⟨ac, _⟩ := c_is_inv
      rw [←one_mul b, ←one_mul c]
      rw [←ba]
      rw [mul_assoc b a b, mul_assoc b a c]
      apply congrArg₂
      · rfl
      · apply Eq.trans ab 
        exact Eq.symm ac

/-- This corresponds to Theorem 1 of Chapter 12.

Let R be a ring with unity, then Rˣ = {a ∈ R | a is a unit} is a group with
respect to · (* in Lean).

This proof looks too easy to be true, but it makes sense when you think about
it. The four requirements of a group are:
1. Closed. (by R is a ring)
2. · is assoc. (by R is a ring)
3. 1 (identity) exists. (by R is  ring)
4. (Multiplicative) inverse exists.

Only 4 we need to prove by ourselves, 1~3 are all provided by R is a ring. Then,
the proof of 4 is also trivial because that's the definition of a unit!

Lean is quite smart in this case! (o^▽^o)
-/
instance [Ring α] : Group (Units α) where
  inv_mul_cancel := inv_mul_cancel

def twostep_nonunitalsubring {α : Type} [NonUnitalRing α]
  (s : Set α)
  (s_not_empty : s.Nonempty)
  (sub_mem : ∀ a ∈ s, ∀ b ∈ s, a - b ∈ s)
  (mul_mem : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) : NonUnitalSubring α := 
    let zero_mem'' : 0 ∈ s := by
        obtain ⟨x, hx⟩ := s_not_empty
        have x_sub_x_is_0 : x - x = 0 := by exact sub_eq_zero_of_eq rfl
        rw [←x_sub_x_is_0]
        exact sub_mem x hx x hx

    let neg_mem'' : ∀x ∈ s, (-x) ∈ s := by 
        intro a a_in_s
        rw [←zero_sub a]
        exact sub_mem 0 zero_mem'' a a_in_s


    {
      carrier := s 

      zero_mem' := zero_mem''

      mul_mem' := by 
        intro a b a_in_s b_in_s
        exact mul_mem a a_in_s b b_in_s

      add_mem' := by
        intro a b a_in_s b_in_s
        rw [←neg_neg b, ←sub_eq_add_neg a (-b)]
        have neg_b_in_s : (-b) ∈ s := neg_mem'' b b_in_s
        exact sub_mem a a_in_s (-b) neg_b_in_s

      neg_mem' := by 
        intro a a_in_s
        exact neg_mem'' a a_in_s
    }

end Ring

end MATH1530

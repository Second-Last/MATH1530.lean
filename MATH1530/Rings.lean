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


end Ring

end MATH1530

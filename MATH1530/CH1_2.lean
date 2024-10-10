import Mathlib

namespace MATH1530

namespace CH1_2

theorem th4 {α : Type} [Group α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  let rhs : (b⁻¹ * a⁻¹) * (a * b) = 1 := 
    (calc (b⁻¹ * a⁻¹) * (a * b)
      _ = b⁻¹ * a⁻¹ * a * b := by rw [←mul_assoc (b⁻¹ * a⁻¹) a b]
      _ = b⁻¹ * (a⁻¹ * a) * b := by rw [mul_assoc b⁻¹ a⁻¹ a]
      _ = b⁻¹ * 1 * b := by rw [inv_mul_cancel a]
      _ = b⁻¹ * b := by rw [mul_one b⁻¹]
      _ = 1 := inv_mul_cancel b)
  inv_eq_of_mul_eq_one_left rhs

end CH1_2

end MATH1530

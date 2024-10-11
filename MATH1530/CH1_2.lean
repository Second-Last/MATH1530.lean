/- import MATH1530.Basic -/
import Mathlib

namespace MATH1530

namespace CH1_2

theorem th4 {G : Type} [Group G] (a b : G) : (a • b)⁻¹ = b⁻¹ * a⁻¹ :=
  let rhs : (b⁻¹ * a⁻¹) * (a * b) = 1 := 
    (calc (b⁻¹ * a⁻¹) * (a * b)
      _ = b⁻¹ * a⁻¹ * a * b := by rw [←mul_assoc (b⁻¹ * a⁻¹) a b]
      _ = b⁻¹ * (a⁻¹ * a) * b := by rw [mul_assoc b⁻¹ a⁻¹ a]
      _ = b⁻¹ * 1 * b := by rw [inv_mul_cancel a]
      _ = b⁻¹ * b := by rw [mul_one b⁻¹]
      _ = 1 := inv_mul_cancel b)
  inv_eq_of_mul_eq_one_left rhs

/- theorem th4 {G : Type} [Group G] (a b : G) : (a • b)⁻¹ = b⁻¹ • a⁻¹ :=  -/
/-   let lhs_op_rhs_is_e : (a • b) • (b⁻¹ • a⁻¹) = e := sorry -/
/-   inv_eq_of_mul_eq_one_left (a • b) (b⁻¹ • a⁻¹) lhs_op_rhs_is_e -/

end CH1_2

end MATH1530

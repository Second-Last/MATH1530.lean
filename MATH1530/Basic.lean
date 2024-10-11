class Group (carrier : Type) where
  op : carrier → carrier → carrier
  e : carrier
  e_right : ∀ x : carrier, op x e = x
  e_left : ∀ x : carrier, op e x = x
  op_assoc : ∀ x y z, op x (op y z) = op (op x y) z
  inv : carrier → carrier
  op_inv_left : ∀ x, op (inv x) x = e
  op_inv_right: ∀ x, op x (inv x) = e 

postfix:max "⁻¹" => Group.inv
infixl:73 " • " => Group.op

open Group 

theorem inv_eq_of_mul_eq_one_left {G : Type} [Group G] 
  (a b : G) : a • b = e → a⁻¹ = b :=  λ a_op_b_is_e =>
    let a_inv_right : a • a⁻¹ = e := op_inv_right a
    let eq : a⁻¹ • (a • a⁻¹) = a⁻¹ • (a • b) := congrArg _ <| Eq.trans a_inv_right (Eq.symm a_op_b_is_e)

    let lhs : a⁻¹ • (a • a⁻¹) = a⁻¹ := (calc a⁻¹ • (a • a⁻¹)
      _ = (a⁻¹ • a) • a⁻¹ := op_assoc _ _ _
      _ = e • a⁻¹ := by rw [op_inv_left a]
      _ = a⁻¹ := by rw [e_left a⁻¹])

    let rhs : a⁻¹ • (a • b) = b := (calc a⁻¹ • (a • b)
      _ = (a⁻¹ • a) • b := op_assoc _ _ _
      _ = e • b := by rw [op_inv_left a]
      _ = b := by rw [e_left b])

    by rw [←lhs, ←rhs]; assumption

class Subgroup (carrier : Type) (parent : Type) [Group parent] where
  is_subset : carrier → parent
  carrier_is_group : Group carrier

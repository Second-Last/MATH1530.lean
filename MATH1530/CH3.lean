/- import MATH1530.Basic -/
import Mathlib

namespace MATH1530

namespace CH3

/- theorem th1 {α : Type} {H G : Set α} [Group α] (h_is_subset : H ⊆ G) -/
/-   : H = Subgroup G <-> H = G := sorry -/

open Group

theorem th1 {G : Type*} [Group G] (H : Set G)
  : IsSubgroup H ↔ (H.Nonempty ∧ ∀ (a b : G), a ∈ H → b ∈ H → (a * b⁻¹) ∈ H) 
  := Iff.intro fwd_direction bwd_direction
  where
    bwd_direction : 
      (H.Nonempty ∧ ∀ (a b : G), a ∈ H → b ∈ H → (a * b⁻¹) ∈ H) → IsSubgroup H 
    | ⟨⟨x, x_in_h⟩, rel⟩ =>  
      let x_op_invx_in_h : x * x⁻¹ ∈ H := rel x x x_in_h x_in_h
      let one_in_h : 1 ∈ H := Eq.subst (mul_inv_cancel x) x_op_invx_in_h

      let h_is_submonoid : IsSubmonoid H := 
        { one_mem := one_in_h
          mul_mem := λ {a b} ha hb => 
            let b_inv_in_h : b⁻¹ ∈ H := Eq.subst (one_mul b⁻¹) (rel 1 b one_in_h hb)
            (inv_inv b) ▸ (rel a b⁻¹ ha b_inv_in_h)
        }

      let h_is_subgroup : IsSubgroup H := 
        { h_is_submonoid with 
          inv_mem := λ {a} ha => Eq.subst (one_mul a⁻¹) (rel 1 a one_in_h ha) }

      h_is_subgroup

    fwd_direction 
      (h_is_subgroup : IsSubgroup H) : (H.Nonempty ∧ ∀ (a b : G), a ∈ H → b ∈ H → (a * b⁻¹) ∈ H)
        := 
        let h_is_nonempty : H.Nonempty := ⟨1, h_is_subgroup.one_mem⟩
        let a_b_inv_in_h (a b : G) (ha : a ∈ H) (hb : b ∈ H) : (a * b⁻¹ ∈ H) := 
          let b_inv_in_h : b⁻¹ ∈ H := h_is_subgroup.inv_mem hb
          h_is_subgroup.mul_mem ha b_inv_in_h

        And.intro h_is_nonempty a_b_inv_in_h
    

theorem th2 {G : Type*} [Group G] (H : Set G)
  : IsSubgroup H ↔ (H.Nonempty ∧ (∀ (a b : G), a ∈ H → b ∈ H → (a * b) ∈ H) ∧ (∀ (a : G), a ∈ H → a⁻¹ ∈ H)) := 
    let cond_is_same : 
      (H.Nonempty ∧ ∀ (a b : G), a ∈ H → b ∈ H → (a * b⁻¹) ∈ H) ↔
      (H.Nonempty ∧ (∀ (a b : G), a ∈ H → b ∈ H → (a * b) ∈ H) ∧ (∀ (a : G), a ∈ H → a⁻¹ ∈ H)) := 
        let fwd_direction :
          (H.Nonempty ∧ ∀ (a b : G), a ∈ H → b ∈ H → (a * b⁻¹) ∈ H) →
          (H.Nonempty ∧ (∀ (a b : G), a ∈ H → b ∈ H → (a * b) ∈ H) ∧ (∀ (a : G), a ∈ H → a⁻¹ ∈ H)) 
          | ⟨h_is_nonempty, rel⟩ => 
            let ⟨x, x_in_h⟩ := h_is_nonempty
            let x_op_invx_in_h : x * x⁻¹ ∈ H := rel x x x_in_h x_in_h
            let one_in_h : 1 ∈ H := Eq.subst (mul_inv_cancel x) x_op_invx_in_h
            let ab_in_h (a b : G) (ha : a ∈ H) (hb : b ∈ H) : (a * b) ∈ H := 
              let b_inv_in_h : b⁻¹ ∈ H := Eq.subst (one_mul b⁻¹) (rel 1 b one_in_h hb)
              (inv_inv b) ▸ (rel a b⁻¹ ha b_inv_in_h)
            let a_inv_in_h (a : G) (ha : a ∈ H) : a⁻¹ ∈ H := one_mul a⁻¹ ▸ rel 1 a one_in_h ha
            And.intro h_is_nonempty (And.intro ab_in_h a_inv_in_h)

        let bwd_direction :
          (H.Nonempty ∧ (∀ (a b : G), a ∈ H → b ∈ H → (a * b) ∈ H) ∧ (∀ (a : G), a ∈ H → a⁻¹ ∈ H)) →
          (H.Nonempty ∧ ∀ (a b : G), a ∈ H → b ∈ H → (a * b⁻¹) ∈ H)
          | ⟨h_is_nonempty, ⟨rel1, rel2⟩⟩ =>
            let a_b_inv_in_h (a b : G) (ha : a ∈ H) (hb : b ∈ H) : (a * b⁻¹) ∈ H := 
              rel1 a b⁻¹ ha (rel2 b hb)
            And.intro h_is_nonempty a_b_inv_in_h

        Iff.intro fwd_direction bwd_direction

    (propext cond_is_same) ▸ (th1 H)


theorem th3 {G : Type*} [Group G] [Fintype G] (H : Set G)
  : IsSubgroup H ↔ (H.Nonempty ∧ (∀ (a b : G), a ∈ H → b ∈ H → (a * b) ∈ H)) :=

  let bwd_direction :
    (H.Nonempty ∧ (∀ (a b : G), a ∈ H → b∈H → (a * b) ∈ H)) → IsSubgroup H 
    | ⟨⟨x, hx⟩, rel⟩ =>
      /- let rec f (p : ℕ) : (x ^ (p + 1) ∈ H) := -/
      /-   match p with -/
      /-   | 0 => by simp; exact hx -/
      /-   | p' + 1 =>  -/
      /-     let x_p_in_h : x ^ (p' + 1) ∈ H := f p'  -/
      /-     let xpp : x ^ (p' + 1) * x ∈ H := rel (x ^ (p' + 1)) x x_p_in_h hx -/
      /-     Eq.subst (Eq.symm (pow_succ x (p' + 1))) xpp -/
      let n : ℕ := Fintype.card G
      let f (p : Fin (n + 1)) : G := x ^ (p.val + 1)

      sorry

  sorry


end CH3

end MATH1530

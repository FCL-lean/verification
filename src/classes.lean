import algebra.ordered_group algebra.ordered_ring
section old_structure_cmd
set_option old_structure_cmd true

class decidable_canonically_ordered_monoid (α : Type*) extends canonically_ordered_monoid α, decidable_linear_ordered_cancel_comm_monoid α

end old_structure_cmd

instance : decidable_canonically_ordered_monoid ℕ := {
    ..nat.canonically_ordered_comm_semiring,
    ..nat.decidable_linear_ordered_cancel_comm_monoid
}

instance decidable_linear_order_is_antisymm {α : Type*} [decidable_linear_order α] : is_antisymm α (≥) := 
    ⟨λ a b hab hba, by apply le_antisymm; assumption⟩
instance decidable_linear_order_is_refl {α : Type*} [decidable_linear_order α] : is_refl α (≥) := ⟨λ a, by apply le_refl⟩
instance decidable_linear_order_is_trans {α : Type*} [decidable_linear_order α] : is_trans α (≥) := ⟨λ a b c hab hbc, begin apply le_trans, apply hbc, apply hab, end⟩
instance decidable_linear_order_is_total {α : Type*} [decidable_linear_order α] : is_total α (≥) := ⟨λ a b, by apply le_total⟩ 
instance decidable_linear_order_is_preorder {α : Type*} [decidable_linear_order α] : is_preorder α (≥) := @is_preorder.mk α (≥) decidable_linear_order_is_refl _
instance decidable_linear_order_is_partial_order {α : Type*} [decidable_linear_order α] : is_partial_order α (≥) := @is_partial_order.mk _ (≥) decidable_linear_order_is_preorder _

instance decidable_linear_order_is_linear_order {α : Type*} [decidable_linear_order α] : is_linear_order α (≥) := 
    @is_linear_order.mk _ (≥) decidable_linear_order_is_partial_order _
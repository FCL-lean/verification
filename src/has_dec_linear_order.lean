section dec_linear_order
class has_dec_linear_order (α : Type*) :=
(r : α → α → Prop) (is_lin : is_linear_order α r) (is_dec : decidable_rel r)


instance is_linear_order_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : is_linear_order α a.r := a.is_lin
instance is_antisymm_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : is_antisymm α a.r
 := ⟨a.is_lin.antisymm⟩
instance is_total_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : is_total α a.r
 := ⟨a.is_lin.total⟩
instance is_refl_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : is_refl α a.r
 := ⟨a.is_lin.refl⟩
instance is_trans_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : is_trans α a.r
 := ⟨a.is_lin.trans⟩
instance decidable_rel_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : decidable_rel a.r := a.is_dec
end dec_linear_order


instance decidable_linear_order_is_antisymm {α : Type*} (h : decidable_linear_order α) : is_antisymm α (≥) := 
    ⟨λ a b hab hba, by apply h.le_antisymm; assumption⟩
instance decidable_linear_order_is_refl {α : Type*} [decidable_linear_order α] : is_refl α (≥) := ⟨λ a, by apply le_refl⟩
instance decidable_linear_order_is_trans {α : Type*} [decidable_linear_order α] : is_trans α (≥) := ⟨λ a b c hab hbc, begin apply le_trans, apply hbc, apply hab, end⟩
instance decidable_linear_order_is_total {α : Type*} [decidable_linear_order α] : is_total α (≥) := ⟨λ a b, by apply le_total⟩ 
instance decidable_linear_order_is_preorder {α : Type*} [decidable_linear_order α] : is_preorder α (≥) := @is_preorder.mk α (≥) decidable_linear_order_is_refl _
instance decidable_linear_order_is_partial_order {α : Type*} [decidable_linear_order α] : is_partial_order α (≥) := @is_partial_order.mk _ (≥) decidable_linear_order_is_preorder _

instance decidable_linear_order_is_linear_order {α : Type*} [decidable_linear_order α] : is_linear_order α (≥) := 
    @is_linear_order.mk _ (≥) decidable_linear_order_is_partial_order _

instance decidable_linear_order_has_dec_linear_order {α : Type*} [decidable_linear_order α] : has_dec_linear_order α := {
    r := (≥),
    is_lin := by apply_instance,
    is_dec := by apply_instance,
}
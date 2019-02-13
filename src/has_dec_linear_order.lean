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
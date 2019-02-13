section dec_linear_order
class has_dec_linear_order (α : Type*) :=
(r : α → α → Prop) (is_lin : is_linear_order α r) (is_dec : decidable_rel r)

instance is_linear_order_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : is_linear_order α a.r := a.is_lin
instance decidable_rel_has_dec_linear_order {α : Type*} (a : has_dec_linear_order α) : decidable_rel a.r := a.is_dec
end dec_linear_order
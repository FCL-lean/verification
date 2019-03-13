import data.stream order.order_iso user_classes set
universe u

namespace seq
section seq
variables {α : Type*} (r : α → α → Prop)

def seq := {f : stream α // ∀ n, r (f (n + 1)) (f n)}

lemma no_inf_seq_is_well_founded [is_strict_order α r] : (seq r → false) → well_founded r :=
λ h, order_embedding.well_founded_iff_no_descending_seq.2 
(λ hw, hw.cases_on (λ ⟨f, o⟩, h ⟨f.1, λ n, o.1 (nat.lt_succ_self n)⟩))

end seq

section well_order
variables {α : Type*} [decidable_eq α] [decidable_linear_order α] [is_well_founded α (<)]


end well_order

end seq
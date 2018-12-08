import data.finset
class finite (α : Sort*) :=
(val: finset α)
(is_finite: ∀ (x : α), x ∈ val)
import data.set

namespace set
variables {α : Type*}

def remove (a : α) (s : set α) : set α := s \ {a}

instance decidable_set_of_diff (p q : α → Prop) [H₁ : decidable_pred p] [H₂ : decidable_pred q] :
decidable_pred (set.diff {a | p a} {a | q a}) := begin
    simp [set.diff],
    apply_instance,
end

end set
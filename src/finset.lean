import data.finset

namespace finset
variables {α : Type*}

section sort
variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r]

@[simp] lemma sort_eq_nil (s : finset α) : s.sort r = [] ↔ s = ∅ := 
⟨λ h, begin
    have h' : ↑(sort r s) = (∅ : multiset α),
        simp [h],
    simp at h', assumption,
end, 
λ h, by finish⟩

lemma sort_ne_nil (s : finset α) : (s.sort r) ≠ [] ↔ s ≠ ∅ := by simp

end sort

end finset
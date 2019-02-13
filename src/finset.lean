import data.finset

namespace finset
variables {α : Type*}

section sort
variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r]

--@[simp] lemma sort_empty : sort r ∅ = [] := by finish

@[simp] lemma sort_eq_nil (s : finset α) : s.sort r = [] ↔ s = ∅ := 
⟨λ h, begin
    have h' : ↑(sort r s) = (∅ : multiset α),
        simp [h],
    simpa using h', 
end, 
λ h, by finish⟩

lemma sort_ne_nil (s : finset α) : (s.sort r) ≠ [] ↔ s ≠ ∅ := by simp

lemma sort_singleton [decidable_eq α] {s : finset α} {a} : (s.sort r) = [a] ↔ s = {a} := ⟨λ hs, begin
    ext a', 
    have h := @mem_sort _ r _ _ _ _ s,
    split; intro ha',
    rwa [←@h a', hs] at ha',
    simpa [(@h a').symm, hs] using ha',
end, λ h, begin finish [h], end⟩

lemma sort_hd_rel [inhabited α] [decidable_eq α] {s : finset α} : ∀ a ∈ (s.sort r).tail, r (s.sort r).head a := begin
    have h := sort_sorted r s,
    generalize hl : sort r s = l,
    rw hl at h,
    cases l; finish,
end

end sort

end finset
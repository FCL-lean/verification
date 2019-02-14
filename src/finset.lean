import data.finset
import has_dec_linear_order
namespace finset
variables {α : Type*}
section 
    @[simp] lemma subset_to_set (s₁ s₂ : finset α) : s₁.to_set ⊆ s₂.to_set ↔ s₁ ⊆ s₂  := by finish
    @[simp] lemma mem_to_set (s : finset α) : ∀ a, a ∈ s.to_set ↔ a ∈ s := by finish

    lemma insert_to_set [decidable_eq α] (s : finset α) (a : α) : (insert a s).to_set = insert a (s.to_set) :=
        by ext x; finish
end


section sort
variables [has_dec_linear_order α]
def dlo : has_dec_linear_order α := by apply_instance
--@[simp] lemma sort_empty : sort dlo.r ∅ = [] := by finish

@[simp] lemma sort_eq_nil (s : finset α) : s.sort dlo.r = [] ↔ s = ∅ := 
⟨λ h, begin
    have h' : ↑(sort dlo.r s) = (∅ : multiset α),
        simp [h],
    simpa using h', 
end, 
λ h, by finish⟩

lemma sort_ne_nil (s : finset α) : (s.sort dlo.r) ≠ [] ↔ s ≠ ∅ := by simp

lemma sort_singleton [decidable_eq α] {s : finset α} {a} : (s.sort dlo.r) = [a] ↔ s = {a} := ⟨λ hs, begin
    ext a', 
    have h := @mem_sort _ dlo.r _ _ _ _ s,
    split; intro ha',
    rwa [←@h a', hs] at ha',
    simpa [(@h a').symm, hs] using ha',
end, λ h, begin finish [h], end⟩

lemma sort_hd_rel [inhabited α] [decidable_eq α] {s : finset α} : ∀ a ∈ (s.sort dlo.r).tail, (dlo.r : α → α → Prop) (s.sort dlo.r).head a := begin
    have h := sort_sorted dlo.r s,
    generalize hl : sort dlo.r s = l,
    rw hl at h,
    cases l; finish,
end

end sort

end finset
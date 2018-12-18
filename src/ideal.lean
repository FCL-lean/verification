import ring_theory.ideals
import util
variables {α : Type*} [comm_ring α] [decidable_eq α]

namespace ideal

set_option trace.simplify.rewrite true
lemma mem_set : ∀ {a : α} {s : set α}, a ∈ s → a ∈ span s :=
λ a s h, begin
    have h' : s ⊆ span s, exact subset_span,
    rw set.subset_def at h',
    apply h' a h,
end

lemma mem_singleton_union : ∀ (a : α) {s : set α}, a ∈ span ({a} ∪ s) :=
λ a s, by finish [mem_set]

lemma linear_combine_mem {p q : α} {s : set α} : ∀ a b, p ∈ s → q ∈ s → (a * p + b * q) ∈ span s :=
λ a b hp hq, begin
    apply ideal.add_mem (span s);
    apply ideal.mul_mem_left (span s),
    exact mem_set hp,
    exact mem_set hq,
end

lemma list_subset {I : ideal α} {l : list α} : l.to_finset.to_set ⊆ I ↔ (∀ a ∈ l, a ∈ I) :=
begin
    unfold has_subset.subset set.subset,
    apply iff.intro,
    intros h a ha, rw list.mem_to_set at ha, apply h ha,
    intros h a ha, rw ←list.mem_to_set at ha, exact h a ha,
end

lemma subset_of_set_subset {s₁ s₂ : set α} {I : ideal α} : s₁ ⊆ s₂ → s₂ ⊆ I → s₁ ⊆ I :=
λ s12 s2i, begin
    let hs12 := span_mono s12, 
    rw ←span_le at *,
    exact le_trans hs12 s2i,
end

lemma subset_of_span_eq {I : ideal α} {s : set α} (h : span s = I) : s ⊆ I := by rw ←h;  apply subset_span

lemma subset_of_subset_carrier {i : ideal α} {s : set α} : s ⊆ i.carrier ↔ s ⊆ i := by finish

lemma subset_of_le {i₁ i₂ : ideal α} : i₁ ≤ i₂ ↔ (i₁ : set α) ⊆ ↑i₂ := by finish

lemma carrier_lt_of_lt {i₁ i₂ : ideal α} (h : i₁ < i₂) : i₁.carrier < i₂.carrier := by finish

lemma mem_of_mem_le_ideal {I₁ I₂ : ideal α} : ∀ x : α, x ∈ I₁ → I₁ ≤ I₂ → x ∈ I₂ :=
λ x h₁ h₂ , by rw [←ideal.span_eq I₁, span_le] at h₂; apply h₂ h₁

lemma lt_of_union_not_mem {s : set α} {a : α} (h : a ∉ span s) : span s < span ({a} ∪ s) :=
begin
    rw [lt_iff_le_and_ne], apply and.intro, finish [span_mono],
    intro H, rw H at h, apply absurd (mem_singleton_union a) h,
end

end ideal

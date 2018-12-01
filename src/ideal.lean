import ring_theory.ideals
variables {α : Type*} [comm_ring α]

namespace ideal

set_option trace.simplify.rewrite true
lemma mem_set : ∀ {a : α} {s : set α}, a ∈ s → a ∈ span s :=
λ a s h, begin
    have h' : s ⊆ span s, exact subset_span,
    rw set.subset_def at h',
    apply h' a h,
end

lemma linear_combine_mem {p q : α} {s : set α} : ∀ a b, p ∈ s → q ∈ s → (a * p + b * q) ∈ span s :=
λ a b hp hq, begin
    apply ideal.add_mem (span s);
    apply ideal.mul_mem_left (span s),
    exact mem_set hp,
    exact mem_set hq,
end

end ideal

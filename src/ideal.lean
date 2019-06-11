import ring_theory.ideals

namespace ideal
variables {α : Type*} [comm_ring α]

lemma ne_of_not_mem_mem {i₁ i₂ : ideal α} (a : α) : a ∉ i₁ → a ∈ i₂ → i₁ ≠ i₂ :=
λ ha₁ ha₂ h, ha₁ (by rwa h)

end ideal
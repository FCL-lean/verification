import data.mv_polynomial ring_theory.noetherian ring_theory.polynomial

section division_ring

variables {α : Type*} [decidable_eq α] [division_ring α]

lemma submodule_ne_zero {s : submodule α α} (h : ¬ ↑s = ({0} : set α)) : (1 : α) ∈ s :=
begin
    have : ¬ ∀ x ∈ s, x = (0 : α) := λ H, h (begin 
        ext x, 
        refine ⟨by simpa using H x, λ hx, by simp at hx; simp [hx]⟩,
    end),

    letI := classical.dec,
    simp [not_forall, not_imp] at this,
    rcases this with ⟨x, hx₁, hx₂⟩,
    simpa [hx₂] using s.smul x⁻¹ hx₁,
end

instance division_ring_is_noetherian : is_noetherian_ring α := {
    noetherian := λ s, begin
        letI := classical.dec,
        unfold submodule.fg,
        by_cases s = ⊥,
        {refine ⟨{0}, by simp [h, submodule.span_eq_bot]⟩},
        {
            refine ⟨{1}, _⟩,
            ext y,
            refine ⟨λ _, by simp [submodule.ext'_iff.symm] at h; simpa using s.smul y (submodule_ne_zero h),
            λ _, by simp [submodule.mem_span]; from λ p hp, by simpa using p.smul _ hp⟩,
        }
    end
}

end division_ring

open finsupp
namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] 
variables [fintype σ] [comm_ring α] [is_noetherian_ring α]

lemma ideal_wf : well_founded ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) 
    := is_noetherian_iff_well_founded.1 is_noetherian_ring_mv_polynomial_of_fintype

end mv_polynomial

import data.mv_polynomial ring_theory.noetherian finsupp finset

open finsupp
namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] 

/-section discrete_field
variables [discrete_field α] 

theorem HBT : is_noetherian (mv_polynomial σ α) (mv_polynomial σ α) := sorry

lemma ideal_wf : well_founded ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) := is_noetherian_iff_well_founded.1 HBT

end discrete_field-/

section basic
variables [comm_semiring α]

instance : has_coe_to_fun (mv_polynomial σ α) := ⟨λ _, (σ →₀ ℕ) → α, finsupp.to_fun⟩
@[simp] lemma support_zero : (0 : mv_polynomial σ α).support = ∅ := finsupp.support_zero
@[simp] lemma zero_apply {a} : (0 : mv_polynomial σ α) a = 0 := rfl
@[simp] lemma support_eq_empty {p : mv_polynomial σ α} : p.support = ∅ ↔ p = 0 := finsupp.support_eq_empty
lemma support_ne_empty (p : mv_polynomial σ α) : p.support ≠ ∅ ↔ p ≠ 0 := by finish
@[simp] lemma eq_zero_lem : ∀ {f : (σ →₀ ℕ) → α} {l}, ({support := ∅, to_fun := f, mem_support_to_fun := l} : mv_polynomial σ α) = (0 : mv_polynomial σ α) := by apply finsupp.eq_zero_lem 
lemma eq_zero_apply (p : mv_polynomial σ α) : (∀ a, p a = 0) ↔ p = 0 := eq_zero_apply p

@[simp] lemma zero_monomial {a : σ →₀ ℕ} : ((monomial a 0) : mv_polynomial σ α) = 0 := by simp [monomial]; refl
lemma monomial_eq_zero_iff {a : σ →₀ ℕ} {b : α} : monomial a b = 0 ↔ b = 0 := by simp [monomial]; apply single_eq_zero_iff

lemma monomial_add_monomial {a : σ →₀ ℕ} {b₁ b₂ : α} :
    monomial a (b₁ + b₂) = monomial a b₁ + monomial a b₂ := by simp [monomial]
lemma monomial_mul_monomial {a₁ a₂ : σ →₀ ℕ} {b₁ b₂ : α} :
  monomial a₁ b₁ * monomial a₂ b₂ = monomial (a₁ + a₂) (b₁ * b₂) := by simp [monomial]; apply single_mul_single

lemma monomial_apply {a a' : σ →₀ ℕ} {b : α} : ((monomial a b) : mv_polynomial σ α) a' = if a = a' then b else 0 := rfl

lemma support_monomial_eq {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : (monomial a b).support = {a} :=
    by simp [monomial, single, hb]

lemma not_mem_disjoint {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a ∉ p.support) 
{b : α} (hb : b ≠ 0) : disjoint (monomial a b).support p.support :=
by simpa [support_monomial_eq hb, finset.disjoint_singleton] using ha

@[simp] lemma add_zero {p : mv_polynomial σ α} : p + 0 = p := by simp

lemma add_monomial_nez {p : mv_polynomial σ α} {a} (ha : a ∉ p.support) {b : α} (hb : b ≠ 0) : monomial a b + p ≠ 0 := 
λ h, hb begin
    rw ←eq_zero_apply (monomial a b + p) at h,
    simpa [monomial_apply, not_mem_support_iff.1 ha] using h a,
end

@[simp] lemma nez_of_mem_support {p : mv_polynomial σ α} {a} (ha : a ∈ p.support) : p ≠ 0 :=
λ h', by finish

@[elab_as_eliminator]
theorem induction_f {C : (mv_polynomial σ α) → Prop} (p : mv_polynomial σ α)
  (C0 : C (0 : mv_polynomial σ α)) (Ca : ∀a b (p : mv_polynomial σ α), a ∉ p.support → b ≠ 0 → C p → C (monomial a b + p)) :
  C p :=
  begin
    apply finsupp.induction, assumption,
    intros a b f haf hb hf,
    simpa [monomial] using Ca a b f haf hb hf,
  end

end basic
end mv_polynomial

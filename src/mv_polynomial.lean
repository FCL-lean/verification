import linear_algebra.multivariate_polynomial ring_theory.noetherian finsupp finset

open finsupp
namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] 

section discrete_field
variables [discrete_field α]

def HBT : is_noetherian (mv_polynomial σ α) (mv_polynomial σ α) := sorry

lemma ideal_wf : well_founded ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) := 
    by rw ←is_noetherian_iff_well_founded; exact HBT

end discrete_field

section basic
variables [comm_semiring α]

instance : has_coe_to_fun (mv_polynomial σ α) := ⟨λ _, (σ →₀ ℕ) → α, finsupp.to_fun⟩
@[simp] lemma support_zero : (0 : mv_polynomial σ α).support = ∅ := finsupp.support_zero
@[simp] lemma zero_apply {a} : (0 : mv_polynomial σ α) a = 0 := rfl
@[simp] lemma support_eq_empty {p : mv_polynomial σ α} : p.support = ∅ ↔ p = 0 := finsupp.support_eq_empty
lemma support_ne_empty (p : mv_polynomial σ α) : p.support ≠ ∅ ↔ p ≠ 0 := by finish
@[simp] lemma eq_zero_lem : ∀ {f : (σ →₀ ℕ) → α} {l}, ({support := ∅, to_fun := f, mem_support_to_fun := l} : mv_polynomial σ α) = (0 : mv_polynomial σ α) := by apply finsupp.eq_zero_lem 

@[simp] lemma zero_monomial {a : σ →₀ ℕ} : ((monomial a 0) : mv_polynomial σ α) = 0 := by simp [monomial]; refl
lemma monomial_eq_zero_iff {a : σ →₀ ℕ} {b : α} : monomial a b = 0 ↔ b = 0 := by simp [monomial]; apply single_eq_zero_iff
lemma monomial_mul_monomial {a₁ a₂ : σ →₀ ℕ} {b₁ b₂ : α}:
  monomial a₁ b₁ * monomial a₂ b₂ = monomial (a₁ + a₂) (b₁ * b₂) := by simp [monomial]; apply single_mul_single

lemma monomial_apply {a a' : σ →₀ ℕ} {b : α} : ((monomial a b) : mv_polynomial σ α) a' = if a = a' then b else 0 := rfl

lemma support_monomial_eq {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : (monomial a b).support = {a} :=
    by simp [monomial, single, hb]

@[simp] lemma add_zero {p : mv_polynomial σ α} : p + 0 = p := by simp

lemma add_support_subset_union (c : mv_polynomial σ α) (as : σ →₀ ℕ) {aa : α} (haa : aa ≠ 0) :
 (finset.fold (+) 0 (λ (a : σ →₀ ℕ), single (as + a) (mul_zero_class.mul (c.to_fun a) aa)) (c.support)).support 
  ⊆ finset.fold (∪) (∅) (λ (a : σ →₀ ℕ), (single (as + a) (mul_zero_class.mul (c.to_fun a) aa)).support) (c.support) :=
begin
    apply finsupp.induction c, simp,
    intros a b f haf hb ih,
    have h : (single a b + f).support = insert a f.support,
        have h' : (single a b).support = {a}, simp [single, hb],
        rw [finset.insert_eq, ←h'],
        apply support_add_eq,
        simp [single, hb, not_mem_support_iff.1 haf],
    rw [h, finset.fold_insert haf], simp, 
    apply finset.subset.trans support_add,
    have h_to_fun_eq : ∀ (x : σ →₀ ℕ) (hx : x ∈ f.support), f.to_fun x = (f + single a b).to_fun x,
            intros x hx,
            have hax : a ≠ x, intro hax', rw hax' at haf, exact haf hx,
            repeat {rw ←coe_f}, simp, simp [coe_f, single], simp [hax],
    have h_congr : ∀ (x : σ →₀ ℕ) (hx : x ∈ f.support), (λ x, single (as + x) (mul_zero_class.mul (f.to_fun x) aa)) x =
        (λ x, single (as + x) (mul_zero_class.mul ((f + single a b).to_fun x) aa)) x,
        intros x hx, simp [h_to_fun_eq x hx],
    have h_congr' : ∀ (x : σ →₀ ℕ) (hx : x ∈ f.support), (λ x, (single (as + x) (mul_zero_class.mul (f.to_fun x) aa)).support) x =
        (λ x, (single (as + x) (mul_zero_class.mul ((f + single a b).to_fun x) aa)).support) x,
        intros x hx, simp [h_to_fun_eq x hx],
    rw [finset.fold_congr h_congr, finset.fold_congr h_congr'] at ih,
    apply finset.union_subset' (finset.subset.refl _) ih,
end

end basic
end mv_polynomial

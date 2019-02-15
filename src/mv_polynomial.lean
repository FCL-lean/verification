import linear_algebra.multivariate_polynomial ring_theory.noetherian order_finsupp lex_order

open finsupp
namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] 

section discrete_field
variables [discrete_field α]
def HBT : is_noetherian (mv_polynomial σ α) (mv_polynomial σ α) := sorry

lemma ideal_wf : well_founded ((>) : ideal (mv_polynomial σ α) → ideal (mv_polynomial σ α) → Prop) := 
    by rw ←is_noetherian_iff_well_founded; exact HBT

end discrete_field

section comm_semiring
variables [comm_semiring α]
def is_const (p : mv_polynomial σ α) := p = 0 ∨ p.support = {0} 
def is_const' (p : mv_polynomial σ α) := p.support = {0} 

instance decidable_is_const : @decidable_pred (mv_polynomial σ α) is_const := λ p, by unfold is_const; apply_instance
instance decidable_is_const' : @decidable_pred (mv_polynomial σ α) is_const' := λ p, by unfold is_const'; apply_instance

lemma zero_is_const : is_const (0 : mv_polynomial σ α) := by simp [is_const]

lemma const'_hd_dvd [has_dec_linear_order (σ →₀ ℕ)] {p : mv_polynomial σ α} (h : is_const' p) : ∀ q : σ →₀ ℕ, p.hd ∣ q := 
    by simp [singleton_hd h, has_dvd.dvd, dvd]

lemma const_hd_dvd [has_dec_linear_order (σ →₀ ℕ)] {p : mv_polynomial σ α} (h : is_const p) : ∀ q : σ →₀ ℕ, p.hd ∣ q := begin
    cases h; intro q, simp [eq_zero_hd h, inhabited.default, has_dvd.dvd, dvd],
    apply const'_hd_dvd h,
end

lemma monomial_eq_zero_iff {a : σ →₀ ℕ} {b : α} : monomial a b = 0 ↔ b = 0 := begin
    simp [monomial], apply single_eq_zero_iff,
end

@[simp] lemma support_zero : (0 : mv_polynomial σ α).support = ∅ := by apply finsupp.support_zero

lemma support_monomial_eq {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : (monomial a b).support = {a} := begin
    simp [monomial], apply support_single_eq hb,
end

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

section has_dec_linear_order

variables [has_dec_linear_order (σ →₀ ℕ)]
@[simp] lemma zero_lm : (0 : mv_polynomial σ α).hd = 0 := begin
    generalize h : hd 0 = x, simp [inhabited.default] at h, exact h.symm,
end

lemma is_const_lm {p : mv_polynomial σ α} (hp : is_const p) : p.hd = 0 := 
    by cases hp; finish [hd, s_support, hp]

lemma eq_zero_of_div_zero : ∀ p : mv_polynomial σ α, (p.hd ∣ (0 : σ →₀ ℕ)) ↔ p.hd = 0 := 
λ p, by simp [has_dvd.dvd, dvd, eq_zero_apply]

end has_dec_linear_order

section fin
variables {n : ℕ}

lemma is_const_of_lm_eqz {p : mv_polynomial (fin n) α} : is_const p ↔ p.hd = 0:= 
⟨is_const_lm, 
λ hp, begin
    by_cases h : p = 0, left, assumption,
    right,
    have h_rel := hd_rel p,
    have h_cons := cons_hd_tl h,
    ext x, simp [-mem_support_iff, mem_s_support.symm, h_cons.symm, hp] at ⊢ h_rel,
    split, rintros (hx | hx), assumption,
    rw ←fin.le_zero_iff, apply h_rel x hx,
    finish,
end⟩

lemma not_const_of_lm_nez {p : mv_polynomial (fin n) α} : ¬is_const p ↔ p.hd ≠ 0:= by finish [is_const_of_lm_eqz]

lemma not_const_of_div {p q : mv_polynomial (fin n) α} : ¬is_const q → q.hd ∣ p.hd → ¬ is_const p := 
λ hq hqp hp, begin
    rw [is_const_lm hp, eq_zero_of_div_zero] at hqp,
    apply hq, rwa is_const_of_lm_eqz,
end
end fin

end comm_semiring

section monomial_ideal
variables [has_dec_linear_order (σ →₀ ℕ)]

section comm_ring
variables [comm_ring α] 
def monomial_ideal (l : list (mv_polynomial σ α)) : ideal (mv_polynomial σ α) := 
    ideal.span ↑(l.map (λ f : mv_polynomial σ α, monomial f.hd f.hd_val)).to_finset

lemma support_subset_of_linear_combination_union (s : finset (mv_polynomial σ α)) : 
    ∀ (hs: s ≠ ∅) (p : mv_polynomial σ α) (hp₁ : p ∈ ideal.span (↑s : set (mv_polynomial σ α))),
    ∃ (c : ((mv_polynomial σ α) →₀ (mv_polynomial σ α))), c.support ⊆ s ∧ p.support ⊆ s.fold (∪) (∅) (λ a, ((c.to_fun a) * a).support) :=
begin
    apply finset.induction_on s, finish,
    intros a s' has' ih hs p hp,
    rw [finset.coe_insert, ideal.mem_span_insert] at hp,
    rcases hp with ⟨a', ⟨z, ⟨hz, hp⟩⟩⟩,
    by_cases hs' : s' = ∅,
    simp [hs', ideal.span] at hz, 
    apply exists.intro (single a a'),
    rw [finset.fold_insert has', hp, hz, hs', ←coe_f], simp [single, finset.insert_eq], 
    by_cases ha' : a' = 0; finish [ha'],
    rcases ih hs' z hz with ⟨zc, ⟨hzc, hz'⟩⟩,
    apply exists.intro (single a a' + zc), 
    simp,
    have hzc_app : zc a = 0, rw [←not_mem_support_iff], intro hazc, exact has' (hzc hazc),
    
    have h_congr : ∀ x ∈ s', (λ x, (zc.to_fun x * x).support) x = (λ x, ((zc + single a a').to_fun x * x).support) x,
        intros x hx, simp, repeat {rw [←coe_f]}, simp [single_apply, ne.symm (finset.ne_of_mem_and_not_mem hx has')],
    
    simp [(finset.fold_congr h_congr).symm, hzc_app, hp], split,
    apply finset.subset.trans support_add (finset.union_subset'_symm hzc support_single_subset),
    apply finset.subset.trans support_add (finset.union_subset'_symm hz' (finset.subset.refl _)),
end

end comm_ring

section integral_domain
variables [integral_domain α]
lemma mem_mul_support {a a': σ →₀ ℕ} {b b': α} (hb : b ≠ 0) (hb' : b' ≠ 0) (c : mv_polynomial σ α) 
(h_sub : {a} ⊆ (c * (monomial a' b')).support) : a' ∣ a := begin
    simp [has_mul.mul, monomial, single_sum' a' hb'] at h_sub,
    simp [finsupp.sum, finset.sum_eq_fold] at h_sub,
    rcases finset.mem_fold_union (finset.subset.trans h_sub (add_support_subset_union c a' hb')) with ⟨d, ⟨hd, h⟩⟩,
    have h_mul_nez : mul_zero_class.mul (c.to_fun d) b' ≠ 0,
        apply mul_ne_zero _ hb',
        simpa using hd,
    simp [single, h_mul_nez, finset.subset_iff] at h,
    apply dvd_of_add h,
end

lemma monomial_mem_ideal {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : ∀ l : list (mv_polynomial σ α), 
    monomial a b ∈ monomial_ideal l → ∃ (p  : mv_polynomial σ α) (hp : p ∈ l), p.hd ∣ a
| [] := by simpa [monomial_ideal, ideal.span, monomial_eq_zero_iff] using hb
| (q :: l') := 
λ h_mem, begin
    rcases support_subset_of_linear_combination_union ((list.cons q l').map (λ f : mv_polynomial σ α, monomial f.hd f.hd_val)).to_finset (by simp) (monomial a b) h_mem
        with ⟨c, ⟨hc, h⟩⟩,
    rw support_monomial_eq hb at h,
    rcases finset.mem_fold_union h with ⟨p, ⟨hp, h'⟩⟩,
    rw [list.mem_to_finset, list.mem_map] at hp,
    rcases hp with ⟨p', ⟨hp', hp⟩⟩,
    refine ⟨p', ⟨hp', _⟩⟩, 
    simp [hp.symm] at h',
    have hp'_val : p'.hd_val ≠ 0, intro hp', simpa [monomial_eq_zero_iff.2 hp', finset.subset_empty] using h',
    apply mem_mul_support hb hp'_val; assumption,
end
end integral_domain
end monomial_ideal




end mv_polynomial
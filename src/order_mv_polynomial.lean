import mv_polynomial sorted_list lex_order

open finsupp
namespace mv_polynomial
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] 

section decidable_linear_order
variables [decidable_linear_order (σ →₀ ℕ)]

section comm_semiring
variables [comm_semiring α]

section sort_support
def s_support (p : mv_polynomial σ α) := p.support.sort (≥)

lemma mem_s_support {p : mv_polynomial σ α} {a} : a ∈ p.s_support ↔ a ∈ p.support := by simp [s_support]
lemma not_mem_s_support {p : mv_polynomial σ α} {a} : a ∉ p.s_support ↔ a ∉ p.support := by simp [s_support]
lemma support_empty_of_s_nil {p : mv_polynomial σ α} : p.s_support = [] ↔ p.support = ∅ := by simp [s_support]
@[simp] lemma zero_s_support : (0 : mv_polynomial σ α).s_support = [] := by simp [s_support]
lemma eq_zero_of_s_nil {p : mv_polynomial σ α} : p.s_support = [] ↔ p = 0 := by simp [s_support]
lemma ne_zero_of_s_ne_nil {p : mv_polynomial σ α} : p.s_support ≠ [] ↔ p ≠ 0 := by simp [s_support, eq_zero_of_s_nil]

def hd (p : mv_polynomial σ α) := p.s_support.head
def hd_val (p : mv_polynomial σ α) := p p.hd

def tl (p : mv_polynomial σ α) : mv_polynomial σ α := 
⟨(p.support.erase p.hd), λ a, if a = p.hd then 0 else p a, 
λ a, begin
    split; simp_intros, simp [a_1],
    by_cases a = p.hd; finish,
end⟩ 

@[simp] lemma zero_hd : (0 : mv_polynomial σ α).hd = 0 := by finish
@[simp] lemma zero_hd_val : (0 : mv_polynomial σ α).hd_val = 0 := by finish
lemma eq_zero_hd {p : mv_polynomial σ α} : p = 0 → p.hd = 0 := by finish

lemma hd_mem_s_support (p : mv_polynomial σ α) (h : p ≠ 0) : p.hd ∈ p.s_support:= begin
    rw [←support_ne_empty, ←finset.sort_ne_nil] at h,
    unfold hd s_support, rw [←list.cons_head_tail h],
    simp,
end

lemma hd_mem_support {p : mv_polynomial σ α} (h : p ≠ 0) : p.hd  ∈ p.support := 
    by rw ←finset.mem_sort (≥); apply hd_mem_s_support _ h

lemma hd_not_mem {p : mv_polynomial σ α} : p.hd ∉ p.support ↔ p = 0 := ⟨λ h, begin
    by_cases hf : p = 0, assumption, 
    apply absurd (hd_mem_support hf) h,
end, λ h, by simp [h]⟩

lemma hd_not_mem_tl {p : mv_polynomial σ α} : p.hd ∉ p.tl.support := by simp [tl]

lemma hd_val_eqz_iff {p : mv_polynomial σ α} : p = 0 ↔ p.hd_val = 0 := begin
    split; intro h, 
    rw [hd_val, hd, ←not_mem_support_iff, ←not_mem_s_support],
    simp [h],
    rwa [hd_val, ←not_mem_support_iff, hd_not_mem] at h,
end

lemma hd_val_nez_iff {p : mv_polynomial σ α} : p ≠ 0 ↔ p.hd_val ≠ 0 := 
    by simp [hd_val_eqz_iff]

lemma singleton_hd {p : mv_polynomial σ α} {a} (h : p.support = {a}) : p.hd = a := by finish [hd, s_support, h]
lemma singleton_eq_monomial {p : mv_polynomial σ α} {a} (h : p.support = {a}) : p = monomial a (p a) := begin
    ext x, 
    by_cases ha : a = x; simp [monomial_apply, ha],
    simp [not_mem_support_iff.symm, h, ne.symm ha],
end

@[simp] lemma hd_of_monomial {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0): (monomial a b).hd = a := 
    by simp [singleton_hd (support_monomial_eq hb)]

@[simp] lemma hd_val_of_monomial {a : σ →₀ ℕ} {b : α} : (monomial a b).hd_val = b := begin
    by_cases hb : b = 0, simp [hb],
    simp [hd_val, monomial_apply, singleton_hd (support_monomial_eq hb)], 
end

lemma tl_apply (p : mv_polynomial σ α) : ∀ a ≠ p.hd, p.tl a = p a := 
λ a h, by rw coe_f; finish [tl]

lemma tl_apply_hd (p : mv_polynomial σ α) : p.tl p.hd = 0 := 
    by rw ←not_mem_support_iff; simp [tl]

lemma tl_eq_s_tl {p : mv_polynomial σ α} : p.tl.s_support = p.s_support.tail := begin
    by_cases hp : s_support p = [], 
    {simp [hp, tl, support_empty_of_s_nil.1 hp],},
    {
        apply @list.sorted_nodup_ext (σ →₀ ℕ) (≥) _,
        {simp [s_support]},
        {apply list.sorted_tail, simp [s_support]},
        {simp [s_support],},
        {apply @list.nodup_of_nodup_cons _ p.s_support.head, rw list.cons_head_tail hp, simp [s_support],},
        {
            intro a, unfold s_support at hp, simp [s_support, hd, tl, -mem_support_iff],
            rw [←finset.mem_sort (≥), ←list.cons_head_tail hp],
            simp [and_or_distrib_left],
            refine ⟨λ h, h.right, λ h, ⟨_, by assumption⟩⟩,
            have nh := finset.sort_nodup (≥) p.support, rw [←list.cons_head_tail hp, list.nodup_cons] at nh,
            intro ha, apply nh.left, rwa ha at h, 
        }
    },
end 

lemma hd_rel (p : mv_polynomial σ α) : ∀ a, a ∈ p.tl.support → p.hd ≥ a := λ a, 
    by rw [←mem_s_support, tl_eq_s_tl, hd]; apply finset.sort_hd_rel

lemma hd_rel' {p : mv_polynomial σ α} : ∀ a, a ∈ p.support → p.hd ≥ a := λ a, 
begin
    by_cases hp : p = 0, simp [hp],
    have h :  insert p.hd p.tl.support = p.support,
        simp [tl, -finset.union_comm], apply finset.insert_erase (hd_mem_support hp),
    simp [h.symm, -mem_support_iff], rintro (h' | h'),
    rw h', apply le_refl,
    apply hd_rel _ a h',
end

lemma gt_hd_not_mem {p : mv_polynomial σ α} : ∀ {x}, x > p.hd → x ∉ p.support := 
λ x hx h_mem, begin
    apply lt_iff_not_ge'.1 hx,
    apply hd_rel' _ h_mem,
end

lemma gt_hd_apply {p : mv_polynomial σ α} : ∀ {x}, x > p.hd → p x = 0 := 
λ x, by rw ←not_mem_support_iff; apply gt_hd_not_mem

lemma cons_hd_tl {p : mv_polynomial σ α} (hp : p ≠ 0) : list.cons p.hd p.tl.s_support = p.s_support := 
    by simp [tl_eq_s_tl, hd]; apply list.cons_head_tail; rwa ne_zero_of_s_ne_nil

lemma hd_tl_eq (p : mv_polynomial σ α) : (monomial p.hd p.hd_val) + p.tl = p := begin
    ext a, simp [monomial_apply], 
    by_cases ha : p.hd = a; simp [ha],
    simp [hd_val, ha.symm, tl_apply_hd], 
    exact (tl_apply p _ (ne.symm ha)),
end

@[elab_as_eliminator]
lemma induction {C : (mv_polynomial σ α) → Prop} (p : mv_polynomial σ α) 
    (C₀ : C 0)
    (Cₙ : ∀ (p : mv_polynomial σ α), C p.tl → C p) : C p := 
    suffices ∀ l (p : mv_polynomial σ α), p.s_support = l → C p, from this _ _ rfl,
    λ l, @list.rec_on _ (λ l, (∀ p : mv_polynomial σ α, p.s_support = l → C p)) l
    (λ p hp, by rw eq_zero_of_s_nil at hp; rwa hp) 
    begin
        simp_intros l_hd l_tl ih p hp,
        apply Cₙ, apply ih,
        rw ←cons_hd_tl at hp, simp at hp, exact hp.right,
        rw [←ne_zero_of_s_ne_nil, hp], simp,
    end

end sort_support

section const
def is_const (p : mv_polynomial σ α) := p.hd = 0

instance decidable_is_const : @decidable_pred (mv_polynomial σ α) is_const := λ p, by unfold is_const; apply_instance

@[simp] lemma zero_is_const : is_const (0 : mv_polynomial σ α) := by simp [is_const]
lemma nez_of_not_const {p : mv_polynomial σ α} (h : ¬is_const p) : p ≠ 0 := λ hp, h (by simp [zero_is_const, hp])

lemma const_hd_dvd {p : mv_polynomial σ α} (h : is_const p) : ∀ q : σ →₀ ℕ, p.hd ∣ q := λ q, by unfold is_const at h; simp [h]

lemma hd_val_nez_of_not_const {p : mv_polynomial σ α} : ¬is_const p → p.hd_val ≠ 0 := 
λ h h', h (by rw ←hd_val_eqz_iff at h'; simp [is_const, h'])

lemma hd_is_const_iff {p : mv_polynomial σ α} : is_const p ↔ p.hd = 0 := by simp [is_const]
lemma not_const_iff {p : mv_polynomial σ α} : ¬is_const p ↔ p.hd ≠ 0:= by finish [hd_is_const_iff]

lemma eq_zero_of_div_zero : ∀ p : mv_polynomial σ α, (p.hd ∣ (0 : σ →₀ ℕ)) ↔ p.hd = 0 := 
λ p, by simp [has_dvd.dvd, dvd, eq_zero_apply]

lemma not_const_of_div {p q : mv_polynomial σ α} : ¬is_const q → q.hd ∣ p.hd → ¬ is_const p := 
λ hq hqp hp, begin
    rw [hd_is_const_iff.1 hp, eq_zero_of_div_zero] at hqp,
    apply hq, rwa hd_is_const_iff,
end

lemma mem_support_add_le_hd {p q : mv_polynomial σ α} (hpq : p.hd ≥ q.hd) : ∀ (x : σ →₀ ℕ), (x ∈ (p + q).support) → p.hd ≥ x :=
λ x hx, begin
    have hx' := support_add hx, rw [finset.mem_union] at hx', 
    cases hx',
    apply hd_rel' _ hx',
    apply le_trans (hd_rel' _ hx') hpq,
end

end const

end comm_semiring

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
    have hp'_val : p'.hd_val ≠ 0, intro hp'', simpa [monomial_eq_zero_iff.2 hp'', finset.subset_empty] using h',
    apply mem_mul_support hb hp'_val; assumption,
end

end integral_domain

end decidable_linear_order

section fin
variables {n : ℕ}
section comm_ring
variables [comm_ring α]

lemma hd_of_add_left {p q : mv_polynomial (fin n) α} (hpq : p.hd > q.hd) :
    (p + q).hd = p.hd := 
begin
    have hp_hd := mem_support_add_le_hd (le_of_lt hpq),
    apply (antisymm (hp_hd _ (hd_mem_support (λ h, _))) (hd_rel' _ _)).symm,
    have h' := (eq_zero_apply _).2 h p.hd, revert h',
    all_goals {
        simp [gt_hd_apply hpq], rw [←not_mem_support_iff, hd_not_mem],
        intros h,
        simp [h] at hpq,
        apply (not_lt_of_le (finsupp.fin.zero_le q.hd)) hpq,
    },
end

lemma hd_val_of_add_left {p q : mv_polynomial (fin n) α} (hpq : p.hd > q.hd) :
    (p + q).hd_val = p.hd_val := 
by simp [hd_val, hd_of_add_left hpq, gt_hd_apply hpq]

lemma sub_hd_lt {p q : mv_polynomial (fin n) α} (h₁ : p.hd = q.hd) (h₂ : p.hd_val = q.hd_val) (hp : p.hd ≠ 0) : 
    (p - q).hd < p.hd := 
begin
    by_cases hpq : p - q = 0,
        simp [hpq], apply lt_of_le_of_ne (finsupp.fin.zero_le p.hd) (ne.symm hp),
    have hab_hd : ∀ (x : (fin n) →₀ ℕ), (x ∈ (p - q).support) → p.hd ≥ x,
        intros x hx, 
        have hx' := mem_sub_support x hx,
        rw [finset.mem_union] at hx', cases hx',
        apply hd_rel' _ hx',
        rw h₁, apply hd_rel' _ hx',
    apply lt_of_le_of_ne (hab_hd (p - q).hd (hd_mem_support hpq)),
    apply finset.ne_of_mem_and_not_mem (hd_mem_support hpq),
    simp [hd_val, h₁] at h₂, simp [h₁, h₂],
end

end comm_ring

section integral_domain
variables [integral_domain α]
lemma hd_of_mul {p : mv_polynomial (fin n) α} : p ≠ 0 → ∀ {a b}, b ≠ 0 → (p * (monomial a b)).hd = p.hd + a := begin
    apply induction p, finish,
    intros q ih hq a b hb,
    have hq' := hd_val_nez_iff.1 hq,
    have hmq := mul_ne_zero hq' hb,
    rw ←hd_tl_eq q,
    by_cases h_tl : q.tl = 0,
    {
        simp [h_tl, -add_comm], generalize hx : (monomial (hd q) (hd_val q) + 0) = x,
        simp at hx, simp [hx.symm, monomial_mul_monomial, hq', hmq],
    },
    have h : q.tl.hd < (monomial (hd q) (hd_val q)).hd,
        simp [hq', lt_iff_le_and_ne], 
        refine ⟨(hd_rel _ _ (hd_mem_support h_tl)), finset.ne_of_mem_and_not_mem (hd_mem_support h_tl) hd_not_mem_tl⟩,
    have h' : (q.tl * monomial a b).hd < ((monomial q.hd q.hd_val) * monomial a b).hd,
        simpa [monomial_mul_monomial, ih h_tl hb, hmq, hq'] using h,
    rw [add_mul, hd_of_add_left h', hd_of_add_left h, monomial_mul_monomial, hd_of_monomial hmq, hd_of_monomial hq'],
end

lemma hd_val_of_mul {p : mv_polynomial (fin n) α} : p ≠ 0 → ∀ {a b}, (p * (monomial a b)).hd_val = p.hd_val * b := begin
    apply induction p, finish,
    intros q ih hq a b,
    by_cases hb : b = 0,
    {rw [monomial_eq_zero_iff.2 hb, hb], simp},
    have hq' := hd_val_nez_iff.1 hq,
    have hmq := mul_ne_zero hq' hb,
    
    rw ←hd_tl_eq q,
    by_cases h_tl : q.tl = 0,
    {
        simp [h_tl, -add_comm], generalize hx : (monomial (hd q) (hd_val q) + 0) = x,
        simp at hx, simp [hx.symm, monomial_mul_monomial],
    },
    have h : q.tl.hd < (monomial (hd q) (hd_val q)).hd,
        simp [hq', lt_iff_le_and_ne], 
        refine ⟨(hd_rel _ _ (hd_mem_support h_tl)), finset.ne_of_mem_and_not_mem (hd_mem_support h_tl) hd_not_mem_tl⟩,
    have h' : (q.tl * monomial a b).hd < ((monomial q.hd q.hd_val) * monomial a b).hd,
        simpa [hd_of_mul h_tl hb, monomial_mul_monomial, hmq, hq'] using h,
    rw [add_mul, hd_val_of_add_left h, hd_val_of_add_left h', monomial_mul_monomial],
    simp,
end

end integral_domain
end fin

end mv_polynomial
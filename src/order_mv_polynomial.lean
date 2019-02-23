import mv_polynomial sorted_list lex_order user_classes

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

def lm (p : mv_polynomial σ α) := p.s_support.head
def lc (p : mv_polynomial σ α) := p p.lm

def tl (p : mv_polynomial σ α) : mv_polynomial σ α := 
⟨(p.support.erase p.lm), λ a, if a = p.lm then 0 else p a, 
λ a, begin
    split; simp_intros, simp [a_1],
    by_cases a = p.lm; finish,
end⟩ 

@[simp] lemma zero_lm : (0 : mv_polynomial σ α).lm = 0 := by finish
@[simp] lemma zero_lc : (0 : mv_polynomial σ α).lc = 0 := by finish
lemma eq_zero_lm {p : mv_polynomial σ α} : p = 0 → p.lm = 0 := by finish

lemma lm_mem_s_support (p : mv_polynomial σ α) (h : p ≠ 0) : p.lm ∈ p.s_support:= begin
    rw [←support_ne_empty, ←finset.sort_ne_nil] at h,
    unfold lm s_support, rw [←list.cons_head_tail h],
    simp,
end

lemma lm_mem_support {p : mv_polynomial σ α} (h : p ≠ 0) : p.lm  ∈ p.support := 
    by rw ←finset.mem_sort (≥); apply lm_mem_s_support _ h

lemma lm_not_mem {p : mv_polynomial σ α} : p.lm ∉ p.support ↔ p = 0 := ⟨λ h, begin
    by_cases hf : p = 0, assumption, 
    apply absurd (lm_mem_support hf) h,
end, λ h, by simp [h]⟩

lemma lm_not_mem_tl {p : mv_polynomial σ α} : p.lm ∉ p.tl.support := by simp [tl]

@[simp] lemma eq_zero_of_div_zero : ∀ p : mv_polynomial σ α, (p.lm ∣ (0 : σ →₀ ℕ)) ↔ p.lm = 0 := 
λ p, by simp [has_dvd.dvd, dvd, eq_zero_apply]

lemma lc_eqz_iff {p : mv_polynomial σ α} : p = 0 ↔ p.lc = 0 := begin
    split; intro h, 
    rw [lc, lm, ←not_mem_support_iff, ←not_mem_s_support],
    simp [h],
    rwa [lc, ←not_mem_support_iff, lm_not_mem] at h,
end

lemma lc_nez_iff {p : mv_polynomial σ α} : p ≠ 0 ↔ p.lc ≠ 0 := 
    by simp [lc_eqz_iff]

lemma lc_nez_of_lm_nez {p : mv_polynomial σ α} : p.lm ≠ 0 → p.lc ≠ 0 := λ h h', h (eq_zero_lm (lc_eqz_iff.2 h'))

lemma singleton_lm {p : mv_polynomial σ α} {a} (h : p.support = {a}) : p.lm = a := by finish [lm, s_support, h]
lemma singleton_eq_monomial {p : mv_polynomial σ α} {a} (h : p.support = {a}) : p = monomial a (p a) := begin
    ext x, 
    by_cases ha : a = x; simp [monomial_apply, ha],
    simp [not_mem_support_iff.symm, h, ne.symm ha],
end

@[simp] lemma lm_of_monomial {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0): (monomial a b).lm = a := 
    by simp [singleton_lm (support_monomial_eq hb)]

@[simp] lemma lm_of_monomial' {b : α} : (monomial 0 b).lm = (0 : σ →₀ ℕ) := 
    begin
        by_cases hb : b = 0, simp [hb],
        simp [singleton_lm (support_monomial_eq hb)],
    end

@[simp] lemma lc_of_monomial {a : σ →₀ ℕ} {b : α} : (monomial a b).lc = b := begin
    by_cases hb : b = 0, simp [hb],
    simp [lc, monomial_apply, singleton_lm (support_monomial_eq hb)], 
end

lemma tl_apply (p : mv_polynomial σ α) : ∀ a ≠ p.lm, p.tl a = p a := 
λ a h, by rw coe_f; finish [tl]

lemma tl_apply_lm (p : mv_polynomial σ α) : p.tl p.lm = 0 := 
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
            intro a, unfold s_support at hp, simp [s_support, lm, tl, -mem_support_iff],
            rw [←finset.mem_sort (≥), ←list.cons_head_tail hp],
            simp [and_or_distrib_left],
            refine ⟨λ h, h.right, λ h, ⟨_, by assumption⟩⟩,
            have nh := finset.sort_nodup (≥) p.support, rw [←list.cons_head_tail hp, list.nodup_cons] at nh,
            intro ha, apply nh.left, rwa ha at h, 
        }
    },
end 

lemma lm_rel (p : mv_polynomial σ α) : ∀ a, a ∈ p.tl.support → p.lm ≥ a := λ a, 
    by rw [←mem_s_support, tl_eq_s_tl, lm]; apply finset.sort_hd_rel

lemma lm_rel_gt (p : mv_polynomial σ α) : ∀ a, a ∈ p.tl.support → p.lm > a := λ a ha, 
begin
    apply lt_of_le_of_ne (lm_rel _ _ ha),
    apply finset.ne_of_mem_and_not_mem ha lm_not_mem_tl,
end

lemma lm_rel' {p : mv_polynomial σ α} : ∀ a, a ∈ p.support → p.lm ≥ a := λ a, 
begin
    by_cases hp : p = 0, simp [hp],
    have h :  insert p.lm p.tl.support = p.support,
        simp [tl, -finset.union_comm], apply finset.insert_erase (lm_mem_support hp),
    simp [h.symm, -mem_support_iff], rintro (h' | h'),
    rw h', apply le_refl,
    apply lm_rel _ a h',
end

lemma gt_lm_not_mem {p : mv_polynomial σ α} : ∀ {x}, x > p.lm → x ∉ p.support := 
λ x hx h_mem, begin
    apply lt_iff_not_ge'.1 hx,
    apply lm_rel' _ h_mem,
end

lemma gt_lm_apply {p : mv_polynomial σ α} : ∀ {x}, x > p.lm → p x = 0 := 
λ x, by rw ←not_mem_support_iff; apply gt_lm_not_mem

lemma cons_lm_tl {p : mv_polynomial σ α} (hp : p ≠ 0) : list.cons p.lm p.tl.s_support = p.s_support := 
    by simp [tl_eq_s_tl, lm]; apply list.cons_head_tail; rwa ne_zero_of_s_ne_nil

lemma lm_tl_eq (p : mv_polynomial σ α) : (monomial p.lm p.lc) + p.tl = p := begin
    ext a, simp [monomial_apply], 
    by_cases ha : p.lm = a; simp [ha],
    simp [lc, ha.symm, tl_apply_lm], 
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
        simp_intros l_lm l_tl ih p hp,
        apply Cₙ, apply ih,
        rw ←cons_lm_tl at hp, simp at hp, exact hp.right,
        rw [←ne_zero_of_s_ne_nil, hp], simp,
    end

lemma mem_support_add_le_lm {p q : mv_polynomial σ α} (hpq : p.lm ≥ q.lm) : ∀ (x : σ →₀ ℕ), (x ∈ (p + q).support) → p.lm ≥ x :=
λ x hx, begin
    have hx' := support_add hx, rw [finset.mem_union] at hx', 
    cases hx',
    apply lm_rel' _ hx',
    apply le_trans (lm_rel' _ hx') hpq,
end

end sort_support

end comm_semiring

section comm_ring
variables [comm_ring α] 

def monomial_ideal (l : list (mv_polynomial σ α)) : ideal (mv_polynomial σ α) := 
    ideal.span ↑(l.map (λ f : mv_polynomial σ α, monomial f.lm f.lc)).to_finset

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
    rcases finset.mem_fold_union (finset.subset.trans h_sub (add_support_subset_union c a' hb')) with ⟨d, ⟨lm, h⟩⟩,
    have h_mul_nez : (c d) * b' ≠ 0,
        apply mul_ne_zero _ hb',
        simpa using lm,
    simp [monomial, single, h_mul_nez, finset.subset_iff] at h,
    apply dvd_of_add h,
end

lemma monomial_mem_ideal {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : ∀ l : list (mv_polynomial σ α), 
    monomial a b ∈ monomial_ideal l → ∃ (p  : mv_polynomial σ α) (hp : p ∈ l ∧ p ≠ 0), p.lm ∣ a
| [] := by simpa [monomial_ideal, ideal.span, monomial_eq_zero_iff] using hb
| (q :: l') := 
λ h_mem, begin
    rcases support_subset_of_linear_combination_union ((list.cons q l').map (λ f : mv_polynomial σ α, monomial f.lm f.lc)).to_finset (by simp) (monomial a b) h_mem
        with ⟨c, ⟨hc, h⟩⟩,
    rw support_monomial_eq hb at h,
    rcases finset.mem_fold_union h with ⟨p, ⟨hp, h'⟩⟩,
    rw [list.mem_to_finset, list.mem_map] at hp,
    rcases hp with ⟨p', ⟨hp', hp⟩⟩,
    simp [hp.symm] at h',
    have lc'_val : p'.lc ≠ 0, intro hp'', simpa [monomial_eq_zero_iff.2 hp'', finset.subset_empty] using h',
    refine ⟨p', ⟨⟨hp', by rwa lc_nez_iff⟩, _⟩⟩, 
    apply mem_mul_support hb lc'_val; assumption,
end

end integral_domain

end decidable_linear_order

section fin
variables {n : ℕ}
section comm_semiring
variables [comm_semiring α]

lemma singleton_of_lm_eqz {p : mv_polynomial (fin n) α} : p ≠ 0 ∧ p.lm = 0 ↔ p.support = {0} := 
⟨λ h, begin
    have h' := cons_lm_tl h.left,
    ext a, simp [mem_s_support.symm, h'.symm, h.right],
    split; intro ha,
    {
        cases ha, exact ha,
        apply absurd (finsupp.fin.zero_le a),
        rw ←h.right,
        apply not_le_of_lt,
        apply lm_rel_gt p a (by rwa mem_s_support at ha),
    },
    left, exact ha,
end, λ h, ⟨λ h', @finset.ne_empty_of_mem ((fin n) →₀ ℕ) 0 p.support (by simp [h]) (by simp [h']), singleton_lm h⟩⟩

lemma eqC_of_lm_eqz {p : mv_polynomial (fin n) α} : p.lm = 0 ↔ p = C (p 0) := 
⟨λ h, begin
    by_cases hp : p = 0, rw hp, simp,
    simp [C],
    apply singleton_eq_monomial (singleton_of_lm_eqz.1 ⟨hp, h⟩),
end,
λ h, by rw [h, C]; simp⟩

lemma lm_is_const_iff {p : mv_polynomial (fin n) α} : p = 0 ∨ p.support = {0} ↔ p.lm = 0 := 
⟨λ h, begin 
    cases h, simp [h],
    apply singleton_lm h,
end, λ h, begin 
    by_cases hp : p = 0, 
    left, exact hp,
    right, apply singleton_of_lm_eqz.1 ⟨hp, h⟩,
end⟩

lemma not_const_iff {p : mv_polynomial (fin n) α} : p ≠ 0 ∧ p.support ≠ {0} ↔ p.lm ≠ 0:= 
⟨λ h, by rwa [←not_or_distrib, lm_is_const_iff] at h, λ h, by rwa [←not_or_distrib, lm_is_const_iff]⟩


end comm_semiring

section comm_ring
variables [comm_ring α]

lemma lm_of_add_left {p q : mv_polynomial (fin n) α} (hpq : p.lm > q.lm) :
    (p + q).lm = p.lm := 
begin
    have hp_lm := mem_support_add_le_lm (le_of_lt hpq),
    apply (antisymm (hp_lm _ (lm_mem_support (λ h, _))) (lm_rel' _ _)).symm,
    have h' := (eq_zero_apply _).2 h p.lm, revert h',
    all_goals {
        simp [gt_lm_apply hpq], rw [←not_mem_support_iff, lm_not_mem],
        intros h,
        simp [h] at hpq,
        apply (not_lt_of_le (finsupp.fin.zero_le q.lm)) hpq,
    },
end

lemma lc_of_add_left {p q : mv_polynomial (fin n) α} (hpq : p.lm > q.lm) :
    (p + q).lc = p.lc := 
by simp [lc, lm_of_add_left hpq, gt_lm_apply hpq]

lemma sub_lm_lt {p q : mv_polynomial (fin n) α} (h₁ : p.lm = q.lm) (h₂ : p.lc = q.lc) (hp : p.lm ≠ 0) : 
    (p - q).lm < p.lm := 
begin
    by_cases hpq : p - q = 0,
        simp [hpq], apply lt_of_le_of_ne (finsupp.fin.zero_le p.lm) (ne.symm hp),
    have hab_lm : ∀ (x : (fin n) →₀ ℕ), (x ∈ (p - q).support) → p.lm ≥ x,
        intros x hx, 
        have hx' := mem_sub_support x hx,
        rw [finset.mem_union] at hx', cases hx',
        apply lm_rel' _ hx',
        rw h₁, apply lm_rel' _ hx',
    apply lt_of_le_of_ne (hab_lm (p - q).lm (lm_mem_support hpq)),
    apply finset.ne_of_mem_and_not_mem (lm_mem_support hpq),
    simp [lc, h₁] at h₂, simp [h₁, h₂],
end

end comm_ring

section integral_domain
variables [integral_domain α]
lemma lm_of_mul {p : mv_polynomial (fin n) α} : p ≠ 0 → ∀ {a b}, b ≠ 0 → (p * (monomial a b)).lm = p.lm + a := begin
    apply induction p, finish,
    intros q ih hq a b hb,
    have hq' := lc_nez_iff.1 hq,
    have hmq := mul_ne_zero hq' hb,
    rw ←lm_tl_eq q,
    by_cases h_tl : q.tl = 0,
    {
        simp [h_tl, -add_comm], generalize hx : (monomial (lm q) (lc q) + 0) = x,
        simp at hx, simp [hx.symm, monomial_mul_monomial, hq', hmq],
    },
    have h : q.tl.lm < (monomial (lm q) (lc q)).lm,
        simp [hq', lt_iff_le_and_ne], 
        refine ⟨(lm_rel _ _ (lm_mem_support h_tl)), finset.ne_of_mem_and_not_mem (lm_mem_support h_tl) lm_not_mem_tl⟩,
    have h' : (q.tl * monomial a b).lm < ((monomial q.lm q.lc) * monomial a b).lm,
        simpa [monomial_mul_monomial, ih h_tl hb, hmq, hq'] using h,
    rw [add_mul, lm_of_add_left h', lm_of_add_left h, monomial_mul_monomial, lm_of_monomial hmq, lm_of_monomial hq'],
end

lemma lc_of_mul {p : mv_polynomial (fin n) α} : p ≠ 0 → ∀ {a b}, (p * (monomial a b)).lc = p.lc * b := begin
    apply induction p, finish,
    intros q ih hq a b,
    by_cases hb : b = 0,
    {rw [monomial_eq_zero_iff.2 hb, hb], simp},
    have hq' := lc_nez_iff.1 hq,
    have hmq := mul_ne_zero hq' hb,
    
    rw ←lm_tl_eq q,
    by_cases h_tl : q.tl = 0,
    {
        simp [h_tl, -add_comm], generalize hx : (monomial (lm q) (lc q) + 0) = x,
        simp at hx, simp [hx.symm, monomial_mul_monomial],
    },
    have h : q.tl.lm < (monomial (lm q) (lc q)).lm,
        simp [hq', lt_iff_le_and_ne], 
        refine ⟨(lm_rel _ _ (lm_mem_support h_tl)), finset.ne_of_mem_and_not_mem (lm_mem_support h_tl) lm_not_mem_tl⟩,
    have h' : (q.tl * monomial a b).lm < ((monomial q.lm q.lc) * monomial a b).lm,
        simpa [lm_of_mul h_tl hb, monomial_mul_monomial, hmq, hq'] using h,
    rw [add_mul, lc_of_add_left h, lc_of_add_left h', monomial_mul_monomial],
    simp,
end

end integral_domain
end fin

end mv_polynomial
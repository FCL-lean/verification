import mv_polynomial sorted_list finsupp_pos user_classes

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

def LM (p : mv_polynomial σ α) := p.s_support.head
def LC (p : mv_polynomial σ α) := p p.LM
def LT (p : mv_polynomial σ α) := monomial p.LM p.LC

def TL (p : mv_polynomial σ α) : mv_polynomial σ α := 
⟨(p.support.erase p.LM), λ a, if p.LM = a then 0 else p a, 
λ a, ⟨λ h, by simp at h; simp [ne.symm h.left, h.right], λ h, by by_cases p.LM = a; finish⟩⟩

@[simp] lemma zero_LM : (0 : mv_polynomial σ α).LM = 0 := by finish
@[simp] lemma zero_LC : (0 : mv_polynomial σ α).LC = 0 := by finish
@[simp] lemma zero_LT : (0 : mv_polynomial σ α).LT = 0 := by finish [LT]
@[simp] lemma zero_TL : (0 : mv_polynomial σ α).TL = 0 := by simp [TL]

lemma LM_mem_support {p : mv_polynomial σ α} (h : p ≠ 0) : p.LM  ∈ p.support := 
begin 
    rw ←finset.mem_sort ((≥) : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop), 
    rw [←support_ne_empty, ←finset.sort_ne_nil] at h,
    rw [←list.cons_head_tail h],
    simp [LM, s_support],
end

lemma LM_not_mem {p : mv_polynomial σ α} : p.LM ∉ p.support ↔ p = 0 := ⟨λ h, begin
    by_cases hf : p = 0, assumption, 
    apply absurd (LM_mem_support hf) h,
end, λ h, by simp [h]⟩

lemma LM_not_mem_TL {p : mv_polynomial σ α} : p.LM ∉ p.TL.support := by simp [TL]

@[simp] lemma eq_zero_of_div_zero : ∀ p : mv_polynomial σ α, (p.LM ∣ (0 : σ →₀ ℕ)) ↔ p.LM = 0 := 
λ p, by simp [has_dvd.dvd, dvd, eq_zero_apply]; apply finsupp.eq_zero_apply

lemma LC_eqz_iff {p : mv_polynomial σ α} : p = 0 ↔ p.LC = 0 := begin
    split; intro h, 
    rw [LC, LM, ←not_mem_support_iff, ←not_mem_s_support],
    simp [h],
    rwa [LC, ←not_mem_support_iff, LM_not_mem] at h,
end

lemma LC_nez_iff {p : mv_polynomial σ α} : p ≠ 0 ↔ p.LC ≠ 0 := 
    by simp [LC_eqz_iff]

lemma LC_nez_of_LM_nez {p : mv_polynomial σ α} : p.LM ≠ 0 → p.LC ≠ 0 := λ h h', h (by simp [LC_eqz_iff.2 h'])
lemma nez_of_LM_nez {p : mv_polynomial σ α} : p.LM ≠ 0 → p ≠ 0 := λ h, LC_nez_iff.2 (LC_nez_of_LM_nez h)

lemma singleton_LM {p : mv_polynomial σ α} {a} (h : p.support = {a}) : p.LM = a := by finish [LM, s_support, h]
lemma singleton_eq_monomial {p : mv_polynomial σ α} {a} (h : p.support = {a}) : p = monomial a (p a) := begin
    ext x, 
    by_cases ha : a = x; simp [monomial_apply, ha],
    simp [not_mem_support_iff.symm, h, ne.symm ha],
end

@[simp] lemma LM_of_monomial {a : σ →₀ ℕ} {b : α} : (monomial a b).LM = ite (b = 0) 0 a := 
begin
    by_cases b = 0,
    {simp [h]},
    {simp [h, singleton_LM (support_monomial_eq h)]},
end

lemma eq_LM_of_monomial (a : σ →₀ ℕ) {b : α} (hb : b ≠ 0) : a = (monomial a b).LM := by simp [hb]

@[simp] lemma LM_of_monomial' {b : α} : (monomial 0 b).LM = (0 : σ →₀ ℕ) := 
    begin
        by_cases hb : b = 0, simp [hb],
        simp [singleton_LM (support_monomial_eq hb)],
    end

@[simp] lemma LC_of_monomial {a : σ →₀ ℕ} {b : α} : (monomial a b).LC = b := begin
    by_cases hb : b = 0, simp [hb],
    simp [LC, monomial_apply, singleton_LM (support_monomial_eq hb)], 
end

@[simp] lemma LT_apply {p : mv_polynomial σ α} : ∀ a, p.LT a = ite (p.LM = a) p.LC 0 :=
by rw LT; simp [monomial_apply]

lemma LT_mul_monomial {p : mv_polynomial σ α} : ∀ {a b}, p.LT * monomial a b = monomial (p.LM + a) (p.LC * b) :=
by simp [LT, monomial_mul_monomial]

@[simp] lemma LM_of_LT {p : mv_polynomial σ α} : p.LT.LM = p.LM := begin
    by_cases p = 0,
    {simp [LT, h]},
    {simp [LT, LC_nez_iff.1 h]},
end

@[simp] lemma LC_of_LT {p : mv_polynomial σ α} : p.LT.LC = p.LC := by simp [LT]

@[simp] lemma LT_of_monomial {a : σ →₀ ℕ} {b : α} : (monomial a b).LT = monomial a b :=
by by_cases hb : b = 0; simp [LT, hb]

lemma LM_eq_of_LT_eq {p q : mv_polynomial σ α} : p.LT = q.LT → p.LM = q.LM :=
λ h, begin have h' : p.LT.LM = q.LT.LM := by simp [h], simpa using h', end

lemma LC_eq_of_LT_eq {p q : mv_polynomial σ α} : p.LT = q.LT → p.LC = q.LC :=
λ h, begin have h' : p.LT.LC = q.LT.LC := by simp [h], simpa using h', end

lemma LT_eq_iff_LM_LC_eq {p q : mv_polynomial σ α} : p.LT = q.LT ↔ p.LM = q.LM ∧ p.LC = q.LC :=
⟨λ h, ⟨LM_eq_of_LT_eq h, LC_eq_of_LT_eq h⟩, 
λ h, by simp [LT, h.left, h.right]⟩    

@[simp] lemma TL_apply {p : mv_polynomial σ α} : ∀ a, p.TL a = ite (p.LM = a) 0 (p a) :=
λ a, by rw [TL, coe_f]

lemma TL_support_subset {p : mv_polynomial σ α} : p.TL.support ⊆ p.support :=
by simp [TL]; apply finset.erase_subset

lemma mem_TL_support {p : mv_polynomial σ α} {a} : a ≠ p.LM → a ∈ p.support → a ∈ p.TL.support :=
λ h₁ h₂, by simp [TL]; use [h₁, by simpa using h₂]

lemma TL_apply_mem {p : mv_polynomial σ α} : ∀ {a}, a ∈ p.TL.support → p.TL a = p a :=
λ a h, by simp [ne.symm (finset.ne_of_mem_and_not_mem h LM_not_mem_TL)]

@[simp] lemma TL_of_monomial {a : σ →₀ ℕ} {b : α}: (monomial a b).TL = 0 :=
begin
    by_cases hb : b = 0,
    simp [hb, TL],
    ext x,
    by_cases a = x, 
    {simp [h, hb]},
    {simp [h, monomial_apply]},
end

lemma TL_eq_s_TL {p : mv_polynomial σ α} : p.TL.s_support = p.s_support.tail := begin
    by_cases hp : s_support p = [], 
    {simp [hp, TL, support_empty_of_s_nil.1 hp],},
    {
        apply @list.sorted_nodup_ext (σ →₀ ℕ) (≥) _,
        {simp [s_support]},
        {apply list.sorted_tail, simp [s_support]},
        {simp [s_support],},
        {apply @list.nodup_of_nodup_cons _ p.s_support.head, rw list.cons_head_tail hp, simp [s_support],},
        {
            intro a, unfold s_support at hp, simp [s_support, LM, TL, -mem_support_iff],
            rw [←finset.mem_sort (≥), ←list.cons_head_tail hp],
            simp [and_or_distrib_left],
            refine ⟨λ h, h.right, λ h, ⟨_, by assumption⟩⟩,
            have nh := finset.sort_nodup (≥) p.support, rw [←list.cons_head_tail hp, list.nodup_cons] at nh,
            intro ha, apply nh.left, rwa ha at h, 
        }
    },
end 

lemma LM_rel {p : mv_polynomial σ α} : ∀ {a}, a ∈ p.TL.support → p.LM ≥ a := λ a, 
    by rw [←mem_s_support, TL_eq_s_TL, LM]; apply finset.sort_hd_rel

lemma LM_rel_gt {p : mv_polynomial σ α} : ∀ {a}, a ∈ p.TL.support → p.LM > a := λ a ha, 
begin
    apply lt_of_le_of_ne (LM_rel ha),
    apply finset.ne_of_mem_and_not_mem ha LM_not_mem_TL,
end

lemma LM_rel' {p : mv_polynomial σ α} : ∀ {a}, a ∈ p.support → p.LM ≥ a := λ a, 
begin
    by_cases hp : p = 0, simp [hp],
    have h :  insert p.LM p.TL.support = p.support,
        simp [TL, -finset.union_comm], apply finset.insert_erase (LM_mem_support hp),
    simp [h.symm, -mem_support_iff], rintro (h' | h'),
    rw h', apply le_refl,
    apply LM_rel h',
end

lemma gt_LM_not_mem {p : mv_polynomial σ α} : ∀ {x}, x > p.LM → x ∉ p.support := 
λ x hx h_mem, begin
    apply lt_iff_not_ge'.1 hx,
    apply LM_rel' h_mem,
end

lemma gt_LM_apply {p : mv_polynomial σ α} : ∀ {x}, x > p.LM → p x = 0 := 
λ x, by rw ←not_mem_support_iff; apply gt_LM_not_mem

lemma cons_LM_TL {p : mv_polynomial σ α} (hp : p ≠ 0) : list.cons p.LM p.TL.s_support = p.s_support := 
    by simp [TL_eq_s_TL, LM]; apply list.cons_head_tail; rwa ne_zero_of_s_ne_nil

lemma LM_TL_eq (p : mv_polynomial σ α) : p.LT + p.TL = p := begin
    ext a, simp [monomial_apply], 
    by_cases ha : p.LM = a, 
    {simp [LC, ha, TL_apply]},
    {simp [ha]},
end

@[elab_as_eliminator]
theorem induction {C : (mv_polynomial σ α) → Prop} (p : mv_polynomial σ α) 
    (C₀ : C 0)
    (Cₙ : ∀ (p : mv_polynomial σ α), C p.TL → C p) : C p := 
    suffices ∀ l (p : mv_polynomial σ α), p.s_support = l → C p, from this _ _ rfl,
    λ l, @list.rec_on _ (λ l, (∀ p : mv_polynomial σ α, p.s_support = l → C p)) l
    (λ p hp, by rw eq_zero_of_s_nil at hp; rwa hp) 
    begin
        simp_intros l_LM l_TL ih p hp,
        apply Cₙ, apply ih,
        rw ←cons_LM_TL at hp, simp at hp, exact hp.right,
        rw [←ne_zero_of_s_ne_nil, hp], simp,
    end

end sort_support

end comm_semiring

section comm_ring
variables [comm_ring α] 
@[simp] lemma LM_neg {p : mv_polynomial σ α} : (-p).LM = p.LM := by simp [LM, s_support]
@[simp] lemma LC_neg {p : mv_polynomial σ α} : (-p).LC = -(p.LC) := by simp [LC]
@[simp] lemma monomial_neg {a : σ →₀ ℕ} {b : α} : monomial a (-b) = -(monomial a b) := 
begin
    ext x,
    by_cases a = x;
    simp [h, monomial_apply],
end

def monomial_ideal (l : list (mv_polynomial σ α)) : ideal (mv_polynomial σ α) := 
    ideal.span ↑(l.map (λ f : mv_polynomial σ α, f.LT)).to_finset

lemma support_subset_of_linear_combination_union (s : finset (mv_polynomial σ α)) : 
    ∀ (p : mv_polynomial σ α) (hp₁ : p ∈ ideal.span (↑s : set (mv_polynomial σ α))),
    ∃ (c : ((mv_polynomial σ α) →₀ (mv_polynomial σ α))), c.support ⊆ s ∧ p.support ⊆ s.fold (∪) (∅) (λ a, ((c.to_fun a) * a).support) :=
begin
    apply finset.induction_on s, 
    {simp [ideal.span], refine ⟨0, by simp⟩},
    {
        intros q s hqs ih p hp,
        simp [finset.coe_insert, ideal.mem_span_insert] at hp ⊢,
        rcases hp with ⟨a, z, hz, hp⟩,
        rcases ih z hz with ⟨c, hc, hz'⟩,
        refine ⟨single q a + c, finset.subset.trans support_add (finset.union_subset' support_single_subset hc), _⟩,
        
        have hc_app : c q = 0, 
            {rw [←not_mem_support_iff], exact finset.not_mem_subset_of_not_mem hc hqs},
        have h_congr : ∀ x ∈ s, ((single q a + c) x * x).support  = (c x * x).support := 
            λ x hx, by simp [single_apply, ne.symm (finset.ne_of_mem_and_not_mem hx hqs)],
        simp at h_congr,
        simp [coe_f', (finset.fold_congr h_congr), hp, hc_app] at hz' ⊢,
        apply finset.subset.trans support_add (finset.union_subset'_symm hz' (finset.subset.refl _)),
    }
end

end comm_ring

section integral_domain
variables [integral_domain α]

lemma mem_mul_support {a a': σ →₀ ℕ} {b': α} (hb' : b' ≠ 0) (c : mv_polynomial σ α) 
(h : a ∈ (c * (monomial a' b')).support) : a' ∣ a := begin
    simp [has_mul.mul, monomial, single_sum' a' hb'] at h,
    simp [finsupp.sum, single_apply] at h,
    have h' : ∃ x ∈ c.support, a' + x = a,
    {
        by_contradiction h',
        simp [not_exists, -finsupp.mem_support_iff] at h',
        exact h (finset.sum_eq_zero (λ x hx, by simp [h' x hx])),
    },
    rcases h' with ⟨_, _, h'⟩,
    exact dvd_of_add (by rwa eq_comm at h'),
end

set_option class.instance_max_depth 50
theorem monomial_mem_ideal {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : ∀ l : list (mv_polynomial σ α), 
    monomial a b ∈ monomial_ideal l → ∃ (p  : mv_polynomial σ α) (hp : p ∈ l ∧ p ≠ 0), p.LM ∣ a
| [] := by simpa [monomial_ideal, ideal.span, monomial_eq_zero_iff] using hb
| (q :: l') := 
λ h_mem, begin
    rcases support_subset_of_linear_combination_union ((list.cons q l').map (λ f : mv_polynomial σ α, f.LT)).to_finset (monomial a b) h_mem with ⟨c, hc, h⟩,
    rw support_monomial_eq hb at h,
    rcases finset.mem_fold_union h with ⟨p, hp, h'⟩,
    rw [list.mem_to_finset, list.mem_map] at hp,
    rcases hp with ⟨p', hp'₁, hp'₂⟩,
    have hp' : p' ≠ 0 := λ hp', by simpa [hp', hp'₂.symm, finset.subset_empty] using h',
    refine ⟨p', ⟨hp'₁, hp'⟩, mem_mul_support (LC_nez_iff.1 hp') (c.to_fun p'.LT) (by simpa [hp'₂.symm] using h' (finset.mem_singleton_self _))⟩,
end

end integral_domain

end decidable_linear_order

section well_order
variables [decidable_linear_order (σ →₀ ℕ)] [is_well_founded (σ →₀ ℕ) (<)] [is_monomial_order (σ →₀ ℕ) (≤)] 
section comm_semiring
variables [comm_semiring α]
lemma TL_eqz_of_LM_eqz {p : mv_polynomial σ α} (h : p.LM = 0) : p.TL = 0 :=
begin
    by_contradiction,
    apply (not_lt_of_le (finsupp.zero_le p.TL.LM)),
    simpa [h] using LM_rel_gt (LM_mem_support a),
end

lemma gt_TL_LM_of_LM_nez {p : mv_polynomial σ α} (h : p.LM ≠ 0) : p.LM > p.TL.LM :=
begin
    by_cases hTL : p.TL = 0,
    {simp [hTL], apply finsupp.zero_lt_iff_ne_zero.2 h},
    {apply LM_rel_gt (LM_mem_support hTL)},
end

lemma eqC_of_LM_eqz {p : mv_polynomial σ α} : p.LM = 0 ↔ p = C (p.LC) := 
⟨λ h, begin
    by_cases hp : p = 0, 
    {rw hp, simp},
    {
        conv {to_lhs, rw [←LM_TL_eq p, LT, h]},
        simp [C, TL_eqz_of_LM_eqz h],
    }
end,
λ h, by rw [h, C]; simp⟩

end comm_semiring

section comm_ring
variables [comm_ring α]

lemma LM_of_add_left {p q : mv_polynomial σ α} (hpq : p.LM > q.LM) :
    (p + q).LM = p.LM := 
begin
    have hp : p.LM > 0 := gt_of_gt_of_ge hpq (finsupp.zero_le q.LM),
    have h : (p + q).LM ≥ p.LM := 
        LM_rel' (by simpa [gt_LM_apply hpq] using LM_mem_support (nez_of_LM_nez (ne_of_gt hp))),
        have : (p + q).LM ∈ p.support ∨ (p + q).LM ∈ q.support := 
        finset.mem_union.1 (finset.mem_of_subset support_add (LM_mem_support (nez_of_LM_nez (ne_of_gt $ gt_of_ge_of_gt h hp)))),
    cases this,
    {apply antisymm h (LM_rel' this),},
    {apply antisymm h (le_trans (LM_rel' this) (le_of_lt hpq))},
end

lemma LM_of_add_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p + q).LM = q.LM := 
by rw [add_comm, LM_of_add_left hpq]

lemma LC_of_add_left {p q : mv_polynomial σ α} (hpq : p.LM > q.LM) :
    (p + q).LC = p.LC := 
by simp [LC, LM_of_add_left hpq, gt_LM_apply hpq]

lemma LC_of_add_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p + q).LC = q.LC := 
by rw [add_comm, LC_of_add_left hpq]

lemma LT_of_add_left {p q : mv_polynomial σ α} (hpq : p.LM > q.LM) :
    (p + q).LT = p.LT :=
by simp [LT, LM_of_add_left hpq, LC_of_add_left hpq]

lemma LT_of_add_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p + q).LT = q.LT :=
by simp [LT, LM_of_add_right hpq, LC_of_add_right hpq]

theorem sub_LM_lt {p q : mv_polynomial σ α} (h : p.LT = q.LT) (hp : p.LM ≠ 0) : 
    (p - q).LM < p.LM := 
begin
    by_cases hpq : p - q = 0,
    {simpa [hpq, finsupp.zero_lt_iff_ne_zero] using hp},
    {
        simp [LT, monomial, single_eq_single_iff, LC_nez_of_LM_nez hp] at h,
        apply lt_of_le_of_ne,
        {
            cases finset.mem_union.1 (support_sub (LM_mem_support hpq)),
            {exact LM_rel' h_1},
            {rw h.left, exact LM_rel' h_1},
        },
        {
            apply finset.ne_of_mem_and_not_mem (LM_mem_support hpq),       
            simpa [LC, h.left, add_neg_eq_zero] using h.right,
        },
    }
end

theorem LM_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM) 
{b : α} (hb : b ≠ 0) : (monomial a b + p).LM = a := 
begin
    rw eq_LM_of_monomial a hb at ha,
    simp [LM_of_add_right ha, hb],
end

theorem LC_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM) 
{b : α} (hb : b ≠ 0) : (monomial a b + p).LC = b := 
begin
    rw eq_LM_of_monomial a hb at ha,
    simp [LC_of_add_right ha],
end

theorem LT_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM) 
{b : α} (hb : b ≠ 0) : (monomial a b + p).LT = monomial a b :=
by rw [LT, LM_of_add_gt_LM ha hb, LC_of_add_gt_LM ha hb]

theorem TL_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM)
{b : α} (hb : b ≠ 0) : (monomial a b + p).TL = p :=
begin
    have h := LM_TL_eq (monomial a b + p),
    rw [LT, LM_of_add_gt_LM ha hb, LC_of_add_gt_LM ha hb] at h,
    apply add_left_cancel h,
end

end comm_ring

section integral_domain
variables [integral_domain α]

lemma mul_mem_mul_support {a₂ a₁: σ →₀ ℕ} {b₁: α} (hb : b₁ ≠ 0) (c : mv_polynomial σ α) 
(ha : a₂ ∈ c.support) : a₁ + a₂ ∈ (monomial a₁ b₁ * c).support :=
begin
    simp [has_mul.mul, monomial, single_sum' a₁ hb],
    simp [finsupp.sum, single_apply],
    rw [add_comm, finset.sum_eq_single a₂],
    {simp, exact mul_ne_zero hb (by simpa using ha)},
    {intros _ _ h, simp [add_right_cancel_iff, h]},
    {finish},
end

lemma mul_apply {p : mv_polynomial σ α} :
∀ {a₁ a₂ b₁}, a₂ ∈ p.support → (monomial a₁ b₁ * p) (a₁ + a₂) = b₁ * p a₂ :=
λ a₁ a₂ b₁ ha₂, begin
    by_cases hb₁ : b₁ = 0,
    {simp [coe_f, hb₁], simp [coe_f']},
    {
        conv {
            to_lhs,
            simp [coe_f, has_mul.mul, monomial, single_sum' a₁ hb₁], 
            simp [coe_f', finsupp.sum_apply, single_apply],
            simp [finsupp.sum],
        },
        rw finset.sum_eq_single a₂,
        {simp, refl},
        {intros b hb h, simp [h]},
        {
            simp_intros h,
            change b₁ * (p a₂) = 0,
            simp [h],
        }
    }
end

theorem LM_of_mul_m {p : mv_polynomial σ α} : ∀ {a b}, (p * (monomial a b)).LM = ite (p = 0 ∨ b = 0) 0 (p.LM + a) := 
λ a b, begin
    by_cases hp : p = 0,
    {simp [hp]},
    by_cases hb : b = 0,
    {simp [hb]},
    revert hp, apply induction p, 
    {simp},
    {
        simp_intros q ih hq [hb],
        conv {to_lhs, rw [←LM_TL_eq q, add_mul]},
        by_cases hq' : q.TL = 0,
        {simp [hq', LT_mul_monomial, hb, hq, LC_nez_iff.1 hq]},
        {
            have h : (q.TL * monomial a b).LM < (q.LT * monomial a b).LM,
            {
                simp [LT_mul_monomial, hb, LC_nez_iff.1 hq, ih hq', hq'],
                apply gt_TL_LM_of_LM_nez (λ h, hq' (TL_eqz_of_LM_eqz h)),
            },
            rw LM_of_add_left h,
            simp [LT_mul_monomial, hb, hq, LC_nez_iff.1 hq],
        }
    }
end

theorem LC_of_mul_m {p : mv_polynomial σ α} : ∀ {a b}, (p * (monomial a b)).LC = p.LC * b := 
λ a b, begin
    apply induction p, 
    {simp},
    {
        intros q ih,
        by_cases hb : b = 0,
        {simp [hb]},
        {
            conv {to_lhs, rw [←LM_TL_eq q, add_mul]},
            by_cases hq : q.TL = 0,
            {simp [hq, LT_mul_monomial]},
            {
                have hq' : q.LT ≠ 0 := nez_of_LM_nez (λ h, hq (TL_eqz_of_LM_eqz (by simpa using h))),
                have h : (q.TL * monomial a b).LM < (q.LT * monomial a b).LM,
                {
                    simp [LM_of_mul_m, hq, hq', hb],
                    apply gt_TL_LM_of_LM_nez (λ h, hq (TL_eqz_of_LM_eqz h)),
                },
                rw LC_of_add_left h,
                simp [LT_mul_monomial],
            }
        }
    }
end

theorem LT_of_mul_m {p : mv_polynomial σ α} : ∀ {a b}, (p * (monomial a b)).LT = p.LT * (monomial a b) := 
λ a b, begin
    by_cases hp : p = 0; by_cases hb : b = 0;
    simp [LM_of_mul_m, LC_of_mul_m, hp, hb, monomial_mul_monomial, LT],
end

end integral_domain
end well_order

end mv_polynomial
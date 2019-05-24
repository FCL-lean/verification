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
⟨(p.support.erase p.LM), λ a, if a = p.LM then 0 else p a, 
λ a, begin
    split; simp_intros, simp [a_1],
    by_cases a = p.LM; finish,
end⟩ 

@[simp] lemma zero_LM : (0 : mv_polynomial σ α).LM = 0 := by finish
@[simp] lemma zero_LC : (0 : mv_polynomial σ α).LC = 0 := by finish
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

@[simp] lemma LM_of_monomial {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0): (monomial a b).LM = a := 
    by simp [singleton_LM (support_monomial_eq hb)]

@[simp] lemma LM_of_monomial' {b : α} : (monomial 0 b).LM = (0 : σ →₀ ℕ) := 
    begin
        by_cases hb : b = 0, simp [hb],
        simp [singleton_LM (support_monomial_eq hb)],
    end

@[simp] lemma LC_of_monomial {a : σ →₀ ℕ} {b : α} : (monomial a b).LC = b := begin
    by_cases hb : b = 0, simp [hb],
    simp [LC, monomial_apply, singleton_LM (support_monomial_eq hb)], 
end

lemma TL_support_subset {p : mv_polynomial σ α} : p.TL.support ⊆ p.support :=
by simp [TL]; apply finset.erase_subset

lemma TL_apply (p : mv_polynomial σ α) : ∀ a ≠ p.LM, p.TL a = p a := 
λ a h, by rw coe_f; finish [TL]

lemma TL_apply_LM (p : mv_polynomial σ α) : p.TL p.LM = 0 := 
    by rw ←not_mem_support_iff; simp [TL]

lemma mem_TL_support {p : mv_polynomial σ α} {a} : a ≠ p.LM → a ∈ p.support → a ∈ p.TL.support :=
λ h₁ h₂, by simp [TL]; use [h₁, by simpa using h₂]

lemma TL_apply_mem {p : mv_polynomial σ α} : ∀ {a}, a ∈ p.TL.support → p.TL a = p a :=
λ a h, TL_apply p a (λ h', by simp [h'] at h; apply h (TL_apply_LM _))

@[simp] lemma TL_of_monomial {a : σ →₀ ℕ} {b : α}: (monomial a b).TL = 0 :=
begin
    by_cases hb : b = 0,
    simp [hb, TL],
    ext x,
    by_cases x = a;
    rw ←@LM_of_monomial _ _ _ _ _ _ a _ hb at h,
    {simp [h, TL_apply_LM]},
    {
        simp [TL_apply _ _ h, monomial_apply],
        simp [hb] at h, 
        simp [ne.symm h],
    }
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

lemma LM_TL_eq (p : mv_polynomial σ α) : (monomial p.LM p.LC) + p.TL = p := begin
    ext a, simp [monomial_apply], 
    by_cases ha : p.LM = a; simp [ha],
    simp [LC, ha.symm, TL_apply_LM], 
    exact (TL_apply p _ (ne.symm ha)),
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
    ideal.span ↑(l.map (λ f : mv_polynomial σ α, monomial f.LM f.LC)).to_finset

lemma support_subset_of_linear_combination_union (s : finset (mv_polynomial σ α)) : 
    ∀ (hs: s ≠ ∅) (p : mv_polynomial σ α) (hp₁ : p ∈ ideal.span (↑s : set (mv_polynomial σ α))),
    ∃ (c : ((mv_polynomial σ α) →₀ (mv_polynomial σ α))), c.support ⊆ s ∧ p.support ⊆ s.fold (∪) (∅) (λ a, ((c.to_fun a) * a).support) :=
begin
    apply finset.induction_on s, finish,
    intros a s' has' ih hs p hp,
    rw [finset.coe_insert, ideal.mem_span_insert] at hp,
    rcases hp with ⟨a', z, hz, hp⟩,
    by_cases hs' : s' = ∅,
    {
        refine ⟨single a a', _⟩,
        simp [hs', ideal.span, finset.insert_eq, single, hp] at hz ⊢, 
        by_cases ha' : a' = 0;
        simp [ha', hz],
    },
    {
        rcases ih hs' z hz with ⟨zc, hzc, hz'⟩,
        refine ⟨single a a' + zc, finset.subset.trans support_add (finset.union_subset' support_single_subset hzc), _⟩,
        
        have hzc_app : zc a = 0, rw [←not_mem_support_iff], intro hazc, exact has' (hzc hazc),
        have h_congr : ∀ x ∈ s', (λ x, (zc x * x).support) x = (λ x, ((single a a' + zc) x * x).support) x,
            intros x hx, simp [single_apply, ne.symm (finset.ne_of_mem_and_not_mem hx has')],

        simp only [coe_f'] at hz' ⊢,
        simp [(finset.fold_congr h_congr).symm, hp, -add_apply],
        apply finset.subset.trans support_add (finset.union_subset' hz' _),
        conv {to_rhs, simp [hzc_app]}, simp,
    }
end

end comm_ring

section integral_domain
variables [integral_domain α]
lemma mem_mul_support {a a': σ →₀ ℕ} {b': α} (hb' : b' ≠ 0) (c : mv_polynomial σ α) 
(h_sub : {a} ⊆ (c * (monomial a' b')).support) : a' ∣ a := begin
    simp [has_mul.mul, monomial, single_sum' a' hb'] at h_sub,
    simp [finsupp.sum, finset.sum_eq_fold] at h_sub,
    rcases finset.mem_fold_union (finset.subset.trans h_sub (add_support_subset_union c a' hb')) with ⟨d, ⟨LM, h⟩⟩,
    have h_mul_nez : (c d) * b' ≠ 0 := mul_ne_zero (by simpa using LM) hb',
    apply dvd_of_add (by simpa [monomial, single, h_mul_nez, finset.subset_iff] using h),
end

theorem monomial_mem_ideal {a : σ →₀ ℕ} {b : α} (hb : b ≠ 0) : ∀ l : list (mv_polynomial σ α), 
    monomial a b ∈ monomial_ideal l → ∃ (p  : mv_polynomial σ α) (hp : p ∈ l ∧ p ≠ 0), p.LM ∣ a
| [] := by simpa [monomial_ideal, ideal.span, monomial_eq_zero_iff] using hb
| (q :: l') := 
λ h_mem, begin
    rcases support_subset_of_linear_combination_union ((list.cons q l').map (λ f : mv_polynomial σ α, monomial f.LM f.LC)).to_finset (by simp) (monomial a b) h_mem
        with ⟨c, hc, h⟩,
    rw support_monomial_eq hb at h,
    rcases finset.mem_fold_union h with ⟨p, hp, h'⟩,
    rw [list.mem_to_finset, list.mem_map] at hp,
    rcases hp with ⟨p', hp', hp⟩,
    simp [hp.symm] at h',
    have LC'_val : p'.LC ≠ 0, intro hp'', simpa [monomial_eq_zero_iff.2 hp'', finset.subset_empty] using h',
    refine ⟨p', ⟨hp', by rwa LC_nez_iff⟩, _⟩, 
    apply mem_mul_support LC'_val; assumption,
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
        conv {to_lhs, rw [←LM_TL_eq p, h]},
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
    have hp_LM : ∀ {x}, (x ∈ p.support ∪ q.support) → p.LM ≥ x,
    {
        intros x hx,
        rw [finset.mem_union] at hx, 
        cases hx,
        apply LM_rel' hx,
        apply le_trans (LM_rel' hx) (le_of_lt hpq),
    },
    apply (antisymm (hp_LM $ support_add $ LM_mem_support (λ h, _)) (LM_rel' _)).symm,
    have h' := (eq_zero_apply _).2 h p.LM, revert h',
    all_goals {
        simp [gt_LM_apply hpq], rw [←not_mem_support_iff, LM_not_mem],
        intros h,
        simp [h] at hpq,
        apply (not_lt_of_le (finsupp.zero_le q.LM)) hpq,
    },
end

lemma LM_of_add_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p + q).LM = q.LM := 
by rw [add_comm, LM_of_add_left hpq]

lemma LM_of_sub_left {p q : mv_polynomial σ α} (hpq : p.LM > q.LM) :
    (p - q).LM = p.LM := 
begin
    --rw ←@LM_neg _ _ _ _ _ _ q at hpq,
    --simp [LM_of_add_left hpq],
    conv at hpq {to_rhs, rw ←LM_neg,},
    simp [LM_of_add_left hpq],
end

lemma LM_of_sub_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p - q).LM = q.LM := 
begin
    rw ←@LM_neg _ _ _ _ _ _ q at hpq,
    simp [LM_of_add_right hpq],
end

lemma LC_of_add_left {p q : mv_polynomial σ α} (hpq : p.LM > q.LM) :
    (p + q).LC = p.LC := 
by simp [LC, LM_of_add_left hpq, gt_LM_apply hpq]

lemma LC_of_add_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p + q).LC = q.LC := 
by rw [add_comm, LC_of_add_left hpq]

lemma LC_of_sub_left {p q : mv_polynomial σ α} (hpq : p.LM > q.LM) :
    (p - q).LC = p.LC := 
begin
    rw [LC, LM_of_sub_left hpq],
    simp [LC, gt_LM_apply hpq],
end

lemma LC_of_sub_right {p q : mv_polynomial σ α} (hpq : q.LM > p.LM) :
    (p - q).LC = -q.LC := 
begin
    rw [LC, LM_of_sub_right hpq],
    simp [LC, gt_LM_apply hpq],
end

theorem sub_LM_lt {p q : mv_polynomial σ α} (h₁ : p.LM = q.LM) (h₂ : p.LC = q.LC) (hp : p.LM ≠ 0) : 
    (p - q).LM < p.LM := 
begin
    by_cases hpq : p - q = 0,
        simp [hpq], apply lt_of_le_of_ne (finsupp.zero_le p.LM) (ne.symm hp),
    have hab_LM : ∀ (x : σ →₀ ℕ), (x ∈ (p - q).support) → p.LM ≥ x,
        intros x hx, 
        have hx' := support_sub hx,
        rw [finset.mem_union] at hx', cases hx',
        apply LM_rel' hx',
        rw h₁, apply LM_rel' hx',
    apply lt_of_le_of_ne (hab_LM (p - q).LM (LM_mem_support hpq)),
    apply finset.ne_of_mem_and_not_mem (LM_mem_support hpq),
    simp [LC, h₁] at h₂, simp [h₁, h₂],
end

theorem LM_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM) 
{b : α} (hb : b ≠ 0) : (monomial a b + p).LM = a := 
begin
    rw ←@LM_of_monomial _ _ _ _ _ _ a _ hb at ha,
    rw [LM_of_add_left ha, LM_of_monomial hb],
end

theorem LC_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM) 
{b : α} (hb : b ≠ 0) : (monomial a b + p).LC = b := 
begin
    rw ←@LM_of_monomial _ _ _ _ _ _ a _ hb at ha,
    rw [LC_of_add_left ha, LC_of_monomial],
end

theorem TL_of_add_gt_LM {p : mv_polynomial σ α} {a : σ →₀ ℕ} (ha : a > p.LM)
{b : α} (hb : b ≠ 0) : (monomial a b + p).TL = p :=
begin
    have h := LM_TL_eq (monomial a b + p),
    rw [LM_of_add_gt_LM ha hb, LC_of_add_gt_LM ha hb] at h,
    apply add_left_cancel h,
end

end comm_ring

section integral_domain
variables [integral_domain α]
lemma mul_mem_mul_support {a a': σ →₀ ℕ} {b': α} (hb' : b' ≠ 0) (c : mv_polynomial σ α) 
(ha : a ∈ c.support) : a' + a ∈ (monomial a' b' * c).support :=
begin
    simp [has_mul.mul, monomial, single_sum' a' hb'],
    simp [finsupp.sum, single_apply],
    conv in (ite _ _ _) {
        congr,
        rw [add_comm, add_right_cancel_iff], skip,
        change b' * c x,
    },
    rw finset.sum_eq_single a,
    {simp [not_or_distrib] at ha ⊢, use [hb', ha]},
    {intros _ _ h, simp [h]},
    {finish}
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

theorem LM_of_mul_m {p : mv_polynomial σ α} : p ≠ 0 → ∀ {a b}, b ≠ 0 → (p * (monomial a b)).LM = p.LM + a := begin
    apply induction p, finish,
    intros q ih hq a b hb,
    have hq' := LC_nez_iff.1 hq,
    have hmq := mul_ne_zero hq' hb,
    rw ←LM_TL_eq q,
    by_cases h_TL : q.TL = 0,
    { simp [h_TL, -add_comm, monomial_mul_monomial, hq', hmq],},
    have h : q.TL.LM < (monomial (LM q) (LC q)).LM,
        simp [hq', lt_iff_le_and_ne], 
        refine ⟨(LM_rel (LM_mem_support h_TL)), finset.ne_of_mem_and_not_mem (LM_mem_support h_TL) LM_not_mem_TL⟩,
    have h' : (q.TL * monomial a b).LM < ((monomial q.LM q.LC) * monomial a b).LM,
        simpa [monomial_mul_monomial, ih h_TL hb, hmq, hq'] using h,
    rw [add_mul, LM_of_add_left h', LM_of_add_left h, monomial_mul_monomial, LM_of_monomial hmq, LM_of_monomial hq'],
end

theorem LC_of_mul_m {p : mv_polynomial σ α} : p ≠ 0 → ∀ {a b}, (p * (monomial a b)).LC = p.LC * b := begin
    apply induction p, finish,
    intros q ih hq a b,
    by_cases hb : b = 0,
    {rw [monomial_eq_zero_iff.2 hb, hb], simp},
    have hq' := LC_nez_iff.1 hq,
    have hmq := mul_ne_zero hq' hb,
    
    rw ←LM_TL_eq q,
    by_cases h_TL : q.TL = 0,
    {
        simp [h_TL, -add_comm], generalize hx : (monomial (LM q) (LC q) + 0) = x,
        simp at hx, simp [hx.symm, monomial_mul_monomial],
    },
    have h : q.TL.LM < (monomial (LM q) (LC q)).LM,
        simp [hq', lt_iff_le_and_ne], 
        refine ⟨(LM_rel (LM_mem_support h_TL)), finset.ne_of_mem_and_not_mem (LM_mem_support h_TL) LM_not_mem_TL⟩,
    have h' : (q.TL * monomial a b).LM < ((monomial q.LM q.LC) * monomial a b).LM,
        simpa [LM_of_mul_m h_TL hb, monomial_mul_monomial, hmq, hq'] using h,
    rw [add_mul, LC_of_add_left h, LC_of_add_left h', monomial_mul_monomial],
    simp,
end

end integral_domain
end well_order

end mv_polynomial
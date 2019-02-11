import data.list
import data.finsupp
import data.fin
import list
import algebra.gcd_domain
import util

universes u v

variable {n : ℕ}

lemma fin_0_id (a b : fin 0 →₀ ℕ) : a = b := begin apply finsupp.ext, intro x, cases x.2, end 

def le_aux : ∀ m < (n + 1), ((fin $ n + 1) →₀ ℕ) → ((fin $ n + 1) →₀ ℕ) → Prop
| 0 h := λ a b, a ⟨0, h⟩ ≤ b ⟨0, h⟩
| (m + 1) h := λ a b, a ⟨m + 1, h⟩ < b ⟨m + 1, h⟩ ∨ (a ⟨m + 1, h⟩ = b ⟨m + 1, h⟩ ∧ le_aux m (nat.lt_of_succ_lt h) a b)

def mon_le: Π {n}, (fin n →₀ ℕ) → (fin n →₀ ℕ) → Prop
| 0 a b            := true
| (nat.succ n) a b := le_aux n (nat.lt_succ_self n) a b

lemma le_refl_aux (m : ℕ) (h : m < n + 1) : ∀ a : (fin $ n + 1) →₀ ℕ, le_aux m h a a :=
λ a, begin
    induction m;
    unfold le_aux, right,
    apply and.intro rfl (m_ih (nat.lt_of_succ_lt h)),
end

lemma mon_le_refl : ∀ a : fin n →₀ ℕ, mon_le a a := 
λ a, by cases n; simp [mon_le]; apply le_refl_aux

lemma le_trans_aux (m : ℕ) (h : m < n + 1) : ∀ a b c : (fin $ n + 1) →₀ ℕ, le_aux m h a b → le_aux m h b c → le_aux m h a c :=
λ a b c, begin
    induction m; unfold le_aux, apply le_trans,
    intros hab hbc, cases hab; cases hbc,
    left, exact lt_trans hab hbc,
    left, exact lt_of_lt_of_le hab (le_of_eq hbc.left),
    left, exact lt_of_le_of_lt (le_of_eq hab.left) hbc,
    right, apply and.intro (eq.trans hab.left hbc.left) (m_ih (nat.lt_of_succ_lt h) hab.right hbc.right),
end

lemma mon_le_trans : ∀ a b c : fin n →₀ ℕ, 
    mon_le a b → mon_le b c → mon_le a c := 
λ a b c, by cases n; simp [mon_le]; apply le_trans_aux

instance : preorder (fin n →₀ ℕ) :=
{
    le := mon_le,
    le_refl := mon_le_refl,
    le_trans := mon_le_trans,
}


lemma le_antisymm_aux (m₁ m₂ : ℕ) (h : m₁ + m₂ < n + 1) : ∀ a b : (fin $ n + 1) →₀ ℕ, 
    le_aux (m₁ + m₂) h a b → le_aux (m₁ + m₂) h b a → a.to_fun ⟨m₁, nat.left_lt_of_add_lt h⟩ = b.to_fun ⟨m₁, nat.left_lt_of_add_lt h⟩ :=
λ a b, begin
    induction m₂, induction m₁, all_goals {simp [le_aux, nat.add_succ]}, 
    apply le_antisymm,
    all_goals {intros hab hba, cases hab; cases hba},
    any_goals { 
        try {apply absurd hab (not_lt_of_le (le_of_lt hba))},
        try {apply absurd hab (not_lt_of_le (le_of_eq hba.left))},
        try {apply absurd hba (not_lt_of_le (le_of_eq hab.left))},
    },
    exact hab.left,
    rw [nat.add_succ] at h,
    exact m₂_ih (nat.lt_of_succ_lt h) hab.right hba.right,
end

lemma mon_le_antisymm : ∀ a b : fin n →₀ ℕ, a ≤ b → b ≤ a → a = b := 
λ a b, begin
    cases n;
    intros hab hba, 
    apply fin_0_id,
    apply finsupp.ext, intro x, 
    have h_add_sub : x.val + (n - x.val) = n, rw [←nat.add_sub_assoc (nat.le_of_lt_succ x.is_lt)], finish,
    have h := le_antisymm_aux x.val (n - x.val) (lt_of_le_of_lt (le_of_eq h_add_sub) (nat.lt_succ_self n)) a b, 
    simp [h_add_sub] at h,
    apply h hab hba,
end

lemma le_total_aux (m : ℕ) (h : m < n + 1) : ∀ a b : (fin $ n + 1) →₀ ℕ, le_aux m h a b ∨ le_aux m h b a :=
λ a b, begin
    induction m; unfold le_aux, apply le_total,
    cases lt_trichotomy (a.to_fun ⟨m_n + 1, h⟩) (b.to_fun ⟨m_n + 1, h⟩),
    apply or.inl (or.inl h_1),
    cases h_1, cases m_ih (nat.lt_of_succ_lt h),
        apply or.inl (or.inr (and.intro h_1 h_2)),
        apply or.inr (or.inr (and.intro h_1.symm h_2)),
    apply or.inr (or.inl h_1),
end

lemma mon_le_total : ∀ a b : fin n →₀ ℕ, a ≤ b ∨ b ≤ a :=
λ a b, by cases n; simp [has_le.le, preorder.le, mon_le]; apply le_total_aux n

instance decidable_le_aux (m : ℕ) (h : m < n + 1) : decidable_rel (le_aux m h) :=
λ a b, begin
    induction m;
    unfold le_aux, apply_instance,
    from if h₀ : (a.to_fun ⟨m_n + 1, h⟩) < (b.to_fun ⟨m_n + 1, h⟩)
    then is_true (or.inl h₀)
    else if h₁ : (a.to_fun ⟨m_n + 1, h⟩) > (b.to_fun ⟨m_n + 1, h⟩)
    then is_false (λ h₁', begin 
        cases h₁', apply nat.lt_lt_antisym h₁ h₁',
        apply absurd h₁ (not_lt_of_le (le_of_eq h₁'.left)),
    end)
    else begin
        cases m_ih (nat.lt_of_succ_lt h),
        left, intro h_1', cases h_1', apply absurd h_1' h₀, apply absurd h_1'.right h_1,
        right, apply or.inr (and.intro (nat.not_le_not_ge_eq h₀ h₁) h_1),
    end
end

instance mon_le_decidable_rel : decidable_rel ((≤) : (fin n →₀ ℕ) → (fin n →₀ ℕ) → Prop) := λ a b,
by cases n; unfold has_le.le preorder.le mon_le; apply_instance

lemma le_mono_order_aux (m : ℕ) (h : m < n + 1) : ∀ a b w : (fin $ n + 1) →₀ ℕ, le_aux m h a b →  le_aux m h (a + w) (b + w) :=
λ a b w, begin
    induction m;
    unfold le_aux, simp,
    intro hab, simp, 
    cases hab, exact or.inl hab,
    exact or.inr (and.intro hab.left (m_ih (nat.lt_of_succ_lt h) hab.right)),
end

lemma le_mono_order : ∀ (a b w : fin n →₀ ℕ), (a ≤ b) → ((a + w) ≤ (b + w)) := 
λ a b w, by cases n; simp [has_le.le, preorder.le, mon_le]; apply le_mono_order_aux

instance : decidable_monomial_order (fin n →₀ ℕ) := {
    le := preorder.le,
    le_refl := preorder.le_refl,
    le_trans := preorder.le_trans,
    le_antisymm := mon_le_antisymm,
    le_total := mon_le_total,
    decidable_le := mon_le_decidable_rel,
    add := finsupp.has_add.add,
    mono_order := le_mono_order,
}

lemma zero_le_aux : ∀ (m < n + 1) (a : fin (n + 1) →₀ ℕ), le_aux m H 0 a
| 0 H a := by simp [le_aux]
|(m + 1) H a := by simp [le_aux]; 
                from if h : 0 < a ⟨m + 1, H⟩ 
                    then by simp [h]
                    else begin exact or.inr (and.intro (nat.eq_zero_of_le_zero (le_of_not_lt h)).symm
                                (zero_le_aux m (nat.lt_of_succ_lt H) a)) end

lemma mon_zero_le : ∀ a : fin n →₀ ℕ, 0 ≤ a :=
λ a, by cases n; simp [has_le.le, preorder.le, mon_le, zero_le_aux]

@[simp] lemma list_head'_none {α : Type*} : ∀ {l : list α}, l.head' = none ↔ l = [] 
| [] := by simp
| (hd :: tl) := by simp

lemma ne_empty_iff_exists_mem {α : Type*} {s : finset α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
begin
    simp [finset.eq_empty_iff_forall_not_mem],
    apply @not_forall_not _ _ (classical.dec _),
end

@[simp] lemma finset_sort_empty {α : Type*} {r : α → α → Prop} 
[decidable_eq α] [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r] : (∅ : finset α).sort r = [] :=
by apply quot.lift_beta id; intros; assumption

@[simp] lemma finset_sort_empty' {α : Type*} {r : α → α → Prop} 
[decidable_eq α] [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r] : ∀ {s : finset α}, s.sort r = [] ↔ s = ∅ :=
λ s, begin
    apply iff.intro; intro h,
    from if hs : s = ∅ 
    then by assumption
    else begin 
        rw [←ne.def, ne_empty_iff_exists_mem] at hs,
        cases hs, rw [←finset.mem_sort r, h] at hs_h,
        cases hs_h,
    end,
    rw h, apply finset_sort_empty,
end

structure order_poly (α : Type*) (β : Type*) [has_zero β] (r : α → α → Prop) := 
(support : list α)
(to_fun : α → β)
(mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0)
(order : list.sorted r support)
(nodup : support.nodup)

notation β ` ⬝ ` α ` /ᵣ ` r  := order_poly α β r

namespace order_poly
section basic

variables {α : Type*} {β : Type*} {r : α → α → Prop} [has_zero β]
instance : has_coe_to_fun (β ⬝ α /ᵣ r) := ⟨λ_, α → β, order_poly.to_fun⟩
instance : has_zero (β ⬝ α /ᵣ r) := ⟨⟨[], (λ_, 0), (λ _, ⟨false.elim, λ H, H rfl⟩), by finish, by finish⟩⟩

@[simp] lemma zero_apply {a : α} : (0 : β ⬝ α /ᵣ r) a = 0 := rfl

@[simp] lemma support_zero : (0 : β ⬝ α /ᵣ r).support = [] := rfl

instance : inhabited (β ⬝ α /ᵣ r) := ⟨0⟩

@[simp] lemma mem_support_iff {p : β ⬝ α /ᵣ r} : ∀{a}, a ∈ p.support ↔ p a ≠ 0 :=
p.mem_support_to_fun

lemma not_mem_support_iff {p : β ⬝ α /ᵣ r} {a} : a ∉ p.support ↔ p a = 0 :=
by haveI := classical.dec; exact not_iff_comm.1 mem_support_iff.symm

@[extensionality]
lemma ext [is_antisymm α r] : ∀{p q : β ⬝ α /ᵣ r }, (∀a, p a = q a) → p = q
| ⟨s, f, hf, of, nf⟩ ⟨t, g, hg, og, ng⟩ h := begin
    have : f = g, { funext a, exact h a },
    subst this,
    have : s = t, 
        apply list.sorted_nodup_ext of og nf ng, intro a,
        exact (hf a).trans (hg a).symm,
    subst this,
end

instance [decidable_eq α] [decidable_eq β] [is_antisymm α r] : decidable_eq (β ⬝ α /ᵣ r) := 
λ p q, decidable_of_iff (p.support = q.support ∧ ∀ a ∈ p.support, p a = q a) 
⟨λ ⟨h₁, h₂⟩, ext $ λ a, if h : a ∈ p.support then h₂ a h else
    have hp : p a = 0, by rwa [mem_support_iff, not_not] at h,
    have hq : q a = 0, by rwa [h₁, mem_support_iff, not_not] at h,
    by rw [hp, hq], 
by rintro rfl; finish⟩

end basic

section single
variables {α : Type*} {β : Type*} {r : α → α → Prop} [decidable_eq α] [decidable_eq β] [has_zero β] 

def single (a : α) (b : β) : β ⬝ α /ᵣ r :=
⟨if b = 0 then [] else [a], λ a', if a = a' then b else 0, 
    λ a', begin by_cases hb : b = 0; by_cases a = a'; finish, end, 
by by_cases hb : b = 0; finish, by by_cases hb : b = 0; finish⟩

end single

section on_list
variables {α : Type*} {β : Type*} {r : α → α → Prop} [decidable_eq β] [has_zero β]

def on_list (s : list α) (f : α → β) (hf : ∀a, f a ≠ 0 → a ∈ s) (os : s.sorted r) (ns : s.nodup) : β ⬝ α /ᵣ r := 
⟨s.filter (λa, f a ≠ 0), f,
  assume a, classical.by_cases
    (assume h : f a = 0, by rw list.mem_filter; exact ⟨and.right, λ H, (H h).elim⟩)
    (assume h : f a ≠ 0, by rw list.mem_filter; simp only [iff_true_intro h, hf a h, true_and]), 
    list.sorted_filter s os _, list.nodup_filter _ ns⟩

end on_list

section decidable
variables {α : Type*} {β : Type*} {r : α → α → Prop}
variables [decidable_eq α] [decidable_eq β]

section add_monoid
variables [add_monoid β]

def add [decidable_rel r] [is_trans α r] [is_total α r] (p q : β ⬝ α /ᵣ r) : β ⬝ α /ᵣ r := 
    on_list (list.erase_dup (list.merge r p.support q.support)) (λ a, p a + q a) 
    (λ a h, by finish [not_and_distrib.symm] ) 
    (begin 
        apply list.sorted_nodup,
        exact list.sorted_merge _ p.order q.order, 
    end) (by apply list.nodup_erase_dup)

/-
on_finset (g₁.support ∪ g₂.support) (λa, f (g₁ a) (g₂ a)) $ λ a H, begin
  haveI := classical.dec_eq β₁,
  simp only [mem_union, mem_support_iff, ne], rw [← not_and_distrib],
  rintro ⟨h₁, h₂⟩, rw [h₁, h₂] at H, exact H hf
end
-/

instance : has_add (β ⬝ α /ᵣ r) := begin

end

end add_monoid

instance [has_zero α] [has_zero β] [has_one β] : has_one  (β ⬝ α /ᵣ r) := ⟨single 0 1⟩

end decidable
/-
section comm_semiring
variables [comm_semiring α]





end comm_semiring
-/
end order_poly

/-
section comm_semiring
variables {α : Type*} [comm_semiring α] [decidable_eq α]

def is_const (p : mv_polynomial (fin n) α) := p = 0 ∨ p.support = {0}
def is_const' (p : mv_polynomial (fin n) α) := p.support = {0}

instance decidable_is_const (p : mv_polynomial (fin n) α): decidable (is_const p) :=
    by apply or.decidable
instance decidable_is_const' (p : mv_polynomial (fin n) α): decidable (is_const' p) :=
    by simp [is_const']; apply_instance

def lm (p : mv_polynomial (fin n) α) := (p.support.sort mon_le).head
def lc (p : mv_polynomial (fin n) α) := p.to_fun p.lm

lemma lm_zero (p : mv_polynomial (fin n) α) : p = 0 → lm p = 0 :=
λ h, begin
    have hp : p.support = ∅, finish,
    simp [lm, hp], constructor,
end

def m_lcm (a b : (fin n) →₀ ℕ) : (fin n) →₀ ℕ :=
    if a = 0 ∨ b = 0 then 0
    else finsupp.zip_with max (max_self 0) a b

def m_sub (a b : (fin n →₀ ℕ)) : (fin n) →₀ ℕ :=
    finsupp.zip_with (nat.sub) (by finish) a b

end comm_semiring

section gcd_domain 
variables {α : Type*} [gcd_domain α] [decidable_eq α]

def lm_lcm (p q : mv_polynomial (fin n) α) : mv_polynomial (fin n) α :=
    monomial (m_lcm p.lm q.lm) (lcm p.lc q.lc)

end gcd_domain

section discrete_field
variables {α : Type*} [discrete_field α] [decidable_eq α]

instance discrete_field_is_gcd_domain : gcd_domain α := {
    eq_zero_or_eq_zero_of_mul_eq_zero := discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero,
    norm_unit := λ a, if h : a = 0 then 1 else {
        val := a⁻¹,
        inv := a⁻¹⁻¹,
        val_inv := mul_inv_cancel (inv_ne_zero h),
        inv_val := inv_mul_cancel (inv_ne_zero h),
    },
    norm_unit_zero := by simp,
    norm_unit_mul := λ a b ha hb, begin
        simp [ha, hb, has_mul.mul, units.mul],
        split,
        change (a * b)⁻¹ = a⁻¹ * b⁻¹, finish [mul_inv'],
        finish,
    end,
    norm_unit_coe_units := λ u, begin 
        simp [units.ext_iff, units.val_coe], 
        generalize h_inv : u⁻¹ = k,
        unfold has_inv.inv units.inv' at h_inv, simp [h_inv.symm], 
        have h : u.val * u.val⁻¹ = u.val * u.inv, simp [units.val_inv], apply division_ring.mul_inv_cancel (units.ne_zero u),
        have h' :  u.inv * u.val * u.val⁻¹ = u.inv * u.val * u.inv, simp [mul_assoc, h], 
        finish [h', units.inv_val],
    end,
    gcd := λ a b, if a = 0 ∧ b = 0 then 0 else 1,
    lcm := λ a b, if a = 0 ∨ b = 0 then 0 else 1,
    gcd_dvd_left := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else by simp [h],
    gcd_dvd_right := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else by simp [h],
    dvd_gcd := λ a b c hac hab, if h : c = 0 ∧ b = 0 then by simp [h] else begin 
            simp [h], apply dvd.intro a⁻¹, apply mul_inv_cancel, intro ha, rw [ha, zero_dvd_iff] at hac hab,
            apply absurd (and.intro hac hab) h,
        end,
    norm_unit_gcd := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else begin 
        simp [h, units.ext_iff, units.val_coe], 
        unfold has_one.one, simp, apply one_inv_eq,
    end,
    gcd_mul_lcm := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else begin 
        simp [h], by_cases h' : a = 0 ∨ b = 0; simp [h', units.val_coe],
    end,
    lcm_zero_left := λ a, by simp,
    lcm_zero_right := λ a, by simp,
    .._inst_1,    
}

def s_poly (p q : mv_polynomial (fin n) α) : mv_polynomial (fin n) α :=
    let X := m_lcm p.lm q.lm in 
    let Xc := lcm p.lc q.lc in
    monomial (m_sub X p.lm) (Xc / p.lc) * p - monomial (m_sub X q.lm) (Xc / q.lc) * q


end discrete_field
-/
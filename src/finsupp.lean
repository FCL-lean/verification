--import data.finsupp
import linear_algebra.multivariate_polynomial
import algebra.gcd_domain
import discrete_field
import finset

namespace finsupp
section basic
variables {α : Type*} {β : Type*} [has_zero β]

lemma support_ne_empty [decidable_eq β] (f : α →₀ β) : f.support ≠ ∅ ↔ f ≠ 0 := by finish

lemma coe_f : Π (f : α →₀ β) (a : α), f a = f.to_fun a := λ f a, rfl
lemma coe_f' : Π (f : α →₀ β) (a : α), f.to_fun a = f a := λ f a, rfl

lemma eq_zero_apply (f : α →₀ β) : f = 0 ↔ ∀ {a}, f a = 0 := 
⟨λ h a, by rw [coe_f, h, coe_f', zero_apply], 
λ h, by ext a; finish⟩

end basic

section monomial
variables {σ : Type*} [decidable_eq σ] 

def m_lcm (a b : σ →₀ ℕ) : σ →₀ ℕ :=
    if a = 0 ∨ b = 0 then 0
    else finsupp.zip_with max (max_self 0) a b

def m_sub (a b : (σ →₀ ℕ)) : σ →₀ ℕ :=
    finsupp.zip_with (nat.sub) (by finish) a b

end monomial

section order_finsupp
variables {α : Type*} {β : Type*} 
variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r]

def s_support [has_zero β] (f : α →₀ β) := f.support.sort r

lemma support_empty_of_s_nil [has_zero β] {f : α →₀ β} : f.s_support r = [] ↔ f.support = ∅ := sorry
lemma support_ne_empty_of_s_ne_nil [has_zero β] {f : α →₀ β} : f.s_support r ≠ [] ↔ f.support ≠ ∅ := sorry
lemma eq_zero_of_s_nil [has_zero β] {f : α →₀ β} : f.s_support r = [] ↔ f = 0 := sorry
lemma ne_zero_of_s_ne_nil [has_zero β] {f : α →₀ β} : f.s_support r ≠ [] ↔ f ≠ 0 := sorry

section basic
variables [has_zero β] [inhabited α]

def hd (f : α →₀ β) := (s_support r f).head
def hd_val (f : α →₀ β) := f (s_support r f).head

def tl [decidable_eq α] (f : α →₀ β) : α →₀ β := 
let hd := f.hd r in
⟨(f.support.erase hd), λ a, if a = hd then 0 else f a, 
λ a, begin
    split; simp_intros, simp [a_1],
    by_cases a = hd; finish,
end⟩ 

lemma cons_hd_tl [decidable_eq α]  {f : α →₀ β} : s_support r f = (hd r f) :: (s_support r (tl r f)) := sorry

lemma tl_apply [decidable_eq α] (f : α →₀ β) : ∀ a ≠ hd r f, (tl r f) a = f a := 
λ a h, by rw coe_f; finish [tl]

lemma tl_apply_hd [decidable_eq α] (f : α →₀ β) : (tl r f) (hd r f) = 0 := 
    by rw ←not_mem_support_iff; simp [tl]

lemma hd_mem_s_support [decidable_eq β] (f : α →₀ β) (h : f ≠ 0) : f.hd r ∈ s_support r f:= begin
    rw [←support_ne_empty, ←finset.sort_ne_nil r] at h,
    unfold hd s_support, rw [←list.cons_head_tail h],
    simp,
end

lemma hd_mem_support [decidable_eq β] (f : α →₀ β) (h : f ≠ 0) : f.hd r ∈ f.support := 
    by rw ←finset.mem_sort r; apply hd_mem_s_support _ _ h

lemma hd_not_mem_tl [decidable_eq α] {f : α →₀ β} : f.hd r ∉ (tl r f).support := sorry
lemma hd_rel_tl_hd [decidable_eq α] {f : α →₀ β} (h : f ≠ 0) : r (hd r f) (hd r (tl r f)) := sorry

lemma hd_val_nez [decidable_eq β] (f : α →₀ β) (h : f ≠ 0) : hd_val r f ≠ 0 := begin
    unfold hd_val, rw ←mem_support_iff, apply hd_mem_support r f h,
end

end basic
section add_monoid
variables [decidable_eq α] [decidable_eq β] [inhabited α] [add_monoid β]

lemma hd_tl_eq (f : α →₀ β) : (single (hd r f) (hd_val r f)) + (tl r f) = f:= begin
    ext a, simp [single_apply],
    by_cases ha : hd r f = a; simp [ha],
    simp [hd_val, ha.symm, tl_apply_hd], refl,
    exact (tl_apply r f _ (ne.symm ha)),
end

@[elab_as_eliminator]
lemma induction_on [inhabited α] [decidable_eq α] [decidable_eq β] {C : (α →₀ β) → Prop} (f : α →₀ β) 
    (C₀ : C 0)
    (Cₙ : ∀ (f : α →₀ β) a b, a ∉ f.support → r a (hd r f) → C f → C (single a b + f)) : C f := 
suffices ∀ l (f : α →₀ β), f.s_support r = l → C f, from this _ _ rfl,
λ l, @list.rec_on _ (λ l, (∀ (f : α →₀ β), s_support r f = l → C f)) l
    (λ f hf, by rw eq_zero_of_s_nil at hf; rwa hf) 
    (begin 
        simp_intros l_hd l_tl ih f hf,
        have h := Cₙ (tl r f) (hd r f) (hd_val r f) (hd_not_mem_tl _) (hd_rel_tl_hd _ _),
        simp [hd_tl_eq] at h,
        apply h, apply ih, rw cons_hd_tl at hf, finish,
        rw [←ne_zero_of_s_ne_nil r, hf], simp,
    end)

end add_monoid

end order_finsupp
end finsupp

open finsupp
namespace mv_polynomial

section gcd_domain 
variables {σ : Type*} {α : Type*} [gcd_domain α] [decidable_eq α] [decidable_eq σ]
variables (r : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop) [decidable_rel r] [is_trans (σ →₀ ℕ) r] [is_antisymm (σ →₀ ℕ) r] [is_total (σ →₀ ℕ) r]

def lm_lcm (p q : mv_polynomial σ α) : mv_polynomial σ α :=
    monomial (m_lcm (p.hd r) (q.hd r)) (lcm (p.hd_val r) (q.hd_val r))

end gcd_domain

section discrete_field
variables {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [discrete_field α]
variables (r : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop) [decidable_rel r] [is_trans (σ →₀ ℕ) r] [is_antisymm (σ →₀ ℕ) r] [is_total (σ →₀ ℕ) r]

def s_poly (p q : mv_polynomial σ α) : mv_polynomial σ α := 
    let lm : (σ →₀ ℕ →₀ α) → (σ →₀ ℕ) := hd r in
    let lc : (σ →₀ ℕ →₀ α) → α := hd_val r in
    let X := m_lcm (lm p) (lm q) in
    let Xc := lcm (lc p) (lc q) in
    monomial (m_sub X (lm p)) (Xc / (lc p)) * p - monomial (m_sub X (lm q)) (Xc / (lc q)) * q

end discrete_field

end mv_polynomial
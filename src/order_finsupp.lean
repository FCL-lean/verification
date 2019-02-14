import has_dec_linear_order
import discrete_field
import finset
import sorted_list
import finsupp

namespace finsupp
section order_finsupp

variables {α : Type*} {β : Type*} 
variables [has_dec_linear_order α]

def dlo : has_dec_linear_order α := by apply_instance
def R : α → α → Prop := dlo.r

section s_support
variables [has_zero β]

def s_support (f : α →₀ β) := f.support.sort dlo.r

lemma mem_s_support {f : α →₀ β} {a : α} : a ∈ f.s_support ↔ a ∈ f.support := by simp [s_support]

lemma support_empty_of_s_nil {f : α →₀ β} : f.s_support = [] ↔ f.support = ∅ := by simp [s_support]
lemma support_ne_empty_of_s_ne_nil {f : α →₀ β} : f.s_support ≠ [] ↔ f.support ≠ ∅ := by simp [s_support, support_empty_of_s_nil]
lemma eq_zero_of_s_nil [decidable_eq β] {f : α →₀ β} : f.s_support = [] ↔ f = 0 := by simp [s_support]
lemma ne_zero_of_s_ne_nil [decidable_eq β] {f : α →₀ β} : f.s_support ≠ [] ↔ f ≠ 0 := by simp [s_support, eq_zero_of_s_nil]

lemma s_support_singleton [decidable_eq α] [decidable_eq β] {f : α →₀ β} {a} (h : f.s_support = [a]) : f = single a (f a) :=
begin
    simp [s_support, finset.sort_singleton] at h,
    ext x,
    by_cases ha : a = x; simp [single_apply, ha], 
    rw [←not_mem_support_iff, h, finset.not_mem_singleton], exact ne.symm ha,
end

end s_support

section basic
variables [has_zero β] [inhabited α]

def hd (f : α →₀ β) := (s_support f).head
def hd_val (f : α →₀ β) := f (s_support f).head

def tl [decidable_eq α] (f : α →₀ β) : α →₀ β := 
let hd := f.hd in
⟨(f.support.erase hd), λ a, if a = hd then 0 else f a, 
λ a, begin
    split; simp_intros, simp [a_1],
    by_cases a = hd; finish,
end⟩ 

lemma tl_apply [decidable_eq α] (f : α →₀ β) : ∀ a ≠ hd f, (tl f) a = f a := 
λ a h, by rw coe_f; finish [tl]

lemma tl_apply_hd [decidable_eq α] (f : α →₀ β) : (tl f) (hd f) = 0 := 
    by rw ←not_mem_support_iff; simp [tl]

lemma hd_mem_s_support [decidable_eq β] (f : α →₀ β) (h : f ≠ 0) : f.hd ∈ s_support f:= begin
    rw [←support_ne_empty, ←finset.sort_ne_nil] at h,
    unfold hd s_support, rw [←list.cons_head_tail h],
    simp,
end

lemma hd_mem_support [decidable_eq β] (f : α →₀ β) (h : f ≠ 0) : f.hd  ∈ f.support := 
    by rw ←finset.mem_sort dlo.r; apply hd_mem_s_support _ h

lemma hd_not_mem_tl [decidable_eq α] {f : α →₀ β} : f.hd ∉ (tl f).support := by simp [tl]

lemma tl_eq_s_tl [decidable_eq α] [decidable_eq β] {f : α →₀ β} : s_support (tl f) = (s_support f).tail := begin
    by_cases hf : s_support f = [], 
    simp [hf, tl, support_empty_of_s_nil.1 hf], 
    apply eq_zero_of_s_nil.2, apply eq_zero_lem, apply_instance,

    apply @list.sorted_nodup_ext _ dlo.r (is_antisymm_has_dec_linear_order dlo), simp [s_support], 
    apply list.sorted_tail, simp [s_support],
    apply finset.sort_sorted, simp [s_support],
    apply @list.nodup_of_nodup_cons _ (s_support f).head,
    rw list.cons_head_tail hf, all_goals {simp [s_support, hd, tl, -mem_support_iff]},
    intro a, unfold s_support at hf,
    rw [←finset.mem_sort dlo.r, ←list.cons_head_tail hf],
    simp [and_or_distrib_left],
    split; intro h,
    exact h.right,
    split,
    have nh := finset.sort_nodup dlo.r f.support, rw ←list.cons_head_tail hf at nh,
    simp at nh, intro ha, rw ha at h, exact nh.left h,
    assumption,
end 

lemma cons_hd_tl [decidable_eq α] [decidable_eq β] {f : α →₀ β} (hf : f ≠ 0) : list.cons (hd f) (s_support (tl f)) = s_support f := 
    by simp [tl_eq_s_tl, hd]; apply list.cons_head_tail; rwa ne_zero_of_s_ne_nil

lemma hd_val_nez [decidable_eq β] (f : α →₀ β) (h : f ≠ 0) : hd_val f ≠ 0 := begin
    unfold hd_val, rw ←mem_support_iff, apply hd_mem_support f h,
end

lemma hd_rel [decidable_eq α] [decidable_eq β] {f : α →₀ β} : ∀ a, a ∈ (tl f).support → R (hd f) a := λ a, 
    by rw [←mem_s_support, tl_eq_s_tl, hd]; apply finset.sort_hd_rel

end basic
section add_monoid
variables [decidable_eq α] [decidable_eq β] [inhabited α] [add_monoid β]

lemma hd_tl_eq (f : α →₀ β) : (single (hd f) (hd_val f)) + (tl f) = f:= begin
    ext a, simp [single_apply],
    by_cases ha : hd f = a; simp [ha],
    simp [hd_val, ha.symm, tl_apply_hd], refl,
    exact (tl_apply f _ (ne.symm ha)),
end

@[elab_as_eliminator]
lemma induction_on [inhabited α] [decidable_eq α] [decidable_eq β] {C : (α →₀ β) → Prop} (f : α →₀ β) 
    (C₀ : C 0)
    (Cₙ : ∀ (f : α →₀ β), C (tl f) → C f) : C f := 
    suffices ∀ l (f : α →₀ β), f.s_support = l → C f, from this _ _ rfl,
    λ l, @list.rec_on _ (λ l, (∀ (f : α →₀ β), s_support f = l → C f)) l
    (λ f hf, by rw eq_zero_of_s_nil at hf; rwa hf) 
    begin
        simp_intros l_hd l_tl ih f hf,
        apply Cₙ, apply ih,
        rw ←cons_hd_tl at hf, simp at hf, exact hf.right,
        rw [←ne_zero_of_s_ne_nil, hf], simp,
    end

@[elab_as_eliminator]
lemma induction_on' [inhabited α] [decidable_eq α] [decidable_eq β] {C : (α →₀ β) → Prop} (f : α →₀ β) 
    (C₀ : C 0)
    (Cₙ : ∀ (f : α →₀ β) a b, a ∉ f.support → (∀ x ∈ f.support, R a x) → C f → C (single a b + f)) : C f := 
    suffices ∀ l (f : α →₀ β), f.s_support = l → C f, from this _ _ rfl,
    λ l, @list.rec_on _ (λ l, (∀ (f : α →₀ β), s_support f = l → C f)) l
    (λ f hf, by rw eq_zero_of_s_nil at hf; rwa hf) 
    begin 
        simp_intros l_hd l_tl ih f hf,
        have h := Cₙ (tl f) (hd f) (hd_val f) (by simp [tl]) hd_rel,
        rw hd_tl_eq at h, apply h,
        apply ih,
        rw ←cons_hd_tl at hf, simp at hf, exact hf.right,
        rw [←ne_zero_of_s_ne_nil, hf], simp,
    end

end add_monoid

end order_finsupp
end finsupp



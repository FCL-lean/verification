import data.finsupp
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
namespace finsupp

section general
variables [decidable_eq α] [decidable_eq β]

section has_zero
variables [has_zero β] 

lemma in_not (a : α →₀ β) : ∀ x : α, x ∈ a.support ∨ x ∉ a.support := 
    by intro; apply classical.or_not

lemma support_singleton_neq_zero {a : α →₀ β} {x : α} (h : a.support = {x}) : a x ≠ 0 :=
by apply (a.mem_support_to_fun x).1; simp [h]

lemma support_singleton_eq_zero {a : α →₀ β} {x y : α} (h₁ : x ≠ y) (h₂ : a.support = {y}) : a x = 0 :=
by rw [←not_mem_support_iff]; simp [h₁, h₂]

def single_inj1 : Π {a b: α} {c d: β}, (c ≠ 0) → single a c = single b d → a = b :=
begin
    intros, unfold single at *, simp at a_1,
    by_cases c = 0, rw h at *, simp at *,
    apply false.elim; assumption,
    simp [a_1] at a_2,
    by_cases d = 0, rw h at *, simp at *,
    apply false.elim; assumption,
    simp [a_1, h] at a_2,
    cases a_2, rw finset.singleton_inj at a_2_left,
    assumption,
end

def single_inj2 : Π {a b: α} {c d: β}, single a c = single b d → c = d :=
begin
    intros, unfold single at *, simp at a_1,
    by_cases c = 0; rw h at *;
    by_cases d = 0; rw h at *,
    simp [h] at *, cases a_1, 
    unfold finset.singleton has_emptyc.emptyc finset.empty at a_1_left,
    simp at a_1_left, apply false.elim, assumption,
    tactic.unfreeze_local_instances, dedup, simp [h] at a_1,
    apply false.elim, assumption,
    tactic.unfreeze_local_instances, dedup, simp [h, h_1] at a_1,
    cases a_1, rw finset.singleton_inj at a_1_left,
    rw a_1_left at *, let m := congr_fun a_1_right b,
    simp at m, assumption,
end

def single_eqz : Π {a : α} {b : β}, single a b = 0 → b = 0 :=
begin
    intros a b sin,
    unfold single at sin,
    by_cases b = 0,
    assumption,
    simp [h] at sin,
    apply false.elim,
    have m := congr_arg finsupp.support sin, simp at m,
    assumption,
end

def coe_f : Π (a : α →₀ β) (n : α), a n = a.to_fun n := λ a n, rfl
end has_zero

section canonically_ordered_monoid
variables [canonically_ordered_monoid β]

lemma support_contain_a (a b : α →₀ β) : a.support ⊆ (a + b).support :=
begin
    unfold has_subset.subset,
    intros a_1 h,
    let ha := (a.mem_support_to_fun a_1).elim_left h,
    have hab : (a + b).to_fun a_1 ≠ 0,
    rw ←coe_f at *,
    simp, intro ha',
    apply (absurd ha' ha),
    apply ((a + b).mem_support_to_fun a_1).elim_right hab,
end

lemma support_contain_b (a b : α →₀ β) : b.support ⊆ (a + b).support := by rw add_comm; apply support_contain_a

lemma union_support_contain (a b : α →₀ β) : a.support ∪ b.support ⊆ (a + b).support :=
begin
    have ha := support_contain_a a b,
    have hb := support_contain_b a b,
    intros elem p,
    have lem := finset.mem_union.elim_left p,
    cases lem,
    exact ha lem,
    exact hb lem,
end

end canonically_ordered_monoid
end general

section fin_n
end fin_n

end finsupp
import order.order_iso finsupp user_classes

namespace finsupp
variables {α : Type*} {β : Type*} [decidable_eq α] [decidable_canonically_ordered_monoid β]
variables (r : (α →₀ β) → (α →₀ β) → Prop)
variables [is_well_order (α →₀ β) r] [mo : is_monomial_order (α →₀ β) (λ x y, x = y ∨ r x y)] 

instance : ordered_cancel_comm_monoid (α →₀ β) := {
    add_left_cancel := λ a b c, (finsupp.add_left_cancel_iff_eq a b c).1,
    add_right_cancel := λ a b c, (finsupp.add_right_cancel_iff_eq a b c).1,
    add_le_add_left := mo.monomial_order,
    le_of_add_le_add_left := λ a b c h, begin
        letI := linear_order_of_STO' r,
        rcases @trichotomous (α →₀ β) (<) _ b c with hbc | hbc | hbc,
        apply le_of_lt hbc,
        apply le_of_eq hbc,
        have h' : a + c ≤ a + b, apply mo.monomial_order, apply le_of_lt hbc,
        simp [(finsupp.add_left_cancel_iff_eq a c b).1 (antisymm h' h)],
    end,
    ..linear_order_of_STO' r,
    ..finsupp.add_comm_monoid
}

private def f (x : α →₀ β) : ℕ → (α →₀ β)
| 0 := 0
| (n + 1) := x + f n

private lemma f_nez {x : α →₀ β} (hx : x ≠ 0): ∀ n ≠ 0, (f x) n ≠ 0
| 0 := by simp
| (n + 1) := λ _ h, begin
    simp [f, add_eqz] at h, 
    exact hx h.left,
end

include r mo
private lemma f_inj {x : α →₀ β} (hx : x ≠ 0) : ∀ n m : ℕ, (f x) n = (f x) m → n = m
| 0 0 := by simp
| 0 (m + 1) := 
    by simp_intros h [f]; apply absurd (eq.symm h) (f_nez hx (m + 1) (by simp))
| (n + 1) 0 := 
    by simp_intros h [f]; apply absurd h (f_nez hx (n + 1) (by simp))
| (n + 1) (m + 1) := 
    begin simp_intros h [f, add_left_cancel_iff], simpa using f_inj _ _ h, end

private lemma f_lt_zero {x : α →₀ β} (hx : x < 0) : ∀ a ≠ 0, f x a < 0
| 0 := by simp
| (a + 1) := λ _, begin
    by_cases a = 0; simp [h, f, hx],
    apply lt_trans _ (f_lt_zero _ h),
    simpa using add_lt_add_right hx (f x a),
end

private lemma f_descend_seq₁ {x : α →₀ β} (hx : x < 0) : ∀ a b, (f x) (a + b + 1) < f x a 
| a 0 := by simpa [f] using add_lt_add_right hx (f x a)
| a (b + 1) := begin
    apply lt_trans _ (f_descend_seq₁ a b),
    rw [←add_assoc a b, ←nat.succ_eq_add_one],
    simpa [f] using add_lt_add_right hx (f x (a + b + 1)),
end

private lemma f_descend_seq₂ {x : α →₀ β} (hx : x < 0) : ∀ a b, f x a < f x b → a > b
| 0 0 := by simp [lt_irrefl]
| 0 (b + 1) := begin
    simp_intros hb [f],
    apply absurd (lt_trans (f_lt_zero _ hx (b + 1) (by simp)) hb) (lt_irrefl _),
end
| (a + 1) 0 := λ _, nat.zero_lt_succ a
| (a + 1) (b + 1) := begin
    simp_intros h [f],
    apply add_lt_add_right (f_descend_seq₂ _ _ h),
end

private lemma f_descend_seq {x : α →₀ β} (hx : x < 0) : ∀ (a b : ℕ), a > b ↔ f x a < f x b :=
λ a b, 
⟨λ h, begin
    have hab := nat.add_sub_cancel' (nat.succ_le_of_lt h),
    rw [nat.succ_add, nat.succ_eq_add_one, nat.succ_eq_add_one] at hab,
    simpa [hab] using f_descend_seq₁ _ hx b (a - (b + 1)),
end, 
f_descend_seq₂ _ hx a b⟩

lemma not_lt_zero (x : α →₀ β) : ¬ x < 0 := 
λ hx, begin
    letI h := _inst_3.wf,
    rw order_embedding.well_founded_iff_no_descending_seq at h,
    apply h,
    constructor, apply order_embedding.mk ⟨f x, f_inj r (ne_of_lt hx)⟩,
    simp_intros, 
    apply f_descend_seq _ hx a b,
end 

lemma zero_le' (x : α →₀ β) : 0 ≤ x := 
begin
    letI := linear_order_of_STO' r,
    rcases @trichotomous (α →₀ β) (<) _ 0 x with hx | hx | hx,
    apply le_of_lt hx,
    apply le_of_eq hx,
    apply absurd hx (not_lt_zero _ x),
end

lemma le_zero_iff' (x : α →₀ β) : x ≤ 0 ↔ x = 0 := ⟨λ ha, begin
    apply antisymm ha,
    exact zero_le' _ x,
end, λ h, by simp [h]⟩

lemma zero_lt_iff_ne_zero' {x : α →₀ β} : 0 < x ↔ x ≠ 0 := 
⟨λ h h', begin rw h' at h, apply (lt_irrefl _) h, end,
λ h, lt_of_le_of_ne (zero_le' _ x) (ne.symm h)⟩

end finsupp

import order.order_iso finsupp user_classes

namespace finsupp

section linear_order
variables {α : Type*} {β : Type*} [decidable_eq α] [decidable_canonically_ordered_monoid β]
variables [linear_order (α →₀ β)] [is_well_founded (α →₀ β) (<)] [is_monomial_order (α →₀ β) (≤)] 

instance : ordered_cancel_comm_monoid (α →₀ β) := {
    add_left_cancel := λ a b c, (finsupp.add_left_cancel_iff_eq a b c).1,
    add_right_cancel := λ a b c, (finsupp.add_right_cancel_iff_eq a b c).1,
    add_le_add_left := _inst_5.monomial_order,
    le_of_add_le_add_left := λ a b c h, begin
        rcases lt_trichotomy b c with hbc | hbc | hbc,
        apply le_of_lt hbc,
        apply le_of_eq hbc,
        have h' : a + c ≤ a + b, apply _inst_5.monomial_order, apply le_of_lt hbc,
        simp [(finsupp.add_left_cancel_iff_eq a c b).1 (antisymm h' h)],
    end,
    .._inst_3,
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
    apply absurd (lt_trans (f_lt_zero hx (b + 1) (by simp)) hb) (lt_irrefl _),
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
    simpa [hab] using f_descend_seq₁ hx b (a - (b + 1)),
end, 
f_descend_seq₂ hx a b⟩

lemma not_lt_zero (x : α →₀ β) : ¬ x < 0 := 
λ hx, order_embedding.well_founded_iff_no_descending_seq.1 _inst_4.wf begin
    constructor, apply order_embedding.mk ⟨f x, f_inj (ne_of_lt hx)⟩,
    simp_intros, 
    apply f_descend_seq hx a b,
end 

lemma zero_le (x : α →₀ β) : 0 ≤ x := le_of_not_lt (not_lt_zero x)

lemma le_zero_iff (x : α →₀ β) : x ≤ 0 ↔ x = 0 := 
⟨λ ha, begin
    apply antisymm ha,
    exact zero_le x,
end, λ h, by simp [h]⟩

lemma zero_lt_iff_ne_zero {x : α →₀ β} : 0 < x ↔ x ≠ 0 := 
    by finish [lt_iff_le_and_ne, zero_le x]

lemma ne_zero_of_gt {x y : α →₀ β} : y < x → x ≠ 0 := 
λ h, zero_lt_iff_ne_zero.1 (lt_of_le_of_lt (zero_le y) h)

end linear_order
end finsupp

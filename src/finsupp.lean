import data.finsupp

namespace finsupp
section basic
variables {α : Type*} {β : Type*} [has_zero β]

lemma support_ne_empty [decidable_eq β] (f : α →₀ β) : f.support ≠ ∅ ↔ f ≠ 0 := by finish

lemma coe_f : Π (f : α →₀ β) (a : α), f a = f.to_fun a := λ f a, rfl
lemma coe_f' : Π (f : α →₀ β) (a : α), f.to_fun a = f a := λ f a, rfl

lemma eq_zero_lem [decidable_eq β] : ∀ {f : α → β} {l}, ({support := ∅, to_fun := f, mem_support_to_fun := l} : α →₀ β) = 0 :=
begin
    intros,
    rw support_eq_empty.1 (rfl : ({support := ∅, to_fun := f, mem_support_to_fun := l} : α →₀ β).support = ∅),
end

lemma eq_zero_apply (f : α →₀ β) : f = 0 ↔ ∀ {a}, f a = 0 := 
⟨λ h a, by rw [coe_f, h, coe_f', zero_apply], 
λ h, by ext a; finish⟩

lemma ext_lem {a b : α →₀ β} : a = b ↔ ∀ x, a x = b x := ⟨λ h, by finish, λ h, by apply finsupp.ext; assumption⟩

end basic

section monomial
variables {σ : Type*} [decidable_eq σ] 

def m_lcm (a b : σ →₀ ℕ) : σ →₀ ℕ :=
    if a = 0 ∨ b = 0 then 0
    else zip_with max (max_self 0) a b

--def m_div (a b : (σ →₀ ℕ)) : σ →₀ ℕ :=
--    zip_with (nat.sub) (by finish) a b

def has_div (a b : σ →₀ ℕ) : Prop := ∀ x, a x ≤ b x
notation a ` |ₘ ` b := has_div a b

def m_div (a b : σ →₀ ℕ) : σ →₀ ℕ := 
    zip_with (nat.sub) (by finish) a b
notation a ` /ₘ ` b := m_div a b

instance decidable_has_div (a b : σ →₀ ℕ) : decidable (a |ₘ b) := sorry

lemma m_lcm_has_div_left (a b : σ →₀ ℕ) : a |ₘ (m_lcm a b) := sorry
lemma m_lcm_has_div_right (a b : σ →₀ ℕ) : b |ₘ (m_lcm a b) := sorry

end monomial

section decidable_linear_ordered_cancel_comm_monoid
variables {α : Type*} {β : Type*} [decidable_eq α] [decidable_linear_ordered_cancel_comm_monoid β]

lemma add_left_cancel (a b c : α →₀ β) : a + b = a + c ↔ b = c := 
⟨λ h, by simpa [ext_lem] using h, 
λ h, by  simpa [ext_lem] using h⟩

lemma add_right_cancel (a b c : α →₀ β) : a + b = c + b ↔ a = c := 
⟨λ h, by simpa [ext_lem, -add_comm] using h, 
λ h, by simpa [ext_lem, -add_comm] using h⟩

end decidable_linear_ordered_cancel_comm_monoid

end finsupp
import data.finsupp

namespace finsupp
section basic
variables {α : Type*} {β : Type*} [has_zero β]

lemma support_ne_empty [decidable_eq β] (f : α →₀ β) : f.support ≠ ∅ ↔ f ≠ 0 := by finish

lemma coe_f : Π (f : α →₀ β) (a : α), f a = f.to_fun a := λ f a, rfl
lemma coe_f' : Π (f : α →₀ β) (a : α), f.to_fun a = f a := λ f a, rfl

@[simp] lemma eq_zero_lem [decidable_eq β] : ∀ {f : α → β} {l}, ({support := ∅, to_fun := f, mem_support_to_fun := l} : α →₀ β) = 0 :=
begin
    intros,
    rw support_eq_empty.1 (rfl : ({support := ∅, to_fun := f, mem_support_to_fun := l} : α →₀ β).support = ∅),
end

lemma eq_zero_apply (f : α →₀ β) : (∀ a, f a = 0) ↔ f = 0 := 
⟨λ h, by ext a; finish, λ h a, by rw [coe_f, h, coe_f', zero_apply]⟩

lemma ext_lem {a b : α →₀ β} : a = b ↔ ∀ x, a x = b x := ⟨λ h, by finish, λ h, by apply finsupp.ext; assumption⟩

lemma single_eq_zero_iff [decidable_eq α] [decidable_eq β] {a : α} {b : β} : single a b = 0 ↔ b = 0 := begin
    simp [(eq_zero_apply _).symm, single_apply], split; intros,
    simpa using @a_1 a,
    by_cases a = a_2; simp [h], assumption,
end

lemma single_sum' [decidable_eq α] [decidable_eq β] {γ : Type*} [add_comm_monoid γ] (a : α) {b : β} (hb : b ≠ 0) (f : α → β → γ) : 
(single a b).sum f = f a b := by simp [sum, single, hb, coe_f]

end basic

section monomial
variables {σ : Type*} [decidable_eq σ] 

def m_lcm (a b : σ →₀ ℕ) : σ →₀ ℕ :=
    if a = 0 ∨ b = 0 then 0
    else zip_with max (max_self 0) a b

def dvd (a b : σ →₀ ℕ) : Prop := ∀ x, a x ≤ b x
instance : has_dvd (σ →₀ ℕ) := ⟨dvd⟩
notation a ` ∤ ` b := ¬ a ∣ b

instance decidable_has_div [fintype σ] (a b : σ →₀ ℕ) : decidable (a ∣ b) := by simp [has_dvd.dvd, dvd]; apply_instance

@[simp] lemma zero_dvd {a : σ →₀ ℕ} : 0 ∣ a := 
    by simp [has_dvd.dvd, dvd]

lemma dvd_of_add {a b c : σ →₀ ℕ} (h : a = b + c) : b ∣ a := 
begin rw h, intro x, simp, end

def m_div (a b : σ →₀ ℕ) : σ →₀ ℕ := 
    zip_with (nat.sub) (by finish) a b
instance : has_sub (σ →₀ ℕ) := ⟨m_div⟩

@[simp] lemma sub_zero (f : σ →₀ ℕ) : f - 0 = f := begin
    simp [has_sub.sub, m_div],
    ext a, simp, apply nat.sub_zero,
end

lemma sub_apply_dvd {f g : σ →₀ ℕ} (h : g ∣ f) : ∀ x, (f - g) x = f x - g x := 
λ x, begin
    simp [coe_f, has_sub.sub, m_div],
    rw [coe_f', zip_with_apply], refl,
end

lemma add_sub_cancel' {n m : σ →₀ ℕ} (h : m ∣ n) : m + (n - m) = n := begin
    ext a, simp [sub_apply_dvd h], apply nat.add_sub_cancel',
    simpa [has_dvd.dvd, dvd] using h a,
end

end monomial

section comm_ring
variables {α : Type*} {β : Type*} [comm_ring β] [decidable_eq α] [decidable_eq β]

lemma mem_sub_support {f g : α →₀ β} : ∀ x ∈ (f - g).support, x ∈ f.support ∪ g.support := 
λ x hx, begin
    simp [-mem_support_iff] at hx, rw ←@support_neg _ _ _ _ _ g,
    apply support_add hx,
end

end comm_ring

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
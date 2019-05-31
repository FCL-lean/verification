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


def m_lcm (a b : σ →₀ ℕ) : σ →₀ ℕ := zip_with max (max_self 0) a b

lemma m_lcm_apply_eq_left {a b : σ →₀ ℕ} {x} (h : b x ≤ a x) 
: (m_lcm a b) x = a x := by rw [m_lcm]; simp [max_eq_left h]

lemma m_lcm_apply_eq_right {a b : σ →₀ ℕ} {x} (h : a x ≤ b x) 
: (m_lcm a b) x = b x := by rw [m_lcm]; simp [max_eq_right h]

theorem m_lcm_comm (a b : σ →₀ ℕ) : m_lcm a b = m_lcm b a :=
begin
    ext x,
    by_cases a x ≤ b x,
    {simp [m_lcm_apply_eq_left h, m_lcm_apply_eq_right h]},
    {simp [m_lcm_apply_eq_left (le_of_not_le h), m_lcm_apply_eq_right (le_of_not_le h)]}
end

def dvd (a b : σ →₀ ℕ) : Prop := ∀ x, a x ≤ b x
instance : has_dvd (σ →₀ ℕ) := ⟨dvd⟩
notation a ` ∤ ` b := ¬ a ∣ b

instance decidable_has_div [fintype σ] (a b : σ →₀ ℕ) : decidable (a ∣ b) := by simp [has_dvd.dvd, dvd]; apply_instance

@[simp] lemma zero_dvd {a : σ →₀ ℕ} : 0 ∣ a := 
    by simp [has_dvd.dvd, dvd]

@[simp] theorem dvd_refl {a : σ →₀ ℕ} : a ∣ a := λ x, le_refl _

@[simp] theorem dvd_add_right {a b : σ →₀ ℕ} : a ∣ a + b :=
λ x, by simp

lemma dvd_of_add {a b c : σ →₀ ℕ} (h : a = b + c) : b ∣ a := 
by simp [h]

lemma dvd_trans' {a b c : σ →₀ ℕ} : a ∣ b → b ∣ c → a ∣ c :=
λ hab hbc x, trans (hab x) (hbc x)

lemma dvd_of_dvd_of_add {a b : σ →₀ ℕ} : a ∣ b → ∀ c, a ∣ b + c :=
λ hab c, dvd_trans' hab (by simp)

lemma dvd_of_dvd_of_add' {a b : σ →₀ ℕ} : a ∣ b → ∀ c, a ∣ c + b :=
λ hab c, dvd_trans' hab (by simp)

lemma dvd_lcm_left {a b : σ →₀ ℕ} : a ∣ m_lcm a b := 
λ x, by rw m_lcm; finish

lemma dvd_lcm_right {a b : σ →₀ ℕ} : b ∣ m_lcm a b := 
λ x, by rw m_lcm; finish

lemma lcm_dvd {a b c : σ →₀ ℕ} : a ∣ c → b ∣ c → m_lcm a b ∣ c :=
λ ha hb x, begin
    by_cases hab : a x ≤ b x,
    {simp [m_lcm_apply_eq_right hab, hb x]},
    {simp [m_lcm_apply_eq_left (le_of_not_le hab), ha x]}
end

def m_div (a b : σ →₀ ℕ) : σ →₀ ℕ := 
    zip_with (nat.sub) (by finish) a b
instance : has_sub (σ →₀ ℕ) := ⟨m_div⟩

@[simp] lemma sub_zero (f : σ →₀ ℕ) : f - 0 = f := begin
    simp [has_sub.sub, m_div],
    ext a, simp, apply nat.sub_zero,
end

@[simp] lemma sub_self {f : σ →₀ ℕ} : f - f = 0 :=
begin
    simp [has_sub.sub, m_div],
    ext a, simp, apply nat.sub_self,
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

lemma add_sub_assoc' {n m k : σ →₀ ℕ} (h : k ∣ m) : n + m - k = n + (m - k) :=
begin
    ext x,
    simp [sub_apply_dvd h, sub_apply_dvd (dvd_of_dvd_of_add' h n), nat.add_sub_assoc (h x)],
end

lemma sub_add_comm {n m k : σ →₀ ℕ} (h₁ : k ∣ n) (h₂ : k ∣ m) : (n - k) + m = (m - k) + n :=
by rw [add_comm _ m, add_comm _ n, ←add_sub_assoc' h₁, ←add_sub_assoc' h₂, add_comm]

lemma exists_eq_mul_left_of_dvd {a b : σ →₀ ℕ} (h : a ∣ b) : ∃ c, b = c + a := ⟨b - a, by simp [add_sub_cancel' h]⟩

lemma exists_eq_mul_right_of_dvd {a b : σ →₀ ℕ} (h : a ∣ b) : ∃ c, b = a + c := ⟨b - a, by simp [add_sub_cancel' h]⟩


end monomial

section comm_ring
variables {α : Type*} {β : Type*} [comm_ring β] [decidable_eq α] [decidable_eq β]

lemma support_sub {f g : α →₀ β} : (f - g).support ⊆ f.support ∪ g.support := 
λ x hx, begin
    simp [-mem_support_iff] at hx, rw ←@support_neg _ _ _ _ _ g,
    apply support_add hx,
end

end comm_ring

section canonically_ordered_monoid
variables {α : Type*} {β : Type*} [canonically_ordered_monoid β] [decidable_eq α] [decidable_eq β]
lemma add_eqz (a b : α →₀ β) : a + b = 0 ↔ a = 0 ∧ b = 0 := 
⟨λ h, begin
    simp [ext_lem, forall_and_distrib] at h,
    simpa [eq_zero_apply] using h,
end,
λ h, by simp [h.left, h.right]⟩

end canonically_ordered_monoid

section decidable_linear_ordered_cancel_comm_monoid
variables {α : Type*} {β : Type*} [decidable_eq α] [decidable_linear_ordered_cancel_comm_monoid β]

lemma add_left_cancel_iff_eq (a b c : α →₀ β) : a + b = a + c ↔ b = c := 
⟨λ h, by simpa [ext_lem] using h, 
λ h, by  simpa [ext_lem] using h⟩

lemma add_right_cancel_iff_eq (a b c : α →₀ β) : a + b = c + b ↔ a = c := 
⟨λ h, by simpa [ext_lem, -add_comm] using h, 
λ h, by simpa [ext_lem, -add_comm] using h⟩

end decidable_linear_ordered_cancel_comm_monoid

end finsupp
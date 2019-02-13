import data.finsupp
import data.fin
import finsupp
import util

variables {n : ℕ} {α : Type*} [decidable_linear_ordered_cancel_comm_monoid α]

lemma fin_0_id (a b : fin 0 →₀ α) : a = b := by ext x; cases x.2

def le_aux : ∀ m < (n + 1), ((fin $ n + 1) →₀ α) → ((fin $ n + 1) →₀ α) → Prop
| 0 h := λ a b, a ⟨0, h⟩ ≤ b ⟨0, h⟩
| (m + 1) h := λ a b, a ⟨m + 1, h⟩ < b ⟨m + 1, h⟩ ∨ (a ⟨m + 1, h⟩ = b ⟨m + 1, h⟩ ∧ le_aux m (nat.lt_of_succ_lt h) a b)

def mon_le: Π {n}, (fin n →₀ α) → (fin n →₀ α) → Prop
| 0 a b            := true
| (n + 1) a b := le_aux n (nat.lt_succ_self n) a b

lemma le_refl_aux (m : ℕ) (h : m < n + 1) : ∀ a : (fin $ n + 1) →₀ α, le_aux m h a a := 
λ a, by induction m; simp [le_aux]; right; exact m_ih (nat.lt_of_succ_lt h)

lemma mon_le_refl : ∀ a : fin n →₀ α, mon_le a a := λ a, by cases n; simp [mon_le]; apply le_refl_aux

lemma le_trans_aux (m : ℕ) (h : m < n + 1) :
∀ a b c : (fin $ n + 1) →₀ α, le_aux m h a b → le_aux m h b c → le_aux m h a c := 
λ a b c, begin
    induction m; simp [le_aux], apply le_trans,
    rintros (hab | ⟨hab₁, hab₂⟩) (hbc | ⟨hbc₁, hbc₂⟩),
    left, exact lt_trans hab hbc,
    left, exact lt_of_lt_of_le hab (le_of_eq hbc₁),
    left, exact lt_of_le_of_lt (le_of_eq hab₁) hbc,
    right, refine ⟨eq.trans hab₁ hbc₁, m_ih (nat.lt_of_succ_lt h) hab₂ hbc₂⟩,
end

lemma mon_le_trans : ∀ a b c : fin n →₀ α, 
    mon_le a b → mon_le b c → mon_le a c := 
λ a b c, by cases n; simp [mon_le]; apply le_trans_aux

instance : preorder (fin n →₀ α) :=
{
    le := mon_le,
    le_refl := mon_le_refl,
    le_trans := mon_le_trans,
}

lemma le_antisymm_aux (m₁ m₂ : ℕ) (h : m₁ + m₂ < n + 1) : ∀ a b : (fin $ n + 1) →₀ α, 
    le_aux (m₁ + m₂) h a b → le_aux (m₁ + m₂) h b a → a.to_fun ⟨m₁, nat.left_lt_of_add_lt h⟩ = b.to_fun ⟨m₁, nat.left_lt_of_add_lt h⟩ := 
λ a b, begin
    induction m₂, induction m₁, all_goals {simp [le_aux, nat.add_succ]}, apply antisymm,
    all_goals {rintros (hab | ⟨hab₁, hab₂⟩) (hba | ⟨hba₁, hba₂⟩)},
    any_goals { 
        {apply absurd hab (not_lt_of_le (le_of_lt hba))} <|>
        {apply absurd hab (not_lt_of_le (le_of_eq hba₁))} <|>
        {apply absurd hba (not_lt_of_le (le_of_eq hab₁))},
    },
    exact hab₁,
    apply m₂_ih _ hab₂ hba₂,
end

lemma mon_le_antisymm : ∀ a b : fin n →₀ α, a ≤ b → b ≤ a → a = b := 
λ a b, begin
    cases n; intros hab hba, 
    apply fin_0_id,
    ext x,
    have h_add_sub : x.val + (n - x.val) = n, rw [←nat.add_sub_assoc (nat.le_of_lt_succ x.is_lt)], finish,
    have h := le_antisymm_aux x.val (n - x.val) (lt_of_le_of_lt (le_of_eq h_add_sub) (nat.lt_succ_self n)) a b, 
    simp [h_add_sub] at h, apply h hab hba,
end

lemma le_total_aux (m : ℕ) (h : m < n + 1) : ∀ a b : (fin $ n + 1) →₀ α, le_aux m h a b ∨ le_aux m h b a :=
λ a b, begin
    induction m; simp [le_aux], apply total_of,
    cases lt_trichotomy (a.to_fun ⟨m_n + 1, h⟩) (b.to_fun ⟨m_n + 1, h⟩),
    left, left, exact h_1,
    cases h_1, cases m_ih (nat.lt_of_succ_lt h),
        left, right, refine ⟨h_1, h_2⟩,
        right, right, refine ⟨h_1.symm, h_2⟩,
    right, left, exact h_1,
end

lemma mon_le_total : ∀ a b : fin n →₀ α, a ≤ b ∨ b ≤ a :=
λ a b, by cases n; simp [has_le.le, preorder.le, mon_le]; apply le_total_aux n

instance decidable_le_aux (m : ℕ) (h : m < n + 1) : decidable_rel (@le_aux _ α _ m h) :=
λ a b, begin
    induction m; simp [le_aux], apply_instance,
    from if h₀ : (a.to_fun ⟨m_n + 1, h⟩) < (b.to_fun ⟨m_n + 1, h⟩)
    then is_true (or.inl h₀)
    else if h₁ : (a.to_fun ⟨m_n + 1, h⟩) > (b.to_fun ⟨m_n + 1, h⟩)
    then is_false (λ h₁', begin 
        cases h₁',
        apply (not_lt_of_gt h₁) h₁',
        apply absurd h₁ (not_lt_of_le (le_of_eq h₁'.left)),
    end)
    else begin
        cases m_ih (nat.lt_of_succ_lt h),
        left, rintro (h_1' | ⟨h_1₁', h_1'₂⟩), apply absurd h_1' h₀, apply absurd h_1'₂ h_1,
        right, right, refine ⟨antisymm (le_of_not_lt h₁) (le_of_not_lt h₀), h_1⟩, 
    end
end

instance mon_le_decidable_rel : decidable_rel ((≤) : (fin n →₀ α) → (fin n →₀ α) → Prop) := 
λ a b, by cases n; unfold has_le.le preorder.le mon_le; apply_instance

lemma le_mono_order_aux (m : ℕ) (h : m < n + 1) : ∀ a b w : (fin $ n + 1) →₀ α, le_aux m h a b →  le_aux m h (a + w) (b + w) :=
λ a b w, begin
    induction m;
    simp [le_aux],
    rintro (hab | ⟨hab₁, hab₂⟩), 
    exact or.inl hab,
    right, refine ⟨hab₁, (m_ih (nat.lt_of_succ_lt h) hab₂)⟩,
end

lemma le_mono_order : ∀ (a b w : fin n →₀ α), (a ≤ b) → ((a + w) ≤ (b + w)) := 
λ a b w, by cases n; simp [has_le.le, preorder.le, mon_le]; apply le_mono_order_aux

lemma le_mono_order' : ∀ (a b w : fin n →₀ α), (a ≤ b) → ((w + a) ≤ (w + b)) :=
by simp [add_comm]; apply le_mono_order

instance : decidable_linear_order (fin n →₀ α) := {
    le := mon_le,
    le_refl := mon_le_refl,
    le_trans := mon_le_trans,
    le_antisymm := mon_le_antisymm,
    le_total := mon_le_total,
    decidable_le := mon_le_decidable_rel,
}

instance : decidable_linear_ordered_cancel_comm_monoid (fin n →₀ α) := {
    add_left_cancel := λ a b c, (finsupp.add_left_cancel a b c).1,
    add_right_cancel := λ a b c, (finsupp.add_right_cancel a b c).1,
    add_le_add_left := λ a b h c, le_mono_order' a b c h,
    le_of_add_le_add_left := λ a b c h, begin
        by_cases hbc : b ≤ c, assumption,
        rw [←lt_iff_not_ge, lt_iff_le_and_ne] at hbc,
        have h' : a + c ≤ a + b, apply le_mono_order', exact hbc.left,
        have h_eq := (finsupp.add_left_cancel a c b).1 (antisymm h' h),
        apply absurd h_eq hbc.right,
    end,
    ..finsupp.decidable_linear_order,
    ..finsupp.add_comm_monoid
}
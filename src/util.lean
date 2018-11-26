import data.set.lattice

namespace nat

lemma lt_lt_antisym : ∀ {a b : ℕ}, a < b → b < a → false
| a b le₀ le₁ := begin apply (absurd le₀ (not_lt_of_ge (le_of_lt le₁))), end

lemma not_le_not_ge_eq (a b : ℕ) : ¬ a < b → ¬ b < a → a = b :=
begin
    intros,
    have h := lt_trichotomy a b,
    cases h, exact absurd h a_1,
    cases h, assumption, exact absurd h a_2,
end

lemma sup_ab_eq_a_or_b : Π (a b : ℕ), a ⊔ b = a ∨ a ⊔ b = b
| a b :=
begin
    intros,
    by_cases (a ≤ b), right, apply lattice.sup_of_le_right, assumption,
    by_cases (b ≤ a), left, apply lattice.sup_of_le_left, assumption,
    rw not_le at *, apply false.elim, dedup, apply nat.lt_lt_antisym h h_1,
end

end nat

namespace logic

lemma demorgan : Π {a b : Prop}, ¬ (a ∨ b) → ¬ a ∧ ¬ b :=
begin
    intros, constructor,
    intro, apply a_1, left, assumption,
    intro, apply a_1, right, assumption,
end

end logic
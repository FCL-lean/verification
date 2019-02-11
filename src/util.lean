
import data.set.lattice

section classes
set_option old_structure_cmd true

class monomial_order (α : Type*) extends has_add α, linear_order α := 
(mono_order : ∀ a b w : α, (a ≤ b) → (a + w) ≤ (b + w))

class decidable_monomial_order (α : Type*) extends monomial_order α, decidable_linear_order α

end classes

namespace nat
lemma lt_lt_antisym : ∀ {a b : ℕ}, a < b → b < a → false
| a b le₀ le₁ := begin apply (absurd le₀ (not_lt_of_ge (le_of_lt le₁))), end

lemma left_lt_of_add_lt : ∀ {a b n : ℕ}, a + b < n → a < n :=
λ a b n h, by apply lt_of_le_of_lt (nat.le_add_right a b) h


lemma not_le_not_ge_eq {a b : ℕ} : ¬ a < b → ¬ b < a → a = b :=
begin
    intros,
    have h := lt_trichotomy a b,
    cases h, exact absurd h a_1,
    cases h, assumption, exact absurd h a_2,
end

end nat
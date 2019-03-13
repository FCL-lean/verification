
section relation

inductive rtc {α : Sort*} (r : α → α → Prop) : α → α → Prop
| refl  : ∀ a, rtc a a
| base  : ∀ a b, r a b → rtc a b
| trans : ∀ a b c, rtc a b → rtc b c → rtc a c

end relation

namespace nat

lemma left_lt_of_add_lt : ∀ {a b n : ℕ}, a + b < n → a < n :=
λ a b n h, by apply lt_of_le_of_lt (nat.le_add_right a b) h

end nat
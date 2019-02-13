
import data.set.lattice

namespace nat
lemma left_lt_of_add_lt : ∀ {a b n : ℕ}, a + b < n → a < n :=
λ a b n h, by apply lt_of_le_of_lt (nat.le_add_right a b) h

end nat
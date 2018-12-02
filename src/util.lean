import data.set.lattice
import data.finset

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
universe u
lemma dite_true {c : Prop} [h: decidable c] {α : Sort u} {b₁ : c → α} {b₂ : ¬ c → α}
    : Π (ev: c = true), dite c b₁ b₂ = b₁ (@eq.subst _ id _ _ (eq.symm ev) true.intro)
 :=
begin
    intros,
    unfold dite, tactic.unfreeze_local_instances, cases h;
    simp, apply false.elim, apply h, rw ev, trivial,
    trivial,
end
lemma dite_true' {c : Prop} [h: decidable c] {α : Sort u} {b₁ : c → α} {b₂ : ¬ c → α}
    : Π ev: c, dite c b₁ b₂ = b₁ ev
 :=
begin
    intros, unfold dite,
    tactic.unfreeze_local_instances,
    cases h, apply false.elim, apply h, assumption,
    trivial,
end

lemma dite_false {c : Prop} [h: decidable c] {α : Sort u} {b₁ : c → α} {b₂ : ¬ c → α}
    : Π (ev: c = false), dite c b₁ b₂ = b₂ (λ neq, begin rw ev at neq, assumption end)
 :=
begin
    intros, unfold dite,
    tactic.unfreeze_local_instances, cases h; simp,
    apply false.elim, rw ev at h, assumption,
end

lemma dite_false' {c : Prop} [h: decidable c] {α : Sort u} {b₁ : c → α} {b₂ : ¬ c → α}
    : Π ev: ¬ c, dite c b₁ b₂ = b₂ ev
 :=
begin
    intros, unfold dite,
    tactic.unfreeze_local_instances,
    cases h,
    simp, apply false.elim, apply ev, assumption,
end



end logic
universe α

def rel (A : Sort α) := A → A → Prop

namespace list
variables {α : Type*} [decidable_eq α]

lemma mem_to_set {a : α} {l : list α} : a ∈ l ↔ a ∈ l.to_finset.to_set := 
begin
    apply iff.intro; intro h, rw [←list.mem_to_finset, ←finset.mem_coe] at h, assumption,
    have h' : a ∈ l.to_finset, rw [←finset.mem_coe], exact h,
    simp at h', assumption,
end

lemma subset_to_set {l₁ l₂ : list α} : l₁ ⊆ l₂ ↔ l₁.to_finset.to_set ⊆ l₂.to_finset.to_set :=
begin
    apply iff.intro; unfold has_subset.subset list.subset set.subset;
    intros h a ha, 
    rw ←mem_to_set at *, exact h ha,
    rw mem_to_set at *, exact h ha,
end

end list

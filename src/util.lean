import data.set.lattice
import data.finset

universe u
def not' : Type u → Prop := λ a, a → false
notation `¬'` a := not' a

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

lemma sup_ab_eq_a_or_b : Π (a b : ℕ), a ⊔ b = a ∨ a ⊔ b = b
| a b :=
begin
    intros,
    by_cases (a ≤ b), right, apply lattice.sup_of_le_right, assumption,
    by_cases (b ≤ a), left, apply lattice.sup_of_le_left, assumption,
    rw not_le at *, apply false.elim, dedup, apply nat.lt_lt_antisym h h_1,
end

lemma zero_of_add {a b : ℕ} : a + b = a → b = 0 :=
λ h, if h₁ : b > 0 
    then begin 
        have h₂ : a + b > a := nat.lt_add_of_pos_right h₁, rw h at h₂,
        apply absurd h₂ (not_lt_of_le (le_of_eq rfl)),
    end
    else by simp at h₁; assumption

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

lemma ite_true {c : Prop} [h: decidable c] {α : Sort u} {b₁ b₂ : α}
    : Π (ev: c = true), ite c b₁ b₂ = b₁ :=
begin
    intros, unfold ite, 
    tactic.unfreeze_local_instances,
    cases h, apply false.elim, apply h, rw ev, trivial,
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

lemma ite_true' {c : Prop} [h: decidable c] {α : Sort u} {b₁ b₂ : α}
    : Π (ev: c), ite c b₁ b₂ = b₁ :=
begin
    intros, unfold ite, 
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

lemma ite_false {c : Prop} [h: decidable c] {α : Sort u} {b₁ b₂ : α}
    : Π (ev: c = false), ite c b₁ b₂ = b₂ :=
begin
    intros, unfold ite, 
    tactic.unfreeze_local_instances,
    cases h, simp,
    apply false.elim, rw ev at *, assumption,
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

lemma ite_false' {c : Prop} [h: decidable c] {α : Sort u} {b₁ b₂ : α}
    : Π (ev: ¬ c), ite c b₁ b₂ = b₂ :=
begin
    intros, unfold ite, 
    tactic.unfreeze_local_instances,
    cases h, simp,
    apply false.elim, apply ev, assumption,
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

lemma last_mem (α : Sort*): Π (l : list α) (h : l ≠ list.nil),  
        l.last h ∈ l :=
begin
    intro l,
    induction l;
    intros, apply false.elim, apply h, trivial,
    simp, cases l_tl,
    left, simp,
    right, simp,
    apply l_ih,
end

end list

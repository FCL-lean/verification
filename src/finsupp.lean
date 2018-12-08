import data.finsupp
import util
import finite
import fin
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
namespace finsupp

section general
variables [decidable_eq α] [decidable_eq β]

section has_zero
variables [has_zero β] 

section finite_dom
variables [fina: finite α]
section has_le
variables [has_le β]


def leading_term_le (a b: α →₀ β): Prop 
    := fina.val.fold (∧) true (λ elem, a elem ≤ b elem)

end has_le
end finite_dom

lemma in_not (a : α →₀ β) : ∀ x : α, x ∈ a.support ∨ x ∉ a.support := 
    by intro; apply classical.or_not

lemma support_singleton_neq_zero {a : α →₀ β} {x : α} (h : a.support = {x}) : a x ≠ 0 :=
by apply (a.mem_support_to_fun x).1; simp [h]

lemma support_singleton_eq_zero {a : α →₀ β} {x y : α} (h₁ : x ≠ y) (h₂ : a.support = {y}) : a x = 0 :=
by rw [←not_mem_support_iff]; simp [h₁, h₂]

def single_inj1 : Π {a b: α} {c d: β}, (c ≠ 0) → single a c = single b d → a = b :=
begin
    intros, unfold single at *, simp at a_1,
    by_cases c = 0, rw h at *, simp at *,
    apply false.elim; assumption,
    simp [a_1] at a_2,
    by_cases d = 0, rw h at *, simp at *,
    apply false.elim; assumption,
    simp [a_1, h] at a_2,
    cases a_2, rw finset.singleton_inj at a_2_left,
    assumption,
end

def single_inj2 : Π {a b: α} {c d: β}, single a c = single b d → c = d :=
begin
    intros, unfold single at *, simp at a_1,
    by_cases c = 0; rw h at *;
    by_cases d = 0; rw h at *,
    simp [h] at *, cases a_1, 
    unfold finset.singleton has_emptyc.emptyc finset.empty at a_1_left,
    simp at a_1_left, apply false.elim, assumption,
    tactic.unfreeze_local_instances, dedup, simp [h] at a_1,
    apply false.elim, assumption,
    tactic.unfreeze_local_instances, dedup, simp [h, h_1] at a_1,
    cases a_1, rw finset.singleton_inj at a_1_left,
    rw a_1_left at *, let m := congr_fun a_1_right b,
    simp at m, assumption,
end

def single_eqz : Π {a : α} {b : β}, single a b = 0 → b = 0 :=
begin
    intros a b sin,
    unfold single at sin,
    by_cases b = 0,
    assumption,
    simp [h] at sin,
    apply false.elim,
    have m := congr_arg finsupp.support sin, simp at m,
    assumption,
end

lemma coe_f : Π (a : α →₀ β) (n : α), a n = a.to_fun n := λ a n, rfl
end has_zero

section canonically_ordered_monoid
variables [canonically_ordered_monoid β]

lemma support_contain_a (a b : α →₀ β) : a.support ⊆ (a + b).support :=
begin
    unfold has_subset.subset,
    intros a_1 h,
    let ha := (a.mem_support_to_fun a_1).elim_left h,
    have hab : (a + b).to_fun a_1 ≠ 0,
    rw ←coe_f at *,
    simp, intro ha',
    apply (absurd ha' ha),
    apply ((a + b).mem_support_to_fun a_1).elim_right hab,
end

lemma support_contain_b (a b : α →₀ β) : b.support ⊆ (a + b).support := by rw add_comm; apply support_contain_a

lemma union_support_contain (a b : α →₀ β) : a.support ∪ b.support ⊆ (a + b).support :=
begin
    have ha := support_contain_a a b,
    have hb := support_contain_b a b,
    intros elem p,
    have lem := finset.mem_union.elim_left p,
    cases lem,
    exact ha lem,
    exact hb lem,
end

end canonically_ordered_monoid
end general

section fin_n
variable {n : ℕ}
include n

lemma leading_term_le_all (a b: fin n →₀ ℕ): leading_term_le a b →
    ∀ (x : fin n), a x ≤ b x :=
begin
    sorry
end
omit n
def leading_term_sub_aux : Π {n : ℕ}(a b: fin n →₀ ℕ),
     (∀ x, b x ≤ a x) → Π (m : ℕ), m < n → (fin n →₀ ℕ)
| 0 a b prf m prf2 := 0
| (nat.succ n) a b prf 0 prf2 := single 0 (a 0 + b 0)
| (nat.succ n) a b prf (nat.succ m) prf2 
    := single (nat.succ m) (a ⟨nat.succ m, prf2⟩ - b ⟨nat.succ m, prf2⟩) 
       + leading_term_sub_aux a b prf m (nat.lt_of_succ_lt prf2)
def leading_term_sub (a b: fin n →₀ ℕ) 
    : leading_term_le b a → (fin n →₀ ℕ) := 
λ ltle,
begin
    have le_all := leading_term_le_all b a ltle,
    cases n, exact 0,
    exact leading_term_sub_aux a b le_all n (by  constructor),
end
def le_aux : ((fin $ n + 1) →₀ ℕ) → ((fin $ n + 1) →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (m + 1) := a (m + 1) < b (m + 1) ∨ (a m = b m ∧ le_aux a b m)

protected def le : Π {n} (a b: fin n →₀ ℕ), Prop 
| 0 a b := true
| (nat.succ n) a b := le_aux a b n

instance : has_le (fin n →₀ ℕ) := ⟨finsupp.le⟩
instance : is_total (fin n →₀ ℕ) (≤) := sorry
instance : lattice.has_bot (fin n →₀ ℕ) := ⟨(0: fin n →₀ ℕ)⟩
lemma le_refl_aux (m : ℕ): ∀ a : (fin $ n + 1) →₀ ℕ, le_aux a a m :=
begin
    intros, induction m,
    unfold le_aux,
    unfold le_aux, right,
    apply and.intro, refl, exact m_ih,
end

lemma le_refl : ∀ a : (fin n) →₀ ℕ, finsupp.le a a :=
begin
    intro a, cases n; unfold finsupp.le,
    apply le_refl_aux,
end

lemma le_trans : ∀ a b c : (fin n) →₀ ℕ, a ≤ b → b ≤ c → a ≤ c := sorry

lemma le_antisymm : ∀ (a b : fin n →₀ ℕ), a ≤ b → b ≤ a → a = b := sorry


lemma zero_le : ∀ (a : fin n →₀ ℕ), ⊥ ≤ a := sorry

instance : decidable_linear_order (fin n →₀ ℕ) := sorry
instance : lattice.semilattice_sup_bot (fin n →₀ ℕ) := {
    bot := 0,
    le := finsupp.le,
    le_refl := le_refl,
    le_trans := le_trans,
    le_antisymm := le_antisymm,
    bot_le := zero_le,
    sup := max,
    le_sup_left := sorry,
    le_sup_right := sorry,
    sup_le := λ a b c, sorry
}
end fin_n

end finsupp
import data.finset
import data.finsupp
import util

namespace finset

namespace nat

lemma max_le (a b : finset ℕ) : finset.sup a id ≤ finset.sup (a ∪ b) id :=
begin
    rw finset.sup_union,
    apply lattice.le_sup_left,
end


lemma sup_max : Π (a : finset ℕ), a ≠ ∅ → some (a.sup id) = a.max
| a :=
begin
    apply finset.induction_on a,
    intros, apply false.elim, apply a_1; trivial,
    intros, intros, by_cases (s = ∅),
    rw h, simp, unfold option.lift_or_get,
    let ih := a_3 h, simp, rw ←ih, unfold option.lift_or_get,
    constructor, 
end

lemma sup_id_insert : Π (a : finset ℕ) (b : ℕ), a.sup id ∈ a
    → (insert b a).sup id ∈ insert b a :=
begin
    intros,
    apply finset.induction_on a,
    simp,
    intros,
    rw finset.insert.comm,
    rw finset.sup_insert,
    unfold id,
    have h := nat.sup_ab_eq_a_or_b a_2 (finset.sup (insert b s) id),
    cases h; rw h,
    simp, apply finset.mem_insert_of_mem, assumption
end

lemma union_sup_in_a_or_b : Π (a b : finset ℕ),
    b ≠ ∅ →
    (a ∪ b).sup id ∈ a
    ∨ (a ∪ b).sup id ∈ b
| a :=
begin
    apply finset.induction_on a,
    intros, right, simp,
    apply mem_of_sup_id, assumption,
    intros c s notin ih b notemp,
    have iha := ih b notemp,
    cases iha;
    rw finset.insert_union;
    have m := sup_id_insert (s ∪ b) c _,
    rw [←finset.mem_union, finset.insert_union], assumption,
    rw [finset.mem_union], left, assumption,
    rw [←finset.mem_union, finset.insert_union], assumption,
    rw [finset.mem_union], right, assumption,
end

end nat

section general
parameters {α : Type*}

lemma ne_empty_iff_exists_mem {s : finset α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
begin
    simp [eq_empty_iff_forall_not_mem],
    apply @not_forall_not _ _ (classical.dec _),
end

section semilattice
parameters [lattice.semilattice_sup_bot α]
lemma ne_empty_of_sup_ne_bot {s : finset α} : s.sup id ≠ ⊥ → s ≠ ∅ := λ h₀ h₁, by simp [h₁, sup_empty] at h₀; exact h₀

end semilattice

section decidable_semilattice
parameters [lattice.semilattice_sup_bot α] [decidable_rel ((≤) : α → α → Prop)] [is_total α (≤)]

lemma mem_of_sup_id : ∀ {a : finset α}, a ≠ ∅ → a.sup id ∈ a
| a := finset.induction_on a (λ a, false.elim (a (refl _)))
    (λ x y notin ih notempty, begin 
        rw [finset.insert_eq, finset.sup_union, finset.mem_union, finset.sup_singleton],
        simp,
        from if h₁ : y = ∅ 
        then begin
            left,
            rw [h₁, finset.sup_empty, lattice.sup_bot_eq],
        end
        else begin
            from if h₂ : x < y.sup id
            then begin
                right, 
                rw [lattice.sup_of_le_right (le_of_lt h₂)],
                apply ih h₁,
            end
            else begin
                left,
                letI : linear_order α := { le_total := is_total.total (≤), .. _inst_1 },
                rw [lattice.sup_of_le_left (le_of_not_lt h₂)],
            end
        end
    end)

end decidable_semilattice

section sort

variables {α : Type*}
variables [decidable_eq α]
variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r]

lemma sort_nil : sort r ∅ = [] := by apply quot.lift_beta id; intros; assumption

lemma sort_empty_nil {s : finset α} : sort r s = [] ↔ s = ∅ :=
begin
    apply iff.intro; intro h,
    from if hs : s = ∅ 
    then by assumption
    else begin      
        rw [←ne.def, ne_empty_iff_exists_mem] at hs,
        cases hs, rw [←finset.mem_sort r, h] at hs_h,
        cases hs_h,
    end,
    rw h, apply sort_nil,
end

lemma sort_ne_empty_ne_nil {s : finset α} : s ≠ ∅ → sort r s ≠ [] :=
λ hs hss, begin
    rw sort_empty_nil at hss,
    apply absurd hss hs,
end

end sort

end general

end finset
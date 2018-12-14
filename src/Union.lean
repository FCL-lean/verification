import data.finset
import data.set.lattice
import util
import seq

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

def fold' : Π {α : Type u} (C : list α → Sort v) (l : list α), 
    C [] → (Π (e : α) (l' : list α), e ∈ l → l' ⊆ l → C l' → C (e :: l')) → C l
| α C [] := λ h_nil ih, by assumption
| α C [hd] := λ h_nil ih, by apply ih hd [] (list.mem_singleton_self hd) (list.nil_subset [hd]) h_nil
| α C (hd :: tl_hd :: tl_tl) := λ h_nil ih, 
begin
    apply ih hd (tl_hd :: tl_tl) (list.mem_cons_self hd (tl_hd :: tl_tl)) (list.subset_cons hd (tl_hd :: tl_tl)),
    have ih' : Π (e : α) (l' : list α), e ∈ (list.cons tl_hd tl_tl) → l' ⊆ (tl_hd :: tl_tl) → C l' → C (e :: l'),
    intros e l' e_mem l'_sub,
    apply ih e l' ((list.mem_cons_iff e hd (tl_hd :: tl_tl)).2 (or.inr e_mem)) (list.subset_cons_of_subset hd l'_sub),
    apply fold' C (tl_hd :: tl_tl) h_nil ih',
end

def flatten : ∀ (l : list α), (α → set β) → set β
| [] := λ f, ∅ 
| (hd :: tl) := λ f, f hd ∪ (flatten tl f)

@[simp] lemma flatten_nil : ∀ f : α → set β, flatten [] f = ∅ := λ f, rfl
@[simp] lemma flatten_cons : ∀ {f : α → set β} {hd : α} {tl : list α}, flatten (hd :: tl) f = f hd ∪ flatten tl f := λ f hd tl, rfl

namespace set
variables [decidable_eq β]

lemma flatten_eq_max (s : seqR.seq_R (set β) (<)) (hd : ℕ) (tl : list ℕ) : flatten (hd :: tl) s.1 = s.1 (tl.foldr max hd) :=
begin
    induction tl; simp at *, 
    rw [←union_assoc, union_comm (s.1 hd), union_assoc, tl_ih],
    from if h : tl_hd ≥ (list.foldr max hd tl_tl)
    then begin
        rw max_eq_left h,
        have H : s.val (list.foldr max hd tl_tl) ⊆ s.val tl_hd, apply seqR.le_trans_of_lt s h,
        rw union_eq_self_of_subset_right H,
    end
    else begin
        rw max_eq_right (le_of_not_ge h),
        have H : s.val tl_hd ⊆ s.val (list.foldr max hd tl_tl), apply seqR.le_trans_of_lt s (le_of_not_ge h),
        rw union_eq_self_of_subset_left H,
    end
end

lemma max_set_of_list_subset_exists {s : seqR.seq_R (set β) (<)} {gs : list β} (h : ↑(gs.to_finset) ⊆ Union (λ (i : ℕ), (s.1 i))) : 
    ∃ i : ℕ, ↑(gs.to_finset) ⊆ s.1 i ∧ s.1 i ⊆ Union (λ (i : ℕ), (s.1 i)) :=
begin
    have H := fold' (λ l : list β, (∃ i : list ℕ, ↑l.to_finset ⊆ flatten i s.1)) gs (by simp)
        (begin
            intros e l' e_mem l'_sub ih, rw list.mem_to_set at e_mem,
            have e_mem' := h e_mem, simp at e_mem',
            cases e_mem', cases ih,
            apply exists.intro (list.cons e_mem'_w ih_w),
            change (list.to_finset (e :: l')).to_set ⊆ s.1 e_mem'_w ∪ flatten ih_w s.1,
            intros x hx, rw ←list.mem_to_set at hx,
            simp,
            cases hx, rw hx at *, apply or.inl e_mem'_h,
            have hx' : x ∈ l'.to_finset.to_set,
                rw ←list.mem_to_set, unfold has_mem.mem, assumption,
            apply or.inr (ih_h hx'),
        end),
    cases H,
    cases H_w, simp [subset_empty_iff] at H_h, rw H_h, apply exists.intro 0,
    apply and.intro, simp, apply subset_Union,
    rw flatten_eq_max s H_w_hd H_w_tl at H_h,
    apply exists.intro (list.foldr max H_w_hd H_w_tl), 
    apply and.intro H_h, apply subset_Union,
end

end set

import data.finset
import data.set.lattice
import util

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

def fold' : Π {α : Type u} (C : list α → Sort v) (l : list α), 
    C [] → (Π (e : α) (l' : list α), e ∈ l → l' ⊆ l → C l' → C (e :: l')) → C l := sorry

def flatten : ∀ (l : list α), (α → set β) → set β
| [] := λ f, ∅ 
| (hd :: tl) := λ f, f hd ∪ (flatten tl f)

@[simp] lemma flatten_nil : ∀ f : α → set β, flatten [] f = ∅ := λ f, rfl
@[simp] lemma flatten_cons : ∀ {f : α → set β} {hd : α} {tl : list α}, flatten (hd :: tl) f = f hd ∪ flatten tl f := λ f hd tl, rfl

namespace set
variables [comm_ring β] [decidable_eq β] [lattice.semilattice_sup_bot ι] [decidable_rel ((≤) : ι → ι → Prop)] [is_total ι (≤)] [decidable_eq ι]

instance : decidable_linear_order ι := 
    { decidable_le := _inst_4,
      decidable_eq := _inst_6,
      le_total := is_total.total (≤),
    .. _inst_3 }

lemma union_of_head_le {s : ι → set β} {hd tl_hd : ι} {tl_tl : list ι} (h : hd ≤ tl_hd) :
     s tl_hd ∪ s (list.foldl max hd tl_tl) = s tl_hd ∪ s (list.foldl max tl_hd tl_tl) :=
begin
    revert hd tl_hd, induction tl_tl; intros,
    simp,
end

lemma flatten_eq_max {s : ι → set β} {hd : ι} {tl : list ι} : flatten (hd :: tl) s = s (tl.foldl max hd) :=
begin
    induction tl; simp at *,
    from if h : hd ≤ tl_hd
    then begin
        rw [max_eq_right h, ←union_assoc, union_comm (s hd), union_assoc, tl_ih],
    end
    else sorry
end


set_option trace.simplify.rewrite true
def mem_set_max {s : ι → set β} {gs : list β} (h : ↑(gs.to_finset) ⊆ Union s) : 
    ∃ i : ι, ↑(gs.to_finset) ⊆ s i ∧ s i ⊆ Union s := 
begin
    --simp [has_subset.subset, set.subset] at h,
    have H := fold' (λ l : list β, (∃ i : list ι, ↑l.to_finset ⊆ flatten i s)) gs (by simp) 
        (begin 
            intros, rw list.mem_to_set at a,
            have h' := h a, simp at h',
            cases h', cases a_2,
            apply exists.intro (list.cons h'_w a_2_w), 
            change (list.to_finset (e :: l')).to_set ⊆ s h'_w ∪ flatten a_2_w s,
            intros x hx, rw ←list.mem_to_set at hx,
            simp,
            cases hx, rw hx at *, apply or.inl h'_h,
            have hx' : x ∈ l'.to_finset.to_set,
                rw ←list.mem_to_set, unfold has_mem.mem, assumption,
            apply or.inr (a_2_h hx'),
        end),
    cases H,
    cases H_w, simp [subset_empty_iff] at H_h, rw H_h, apply exists.intro (⊥ : ι),
    apply and.intro; simp [Union, lattice.supr, lattice.Sup, range, lattice.has_Sup.Sup, lattice.complete_lattice.Sup],
    intros a ha, simp, apply exists.intro (s ⊥), finish,
    have H_h' : flatten (list.cons H_w_hd H_w_tl) s = s ((list.cons H_w_hd H_w_tl).foldl max H_w_hd),
    induction H_w_tl; simp,
end

end set

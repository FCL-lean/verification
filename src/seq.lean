import data.stream
import noetherian
import ideal
import util

universe u
namespace seqR
section seq



def seq (α : Type u): Type u := ℕ → α

def seq_cons {α : Type u}: α → seq α → seq α
| elem seq nat.zero := elem
| elem seq (nat.succ n) := seq n


def seq_R (α : Type u) (R : α → α → Prop) := { f : stream α // ∀ n, R (f (n + 1)) (f n)}


variable {α : Type u}
variable {R : α → α → Prop}

def seq_R_cons : Π (elem: α) (f : seq_R α R), R (f.1 0) elem → seq_R α R 
    := λ elem f r, ⟨seq_cons elem f.1, λ n, begin cases n, assumption, exact f.2 n, end⟩



def seq_R_s (α: Type*) (elem : α) (R : α → α → Prop) : Type u := { f : seq_R α R // f.1 0 = elem }


def head (s: seq_R α R): α := s.1 0

def tail (s: seq_R α R): seq_R α R :=
    ⟨s.1.tail, λ n, s.2 (n + 1)⟩ 






protected def coinduction : 
    ∀ {s₁ s₂: seq_R α R}, head s₁ = head s₂ → 
        (∀ (β : Type u) (fr: seq_R α R → β), fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
| ⟨f₁, p₁⟩ ⟨f₂, p₂⟩ he ft 
    := subtype.eq (stream.coinduction he (λ β tp eqt, (ft β (λ s, tp s.1))))

@[simp]
def nth (s: seq_R α R) (n: ℕ): α := s.1 n


def no_inf_chain (α: Type*) (R: α → α → Prop): Prop := ¬' seq_R α R

def no_inf_chain_s (α: Type*) (R: α → α → Prop) (elem : α): Prop := ¬' seq_R_s α elem R
lemma no_inf_chain_s_lem (α: Type*) (R: α → α → Prop): 
    no_inf_chain α R → ∀ elem, no_inf_chain_s α R elem :=
begin
    intros, intro a_1,
    apply a, apply subtype.mk a_1.1.1,
    intros, apply a_1.1.2,
end

lemma no_inf_chain_iff_emb [is_strict_order α R] : no_inf_chain α R → ¬ nonempty (((>) : ℕ → ℕ → Prop) ≼o R) :=
begin
    intros no_inf nonemp,
    cases nonemp,
    apply no_inf,
    cases nonemp with f o,
    apply subtype.mk f.1, intro,
    change R (f (n + 1)) (f n),
    rw [←o], constructor,
end

lemma no_inf_chain_wf (α: Type*) (R: α → α → Prop) [is_strict_order α R]: no_inf_chain α R → well_founded R :=
begin
    intro,
    rw order_embedding.well_founded_iff_no_descending_seq,
    exact no_inf_chain_iff_emb a,
end



def seq_R_coe {α β : Type*} (ra: rel α) (rb: rel β) (f : α -> β) : 
    seq_R α ra -> (∀ a b, ra a b -> rb (f a) (f b)) -> seq_R β rb :=
λ sra hab, ⟨sra.1.map f, λ n, hab (sra.1 (n + 1)) (sra.1 n) (sra.2 n)⟩

section preorder
variables [partial_order α]

protected lemma lt_trans_of_lt (s : seq_R α (>)) : ∀ {m n}, m < n → (s.1 m) < (s.1 n) :=
λ m n hmn, begin
    rw ←nat.add_sub_cancel' hmn,
    apply @nat.strong_induction_on (λ x, (s.val m) < (s.val ((m + 1) + x))) (n - (m + 1)),
    intros k ih,
    cases k, apply s.2,
    have h := ih k (nat.lt_succ_self k),
    apply lt_trans h (s.2 (m + 1 + k)),
end

protected lemma le_trans_of_lt (s : seq_R α (>)) : ∀ {m n}, m ≤ n → s.1 m ≤ s.1 n :=
λ m n hmn, begin
    from if h : m = n
    then by finish
    else by apply le_of_lt (seqR.lt_trans_of_lt s (lt_of_le_of_ne hmn h))
end

end preorder

section set
variables {β : Type*} [decidable_eq β]

lemma max_set_of_list_subset_exists (s : seqR.seq_R (set β) (>)) (gs : finset β) (h : ↑gs ⊆ (⋃ (i : ℕ), (s.1 i))) : 
    ∃ i : ℕ, ↑gs ⊆ s.1 i :=
begin
    revert h,
    apply finset.induction_on gs, simp,
    intros a s' a_nm_s' ih as'_sub,
    simp [set.insert_subset] at as'_sub,
    cases as'_sub.left, cases (ih as'_sub.right),
    apply exists.intro (max w w_1),
    simp [set.insert_subset],
    apply and.intro (set.mem_of_subset_of_mem (seqR.le_trans_of_lt s (le_max_left w w_1)) h)
    (set.subset.trans h_1 (seqR.le_trans_of_lt s (le_max_right w w_1))),
end

section ideal
variables [comm_ring β] 

def seq_ideal (s : seqR.seq_R (ideal β) (>)) : ideal β := {
    carrier := (⋃ (i : ℕ), (↑(s.1 i) : set β) ),
    zero := by simp,
    add := begin 
        intros x y hx hy, simp at *,
        cases hx, cases hy,
        apply exists.intro (max hx_w hy_w),
        have hx' := ideal.mem_of_mem_le_ideal x hx_h (seqR.le_trans_of_lt s (le_max_left hx_w hy_w)),
        have hy' := ideal.mem_of_mem_le_ideal y hy_h (seqR.le_trans_of_lt s (le_max_right hx_w hy_w)),
        exact (s.1 (max hx_w hy_w)).add hx' hy',
    end,
    smul := begin
        intros c x hx, simp at *, cases hx,
        apply exists.intro hx_w,
        exact (s.1 hx_w).smul c hx_h,
    end,
}

section noetherian
variables [noetherian β]

lemma ideal_contain_generator_eq_Union (s : seqR.seq_R (ideal β) (>)) :
    ∃ i : ℕ, ↑(s.1 i) = (⋃ (i : ℕ), (↑(s.1 i) : set β) ) :=
begin
    generalize hs' : seqR.seq_R_coe (>) (>) (λ i : ideal β, i.carrier) s (λ a b hab, by simp; finish) = s',
    have hss' : (⋃ (i : ℕ), (↑(s.1 i) : set β) ) = (⋃ (i : ℕ), s'.1 i),
        apply set.ext, intro x, simp [hs'.symm, seqR.seq_R_coe], finish,
    have hi : ↑(seq_ideal s) = (⋃ (i : ℕ), (↑(s.1 i) : set β) ), refl,
    have noe : ∃ (s' : finset β), ideal.span ↑s' = (seq_ideal s), apply _inst_3.fin_ideal,
    cases noe,
    have h : ↑noe_w ⊆ (⋃ (i : ℕ), s'.1 i),
        simp [hss'.symm, hi.symm, noe_h.symm, ideal.subset_span],
    
    have H := max_set_of_list_subset_exists s' noe_w h,
    cases H, apply exists.intro H_w, 
    apply set.eq_of_subset_of_subset,
    intros x hx, simp at *, apply exists.intro H_w, assumption,
    simp [hs'.symm, seqR.seq_R_coe, stream.map, ideal.subset_of_subset_carrier, ideal.span_le.symm, noe_h] at H_h, 
    rw [ideal.subset_of_le, hi] at H_h, assumption,
end

lemma ideal_no_inf_chain : seqR.no_inf_chain (ideal β) (>) :=
begin
    intro s, cases (ideal_contain_generator_eq_Union s),
    have H : ↑(s.1 (w + 1)) ⊆ ⋃ (i : ℕ), (↑(s.1 i) : set β),
        intros x hx, simp at *, apply exists.intro (w + 1), assumption,
    rw [←h, ←ideal.subset_of_le] at H,
    apply absurd (s.2 w) (not_lt_of_le H),
end

lemma ideal_wf : well_founded ((>) : rel (ideal β)) := no_inf_chain_wf _ _ ideal_no_inf_chain

instance : has_well_founded (ideal β) := ⟨_, ideal_wf⟩

end noetherian

end ideal
end set

end seq


end seqR
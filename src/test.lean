import data.finset
import linear_algebra.multivariate_polynomial
import ring_theory.ideals
import tactic.find
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}
variables [discrete_field α]
variables [decidable_eq α]
variables [comm_ring (mv_polynomial ℕ α)]

class is_monomial_order (α : Type*) (r : α → α → Prop) extends has_add α, is_linear_order α r :=
    (mono_order : ∀ a b w : α, (r a b) → r (a + w) (b + w) )

namespace finsupp

lemma in_not (a : ℕ →₀ ℕ) : ∀ x : ℕ, x ∈ a.support ∨ x ∉ a.support := 
    by intro; apply classical.or_not

def le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ m) := (a (nat.succ m) < b (nat.succ m)) ∨ 
                        ((a (nat.succ m) = b (nat.succ m)) ∧ le_aux a b m) 
    
def max (a : ℕ →₀ ℕ) : ℕ := a.support.sup id
def max_ab (a b : ℕ →₀ ℕ) : ℕ := (a.support ∪ b.support).sup id

protected def le : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → Prop := λ a b, le_aux a b $ max_ab a b
instance : has_le (ℕ →₀ ℕ) := ⟨finsupp.le⟩ 

protected def lt : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → Prop := λ a b, a ≤ b ∧ a ≠ b
instance : has_lt (ℕ →₀ ℕ) := ⟨finsupp.lt⟩

lemma add_gt (a b : ℕ →₀ ℕ) : a ≤ (a + b) := 
begin
    unfold has_le.le finsupp.le,
    induction (max_ab a (a + b)),
    all_goals {unfold le_aux},
    all_goals {simp},
    by_cases (b (nat.succ n) > 0), left, assumption,
    right,
    let h' := nat.le_zero_iff.elim_left (le_of_not_gt h),
    rw h', simp, assumption
end

lemma gt_max_not_in : ∀ (a : ℕ →₀ ℕ) (x : ℕ), (x > max a) → x ∉ a.support :=
begin
    intros a x h₁ h₂,
    unfold max at *,
    let h₃ : id x ≤ finset.sup (a.support) id := finset.le_sup h₂,
    rw id at *,
    apply (absurd h₁ (not_lt_of_ge h₃))
end

lemma gt_sup_eq_zero (a : ℕ →₀ ℕ) : ∀ k : ℕ, max a < k → a k = 0 :=
begin
    intros,
    have h : k ∉ a.support := gt_max_not_in a k a_1,
    have h' := in_not a k,
    cases h', exact absurd h' h,
    apply not_mem_support_iff.elim_left, assumption
end

lemma max_ab_ge_max_a : ∀ (a b : ℕ →₀ ℕ), max_ab a b ≥ max a :=
begin
    intros a b,
    unfold max_ab max,
    rw finset.sup_union, apply lattice.le_sup_left,
end

lemma max_ab_ge_max_b : ∀ (a b : ℕ →₀ ℕ), max_ab a b ≥ max b :=
begin
    intros a b,
    unfold max_ab max,
    rw finset.sup_union, apply lattice.le_sup_right,
end

lemma gt_max_ab_not_in : ∀ (a b : ℕ →₀ ℕ) (x : ℕ), (x > max_ab a b) → x ∉ a.support ∧ x ∉ b.support :=
begin
    intros a b x h₁,
    unfold max_ab at *, 
    rw finset.sup_union at *,
    have h₄ : finset.sup (a.support) id < x := lt_of_le_of_lt lattice.le_sup_left h₁,
    have h₅ : finset.sup (b.support) id < x := lt_of_le_of_lt lattice.le_sup_right h₁,
    apply and.intro, 
    all_goals {intro h₂},
    apply (gt_max_not_in a x h₄ h₂),
    apply (gt_max_not_in b x h₅ h₂),
end

lemma support_contain_a (a b : ℕ →₀ ℕ) : a.support ⊆ (a + b).support :=
begin
    unfold has_subset.subset,
    intros a_1 h,
    let ha := (a.mem_support_to_fun a_1).elim_left h,
    have hab : (a + b).to_fun a_1 ≠ 0,
    have r : ∀ x : (ℕ →₀ ℕ), x.to_fun = ⇑x, by intro; refl,
    rw r at *, simp, intro ha',
    apply (absurd ha' ha),
    apply ((a + b).mem_support_to_fun a_1).elim_right hab,
end

lemma support_contain_b (a b : ℕ →₀ ℕ) : b.support ⊆ (a + b).support := by rw add_comm; apply support_contain_a


lemma union_support_contain (a b : ℕ →₀ ℕ) : a.support ∪ b.support ⊆ (a + b).support :=
begin
    have ha := support_contain_a a b,
    have hb := support_contain_b a b,
    intros elem p,
    have lem := finset.mem_union.elim_left p,
    cases lem,
    exact ha lem,
    exact hb lem,
end

lemma finset_max_le (a b : finset ℕ) : finset.sup a id ≤ finset.sup (a ∪ b) id :=
begin
    rw finset.sup_union,
    apply lattice.le_sup_left,
end
lemma max_ab_lt_add (a b w : ℕ →₀ ℕ) : max_ab a b ≤ max_ab (a + w) (b + w) :=
begin
    unfold max_ab,
    have prf := λ (a b : ℕ →₀ ℕ), finset.subset.antisymm (union_support_contain a b) finsupp.support_add,
    repeat {rw [←prf] },
    rw [ finset.union_assoc, finset.union_comm b.support w.support ],
    rw [←finset.union_assoc w.support, finset.union_idempotent, 
         finset.union_comm w.support, ←finset.union_assoc],
    apply finset_max_le,
end

lemma le_of_succ_eq (a b : ℕ →₀ ℕ) (i  : ℕ) (hlei : le_aux a b i) 
      (hi_succ : a (i + 1) = b (i + 1)) : le_aux a b (i + 1) :=
begin
    unfold le_aux,
    apply or.inr, apply and.intro,
    repeat {assumption},
end

lemma le_of_succ_eqs (a b : ℕ →₀ ℕ) (i j : ℕ) (hlei : le_aux a b i) 
    (hk : ∀ k : ℕ, i < k → k ≤ (i + j) → a k = b k) : le_aux a b (i + j) :=
begin
    revert i,
    induction j,
    begin
        intros i hlei hk, assumption,
    end,
    begin
        intros i hlei hk,
        apply le_of_succ_eq,
        apply j_ih, assumption,
        intros k hik hki,
        apply (hk k hik (nat.le_succ_of_le hki)),
        apply hk,
        let h : i < i + nat.succ j_n := nat.lt_add_of_pos_right (nat.zero_lt_succ j_n),
        assumption, refl,
    end,
end

lemma le_add (a b w : ℕ →₀ ℕ) (i : ℕ) (hab : le_aux a b i) : le_aux (a + w) (b + w) i :=
begin
    induction i,
    all_goals {unfold le_aux at *, simp},
    assumption,
    cases hab, left, assumption,
    cases hab, apply or.inr, apply and.intro, assumption,
    apply (i_ih hab_right),
end

lemma mono_order_lem : ∀ (a b w : ℕ →₀ ℕ), (a ≤ b) → ((a + w) ≤ (b + w)) := 
begin 
    intros a b w hab,
    unfold has_le.le finsupp.le at *,
    apply le_add,
    have h := le_of_succ_eqs a b (max_ab a b) ((max_ab (a + w) (b + w)) - (max_ab a b)) hab _ ,
    rw nat.add_sub_of_le at h, assumption,
    swap,
    intros,
    rw [gt_sup_eq_zero a k, gt_sup_eq_zero b k],
    have h' := max_ab_ge_max_b a b,
    apply nat.lt_of_le_of_lt h' a_1,
    have h' := max_ab_ge_max_a a b,
    apply nat.lt_of_le_of_lt h' a_1,
    apply max_ab_lt_add,
end
lemma not_le_not_ge_eq (a b : ℕ) : ¬ a < b → ¬ b < a → a = b :=
begin
    intros,
    have h := lt_trichotomy a b,
    cases h, exact absurd h a_1,
    cases h, assumption, exact absurd h a_2,
end

instance : is_monomial_order (ℕ →₀ ℕ) finsupp.le := sorry
instance : decidable_rel finsupp.le := λ a b, 
begin 
    unfold finsupp.le,
    induction max_ab a b,
    unfold le_aux, apply_instance,
    unfold le_aux,
    by_cases (a (nat.succ n) < b (nat.succ n)),
    exact is_true (or.inl h),
    by_cases (a (nat.succ n) > b (nat.succ n)),
    let m : ¬ (a (nat.succ n) < b (nat.succ n) ∨ a (nat.succ n) = 
          b (nat.succ n) ∧ le_aux a b n),
    intro t, cases t with t'; dedup,
    exact h t',
    cases t, rw t_left at *, exact h h_1,
    exact is_false m,
    dedup, have m := not_le_not_ge_eq _ _ h h_1,
    cases ih,
    have m : ¬ (a (nat.succ n) < b (nat.succ n) ∨ a (nat.succ n) = 
          b (nat.succ n) ∧ le_aux a b n),
    intro, cases a_1,
    exact absurd a_1 h,
    cases a_1,
    exact absurd a_1_right ih,
    exact is_false m,
    exact is_true (or.inr (and.intro m ih)),
end

end finsupp


namespace mv_polynomial

def leading_term (p : mv_polynomial ℕ α) : mv_polynomial ℕ α := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, mv_polynomial.C (p.to_fun 0))
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in finsupp.single g (p.to_fun g))

def leading_term' (p : mv_polynomial ℕ α) : ℕ →₀ ℕ := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, 0)
        (λ nprf, list.last (p.support.sort finsupp.le) nprf)

def leading_coeff (p : mv_polynomial ℕ α) : α := 
   dite (p.support.sort finsupp.le = list.nil) 
        (λ prf, p.to_fun 0)
        (λ nprf, let g := list.last (p.support.sort finsupp.le) nprf 
                 in p.to_fun g)

def leading_term_le_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 ≤ b 0
| a b (nat.succ m) := a (nat.succ m) ≤ b (nat.succ m) ∧ leading_term_le_aux a b m 

def leading_term_le (a b : ℕ →₀ ℕ) : Prop := leading_term_le_aux a b (finsupp.max_ab a b)

protected def le (a b : mv_polynomial ℕ α) : Prop := leading_term_le a.leading_term' b.leading_term'
instance : has_le (mv_polynomial ℕ α) := ⟨mv_polynomial.le⟩ 

instance le_decidable (a b : mv_polynomial ℕ α) : decidable (a ≤ b) := sorry

def leading_term_lt_aux : (ℕ →₀ ℕ) → (ℕ →₀ ℕ) → ℕ → Prop
| a b 0 := a 0 < b 0
| a b (nat.succ m) := (a (nat.succ m) < b (nat.succ m) ∧ leading_term_le_aux a b m)
                    ∨ (a (nat.succ m) ≤ b (nat.succ m) ∧ leading_term_lt_aux a b m)

protected def lt (a b : mv_polynomial ℕ α) : Prop 
    := leading_term_lt_aux a.leading_term' b.leading_term' (finsupp.max_ab a.leading_term' b.leading_term') 
instance : has_lt (mv_polynomial ℕ α) := ⟨mv_polynomial.lt⟩ 

instance lt_decidable (a b : mv_polynomial ℕ α) : decidable (a < b) := sorry

universes u v
inductive ind_or {κ : Type u} (r r' : κ → κ → Prop) : κ → κ → Prop
| fst : ∀ (a b : κ), r a b → ind_or a b
| snd : ∀ (a b : κ), r' a b → ind_or a b
| trans_fst : ∀ (a b c: κ), r a b → ind_or b c → ind_or a c
| trans_snd : ∀ (a b c : κ), r' a b → ind_or b c → ind_or a c
open prod
def lex_accessible {α : Type u} {β : Type v} {ra  : α → α → Prop} 
   {rb  : β → β → Prop} {a} (aca : acc ra a) (acb : ∀ b, acc rb b): ∀ b, acc (lex ra rb) (a, b) :=
  acc.rec_on aca (λ xa aca iha b,
    acc.rec_on (acb b) 
       (λ (a : β) (b : ∀ (y : β), rb y a → acc rb y) (c : ∀ (y : β), 
          rb y a → acc (lex ra rb) (xa, y)), {! !}))


def inf_or_acc {κ : Type u} : Π (r r': κ → κ → Prop) (a b : κ), 
    acc r a → acc r' b → ∀ (y : κ), ind_or r r' y a → acc (ind_or r r') y
| r r' a b m@(acc.intro t ac) m'@(acc.intro t' ac') y m''@(ind_or.fst ._ ._ rab r'') :=
    inf_or_acc r r' a b (begin end) (begin end) y m''
| r r' a b (well_founded.intro ac) (well_founded.intro ac') y ind := 
| r r' a b (well_founded.intro ac) (well_founded.intro ac') y ind := 
| r r' a b (well_founded.intro ac) (well_founded.intro ac') y ind := 


def acc_or_eq {κ : Type*} : Π (r r': κ → κ → Prop) (a : κ),
    well_founded (ind_or r r') → acc (λ a b, r a b ∨ r' a b) a
| r r' a (well_founded.intro ac) := 

def acc_or {κ : Type*} : Π (r r': κ → κ → Prop) (a : κ),
    well_founded r → well_founded r' → acc (λ a b, r a b ∨ r' a b) a
| r r' a wf1 wf2 :=
begin
    cases wf1, cases wf2,
    apply acc.rec_on (wf1 a), intros,
    apply acc.rec_on (wf2 x), intros,
    apply acc.intro, intros,
    have aux : a = a → x = x → acc (λ a b, r a b ∨ r' a b) y,
    cases a_1, 
end

def wf_or {κ : Type*} : Π (r r': κ → κ → Prop), 
    well_founded r → well_founded r' 
    → well_founded (λ a b, r a b ∨ r' a b) :=
begin
    intros,
    constructor,
    intros,
    cases a, cases a_1, apply acc_or r r',
    constructor, apply a, constructor, apply a_1,
end

def wf_lt_aux' : Π (a b : ℕ →₀ ℕ) (c : ℕ), 
    leading_term_lt_aux a b c
    → acc (λ x y, leading_term_lt_aux x y c) a :=
begin
    intros a b c, revert a b,
    induction c; intros,
    begin
        constructor,
        intros,
        unfold leading_term_lt_aux at *,
        apply inv_image.accessible, have w := nat.lt_wf,
        cases w, apply w,
    end,
    begin
        unfold leading_term_lt_aux,

    end,
end

def wf_lt_aux : Π (a b : mv_polynomial ℕ α), a < b 
     → acc (@mv_polynomial.lt α _ _ _) a
| a b p :=
begin
    unfold has_lt.lt mv_polynomial.lt at p,
    
end

protected def wf_lt : well_founded (@mv_polynomial.lt α _ _ _) :=
begin
    constructor, intro, 
end

instance : has_well_founded (mv_polynomial ℕ α) :=
⟨mv_polynomial.lt, mv_polynomial.wf_lt⟩



def leading_term_sub_aux (a b : ℕ →₀ ℕ) 
   : Π (k: ℕ), (leading_term_le_aux b a k) → (ℕ →₀ ℕ) 
| nat.zero le := finsupp.single 0 (a 0 - b 0)
| (nat.succ n) le := begin cases le, exact leading_term_sub_aux n le_right end

def leading_term_sub (a b : ℕ →₀ ℕ) : (leading_term_le b a) → (ℕ →₀ ℕ) 
| le := leading_term_sub_aux a b (finsupp.max_ab b a) le

def lcm (p q : mv_polynomial ℕ α) : mv_polynomial ℕ α := sorry

def not_le_le : Π (a b : mv_polynomial ℕ α), ¬ b ≤ a → a < b :=
begin
    intros,
    
end

def div : Π (a b : mv_polynomial ℕ α), Σ'q r, r < b ∧ a = b * q + r
| a b :=
begin
    by_cases (b ≤ a),
    let sub := leading_term_sub a.leading_term' b.leading_term' h,
    let q' := (finsupp.single sub (a.leading_coeff / b.leading_coeff)),
    generalize h : a - b * q' = r',
    have result := div r' b,
    cases result with r_q, cases result_snd with r_r,
    apply psigma.mk (q' + r_q),
    apply psigma.mk r_r,
    apply and.intro,
    exact result_snd_snd.left,
    have prf : a = b * q' + r',
    rw [←h],simp, 
    cases result_snd_snd,
    rw [prf, result_snd_snd_right],
    simp,
    rw left_distrib,
    apply psigma.mk (0 : mv_polynomial ℕ α),
    apply psigma.mk a,
    apply and.intro, apply not_le_le, assumption,
    simp,
end

def s_poly (p q : mv_polynomial ℕ α) : mv_polynomial ℕ α :=
begin
    let fst := div (lcm p q) p.leading_term,
    let snd := div (lcm p q) q.leading_term,
    exact fst.fst * p - snd.fst * q,
end

def buchberger {s : set (mv_polynomial ℕ α)} : set (mv_polynomial ℕ α) := sorry

end mv_polynomial
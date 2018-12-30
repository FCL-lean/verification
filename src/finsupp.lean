import data.finsupp
import util
import fintype
import fin
import bot_zero
import seq

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}

namespace finsupp

section general
variables [decidable_eq α] [decidable_eq β]

section has_zero
variables [has_zero β] 

section fintype_dom
variables [fina: fintype α]
section has_le
variables [has_le β]


def leading_term_le (a b: α →₀ β): Prop 
    := fina.elems.fold (∧) true (λ elem, a elem ≤ b elem)

end has_le
end fintype_dom

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

def single_inj1' : Π {a b: α} {c d: β}, (c ≠ 0) → a ≠ b → single a c ≠ single b d :=
λ a b c d hc hab h, by apply absurd (single_inj1 hc h) hab

def single_ext : Π {a b: α}{c d: β}, a = b → c = d → single a c = single b d :=
    λ a b c d p q, by simp [p, q]

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

lemma single_support : Π (a : α), (single a 1).support = {a} := by finish

lemma coe_f : Π (a : α →₀ β) (n : α), a n = a.to_fun n := λ a n, rfl

lemma eq_zero_lem : ∀ {f : α → β} {l}, ({support := ∅, to_fun := f, mem_support_to_fun := l} : α →₀ β) = 0 :=
begin
    intros,
    rw support_eq_empty.1 (rfl : ({support := ∅, to_fun := f, mem_support_to_fun := l} : α →₀ β).support = ∅),
end

lemma ne_zero_lem : ∀ {s : finset α} {f : α → β} {l}, s ≠ ∅ → ({support := s, to_fun := f, mem_support_to_fun := l} 
    : α →₀ β) ≠ 0 :=
begin
    intros s f l p1 p2,
    rw ←support_eq_empty at p2,
    simp at p2,
    exact absurd p2 p1,
end

lemma eq_zero_apply {a : α →₀ β} : (∀ x, a x = 0) ↔ a = 0 := ⟨λ h, by apply ext; assumption, λ h, by finish⟩

lemma ext_lem {a b : α →₀ β} : a = b ↔ ∀ x, a x = b x := ⟨λ h, by finish, λ h, by apply finsupp.ext; assumption⟩

section semilattice
variables [lattice.semilattice_sup_bot α]

lemma apply_eq_zero_of_gt_max {a : α →₀ β} {x : α} (h : x > a.support.sup id) : a x = 0 :=
begin
    rw ←finsupp.not_mem_support_iff, intro hx,
    apply absurd h (not_lt_of_le (finset.le_sup hx)),
end

end semilattice
end has_zero

section add_monoid
variables [add_monoid β]

def single_add_eqz [decidable_eq β] : Π {a b : α} {c d : β}, ¬ (c = 0 ∧ d = 0) → single a c + single b d = 0 → a = b :=
begin
    intros a b c d h₁ h₂,
    by_cases hc : c = 0; by_cases hd : d = 0,
    apply absurd (and.intro hc hd) h₁,
    any_goals {simp [single, hc, hd, eq_zero_lem] at h₂, try {apply absurd h₂ (ne_zero_lem (finset.singleton_ne_empty _))},}, 
    have h : ∀ x, (single a c + single b d) x = (0 : α →₀ β) x, simp [coe_f, single, h₂, hc, hd],
    simp [single_apply] at h,
    by_cases H : a = b, assumption,
    have h' := h a, simp [H, ne.symm H] at h',
    apply absurd h' hc,
end 

lemma add_left_cancel (a b c : α →₀ β) : a + b = a + c ↔ b = c := sorry

lemma add_right_cancel (a : α →₀ β) {b c : α →₀ β} : b + a = c + a ↔ b = c := sorry

end add_monoid

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

namespace fin_n
variable {n : ℕ}

lemma fin_0_id (a b : fin 0 →₀ ℕ) : a = b := begin apply ext, intro x, cases x.2, end 

lemma leading_term_le_all (a b: fin n →₀ ℕ): leading_term_le a b →
    ∀ (x : fin n), a x ≤ b x :=
λ hle, begin
    unfold leading_term_le at hle, 
    rw fintype.fintype_fold_and_iff at hle, 
    assumption
end

lemma leading_term_le_zero (a : fin n →₀ ℕ):
    leading_term_le 0 a :=
begin
    unfold leading_term_le,
    rw fintype.fintype_fold_and_iff; intros; apply zero_le,
end

lemma leading_term_le_refl: Π {n} {a : fin n →₀ ℕ},
    leading_term_le a a :=
begin
    intros, cases n;
    unfold leading_term_le,
    rw fintype.fintype_fold_and_iff, intros; refl,
end

lemma leading_term_le_antisymm {a b: fin n →₀ ℕ}:
    leading_term_le a b → leading_term_le b a → a = b :=
begin
    intros,
    apply finsupp.ext,
    intro val,
    apply le_antisymm; apply leading_term_le_all; assumption,
end

def leading_term_sub_aux : Π {n : ℕ} (a b: fin n →₀ ℕ),
     (∀ x, b x ≤ a x) → Π (m : ℕ), m < n → (fin n →₀ ℕ)
| 0 a b prf m prf2 := 0
| (nat.succ n) a b prf 0 prf2 := single 0 (a ⟨0, prf2⟩ - b ⟨0, prf2⟩)
| (nat.succ n) a b prf (nat.succ m) prf2 
    := single (nat.succ m) (a ⟨nat.succ m, prf2⟩ - b ⟨nat.succ m, prf2⟩) 
       + leading_term_sub_aux a b prf m (nat.lt_of_succ_lt prf2)

def leading_term_sub : Π {n} (a b: fin n →₀ ℕ), leading_term_le b a → (fin n →₀ ℕ)
| 0 a b ltle := 0
| (nat.succ n) a b ltle 
    := leading_term_sub_aux a b (leading_term_le_all b a ltle) n (by constructor)

lemma leading_term_sub_aux_zero : Π {n m: ℕ} p1 p2, 
    leading_term_sub_aux (0: fin n →₀ ℕ) 0 p1 m p2 = 0 :=
begin
    intros n m; revert n, induction m; intros; cases n; try {by cases p2};
    unfold leading_term_sub_aux; simp,
    apply m_ih,
end

lemma leading_term_sub_zero : Π {n} (h: leading_term_le (0: fin n →₀ ℕ) 0),
    leading_term_sub 0 0 h = 0 :=
begin
    intros, cases n; unfold leading_term_sub,
    apply leading_term_sub_aux_zero,
end

def le_aux : ∀ m < (n + 1), ((fin $ n + 1) →₀ ℕ) → ((fin $ n + 1) →₀ ℕ) → Prop
| 0 h := λ a b, a ⟨0, h⟩ ≤ b ⟨0, h⟩
| (m + 1) h := λ a b, a ⟨m + 1, h⟩ < b ⟨m + 1, h⟩ ∨ (a ⟨m + 1, h⟩ = b ⟨m + 1, h⟩ ∧ le_aux m (nat.lt_of_succ_lt h) a b)

protected def le: Π {n}, rel (fin n →₀ ℕ)
| 0 a b            := true
| (nat.succ n) a b := le_aux n (nat.lt_succ_self n) a b

lemma le_refl_aux (m : ℕ) (h : m < n + 1) : ∀ a : (fin $ n + 1) →₀ ℕ, le_aux m h a a :=
λ a, begin
    induction m;
    unfold le_aux, right,
    apply and.intro rfl (m_ih (nat.lt_of_succ_lt h)),
end

lemma le_refl : ∀ a : fin n →₀ ℕ, finsupp.fin_n.le a a := 
λ a, by cases n; simp [fin_n.le]; apply le_refl_aux

lemma le_trans_aux (m : ℕ) (h : m < n + 1) : ∀ a b c : (fin $ n + 1) →₀ ℕ, le_aux m h a b → le_aux m h b c → le_aux m h a c :=
λ a b c, begin
    induction m; unfold le_aux, apply le_trans,
    intros hab hbc, cases hab; cases hbc,
    left, exact lt_trans hab hbc,
    left, exact lt_of_lt_of_le hab (le_of_eq hbc.left),
    left, exact lt_of_le_of_lt (le_of_eq hab.left) hbc,
    right, apply and.intro (eq.trans hab.left hbc.left) (m_ih (nat.lt_of_succ_lt h) hab.right hbc.right),
end

lemma le_trans : ∀ a b c : fin n →₀ ℕ, 
    finsupp.fin_n.le a b → finsupp.fin_n.le b c → finsupp.fin_n.le a c := 
λ a b c, by cases n; simp [fin_n.le]; apply le_trans_aux

instance : preorder (fin n →₀ ℕ) :=
{
    le := finsupp.fin_n.le,
    le_refl := le_refl,
    le_trans := le_trans,
}

lemma le_antisymm_aux (m₁ m₂ : ℕ) (h : m₁ + m₂ < n + 1) : ∀ a b : (fin $ n + 1) →₀ ℕ, 
    le_aux (m₁ + m₂) h a b → le_aux (m₁ + m₂) h b a → a.to_fun ⟨m₁, nat.left_lt_of_add_lt h⟩ = b.to_fun ⟨m₁, nat.left_lt_of_add_lt h⟩ :=
λ a b, begin
    induction m₂, induction m₁, all_goals {simp [le_aux, nat.add_succ]}, 
    apply le_antisymm,
    all_goals {intros hab hba, cases hab; cases hba},
    any_goals { 
        try {apply absurd hab (not_lt_of_le (le_of_lt hba))},
        try {apply absurd hab (not_lt_of_le (le_of_eq hba.left))},
        try {apply absurd hba (not_lt_of_le (le_of_eq hab.left))},
    },
    exact hab.left,
    rw [nat.add_succ] at h,
    exact m₂_ih (nat.lt_of_succ_lt h) hab.right hba.right,
end

set_option trace.check true
lemma le_antisymm : ∀ a b : fin n →₀ ℕ, a ≤ b → b ≤ a → a = b := 
λ a b, begin
    cases n;
    intros hab hba, 
    apply fin_0_id,
    apply ext, intro x, 
    have h_add_sub : x.val + (n - x.val) = n, rw [←nat.add_sub_assoc (nat.le_of_lt_succ x.is_lt)], simp,
    have h := le_antisymm_aux x.val (n - x.val) (lt_of_le_of_lt (le_of_eq h_add_sub) (nat.lt_succ_self n)) a b, 
    simp [h_add_sub] at h,
    apply h hab hba,
end

lemma le_total_aux (m : ℕ) (h : m < n + 1) : ∀ a b : (fin $ n + 1) →₀ ℕ, le_aux m h a b ∨ le_aux m h b a :=
λ a b, begin
    induction m; unfold le_aux, apply le_total,
    cases lt_trichotomy (a.to_fun ⟨m_n + 1, h⟩) (b.to_fun ⟨m_n + 1, h⟩),
    apply or.inl (or.inl h_1),
    cases h_1, cases m_ih (nat.lt_of_succ_lt h),
        apply or.inl (or.inr (and.intro h_1 h_2)),
        apply or.inr (or.inr (and.intro h_1.symm h_2)),
    apply or.inr (or.inl h_1),
end

lemma le_total : ∀ a b : fin n →₀ ℕ, a ≤ b ∨ b ≤ a :=
λ a b, by cases n; simp [has_le.le, preorder.le, fin_n.le]; apply le_total_aux n

instance decidable_le_aux (m : ℕ) (h : m < n + 1) : decidable_rel (le_aux m h) :=
λ a b, begin
    induction m;
    unfold le_aux, apply_instance,
    from if h₀ : (a.to_fun ⟨m_n + 1, h⟩) < (b.to_fun ⟨m_n + 1, h⟩)
    then is_true (or.inl h₀)
    else if h₁ : (a.to_fun ⟨m_n + 1, h⟩) > (b.to_fun ⟨m_n + 1, h⟩)
    then is_false (λ h₁', begin 
        cases h₁', apply nat.lt_lt_antisym h₁ h₁',
        apply absurd h₁ (not_lt_of_le (le_of_eq h₁'.left)),
    end)
    else begin
        cases m_ih (nat.lt_of_succ_lt h),
        left, intro h_1', cases h_1', apply absurd h_1' h₀, apply absurd h_1'.right h_1,
        right, apply or.inr (and.intro (nat.not_le_not_ge_eq h₀ h₁) h_1),
    end
end

instance : decidable_rel ((≤) : rel (fin n →₀ ℕ)) := λ a b,
by cases n; unfold has_le.le preorder.le finsupp.fin_n.le; apply_instance

lemma le_mono_order_aux (m : ℕ) (h : m < n + 1) : ∀ a b w : (fin $ n + 1) →₀ ℕ, le_aux m h a b →  le_aux m h (a + w) (b + w) :=
λ a b w, begin
    induction m;
    unfold le_aux, simp,
    intro hab, simp, 
    cases hab, exact or.inl hab,
    exact or.inr (and.intro hab.left (m_ih (nat.lt_of_succ_lt h) hab.right)),
end

lemma le_mono_order : ∀ (a b w : fin n →₀ ℕ), (a ≤ b) → ((a + w) ≤ (b + w)) := 
λ a b w, by cases n; simp[has_le.le, preorder.le, fin_n.le]; apply le_mono_order_aux

instance : decidable_monomial_order (fin n →₀ ℕ) := {
    le := preorder.le,
    le_refl := preorder.le_refl,
    le_trans := preorder.le_trans,
    le_antisymm := le_antisymm,
    le_total := le_total,
    decidable_le := finsupp.fin_n.decidable_rel,
    add := finsupp.has_add.add,
    mono_order := le_mono_order,
}

lemma zero_le_aux : ∀ (m < n + 1) (a : fin (n + 1) →₀ ℕ), le_aux m H 0 a
| 0 H a := by simp [le_aux]
|(m + 1) H a := by simp [le_aux]; 
                from if h : 0 < a ⟨m + 1, H⟩ 
                    then by simp [h]
                    else begin exact or.inr (and.intro (nat.eq_zero_of_le_zero (le_of_not_lt h)).symm
                                (zero_le_aux m (nat.lt_of_succ_lt H) a)) end

lemma zero_le : ∀ a : fin n →₀ ℕ, 0 ≤ a :=
λ a, by cases n; simp [has_le.le, preorder.le, fin_n.le, zero_le_aux]

instance : lattice.semilattice_sup_bot (fin n →₀ ℕ) := {
    bot := 0,
    le := preorder.le,
    le_refl := preorder.le_refl,
    le_trans := preorder.le_trans,
    le_antisymm := le_antisymm,
    bot_le := zero_le,
    sup := max,
    le_sup_left := le_max_left,
    le_sup_right := le_max_right,
    sup_le := λ a b c, max_le
}

lemma lt_zero_aux {a : fin (n + 1) →₀ ℕ} : 
    ∀ m < n + 1, le_aux m H a 0 ∧ ¬le_aux m H 0 a → false
| 0 H := λ h, by simp [le_aux] at h; assumption
|(m + 1) H := λ h, begin 
    simp [le_aux] at h, cases h, simp [not_or_distrib] at h_right,
    cases h_left, cases h_left,
    apply lt_zero_aux m (nat.lt_of_succ_lt H) (and.intro h_left.right (h_right.right h_right.left.symm)),
end

lemma eq_le_aux'' : 
    Π (a b : fin (n + 1) →₀ ℕ) t
    p1 p2 p3
    (H1: a.to_fun ⟨t, p1⟩ = b.to_fun ⟨t, p1⟩),
    Π (H2: le_aux t p2 a b), 
    a.to_fun ⟨t - 1, p3⟩ ≤ b.to_fun ⟨t - 1, p3⟩ :=
begin
    intros,
    cases t,
    begin
        revert p3, rw nat.zero_sub,
        intros, assumption,
    end,
    begin
        simp,
        cases H2,
        begin
            have H: a ⟨t + 1, p1⟩ = b ⟨t + 1, p1⟩,
                assumption,
            rw H at H2, apply false.elim, apply nat.lt_irrefl, assumption,
        end,
        begin
            cases H2,
            cases t,
            by assumption,
            begin
                cases H2_right,
                by apply le_of_lt; assumption,
                by apply le_of_eq; exact H2_right.1,
            end,
        end,
    end,
end

lemma le_aux_descend : 
    Π (a b : fin (n + 1) →₀ ℕ) t (p1: ∀ k', t - k' < n + 1) p2 q p3
    (H1: le_aux t p2 a b)
    (H2: ∀ (k' : ℕ), k' < nat.succ q
        → a.to_fun ⟨t - k', p1 k'⟩ = b.to_fun ⟨t - k', p1 k'⟩),
    le_aux (nat.sub t q) p3 a b :=
begin
    intros, 
    induction q,
    by assumption,
    begin
        have IH := q_ih (p1 _) (λ h1 h2, by apply H2; constructor; assumption),
        generalize H : nat.sub t q_n = w,
        have p1q_n := p1 q_n,
        have IH' : ∀ y, le_aux (nat.sub t q_n) y a b := λ _, IH,
        rw H at IH', cases w; unfold nat.sub;
        change le_aux (nat.pred (nat.sub t q_n)) p3 a b;
        revert p3;
        change ∀ (p3 : nat.pred (nat.sub t q_n) < n + 1), le_aux (nat.pred (nat.sub t q_n)) p3 a b,
        all_goals { rw H; intro },
        by exact IH' p3,
        begin
            simp,
            have IH'' := IH' (H ▸ p1q_n),
            cases IH'',
            begin
                have IHEQ := H2 q_n (by constructor; constructor),
                apply false.elim,
                have EQ' : ∀ y, a ⟨t - q_n, y⟩ = b ⟨t - q_n, y⟩ := λ _, IHEQ,
                have H' : t - q_n = w + 1 := H,
                rw H' at EQ',
                rw EQ' (H' ▸ p1q_n) at IH'',
                exact lt_irrefl _ IH'',
            end,
            by exact IH''.2,
        end,
    end,
end

lemma eq_le_aux' :
    Π (a b : fin (n + 1) →₀ ℕ) t k
    (p1 : ∀ k, t - k < n + 1) p2 p3
    (H1:  ∀ (k' : ℕ), k' < k → a.to_fun ⟨t - k', p1 k'⟩ = b.to_fun ⟨t - k', p1 k'⟩),
    Π (H2: le_aux t p2 a b), 
    a.to_fun ⟨t - k, p3⟩ ≤ b.to_fun ⟨t - k, p3⟩ :=
begin
    intros; induction k,
    begin
        cases t; unfold le_aux at H2,
        by assumption,
        begin
            cases H2,
            by apply le_of_lt; assumption,
            by apply le_of_eq; exact H2.1,
        end
    end,
    begin
        by_cases HLT : t - k_n < n + 1,
        begin
            have IH := k_ih HLT,
            apply eq_le_aux''; try { assumption }; try { apply H1 },
            by constructor,
            by apply le_aux_descend; assumption, 
        end,
        begin
            rw not_lt at HLT,
            by_cases H: nat.succ k_n ≤ t,
            begin
            /-
                ¬t - k_n < n + 1
                t - k_n ≥ n + 1
                n + 1 ≤ t - k_n
                t - nat.succ k_n < n + 1 ≤ t - k_n
                -> n + 1 = t - k_n
                -> t - (k_n + 1) = n 
                -> p1 k_n : t - k_n = n + 1 < n + 1 =><=
            -/
                have p4 : (t - nat.succ k_n) + 1 ≤ n + 1 := p3,
                have eq' : t - nat.succ k_n + 1 = t - k_n,
                    from nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt H),
                rw eq' at p4,
                have H' := nat.le_antisymm p4 HLT,
                have wrong := p1 k_n,
                rw H' at wrong,
                apply false.elim, apply nat.lt_irrefl, assumption,
            end,
            begin
                rw not_lt at H,
                have eqz := nat.sub_eq_zero_of_le H,
                rw eqz at HLT, cases HLT,
            end
        end,
    end,
end


lemma eq_le : Π m (a b : fin (n + 1) →₀ ℕ) (p1 : ∀ k, n - k < n + 1) p2
    (H1: ∀ k : ℕ, k < nat.succ m → a.to_fun ⟨n - k, p1 k⟩ = b.to_fun ⟨n - k, p1 k⟩)
    (H2: a ≤ b),
    a.to_fun ⟨n - nat.succ m, p2⟩ ≤ b.to_fun ⟨n - nat.succ m, p2⟩ :=
begin
    intros,
    unfold has_le.le preorder.le fin_n.le at H2,
    apply eq_le_aux'; assumption,
end


lemma seq_R_elem_le_aux : Π (n : ℕ) (s : seqR.seq_R (fin (n + 1) →₀ ℕ) (<))
    (i : ℕ) (p : i < n + 1) (j : ℕ) (p1 : ∀ k, n - k < n + 1) p2,
        (∀ (k : ℕ) (p: k < i), ((s.1 (j + 1)).to_fun ⟨n - k, p1 k⟩)
            = ((s.1 j).to_fun ⟨n - k, p1 k⟩))
        → (s.1 (j + 1)).to_fun ⟨n - i, p2⟩ ≤ (s.1 j).to_fun ⟨n - i, p2⟩ :=
begin
    intros,
    revert j; induction i; intros;
    have h := s.2 j,
    begin
        cases h,
        unfold fin_n.le at h_left,
        cases n; unfold le_aux at h_left,
        by assumption,
        begin
            cases h_left,
            begin
                apply le_of_lt,
                assumption,
            end,
            begin
                simp,
                apply le_of_eq,
                exact h_left.1,
            end,
        end,
    end,
    begin
        cases h,
        apply eq_le; assumption,
    end,
end

lemma seq_R_elem_le :  Π (n : ℕ) (s : seqR.seq_R (fin (n + 1) →₀ ℕ) (<))
    (i : ℕ) (p : i < n + 1) (p1: ∀ k, n - k < n + 1) (j k : ℕ), j ≤ k →
        (∀ (k' : ℕ) (p: k' < n - i) (t : ℕ), t ≥ j → t < k → 
            ((s.1 (t + 1)).to_fun ⟨n - k', p1 k'⟩)
                = ((s.1 t).to_fun ⟨n - k', p1 k'⟩))
        → (s.1 k).to_fun ⟨i, p⟩ ≤ (s.1 j).to_fun ⟨i, p⟩ :=
begin
    intros,
    by_cases j = k,
    begin
        cases h, refl,
    end,
    begin
        have jklt: j < k := lt_of_le_of_ne a h,
        revert a_1,
        rw ←nat.add_sub_cancel' jklt,
        apply @nat.strong_induction_on 
                (λ x, (∀ (k' : ℕ),
                        k' < n - i → ∀ (t : ℕ), t ≥ j →
                        t < nat.succ j + x →
                        (s.val (t + 1)).to_fun ⟨n - k', p1 k'⟩ 
                        = (s.val t).to_fun ⟨n - k', p1 k'⟩) →
                    (s.val (nat.succ j + x)).to_fun ⟨i, p⟩ 
                        ≤ (s.val j).to_fun ⟨i, p⟩)
                (k - nat.succ j),
        intros,
        cases n_1,
        begin
            have p' := p,
            revert p,
            rw ←nat.sub_sub_self (nat.le_of_succ_le_succ p'),
            intros,
            apply seq_R_elem_le_aux _ _ (n - i) (p1 i) j p1 (p1 (n - i)),
            begin
                intros,
                apply a_2; try {trivial}; try {assumption}; try {constructor},
            end,
        end,
        begin
            have ih:= a_1 n_1 (by constructor) 
                (λ k' p t p' p'', begin apply a_2; try {assumption}, 
                                        constructor; assumption, end),
            transitivity,
            swap,
            by exact ih,
            begin
                have p' := p,
                revert p,
                rw ←nat.sub_sub_self (nat.le_of_succ_le_succ p'),
                intros,
                apply seq_R_elem_le_aux _ _ _ (p1 i) _ p1,
                begin
                    intros,
                    apply a_2,
                    by assumption,
                    begin
                        change (nat.succ j) + n_1 ≥ j,
                        rw add_comm,
                        constructor,
                        have H' := add_le_add' (nat.zero_le n_1) (by refl : j ≤ j),
                        rw zero_add at H',
                        assumption,
                    end,
                    by constructor,
                end,
            end,
        end,
    end,
end

lemma no_t_inf_indx' : Π (n : ℕ) (s: seqR.seq_R (fin (n + 1) →₀ ℕ) (<)) (i : ℕ) (p0: i < n + 1) (t : ℕ)
    (p1: ∀ k, n - k < n + 1),
    (∀ (t' : ℕ), t' ≥ t →
        ∀ (k : ℕ), k ≤ i → 
      (s.val t').to_fun ⟨n - k, p1 k⟩ = (s.val t).to_fun ⟨n - k, p1 k⟩) →
    (¬∃ (t : ℕ), ∀ (t' : ℕ), t' ≥ t →
            (s.val t').to_fun ⟨n - (i + 1), p1 (i + 1)⟩ = (s.val t).to_fun ⟨n - (i + 1), p1 (i + 1)⟩)
    → ∃ (l : ℕ → ℕ), (∀ n, l n < l (n + 1)) ∧
            ∀ m, (s.1 (l m)).to_fun ⟨n - (i + 1), p1 (i + 1)⟩ 
                > (s.1 (l (m + 1))).to_fun ⟨n - (i + 1), p1 (i + 1)⟩ :=
begin
    intros,
    rw [not_exists] at a_1,
    have ex: ∀ t : ℕ, ∃ (t' : ℕ), t' ≥ t ∧ (s.val t').to_fun ⟨n - (i + 1), p1 (i + 1)⟩ 
                                        ≠ (s.val t).to_fun ⟨n - (i + 1), p1 (i + 1)⟩,
        begin
            intro t,
            apply classical.by_contradiction,
            intros, apply a_1 t, intros,
            apply classical.by_contradiction,
            intro, apply a_2,
            apply exists.intro t',
            apply and.intro; assumption,
        end,
    have sty : ∀ (x : ℕ), { t' : ℕ  // t' ≥ x ∧ (s.val t').to_fun ⟨n - (i + 1), p1 (i + 1)⟩ ≠ (s.val x).to_fun ⟨n - (i + 1), p1 (i + 1)⟩},
        from λ x, classical.indefinite_description (λ m, m ≥ x ∧ (s.val m).to_fun ⟨n - (i + 1), p1 (i + 1)⟩ ≠ (s.val x).to_fun ⟨n - (i + 1), p1 (i + 1)⟩) (ex x),
    let styf : ℕ → ℕ := λ x, (sty x).val,
    let f : ℕ → ℕ := λ x, nat.rec_on x (styf t) (λ n m, styf m),
    apply exists.intro f,
    have : ∀ x, x < styf x,
        from λ x, begin 
            have neqle := (sty x).2, 
            apply lt_of_le_of_ne,
            from neqle.1,
            begin
                intro,
                apply neqle.2,
                change (s.val (styf x)).to_fun ⟨n - (i + 1), _⟩ = (s.val x).to_fun ⟨n - (i + 1), _⟩,
                rw ←a_2,
            end,
        end,
    have this': ∀ x, t < f x,
        from λ x, begin
            induction x,
            by apply this,
            begin
                transitivity,
                exact x_ih,
                apply this,
            end,
        end,
    apply and.intro,
    by intro; apply this,
    begin
        intros,
        apply lt_of_le_of_ne,
        begin
            apply seq_R_elem_le,
            begin
                apply le_of_lt, apply this,
            end,
            begin
                intros,
                transitivity,
                begin
                    apply a,
                    transitivity,
                    by apply nat.le_succ,
                    begin
                        transitivity,
                        by exact a_2,
                        by apply le_of_lt; apply this',
                    end,
                    begin
                        by_cases i = n,
                        begin
                            rw h at *,
                            rw [nat.sub_eq_zero_iff_le.2 (nat.le_succ n), nat.sub_zero] at p,
                            apply le_of_lt, assumption,
                        end,
                        have i_lt_n : i < n := nat.lt_of_le_and_ne (nat.le_of_succ_le_succ p0) h,
                        rw nat.sub_sub_self i_lt_n at p,
                        exact nat.le_of_succ_le_succ p,
                    end,
                end,
                begin
                    symmetry,
                    apply a,
                    begin
                        transitivity,
                        by exact a_2,
                        by apply le_of_lt; apply this',
                    end,
                    begin
                        by_cases i = n,
                        begin
                            rw h at *,
                            rw [nat.sub_eq_zero_iff_le.2 (nat.le_succ n), nat.sub_zero] at p,
                            apply le_of_lt, assumption,
                        end,
                        have i_lt_n : i < n := nat.lt_of_le_and_ne (nat.le_of_succ_le_succ p0) h,
                        rw nat.sub_sub_self i_lt_n at p,
                        exact nat.le_of_succ_le_succ p,
                    end,
                end,           
            end,
        end,
        from (sty (f m)).2.2,
    end
end

lemma no_t_inf_indx : Π (n : ℕ) (s: seqR.seq_R (fin (n + 1) →₀ ℕ) (<)),
    (¬ ∃ (t : ℕ), ∀ t' (p1: t' ≥ t), (s.1 t').to_fun ⟨n, by constructor⟩ 
                                = (s.1 t).to_fun ⟨n, by constructor⟩)
        → ∃ (l : ℕ → ℕ), (∀ n, l n < l (n + 1)) ∧
            ∀ m, (s.1 (l m)).to_fun ⟨n, by constructor⟩ 
                > (s.1 (l (m + 1))).to_fun ⟨n, by constructor⟩ :=
begin
    intros,
    rw [not_exists] at a,
    have ex : ∀ (x : ℕ), ∃ (t' : ℕ), t' ≥ x 
        ∧ (s.val t').to_fun ⟨n, by constructor⟩ ≠ (s.val x).to_fun ⟨n, by constructor⟩,
        begin
            intro x,
            apply classical.by_contradiction,
            intros, apply a x,
            intros,
            apply classical.by_contradiction,
            intro, apply a_1,
            apply exists.intro t',
            intros, apply and.intro; assumption,
        end,
    have sty : ∀ (x : ℕ), { t' : ℕ  // t' ≥ x ∧ (s.val t').to_fun ⟨n, by constructor⟩ ≠ (s.val x).to_fun ⟨n, by constructor⟩},
        from λ x, classical.indefinite_description (λ m, m ≥ x ∧ (s.val m).to_fun ⟨n, by constructor⟩ ≠ (s.val x).to_fun ⟨n, by constructor⟩) (ex x),
    let styf : ℕ → ℕ := λ x, (sty x).val,
    let f : ℕ → ℕ := λ x, nat.rec_on x (styf 0) (λ n m, styf m),
    apply exists.intro f,
    have : ∀ x, x < styf x,
        from λ x, begin 
            have neqle := (sty x).2, 
            apply lt_of_le_of_ne,
            from neqle.1,
            begin
                intro,
                apply neqle.2,
                change (s.val (styf x)).to_fun ⟨n, _⟩ = (s.val x).to_fun ⟨n, _⟩,
                rw ←a_1,
            end,
        end,
    apply and.intro,
    from λ x, by apply this,
    begin
        intro m,
        have seq_gt := seqR.gt_trans_of_lt s (this (f m)),
        cases seq_gt,
        apply lt_of_le_of_ne,
        begin
            cases n, 
            by assumption,
            begin
                cases seq_gt_left,
                begin
                    apply le_of_lt, assumption,
                end,
                begin
                    apply le_of_eq, exact seq_gt_left.1,
                end,
            end,
        end,
        from (sty (f m)).2.2,
    end,
end

lemma no_inf_indx' : Π (n : ℕ) (s: seqR.seq_R (fin (n + 1) →₀ ℕ) (<)),
    ∀ (l : ℕ → ℕ) (H1: ∀ n, l n < l (n + 1)) (k : ℕ) (p: k < n + 1)
      (H2: (∀ m n', m < n' → (s.1 (l m)).to_fun ⟨k, p⟩ 
                > (s.1 (l n')).to_fun ⟨k, p⟩)),
    false :=
begin
    intros,
    apply order_embedding.well_founded_iff_no_descending_seq.1 nat.lt_wf,
    constructor,
    constructor, swap,
    constructor, swap,
    exact λ m, (s.1 (l m)).to_fun ⟨k, p⟩,
    begin
        intros a b p,
        apply classical.by_contradiction,
        intro neq,
        have lt_or_gt := lt_or_gt_of_ne neq,
        cases lt_or_gt;
        have := H2 _ _ lt_or_gt;
        rw p at *; exact lt_irrefl _ this,
    end,
    begin
        intros; apply iff.intro; intros; simp at *,
        begin
            apply H2; assumption,
        end,
        begin
            by_cases a = b,
            by rw h at a_1; apply false.elim; exact lt_irrefl ((s.val (l b)).to_fun ⟨k, p⟩) a_1,
            cases lt_or_gt_of_ne h,
            begin
                apply false.elim,
                exact nat.lt_lt_antisym a_1 (H2 _ _ h_1),
            end,
            by assumption,
        end,
    end,
end


lemma seqR_eq' : Π (n : ℕ) (s: seqR.seq_R (fin (n + 1) →₀ ℕ) (<)) (i: ℕ) (ip: i < n + 1)
    (p3: ∀ k, n - k < n + 1),
    ∃ (t : ℕ), ∀ t' (p1: t' ≥ t),
        (s.1 t').to_fun ⟨n - i, p3 i⟩ 
    = (s.1 t).to_fun ⟨n - i, p3 i⟩ :=
begin
    intros n s i p p3, revert p,
    apply nat.strong_induction_on i,
    intro n_i,
    cases n_i; intros,
    begin
        apply classical.by_contradiction,
        intro,
        have H := no_t_inf_indx n s _,
            swap, intro, apply a_1,
            sorry,
        cases H with idx idxp, cases idxp,
        apply no_inf_indx' n s idx idxp_left n,
        apply nat.many_step, assumption,
        constructor; intros; transitivity; assumption,
    end,
    begin
        apply classical.by_contradiction,
        intro,
        have H := no_t_inf_indx' n s n_i _ _ p3 _ a_1,
        cases H with idx idxp, cases idxp,
        apply no_inf_indx' n s idx idxp_left (n - (n_i + 1)),
        apply nat.many_step, assumption,
        constructor, intros; transitivity; assumption,
        sorry, sorry, sorry
    end,
end

lemma seqR_eq : Π (n : ℕ) (s: seqR.seq_R (fin (n + 1) →₀ ℕ) (<)),
    ∃ (t : ℕ), ∀ t' ≥ t, s.1 t = s.1 t' :=
begin
    intros,
    have : ∀ k, n - k < n + 1 := sorry,
    have lem := λ o u, seqR_eq' n s o u this,
    cases lem,
    apply exists.intro lem_w,
    intros, apply finsupp.ext, intro a,
    have H' := nat.le_add (nat.le_of_succ_le_succ a.2),
    cases H',
    have lem' := lem_h t' H,
    symmetry, rw [←fin.eta a a.2], 
    have H'' : a.val = n - H'_fst, sorry,
    have a2 := a.2,
    change (s.val t') ⟨a.val, a2⟩ = (s.val lem_w) ⟨a.val, a2⟩,
    revert a2,
    rw H'', intros,
    apply lem',
end

lemma seqR_false : Π (n : ℕ), ¬' seqR.seq_R (fin (n + 1) →₀ ℕ) (<) :=
λ n seq,
begin
    have eq := seqR_eq n seq,
    cases eq,
    have eq_w'_eq := eq_h (eq_w + 1) (by unfold ge; constructor; constructor),
    have related := seq.2 eq_w,
    rw eq_w'_eq at related,
    apply lt_irrefl _ related,
end

lemma lt_wf : well_founded ((<) : rel (fin n →₀ ℕ)) :=
begin
    cases n,
    begin
        constructor, intro a,
        constructor, intros,
        rw fin_0_id y a at a_1,
        apply false.elim (lt_irrefl _ a_1),
    end,
    begin
        apply seqR.no_inf_chain_wf,
        apply seqR_false,
    end
end

end fin_n

end finsupp
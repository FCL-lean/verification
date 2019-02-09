import data.list
import data.finsupp
import data.fin

import util
universes u v w

@[reducible]
def monomial : ℕ → Type := λ n, fin n →₀ ℕ

structure poly_term (α : Type u) (n : ℕ) [discrete_field α] :=
mk :: (coeff : α) (mon : monomial n) (coeff_neqz : coeff ≠ 0) (mon_neqz : mon.support ≠ ∅)


variable {n : ℕ}



lemma fin_0_id (a b : fin 0 →₀ ℕ) : a = b := begin apply finsupp.ext, intro x, cases x.2, end 

def le_aux : ∀ m < (n + 1), ((fin $ n + 1) →₀ ℕ) → ((fin $ n + 1) →₀ ℕ) → Prop
| 0 h := λ a b, a ⟨0, h⟩ ≤ b ⟨0, h⟩
| (m + 1) h := λ a b, a ⟨m + 1, h⟩ < b ⟨m + 1, h⟩ ∨ (a ⟨m + 1, h⟩ = b ⟨m + 1, h⟩ ∧ le_aux m (nat.lt_of_succ_lt h) a b)

def mon_le: Π {n}, rel (fin n →₀ ℕ)
| 0 a b            := true
| (nat.succ n) a b := le_aux n (nat.lt_succ_self n) a b

lemma le_refl_aux (m : ℕ) (h : m < n + 1) : ∀ a : (fin $ n + 1) →₀ ℕ, le_aux m h a a :=
λ a, begin
    induction m;
    unfold le_aux, right,
    apply and.intro rfl (m_ih (nat.lt_of_succ_lt h)),
end

lemma mon_le_refl : ∀ a : fin n →₀ ℕ, mon_le a a := 
λ a, by cases n; simp [mon_le]; apply le_refl_aux

lemma le_trans_aux (m : ℕ) (h : m < n + 1) : ∀ a b c : (fin $ n + 1) →₀ ℕ, le_aux m h a b → le_aux m h b c → le_aux m h a c :=
λ a b c, begin
    induction m; unfold le_aux, apply le_trans,
    intros hab hbc, cases hab; cases hbc,
    left, exact lt_trans hab hbc,
    left, exact lt_of_lt_of_le hab (le_of_eq hbc.left),
    left, exact lt_of_le_of_lt (le_of_eq hab.left) hbc,
    right, apply and.intro (eq.trans hab.left hbc.left) (m_ih (nat.lt_of_succ_lt h) hab.right hbc.right),
end

lemma mon_le_trans : ∀ a b c : fin n →₀ ℕ, 
    mon_le a b → mon_le b c → mon_le a c := 
λ a b c, by cases n; simp [mon_le]; apply le_trans_aux

instance : preorder (fin n →₀ ℕ) :=
{
    le := mon_le,
    le_refl := mon_le_refl,
    le_trans := mon_le_trans,
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

lemma mon_le_antisymm : ∀ a b : fin n →₀ ℕ, a ≤ b → b ≤ a → a = b := 
λ a b, begin
    cases n;
    intros hab hba, 
    apply fin_0_id,
    apply finsupp.ext, intro x, 
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

lemma mon_le_total : ∀ a b : fin n →₀ ℕ, a ≤ b ∨ b ≤ a :=
λ a b, by cases n; simp [has_le.le, preorder.le, mon_le]; apply le_total_aux n

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

instance mon_le_decidable_rel : decidable_rel ((≤) : rel (fin n →₀ ℕ)) := λ a b,
by cases n; unfold has_le.le preorder.le mon_le; apply_instance

lemma le_mono_order_aux (m : ℕ) (h : m < n + 1) : ∀ a b w : (fin $ n + 1) →₀ ℕ, le_aux m h a b →  le_aux m h (a + w) (b + w) :=
λ a b w, begin
    induction m;
    unfold le_aux, simp,
    intro hab, simp, 
    cases hab, exact or.inl hab,
    exact or.inr (and.intro hab.left (m_ih (nat.lt_of_succ_lt h) hab.right)),
end

lemma le_mono_order : ∀ (a b w : fin n →₀ ℕ), (a ≤ b) → ((a + w) ≤ (b + w)) := 
λ a b w, by cases n; simp [has_le.le, preorder.le, mon_le]; apply le_mono_order_aux

instance : decidable_monomial_order (fin n →₀ ℕ) := {
    le := preorder.le,
    le_refl := preorder.le_refl,
    le_trans := preorder.le_trans,
    le_antisymm := mon_le_antisymm,
    le_total := mon_le_total,
    decidable_le := mon_le_decidable_rel,
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

lemma mon_zero_le : ∀ a : fin n →₀ ℕ, 0 ≤ a :=
λ a, by cases n; simp [has_le.le, preorder.le, mon_le, zero_le_aux]

-- def lifted_lt : option (poly_term α n) → 

inductive polynomial (α : Type u) (n : ℕ) [discrete_field α] : option (poly_term α n) → Type u
| nil : polynomial none
| sing : Π (p : poly_term α n), polynomial (some p)
| cons : Π (p p': poly_term α n), p'.mon < p.mon → polynomial (some p') → polynomial (some p)

inductive polynomial' (α : Type u) (n : ℕ) [discrete_field α] : Type u
| mk : Π (p : option (poly_term α n)) (poly : polynomial α n p), polynomial'

instance (α : Type u) (n : ℕ) [discrete_field α] : decidable_eq (polynomial' α n) :=
begin
    intros a b,
    cases a; cases b,
    induction a_poly; induction b_poly;
    try { by right; simp }; try { by left; simp },
    
end
@[elab_as_eliminator]
def option_rec {α : Type u} : Π {C : option α → Sort w} (o : option α) (b₁ : o = none → C none) (b₂ : ∀ m, o = some m → C (some m)), C o :=
begin
    intros,
    induction o,
    { exact b₁ rfl, },
    { exact b₂ _ rfl, }
end

def poly_add_insert {α : Type u} {n : ℕ} [discrete_field α] : poly_term α n → polynomial' α n → polynomial' α n
| t (polynomial'.mk none (polynomial.nil α n)) := polynomial'.mk (some t) (polynomial.sing t)
| t (polynomial'.mk (some p) pp@(polynomial.sing .(p))) := if h : p.mon < t.mon 
                                                           then polynomial'.mk _ (polynomial.cons t p h pp)
                                                           else if h' : p.mon = t.mon
                                                                then if coeff_neqz : p.coeff + t.coeff = 0
                                                                     then polynomial'.mk _ (polynomial.nil α n)
                                                                     else polynomial'.mk _ (polynomial.sing (poly_term.mk (p.coeff + t.coeff) p.mon coeff_neqz p.mon_neqz))
                                                                else polynomial'.mk _ (polynomial.cons p t (or.rec_on (eq_or_lt_of_not_lt h) (λ k, false.elim (h' k)) id) 
                                                                                                        (polynomial.sing t))
| t (polynomial'.mk (some p) pp@(polynomial.cons .(p) p₂ prf tl)) := if h : p.mon < t.mon
                                                                     then polynomial'.mk _ (polynomial.cons t p h pp)
                                                                     else if h' : p.mon = t.mon
                                                                          then if coeff_neqz : p.coeff + t.coeff = 0
                                                                               then polynomial'.mk _ tl
                                                                               else polynomial'.mk _ (polynomial.cons (poly_term.mk (p.coeff + t.coeff) p.mon coeff_neqz p.mon_neqz)
                                                                                                          p₂ prf tl)
                                                                           else let (polynomial'.mk m pp₂) := poly_add_insert t (polynomial'.mk _ tl)
                                                                                in option_rec m (λ _, polynomial'.mk none (polynomial.nil α n)) 
                                                                                        (λ t' t'_prf, if head_lt : t'.mon < t.mon 
                                                                                                      then polynomial'.mk (some t) (polynomial.cons t t' head_lt (by rw t'_prf at pp₂; exact pp₂)) 
                                                                                                      else polynomial'.mk none (polynomial.nil α n))
def poly_add {α : Type u} {n : ℕ} [discrete_field α] : polynomial' α n → polynomial' α n → polynomial' α n
| (polynomial'.mk none (polynomial.nil α n)) p := p
| p (polynomial'.mk none (polynomial.nil α n)) := p
| (polynomial'.mk (some p) (polynomial.sing .(p))) p₂ := poly_add_insert p p₂
| p (polynomial'.mk (some p₂) (polynomial.sing .(p₂))) := poly_add_insert p₂ p
| (polynomial'.mk (some p) (polynomial.cons .(p) p₂ prf tl)) pp := poly_add (polynomial'.mk (some p₂) tl) (poly_add_insert p pp)

instance {α : Type u} {n : ℕ} [discrete_field α] : has_add (polynomial' α n) := has_add.mk poly_add

lemma poly_add_comm {α : Type u} {n : ℕ} [discrete_field α] : ∀ (a b : polynomial' α n), a + b = b + a := sorry
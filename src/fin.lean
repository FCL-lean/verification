import finite
namespace fin
def succ_lem: ∀ a val h, 
    Σ' b, fin.succ b = (⟨nat.succ a, h⟩: fin (nat.succ val)) :=
begin
    intros,
    apply psigma.mk (fin.mk a (nat.lt_of_succ_lt_succ h)), 
    refl,
end

end fin
inductive fin' : ℕ → Type
| zero : ∀ {n}, fin' (nat.succ n)
| succ : ∀ {n}, fin' n → fin' (nat.succ n)

namespace fin'

def from_fin : ∀ {n}, fin n → fin' n
| 0 ⟨num, p⟩ := false.elim $ by cases p
| (nat.succ n) ⟨0, p⟩ := fin'.zero
| (nat.succ n) ⟨nat.succ m, p⟩ := fin'.succ (from_fin ⟨m, nat.lt_of_succ_lt_succ p⟩)

def to_fin : ∀ {n}, fin' n → fin n
| (nat.succ n) zero := 0
| (nat.succ n) (succ m) := fin.succ (to_fin m)

lemma to_from : ∀ {n} (f: fin n), to_fin (from_fin f) = f
| 0 ⟨num, p⟩ := false.elim $ by cases p
| (nat.succ n) ⟨0, p⟩ := rfl
| (nat.succ n) ⟨nat.succ m, p⟩ := 
begin 
    unfold from_fin to_fin,
    have h:= fin.succ_lem m n p,
    cases h,
    rw ←h_snd, apply congr_arg,
    rw to_from, symmetry,
    cases h_fst, unfold fin.succ at h_snd,
    have q: h_fst_val = m,
    have t := congr_arg fin.val h_snd, simp at t,
    assumption,
    revert p, revert h_fst_is_lt, rw q, intros,
    refl,
end

lemma from_to : ∀ {n} (f: fin' n), from_fin (to_fin f) = f
| (nat.succ n) zero := rfl
| (nat.succ n) (succ m) :=
begin
    intros, unfold to_fin,
    generalize t : to_fin m = k,
    cases k, unfold fin.succ,
    unfold from_fin, apply congr_arg,
    rw ←t, apply from_to, 
end

end fin'

namespace fin
@[simp]
def from_nat (a : ℕ): fin (nat.succ a) := ⟨a, by constructor⟩

-- variable {n : ℕ}

def induction_on {n} (a : fin n): 
    Π {C: Π n, fin n → Sort*},
        (∀ {n}, C (nat.succ n) 0) 
        → (∀ {n} (k : fin n), C n k → C (nat.succ n) (fin.succ k))
        → C n a :=
begin
    intros,
    rw ←fin'.to_from a,
    apply @fin'.rec_on (λ n x, C n (fin'.to_fin x)) _ (fin'.from_fin a),
    intros, apply a_1,
    intros, unfold fin'.to_fin,
    apply a_2, assumption,
end

def enum_aux : Π (n m : ℕ), (m < n) → list (fin n)
| _ 0 p := ⟨0, p⟩ :: []
| _ (nat.succ m) p := ⟨nat.succ m, p⟩ :: enum_aux _ m (nat.lt_of_succ_lt p)

def enum_aux_in : Π (n : ℕ) (m : ℕ) (h : m < n) k,
    ∀ a ∈ @enum_aux n m h, 
        k = (⟨a.1, nat.lt_succ_of_lt a.2⟩ : fin (nat.succ n)) →
            k ∈ enum_aux (nat.succ n) m (nat.lt_succ_of_lt h) :=
begin
    intros n m, revert n,
    induction m, intros, unfold enum_aux at *, simp at *,
    rw H at a_1, simp at a_1, rw a_1,
    intros, unfold enum_aux, simp,
    rw a_1 at *,
    unfold enum_aux at H, simp at H,
    cases H,
    rw H, simp,
    right, apply m_ih; try {assumption},
    refl,
end

def enum : Π n, list (fin n) 
| 0 := []
| (nat.succ n) := enum_aux (nat.succ n) n (by constructor)

def zero_in_enum {n : ℕ}: (0: fin (nat.succ n)) ∈ (enum (nat.succ n)) :=
begin
    induction n, unfold enum enum_aux, simp, refl,
    unfold enum enum_aux, simp, right,
    unfold enum at n_ih, unfold has_zero.zero, 
    apply @enum_aux_in (nat.succ n_n) n_n (by constructor) _ 0,
    assumption, refl,
end

def m_in_enum : Π n m h h', (⟨m, h'⟩: fin n) ∈ enum_aux n m h :=
begin
    intros n m, revert n,
    induction m, intros, unfold enum_aux, simp,
    intros, unfold enum_aux, simp,
end
-- set_option trace.class_instances true
def in_enum : Π n, ∀ (x : fin n), x ∈ enum n :=
begin 
    intros n,
    induction n, intros, apply fin.elim0 x,
    induction n_n, intros, unfold enum enum_aux, simp,
    rw ←fin.eta x, swap, exact x.2,
    have h: x.1 ≤ 0, exact nat.le_of_succ_le_succ x.2, 
    have h': x.1 = 0, exact nat.eq_zero_of_le_zero h,
    rw fin.ext_iff, simp, assumption,
    unfold enum enum_aux, intros,
    simp, by_cases x.val = nat.succ n_n_n, left, 
    rw fin.ext_iff, assumption,
    right,
    apply enum_aux_in _ _ (by constructor) x _ _ ,
    rw fin.ext_iff, simp, swap,
    have smaller := 
        fin.cast_lt x (nat.lt_of_le_and_ne (nat.le_of_succ_le_succ x.2) h),
    exact smaller,
    rw fin.cast_lt_val,
    rw ←fin.eta (cast_lt x (nat.lt_of_le_and_ne (nat.le_of_succ_le_succ x.2) h)), 
    swap, rw fin.cast_lt_val, exact (nat.lt_of_le_and_ne (nat.le_of_succ_le_succ x.2) h),
    apply n_ih,
end

instance {n : ℕ} : finite (fin n) 
    := ⟨(enum n).to_finset, by simp; apply in_enum⟩



end fin
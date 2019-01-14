import linear_algebra.multivariate_polynomial
import finsupp
import finset
import fintype
import fin
import noetherian
import seq
import bot_zero
import field
import ideal_linear
--set_option profiler true
variables {σ : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Type*}

namespace mv_polynomial

section general
variables [decidable_eq σ] [decidable_eq α]

section discrete_field
variable [discrete_field α]

instance HBT : noetherian (mv_polynomial σ α) := sorry

end discrete_field

section comm_semiring
variables [comm_semiring α]

lemma monomial_mul {a b : σ →₀ ℕ} {c d : α} : 
    monomial a c * monomial b d = monomial (a + b) (c * d) := by finish [monomial, finsupp.single_mul_single]

lemma monomial_ne_zero_lem (a : σ →₀ ℕ) {b : α} (hb : b ≠ 0) : monomial a b ≠ 0 :=
by simp [monomial, finsupp.single, hb]; exact finsupp.ne_zero_lem (finset.singleton_ne_empty _)

def mv_trichotomy (p : mv_polynomial σ α) : psum(p = C 0) 
            (psum (Σ'a : α, pprod (a ≠ 0) (p = C a)) ((Σ'a : α, p = C a) → false)):= 
if h₀ : p.support = ∅ 
    then
    begin
        rw iff.elim_left finsupp.support_eq_empty h₀,
        left, simp, refl,
    end
else if h₁ : p.support = {0} 
        then 
        begin
            right, left,
            unfold C monomial,
            apply (psigma.mk (p.to_fun 0)),
            apply pprod.mk, 
            exact finsupp.support_singleton_neq_zero h₁,
            apply finsupp.ext, intro,
            simp [finsupp.coe_f], unfold finsupp.single,
            by_cases 0 = a;
            simp [h], apply finsupp.support_singleton_eq_zero (ne.symm h) h₁,
        end
    else
    begin
        right, right,
        intro h, unfold C monomial finsupp.single at h,
        cases h,
        by_cases h_fst = 0; simp [h, h_snd] at *; assumption, 
    end

def mv_is_const_aux : Π (p : mv_polynomial σ α), (psum (p = mv_polynomial.C 0) 
            (psum (Σ'a : α, pprod (a ≠ 0) (p = mv_polynomial.C a)) 
                ((Σ'a : α, p = mv_polynomial.C a) → false))) → Prop
| p (psum.inl lp) := true
| p (psum.inr (psum.inl lp)) := true
| p (psum.inr (psum.inr rp)) := false

def mv_is_const (p : mv_polynomial σ α): Prop := mv_is_const_aux p (mv_trichotomy p)

def mv_is_const_neqz {p : mv_polynomial σ α}:
    mv_is_const p → p ≠ 0 → (Σ'a : α, pprod (a ≠ 0) (p = mv_polynomial.C a)) :=
begin
    intros, unfold mv_is_const at a,
    generalize h : mv_trichotomy p = m,
    rw h at a,
    cases m, rw m at a_1, apply false.elim, apply a_1, simp,
    cases m, assumption,
    unfold mv_is_const_aux at a,
    apply false.elim, assumption,
end
@[simp]
lemma const_mv_is_const (a : α):
    mv_is_const (C a : mv_polynomial σ α) :=
begin
    unfold mv_is_const,
    cases h: mv_trichotomy (C a),
    unfold mv_is_const_aux,
    cases h': val,
    unfold mv_is_const_aux, unfold mv_is_const_aux,
    apply val_1, exact ⟨a, rfl⟩,
end

lemma eq_mv_is_const {p : mv_polynomial σ α} :
    mv_is_const p → Σ'a : α, p = C a :=
λ h, begin
    generalize hp_tri : mv_trichotomy p = p_tri,
    unfold mv_is_const at h, rw hp_tri at h,
    cases p_tri, apply psigma.mk (0 : α), assumption,
    cases p_tri, apply psigma.mk p_tri.1, exact p_tri.2.2,
    unfold mv_is_const_aux at h, apply psigma.mk (0 : α), revert h, simp,
end

lemma eq_mv_is_const' {p : mv_polynomial σ α} :
    (Σ' a : α, p = C a) → mv_is_const p :=
λ h, begin
    unfold mv_is_const,
    cases mv_trichotomy p, simp [mv_is_const_aux],
    cases val, simp [mv_is_const_aux],
    simp [mv_is_const_aux], exact val h,
end

lemma ne_mv_is_const {p : mv_polynomial σ α}:
    ¬ mv_is_const p → (Σ'a : α, p = mv_polynomial.C a) → false :=
begin
    intros,
    generalize j : mv_trichotomy p = m,
    cases h:m, unfold mv_is_const at a,
    rw [j, h] at a, unfold mv_is_const_aux at a,
    apply a, trivial,
    cases h1:val, unfold mv_is_const at a,
    rw [j, h, h1] at a, unfold mv_is_const_aux at a,
    apply a, trivial, apply val_1, assumption,
end

lemma nzero_of_ne_mv_is_const {p : mv_polynomial σ α} : 
    ¬ mv_is_const p → p ≠ 0 :=
λ h, begin
    let ne_p := ne_mv_is_const h,
    intro, apply ne_p,
    apply psigma.mk (0 : α), simp [a],
end

instance decidable_mv_is_const (p : mv_polynomial σ α): decidable (mv_is_const p) :=
begin
    cases mv_trichotomy p,
    right, apply eq_mv_is_const' (psigma.mk 0 val),
    cases val,
    right, apply eq_mv_is_const' (psigma.mk val.fst val.snd.snd),
    left, intro h, apply val (eq_mv_is_const h),
end

section semilattice
variables [lattice.semilattice_sup_bot (σ →₀ ℕ)]
variables [bot_zero σ ℕ]
def leading_monomial (a: mv_polynomial σ α): σ →₀ ℕ := a.support.sup id

def leading_monomial_zero : (0: mv_polynomial σ α).leading_monomial = 0 :=
begin
    unfold leading_monomial,
    rw finsupp.support_eq_empty.2; try {simp}; try {trivial},
    rw _inst_5.zero_bot, by apply_instance,
end

def leading_coeff (a: mv_polynomial σ α): α := a.to_fun a.leading_monomial

lemma leading_coeff_C (a : α): leading_coeff (C a : mv_polynomial σ α) = a :=
begin
    unfold leading_coeff leading_monomial C monomial,
    rw [←finsupp.coe_f, finsupp.single_apply],
    simp [finsupp.single], by_cases a = 0; simp [h, finset.singleton, finset.sup, finset.fold],
end

def leading_term (a: mv_polynomial σ α): mv_polynomial σ α 
    := monomial a.leading_monomial a.leading_coeff

lemma leading_monomial_eq (p : σ →₀ ℕ) {x : α} (h : x ≠ 0) : 
    p = (monomial p x).leading_monomial :=
begin
    simp [leading_monomial, monomial, finsupp.single, h],
    change p = finset.sup {p} id,
    rw finset.sup_singleton, trivial,
end

lemma support_empty {a : mv_polynomial σ α} : a.support = ∅ → a.leading_monomial = ⊥ :=
λ h, by finish [leading_monomial, h]

lemma leading_monomial_zero_of_zero {a : mv_polynomial σ α} : a = 0 → a.leading_monomial = 0 :=
λ h, by finish [leading_monomial, h, _inst_5.zero_bot]

lemma const_support_zero {a : α} (h : a ≠ 0) : (C a : mv_polynomial σ α).support = {0} := 
by finish [C, monomial, finsupp.single, h]

lemma const_leading_monomial {a : α} : (C a : mv_polynomial σ α).leading_monomial = 0 :=
if h : a = 0 then by finish [h, leading_monomial, _inst_5.zero_bot]
else by unfold leading_monomial; rw [@const_support_zero _ _ _ _ _ _ _inst_5 _ h, finset.sup_singleton]; refl

lemma leading_monomial_eqz_of_const {p : mv_polynomial σ α} (h : mv_is_const p) : p.leading_monomial = 0 :=
begin
    have h' := eq_mv_is_const h,
    cases h', by_cases h'_fst = (0 : α),
    finish [leading_monomial_zero_of_zero],
    simp [h'_snd, leading_monomial, @const_support_zero σ _ _ _ _ _ _ _ h],
    apply finset.sup_singleton,
end 

section fintype_s
variable [fins: fintype σ]
include fins

def leading_monomial_le (a b: mv_polynomial σ α): Prop
    := finsupp.leading_monomial_le a.leading_monomial b.leading_monomial

instance leading_monomial_le_dec (a b: mv_polynomial σ α): decidable (leading_monomial_le a b) :=
begin
    unfold leading_monomial_le finsupp.leading_monomial_le,
    apply decidable_of_iff (∀ e ∈ fins.elems, a.leading_monomial e ≤ b.leading_monomial e),
    split; intros,
    apply a_1 elem, apply fins.complete,
    apply a_1 e,
end

lemma leading_monomial_zero_of_le_zero {a b : mv_polynomial σ α} : a.leading_monomial = 0
     → leading_monomial_le b a → b.leading_monomial = 0 := 
λ ha hba, begin
    simp [leading_monomial_le, finsupp.leading_monomial_le, ha] at hba,
    apply finsupp.ext, simp [hba],
end

omit fins
end fintype_s

end semilattice

def leading_term_sub' {n} (a b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_monomial_le b a) : fin n →₀ ℕ
     := finsupp.fin_n.leading_term_sub a.leading_monomial b.leading_monomial h

@[simp]
def leading_term_sub'_zero {n} (b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_monomial_le b 0): leading_term_sub' 0 b h = 0 :=
begin
    have h': b.leading_monomial = 0,
    apply finsupp.fin_n.leading_monomial_le_antisymm,
    assumption, apply finsupp.fin_n.leading_monomial_le_zero,
    unfold leading_term_sub',
    unfold leading_monomial_le at h,
    revert h,
    change Π (h: finsupp.leading_monomial_le (leading_monomial b) (leading_monomial 0)),
        finsupp.fin_n.leading_term_sub (leading_monomial 0) (leading_monomial b) h = 0,
    rw [h', @leading_monomial_zero (fin n) α],
    intros, apply finsupp.fin_n.leading_term_sub_zero,
end

end comm_semiring

section semilattice_decidable_linear_order
variables [lattice.semilattice_sup_bot (σ →₀ ℕ)] [bot_zero σ ℕ]
variables [is_total (σ →₀ ℕ) has_le.le] [@decidable_rel (σ →₀ ℕ) has_le.le]

section comm_semiring
variables [comm_semiring α]

def last_monomial (p : mv_polynomial σ α) : option (σ →₀ ℕ) := p.support.min

@[simp] lemma zero_last_monomial : (0 : mv_polynomial σ α).last_monomial = none := by finish [last_monomial]

lemma last_monomial_none_iff_zero {p : mv_polynomial σ α} : p = 0 ↔ p.last_monomial = none :=
⟨λ h, begin
    have H : p.support = ∅, finish [h],
    simp [last_monomial, H],
end,
λ h, begin
    simp [last_monomial, finset.min_eq_none] at h, assumption,
end⟩

lemma last_monomial_of_monomial {ps : σ →₀ ℕ} {pa : α} (ha : pa ≠ 0) : (monomial ps pa).last_monomial = ps :=
begin
    simp [option.some_lem, last_monomial, monomial, finsupp.single, ha],
    rw [←finset.singleton_eq_singleton ps, finset.min_singleton], 
end

lemma last_monomial_of_monomial' {p : mv_polynomial σ α} {ps pa} (ha : pa ≠ (0 : α))
(hp : p = monomial ps pa) : p.last_monomial = ps := 
by rw hp; apply last_monomial_of_monomial ha

lemma last_monomial_some_iff_nez {p : mv_polynomial σ α} : p ≠ 0 ↔ ∃ px, p.last_monomial = some px :=
⟨λ h, begin
    unfold last_monomial,
    have h' := finset.min_of_ne_empty ((finsupp.support_ne_empty p).1 h), simp at h',
    assumption,
end, 
λ h h', begin 
    cases h with px h, rw [last_monomial_none_iff_zero.1 h'] at h,
    finish,
end⟩ 

def last_monomial' (p : mv_polynomial σ α) (hp : p ≠ 0) : σ →₀ ℕ := p.support.min' ((finsupp.support_ne_empty p).1 hp)

def last_term (p : mv_polynomial σ α) (hp : p ≠ 0) : mv_polynomial σ α := monomial (last_monomial' _ hp) (p.to_fun (last_monomial' _ hp))

lemma last_monomial_eq {p : mv_polynomial σ α} (hp : p ≠ 0) : 
option.get (option.is_some_iff_exists.2 (last_monomial_some_iff_nez.1 hp)) = last_monomial' _ hp :=
by finish [last_monomial', finset.min']

lemma last_monomial'_of_monomial {ps : σ →₀ ℕ} {pa : α} (ha : pa ≠ 0) : 
last_monomial' _ (monomial_ne_zero_lem ps ha) = ps := begin
   unfold last_monomial' monomial, simp [finsupp.single_support ha],
   have h : finset.min {ps} = some ps := finset.min_singleton,
   rw ←option.mem_def at h,
   simp [finset.min', option.get_of_mem _ h],
end

lemma last_monomial'_apply {p : mv_polynomial σ α} (hp : p ≠ 0) : p.to_fun (last_monomial' _ hp) ≠ 0 :=
by simp [last_monomial']; apply finsupp.min_apply p hp


lemma last_monomial'_mem {p : mv_polynomial σ α} (hp : p ≠ 0) : last_monomial' _ hp ∈ p.support :=
by simp [finsupp.mem_support_iff.symm]; apply last_monomial'_apply hp

lemma lt_last_monomial'_apply {p : mv_polynomial σ α} (hp : p ≠ 0) : ∀ x < last_monomial' _ hp, p.to_fun x = 0 :=
by simp [last_monomial']; apply finsupp.lt_min_apply p hp

lemma last_monomial_of_add_le' {p q : mv_polynomial σ α} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p + q ≠ 0) : 
    min (last_monomial' _ hp) (last_monomial' _ hq) ≤ last_monomial' _ hpq :=
begin
    have h := finset.min'_le _ (finset.ne_empty_union.1 (not_and_of_not_left (q.support = ∅) ((finsupp.support_ne_empty p).1 hp))) 
        _ (finset.mem_of_subset finsupp.support_add (last_monomial'_mem hpq)),
    rw finset.union_min' _ ((finsupp.support_ne_empty q).1 hq) at h,
    finish [last_monomial', h],
end

lemma last_monomial_of_add {p q : mv_polynomial σ α} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p + q ≠ 0)
(h_nez : (last_term _ hp) + (last_term _ hq) ≠ 0) : 
min (last_monomial' _ hp) (last_monomial' _ hq) = last_monomial' _ hpq :=
begin
    apply antisymm (last_monomial_of_add_le' hp hq hpq),
    cases lt_trichotomy (last_monomial' _ hp) (last_monomial' _ hq) with h; unfold last_monomial' at *,
    simp [min, le_of_lt h], apply finset.min'_le, simp [finsupp.mem_support_iff],
    simp [finsupp.coe_f, lt_last_monomial'_apply hq _ h], apply last_monomial'_apply,
    cases h,
    simp [min, le_of_eq h], apply finset.min'_le, simp [finsupp.mem_support_iff],
    intro h', apply h_nez, simp [last_term, last_monomial', h.symm, monomial],
    rw [←finsupp.single_add, ←finsupp.coe_f, ←finsupp.coe_f],
    apply finsupp.single_eqz.2 h', 
    simp [min, not_le_of_lt h], apply finset.min'_le, simp [finsupp.mem_support_iff],
    simp [finsupp.coe_f, lt_last_monomial'_apply hp _ h], apply last_monomial'_apply,
end

lemma last_term_add_nez_of_not_mem (p : mv_polynomial σ α ) {a : σ →₀ ℕ} {b : α} 
(ha : a ∉ p.support) (hb : b ≠ 0) (hp : p ≠ 0) :
last_term _ (monomial_ne_zero_lem a hb) + last_term _ hp ≠ 0 :=
λ h, begin
    have ha' : last_monomial' (monomial a b) (by apply monomial_ne_zero_lem a hb) ∉ p.support,
        rw last_monomial'_of_monomial, assumption,
    unfold last_term at h,
    have h' := finsupp.mem_support_iff.1 (last_monomial'_mem hp), rw finsupp.coe_f at h',
    have H := finsupp.single_add_eqz' (not_and_of_not_right ((monomial a b).to_fun (last_monomial' (monomial a b) _) = 0) h') h,
    rw [←finsupp.single_add_eqz (not_and_of_not_right ((monomial a b).to_fun (last_monomial' (monomial a b) _) = 0) h') h,
        ←finsupp.coe_f, ←finsupp.coe_f] at H,
    simp [finsupp.not_mem_support_iff.1 ha'] at H,
    apply absurd H, apply last_monomial'_apply,
end

lemma zero_iff_leading_coeff_zero {p : mv_polynomial σ α}: 
    p.leading_coeff = 0 ↔ p = 0 :=
⟨λ coeffz, begin
    unfold leading_coeff leading_monomial at coeffz,
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff] at coeffz,
    have h: p.support = ∅,
    by_cases p.support = ∅,
    assumption,
    apply false.elim, apply coeffz,
    apply finset.mem_of_sup_id, assumption,
    rw finsupp.support_eq_empty at h,
    assumption,
end, 
λ hp, by finish [leading_coeff, leading_monomial, hp] ⟩

lemma not_zero_iff_leading_coeff_not_zero {p : mv_polynomial σ α}: 
    p.leading_coeff ≠ 0 ↔ p ≠ 0 := by finish [zero_iff_leading_coeff_zero]

lemma leading_monomial_ne_zero_coeff {a : mv_polynomial σ α} : 
    a.leading_monomial ≠ 0 → a.leading_coeff ≠ 0 :=
λ neqz eqa, begin
    unfold leading_monomial at neqz,
    unfold leading_coeff at eqa,
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff] at eqa,
    apply eqa, apply finset.mem_of_sup_id,
    intro eqe, rw eqe at *,
    simp at neqz,
    apply neqz, rw _inst_4.zero_bot,
end

lemma leading_monomial_eqz_of_const' {p : mv_polynomial σ α} (h : p.leading_monomial = 0) : mv_is_const p :=
begin 
    rw [_inst_4.zero_bot, leading_monomial] at h,
    have h' : p.support = ∅ ∨ p.support = {⊥}, from finset.sup_bot p.support h,
    cases h', rw finsupp.support_eq_empty at h', simp [h'],
    rw [←_inst_4.zero_bot] at h', 
    apply eq_mv_is_const', apply psigma.mk (p.to_fun 0),
    apply finsupp.ext, intro x,
    simp [finsupp.coe_f, C, monomial, finsupp.single],
    by_cases hx: 0 = x; simp [hx],
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff, h'],
    finish [finset.not_mem_singleton],
end

lemma leading_monomial_nez_of_ne_const {p : mv_polynomial σ α} (h : ¬ mv_is_const p) : p.leading_monomial ≠ 0 :=
λ h', by apply h (leading_monomial_eqz_of_const' h')

def leading_monomial_eqz_const {p : mv_polynomial σ α}:
    p.leading_monomial = 0 → Σ' (a : α), p = C a :=
λ h, by apply eq_mv_is_const (leading_monomial_eqz_of_const' h)

lemma leading_monomial_lt_right_of_add {a b : mv_polynomial σ α} (h : a.leading_term + b.leading_term ≠ 0) :
    (a + b).leading_monomial ≥ b.leading_monomial :=
begin
    unfold leading_monomial leading_term monomial at *,
    from if h₁ : finset.sup (a.support) id = finset.sup (b.support) id
    then begin
        rw [h₁, ←finsupp.single_add] at h,
        have lc_ab : leading_coeff a + leading_coeff b ≠ 0,
            intro hlc, rw hlc at h, finish,
        unfold leading_coeff leading_monomial at lc_ab,
        rw [←finsupp.coe_f, ←finsupp.coe_f, h₁, ←finsupp.add_apply, ←finsupp.mem_support_iff] at lc_ab,
        rw ←id.def (finset.sup (b.support) id), apply finset.le_sup lc_ab,
    end
    else begin 
        have h₂ := lt_or_gt_of_ne h₁,
        have H : ∀ {x y : mv_polynomial σ α}, x.support.sup id > y.support.sup id → x.support.sup id ∈ (x + y).support,
            intros x y hxy,
            have hx : x.support ≠ ∅, intro hx, simp [hx] at hxy, apply absurd hxy, apply not_lt_of_le, apply _inst_3.bot_le,
            simp [finsupp.mem_support_iff, finsupp.apply_eq_zero_of_gt_max hxy, finsupp.mem_support_iff.1 (finset.mem_of_sup_id hx)],
        cases h₂,
        rw add_comm,
        apply finset.le_sup_id (H h₂),
        apply le_of_lt (lt_of_lt_of_le h₂ (finset.le_sup_id (H h₂))),
    end
end

lemma leading_monomial_lt_left_of_add {a b : mv_polynomial σ α} (h : a.leading_term + b.leading_term ≠ 0) :
    (a + b).leading_monomial ≥ a.leading_monomial := 
    by rw add_comm at *; apply leading_monomial_lt_right_of_add h

lemma leading_monomial_of_add {p q :mv_polynomial σ α} (hpq : p.leading_term + q.leading_term ≠ 0) : 
    (p + q).leading_monomial = p.leading_monomial ∨ (p + q).leading_monomial = q.leading_monomial :=
begin
    unfold leading_term monomial leading_monomial leading_coeff at *,
    have H₁ : ∀ {x y : mv_polynomial σ α}, x.support.sup id > y.support.sup id → x.support.sup id ≤ (x + y).support.sup id,
        intros x y hxy,
        have hx : x.support ≠ ∅, intro hx, simp [hx] at hxy, apply absurd hxy, apply not_lt_of_le, apply _inst_3.bot_le,
        apply finset.le_sup_id,
        simp [finset.le_sup, finsupp.mem_support_iff, finsupp.apply_eq_zero_of_gt_max hxy, finsupp.mem_support_iff.1 (finset.mem_of_sup_id hx)],
    have H₂ : (p + q).support.sup id ≤ (p.support ∪ q.support).sup id := finset.sub_sup finsupp.support_add,
        rw finset.sup_union at H₂,
    cases (lt_trichotomy (p.support.sup id) (q.support.sup id)) with h,
    right, rw lattice.sup_of_le_right (le_of_lt h) at H₂, rw add_comm at *, apply antisymm H₂ (H₁ h),
    cases h, {
        right, rw lattice.sup_of_le_right (le_of_eq h) at H₂,
        rw [h, ←finsupp.single_add] at hpq,
        have hpq' : p.to_fun (finset.sup (q.support) id) + q.to_fun (finset.sup (q.support) id) ≠ 0,
            intro h_sup, rw h_sup at hpq, finish,
        rw [←finsupp.coe_f, ←finsupp.coe_f, ←finsupp.add_apply, ←finsupp.mem_support_iff] at hpq',
        apply antisymm H₂ (finset.le_sup_id hpq'),
    },
    left, rw lattice.sup_of_le_left (le_of_lt h) at H₂, apply antisymm H₂ (H₁ h),
end

lemma leading_monomial_of_add_of_le {p q : mv_polynomial σ α} (hpq₁ : p.leading_term + q.leading_term ≠ 0) 
(hpq₂ : q.leading_monomial ≤ p.leading_monomial) :  (p + q).leading_monomial = p.leading_monomial :=
begin
    rw le_iff_lt_or_eq at hpq₂, 
    have h := leading_monomial_of_add hpq₁, 
    cases hpq₂; cases h, any_goals {finish},
    rw ←h at hpq₂, apply absurd hpq₂ (not_lt_of_le (leading_monomial_lt_left_of_add hpq₁)),
end

lemma leading_term_add_nez_of_not_mem {p : mv_polynomial σ α} {a : σ →₀ ℕ} {b : α} :
p ≠ 0 → b ≠ 0 → a ∉ p.support → leading_term (monomial a b) + leading_term p ≠ 0 :=
λ hp hb ha h, begin
    unfold leading_term at h,
    have h' := finsupp.single_add_eqz (not_and_of_not_right _ (not_zero_iff_leading_coeff_not_zero.2 hp)) h,
    rw ←leading_monomial_eq a hb at h',
    simp [leading_monomial] at h', rw h' at ha,
    apply absurd (finset.mem_of_sup_id (λ h, hp (finsupp.support_eq_empty.1 h))) ha,
end

lemma add_support_subset_union (c : mv_polynomial σ α) (as : σ →₀ ℕ) {aa : α} (haa : aa ≠ 0) :
 (finset.fold (+) 0 (λ (a : σ →₀ ℕ), finsupp.single (as + a) (mul_zero_class.mul (c.to_fun a) aa)) (c.support)).support 
  ⊆ finset.fold (∪) (∅) (λ (a : σ →₀ ℕ), (finsupp.single (as + a) (mul_zero_class.mul (c.to_fun a) aa)).support) (c.support) :=
begin
    apply finsupp.induction c, simp,
    intros a b f haf hb ih,
    have h : (finsupp.single a b + f).support = insert a f.support,
        have h' : (finsupp.single a b).support = {a}, simp [finsupp.single, hb],
        rw [finset.insert_eq, ←h'],
        apply finsupp.support_add_eq,
        simp [finsupp.single, hb, finsupp.not_mem_support_iff.1 haf],
    rw [h, finset.fold_insert haf], simp, 
    apply finset.subset.trans finsupp.support_add,
    have h_to_fun_eq : ∀ (x : σ →₀ ℕ) (hx : x ∈ f.support), f.to_fun x = (f + finsupp.single a b).to_fun x,
            intros x hx,
            have hax : a ≠ x, intro hax', rw hax' at haf, exact haf hx,
            repeat {rw ←finsupp.coe_f}, simp, simp [finsupp.coe_f, finsupp.single], simp [hax],
    have h_congr : ∀ (x : σ →₀ ℕ) (hx : x ∈ f.support), (λ x, finsupp.single (as + x) (mul_zero_class.mul (f.to_fun x) aa)) x =
        (λ x, finsupp.single (as + x) (mul_zero_class.mul ((f + finsupp.single a b).to_fun x) aa)) x,
        intros x hx, simp [h_to_fun_eq x hx],
    have h_congr' : ∀ (x : σ →₀ ℕ) (hx : x ∈ f.support), (λ x, (finsupp.single (as + x) (mul_zero_class.mul (f.to_fun x) aa)).support) x =
        (λ x, (finsupp.single (as + x) (mul_zero_class.mul ((f + finsupp.single a b).to_fun x) aa)).support) x,
        intros x hx, simp [h_to_fun_eq x hx],
    rw [finset.fold_congr h_congr, finset.fold_congr h_congr'] at ih,
    apply finset.union_subset' (finset.subset.refl _) ih,
end

end comm_semiring

section comm_ring
variables [comm_ring α]

lemma support_subset_of_linear_combination_union (s : finset (mv_polynomial σ α)) : 
    ∀ (hs: s ≠ ∅) (p : mv_polynomial σ α) (hp₁ : p ∈ ideal.span (↑s : set (mv_polynomial σ α))),
    ∃ (c : ((mv_polynomial σ α) →₀ (mv_polynomial σ α))), c.support ⊆ s ∧ p.support ⊆ s.fold (∪) (∅) (λ a, ((c.to_fun a) * a).support) :=
begin
    apply finset.induction_on s, finish,
    intros a s' has' ih hs p hp,
    rw [finset.coe_insert, ideal.mem_span_insert] at hp,
    rcases hp with ⟨a', ⟨z, ⟨hz, hp⟩⟩⟩,
    by_cases hs' : s' = ∅,
    simp [hs', ideal.span] at hz, 
    apply exists.intro (finsupp.single a a'),
    rw [finset.fold_insert has', hp, hz, hs', ←finsupp.coe_f], simp [finsupp.single, finset.insert_eq], 
    by_cases ha' : a' = 0; finish [ha'],
    rcases ih hs' z hz with ⟨zc, ⟨hzc, hz'⟩⟩,
    apply exists.intro (finsupp.single a a' + zc), 
    simp,
    have hzc_app : zc a = 0, rw [←finsupp.not_mem_support_iff], intro hazc, exact has' (hzc hazc),
    
    have h_congr : ∀ x ∈ s', (λ x, (zc.to_fun x * x).support) x = (λ x, ((zc + finsupp.single a a').to_fun x * x).support) x,
        intros x hx, simp, repeat {rw [←finsupp.coe_f]}, simp [finsupp.single_apply, ne.symm (finset.ne_of_mem_and_not_mem hx has')],
    
    simp [(finset.fold_congr h_congr).symm, hzc_app, hp], split,
    apply finset.subset.trans finsupp.support_add (finset.union_subset'_symm hzc finsupp.support_single_subset),
    apply finset.subset.trans finsupp.support_add (finset.union_subset'_symm hz' (finset.subset.refl _)),
end

end comm_ring

section integral_domain
variables [integral_domain α] [is_monomial_order (σ →₀ ℕ) has_le.le]

def finsupp.nat.decidable_linear_ordered_cancel_comm_monoid
 : decidable_linear_ordered_cancel_comm_monoid (σ →₀ ℕ) := {
    add_left_cancel := λ a b c, (finsupp.nat.add_left_cancel a b c).1,
    add_right_cancel := λ a b c, (finsupp.nat.add_right_cancel a b c).1,
    add_le_add_left := λ a b h c, by simp [add_comm]; apply _inst_8.mono_order; exact h,
    le_of_add_le_add_left := λ a b c H, begin 
        rw [add_comm a b, add_comm a c] at H,
        by_cases b ≤ c, finish,
        rw [←lt_iff_not_ge, lt_iff_le_and_ne] at h,
        have h' : c + a ≤ b + a, apply _inst_8.mono_order, exact h.left,
        have h_eq := (finsupp.nat.add_right_cancel c a b).1 (antisymm h' H),
        apply absurd h_eq h.right,
    end,
    le_total := _inst_5.total,
    decidable_le := _inst_6,
    .._inst_3,
    ..@finsupp.add_comm_monoid σ ℕ _ _ _
}

lemma mul_m_leading_term_add_nez {p : mv_polynomial σ α} {a a' : σ →₀ ℕ} {b b' : α} (hp : p ≠ 0) (hb : b ≠ 0 ∧ b' ≠ 0)
(ih : p ≠ 0 → b' ≠ 0 → leading_monomial (monomial a' b' * p) = a' + p.leading_monomial)
(ha : a ∉ p.support) : leading_term ((monomial a' b') * (monomial a b)) + leading_term (monomial a' b' * p) ≠ 0 :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    rw [monomial_mul], unfold leading_term, intro h,
    have h_mc : leading_coeff (monomial (a' + a) (b' * b)) ≠ 0,
        rw not_zero_iff_leading_coeff_not_zero, exact monomial_ne_zero_lem _ (mul_ne_zero hb.right hb.left),
    have h' := finsupp.single_add_eqz (not_and_of_not_left _ h_mc) h,
    rw [ih hp hb.right, ←leading_monomial_eq (a' + a) (mul_ne_zero hb.right hb.left), add_left_cancel_iff, leading_monomial] at h',
    rw h' at ha,
    apply absurd (finset.mem_of_sup_id (λ h, hp (finsupp.support_eq_empty.1 h))) ha,
end

lemma leading_monomial_of_mul_m_left {p : mv_polynomial σ α} : ∀ {a b}, p ≠ 0 → b ≠ 0
→ ((monomial a b) * p).leading_monomial = a + p.leading_monomial :=
begin
    apply finsupp.induction p, finish,
    intros a b f haf hb ih a' b' h_nez hb',
    have H : finsupp.single a b = monomial a b := by finish [monomial],
    simp [H],
    from if hf : f = 0 
    then by simp [hf, monomial_mul, (leading_monomial_eq (a + a') (mul_ne_zero hb' hb)).symm, (leading_monomial_eq a hb).symm]
    else begin
        have ltm_nez := leading_term_add_nez_of_not_mem hf hb haf,
        have ltm_nez' := mul_m_leading_term_add_nez hf (and.intro hb hb') (@ih a' _) haf,
        have m_id : leading_monomial ((monomial a' b') * (monomial a b)) = a' + leading_monomial (monomial a b),
            rw [monomial_mul, ←leading_monomial_eq (a' + a) (mul_ne_zero hb' hb), ←leading_monomial_eq a hb],
        letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
        by_cases h : leading_monomial f ≤ leading_monomial (monomial a b),
        have h' : leading_monomial (monomial a' b' * f) ≤ leading_monomial (monomial a' b' * monomial a b),
            rw [m_id, (ih hf hb')], apply add_le_add_left h,
        rw [add_comm f (monomial a b), mul_add, leading_monomial_of_add_of_le ltm_nez h, leading_monomial_of_add_of_le ltm_nez' h', m_id],
        rw [add_comm] at ltm_nez ltm_nez',
        have h' : leading_monomial (monomial a' b' * monomial a b) ≤ leading_monomial (monomial a' b' * f),
            rw [(ih hf hb'), m_id], apply add_le_add_left (le_of_not_le h),
        rw [mul_add, leading_monomial_of_add_of_le ltm_nez (le_of_not_le h), leading_monomial_of_add_of_le ltm_nez' h', ih hf hb'],
    end
end

lemma leading_monomial_of_mul_m_right {p : mv_polynomial σ α} : ∀ {a b}, p ≠ 0 → b ≠ 0
→ (p * (monomial a b)).leading_monomial = p.leading_monomial + a := 
    λ _ _ hp hb, by rw [mul_comm, add_comm]; apply leading_monomial_of_mul_m_left hp hb

lemma mv_mul_m_ne_zero {p : mv_polynomial σ α} {a : σ →₀ ℕ} {b : α}: p ≠ 0 → b ≠ 0 → p * (monomial a b) ≠ 0 := 
λ hp hb, begin
    cases (mv_trichotomy p) with _ hp', finish,
    cases hp',
    rw [hp'.2.2, C_mul_monomial], apply monomial_ne_zero_lem _ (mul_ne_zero hp'.2.1 hb),
    intro h,
    have h' := leading_monomial_zero_of_zero h,
    rw [leading_monomial_of_mul_m_right hp hb, finsupp.nat.add_eqz_iff] at h',
    apply hp' (leading_monomial_eqz_const h'.left),
end

lemma mv_mul_m_ne_zero' {p : mv_polynomial σ α} {a : σ →₀ ℕ} {b : α}: p ≠ 0 → b ≠ 0 → (monomial a b) * p ≠ 0 := 
λ hp hb, by rw [mul_comm]; apply mv_mul_m_ne_zero hp hb

lemma mul_leading_term_add_nez {p q : mv_polynomial σ α} {a : σ →₀ ℕ} {b : α} (hp : p ≠ 0) (hq : q ≠ 0) (hb : b ≠ 0)
(ihp : leading_monomial (p * q) = p.leading_monomial + q.leading_monomial)
(ihm : leading_monomial (p * (monomial a b)) = p.leading_monomial + a) 
(ha : a ∉ q.support) : leading_term (p * (monomial a b)) + leading_term (p * q) ≠ 0 :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    unfold leading_term, intro h,
    have h' := finsupp.single_add_eqz (not_and_of_not_left _ (not_zero_iff_leading_coeff_not_zero.2 (mv_mul_m_ne_zero hp hb))) h,
    simp [-add_comm, ihp, ihm, add_left_cancel_iff] at h',
    rw h' at ha,
    apply absurd (finset.mem_of_sup_id (λ h, hq (finsupp.support_eq_empty.1 h))) ha,
end

lemma support_of_mul_single {a b : σ →₀ ℕ} {c : α} {f : mv_polynomial σ α} : 
    f ≠ 0 → c ≠ 0 → a + b ∈ (f * finsupp.single b c).support → a ∈ f.support :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    letI : ring (mv_polynomial σ α) := mv_polynomial.ring,
    intros, revert a b, apply finsupp.induction f,
    begin
        intros,
        from @eq.subst _ (λ x : mv_polynomial σ α, a + b ∈ x.support) _ _ (@ring.zero_mul _ _inst_9 (finsupp.single b c)) a_3,
    end,
    begin
        intros,
        rw [right_distrib, finsupp.support_add_eq, finset.mem_union, finsupp.single_mul_single, finsupp.single_support] at a_3_1,
        cases a_3_1,
        begin
            cases a_3_1, 
            rw [add_right_cancel_iff] at a_3_1, cases a_3_1,
            rw [finsupp.support_add_eq, finset.mem_union],
            left, rw finsupp.single_support, simp,
            assumption, rw [disjoint, finsupp.single_support, finset.singleton_non_mem_inter_empty'],
            any_goals { assumption }, any_goals { by simp * }, cases a_3_1,
        end,
        begin
            rw [finsupp.support_add_eq, finset.mem_union],
            right, apply a_5, assumption,
            rw [disjoint, finsupp.single_support, finset.singleton_non_mem_inter_empty'],
            all_goals {simp *},
        end,
        by simp *,
        begin
            rw [disjoint, finsupp.single_mul_single, finsupp.single_support, finset.singleton_non_mem_inter_empty'],
            any_goals { by simp * },
            intro, apply a_3, apply a_5,
            assumption,
        end,
    end,
end

lemma support_of_mul_single_iff {a b : σ →₀ ℕ} {c : α} {f : mv_polynomial σ α} : 
    f ≠ 0 → c ≠ 0 → (a ∈ f.support ↔ a + b ∈ (f * finsupp.single b c).support) :=
begin
    letI : ring (mv_polynomial σ α) := mv_polynomial.ring,
    intros; apply iff.intro,
    begin
        revert a b a_1, apply finsupp.induction f,
        by finish,
        begin
            intros,
            by_cases f_1 = 0;
            rw [right_distrib, finsupp.support_add_eq, finsupp.single_mul_single, finset.mem_union],
            begin
                rw [h] at *,
                rw [add_zero, finsupp.single_support] at *, cases a_6, cases a_6,
                left, rw finsupp.single_support, any_goals { by simp *}, cases a_6,

            end,
            begin
                unfold disjoint, rw [finsupp.single_mul_single, finsupp.single_support],
                rw finset.singleton_non_mem_inter_empty'; simp *,
                apply @eq.subst _ (λ (x : mv_polynomial σ α), x.to_fun (a + b_1) = 0) _ _ (@ring.zero_mul _ _inst (0 * finsupp.single b_1 c)).symm,
                apply @finsupp.zero_apply (σ →₀ ℕ) α _ (a + b_1),
                simp *,
            end,
            begin
                rw [finsupp.support_add_eq, finset.mem_union] at a_6,
                cases a_6,
                left, rw [finsupp.single_support] at *,
                cases a_6, cases a_6,
                by constructor; refl,
                by cases a_6,
                by simp [a_2, a_3],
                by assumption,
                begin
                    right,
                    apply a_4; assumption,
                end,
                begin
                    rw [disjoint, finsupp.single_support, finset.singleton_non_mem_inter_empty']; simp *,
                end
            end,
            begin
                rw [disjoint, finsupp.single_mul_single, finsupp.single_support, finset.singleton_non_mem_inter_empty']; try {by simp *},
                intro, apply a_1, apply @support_of_mul_single _ _ _ _ _ _ _ _ _ _ _; try { apply_instance }; try { assumption },
            end,
        end,
    end,
    begin
        apply @support_of_mul_single _ _ _ _ _ _ _ _ _ _ _; try { apply_instance }; try { assumption },
    end,
end

lemma leading_monomial_of_mul {p q : mv_polynomial σ α} : (p ≠ 0 ∧ q ≠ 0)
→ (p * q).leading_monomial = p.leading_monomial + q.leading_monomial :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    apply finsupp.induction q, finish,
    intros a b f haf hb hfp h_sfp, 
    have H : finsupp.single a b = monomial a b := by finish [monomial], rw [H] at *,
    from if hf : f = 0 
    then by simp [hf, leading_monomial_of_mul_m_right h_sfp.left hb, (leading_monomial_eq a hb).symm]
    else begin
        have ltm_nez := leading_term_add_nez_of_not_mem hf hb haf,
        have ltm_nez' := mul_leading_term_add_nez h_sfp.left hf hb (hfp (and.intro h_sfp.left hf)) (leading_monomial_of_mul_m_right h_sfp.left hb) haf,
        by_cases h: leading_monomial f ≤ leading_monomial (monomial a b),
        {
            have h' :  leading_monomial (p * f) ≤ leading_monomial (p * monomial a b),
                rw [hfp (and.intro h_sfp.left hf), leading_monomial_of_mul_m_right h_sfp.left hb, leading_monomial_eq a hb], 
                apply add_le_add_left h,
            rw [mul_add, leading_monomial_of_add_of_le ltm_nez h, leading_monomial_of_add_of_le ltm_nez' h',
                leading_monomial_of_mul_m_right h_sfp.left hb, ←leading_monomial_eq a hb]
        }, {
            have h' :  leading_monomial (p * monomial a b) ≤ leading_monomial (p * f),
                rw [hfp (and.intro h_sfp.left hf), leading_monomial_of_mul_m_right h_sfp.left hb, leading_monomial_eq a hb],
                apply add_le_add_left (le_of_not_le h),
            rw add_comm at ltm_nez ltm_nez',
            rw [add_comm (monomial a b) f, mul_add, leading_monomial_of_add_of_le ltm_nez (le_of_not_le h), 
                leading_monomial_of_add_of_le ltm_nez' h', hfp (and.intro h_sfp.left hf)]
        },
    end
end

lemma leading_monomial_lt_of_mul (p q : mv_polynomial σ α) (hp : p ≠ 0) :
    (p * q).leading_monomial ≥ q.leading_monomial :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    by_cases hq : q = 0, 
    rw [leading_monomial_zero_of_zero hq, _inst_4.zero_bot], 
    apply _inst_3.bot_le,
    rw [leading_monomial_of_mul (and.intro hp hq)],
    apply le_add_of_nonneg_left, rw _inst_4.zero_bot, apply _inst_3.bot_le,
end


lemma mv_mul_ne_zero {p q : mv_polynomial σ α} : p ≠ 0 → q ≠ 0 → p * q ≠ 0 := 
λ hp hq, begin
    cases (mv_trichotomy p) with _ hp', finish,
    cases (mv_trichotomy q) with _ hq', finish,
    cases hp', rw [hp'.2.2, C], apply mv_mul_m_ne_zero' hq hp'.2.1,
    intro h,
    have h' := leading_monomial_zero_of_zero h,
    rw [leading_monomial_of_mul (and.intro hp hq), finsupp.nat.add_eqz_iff] at h',
    apply hp' (leading_monomial_eqz_const h'.left),
end

lemma last_monomial_of_mul_m_left {p : mv_polynomial σ α} {a : σ →₀ ℕ} {b : α} (hp : p ≠ 0) (hb : b ≠ 0) :
last_monomial' _ (mv_mul_ne_zero (monomial_ne_zero_lem a hb) hp) =
    a + (last_monomial' _ hp) :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    revert hp,
    apply finsupp.induction p, finish,
    intros a' b' f haf' hb' ih h_sf',
    have H : finsupp.single a' b' = monomial a' b', finish [monomial],
    simp [-add_comm, H] at h_sf' ⊢,
    by_cases hf : f = 0,
    simp [hf, last_monomial'_of_monomial hb', monomial_mul, last_monomial'_of_monomial (mul_ne_zero hb hb')],
    have hmab := monomial_ne_zero_lem a hb, 
    have hmab' := monomial_ne_zero_lem a' hb', 
    have hmmab' := mv_mul_ne_zero hmab hmab',
    have hmmabf := mv_mul_ne_zero hmab hf,
    have h := last_term_add_nez_of_not_mem f haf' hb' hf,
    have h' : last_term _ hmmab' + 
        last_term _ hmmabf ≠ 0,
        intro h', unfold last_term at h',
        have h₁ : (monomial a b * monomial a' b').to_fun 
            (last_monomial' (monomial a b * monomial a' b') hmmab') ≠ 0,
            apply last_monomial'_apply,
        have h₂ := finsupp.single_add_eqz (not_and_of_not_left _ h₁) h',
            simp [monomial_mul] at h₂,
            rw [last_monomial'_of_monomial (mul_ne_zero hb hb'), ih hf, add_left_cancel_iff] at h₂,
            rw h₂ at haf', apply absurd (last_monomial'_mem hf) haf',
    have h_sf'' : monomial a b * monomial a' b' + monomial a b * f ≠ 0,
        rw [←left_distrib], apply mv_mul_ne_zero hmab h_sf',
    simp [-add_comm, mul_add],
    rw [←last_monomial_of_add hmab' hf h_sf' h,
        ←last_monomial_of_add hmmab' hmmabf h_sf'' h'],
    simp [monomial_mul, ih hf, last_monomial'_of_monomial (mul_ne_zero hb hb'), last_monomial'_of_monomial hb', min],
    by_cases h_le : a' ≤ last_monomial' f hf;
    simp [h_le],
end

lemma last_monomial_of_mul_m_right {p : mv_polynomial σ α} (a : σ →₀ ℕ) {b : α} (hp : p ≠ 0) (hb : b ≠ 0) :
last_monomial' _ (mv_mul_ne_zero hp (monomial_ne_zero_lem a hb)) =
    (last_monomial' _ hp) + a :=
begin
    simp [mul_comm p (monomial a b), add_comm],
    apply last_monomial_of_mul_m_left hp hb,
end

lemma last_monomial_of_mul {p q : mv_polynomial σ α} (hp : p ≠ 0) (hq : q ≠ 0) :
last_monomial' _ (mv_mul_ne_zero hp hq) = (last_monomial' _ hp) + (last_monomial' _ hq) :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    revert hq, apply finsupp.induction q, finish,
    intros a b f haf hb ih h_sf,
    have H : finsupp.single a b = monomial a b, finish [monomial],
    simp [-add_comm, H] at h_sf ⊢,
    have hmab := monomial_ne_zero_lem a hb, 
    by_cases hf : f = 0,
    simp [hf, last_monomial'_of_monomial hb, -add_comm],
    apply last_monomial_of_mul_m_right a hp hb,
    have h := last_term_add_nez_of_not_mem f haf hb hf,
    have h' : last_term _ (mv_mul_ne_zero hp hmab) + last_term _ (mv_mul_ne_zero hp hf) ≠ 0,
        intro h', simp [last_term] at h',
        have h'₁ : (p * f).to_fun (last_monomial' (p * f) (mv_mul_ne_zero hp hf)) ≠ 0,
            apply last_monomial'_apply,
        have h'₂ := finsupp.single_add_eqz (not_and_of_not_left _ h'₁) h',
        simp [ih hf, last_monomial_of_mul_m_right a hp hb, -add_comm] at h'₂,
        rw ←h'₂ at haf, apply absurd (last_monomial'_mem hf) haf,
    have h_sf' : (p * (monomial a b)) + (p * f) ≠ 0,
        rw [←left_distrib], apply mv_mul_ne_zero hp h_sf,
    simp [-add_comm, mul_add],
    rw [←last_monomial_of_add hmab hf h_sf h,
        ←last_monomial_of_add (mv_mul_ne_zero hp hmab) (mv_mul_ne_zero hp hf) h_sf' h'],
    simp [ih hf, last_monomial_of_mul_m_right a hp hb, last_monomial'_of_monomial hb, min, -add_comm],
    by_cases h_le : a ≤ last_monomial' _ hf;
    simp [h_le],
end

lemma last_monomial_lt_ideal_of_lt_finset (x : mv_polynomial σ α) (s : finset (mv_polynomial σ α))
    (hx₁ : x ≠ 0) (hx₂ : ∃ xs xa, x = monomial xs xa) (hs₁ : s ≠ ∅) 
    (hs₂ : ∀ (p : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : p ∈ s), ∃ ps pa, p = monomial ps pa ∧ last_monomial' p h₁ > last_monomial' x hx₁) : 
    ∀ (p : mv_polynomial σ α) (h : p ≠ 0), p ∈ ideal.span (↑s : set (mv_polynomial σ α)) → last_monomial' p h > last_monomial' x hx₁ :=
begin
    letI := @finsupp.nat.decidable_linear_ordered_cancel_comm_monoid σ _ _ _ _ _,
    revert hs₁ hs₂,
    apply finset.case_strong_induction_on s, simp,
    intros a s a_nm ih hs₁' hs₂' p hp₁ hp₂,
    rw [finset.coe_insert, ideal.mem_span_insert] at hp₂,
    cases hp₂ with a' hp, cases hp with z hp, cases hp with hzs hp,
    by_cases ha : a = 0; by_cases hz : z = 0, finish,
    any_goals {by_cases hs : s = ∅, simp [hs, ideal.span] at hzs, apply absurd hzs hz},
    any_goals {have hzgt := ih s (by refl) hs (λ a ha₁ ha₂, hs₂' a ha₁ (finset.mem_insert_of_mem ha₂)) z hz hzs,},
    simp [hp, ha], assumption,
    all_goals {
        have hagt := hs₂' a ha (finset.mem_insert_self a s), cases hagt with as hagt, cases hagt with aa hagt,
        by_cases ha' : a' = 0,
    },
    simp [ha', hz] at hp, apply absurd hp hp₁,
    any_goals {
        have ha'a : last_monomial' (a' * a) (mv_mul_ne_zero ha' ha) > last_monomial' x hx₁,
        simp [last_monomial_of_mul ha' ha],
        apply lt_of_lt_of_le hagt.right, apply le_add_of_nonneg_right, 
        rw _inst_4.zero_bot, apply _inst_3.bot_le,
    },
    finish,
    finish,
    simp [hp] at hp₁ ⊢,
    apply lt_of_lt_of_le _ (last_monomial_of_add_le' hz (mv_mul_ne_zero ha' ha) hp₁),
    by_cases h : last_monomial' _ hz ≤ last_monomial' _ (mv_mul_ne_zero ha' ha);
    simp [min, h]; assumption,
end

lemma last_monomial_lt_not_mem_ideal (x : mv_polynomial σ α) (s : finset (mv_polynomial σ α))
    (hx₁ : x ≠ 0) (hx₂ : ∃ xs xa, x = monomial xs xa) (hs₁ : s ≠ ∅) 
    (hs₂ : ∀ (p : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : p ∈ s), ∃ ps pa, p = monomial ps pa ∧ last_monomial' p h₁ > last_monomial' x hx₁) : 
    x ∉ ideal.span (↑s : set (mv_polynomial σ α)) :=
λ hx, by apply absurd (le_of_eq (by refl)) (not_le_of_gt $ last_monomial_lt_ideal_of_lt_finset x s hx₁ hx₂ hs₁ hs₂ x hx₁ hx)

lemma mem_mul_support (p c a : mv_polynomial σ α) (hp : p ≠ 0 ∧ ∃ ps pa, monomial ps pa = p)
(hp_sub : p.support ⊆ (c * a).support) (ha : a ≠ 0 ∧ ∃ as aa, monomial as aa = a) : 
∀ x, p.leading_monomial x ≥ a.leading_monomial x :=
begin
    rcases hp with ⟨hp₁, ⟨ps, ⟨pa, hp₂⟩⟩⟩,
    rcases ha with ⟨ha₁, ⟨as, ⟨aa, ha₂⟩⟩⟩,
    have haa : aa ≠ 0, intro haa, simp [haa, monomial] at ha₂, exact ha₁ ha₂.symm,
    have hpa : pa ≠ 0, intro hpa, simp [hpa, monomial] at hp₂, exact hp₁ hp₂.symm,
    simp [finsupp.coe_f, hp₂.symm, ha₂.symm, leading_monomial, monomial, finsupp.single, haa, hpa],
    rw [←(finset.singleton_eq_singleton ps), ←(finset.singleton_eq_singleton as), finset.sup_singleton, finset.sup_singleton],
    simp [ha₂.symm] at hp_sub ⊢,
    simp [monomial, finsupp.single, hpa] at hp₂,
    simp [has_mul.mul, monomial, finsupp.single_sum' as haa] at hp_sub,
    simp [finsupp.sum, finset.sum_eq_fold, hp₂.symm] at hp_sub,
    have hp_sub' := finset.subset.trans hp_sub (add_support_subset_union c as haa),
    rcases finset.mem_fold_union hp_sub' with ⟨b, ⟨hb, h⟩⟩,
    have h_mul_nez : mul_zero_class.mul (c.to_fun b) aa ≠ 0,
        apply mul_ne_zero _ haa,
        rw ←finsupp.coe_f, exact finsupp.mem_support_iff.1 hb,
    simp [finsupp.single, h_mul_nez, finset.subset_iff] at h,
    intro x,
    rw [h, ←finsupp.coe_f, ←finsupp.coe_f],
    simp, 
    apply nat.le_add_right,
end

lemma monomial_mem_ideal : ∀ (s : finset (mv_polynomial σ α)) 
(hs₁ : s ≠ ∅) (hs₂ : ∀ (p : mv_polynomial σ α) (h₁ : p ∈ s), p ≠ 0 ∧ ∃ ps pa, monomial ps pa = p),
∀ (p : mv_polynomial σ α) (hp : p ∈ ideal.span (↑s : set (mv_polynomial σ α))), (p ≠ 0 ∧ ∃ ps pa, monomial ps pa = p) → 
    ∃ (q : mv_polynomial σ α) (hq : q ∈ s), ∀ x, q.leading_monomial x ≤ p.leading_monomial x :=
λ s, begin
    apply finset.case_strong_induction_on s, finish,
    intros a s has ih hias hs' p hp₁ hp₂,
    by_cases hs : s = ∅,
    {
        apply exists.intro a, simp [hs, finset.insert_eq, ideal.mem_span_singleton'] at *,
        rcases hs' with ⟨ha₁, ⟨as, ⟨aa, ha₂⟩⟩⟩,
        cases hp₁ with a' hp₁,
        have ha' : a' ≠ 0, intro ha', simp [ha'] at hp₁, apply hp₂.left hp₁.symm,
        rw [←hp₁, leading_monomial_of_mul (and.intro ha' ha₁)],
        simp,
    },
    let hp₂' := hp₂,
    rcases hp₂ with ⟨hp₂, ⟨ps, ⟨pa, hp₃⟩⟩⟩,
    have hpa : pa ≠ 0, intro hpa', simp [hpa', monomial] at hp₃, exact hp₂ hp₃.symm,
    have hp₄ : p.support = {ps},
        simp [hp₃.symm, monomial, finsupp.single, hpa],
    rcases support_subset_of_linear_combination_union (insert a s) hias p hp₁ with ⟨c, ⟨hc, h⟩⟩,
    rw [hp₄] at h,
    rcases finset.mem_fold_union h with ⟨q, ⟨hq, h'⟩⟩,
    apply exists.intro q, apply exists.intro hq,
    have hq' := hs' q hq,
    apply mem_mul_support p (c.to_fun q) q hp₂' _ hq',
    simp [hp₄], apply h',
end

end integral_domain

section gcd_domain
variables [gcd_domain α] 

def leading_term_lcm (p q : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : q ≠ 0) : mv_polynomial σ α := 
    if mv_is_const p 
    then monomial q.leading_monomial (lcm p.leading_coeff q.leading_coeff)
    else if mv_is_const q
        then monomial p.leading_monomial (lcm p.leading_coeff q.leading_coeff)
        else 
            let supp := finsupp.zip_with max (max_self 0) p.leading_monomial q.leading_monomial in
            monomial supp (lcm p.leading_coeff q.leading_coeff)

lemma leading_term_lcm_comm (p q :mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : q ≠ 0) : leading_term_lcm p q h₁ h₂ = leading_term_lcm q p h₂ h₁ :=
begin
    by_cases hp : mv_is_const p;
    by_cases hq : mv_is_const q,
    any_goals {
        simp [leading_term_lcm, hp, hq], rw lcm_comm, 
        try {rw [leading_monomial_eqz_of_const hp, leading_monomial_eqz_of_const hq],}
    },
    have h : finsupp.zip_with max leading_term_lcm._proof_1 p.leading_monomial q.leading_monomial
        = finsupp.zip_with max leading_term_lcm._proof_1 q.leading_monomial p.leading_monomial,
        apply finsupp.ext, finish [max_comm],
    finish [h],
end

lemma leading_monomial_le_of_lcm_left [fintype σ]
    (p q : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : q ≠ 0) : 
    leading_monomial_le p.leading_term (leading_term_lcm p q h₁ h₂) := 
begin
    rw ←@not_zero_iff_leading_coeff_not_zero σ α _ _ _ _ _ _ _ p at h₁,
    rw ←@not_zero_iff_leading_coeff_not_zero σ α _ _ _ _ _ _ _ q at h₂,
    have h : lcm (leading_coeff p) (leading_coeff q) ≠ 0, intro h',
        rw lcm_eq_zero_iff at h', cases h', apply h₁ h', apply h₂ h', 
    have H : p.leading_monomial = p.leading_term.leading_monomial,
        unfold leading_term,
        change p.leading_monomial = leading_monomial (monomial p.leading_monomial p.leading_coeff),
        rw ←leading_monomial_eq p.leading_monomial h₁,
 
    by_cases hp : mv_is_const p;
    by_cases hq : mv_is_const q,
    any_goals {simp [leading_term_lcm, hp, hq, leading_monomial_le, finsupp.leading_monomial_le, fintype.fintype_fold_and_iff], 
        intro x, rw ←H, try { rw [leading_monomial_eqz_of_const hp], simp},
    },

    rw ←leading_monomial_eq p.leading_monomial h,
    rw ←leading_monomial_eq (finsupp.zip_with max leading_term_lcm._proof_1 p.leading_monomial q.leading_monomial) h,
    simp, apply le_max_left,
end

lemma leading_monomial_le_of_lcm_right [fintype σ] (p q : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : q ≠ 0) : 
    leading_monomial_le q.leading_term (leading_term_lcm p q h₁ h₂) := 
by rw leading_term_lcm_comm p q h₁ h₂; apply leading_monomial_le_of_lcm_left

end gcd_domain
end semilattice_decidable_linear_order
end general

namespace fin_n
variables {n : ℕ}

variables [discrete_field α] (lt_wellfounded: @well_founded (fin n →₀ ℕ) (<)) [bot_zero (fin n) ℕ]


def leading_term_sub' {n} (a b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_monomial_le b a) : fin n →₀ ℕ
     := finsupp.fin_n.leading_term_sub a.leading_monomial b.leading_monomial h

lemma sub_support: Π (a b: mv_polynomial (fin n) α), (a - b).support ⊆ a.support ∪ b.support :=
λ a b,
begin
    unfold has_sub.sub algebra.sub, 
    have m := @finsupp.support_add _ _ _ _ _ a (-b),
    rw finsupp.support_neg at m, assumption,
end

lemma sub_dec : Π (a b : mv_polynomial (fin n) α),
    a.leading_term = b.leading_term 
    → a.leading_monomial ≠ 0
→ (a - b).leading_monomial < a.leading_monomial :=
λ a b hab ha, begin
    unfold leading_term at hab,
    have h₁ := finsupp.single_inj1 (leading_monomial_ne_zero_coeff ha) hab,
    have h₂ := finsupp.single_inj2 hab,
    unfold leading_coeff leading_monomial at *,
    have h₃ : finset.sup (a.support ∪ b.support) id = finset.sup a.support id, simp [finset.sup_union, h₁],
    rw [lt_iff_le_and_ne, sub_eq_add_neg, ←h₃], apply and.intro,
    apply finset.sub_sup, rw [←@finsupp.support_neg _ _ _ _ _ b], apply finsupp.support_add,
    rw h₃, intro h,
    from if H : (a - b).support = ∅ 
    then begin 
        rw [←sub_eq_add_neg, H, finset.sup_empty, ←_inst_2.zero_bot] at h,
        exact ha h.symm,
    end 
    else begin
        apply absurd (finset.mem_of_sup_id H),
        apply finsupp.not_mem_support_iff.2, rw [finsupp.sub_apply, sub_eq_add_neg a b, h, finsupp.coe_f, h₂, ←h₁], apply sub_self,
    end
end


lemma sup_mul : ∀ (a b : mv_polynomial (fin n) α),
    a ≠ 0 → b ≠ 0 →
    (finset.sup (a * b).support id) = 
    finset.sup a.support id + finset.sup b.support id :=
λ a b p₁ p₂, begin
    apply @leading_monomial_of_mul _ _ _ _ _ _ _ _ _ _;
    try {apply_instance}, swap,
    letI := (@finsupp.fin_n.decidable_monomial_order n).mono_order,
    letI : is_monomial_order (fin n →₀ ℕ) (≤);
            repeat { constructor <|> apply_instance <|> assumption },
    finish,
end

lemma sup_add : ∀ (a b : mv_polynomial (fin n) α),
    disjoint a.support b.support → 
    (finset.sup (a + b).support id) = finset.sup a.support id ⊔ finset.sup b.support id :=
λ a b p₁, begin
    rw [finsupp.support_add_eq p₁, finset.sup_union],
end

lemma sup_single : ∀ {b : mv_polynomial (fin n) α} c d,
    b ≠ 0 → finsupp.single c d ≠ 0 → d ≠ 0 →
    (finset.sup ((b * finsupp.single c d).support) id) = 
        (finset.sup b.support id) + c :=
begin
    intros, rw [sup_mul, finsupp.single_support, finset.sup_singleton]; try {assumption},
    simp,
end

lemma coeff_single : ∀ {a : mv_polynomial (fin n) α} b c,
    (leading_coeff (a * finsupp.single b c)) = a.leading_coeff * c :=
begin
    intro a,
    haveI : is_monomial_order ((fin n) →₀ ℕ) (≤) :=
    by constructor; apply finsupp.fin_n.decidable_monomial_order.mono_order,
    letI : ring ((fin n →₀ ℕ) →₀ α) := mv_polynomial.ring,

    apply finsupp.induction a; intros,
    begin
        rw @ring.zero_mul _ _inst_3,
        change 0 = 0 * c,
        rw ring.zero_mul,
    end,
    begin
        rw right_distrib,
        unfold leading_coeff leading_monomial,
        by_cases ceq: c = 0,
        begin
            simp [ceq],
            apply @eq.subst _ (λ x, (x + finsupp.single a_1 b * 0).to_fun (finset.sup 
                    ((x + finsupp.single a_1 b * 0).support) id) = 0) _ _ (ring.mul_zero f).symm,
            apply @eq.subst _ (λ (x : mv_polynomial (fin n) α), (0 + x).to_fun 
                    (finset.sup ((0 + x).support) id) = 0) _ _ (ring.mul_zero (finsupp.single a_1 b)).symm,
            apply @eq.subst _ (λ (x : mv_polynomial (fin n) α), x.to_fun (finset.sup (x.support) id) = 0) _ _ (ring.add_zero 0).symm,
            apply @finsupp.zero_apply (fin n →₀ ℕ) α _ 0,
        end,
        begin
            rwcs [finsupp.add_apply, sup_add],
            by_cases a_1 ≤ f.support.sup id,
            begin
                by_cases h': f = 0,
                begin
                    rw [h', @ring.zero_mul _ _inst_3],
                    rwcs [finsupp.zero_apply, finsupp.single_mul_single, finsupp.single_apply, finsupp.single_support,
                            finset.sup_singleton, finsupp.single_apply, finsupp.single_support, finset.sup_singleton];
                    simp *,                    
                end,
                begin
                    unfold leading_coeff leading_monomial at a_4,
                    have h'' := (finsupp.support_ne_empty f).1 h',
                    have mem_sup := finset.mem_of_sup_id h'',

                    rwcs [lattice.sup_of_le_right, finsupp.add_apply, 
                            a_4, sup_add, lattice.sup_of_le_left, finsupp.single_mul_single, 
                            finsupp.single_apply, logic.ite_false', finsupp.single_apply,
                            logic.ite_false']; try {assumption},
                    begin
                        intro,
                        exact a_2 (a_5.symm ▸ mem_sup),
                    end,
                    begin
                        change ¬a_1 + b_1 = ((f * monomial b_1 c) : mv_polynomial (fin n) α).leading_monomial,
                        rw @leading_monomial_of_mul_m_right _ _ _ _ _ _ _ _ _ _; try {assumption}; try {apply_instance},
                        begin
                            intro,
                            rw finsupp.nat.add_right_cancel at a_5,
                            unfold leading_monomial at a_5,
                            exact a_2 (a_5.symm ▸ mem_sup),
                        end,
                    end,
                    begin
                        rw [finsupp.single_support, finset.sup_singleton];
                        assumption,
                    end,
                    begin
                        rw [disjoint, finsupp.single_support, finset.singleton_non_mem_inter_empty]; simp *,
                    end,
                    begin
                        change ((finsupp.single a_1 b * finsupp.single b_1 c) : mv_polynomial (fin n) α).support.sup id ≤
                            ((f * monomial b_1 c) : mv_polynomial (fin n) α).leading_monomial,
                        rw [finsupp.single_mul_single, @leading_monomial_of_mul_m_right _ _ _ _ _ _ _ _ _ _, 
                            finsupp.single_support, finset.sup_singleton, id]; try {assumption}; try {apply_instance},
                        apply finsupp.fin_n.decidable_monomial_order.mono_order; assumption,
                        simp [a_3, ceq],
                    end,
                end,
            end,
            begin
                replace h := le_of_not_le h,
                by_cases h': f = 0,
                begin
                    rw [h', @ring.zero_mul _ _inst_3],
                    rwcs [finsupp.zero_apply, finsupp.single_mul_single, finsupp.single_apply, finsupp.single_support,
                            finset.sup_singleton, finsupp.single_apply, finsupp.single_support, finset.sup_singleton];
                    simp *, 
                end,
                begin
                    unfold leading_coeff leading_monomial at a_4,
                    have h'' := (finsupp.support_ne_empty f).1 h',
                    have mem_sup := finset.mem_of_sup_id h'',

                    rwcs [lattice.sup_of_le_left, finsupp.add_apply, finsupp.single_mul_single,
                            finsupp.single_apply, sup_add, lattice.sup_of_le_right, finsupp.single_apply,
                            finsupp.single_support, finset.sup_singleton, finsupp.single_support, finset.sup_singleton]; 
                            try { simp [*, finsupp.single_support, finset.sup_singleton] };
                            try { assumption }, 
                    rw [ring.right_distrib],
                    apply congr_arg (λ x, b * c + x),
                    rwcs [finsupp.not_mem_support_iff.1], symmetry,
                    apply mul_eq_zero_iff_eq_zero_or_eq_zero.2, left,
                    apply finsupp.not_mem_support_iff.1 a_2,
                    intro, rw [←(@support_of_mul_single_iff _ _ _ _ _ _ _ _ _ _)] at a_5; try {apply_instance}; try {assumption},
                    exact a_2 a_5,
                    rw [←finset.singleton_eq_singleton, finset.sup_singleton], assumption,
                    change ((f * monomial b_1 c) : mv_polynomial (fin n) α).leading_monomial ≤
                        finset.sup ((finsupp.single a_1 b * finsupp.single b_1 c).support) id,
                    rw @leading_monomial_of_mul_m_right _ _ _ _ _ _ _ _ _ _; try {assumption}; try {apply_instance},
                    rw [finsupp.single_mul_single, finsupp.single_support, finset.sup_singleton],
                    apply finsupp.fin_n.decidable_monomial_order.mono_order, assumption,
                    simp [a_3, ceq],
                end,
            end,
            begin
                by_cases f = 0,
                begin
                    rw h at *,
                    rw [finsupp.single_mul_single, finsupp.single_support, disjoint, finset.singleton_non_mem_inter_empty'],
                    simp,
                    apply @eq.subst _ (λ x : mv_polynomial (fin n) α, a_1 + b_1 ∉ x.support) _ _ (@ring.zero_mul _ _inst_3 (finsupp.single b_1 c)).symm,
                    simp, simp *,
                end,
                begin
                    rw [finsupp.single_mul_single, disjoint, finsupp.single_support, finset.singleton_non_mem_inter_empty'],
                    any_goals { by simp * },
                    intro, rw [←(@support_of_mul_single_iff _ _ _ _ _ _ _ _ _ _)] at a_5; try {apply_instance}; try {assumption},
                    exact a_2 a_5,
                end,
            end,
        end,
    end,
end

lemma sup_eq' : ∀ (a : fin n →₀ ℕ) (b: mv_polynomial (fin n) α) h,
    a = finset.sup (b.support) id + 
        finsupp.fin_n.leading_term_sub a (finset.sup (b.support) id) h :=
λ a b h, begin
    revert a,
    apply finsupp.induction b; intros,
    begin
        simp [_inst_2.zero_bot.symm],
        symmetry, 
        have := finsupp.fin_n.leading_term_sub_lem a 0 h,
        simp at this, apply this,
    end,
    begin
        revert h,
        rw [finsupp.support_add_eq, finset.sup_union, finsupp.single_support, finset.sup_singleton]; try {assumption},
        change ∀ (h : finsupp.leading_monomial_le (a ⊔ finset.sup (f.support) id) a_4),
            a_4 = a ⊔ finset.sup (f.support) id + finsupp.fin_n.leading_term_sub a_4 (a ⊔ finset.sup (f.support) id) h,
        by_cases a ≤ finset.sup (f.support) id,
        begin
            rw lattice.sup_of_le_right; intros,
            apply a_3, assumption,
        end,
        begin
            rw not_le at h,
            rw lattice.sup_of_le_left; intros,
            begin
                symmetry, rw [add_comm],
                apply finsupp.fin_n.leading_term_sub_lem,
            end,
            begin
                apply le_of_lt,
                assumption,
            end,
        end,
        begin
            unfold disjoint,
            rw [finsupp.single_support, finset.singleton_non_mem_inter_empty'],
            finish, assumption, assumption,
        end,
    end,
end

lemma sup_eq : ∀ {a b: mv_polynomial (fin n) α} {hab},
    finset.sup (a.support) id = 
    leading_term_sub' a b hab + finset.sup (b.support) id :=
begin
    intro a,
    apply finsupp.induction a; intros,
    begin
        have : b.leading_monomial = 0,
        from finsupp.fin_n.leading_monomial_le_antisymm hab 
            (finsupp.fin_n.leading_monomial_le_zero _),
        revert hab, have this' := this,
        unfold leading_monomial at this, rw this, intro hab,
        simp [_inst_2.zero_bot.symm], symmetry, apply leading_term_sub'_zero,
    end,
    begin
        simp,
        unfold leading_term_sub' leading_monomial,
        have : ∀ h, finset.sup ((f + finsupp.single a_1 b).support) id =
            finset.sup (b_1.support) id + finsupp.fin_n.leading_term_sub (finset.sup ((f + finsupp.single a_1 b).support) id) (finset.sup (b_1.support) id)
                h,
            rw [finsupp.support_add_eq, finset.sup_union],
            by_cases sup_le: finset.sup (f.support) id ≤ finset.sup ((finsupp.single a_1 b).support) id,
            begin
                rw lattice.sup_of_le_right sup_le,
                intros, revert h, rw [finsupp.single_support, finset.sup_singleton], intro,
                apply sup_eq', assumption,
            end,
            begin
                rw lattice.sup_of_le_left,
                intros, rw add_comm,
                apply a_4, rw not_le at sup_le,
                apply le_of_lt, assumption,
            end,
        begin
            unfold disjoint,
            rw [finsupp.single_support a_3, finset.singleton_non_mem_inter_empty];
            simp [a_2],
        end,
        begin
            apply this,
        end,
    end,
end

lemma leading_term_eq {a b : mv_polynomial (fin n) α} (ha : a ≠ 0) (hb : b ≠ 0) (hab : leading_monomial_le b a) : 
    a.leading_term = leading_term (b * finsupp.single (leading_term_sub' a b hab) 
                (a.leading_coeff / b.leading_coeff)) :=
begin
    unfold leading_term leading_monomial,
    have := @sup_single _ _ _ _ b (leading_term_sub' a b hab) (leading_coeff a / leading_coeff b) _ _ _,
    rw this,
    simp [coeff_single, has_div.div, algebra.div],
    apply finsupp.single_ext,
    by apply sup_eq,
    begin
        rw ←@not_zero_iff_leading_coeff_not_zero _ _ _ _ _ _ _ _ _ at hb; try {apply_instance},
        rw [mul_comm (leading_coeff a), ←mul_assoc, discrete_field.mul_inv_cancel],
        by simp, assumption,
    end,
    by assumption,
    all_goals {
        rw ←@not_zero_iff_leading_coeff_not_zero _ _ _ _ _ _ _ _ _ at ha hb; try {apply_instance},
    },
    rw finsupp.single_neqz,
    all_goals {
        apply division_ring.mul_ne_zero ha,
        apply inv_ne_zero, assumption,
    },
end

end fin_n

end mv_polynomial
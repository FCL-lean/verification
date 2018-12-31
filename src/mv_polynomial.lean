import linear_algebra.multivariate_polynomial
import finsupp
import finset
import fintype
import fin
import noetherian
import seq
import bot_zero
import field
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
    := finsupp.single a.leading_monomial a.leading_coeff

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

lemma leading_monomial_eq_zero_of_const {p : mv_polynomial σ α} (h : mv_is_const p) : p.leading_monomial = 0 :=
begin
    have h' := eq_mv_is_const h,
    cases h', by_cases h'_fst = (0 : α),
    finish [leading_monomial_zero_of_zero],
    simp [h'_snd, leading_monomial, @const_support_zero σ _ _ _ _ _ _ _ h],
    apply finset.sup_singleton,
end 

lemma support_ne_empty_of_leading_term {a b : mv_polynomial σ α} : a.leading_monomial ≠ ⊥ 
    → a.leading_monomial = b.leading_monomial 
    → b.support ≠ ∅ := 
λ ha hab, begin
    rw hab at ha, intro h,
    apply absurd (support_empty h) ha,
end

lemma support_ne_empty_of_leading_term' {a : mv_polynomial σ α} : 
    a.leading_monomial ≠ ⊥
    → a.support ≠ ∅ := 
begin
    intros neqz neqz2,
    apply absurd (support_empty neqz2) neqz,
end

section is_total
variables [is_total (σ →₀ ℕ) has_le.le] [@decidable_rel (σ →₀ ℕ) has_le.le]

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


/-
lemma last_monomial_of_add_le (p q : mv_polynomial σ α) (hpq : p ≠ 0 ∧ q ≠ 0 ∧ p + q ≠ 0) : 
    option.rel (≤) (option.lift_or_get min p.last_monomial q.last_monomial) (p + q).last_monomial :=
begin
    cases (last_monomial_some_iff_nez.1 hpq.left) with px hp',
    cases (last_monomial_some_iff_nez.1 hpq.right.left) with qx hq',
    cases (last_monomial_some_iff_nez.1 hpq.right.right) with pqx hpq',
    cases (finset.min_of_ne_empty (finset.ne_empty_union.1 (not_and_of_not_left (q.support = ∅) ((finsupp.support_ne_empty p).1 hpq.left)))) with pqx' hpq'',
    have h := finset.le_min_of_mem (finset.mem_of_subset finsupp.support_add (finset.mem_of_min hpq')) hpq'',
    rw finset.union_min at hpq'',
    simp [last_monomial] at *,
    rw [hp', hq', option.lift_or_get] at *, rw hpq', apply option.rel.some, 
    simp at hpq'',
    finish,
end-/

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
    apply neqz, rw _inst_5.zero_bot,
end

lemma ne_zero_of_leading_monomial_ne_zero (a : mv_polynomial σ α) : 
    a.leading_monomial ≠ 0 → a ≠ 0 := λ h, by exact not_zero_iff_leading_coeff_not_zero.1 (leading_monomial_ne_zero_coeff h)

lemma leading_monomial_eqz_iff_leading_term_const {p : mv_polynomial σ α} : 
    mv_is_const p.leading_term ↔ p.leading_monomial = ⊥ :=
begin
    apply iff.intro; intro h,
    rw ←_inst_5.zero_bot,
    have h' := eq_mv_is_const h,
    unfold leading_term C monomial at h', {
        from if hpcz :p.leading_coeff = 0
        then 
            begin 
                simp [zero_iff_leading_coeff_zero] at hpcz, simp [leading_monomial, hpcz, _inst_5.zero_bot], 
                change finset.sup ∅ id = ⊥, exact finset.sup_empty,
            end
        else by apply finsupp.single_inj1 hpcz h'.2
    },
    rw [←_inst_5.zero_bot] at h,
    simp [leading_term, h],
    change mv_is_const (C p.leading_coeff),
    apply eq_mv_is_const',
    apply psigma.mk p.leading_coeff,
    refl,
end

lemma leading_monomial_eq_zero_of_const' {p : mv_polynomial σ α} (h : p.leading_monomial = 0) : mv_is_const p :=
begin 
    rw [_inst_5.zero_bot, leading_monomial] at h,
    have h' : p.support = ∅ ∨ p.support = {⊥}, from finset.sup_bot p.support h,
    cases h', rw finsupp.support_eq_empty at h', simp [h'],
    rw [←_inst_5.zero_bot] at h', 
    apply eq_mv_is_const', apply psigma.mk (p.to_fun 0),
    apply finsupp.ext, intro x,
    simp [finsupp.coe_f, C, monomial, finsupp.single],
    by_cases hx: 0 = x; simp [hx],
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff, h'],
    finish [finset.not_mem_singleton],
end

def leading_monomial_eqz_const {p : mv_polynomial σ α}:
    p.leading_monomial = 0 → Σ' (a : α), p = C a :=
λ h,
begin 
    rw [_inst_5.zero_bot, leading_monomial] at h,
    have h' : p.support = ∅ ∨ p.support = {⊥}, from finset.sup_bot p.support h,
    rw [←_inst_5.zero_bot] at h', 
    apply psigma.mk (p.to_fun 0),
    cases h', rw finsupp.support_eq_empty at h', rw [←finsupp.coe_f, h'], finish, 
    apply finsupp.ext, intro x,
    simp [finsupp.coe_f, C, monomial, finsupp.single],
    by_cases hx: 0 = x; simp [hx],
    rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff, h'],
    finish [finset.not_mem_singleton],
end

lemma const_of_support_singleton {p : mv_polynomial σ α} (h : p.support = {0}) : Σ' a : α, p = C a :=
begin
    apply psigma.mk (p.to_fun 0), unfold C monomial finsupp.single,
    apply finsupp.ext, intro a,
    from if ha : a = 0
    then by simp [finsupp.coe_f, ha.symm]
    else begin 
        rw [←ne.def] at ha,
        simp [finsupp.coe_f, ne.symm ha],
        rw [←finsupp.coe_f, ←finsupp.not_mem_support_iff, h],
        apply finset.not_mem_singleton.2 ha,
    end
end


lemma leading_monomial_lt_right_of_add {a b : mv_polynomial σ α} (h : a.leading_term + b.leading_term ≠ 0) :
    (a + b).leading_monomial ≥ b.leading_monomial :=
begin
    unfold leading_monomial leading_term at *,
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
            have hx : x.support ≠ ∅, intro hx, simp [hx] at hxy, apply absurd hxy, apply not_lt_of_le, apply _inst_4.bot_le,
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
    unfold leading_term leading_monomial leading_coeff at *,
    have H₁ : ∀ {x y : mv_polynomial σ α}, x.support.sup id > y.support.sup id → x.support.sup id ≤ (x + y).support.sup id,
        intros x y hxy,
        have hx : x.support ≠ ∅, intro hx, simp [hx] at hxy, apply absurd hxy, apply not_lt_of_le, apply _inst_4.bot_le,
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

end is_total

section fintype_s
variable [fins: fintype σ]
include fins

def leading_term_le (a b: mv_polynomial σ α): Prop
    := finsupp.leading_term_le a.leading_monomial b.leading_monomial

instance leading_term_le_dec (a b: mv_polynomial σ α): decidable (leading_term_le a b) :=
begin
    unfold leading_term_le finsupp.leading_term_le,
    apply fintype.fintype_fold_dec,
    intro, apply_instance,
end

lemma leading_monomial_zero_of_le_zero {a b : mv_polynomial σ α} : a.leading_monomial = 0
     → leading_term_le b a → b.leading_monomial = 0 := 
λ ha hba, begin
    simp [leading_term_le, finsupp.leading_term_le, ha, fintype.fintype_fold_and_iff] at hba,
    apply finsupp.ext, simp [hba],
end


omit fins

end fintype_s
end semilattice

def leading_term_sub' {n} (a b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_term_le b a) : fin n →₀ ℕ
     := finsupp.fin_n.leading_term_sub a.leading_monomial b.leading_monomial h

@[simp]
def leading_term_sub'_zero {n} (b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_term_le b 0): leading_term_sub' 0 b h = 0 :=
begin
    have h': b.leading_monomial = 0,
    apply finsupp.fin_n.leading_term_le_antisymm,
    assumption, apply finsupp.fin_n.leading_term_le_zero,
    unfold leading_term_sub',
    unfold leading_term_le at h,
    revert h,
    change Π (h: finsupp.leading_term_le (leading_monomial b) (leading_monomial 0)),
        finsupp.fin_n.leading_term_sub (leading_monomial 0) (leading_monomial b) h = 0,
    rw [h', @leading_monomial_zero (fin n) α],
    intros, apply finsupp.fin_n.leading_term_sub_zero,
end

end comm_semiring

section integral_domain
variables [integral_domain α] [lattice.semilattice_sup_bot (σ →₀ ℕ)] [bot_zero σ ℕ] 
variables [is_total (σ →₀ ℕ) (≤)] [@decidable_rel (σ →₀ ℕ) has_le.le] [is_monomial_order (σ →₀ ℕ) has_le.le]

instance : decidable_linear_ordered_cancel_comm_monoid (σ →₀ ℕ) := {
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
    le_total := _inst_6.total,
    decidable_le := _inst_7,
    .._inst_4,
    ..@finsupp.add_comm_monoid σ ℕ _ _ _
}

lemma mul_m_leading_term_add_nez {p : mv_polynomial σ α} {a a' : σ →₀ ℕ} {b b' : α} (hp : p ≠ 0) (hb : b ≠ 0 ∧ b' ≠ 0)
(ih : p ≠ 0 → b' ≠ 0 → leading_monomial (monomial a' b' * p) = a' + p.leading_monomial)
(ha : a ∉ p.support) : leading_term ((monomial a' b') * (monomial a b)) + leading_term (monomial a' b' * p) ≠ 0 :=
begin
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
    unfold leading_term, intro h,
    have h' := finsupp.single_add_eqz (not_and_of_not_left _ (not_zero_iff_leading_coeff_not_zero.2 (mv_mul_m_ne_zero hp hb))) h,
    simp [-add_comm, ihp, ihm, add_left_cancel_iff] at h',
    rw h' at ha,
    apply absurd (finset.mem_of_sup_id (λ h, hq (finsupp.support_eq_empty.1 h))) ha,
end

lemma leading_monomial_of_mul {p q : mv_polynomial σ α} : (p ≠ 0 ∧ q ≠ 0)
→ (p * q).leading_monomial = p.leading_monomial + q.leading_monomial :=
begin
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
    by_cases hq : q = 0, 
    rw [leading_monomial_zero_of_zero hq, _inst_5.zero_bot], 
    apply _inst_4.bot_le,
    rw [leading_monomial_of_mul (and.intro hp hq)],
    apply le_add_of_nonneg_left, rw _inst_5.zero_bot, apply _inst_4.bot_le,
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
        rw _inst_5.zero_bot, apply _inst_4.bot_le,
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

end integral_domain

section gcd_domain
variables [gcd_domain α] [lattice.semilattice_sup_bot (σ →₀ ℕ)] [bot_zero σ ℕ] 

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
        try {rw [leading_monomial_eq_zero_of_const hp, leading_monomial_eq_zero_of_const hq],}
    },
    have h : finsupp.zip_with max leading_term_lcm._proof_1 p.leading_monomial q.leading_monomial
        = finsupp.zip_with max leading_term_lcm._proof_1 q.leading_monomial p.leading_monomial,
        apply finsupp.ext, finish [max_comm],
    finish [h],
end

section decidable_linear_order
variables [fintype σ] [is_total (σ →₀ ℕ) (≤)] [@decidable_rel (σ →₀ ℕ) (≤)]


lemma leading_term_le_of_lcm_left 
    (p q : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : q ≠ 0) : 
    leading_term_le p.leading_term (leading_term_lcm p q h₁ h₂) := 
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
    any_goals {simp [leading_term_lcm, hp, hq, leading_term_le, finsupp.leading_term_le, fintype.fintype_fold_and_iff], 
        intro x, rw ←H, try { rw [leading_monomial_eq_zero_of_const hp], simp},
    },

    rw ←leading_monomial_eq p.leading_monomial h,
    rw ←leading_monomial_eq (finsupp.zip_with max leading_term_lcm._proof_1 p.leading_monomial q.leading_monomial) h,
    simp, apply le_max_left,
end

lemma leading_term_le_of_lcm_right (p q : mv_polynomial σ α) (h₁ : p ≠ 0) (h₂ : q ≠ 0) : 
    leading_term_le q.leading_term (leading_term_lcm p q h₁ h₂) := 
by rw leading_term_lcm_comm p q h₁ h₂; apply leading_term_le_of_lcm_left

end decidable_linear_order
end gcd_domain

end general

namespace fin_n
variables {n : ℕ}

variables [discrete_field α] (lt_wellfounded: @well_founded (fin n →₀ ℕ) (<)) [bot_zero (fin n) ℕ]

section div

def leading_term_sub' {n} (a b: mv_polynomial (fin n) α) [bot_zero (fin n) ℕ]
    (h: leading_term_le b a) : fin n →₀ ℕ
     := finsupp.fin_n.leading_term_sub a.leading_monomial b.leading_monomial h

lemma leading_term_eq_notin_supp
    : Π {a b: mv_polynomial (fin n) α},
    leading_term a = leading_term b
    → a.leading_monomial ≠ 0
    → a.leading_monomial ∉ (a - b).support :=
λ a b eql neq0 insub,
begin
    unfold leading_term at eql,
    have coeff_neq_z := leading_monomial_ne_zero_coeff neq0,
    have lead_tm_eq := finsupp.single_inj1 coeff_neq_z eql,
    have lead_coeff_eq := finsupp.single_inj2 eql,
    rw finsupp.mem_support_iff at insub,
    apply insub,
    change (a - b).to_fun (leading_monomial a) = 0,
    unfold has_sub.sub algebra.sub,
    rw [←finsupp.coe_f, finsupp.add_apply],
    unfold leading_coeff at lead_coeff_eq,
    rw [←finsupp.coe_f] at lead_coeff_eq,
    rw [lead_coeff_eq, finsupp.coe_f, lead_tm_eq],
    apply add_right_neg,
end

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

lemma mul_X_support : ∀ {b : mv_polynomial (fin n) α} (k : fin n),
    finset.sup ((X k) * b).support id = finset.sup ((X k : mv_polynomial (fin n) α).support) id
                                    + (finset.sup b.support id) :=
begin
    intros,
    unfold has_mul.mul X monomial,
    unfold finsupp.sum,
    generalize lem : (finsupp.single (finsupp.single k 1) 1).support = t,
    rw [finsupp.single_support' (finsupp.single k 1)] at lem,
end

lemma sup_mul : ∀ (a b : mv_polynomial (fin n) α),
    (finset.sup (a * b).support id) = 
    finset.sup a.support id + finset.sup b.support id :=
λ a, begin
    apply mv_polynomial.induction_on a; intros,
    sorry, sorry,
    begin
        rw [a_1],
        rw [mul_assoc, a_1],
        have h: finset.sup ((X n_1 * b).support) id = finset.sup ((X n_1).support) id + finset.sup (b.support) id,
        apply mul_X_support,
        simp [h],
    end
end
lemma sup_single : ∀ {b : mv_polynomial (fin n) α} c d,
    (finset.sup ((b * finsupp.single c d).support) id) = 
        (finset.sup b.support id) + c :=
begin
    intro b,
    apply mv_polynomial.induction_on b; intros; try {simp},
    sorry, sorry,
end

lemma coeff_single : ∀ {a : mv_polynomial (fin n) α} b c,
    (leading_coeff (a * finsupp.single b c)) = a.leading_coeff * c := sorry

lemma leading_term_eq {a b : mv_polynomial (fin n) α} (hb : b ≠ 0) (hab : leading_term_le b a) : 
    a.leading_term = leading_term (b * finsupp.single (leading_term_sub' a b hab) 
                (a.leading_coeff / b.leading_coeff)) :=
begin
    unfold leading_term leading_monomial,
    simp [sup_single, coeff_single, has_div.div, algebra.div],
    apply finsupp.single_ext,

end

def reduction (a b : mv_polynomial (fin n) α) (h : leading_term_le b a) := 
    if mv_is_const b
    then 0
    else a - b * (monomial (leading_term_sub' a b h) (a.leading_coeff / b.leading_coeff))

lemma reduction_const (a : mv_polynomial (fin n) α) (b : α) : ∀ m,
    reduction a (C b) m = 0 :=
begin
    intros, unfold reduction, 
    simp [const_mv_is_const],
end

lemma reduction_zero (a : mv_polynomial (fin n) α) : ∀ m,
    reduction 0 a m = 0 :=
begin
    intro m, unfold reduction,
    have : a.leading_monomial = 0 := finsupp.fin_n.leading_term_le_antisymm m (finsupp.fin_n.leading_term_le_zero _),
    have eqzconst := leading_monomial_eqz_const this,
    cases eqzconst, by_cases mv_is_const a; simp [h],
    apply false.elim, apply h, rw eqzconst_snd, simp,
end

def reduction_list_aux : (mv_polynomial (fin n) α) → 
    (list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) → mv_polynomial (fin n) α
| a [] := a
| a (hd :: tl) := if h: leading_term_le hd.1 a
                  then reduction_list_aux (reduction a hd.1 h) tl
                  else reduction_list_aux a tl

lemma reduction_list_zero : 
    Π (s: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) (p: s ≠ list.nil),
    reduction_list_aux (C 0) s = 0 :=
begin
    intros s,
    cases s,
    begin
        intros, trivial,
    end,
    begin
        induction s_tl; intros,
        begin
            unfold reduction_list_aux,
            by_cases leading_term_le (s_hd.fst) (C 0); simp [h],
            unfold reduction,
            by_cases h': mv_is_const (s_hd.fst); simp [h'],
            rw [←(congr_arg leading_coeff C_0), leading_coeff_C],
            rw C_0 at h, simp, unfold monomial,
            rw [finsupp.single_zero],
            apply ring.mul_zero, 
        end,
        begin
            unfold reduction_list_aux,
            have lem : reduction_list_aux (C 0) (s_hd :: s_tl_tl) = 0 := s_tl_ih (by simp),
            unfold reduction_list_aux at lem,
            rw C_0 at *,
            by_cases h: leading_term_le (s_hd.fst) 0,
            by_cases h': leading_term_le (s_tl_hd.fst) (reduction 0 (s_hd.fst) h), simp [h, h'] at *,
            revert h,
            change ∀ (h : leading_term_le (s_hd.fst) 0) (h' : leading_term_le (s_tl_hd.fst) (reduction 0 (s_hd.fst) h)),
                        reduction_list_aux (reduction 0 (s_hd.fst) h) s_tl_tl = 0 →
                            reduction_list_aux (reduction (reduction 0 (s_hd.fst) h) (s_tl_hd.fst) h') s_tl_tl = 0,
            intro h, rw reduction_zero, intros h' p, rw reduction_zero, assumption,
            simp [h, h'] at *, assumption,
            simp [h] at *, 
            by_cases h': leading_term_le (s_tl_hd.fst) 0, simp [h'],
            rw reduction_zero, assumption, simp [h'], assumption,
        end,
    end
end


lemma reduction_leading_monomial_le: Π (a b: mv_polynomial (fin n) α),
    (b ≠ 0) → (a.leading_monomial ≠ 0) → Π (p: leading_term_le b a),
    leading_monomial (reduction a b p) < leading_monomial a :=
begin
    intros, unfold reduction, 
    by_cases mv_is_const b; simp [h],
    begin
        apply lt_of_le_of_ne, exact finsupp.fin_n.zero_le a.leading_monomial,
        exact a_2.symm, 
    end,
    begin
        apply sub_dec, apply leading_term_eq,
        assumption, assumption,
    end
end


lemma reduction_list_lem : ∀ (a b: mv_polynomial (fin n) α) m l (p: b ≠ 0) (p2: a.leading_monomial ≠ 0), 
    leading_monomial (reduction_list_aux (reduction a b m) l) < leading_monomial a :=
begin
    intros a b m l, revert a b m,
    induction l; intros,
    apply reduction_leading_monomial_le; assumption,
    unfold reduction_list_aux,
    by_cases leh : leading_term_le (l_hd.fst) (reduction a b m); simp [leh],
    begin
        by_cases eqz: leading_monomial (reduction a b m) = 0,
        begin
            have eq0 := leading_monomial_zero_of_le_zero eqz leh,
            have isconst := leading_monomial_eqz_const eq0,
            cases isconst,
            revert leh, rw [isconst_snd], intro leh, 
            rw [reduction_const, ←C_0], 
            cases l_tl,
            begin
                simp [leading_monomial, reduction_list_aux],
                apply lt_of_le_of_ne, exact finsupp.fin_n.zero_le a.leading_monomial,
                exact p2.symm,
            end,
            begin
                rw [reduction_list_zero],
                apply lt_of_le_of_ne, exact finsupp.fin_n.zero_le a.leading_monomial,
                exact p2.symm, simp,
            end,
        end,
        begin
            apply lt_trans,
            apply l_ih (reduction a b m) l_hd.fst leh l_hd.snd eqz,
            apply reduction_leading_monomial_le _ _ p p2,
        end
    end,
    begin
        apply l_ih; assumption,
    end
end

lemma reduction_list_aux_neq_lt : 
    Π (a : mv_polynomial (fin n) α) (l: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)),
    a.leading_monomial ≠ 0 →
    reduction_list_aux a l ≠ a → (reduction_list_aux a l).leading_monomial < a.leading_monomial :=
begin
    intros a l, revert a,
    induction l; intros, 
    apply false.elim (a_2 rfl),
    unfold reduction_list_aux,
    by_cases m: (leading_term_le (l_hd.fst) a); simp [m],
    swap,
    begin 
        apply l_ih a a_1, 
        intro eq,
        apply a_2, unfold reduction_list_aux; simp [m],
        assumption,
    end,
    begin
        apply reduction_list_lem, 
        exact l_hd.snd,
        assumption
    end
end

include lt_wellfounded
def reduction_list : Π (a : mv_polynomial (fin n) α) (l : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
   , mv_polynomial (fin n) α
| a l :=
   let r := reduction_list_aux a l
   in if h: r = a
    then r
    else if h': a.leading_monomial = 0 
         then r
         else have (reduction_list_aux a l).leading_monomial < a.leading_monomial,
         from reduction_list_aux_neq_lt a l h' h, 
         reduction_list r l
using_well_founded 
{ rel_tac := λ _ _, `[exact ⟨_, inv_image.wf (λ a, a.1.leading_monomial) lt_wellfounded⟩] 
, dec_tac := tactic.assumption }

end div

section buchberger
variables [decidable_linear_order α]

def s_poly (p q : mv_polynomial (fin n) α) : 
    p ≠ 0 → q ≠ 0 → mv_polynomial (fin n) α :=
λ p_nz q_nz,
    let fst := leading_term_sub' (leading_term_lcm p q p_nz q_nz) p.leading_term (leading_term_le_of_lcm_left p q p_nz q_nz) in
    let snd := leading_term_sub' (leading_term_lcm p q p_nz q_nz) q.leading_term (leading_term_le_of_lcm_right p q p_nz q_nz) in
    (monomial fst 1) * p - (monomial snd 1) * q

def buch_pairs (s : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)) 
: list (Σ' (p: mv_polynomial (fin n) α × mv_polynomial (fin n) α), 
                pprod (p.1 ≠ 0) (p.2 ≠ 0)) :=
    do  x ← s,
        y ← s,
        if x = y
        then []
        else [⟨(x.fst, y.fst), ⟨x.snd, y.snd⟩⟩]

def buch_s_polys (pairs : list (Σ' (p: mv_polynomial (fin n) α × mv_polynomial (fin n) α), 
                pprod (p.1 ≠ 0) (p.2 ≠ 0))) : list (mv_polynomial (fin n) α) 
    := pairs.map (λ a, s_poly a.fst.fst a.fst.snd a.snd.fst a.snd.snd)

def buch_div_result (s s_polys: list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0))
    := (list.foldl (λ a b, 
    let div_result := reduction_list lt_wellfounded (b: (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)).fst a
    in if div_result ∉ list.map psigma.fst a 
        then (if h: div_result = 0 then a else ⟨div_result, h⟩ :: a ) else a) s s_polys)

def filter_non_zero : list (mv_polynomial (fin n) α) →
    list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)
| [] := []
| (x :: xs) := if h: x = 0 then filter_non_zero xs else ⟨x, h⟩ :: filter_non_zero xs

def non_zero_poly_to_ideal : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0) → ideal (mv_polynomial (fin n) α) :=
    λ s, ideal.span $ finset.to_set $ list.to_finset $ s.map (λ (a : (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)), a.1.leading_term)

include lt_wellfounded

def buchberger : list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0) → 
    list (Σ' (p: mv_polynomial (fin n) α), p ≠ 0)
| s :=
    let result := buch_div_result lt_wellfounded s 
        $ filter_non_zero
        $ buch_s_polys
        $ buch_pairs s
        in if s = result then s else  
            have non_zero_poly_to_ideal s < non_zero_poly_to_ideal result := sorry,
            buchberger result
using_well_founded 
{ rel_tac := λ _ _, 
`[exact ⟨_, inv_image.wf non_zero_poly_to_ideal seqR.ideal_wf⟩] 
, dec_tac := tactic.assumption }

end buchberger
end fin_n

end mv_polynomial
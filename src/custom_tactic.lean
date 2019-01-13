import init.meta.tactic init.meta.rewrite_tactic
import init.meta.interactive_base init.meta.interactive
import data.finsupp
open lean
open lean.parser


namespace finsupp
variables {α : Type*} {β : Type*}
variables [decidable_eq α] [decidable_eq β]

section has_zero
variables [has_zero β] 
lemma coe_f : Π (a : α →₀ β) (n : α), a n = a.to_fun n := λ a n, rfl

lemma coe_f' : Π (a : α →₀ β) (n : α), a.to_fun n = a n := λ a n, rfl

end has_zero
end finsupp

namespace tactic




namespace interactive

open interactive 
open interactive.types
/-
Some tactics are modified from lean core
-/
private meta def repeat_gen_aux {α : Type*} (t : α → tactic α) : α → list expr → list expr → tactic α
| val []      r := set_goals r.reverse >> return val
| val (g::gs) r := do
  ok ← try_core (set_goals [g] >> t val),
  match ok with
  | none := repeat_gen_aux val gs (g::r)
  | (some val') := do
    gs' ← get_goals,
    repeat_gen_aux val' (gs' ++ gs) r
  end

meta def repeat_gen {α : Type*} (val : α) (t : α → tactic α) : tactic α :=
do gs ← get_goals, repeat_gen_aux t val gs []

private meta def rwc_hyp_trans (cfg : rewrite_cfg) (lem e : expr) : tactic expr :=
    do
    coe ← (to_expr' ``(finsupp.coe_f)),
    coe' ← (to_expr' ``(finsupp.coe_f')),
    r' ← (rewrite_hyp lem e cfg <|>
        (do 
            r ← repeat_gen e (λ v, rewrite_hyp coe v cfg),
            rewrite_hyp lem r cfg) <|> 
        (do r ← repeat_gen e (λ v, rewrite_hyp coe' v cfg),
            rewrite_hyp lem r cfg)),
    repeat_gen r' (λ v, rewrite_hyp coe v cfg)
            

private meta def rwcs_hyp_trans (cfg : rewrite_cfg) (lem e : expr) : tactic expr :=
    do
    coe ← (to_expr' ``(finsupp.coe_f)),
    coe' ← (to_expr' ``(finsupp.coe_f')),
    r' ← (rewrite_hyp lem e cfg <|>
        (do 
            r ← repeat_gen e (λ v, rewrite_hyp coe v cfg),
            rewrite_hyp lem r cfg) <|> 
        (do r ← repeat_gen e (λ v, rewrite_hyp coe' v cfg),
            rewrite_hyp lem r cfg)) <|>
        (do `[simp],
            rwcs_hyp_trans),
    repeat_gen r' (λ v, rewrite_hyp coe v cfg)
            
private meta def rewritec_target_trans (lem : expr) (cfg : rewrite_cfg) : tactic unit :=
    do
    coe ← (to_expr' ``(finsupp.coe_f)),
    coe' ← (to_expr' ``(finsupp.coe_f')),
    rewrite_target lem cfg <|> 
        (do 
            tactic.repeat (rewrite_target coe cfg),
            rewrite_target lem cfg) <|> 
        (do 
            tactic.repeat (rewrite_target coe' cfg),
            rewrite_target lem cfg),
    tactic.repeat (rewrite_target coe cfg)

private meta def rewritecs_target_trans (lem : expr) (cfg : rewrite_cfg) : tactic unit :=
    do
    coe ← (to_expr' ``(finsupp.coe_f)),
    coe' ← (to_expr' ``(finsupp.coe_f')),
    rewrite_target lem cfg <|> 
        (do 
            tactic.repeat (rewrite_target coe cfg),
            rewrite_target lem cfg) <|> 
        (do 
            tactic.repeat (rewrite_target coe' cfg),
            rewrite_target lem cfg) <|>
        (do `[simp],
            rewritecs_target_trans),
    tactic.repeat (rewrite_target coe cfg)


private meta def rwc_goal (cfg : rewrite_cfg) (rs : list rw_rule) : tactic unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do e ← to_expr' r.rule, rewritec_target_trans e {symm := r.symm, ..cfg})
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewritec_target_trans e {symm := r.symm, ..cfg})
   (eq_lemmas.empty)


private meta def rwcs_goal (cfg : rewrite_cfg) (rs : list rw_rule) : tactic unit :=
rs.mmap' $ λ r, do
 save_info r.pos,
 eq_lemmas ← get_rule_eqn_lemmas r,
 orelse'
   (do e ← to_expr' r.rule, rewritecs_target_trans e {symm := r.symm, ..cfg})
   (eq_lemmas.mfirst $ λ n, do e ← mk_const n, rewritecs_target_trans e {symm := r.symm, ..cfg})
   (eq_lemmas.empty)

private meta def uses_hyp (e : expr) (h : expr) : bool :=
e.fold ff $ λ t _ r, r || to_bool (t = h)


private meta def rwc_hyp (cfg : rewrite_cfg) : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule, when (not (uses_hyp e hyp)) $ 
                                 do r ← rwc_hyp_trans {symm := r.symm, ..cfg} e hyp,
                                    rwc_hyp rs r)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, 
                                r ← rwc_hyp_trans {symm := r.symm, ..cfg} e hyp,
                                rwc_hyp rs r)
    (eq_lemmas.empty)

private meta def rwcs_hyp (cfg : rewrite_cfg) : list rw_rule → expr → tactic unit
| []      hyp := skip
| (r::rs) hyp := do
  save_info r.pos,
  eq_lemmas ← get_rule_eqn_lemmas r,
  orelse'
    (do e ← to_expr' r.rule, when (not (uses_hyp e hyp)) $ 
                                 do r ← rwcs_hyp_trans {symm := r.symm, ..cfg} e hyp,
                                    rwcs_hyp rs r)
    (eq_lemmas.mfirst $ λ n, do e ← mk_const n, 
                                r ← rwcs_hyp_trans {symm := r.symm, ..cfg} e hyp,
                                rwcs_hyp rs r)
    (eq_lemmas.empty)

meta def rwc (rs : parse rw_rules) (loca : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
tactic.focus1 $
propagate_tags $
match loca with
| loc.wildcard := loca.try_apply (rwc_hyp cfg rs.rules) (rwc_goal cfg rs.rules)
| _            := loca.apply (rwc_hyp cfg rs.rules) (rwc_goal cfg rs.rules)
end >> try (tactic.reflexivity reducible)
    >> (returnopt rs.end_pos >>= save_info <|> skip)

meta def rwcs (rs : parse rw_rules) (loca : parse location) (cfg : rewrite_cfg := {}) : tactic unit :=
tactic.focus1 $
propagate_tags $
match loca with
| loc.wildcard := loca.try_apply (rwcs_hyp cfg rs.rules) (rwcs_goal cfg rs.rules)
| _            := loca.apply (rwcs_hyp cfg rs.rules) (rwcs_goal cfg rs.rules)
end >> try (tactic.reflexivity reducible)
    >> (returnopt rs.end_pos >>= save_info <|> skip)
    >> try `[simp [finsupp.coe_f]]


end interactive

end tactic
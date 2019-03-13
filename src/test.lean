--open tactic.interactive («have»)
--open interactive (parse loc.ns)
--open interactive.types (texpr location)
--open lean.parser (ident)

--open lean.parser (tk)
open lean
open lean.parser
local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
namespace interactive
open interactive interactive.types expr
meta def simp_arg_list_list : parser (list (list simp_arg_type)) :=
(tk "*" *> return [[simp_arg_type.all_hyps]]) <|> 
list_of ((tk "*" *> return [simp_arg_type.all_hyps]) <|> list_of simp_arg <|> return []) 
<|> return []

meta def decode_simp_arg_list' (hs : list (list simp_arg_type)) : 
    tactic $ list (list pexpr) × list (list name) × list (list name) × list bool :=
do
  

meta def simp' (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) 
(hs : parse simp_arg_list_list) (attr_names : parse with_ident_list)
(locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
sorry


example (a b c : ℤ) (h : b + a = c) : a + b = c :=
begin
    --simp [h],
    conv {},
end
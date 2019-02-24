import algebra.ordered_group algebra.ordered_ring
section old_structure_cmd
set_option old_structure_cmd true

class decidable_canonically_ordered_monoid (α : Type*) extends canonically_ordered_monoid α, decidable_linear_ordered_cancel_comm_monoid α

class is_well_founded (α : Type*) (r : α → α → Prop) := 
(wf : well_founded r)

class is_monomial_order (α : Type*) [has_add α] (r : α → α → Prop) :=
(monomial_order : ∀ a b : α, r a b → ∀ c : α, r (c + a) (c + b))

end old_structure_cmd

instance : decidable_canonically_ordered_monoid ℕ := {
    ..nat.canonically_ordered_comm_semiring,
    ..nat.decidable_linear_ordered_cancel_comm_monoid
}

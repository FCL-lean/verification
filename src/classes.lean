import algebra.ordered_group algebra.ordered_ring
section old_structure_cmd
set_option old_structure_cmd true

class decidable_canonically_ordered_monoid (α : Type*) extends canonically_ordered_monoid α, decidable_linear_ordered_cancel_comm_monoid α

end old_structure_cmd

instance : decidable_canonically_ordered_monoid ℕ := {
    ..nat.canonically_ordered_comm_semiring,
    ..nat.decidable_linear_ordered_cancel_comm_monoid
}
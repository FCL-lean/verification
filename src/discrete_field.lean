import algebra.gcd_domain

section discrete_field
variables {α : Type*} [discrete_field α] [decidable_eq α]

instance discrete_field_is_gcd_domain : gcd_domain α := {
    eq_zero_or_eq_zero_of_mul_eq_zero := discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero,
    norm_unit := λ a, if h : a = 0 then 1 else {
        val := a⁻¹,
        inv := a⁻¹⁻¹,
        val_inv := mul_inv_cancel (inv_ne_zero h),
        inv_val := inv_mul_cancel (inv_ne_zero h),
    },
    norm_unit_zero := by simp,
    norm_unit_mul := λ a b ha hb, begin
        simp [ha, hb, has_mul.mul, units.mul],
        split,
        change (a * b)⁻¹ = a⁻¹ * b⁻¹, finish [mul_inv'],
        finish,
    end,
    norm_unit_coe_units := λ u, begin 
        simp [units.ext_iff, units.val_coe], 
        generalize h_inv : u⁻¹ = k,
        unfold has_inv.inv units.inv' at h_inv, simp [h_inv.symm], 
        have h : u.val * u.val⁻¹ = u.val * u.inv, simp [units.val_inv], apply division_ring.mul_inv_cancel (units.ne_zero u),
        have h' :  u.inv * u.val * u.val⁻¹ = u.inv * u.val * u.inv, simp [mul_assoc, h], 
        finish [h', units.inv_val],
    end,
    gcd := λ a b, if a = 0 ∧ b = 0 then 0 else 1,
    lcm := λ a b, if a = 0 ∨ b = 0 then 0 else 1,
    gcd_dvd_left := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else by simp [h],
    gcd_dvd_right := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else by simp [h],
    dvd_gcd := λ a b c hac hab, if h : c = 0 ∧ b = 0 then by simp [h] else begin 
            simp [h], apply dvd.intro a⁻¹, apply mul_inv_cancel, intro ha, rw [ha, zero_dvd_iff] at hac hab,
            apply absurd (and.intro hac hab) h,
        end,
    norm_unit_gcd := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else begin 
        simp [h, units.ext_iff, units.val_coe], 
        unfold has_one.one, simp, apply one_inv_eq,
    end,
    gcd_mul_lcm := λ a b, if h : a = 0 ∧ b = 0 then by simp [h] else begin 
        simp [h], by_cases h' : a = 0 ∨ b = 0; simp [h', units.val_coe],
    end,
    lcm_zero_left := λ a, by simp,
    lcm_zero_right := λ a, by simp,
    .._inst_1,    
}

end discrete_field
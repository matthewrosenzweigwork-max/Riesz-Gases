import HRS.MS.SuppU8Aux3

/-!
# Worker U8 aux 4: the symbol `∫ (2 - 2 cos (2π ⟪y,ξ⟫))^m ‖y‖^{-d-α} dy = M (2π‖ξ‖)^α`
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

variable {d : ℕ}

/-- `(2 - 2 cos (2π t))^m`. -/
def u8_g (m : ℕ) (t : ℝ) : ℝ := (2 - 2 * Real.cos (2 * Real.pi * t)) ^ m

theorem u8_g_nonneg (m : ℕ) (t : ℝ) : 0 ≤ u8_g m t := by
  unfold u8_g
  have := Real.cos_le_one (2 * Real.pi * t)
  exact pow_nonneg (by linarith) m

theorem u8_g_le_four (m : ℕ) (t : ℝ) : u8_g m t ≤ 4 ^ m := by
  unfold u8_g
  have h1 := Real.neg_one_le_cos (2 * Real.pi * t)
  have h2 := Real.cos_le_one (2 * Real.pi * t)
  exact pow_le_pow_left₀ (by linarith) (by linarith) m

theorem u8_g_le_sq (m : ℕ) (t : ℝ) : u8_g m t ≤ ((2 * Real.pi * t) ^ 2) ^ m := by
  unfold u8_g
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * t)
  have h2 := Real.cos_le_one (2 * Real.pi * t)
  exact pow_le_pow_left₀ (by linarith) (by linarith) m

theorem u8_g_zero (m : ℕ) (hm : 1 ≤ m) : u8_g m 0 = 0 := by
  unfold u8_g
  simp
  omega

/-- The integrand of the symbol. -/
def u8_symInt (d m : ℕ) (α : ℝ) (ξ y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  u8_g m (inner ℝ y ξ) * ‖y‖ ^ (-((d : ℝ) + α))

theorem u8_symInt_measurable (m : ℕ) (α : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    Measurable (u8_symInt d m α ξ) := by
  unfold u8_symInt u8_g
  fun_prop

theorem u8_symInt_nonneg (m : ℕ) (α : ℝ) (ξ y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ u8_symInt d m α ξ y :=
  mul_nonneg (u8_g_nonneg m _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem u8_symInt_le_near (m : ℕ) (α : ℝ) (ξ y : EuclideanSpace ℝ (Fin d)) (hy : y ≠ 0) :
    u8_symInt d m α ξ y ≤ (2 * Real.pi * ‖ξ‖) ^ (2 * m) * ‖y‖ ^ ((2 * m : ℝ) - α - d) := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy
  unfold u8_symInt
  have h1 : u8_g m (inner ℝ y ξ) ≤ ((2 * Real.pi * ‖ξ‖) * ‖y‖) ^ (2 * m) := by
    refine (u8_g_le_sq m _).trans ?_
    rw [pow_mul (2 * Real.pi * ‖ξ‖ * ‖y‖) 2 m]
    apply pow_le_pow_left₀ (sq_nonneg _)
    have h2 : |inner ℝ y ξ| ≤ ‖y‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
    have : |2 * Real.pi * inner ℝ y ξ| ≤ 2 * Real.pi * ‖ξ‖ * ‖y‖ := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    calc (2 * Real.pi * inner ℝ y ξ) ^ 2 = |2 * Real.pi * inner ℝ y ξ| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * Real.pi * ‖ξ‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  calc u8_g m (inner ℝ y ξ) * ‖y‖ ^ (-((d : ℝ) + α))
      ≤ ((2 * Real.pi * ‖ξ‖) * ‖y‖) ^ (2 * m) * ‖y‖ ^ (-((d : ℝ) + α)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hyp.le _)
    _ = (2 * Real.pi * ‖ξ‖) ^ (2 * m) * ‖y‖ ^ ((2 * m : ℝ) - α - d) := by
        rw [mul_pow, mul_assoc]
        congr 1
        rw [← Real.rpow_natCast ‖y‖ (2 * m), ← Real.rpow_add hyp]
        congr 1
        push_cast; ring

theorem u8_symInt_le_far (m : ℕ) (α : ℝ) (ξ y : EuclideanSpace ℝ (Fin d)) :
    u8_symInt d m α ξ y ≤ (4 : ℝ) ^ m * ‖y‖ ^ (-(d : ℝ) - α) := by
  unfold u8_symInt
  rw [show -(d : ℝ) - α = -((d : ℝ) + α) by ring]
  exact mul_le_mul_of_nonneg_right (u8_g_le_four m _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem u8_symInt_integrable (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α)
    (hαm : α < 2 * m) (ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (u8_symInt d m α ξ) := by
  have hη : 0 < 2 * (m : ℝ) - α := by linarith
  obtain ⟨hnear, -⟩ := u8_near_int (d := d) hd (2 * m - α) 1 hη one_pos
  obtain ⟨hfar, -⟩ := u8_far_int (d := d) hd α 1 hα one_pos
  have hnear' := (integrable_indicator_iff
    (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin d))) (ε := 1))).2 hnear
  set A : ℝ := (2 * Real.pi * ‖ξ‖) ^ (2 * m) with hA
  have hA0 : 0 ≤ A := by positivity
  refine Integrable.mono' ((hnear'.const_mul A).add (hfar.const_mul ((4 : ℝ) ^ m)))
    (u8_symInt_measurable m α ξ).aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
  rw [Real.norm_of_nonneg (u8_symInt_nonneg m α ξ y)]
  by_cases hy : ‖y‖ < 1
  · have hy1 : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by simpa using hy
    have hy2 : y ∉ (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ := fun h => h hy1
    simp only [Pi.add_apply, indicator_of_mem hy1, indicator_of_notMem hy2, mul_zero, add_zero]
    by_cases h0 : y = 0
    · subst h0
      have : u8_symInt d m α ξ 0 = 0 := by
        unfold u8_symInt
        simp [u8_g_zero m hm]
      rw [this]
      positivity
    · exact u8_symInt_le_near m α ξ y h0
  · have hy1 : y ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ := by simpa using hy
    have hy2 : y ∉ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := fun h => hy (by simpa using h)
    simp only [Pi.add_apply, indicator_of_mem hy1, indicator_of_notMem hy2, mul_zero, zero_add]
    exact u8_symInt_le_far m α ξ y

/-- The symbol `∫ (2 - 2cos(2π⟪y,ξ⟫))^m ‖y‖^{-d-α} dy`. -/
def u8_sym (d m : ℕ) (α : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := ∫ y, u8_symInt d m α ξ y

theorem u8_sym_zero (m : ℕ) (hm : 1 ≤ m) (α : ℝ) : u8_sym d m α 0 = 0 := by
  unfold u8_sym u8_symInt
  simp [u8_g_zero m hm]

theorem u8_sym_smul (hd : 1 ≤ d) (m : ℕ) (α : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hc : 0 < c) : u8_sym d m α (c • ξ) = c ^ α * u8_sym d m α ξ := by
  have : NeZero d := ⟨by omega⟩
  unfold u8_sym
  have h1 : ∀ y : EuclideanSpace ℝ (Fin d),
      u8_symInt d m α (c • ξ) y = c ^ ((d : ℝ) + α) * u8_symInt d m α ξ (c • y) := by
    intro y
    unfold u8_symInt
    rw [inner_smul_right, inner_smul_left, norm_smul, Real.norm_of_nonneg hc.le,
      Real.mul_rpow hc.le (norm_nonneg _), RCLike.conj_to_real]
    have : c ^ ((d : ℝ) + α) * c ^ (-((d : ℝ) + α)) = 1 := by
      rw [← Real.rpow_add hc]; simp
    calc u8_g m (c * inner ℝ y ξ) * ‖y‖ ^ (-((d : ℝ) + α))
        = (c ^ ((d : ℝ) + α) * c ^ (-((d : ℝ) + α))) *
          (u8_g m (c * inner ℝ y ξ) * ‖y‖ ^ (-((d : ℝ) + α))) := by rw [this, one_mul]
      _ = _ := by ring
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (fun y => u8_symInt d m α ξ y) c, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (inv_pos.2 (pow_pos hc d))]
  rw [Real.rpow_add hc, Real.rpow_natCast]
  field_simp

theorem u8_sym_rot (m : ℕ) (α : ℝ) (R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (ξ : EuclideanSpace ℝ (Fin d)) : u8_sym d m α (R ξ) = u8_sym d m α ξ := by
  unfold u8_sym
  have h1 : ∀ y, u8_symInt d m α (R ξ) y = u8_symInt d m α ξ (R.symm y) := by
    intro y
    have e : inner ℝ y (R ξ) = inner ℝ (R.symm y) ξ := by
      rw [← R.inner_map_map (R.symm y) ξ, R.apply_symm_apply]
    have e2 : ‖y‖ = ‖R.symm y‖ := (R.symm.norm_map y).symm
    unfold u8_symInt
    rw [e, e2]
  simp_rw [h1]
  exact (R.symm.measurePreserving).integral_comp R.symm.toHomeomorph.measurableEmbedding
    (fun y => u8_symInt d m α ξ y)

theorem u8_sym_pos (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hαm : α < 2 * m)
    (e0 : EuclideanSpace ℝ (Fin d)) (he0 : ‖e0‖ = 1) : 0 < u8_sym d m α e0 := by
  unfold u8_sym
  rw [integral_pos_iff_support_of_nonneg (u8_symInt_nonneg m α e0)
    (u8_symInt_integrable hd m hm α hα hαm e0)]
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => inner ℝ y e0) := by fun_prop
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin d) | 0 < inner ℝ y e0 ∧ inner ℝ y e0 < 1} :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hne : ({y : EuclideanSpace ℝ (Fin d) | 0 < inner ℝ y e0 ∧ inner ℝ y e0 < 1}).Nonempty := by
    refine ⟨(1 / 2 : ℝ) • e0, ?_⟩
    simp only [mem_setOf_eq, inner_smul_left, real_inner_self_eq_norm_sq, he0]
    norm_num
  have hsub : {y : EuclideanSpace ℝ (Fin d) | 0 < inner ℝ y e0 ∧ inner ℝ y e0 < 1} ⊆
      Function.support (u8_symInt d m α e0) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl; simp at h1
    have hc : Real.cos (2 * Real.pi * inner ℝ y e0) ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
      have hpi := Real.pi_pos
      have h3 : (n : ℝ) = inner ℝ y e0 := by
        have : (n : ℝ) * (2 * Real.pi) = 2 * Real.pi * inner ℝ y e0 := hn
        nlinarith
      have h4 : (0 : ℝ) < n := by rw [h3]; exact h1
      have h5 : (n : ℝ) < 1 := by rw [h3]; exact h2
      have h6 : (0 : ℤ) < n := by exact_mod_cast h4
      have h7 : n < (1 : ℤ) := by exact_mod_cast h5
      omega
    simp only [Function.mem_support, u8_symInt, u8_g]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · intro h; apply hc; linarith
    · exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hy0) _).ne'
  exact lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono hsub)

/-- The multiplier constant. -/
theorem u8_sym_eq (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hαm : α < 2 * m) :
    ∃ M : ℝ, 0 < M ∧ ∀ ξ : EuclideanSpace ℝ (Fin d),
      u8_sym d m α ξ = M * (2 * Real.pi * ‖ξ‖) ^ α := by
  set e0 : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ 1 with he0def
  have he0 : ‖e0‖ = 1 := by simp [he0def]
  have hpos := u8_sym_pos hd m hm α hα hαm e0 he0
  refine ⟨u8_sym d m α e0 / (2 * Real.pi) ^ α, by positivity, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    rw [u8_sym_zero m hm α]
    simp [Real.zero_rpow hα.ne']
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set u : EuclideanSpace ℝ (Fin d) := ‖ξ‖⁻¹ • ξ with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm]; field_simp
    have hξu : ξ = ‖ξ‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    set R := Submodule.reflection (ℝ ∙ (u - e0))ᗮ with hR
    have hRu : R u = e0 := Submodule.reflection_sub (by rw [hun, he0])
    have h1 : u8_sym d m α u = u8_sym d m α e0 := by
      rw [← hRu, u8_sym_rot]
    conv_lhs => rw [hξu]
    rw [u8_sym_smul hd m α u ‖ξ‖ hn, h1, Real.mul_rpow (by positivity) hn.le]
    field_simp

end HRS.U8

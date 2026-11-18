import Mathlib

/-!
# S54 part 9: a weakly singular Gronwall lemma (no dependence on the project)
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.Who

theorem who_exp_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx (by linarith [Real.add_one_le_exp x])

/-- `∫_0^τ u^{-1/2} e^{-λu} du ≤ 2s + 2/(λ s)` -/
theorem who_exp_kernel_le {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ u in (0 : ℝ)..τ, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(lam * u)) ≤ 2 * s + 2 / (lam * s) := by
  set f : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(lam * u)) with hf
  have hfi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num) (a := a) (b := b)).mul_continuousOn
      (by fun_prop)
  have hs2 : (s ^ 2) ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hs2' : (s ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
    rw [Real.rpow_neg_one]
  have hA : ∫ u in (0 : ℝ)..min τ (s ^ 2), f u ≤ 2 * s := by
    have hm0 : 0 ≤ min τ (s ^ 2) := le_min hτ (by positivity)
    have h1 : ∫ u in (0 : ℝ)..min τ (s ^ 2), f u ≤ ∫ u in (0 : ℝ)..min τ (s ^ 2), u ^ (-(1 / 2 : ℝ)) := by
      refine intervalIntegral.integral_mono_on hm0 (hfi _ _)
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num)) fun u hu => ?_
      have : Real.exp (-(lam * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hu.1])
      calc f u = u ^ (-(1 / 2 : ℝ)) * Real.exp (-(lam * u)) := rfl
        _ ≤ u ^ (-(1 / 2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hu.1 _)
        _ = _ := mul_one _
    refine h1.trans ?_
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num
    have : (min τ (s ^ 2)) ^ (1 / 2 : ℝ) ≤ s := by
      calc (min τ (s ^ 2)) ^ (1 / 2 : ℝ) ≤ (s ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hm0 (min_le_right _ _) (by norm_num)
        _ = s := hs2
    linarith
  have hB : ∫ u in min τ (s ^ 2)..τ, f u ≤ 2 / (lam * s) := by
    rcases le_or_gt τ (s ^ 2) with h | h
    · rw [min_eq_left h, intervalIntegral.integral_same]; positivity
    · rw [min_eq_right h.le]
      have h1 : ∫ u in s ^ 2..τ, f u ≤ ∫ u in s ^ 2..τ, (1 / lam) * u ^ (-(3 / 2 : ℝ)) := by
        refine intervalIntegral.integral_mono_on h.le (hfi _ _) ?_ fun u hu => ?_
        · exact (intervalIntegral.intervalIntegrable_rpow (Or.inr (by
            rw [Set.uIcc_of_le h.le]; intro h0; have := h0.1; nlinarith [sq_nonneg s]))).const_mul _
        · have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
          have h2 := who_exp_le_inv (x := lam * u) (by positivity)
          calc f u = u ^ (-(1 / 2 : ℝ)) * Real.exp (-(lam * u)) := rfl
            _ ≤ u ^ (-(1 / 2 : ℝ)) * (1 / (lam * u)) :=
                mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hu0.le _)
            _ = (1 / lam) * u ^ (-(3 / 2 : ℝ)) := by
                have : u ^ (-(3 / 2 : ℝ)) = u ^ (-(1 / 2 : ℝ)) * u⁻¹ := by
                  rw [← Real.rpow_neg_one, ← Real.rpow_add hu0]; norm_num
                rw [this]; field_simp
      refine h1.trans ?_
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, by
        rw [Set.uIcc_of_le h.le]; intro h0; have := h0.1; nlinarith [sq_nonneg s]⟩)]
      norm_num
      have hτ' : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ _
      rw [hs2']
      have : lam⁻¹ * ((τ ^ (-(1 / 2 : ℝ)) - 1 / s) / (-(1 / 2))) = 2 / lam * (1 / s - τ ^ (-(1 / 2 : ℝ))) := by
        field_simp
        ring
      rw [this]
      have h3 : 0 ≤ 2 / lam * τ ^ (-(1 / 2 : ℝ)) := by positivity
      calc 2 / lam * (1 / s - τ ^ (-(1 / 2 : ℝ))) ≤ 2 / lam * (1 / s) := by nlinarith
        _ = 2 / (lam * s) := by field_simp
  calc ∫ u in (0 : ℝ)..τ, f u = (∫ u in (0 : ℝ)..min τ (s ^ 2), f u) + ∫ u in min τ (s ^ 2)..τ, f u := by
        rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
    _ ≤ _ := add_le_add hA hB


/-- **weakly singular Gronwall** -/
theorem who_gronwall {T : ℝ} (hT : 0 ≤ T) (b : ℝ) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t a M : ℝ} {F : ℝ → ℝ}, 0 ≤ t → t ≤ T → 0 ≤ a → Measurable F →
      (∀ τ ∈ Icc 0 t, 0 ≤ F τ ∧ F τ ≤ M) →
      (∀ τ ∈ Icc 0 t, F τ ≤ a + b * ∫ σ in Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ) →
      ∀ τ ∈ Icc 0 t, F τ ≤ K * a := by
  set B : ℝ := b + 1 with hBdef
  have hB : 0 < B := by linarith
  set s : ℝ := 1 / (8 * B) with hsdef
  have hs : 0 < s := by positivity
  set lam : ℝ := 64 * B ^ 2 with hlamdef
  have hlam : 0 < lam := by positivity
  have hI : 2 * s + 2 / (lam * s) = 1 / (2 * B) := by
    rw [hsdef, hlamdef]; field_simp; ring
  refine ⟨2 * Real.exp (lam * T), by positivity, fun {t a M F} ht htT ha hFm hF0 hF τ hτ => ?_⟩
  set M' : ℝ := max M 0 with hM'
  set G : ℝ → ℝ := fun τ => Real.exp (-(lam * τ)) * F τ with hG
  have hGnn : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ G τ := fun τ hτ =>
    mul_nonneg (Real.exp_pos _).le (hF0 τ hτ).1
  have hGle : ∀ τ ∈ Icc (0 : ℝ) t, G τ ≤ M' := fun τ hτ => by
    have h1 : Real.exp (-(lam * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hτ.1])
    calc G τ ≤ 1 * F τ := mul_le_mul_of_nonneg_right h1 (hF0 τ hτ).1
      _ ≤ M' := by rw [one_mul]; exact (hF0 τ hτ).2.trans (le_max_left _ _)
  set N : ℝ := ⨆ τ : Icc (0 : ℝ) t, G τ with hN
  have hbdd : BddAbove (Set.range fun τ : Icc (0 : ℝ) t => G τ) := ⟨M', by
    rintro _ ⟨τ, rfl⟩; exact hGle τ τ.2⟩
  haveI : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
  have hGN : ∀ τ ∈ Icc (0 : ℝ) t, G τ ≤ N := fun τ hτ => le_ciSup hbdd (⟨τ, hτ⟩ : Icc (0 : ℝ) t)
  have hN0 : 0 ≤ N := (hGnn 0 ⟨le_rfl, ht⟩).trans (hGN 0 ⟨le_rfl, ht⟩)
  -- the key estimate
  have key : ∀ τ ∈ Icc (0 : ℝ) t, G τ ≤ a + N / 2 := by
    intro τ hτ
    have hF1 := hF τ hτ
    have hint1 : IntegrableOn (fun σ => (τ - σ) ^ (-(1 / 2 : ℝ))) (Ioo 0 τ) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num) (a := 0) (b := τ)).comp_sub_left τ
      simp only [sub_self, sub_zero] at this
      exact (this.symm.1.mono_set (Ioo_subset_Ioc_self))
    have hmeas : Measurable fun σ : ℝ => (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ :=
      ((measurable_const.sub measurable_id).pow_const _).mul hFm
    have hpt : ∀ σ ∈ Ioo (0 : ℝ) τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ ≤
        N * ((τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ)) := by
      intro σ hσ
      have hσ' : σ ∈ Icc (0 : ℝ) t := ⟨hσ.1.le, (hσ.2.le).trans hτ.2⟩
      have h1 : F σ ≤ N * Real.exp (lam * σ) := by
        have := hGN σ hσ'
        simp only [hG] at this
        have h2 : Real.exp (lam * σ) * (Real.exp (-(lam * σ)) * F σ) = F σ := by
          rw [← mul_assoc, ← Real.exp_add]; simp
        calc F σ = Real.exp (lam * σ) * (Real.exp (-(lam * σ)) * F σ) := h2.symm
          _ ≤ Real.exp (lam * σ) * N := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = _ := mul_comm _ _
      have hu : 0 ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _
      calc (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) * (N * Real.exp (lam * σ)) :=
            mul_le_mul_of_nonneg_left h1 hu
        _ = _ := by ring
    have hint2 : IntegrableOn (fun σ => N * ((τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ))) (Ioo 0 τ) := by
      refine (hint1.const_mul (N * Real.exp (lam * τ))).mono'
        (((measurable_const.sub measurable_id).pow_const _).mul (Real.measurable_exp.comp
          (measurable_const.mul measurable_id)) |>.const_mul N).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
      have hu : 0 ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _
      have he : Real.exp (lam * σ) ≤ Real.exp (lam * τ) := Real.exp_le_exp.2 (by nlinarith [hσ.2])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hN0 (mul_nonneg hu (Real.exp_pos _).le))]
      calc N * ((τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ)) ≤ N * ((τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * τ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hu) hN0
        _ = _ := by ring
    have hint3 : IntegrableOn (fun σ => (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ) (Ioo 0 τ) := by
      refine (hint1.const_mul M').mono' hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
      have hσ' : σ ∈ Icc (0 : ℝ) t := ⟨hσ.1.le, (hσ.2.le).trans hτ.2⟩
      have hu : 0 ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_nonneg.2 hσ.2.le) _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu (hF0 σ hσ').1)]
      calc (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) * M' :=
            mul_le_mul_of_nonneg_left ((hF0 σ hσ').2.trans (le_max_left _ _)) hu
        _ = _ := by ring
    have hmono : ∫ σ in Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * F σ ≤
        N * ∫ σ in Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ) := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on hint3 hint2 measurableSet_Ioo hpt
    have hker : Real.exp (-(lam * τ)) * ∫ σ in Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ) ≤
        1 / (2 * B) := by
      rw [← integral_const_mul]
      have e1 : ∀ σ : ℝ, Real.exp (-(lam * τ)) * ((τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ)) =
          (τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(lam * (τ - σ))) := fun σ => by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      simp_rw [e1]
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hτ.1,
        intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(lam * u))) τ,
        sub_self, sub_zero]
      exact (who_exp_kernel_le hlam hs hτ.1).trans_eq hI
    have hexp : Real.exp (-(lam * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hτ.1])
    have hb2 : b / (2 * B) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc G τ = Real.exp (-(lam * τ)) * F τ := rfl
      _ ≤ Real.exp (-(lam * τ)) * (a + b * (N * ∫ σ in Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ))) :=
          mul_le_mul_of_nonneg_left (hF1.trans (by gcongr)) (Real.exp_pos _).le
      _ = Real.exp (-(lam * τ)) * a + b * N * (Real.exp (-(lam * τ)) *
            ∫ σ in Ioo 0 τ, (τ - σ) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * σ)) := by ring
      _ ≤ 1 * a + b * N * (1 / (2 * B)) := add_le_add (mul_le_mul_of_nonneg_right hexp ha)
          (mul_le_mul_of_nonneg_left hker (mul_nonneg hb hN0))
      _ = a + N * (b / (2 * B)) := by ring
      _ ≤ a + N * (1 / 2) := by gcongr
      _ = a + N / 2 := by ring
  have hNle : N ≤ a + N / 2 := ciSup_le fun τ => key τ τ.2
  have hN2 : N ≤ 2 * a := by linarith
  have h1 := hGN τ hτ
  have h2 : F τ = Real.exp (lam * τ) * G τ := by
    simp only [hG]; rw [← mul_assoc, ← Real.exp_add]; simp
  calc F τ = Real.exp (lam * τ) * G τ := h2
    _ ≤ Real.exp (lam * T) * (2 * a) := mul_le_mul (Real.exp_le_exp.2 (by nlinarith [hτ.2, hlam, htT])) (h1.trans hN2)
        (hGnn τ hτ) (Real.exp_pos _).le
    _ = 2 * Real.exp (lam * T) * a := by ring

end HRS.MS.Who

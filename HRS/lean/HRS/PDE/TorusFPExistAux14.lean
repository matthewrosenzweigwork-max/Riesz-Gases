import HRS.PDE.TorusFPExistAux13

/-!
# D1 existence, helper 14: the weak equation for `C²` time-independent tests
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem d1_hasDerivWithinAt_setIntegral {B : ℝ → ℝ} {T s : ℝ} (hB : ContinuousOn B (Set.Icc 0 T))
    (hs : s ∈ Set.Ico 0 T) :
    HasDerivWithinAt (fun t => ∫ r in Set.Icc 0 t, B r) (B s) (Set.Ioi s) s := by
  have hsub : Set.Icc 0 s ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hs.2.le
  have hint : IntervalIntegrable B MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs.1]
    exact hB.mono hsub
  have hmem : Set.Icc 0 T ∈ 𝓝[Set.Ioi s] s :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hs.2) (fun r hr => ⟨by linarith [hs.1, hr.1], hr.2.le⟩)
  have hcw : ContinuousWithinAt B (Set.Ioi s) s :=
    (hB s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin hmem
  have hmeas : StronglyMeasurableAtFilter B (𝓝[Set.Ioi s] s) MeasureTheory.volume :=
    (hB.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s).filter_mono
      (nhdsWithin_le_of_mem hmem)
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := s) (s := Set.Ici s)
    (t := Set.Ioi s) hint hmeas hcw
  refine (hd.mono Set.Ioi_subset_Ici_self).congr (fun u hu => ?_) ?_
  · have hu0 : 0 ≤ u := by have : s < u := hu; linarith [hs.1]
    rw [intervalIntegral.integral_of_le hu0, integral_Icc_eq_integral_Ioc]
  · rw [intervalIntegral.integral_of_le hs.1, integral_Icc_eq_integral_Ioc]


theorem d1_gen_sub_bound {κ : ℝ} (hκ : 0 ≤ κ) {b : Torus n → Euc n} {B : ℝ} (hB : ∀ x, ‖b x‖ ≤ B)
    {φ ψ : Torus n → ℝ} {ε : ℝ} (x : Torus n) (h1 : ‖Torus.grad φ x - Torus.grad ψ x‖ ≤ ε)
    (h2 : |Torus.laplacian φ x - Torus.laplacian ψ x| ≤ ε) :
    |d1_gen κ b φ x - d1_gen κ b ψ x| ≤ (κ + B) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  unfold d1_gen
  have e : κ * Torus.laplacian φ x + inner ℝ (b x) (Torus.grad φ x) -
      (κ * Torus.laplacian ψ x + inner ℝ (b x) (Torus.grad ψ x)) =
      κ * (Torus.laplacian φ x - Torus.laplacian ψ x) +
        inner ℝ (b x) (Torus.grad φ x - Torus.grad ψ x) := by
    rw [inner_sub_right]; ring
  rw [e]
  calc |κ * (Torus.laplacian φ x - Torus.laplacian ψ x) + inner ℝ (b x) (Torus.grad φ x - Torus.grad ψ x)|
      ≤ |κ * (Torus.laplacian φ x - Torus.laplacian ψ x)| +
        |inner ℝ (b x) (Torus.grad φ x - Torus.grad ψ x)| := abs_add_le _ _
    _ ≤ κ * ε + B * ε := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_nonneg hκ]
          exact mul_le_mul_of_nonneg_left h2 hκ
        · calc |inner ℝ (b x) (Torus.grad φ x - Torus.grad ψ x)|
              ≤ ‖b x‖ * ‖Torus.grad φ x - Torus.grad ψ x‖ := abs_real_inner_le_norm _ _
            _ ≤ B * ε := mul_le_mul (hB x) h1 (norm_nonneg _) hB0
    _ = (κ + B) * ε := by ring

section WeakC2

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

/-- **Weak equation for `C²` time-independent tests.** -/
theorem d1_weak_C2 {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ) = ∫ x, φ x ∂μ₀ +
      ∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s) := by
  have hbc := d1_gradDrift_continuous hU
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hbc.continuousOn
  have hB' : ∀ x, ‖d1_gradDrift U x‖ ≤ B := fun x => hB x (Set.mem_univ x)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  have hφc : Continuous φ := by
    apply Torus.continuous_of_continuous_lift
    exact (d1_contDiff_of_isCk2 hφ (j := 0) (by norm_num)).continuous
  have hLφ : Continuous (d1_gen κ (d1_gradDrift U) φ) := d1_gen_continuous hbc hφ
  set C : ℝ := κ + B + 1 with hC
  have hCpos : 0 < C := by rw [hC]; linarith
  have key : ∀ k : ℕ, |(∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ)) - (∫ x, φ x ∂μ₀ +
      ∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s))| ≤
      (2 + τ) / ((k : ℝ) + 1) := by
    intro k
    have hεk : 0 < 1 / (((k : ℝ) + 1) * C) := by positivity
    obtain ⟨ψ, hψ, hψb⟩ := d1_exists_C2_approx hφ hεk
    have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
    have hψ2 := d1_isCk_of_isSmooth hψ 2
    have hLψ : Continuous (d1_gen κ (d1_gradDrift U) ψ) := d1_gen_smooth_continuous hU hψ
    have hgen : ∀ x, |d1_gen κ (d1_gradDrift U) φ x - d1_gen κ (d1_gradDrift U) ψ x| ≤
        1 / ((k : ℝ) + 1) := by
      intro x
      have := d1_gen_sub_bound hκ.le hB' x (hψb x).2.1 (hψb x).2.2
      refine this.trans ?_
      have : (κ + B) * (1 / (((k : ℝ) + 1) * C)) ≤ 1 / ((k : ℝ) + 1) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        rw [hC]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      exact this
    have hεle : 1 / (((k : ℝ) + 1) * C) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hC]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hW := d1_weak_smooth hn hκ hU μ₀ hψ hτ
    have t1 : |∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ) - ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ τ)| ≤ 1 / ((k : ℝ) + 1) := by
      have := d1_mu_prob hn hκ hU μ₀ τ
      exact d1_abs_integral_sub_le hφc hψc (fun x => (hψb x).1.trans hεle)
    have t2 : |∫ x, φ x ∂μ₀ - ∫ x, ψ x ∂μ₀| ≤ 1 / ((k : ℝ) + 1) :=
      d1_abs_integral_sub_le hφc hψc (fun x => (hψb x).1.trans hεle)
    have hI1 : ContinuousOn (fun s => ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s))
        (Set.Icc 0 τ) := d1_narrow hn hκ hU μ₀ hLφ τ
    have hI2 : ContinuousOn (fun s => ∫ x, d1_gen κ (d1_gradDrift U) ψ x ∂(d1_mu hn hκ hU μ₀ s))
        (Set.Icc 0 τ) := d1_narrow hn hκ hU μ₀ hLψ τ
    have t3 : |(∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) -
        (∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) ψ x ∂(d1_mu hn hκ hU μ₀ s))| ≤
        τ / ((k : ℝ) + 1) := by
      rw [← integral_sub (hI1.integrableOn_Icc) (hI2.integrableOn_Icc)]
      have := norm_setIntegral_le_of_norm_le_const (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) τ)
        (f := fun s => (∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) -
          ∫ x, d1_gen κ (d1_gradDrift U) ψ x ∂(d1_mu hn hκ hU μ₀ s))
        (C := 1 / ((k : ℝ) + 1)) (by simp) (fun s _ => by
          have := d1_mu_prob hn hκ hU μ₀ s
          rw [Real.norm_eq_abs]
          exact d1_abs_integral_sub_le hLφ hLψ hgen)
      rw [Real.norm_eq_abs, Real.volume_real_Icc_of_le hτ, sub_zero] at this
      calc _ ≤ _ := this
        _ = τ / ((k : ℝ) + 1) := by ring
    have hsum : (∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ)) - (∫ x, φ x ∂μ₀ +
        ∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) =
        ((∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ) - ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ τ)) -
          (∫ x, φ x ∂μ₀ - ∫ x, ψ x ∂μ₀)) -
        ((∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) -
        (∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) ψ x ∂(d1_mu hn hκ hU μ₀ s))) := by
      linarith [hW]
    rw [hsum]
    calc _ ≤ |(∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ) - ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ τ)) -
          (∫ x, φ x ∂μ₀ - ∫ x, ψ x ∂μ₀)| + |(∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) -
        (∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) ψ x ∂(d1_mu hn hκ hU μ₀ s))| := abs_sub _ _
      _ ≤ (|∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ) - ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ τ)| +
          |∫ x, φ x ∂μ₀ - ∫ x, ψ x ∂μ₀|) + τ / ((k : ℝ) + 1) :=
          add_le_add (abs_sub _ _) t3
      _ ≤ (1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1)) + τ / ((k : ℝ) + 1) :=
          add_le_add (add_le_add t1 t2) le_rfl
      _ = (2 + τ) / ((k : ℝ) + 1) := by ring
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm (by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨k, hk⟩ := exists_nat_gt ((2 + τ) / |(∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ)) - (∫ x, φ x ∂μ₀ +
      ∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s))|)
    have := key k
    rw [div_lt_iff₀ hcon] at hk
    have h3 : (2 + τ) / ((k : ℝ) + 1) < |(∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ)) - (∫ x, φ x ∂μ₀ +
      ∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s))| := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith) (abs_nonneg _)))

end WeakC2

end HRS

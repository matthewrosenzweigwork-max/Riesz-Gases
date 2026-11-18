import HRS.MC.E213U14a

/-!
# Packet e213u14 (part b): the far estimates for the canonical Gaussian data

* `u14_block_far`: far weighted integral `≤ ∑_k w_k Y_k` from per-block bounds.
* `u14_drift_gauss`, `u14_J_gauss`: `|E rsA(far part of ℬ)|`, `|E rsJ(far part of η)|` `≤ K e^{-c Rw}`.
* `far_gauss_proof`: the relocated statement of `HRS.MC.E213Plan.far_gauss`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U14

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11 HRS.MC.E213U12

variable {d : ℕ}

theorem u14_block_far (φ : ℝ → ℝ) (hφ0 : ∀ v, 0 ≤ φ v) {c a Rw : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hRw : 0 ≤ Rw)
    (hφ : IntegrableOn φ (Set.Icc 0 (⌈max (a - Rw) 0⌉₊ : ℝ))) (Y : ℕ → ℝ)
    (hY : ∀ k : ℕ, ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x ≤ Y k) (s : Set ℝ) (hs : s ⊆ Set.Ioc 0 (max (a - Rw) 0)) :
    ∫ v in s, Real.exp (-c * (a - v)) * φ v ≤
      ∑ k ∈ Finset.range ⌈max (a - Rw) 0⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) * Y k := by
  set b := max (a - Rw) 0 with hb
  set n := ⌈b⌉₊ with hn
  have hbn : b ≤ n := Nat.le_ceil b
  have hg : Continuous fun v : ℝ => Real.exp (-c * (a - v)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hfi : IntegrableOn (fun v => Real.exp (-c * (a - v)) * φ v) (Set.Icc 0 (n : ℝ)) :=
    IntegrableOn.continuousOn_mul hg.continuousOn hφ isCompact_Icc
  have hsub : Set.Ioc 0 b ⊆ Set.Icc 0 (n : ℝ) := fun v hv => ⟨hv.1.le, hv.2.trans hbn⟩
  have h1 : ∫ v in s, Real.exp (-c * (a - v)) * φ v ≤ ∫ v in Set.Ioc 0 b, Real.exp (-c * (a - v)) * φ v :=
    setIntegral_mono_set (hfi.mono_set hsub)
      (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (hφ0 v))
      (HasSubset.Subset.eventuallyLE hs)
  refine h1.trans ((u11_weighted_block φ hφ0 n hφ c a b hc.le hbn).trans ?_)
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (hY k) (Real.exp_pos _).le

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u14_drift_gauss (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (Rw : ℝ), 0 ≤ Rw → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
      |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀| ≤ K * Real.exp (-c * Rw) := by
  obtain ⟨C₁, c, hC₁, hc, hD⟩ := u12_drift_far_bound hE T hT
  obtain ⟨CB, hCB0, hCB⟩ := u11_B_moment gd 1 one_pos 1 le_rfl
  have hA : 0 < Real.exp (2 * c) / (Real.exp c - 1) := by
    have hn0 : 1 < Real.exp c := by have := Real.add_one_lt_exp hc.ne'; linarith
    have : 0 < Real.exp c - 1 := by linarith
    positivity
  refine ⟨C₁ * (Real.exp (2 * c) / (Real.exp c - 1) * CB) + 1, c, by positivity, hc, ?_⟩
  intro a ha Rw hRw Φ hΦ
  have hY := fun k : ℕ => hCB k (Nat.cast_nonneg k)
  have hb0 : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hH : 0 < a + T := by linarith
  set b := max (a - Rw) 0 with hb
  set n := ⌈b⌉₊ with hn
  have hbn : b ≤ n := Nat.le_ceil b
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have key := u14_expect_bound gd.P₀
    (G := fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
      (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))))
    (Y := fun k ω => ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖) (fun k ω => norm_nonneg _)
    (fun k => by simpa [Real.rpow_one] using (hY k).2.1) CB
    (fun k => by simpa [Real.rpow_one] using (hY k).2.2) hc ha hRw hC₁.le ?_
  · refine key.trans ?_
    have h1 : C₁ * (Real.exp (2 * c) / (Real.exp c - 1) * CB) * Real.exp (-c * Rw) ≤
        (C₁ * (Real.exp (2 * c) / (Real.exp c - 1) * CB) + 1) * Real.exp (-c * Rw) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    exact h1
  · filter_upwards [u11_B_integrable gd ((n : ℝ) + 1) hn1, u11_B_integrable gd (a + T) hH, u11_B_blocks gd]
      with ω hint hint2 hblk
    have hbd := hD a ha Φ hΦ (gd.Zwin (a + T) 0 ω) (fun v => gd.B v ω) (u11_B_nearCoef_measurable gd ω) hint2
      (fun v => NegSobolev.embed m (gd.B v ω)) (fun v _ => rfl) b hb0 hba
    refine hbd.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
    refine u14_block_far (fun v => ‖gd.B v ω‖) (fun v => norm_nonneg _) hc ha hRw
      (hint.mono_set (Set.Icc_subset_Icc le_rfl (by linarith))) _
      (fun k => u11_block_integral_le (fun v => gd.B v ω) k (hblk k)) _ ?_
    intro v hv
    exact ⟨hv.1.1, (Set.mem_Iio.1 hv.2).le⟩

theorem u14_continuousOn_Ici {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (h : ∀ L : ℕ, ContinuousOn f (Set.Icc 0 (L : ℝ))) : ContinuousOn f (Set.Ici 0) := by
  intro x hx
  obtain ⟨L, hL⟩ := exists_nat_gt x
  refine (h L x ⟨hx, hL.le⟩).mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin]
  exact ⟨Set.Iio (L : ℝ), isOpen_Iio, hL, fun y hy => ⟨hy.2, hy.1.le⟩⟩

theorem u14_nearCoef_meas_of_continuousOn {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : ℝ → E} (h : ContinuousOn f (Set.Ici 0)) : Measurable (nearCoef 0 f) := by
  classical
  have : nearCoef 0 f = (Set.Ici (0 : ℝ)).piecewise f (fun _ => 0) := by
    funext u
    simp only [nearCoef, Set.piecewise, Set.mem_Ici]
  rw [this]
  exact h.measurable_piecewise continuousOn_const measurableSet_Ici

theorem u14_J_gauss (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (Rw : ℝ), 0 ≤ Rw → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
      |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀| ≤ K * Real.exp (-c * Rw) := by
  obtain ⟨C₂, c, hC₂, hc, hJ⟩ := u12_J_far_bound hE T hT
  obtain ⟨CY, hCY0, hCY⟩ := u11_eta_moment gd 1 one_pos 1 le_rfl
  have hA : 0 < Real.exp (2 * c) / (Real.exp c - 1) := by
    have hn0 : 1 < Real.exp c := by have := Real.add_one_lt_exp hc.ne'; linarith
    have : 0 < Real.exp c - 1 := by linarith
    positivity
  refine ⟨C₂ * (Real.exp (2 * c) / (Real.exp c - 1) * CY) + 1, c, by positivity, hc, ?_⟩
  intro a ha Rw hRw Φ hΦ
  have hY := fun k : ℕ => hCY k (Nat.cast_nonneg k)
  have hb0 : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  set b := max (a - Rw) 0 with hb
  set n := ⌈b⌉₊ with hn
  have hbn : b ≤ n := Nat.le_ceil b
  have key := u14_expect_bound gd.P₀
    (G := fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
      (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))))
    (Y := fun k ω => ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖) (fun k ω => norm_nonneg _)
    (fun k => by simpa [Real.rpow_one] using (hY k).2.1) CY
    (fun k => by simpa [Real.rpow_one] using (hY k).2.2) hc ha hRw hC₂.le ?_
  · refine key.trans ?_
    have h1 : C₂ * (Real.exp (2 * c) / (Real.exp c - 1) * CY) * Real.exp (-c * Rw) ≤
        (C₂ * (Real.exp (2 * c) / (Real.exp c - 1) * CY) + 1) * Real.exp (-c * Rw) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    exact h1
  · filter_upwards [ae_all_iff.2 (fun L : ℕ => u11_eta_cont gd (L : ℝ))] with ω hcL
    have hcI : ContinuousOn (fun t => gd.η t ω) (Set.Ici 0) := u14_continuousOn_Ici hcL
    have hzm : Measurable (nearCoef 0 (fun v => gd.η v ω)) := u14_nearCoef_meas_of_continuousOn hcI
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a + T)).exists_bound_of_continuousOn
      (hcI.mono Set.Icc_subset_Ici_self)
    have hbd := hJ a ha Φ hΦ (gd.Zwin (a + T) 0 ω) (fun v => gd.η v ω) hzm M hM
      (fun v => NegSobolev.embed m (gd.η v ω)) (fun v _ => rfl) b hb0 hba
    refine hbd.trans (mul_le_mul_of_nonneg_left ?_ hC₂.le)
    have hφc : ContinuousOn (fun v => ‖gd.η v ω‖) (Set.Icc 0 (n : ℝ)) :=
      (hcI.mono Set.Icc_subset_Ici_self).norm
    refine u14_block_far (fun v => ‖gd.η v ω‖) (fun v => norm_nonneg _) hc ha hRw
      hφc.integrableOn_Icc _ (fun k => ?_) _ ?_
    · have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
      have hcK : ContinuousOn (fun t => gd.η t ω) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) :=
        (hcI.mono (fun x hx => le_trans (Nat.cast_nonneg k) hx.1))
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k : ℝ)) (b := (k : ℝ) + 1)
        (f := fun v => ‖gd.η v ω‖) (C := ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖) (fun x hx => by
          rw [norm_norm]
          rw [Set.uIoc_of_le hkk] at hx
          exact u11_procWin_norm_ge gd.η 1 (k : ℝ) ω hcK zero_le_one ⟨hx.1.le, hx.2⟩)
      have h2 : |(k : ℝ) + 1 - k| = 1 := by rw [add_sub_cancel_left]; exact abs_one
      rw [h2, mul_one] at h1
      exact (Real.le_norm_self _).trans h1
    · intro v hv
      exact ⟨hv.1.1, (Set.mem_Iio.1 hv.2).le⟩

/-- **Far window, Gaussian limit** (statement of `HRS.MC.E213Plan.far_gauss`, verbatim). -/
theorem far_gauss_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (Rw : ℝ), 0 ≤ Rw → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
      |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀| +
      (1 / 2) * |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀| ≤ C * Real.exp (-c * Rw) := by
  obtain ⟨K₁, c₁, hK₁, hc₁, h₁⟩ := u14_drift_gauss hE gd T hT
  obtain ⟨K₂, c₂, hK₂, hc₂, h₂⟩ := u14_J_gauss hE gd T hT
  refine ⟨K₁ + K₂, min c₁ c₂, by positivity, lt_min hc₁ hc₂, ?_⟩
  intro a ha Rw hRw Φ hΦ
  have e₁ : Real.exp (-c₁ * Rw) ≤ Real.exp (-(min c₁ c₂) * Rw) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c₁ c₂])
  have e₂ : Real.exp (-c₂ * Rw) ≤ Real.exp (-(min c₁ c₂) * Rw) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c₁ c₂])
  have b₁ := h₁ a ha Rw hRw Φ hΦ
  have b₂ := h₂ a ha Rw hRw Φ hΦ
  have p := Real.exp_pos (-(min c₁ c₂) * Rw)
  nlinarith [mul_le_mul_of_nonneg_left e₁ hK₁.le, mul_le_mul_of_nonneg_left e₂ hK₂.le]

end HRS.MC.E213U14

end

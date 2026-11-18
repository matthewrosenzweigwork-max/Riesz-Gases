import HRS.MC.E213U11g

/-!
# Packet e213u11, file h: pointwise block bound for the window covariance tensor `J_a`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section JPointwise

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u11_J_pointwise (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ K₁ K₂ c : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ᵐ ω ∂gd.P₀,
      ‖gd.Jwin T a ω‖ ≤ K₁ * ‖procWin (rLvl d) (T + 1) (max (a - 1) 0) gd.η ω‖ +
        K₂ * ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) *
          ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖ := by
  obtain ⟨K₁, K₂, c, hK₁, hK₂, hc, hbd⟩ := u11_winJ_bound (S := S) (β₀ := β₀) hE T hT
  refine ⟨K₁, K₂, c, hK₁, hK₂, hc, fun a ha => ?_⟩
  have hL0 : (0 : ℝ) ≤ a + T + 1 := by linarith
  obtain ⟨Λ, hΛ⟩ := u11_exists_Lambda (S := S) (β₀ := β₀) hE T hT a ha hL0 (by linarith)
  have heq := u11_Jwin_eq gd T hT a ha Λ hΛ
  filter_upwards [heq, u11_eta_cont gd (a + T + 1)] with ω hJ hc0
  set L : ℝ := a + T + 1 with hL
  set w := procWin (rLvl d) L 0 gd.η ω with hw
  rw [hJ, hΛ]
  set b : ℝ := max (a - 1) 0 with hb
  have hb0 : 0 ≤ b := le_max_right _ _
  have hba : b ≤ a := max_le (by linarith) ha
  have hab : a ≤ b + 1 := by have : a - 1 ≤ b := le_max_left _ _; linarith
  have hcont0 : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (0 + L)) := by simpa using hc0
  have hcpv : ∀ v ∈ Set.Icc (0 : ℝ) L, u11_cp hL0 w v = gd.η v ω := fun v hv => by
    rw [u11_cp_of_mem hL0 w hv, hw, u11_procWin_at gd.η L 0 ω hcont0 hL0 ⟨v, hv⟩]
    simp
  have hcb : ContinuousOn (fun t => gd.η t ω) (Set.Icc b (b + (T + 1))) :=
    hc0.mono (Set.Icc_subset_Icc hb0 (by linarith))
  have hnear : ∀ v ∈ Set.Icc b (a + T), ‖u11_cp hL0 w v‖ ≤ ‖procWin (rLvl d) (T + 1) b gd.η ω‖ := by
    intro v hv
    rw [hcpv v ⟨hb0.trans hv.1, by linarith [hv.2]⟩]
    exact u11_procWin_norm_ge gd.η (T + 1) b ω hcb (by linarith) ⟨hv.1, by linarith [hv.2]⟩
  obtain ⟨-, hn⟩ := hbd a ha (u11_cp hL0 w) (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w))
    ‖w‖ _ (u11_cp_bounds hL0 w _ _) hnear
  refine hn.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hK₂.le))
  have hcpc := u11_cp_continuous hL0 w
  set φ : ℝ → ℝ := fun v => ‖u11_cp hL0 w v‖ with hφ
  have hφc : Continuous φ := hcpc.norm
  have hgc : Continuous fun v : ℝ => Real.exp (-c * (a - v)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hn' : (0 : ℝ) < (⌈a + T⌉₊ : ℝ) := by
    have : 0 < ⌈a + T⌉₊ := Nat.ceil_pos.2 (by linarith)
    exact_mod_cast this
  have hHn : a + T ≤ (⌈a + T⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈a + T⌉₊ : ℝ) < a + T + 1 := Nat.ceil_lt_add_one (by linarith)
  have s1 : ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, Real.exp (-c * (a - v)) * ‖u11_cp hL0 w v‖ ≤
      ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * φ v :=
    setIntegral_mono_set ((hgc.mul hφc).integrableOn_Ioc)
      (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (HasSubset.Subset.eventuallyLE Set.inter_subset_left)
  refine s1.trans ((u11_weighted_block φ (fun v => norm_nonneg _) ⌈a + T⌉₊ hφc.integrableOn_Icc c a (a + T) hc.le
    hHn).trans (Finset.sum_le_sum fun k hk => ?_))
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hk1 : (k : ℝ) + 1 ≤ ⌈a + T⌉₊ := by exact_mod_cast Finset.mem_range.1 hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hckk : ContinuousOn (fun t => gd.η t ω) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) :=
    hc0.mono (Set.Icc_subset_Icc hk0 (by linarith))
  have hbl : ∀ x ∈ Set.uIoc (k : ℝ) ((k : ℝ) + 1), ‖φ x‖ ≤ ‖procWin (rLvl d) 1 (k : ℝ) gd.η ω‖ := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxL : x ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simp only [hφ, norm_norm]
    rw [hcpv x hxL]
    exact u11_procWin_norm_ge gd.η 1 (k : ℝ) ω hckk zero_le_one ⟨hx.1.le, hx.2⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbl
  rw [abs_of_nonneg (by linarith), show (k : ℝ) + 1 - k = 1 by ring, mul_one] at this
  exact (Real.le_norm_self _).trans this

end JPointwise

end HRS.MC.E213U11

end

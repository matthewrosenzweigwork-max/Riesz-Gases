import HRS.MC.E213U11f

/-!
# Packet e213u11, file g: pointwise block bound for the window drift `D_a`

`‖D_a‖ ≤ K ∑_{k<⌈a+T⌉} e^{-c(a-k-1)} ‖ℬ‖_{L²([k,k+1])}` almost surely.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- Block decomposition of an exponentially weighted integral. -/
theorem u11_weighted_block (φ : ℝ → ℝ) (hφ0 : ∀ v, 0 ≤ φ v) (n : ℕ)
    (hφ : IntegrableOn φ (Set.Icc 0 (n : ℝ))) (c a H : ℝ) (hc : 0 ≤ c) (hH : H ≤ n) :
    ∫ v in Set.Ioc 0 H, Real.exp (-c * (a - v)) * φ v ≤
      ∑ k ∈ Finset.range n, Real.exp (-c * (a - ((k : ℝ) + 1))) * ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x := by
  have hg : Continuous fun v : ℝ => Real.exp (-c * (a - v)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hfi : IntegrableOn (fun v => Real.exp (-c * (a - v)) * φ v) (Set.Icc 0 (n : ℝ)) :=
    IntegrableOn.continuousOn_mul hg.continuousOn hφ isCompact_Icc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have s1 : ∫ v in Set.Ioc 0 H, Real.exp (-c * (a - v)) * φ v ≤
      ∫ v in Set.Ioc 0 (n : ℝ), Real.exp (-c * (a - v)) * φ v :=
    setIntegral_mono_set (hfi.mono_set Set.Ioc_subset_Icc_self)
      (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (hφ0 v))
      (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Ioc_right hH))
  have hint : ∀ k < n, IntervalIntegrable (fun v => Real.exp (-c * (a - v)) * φ v) volume
      ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    simp only [Nat.cast_add, Nat.cast_one]
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hfi.mono_set (Set.Icc_subset_Icc (Nat.cast_nonneg k) hk')
  have s2 := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun v => Real.exp (-c * (a - v)) * φ v) (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := n) hint
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at s2
  rw [intervalIntegral.integral_of_le hn0] at s2
  refine s1.trans (s2.symm.le.trans ?_)
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hk
  have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hφi : IntervalIntegrable φ volume (k : ℝ) ((k : ℝ) + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hkk]
    exact hφ.mono_set (Set.Icc_subset_Icc (Nat.cast_nonneg k) hk')
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hkk ?_ (hφi.const_mul _) fun x hx => ?_
  · have := hint k (Finset.mem_range.1 hk)
    simpa only [Nat.cast_add, Nat.cast_one] using this
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc (sub_nonneg.2 hx.2)])) (hφ0 x)

/-- The integral of `‖f‖` over the unit block `[k,k+1]` is bounded by the `L²` norm of the shifted block. -/
theorem u11_block_integral_le {r : ℝ} (f : ℝ → NegSobolev d r) (k : ℕ)
    (h : MemLp (fun t => f ((k : ℝ) + t)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ x in (k : ℝ)..((k : ℝ) + 1), ‖f x‖ ≤ ‖toL2 r 1 (fun t => f ((k : ℝ) + t))‖ := by
  have h1 := intervalIntegral.integral_comp_add_left (a := 0) (b := 1) (fun x => ‖f x‖) (k : ℝ)
  simp only [add_zero] at h1
  rw [← h1, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact u11_cs_unit h

section DBound

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u11_B_blocks : ∀ᵐ ω ∂gd.P₀, ∀ k : ℕ,
    MemLp (fun t => gd.B ((k : ℝ) + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [ae_all_iff]
  intro k
  exact gd.B_L2 1 one_pos (k : ℝ) (Nat.cast_nonneg k)

theorem u11_D_pointwise (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ᵐ ω ∂gd.P₀,
      ‖gd.Dwin T a ω‖ ≤ K * ∑ k ∈ Finset.range ⌈a + T⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) *
        ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖ := by
  obtain ⟨K, c, hK, hc, hbd⟩ := u11_winDrift_bound (S := S) (β₀ := β₀) hE T hT
  refine ⟨K, c, hK, hc, fun a ha => ?_⟩
  have hn : (0 : ℝ) < (⌈a + T⌉₊ : ℝ) := by
    have : 0 < ⌈a + T⌉₊ := Nat.ceil_pos.2 (by linarith)
    exact_mod_cast this
  have hHn : a + T ≤ (⌈a + T⌉₊ : ℝ) := Nat.le_ceil _
  filter_upwards [u11_B_integrable gd (⌈a + T⌉₊ : ℝ) hn, u11_B_blocks gd] with ω hint hblk
  have hint' : IntegrableOn (fun v => ‖gd.B v ω‖) (Set.Icc 0 (a + T)) :=
    hint.mono_set (Set.Icc_subset_Icc le_rfl hHn)
  have h1 := hbd a ha (fun v => gd.B v ω) (u11_B_nearCoef_measurable gd ω) hint'
  unfold GaussData.Dwin
  rw [dif_pos ha]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK.le)
  refine (u11_weighted_block (fun v => ‖gd.B v ω‖) (fun v => norm_nonneg _) ⌈a + T⌉₊ hint c a (a + T) hc.le hHn).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (u11_block_integral_le (fun v => gd.B v ω) k (hblk k)) (Real.exp_pos _).le

end DBound

end HRS.MC.E213U11

end

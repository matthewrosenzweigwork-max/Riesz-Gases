import HRS.MS.SuppU2Aux6

/-!
# U2 auxiliary 7: a refined kernel integral bound, the radial cutoff and the far part `h_2`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_kerInt_W {κ : Euc d → ℝ} {a : ℝ} (hker : U2Ker κ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 ≤ W → ∀ w : Euc d → ℝ, AEStronglyMeasurable w volume →
      (∀ z, 0 ≤ w z) → (∀ z, w z ≤ W) → Integrable w volume →
      Integrable (fun z => ‖κ z‖ * w z) volume ∧
        ∫ z, ‖κ z‖ * w z ≤ C * (W + ∫ z, w z) := by
  obtain ⟨C0, hC0, hb⟩ := hker.bound
  set Φ : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-a)) with hΦ
  have hΦi : Integrable Φ volume := (integrable_indicator_iff measurableSet_ball).2 hker.integ
  have hΦ0 : ∀ z, 0 ≤ Φ z := fun z => by
    rw [hΦ]; exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z
  refine ⟨C0 * ((∫ z, Φ z) + 1), mul_nonneg hC0 (by linarith [u2_integral_nonneg hΦ0]), ?_⟩
  intro W hW w hwm hw0 hwW hwi
  have hpt : ∀ᵐ z : Euc d ∂volume, ‖κ z‖ * w z ≤ C0 * (Φ z * W + w z) := by
    filter_upwards [u2_ae_ne_zero hker.d_pos] with z hz
    have h1 := hb z hz
    rw [Real.norm_eq_abs]
    by_cases hz1 : ‖z‖ < 1
    · have hΦz : Φ z = ‖z‖ ^ (-a) := by
        rw [hΦ]; exact Set.indicator_of_mem (by simpa using hz1) _
      have h2 : |κ z| * w z ≤ C0 * ‖z‖ ^ (-a) * W :=
        mul_le_mul h1 (hwW z) (hw0 z) (by positivity)
      rw [hΦz]
      nlinarith [hw0 z, Real.rpow_nonneg (norm_nonneg z) (-a)]
    · push Not at hz1
      have h2 : ‖z‖ ^ (-a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith [hker.a_nonneg])
      have h3 : |κ z| ≤ C0 := h1.trans (by nlinarith)
      have h4 : |κ z| * w z ≤ C0 * w z := mul_le_mul_of_nonneg_right h3 (hw0 z)
      nlinarith [hΦ0 z, hw0 z, mul_nonneg (hΦ0 z) hW]
  have hbi : Integrable (fun z => C0 * (Φ z * W + w z)) volume :=
    ((hΦi.mul_const W).add hwi).const_mul C0
  have hmeas : AEStronglyMeasurable (fun z => ‖κ z‖ * w z) volume :=
    hker.meas.norm.aestronglyMeasurable.mul hwm
  have hint : Integrable (fun z => ‖κ z‖ * w z) volume := by
    refine hbi.mono' hmeas ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw0 z))]
    exact hz
  refine ⟨hint, ?_⟩
  have h1 : ∫ z, ‖κ z‖ * w z ≤ ∫ z, C0 * (Φ z * W + w z) :=
    integral_mono_ae hint hbi hpt
  rw [integral_const_mul, integral_add (hΦi.mul_const W) hwi, integral_mul_const] at h1
  have h2 : 0 ≤ ∫ z, Φ z := u2_integral_nonneg hΦ0
  have h3 : 0 ≤ ∫ z, w z := u2_integral_nonneg hw0
  refine h1.trans ?_
  have : (∫ z, Φ z) * W + ∫ z, w z ≤ ((∫ z, Φ z) + 1) * (W + ∫ z, w z) := by
    nlinarith [mul_nonneg h2 h3]
  nlinarith

/-- The radial cutoff `ν = 0` near `0`, `ν = 1` outside `B(0,1/2)`, all derivatives bounded. -/
structure U2Cut (ν : Euc d → ℝ) : Prop where
  cd : ∀ n : ℕ, ContDiff ℝ n ν
  one : ∀ w : Euc d, 1 / 2 < ‖w‖ → ν w = 1
  zero : ∀ w : Euc d, ‖w‖ < 1 / 4 → ∀ i : ℕ, iteratedFDeriv ℝ i ν w = 0
  bd : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ w : Euc d, ‖iteratedFDeriv ℝ i ν w‖ ≤ B

lemma u2_exists_cutoff (d : ℕ) : ∃ ν : Euc d → ℝ, U2Cut ν := by
  let f : ContDiffBump (0 : Euc d) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨fun y => 1 - f y, ?_, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_const.sub f.contDiff
  · intro w hw
    have : f w = 0 := f.zero_of_le_dist (by show (1 / 2 : ℝ) ≤ dist w 0; rw [dist_zero_right]; exact hw.le)
    simp [this]
  · intro w hw i
    have hmem : w ∈ ball (0 : Euc d) f.rIn := by
      rw [mem_ball_zero_iff]; exact hw
    have h1 : f =ᶠ[𝓝 w] 1 := f.eventuallyEq_one_of_mem_ball hmem
    have h2 : (fun y => 1 - f y) =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      filter_upwards [h1] with y hy
      simp [hy]
    have h3 := (h2.iteratedFDeriv ℝ i).eq_of_nhds
    rw [h3]
    rw [iteratedFDeriv_fun_zero]
    rfl
  · intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · refine ⟨1, zero_le_one, fun w => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      have h0 : 0 ≤ f w := f.nonneg
      have h1 : f w ≤ 1 := f.le_one
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · have hc : Continuous fun x => ‖iteratedFDeriv ℝ i f x‖ :=
        (f.contDiff.continuous_iteratedFDeriv' (m := i)).norm
      have hcs : HasCompactSupport fun x => ‖iteratedFDeriv ℝ i f x‖ :=
        (f.hasCompactSupport.iteratedFDeriv i).norm
      obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcs
      refine ⟨max B 0, le_max_right _ _, fun w => ?_⟩
      have h1 : iteratedFDeriv ℝ i (fun y => 1 - f y) w = - iteratedFDeriv ℝ i f w := by
        have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (f := fun _ : Euc d => (1 : ℝ))
          (g := f) (x := w) contDiffAt_const f.contDiffAt
        have h2 : iteratedFDeriv ℝ i (fun _ : Euc d => (1 : ℝ)) w = 0 := by
          rw [iteratedFDeriv_const_of_ne hi.ne']; rfl
        rw [show (fun y : Euc d => 1 - f y) = (fun _ : Euc d => (1 : ℝ)) - f from rfl, this, h2,
          zero_sub]
      rw [h1, norm_neg]
      have := hB w
      simp only [norm_norm] at this
      exact this.trans (le_max_left _ _)

/-- The far part `h_2 = ν(·/R) h`. -/
def u2_h2 (ν : Euc d → ℝ) (R : ℝ) (h : Euc d → ℝ) : Euc d → ℝ := fun y => ν (R⁻¹ • y) * h y

lemma u2_h2_dec {ν : Euc d → ℝ} (hν : U2Cut ν) (k : ℕ) :
    ∃ BB : ℝ, 0 ≤ BB ∧ ∀ (L A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec k L A h → ∀ R : ℝ, 1 ≤ R →
      ContDiff ℝ k (u2_h2 ν R h) ∧ ∀ m ≤ k, ∀ y : Euc d,
        ‖iteratedFDeriv ℝ m (u2_h2 ν R h) y‖ ≤ if R / 4 ≤ ‖y‖ then BB * A * u2Wt L y else 0 := by
  choose B hB0 hB using hν.bd
  refine ⟨2 ^ k * ∑ i ∈ Finset.range (k + 1), B i,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hB0 i), ?_⟩
  intro L A h hA hdec R hR
  have hR0 : 0 < R := by linarith
  have hcs : ContDiff ℝ k (fun z : Euc d => ν (R⁻¹ • z)) :=
    (hν.cd k).comp (contDiff_const_smul R⁻¹)
  refine ⟨hcs.mul hdec.1, fun m hm y => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun z : Euc d => ν (R⁻¹ • z)) (g := h)
    (N := (k : ℕ∞ω)) hcs hdec.1 y (n := m) (by exact_mod_cast hm)
  have hνR : ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun z : Euc d => ν (R⁻¹ • z)) y‖ ≤
      if R / 4 ≤ ‖y‖ then B i else 0 := by
    intro i hi
    rw [iteratedFDeriv_comp_const_smul R⁻¹ (hν.cd i)]
    beta_reduce
    by_cases hy : R / 4 ≤ ‖y‖
    · rw [if_pos hy, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
      have h1 : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_pos.mpr hR0).le (inv_le_one_of_one_le₀ hR)
      calc (R⁻¹) ^ i * ‖iteratedFDeriv ℝ i ν (R⁻¹ • y)‖ ≤ 1 * B i :=
            mul_le_mul h1 (hB i _) (norm_nonneg _) zero_le_one
        _ = B i := one_mul _
    · rw [if_neg hy]
      have : ‖R⁻¹ • y‖ < 1 / 4 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
        push Not at hy
        calc R⁻¹ * ‖y‖ < R⁻¹ * (R / 4) := mul_lt_mul_of_pos_left hy (inv_pos.mpr hR0)
          _ = 1 / 4 := by field_simp
      rw [hν.zero _ this i]
      simp
  by_cases hy : R / 4 ≤ ‖y‖
  · rw [if_pos hy]
    refine hmul.trans ?_
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : Euc d => ν (R⁻¹ • z)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) h y‖ ≤ (2 ^ k * B i) * (A * u2Wt L y) := by
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 := hνR i (by omega)
      rw [if_pos hy] at h1
      have h2 := hdec.2 (m - i) (by omega) y
      have h3 : (m.choose i : ℝ) ≤ 2 ^ k := by
        have : m.choose i ≤ 2 ^ m := Nat.choose_le_two_pow m i
        have h4 : (2 : ℕ) ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hm
        exact_mod_cast this.trans h4
      have hn1 : 0 ≤ ‖iteratedFDeriv ℝ i (fun z : Euc d => ν (R⁻¹ • z)) y‖ := norm_nonneg _
      have hn2 : 0 ≤ ‖iteratedFDeriv ℝ (m - i) h y‖ := norm_nonneg _
      calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : Euc d => ν (R⁻¹ • z)) y‖ *
            ‖iteratedFDeriv ℝ (m - i) h y‖ ≤ (2 ^ k) * (B i) * (A * u2Wt L y) := by
            refine mul_le_mul (mul_le_mul h3 h1 hn1 (by positivity)) h2 hn2 (by
              have := hB0 i; positivity)
        _ = _ := by ring
    calc _ ≤ ∑ i ∈ Finset.range (m + 1), (2 ^ k * B i) * (A * u2Wt L y) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ i ∈ Finset.range (k + 1), (2 ^ k * B i) * (A * u2Wt L y) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) (fun i _ _ => ?_)
          have := hB0 i
          have := u2Wt_pos (d := d) L y
          positivity
      _ = (2 ^ k * ∑ i ∈ Finset.range (k + 1), B i) * A * u2Wt L y := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  · rw [if_neg hy]
    have : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : Euc d => ν (R⁻¹ • z)) y‖ *
          ‖iteratedFDeriv ℝ (m - i) h y‖ = 0 := by
      intro i hi
      have h1 := hνR i (by have := Finset.mem_range.mp hi; omega)
      rw [if_neg hy] at h1
      have : ‖iteratedFDeriv ℝ i (fun z : Euc d => ν (R⁻¹ • z)) y‖ = 0 :=
        le_antisymm h1 (norm_nonneg _)
      simp [this]
    rw [Finset.sum_eq_zero this] at hmul
    exact hmul

end HRS.Whole

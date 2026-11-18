import HRS.MS.S82RK1
import HRS.MS.S82P2Mom

/-!
# S8.2 R01A (S82R): the heat cutoff `qTau d s tau` is a `ShortRangePole` (`s = d/2`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.MS.Psd

variable {d : ℕ}

lemma s82r_qTau_measurable (s tau : ℝ) : Measurable (qTau d s tau) := by
  have hm : Measurable (fun p : Euc d × ℝ => psd3_F d s p.2 p.1) :=
    (psd3_F_meas (d := d) s).comp measurable_swap
  have := hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 tau))
  exact this.measurable

lemma s82r_psd3_F_neg (s t : ℝ) (x : Euc d) : psd3_F d s t (-x) = psd3_F d s t x := by
  unfold psd3_F heatKerE
  simp [norm_neg]

lemma s82r_qTau_even (s tau : ℝ) (x : Euc d) : qTau d s tau (-x) = qTau d s tau x := by
  unfold qTau
  simp_rw [s82r_psd3_F_neg]

lemma s82r_rieszKernel_eq {s : ℝ} (hs : 0 < s) (x : Euc d) :
    HRS.Whole.rieszKernel d s x = ‖x‖ ^ (-s) := by
  unfold HRS.Whole.rieszKernel
  rw [if_neg hs.ne']

lemma s82r_qTau_smooth {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    ContDiffOn ℝ ∞ (qTau d s tau) {z : Euc d | z ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞ (fun z : Euc d => ‖z‖ ^ (-s) - kTau d s tau z) {z : Euc d | z ≠ 0} := by
    refine ContDiffOn.sub ?_ (s82r_kTau_contDiff hs htau).contDiffOn
    intro z hz
    have hz' : z ≠ 0 := hz
    have hn : ContDiffAt ℝ ∞ (fun z : Euc d => ‖z‖) z := contDiffAt_norm ℝ hz'
    exact (hn.rpow_const_of_ne (norm_ne_zero_iff.2 hz')).contDiffWithinAt
  refine h1.congr fun z hz => ?_
  have hz' : z ≠ 0 := hz
  have := riesz_heat_split (d := d) hs htau hz'
  rw [s82r_rieszKernel_eq hs] at this
  linarith

lemma s82r_qTau_near {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧ ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ r →
      c * ‖z‖ ^ (-s) ≤ qTau d s tau z ∧ qTau d s tau z ≤ C * ‖z‖ ^ (-s) := by
  set k0 : ℝ := kTau d s tau 0 with hk0
  have hk0n : 0 ≤ k0 := kTau_nonneg hs htau 0
  set B : ℝ := (2 * k0 + 1) ^ (-(1 / s)) with hB
  have hBpos : 0 < B := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨min 1 B, 1 / 2, 1, lt_min one_pos hBpos, min_le_left _ _, by norm_num, fun z hz hzr => ?_⟩
  have hzB : ‖z‖ ≤ B := hzr.trans (min_le_right _ _)
  have hpow : 2 * k0 + 1 ≤ ‖z‖ ^ (-s) := by
    have h1 : B ^ (-s) ≤ ‖z‖ ^ (-s) := Real.rpow_le_rpow_of_nonpos hz hzB (by linarith)
    have h2 : B ^ (-s) = 2 * k0 + 1 := by
      rw [hB, ← Real.rpow_mul (by linarith)]
      have : -(1 / s) * -s = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hz' : z ≠ 0 := norm_pos_iff.1 hz
  have hsplit := riesz_heat_split (d := d) hs htau hz'
  rw [s82r_rieszKernel_eq hs] at hsplit
  have hk1 := kTau_nonneg hs htau z
  have hk2 := kTau_le_zero hs htau z (τ := tau)
  have hq : qTau d s tau z = ‖z‖ ^ (-s) - kTau d s tau z := by linarith
  constructor
  · rw [hq]; nlinarith
  · rw [hq]; nlinarith

lemma s82r_qTau_far {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ ∀ z : Euc d, r ≤ ‖z‖ → qTau d s tau z ≤ C * Real.exp (-c * ‖z‖ ^ 2) := by
  set A : ℝ := aDS d s * (4 * Real.pi) ^ (-(d : ℝ) / 2) with hA
  have hA0 : 0 ≤ A := by
    have := psd3_aDS_pos (d := d) hs
    rw [hA]; positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s / 2 + 1 ≤ m := exists_nat_ge _
  set Bp : ℝ := A * (8 ^ m * (m.factorial : ℝ)) * tau ^ ((m : ℝ) - s / 2 - 1) with hBp
  have hBp0 : 0 ≤ Bp := by rw [hBp]; positivity
  refine ⟨1, 1 / (8 * tau), tau * Bp, one_pos, by positivity, fun z hz => ?_⟩
  have hv : 1 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) tau, ‖psd3_F d s t z‖ ≤ Bp * Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hF0 := psd3_F_nonneg (d := d) hs ht0.le z
    rw [Real.norm_eq_abs, abs_of_nonneg hF0, psd3_F_eq_gauss ht0 z, psd3_F_zero ht0]
    have hexp : Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) ≤
        Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) * Real.exp (-(1 / (8 * t))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 : 1 / (8 * tau) ≤ 1 / (8 * t) := one_div_le_one_div_of_le (by positivity) (by nlinarith [ht.2])
      have e : -(1 / (4 * t)) * ‖z‖ ^ 2 = -(1 / (8 * t)) * ‖z‖ ^ 2 + -(1 / (8 * t)) * ‖z‖ ^ 2 := by
        field_simp; ring
      rw [e]
      have a1 : 0 ≤ (1 / (8 * t) - 1 / (8 * tau)) * ‖z‖ ^ 2 := mul_nonneg (sub_nonneg.2 h1) (sq_nonneg _)
      have a2 : 0 ≤ (1 / (8 * t)) * (‖z‖ ^ 2 - 1) := mul_nonneg (by positivity) (by linarith)
      linarith
    have hfac : Real.exp (-(1 / (8 * t))) ≤ (m.factorial : ℝ) * (8 * t) ^ m := by
      have h1 := Real.pow_div_factorial_le_exp (x := 1 / (8 * t)) (by positivity) m
      have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
      rw [Real.exp_neg]
      have hy : 0 < (1 / (8 * t)) ^ m / m.factorial := by positivity
      calc (Real.exp (1 / (8 * t)))⁻¹ ≤ ((1 / (8 * t)) ^ m / m.factorial)⁻¹ :=
            inv_anti₀ hy h1
        _ = m.factorial * (8 * t) ^ m := by
            rw [inv_div, one_div, inv_pow, div_inv_eq_mul]
    have hpowle : t ^ (-(s / 2) - 1) * t ^ m ≤ tau ^ ((m : ℝ) - s / 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
      have e : -(s / 2) - 1 + (m : ℝ) = (m : ℝ) - s / 2 - 1 := by ring
      rw [e]
      exact Real.rpow_le_rpow ht0.le ht.2 (by linarith)
    have hmain : A * t ^ (-(s / 2) - 1) * Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) ≤
        Bp * Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) := by
      have hr : 0 ≤ t ^ (-(s / 2) - 1) := Real.rpow_nonneg ht0.le _
      calc A * t ^ (-(s / 2) - 1) * Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2)
          ≤ A * t ^ (-(s / 2) - 1) * (Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) *
              Real.exp (-(1 / (8 * t)))) := by gcongr
        _ ≤ A * t ^ (-(s / 2) - 1) * (Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) *
              ((m.factorial : ℝ) * (8 * t) ^ m)) := by gcongr
        _ = A * (8 ^ m * (m.factorial : ℝ)) * (t ^ (-(s / 2) - 1) * t ^ m) *
              Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) := by rw [mul_pow]; ring
        _ ≤ A * (8 ^ m * (m.factorial : ℝ)) * tau ^ ((m : ℝ) - s / 2 - 1) *
              Real.exp (-(1 / (8 * tau)) * ‖z‖ ^ 2) := by gcongr
    have e2 : aDS d s * (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(s / 2) - 1) *
        Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) =
        A * t ^ (-(s / 2) - 1) * Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) := by rw [hA]
    rw [e2]
    exact hmain
  have hle : qTau d s tau z ≤ ‖qTau d s tau z‖ := le_abs_self _
  refine hle.trans ?_
  unfold qTau
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Set.Ioc (0 : ℝ) tau)
    (f := fun t => psd3_F d s t z) (by simp) hpt
  refine this.trans (le_of_eq ?_)
  have hvol : (volume : Measure ℝ).real (Set.Ioc (0 : ℝ) tau) = tau := by
    simp [Measure.real, htau.le]
  rw [hvol]; ring

theorem s82r_qTau_shortRange (hd : 1 ≤ d) {tau : ℝ} (htau : 0 < tau) :
    HRS.MS.Phase2S82.ShortRangePole d (qTau d (HRS.MS.Phase2S82.criticalS d) tau) := by
  have hs : 0 < HRS.MS.Phase2S82.criticalS d := by
    unfold HRS.MS.Phase2S82.criticalS
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact
    { measurable := s82r_qTau_measurable _ tau
      smooth := s82r_qTau_smooth hs htau
      even := fun z => s82r_qTau_even _ tau z
      nonneg := fun z => qTau_nonneg hs z
      near := s82r_qTau_near hs htau
      far := s82r_qTau_far hs htau }

end HRS.MS.S82R

end

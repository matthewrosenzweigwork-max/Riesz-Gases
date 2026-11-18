import Mathlib

/-!
# Packet L2C-3, helper 1: scalar differential inequalities

Pure real analysis used by the Lyapunov argument for the nonautonomous adjoint propagator:

* `l2c3_core`: if `F' + w ≤ 0` on `(0,T)` (with `F`, `w` continuous on `[0,T]`) then `F τ + ∫_0^τ w ≤ F 0`;
* `l2c3_gronwall_rate`: `F' ≤ (-a + C e^{-2κ(t-σ)}) F` gives `F τ ≤ e^{C/(2κ)} e^{-aτ} F 0`;
* `l2c3_weighted_energy`: `F' ≤ -νE + bF` gives `ν ∫_0^τ e^{a'σ} E ≤ F 0 + (a'+b) ∫_0^τ e^{a'σ} F`;
* `l2c3_duhamel`: `F' ≤ -aF + h` gives `e^{aτ} F τ ≤ F 0 + ∫_0^τ e^{aσ} h`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.L2C3

theorem l2c3_core {T : ℝ} (hT : 0 ≤ T) {F f w : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ σ ∈ Ioo 0 T, HasDerivAt F (f σ) σ) (hle : ∀ σ ∈ Ioo 0 T, f σ + w σ ≤ 0)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    F τ + ∫ σ in (0 : ℝ)..τ, w σ ≤ F 0 := by
  have hwi : IntervalIntegrable w volume 0 T :=
    (hw.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hcont : ContinuousOn (fun b => ∫ σ in (0 : ℝ)..b, w σ) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hwi (a := 0)
      (by rw [uIcc_of_le hT]; exact ⟨le_rfl, hT⟩)
    rwa [uIcc_of_le hT] at this
  have hΨc : ContinuousOn (fun b => F b + ∫ σ in (0 : ℝ)..b, w σ) (Icc 0 T) := hF.add hcont
  have hder : ∀ σ ∈ Ioo 0 T,
      HasDerivAt (fun b => F b + ∫ σ in (0 : ℝ)..b, w σ) (f σ + w σ) σ := by
    intro σ hσ
    refine (hd σ hσ).add ?_
    have hwσ : ContinuousAt w σ := hw.continuousAt (Icc_mem_nhds hσ.1 hσ.2)
    have hsub : IntervalIntegrable w volume 0 σ :=
      (hw.mono (by
        rw [uIcc_of_le hσ.1.le]; exact Icc_subset_Icc le_rfl hσ.2.le)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hsub
      ((hw.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo σ hσ) hwσ
  have hanti : AntitoneOn (fun b => F b + ∫ σ in (0 : ℝ)..b, w σ) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hΨc ?_ ?_
    · intro σ hσ
      rw [interior_Icc] at hσ
      exact (hder σ hσ).differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      rw [(hder σ hσ).deriv]
      exact hle σ hσ
  have := hanti (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) hτ hτ.1
  simpa using this

theorem l2c3_gronwall_rate {T t a C κ : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) (hC : 0 ≤ C) (hκ : 0 < κ)
    {F f : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 T)) (hd : ∀ σ ∈ Ioo 0 T, HasDerivAt F (f σ) σ)
    (hle : ∀ σ ∈ Ioo 0 T, f σ ≤ (-a + C * Real.exp (-2 * κ * (t - σ))) * F σ) (hF0 : 0 ≤ F 0)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    F τ ≤ Real.exp (C / (2 * κ)) * Real.exp (-a * τ) * F 0 := by
  set Φ : ℝ → ℝ := fun σ => -a * σ + (C / (2 * κ)) * Real.exp (-2 * κ * (t - σ)) with hΦ
  have hΦd : ∀ σ, HasDerivAt Φ (-a + C * Real.exp (-2 * κ * (t - σ))) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ : ℝ => -2 * κ * (t - σ)) (2 * κ) σ := by
      have := ((hasDerivAt_id σ).const_sub t).const_mul (-2 * κ)
      simpa using this
    have h2 := (h1.exp).const_mul (C / (2 * κ))
    have h3 := ((hasDerivAt_id σ).const_mul (-a)).add h2
    refine h3.congr_deriv ?_
    field_simp
  set G : ℝ → ℝ := fun σ => Real.exp (-Φ σ) * F σ with hG
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦd x).continuousAt
  have hGc : ContinuousOn G (Icc 0 T) :=
    ((Real.continuous_exp.comp hΦc.neg).continuousOn).mul hF
  have hGd : ∀ σ ∈ Ioo 0 T, HasDerivAt G
      (Real.exp (-Φ σ) * (f σ - (-a + C * Real.exp (-2 * κ * (t - σ))) * F σ)) σ := by
    intro σ hσ
    have h1 : HasDerivAt (fun σ => Real.exp (-Φ σ))
        (Real.exp (-Φ σ) * (-(-a + C * Real.exp (-2 * κ * (t - σ))))) σ :=
      (hΦd σ).neg.exp
    refine (h1.mul (hd σ hσ)).congr_deriv ?_
    ring
  have hcore := l2c3_core hT (F := G) hGc (w := fun _ => 0) continuousOn_const hGd (fun σ hσ => by
    have := mul_le_mul_of_nonneg_left (sub_nonpos.2 (hle σ hσ)) (Real.exp_pos (-Φ σ)).le
    simpa using this) hτ
  simp only [intervalIntegral.integral_zero, add_zero, hG] at hcore
  have h1 : F τ ≤ Real.exp (Φ τ - Φ 0) * F 0 := by
    have h2 := mul_le_mul_of_nonneg_left hcore (Real.exp_pos (Φ τ)).le
    have e1 : Real.exp (Φ τ) * (Real.exp (-Φ τ) * F τ) = F τ := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    have e2 : Real.exp (Φ τ) * (Real.exp (-Φ 0) * F 0) = Real.exp (Φ τ - Φ 0) * F 0 := by
      rw [← mul_assoc, ← Real.exp_add]; ring_nf
    linarith
  refine h1.trans ?_
  have h3 : Φ τ - Φ 0 ≤ C / (2 * κ) + -a * τ := by
    simp only [hΦ]
    have hτt : τ ≤ t := hτ.2.trans hTt
    have e1 : Real.exp (-2 * κ * (t - τ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have e0 : 0 ≤ Real.exp (-2 * κ * (t - 0)) := (Real.exp_pos _).le
    have hCk : 0 ≤ C / (2 * κ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e1 hCk, mul_nonneg hCk e0]
  have h4 : Real.exp (Φ τ - Φ 0) ≤ Real.exp (C / (2 * κ)) * Real.exp (-a * τ) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 h3
  exact mul_le_mul_of_nonneg_right h4 hF0

theorem l2c3_weighted_energy {T a' b ν : ℝ} (hT : 0 ≤ T) {F E f : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 T)) (hE : ContinuousOn E (Icc 0 T))
    (hd : ∀ σ ∈ Ioo 0 T, HasDerivAt F (f σ) σ)
    (hle : ∀ σ ∈ Ioo 0 T, f σ ≤ -ν * E σ + b * F σ) (hFn : ∀ σ ∈ Icc 0 T, 0 ≤ F σ)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    ν * ∫ σ in (0 : ℝ)..τ, Real.exp (a' * σ) * E σ ≤
      F 0 + (a' + b) * ∫ σ in (0 : ℝ)..τ, Real.exp (a' * σ) * F σ := by
  have hexp : Continuous fun σ : ℝ => Real.exp (a' * σ) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFe : ContinuousOn (fun σ => Real.exp (a' * σ) * F σ) (Icc 0 T) :=
    hexp.continuousOn.mul hF
  have hEe : ContinuousOn (fun σ => Real.exp (a' * σ) * E σ) (Icc 0 T) :=
    hexp.continuousOn.mul hE
  have hsub : uIcc 0 τ ⊆ Icc 0 T := by
    rw [uIcc_of_le hτ.1]; exact Icc_subset_Icc le_rfl hτ.2
  have hFi : IntervalIntegrable (fun σ => Real.exp (a' * σ) * F σ) volume 0 τ :=
    (hFe.mono hsub).intervalIntegrable
  have hEi : IntervalIntegrable (fun σ => Real.exp (a' * σ) * E σ) volume 0 τ :=
    (hEe.mono hsub).intervalIntegrable
  have hw : ContinuousOn (fun σ => ν * (Real.exp (a' * σ) * E σ) -
      (a' + b) * (Real.exp (a' * σ) * F σ)) (Icc 0 T) :=
    (hEe.const_smul ν).sub (hFe.const_smul (a' + b))
  have hd' : ∀ σ ∈ Ioo 0 T, HasDerivAt (fun σ => Real.exp (a' * σ) * F σ)
      (Real.exp (a' * σ) * (f σ + a' * F σ)) σ := by
    intro σ hσ
    have h1 : HasDerivAt (fun σ : ℝ => Real.exp (a' * σ)) (Real.exp (a' * σ) * a') σ := by
      simpa using ((hasDerivAt_id σ).const_mul a').exp
    refine (h1.mul (hd σ hσ)).congr_deriv ?_
    ring
  have hcore := l2c3_core hT hFe hw hd' (fun σ hσ => by
    have h := hle σ hσ
    have he := Real.exp_pos (a' * σ)
    have : Real.exp (a' * σ) * (f σ + a' * F σ) + (ν * (Real.exp (a' * σ) * E σ) -
        (a' + b) * (Real.exp (a' * σ) * F σ)) =
        Real.exp (a' * σ) * (f σ + ν * E σ - b * F σ) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos he.le (by linarith)) hτ
  rw [intervalIntegral.integral_sub (hEi.const_mul ν) (hFi.const_mul (a' + b)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hcore
  simp only [mul_zero, Real.exp_zero, one_mul] at hcore
  have hnn : 0 ≤ Real.exp (a' * τ) * F τ := mul_nonneg (Real.exp_pos _).le (hFn τ hτ)
  linarith

theorem l2c3_duhamel {T a : ℝ} (hT : 0 ≤ T) {F f h : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 T)) (hh : ContinuousOn h (Icc 0 T))
    (hd : ∀ σ ∈ Ioo 0 T, HasDerivAt F (f σ) σ)
    (hle : ∀ σ ∈ Ioo 0 T, f σ ≤ -a * F σ + h σ) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    Real.exp (a * τ) * F τ ≤ F 0 + ∫ σ in (0 : ℝ)..τ, Real.exp (a * σ) * h σ := by
  have hexp : Continuous fun σ : ℝ => Real.exp (a * σ) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFe : ContinuousOn (fun σ => Real.exp (a * σ) * F σ) (Icc 0 T) := hexp.continuousOn.mul hF
  have hhe : ContinuousOn (fun σ => Real.exp (a * σ) * h σ) (Icc 0 T) := hexp.continuousOn.mul hh
  have hd' : ∀ σ ∈ Ioo 0 T, HasDerivAt (fun σ => Real.exp (a * σ) * F σ)
      (Real.exp (a * σ) * (f σ + a * F σ)) σ := by
    intro σ hσ
    have h1 : HasDerivAt (fun σ : ℝ => Real.exp (a * σ)) (Real.exp (a * σ) * a) σ := by
      simpa using ((hasDerivAt_id σ).const_mul a).exp
    refine (h1.mul (hd σ hσ)).congr_deriv ?_
    ring
  have hcore := l2c3_core hT hFe (w := fun σ => -(Real.exp (a * σ) * h σ)) hhe.neg hd'
    (fun σ hσ => by
      have h1 := hle σ hσ
      have he := Real.exp_pos (a * σ)
      have : Real.exp (a * σ) * (f σ + a * F σ) + -(Real.exp (a * σ) * h σ) =
          Real.exp (a * σ) * (f σ + a * F σ - h σ) := by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos he.le (by linarith)) hτ
  rw [intervalIntegral.integral_neg] at hcore
  simp only [mul_zero, Real.exp_zero, one_mul] at hcore
  linarith

end HRS.MC.L2C3

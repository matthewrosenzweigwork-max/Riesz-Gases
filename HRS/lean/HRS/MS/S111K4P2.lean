import HRS.MS.S111K4P1
import HRS.Whole.MovtrAux4
import HRS.MS.S111X1E2

/-!
# S11.1 / T03 (S11K4), packet `R26-T6C.P02`: continuity and directional derivative of a Gaussian-source potential
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole

variable {d : ℕ}

/-- The potential `x ↦ ∫ g(x-y) q(y) dy` of a continuous Gaussian-decaying source is continuous. -/
theorem k4_potential_continuous (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {q : Euc d → ℝ} (hqc : Continuous q) (h0 : ∀ y, |q y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) :
    Continuous fun x => ∫ y, rieszKernel d s (x - y) * q y := by
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have hB : ∀ᵐ z : Euc d, |rieszKernel d s z| ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := by
    filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    rw [← movtr_gEps_zero d s]
    exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz
  have hBint := movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)
  have hshift : ∀ x : Euc d, ∫ y, rieszKernel d s (x - y) * q y = ∫ z, rieszKernel d s z * q (x - z) := by
    intro x
    rw [← integral_sub_left_eq_self (fun y => rieszKernel d s (x - y) * q y) volume x]
    simp
  simp_rw [hshift]
  rw [continuous_iff_continuousAt]
  intro x0
  set R : ℝ := ‖x0‖ + 1 with hR
  refine continuousAt_of_dominated (bound := fun z => C * Real.exp (c * R ^ 2) *
    ((2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      hgm.aestronglyMeasurable.mul (hqc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have hball : ∀ᶠ x in 𝓝 x0, ‖x‖ ≤ R := by
      have : Metric.ball x0 1 ∈ 𝓝 x0 := Metric.ball_mem_nhds x0 one_pos
      filter_upwards [this] with x hx
      have := norm_le_norm_add_norm_sub' x x0
      rw [Metric.mem_ball, dist_eq_norm] at hx
      rw [hR]; linarith [norm_sub_norm_le x x0, norm_sub_rev x x0]
    filter_upwards [hball] with x hx
    filter_upwards [hB] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := h0 (x - z)
    have h2 := movtr_gauss_shift hc hx z
    calc |rieszKernel d s z| * |q (x - z)|
        ≤ (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * (C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) := by
          apply mul_le_mul hz (h1.trans (mul_le_mul_of_nonneg_left h2 hC)) (abs_nonneg _)
          exact (abs_nonneg _).trans hz
      _ = _ := by ring
  · exact hBint.const_mul (C * Real.exp (c * R ^ 2))
  · refine Filter.Eventually.of_forall fun z => ?_
    exact (continuous_const.mul (hqc.comp (continuous_id.sub continuous_const))).continuousAt


theorem k4_line_hasDerivAt {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x) (e : Euc d) :
    HasDerivAt (fun t : ℝ => g (x + t • e)) (fderiv ℝ g x e) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hg' : HasFDerivAt g (fderiv ℝ g x) ((fun t : ℝ => x + t • e) 0) := by simpa using hg.hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hg' hl

/-- Pro `R26-T6C.P03`: the pointwise gradient equation `∇h = ∇f - β W[h]` of the smooth screened response. -/
theorem k4_response_gradient (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) (f h : Euc d → ℝ)
    (hf : MemCb 2 f) (hh : MemCb 2 h)
    (hresp : HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h) :
    ∀ x, gradient h x = gradient f x - β • HRS.MS.S111X1.Wf d s ρ h x := by
  obtain ⟨M, T⟩ := HRS.MS.S111X2.s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨C0, c, hC0, hc, hρ0, hρ1⟩ := T.gauss
  obtain ⟨hhc, B0h, B1h, h0h, h1h⟩ := HRS.MS.S111X2.s111x2_cb1_bounds (k4_cb1_of_cb2 hh)
  obtain ⟨hfc, B0f, B1f, h0f, h1f⟩ := HRS.MS.S111X2.s111x2_cb1_bounds (k4_cb1_of_cb2 hf)
  have hd1 : 1 ≤ d := by omega
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hs1 : s + 1 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hB0 : 0 ≤ B0h := (norm_nonneg _).trans (h0h 0)
  have hB1 : 0 ≤ B1h := (norm_nonneg _).trans (h1h 0)
  have hρc1 : ContDiff ℝ 1 ρ := T.en.smooth.of_le (by norm_num)
  set q : Euc d → ℝ := fun y => h y * ρ y with hq
  have hq1 : ContDiff ℝ 1 q := hhc.mul hρc1
  have hhd : Differentiable ℝ h := hhc.differentiable (by norm_num)
  have hρd : Differentiable ℝ ρ := hρc1.differentiable (by norm_num)
  have hq0 : ∀ y, |q y| ≤ (B0h * C0 + B1h * C0) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    simp only [hq, abs_mul]
    have h1 : |h y| ≤ B0h := by simpa using h0h y
    calc |h y| * |ρ y| ≤ B0h * (C0 * Real.exp (-c * ‖y‖ ^ 2)) :=
          mul_le_mul h1 (hρ0 y) (abs_nonneg _) hB0
      _ ≤ _ := by
        have : 0 ≤ Real.exp (-c * ‖y‖ ^ 2) := (Real.exp_pos _).le
        nlinarith [mul_nonneg hB1 (mul_nonneg hC0 this)]
  have hq1b : ∀ y, ‖fderiv ℝ q y‖ ≤ (B0h * C0 + B1h * C0) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    have hfd : fderiv ℝ q y = h y • fderiv ℝ ρ y + ρ y • fderiv ℝ h y :=
      (hhd.differentiableAt.hasFDerivAt.mul hρd.differentiableAt.hasFDerivAt).fderiv
    rw [hfd]
    have h1 : ‖h y‖ ≤ B0h := h0h y
    have h2 : ‖ρ y‖ ≤ C0 * Real.exp (-c * ‖y‖ ^ 2) := by simpa using hρ0 y
    have h3 : ‖fderiv ℝ ρ y‖ ≤ C0 * Real.exp (-c * ‖y‖ ^ 2) := hρ1 y
    have h4 : ‖fderiv ℝ h y‖ ≤ B1h := h1h y
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    calc ‖h y‖ * ‖fderiv ℝ ρ y‖ + ‖ρ y‖ * ‖fderiv ℝ h y‖
        ≤ B0h * (C0 * Real.exp (-c * ‖y‖ ^ 2)) + (C0 * Real.exp (-c * ‖y‖ ^ 2)) * B1h :=
          add_le_add (mul_le_mul h1 h3 (norm_nonneg _) hB0) (mul_le_mul h2 h4 (norm_nonneg _)
            ((norm_nonneg _).trans h2))
      _ = _ := by ring
  have hCq : 0 ≤ B0h * C0 + B1h * C0 := by positivity
  have hΦc : Continuous fun x => ∫ y, rieszKernel d s (x - y) * q y :=
    k4_potential_continuous hd1 hs0 hsd hc hCq hq1.continuous hq0
  -- the directional derivatives of the potential
  have hWf : ∀ x i, HasDerivAt (fun t : ℝ => ∫ y, rieszKernel d s (x + t • (EuclideanSpace.single i (1 : ℝ) : Euc d) - y) * q y)
      ((HRS.MS.S111X1.Wf d s ρ h x) i) 0 := by
    intro x i
    have h1 := movtr_hasDerivAt_potential hd1 hs0 hsd hc hCq hq1 hq0 hq1b x i
    have hK := T.en.K
    have h2 := HRS.MS.S111X1.conv_eq_plain hd1 hs0 hs1 hK.meas hK.nonneg hK.int hK.bdd (h := q)
      hq1.continuous.measurable (Bh := B0h) (fun y => by
        simp only [hq, abs_mul]
        have h1 : |h y| ≤ B0h := by simpa using h0h y
        rw [abs_of_nonneg (hK.nonneg y)]
        exact mul_le_mul_of_nonneg_right h1 (hK.nonneg y)) x
    rw [h2] at h1
    exact h1
  -- the response equation holds everywhere
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  set Φ : Euc d → ℝ := fun x => ∫ y, rieszKernel d s (x - y) * q y with hΦ
  have hKop : ∀ x, HRS.Whole.Kop (rieszKernel d s) μ h x =
      Φ x - HRS.Whole.pair μ (fun x => ∫ y, rieszKernel d s (x - y) * h y ∂μ) := by
    intro x
    unfold HRS.Whole.Kop HRS.Whole.projMean
    congr 1
    beta_reduce
    rw [hμ, HRS.MS.TcR.tc2_integral_nu T.prob]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hq]
    ring
  set c1 : ℝ := HRS.Whole.pair μ (fun x => ∫ y, rieszKernel d s (x - y) * h y ∂μ) with hc1
  set c2 : ℝ := HRS.Whole.pair μ f with hc2
  have hae : ∀ᵐ x ∂μ, h x + β * (Φ x - c1) = f x - c2 := by
    filter_upwards [hresp.2] with x hx
    rw [hKop] at hx
    simpa [HRS.Whole.projMean, hc2] using hx
  have hae' : ∀ᵐ x ∂(volume : Measure (Euc d)), h x + β * (Φ x - c1) = f x - c2 := by
    have hμ' : μ = volume.withDensity fun x => ENNReal.ofReal (ρ x) := rfl
    rw [hμ', ae_withDensity_iff (by exact (T.en.K.meas.ennreal_ofReal))] at hae
    filter_upwards [hae] with x hx
    exact hx (by simpa using T.pos x)
  have hcont1 : Continuous fun x => h x + β * (Φ x - c1) :=
    hhc.continuous.add (continuous_const.mul (hΦc.sub continuous_const))
  have hcont2 : Continuous fun x => f x - c2 := hfc.continuous.sub continuous_const
  have hid : ∀ x, h x + β * (Φ x - c1) = f x - c2 := fun x =>
    congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hcont1 hcont2).1 hae') x
  intro x
  ext i
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hdh := k4_line_hasDerivAt (hhd.differentiableAt (x := x)) e
  have hdf := k4_line_hasDerivAt ((hfc.differentiable (by norm_num)).differentiableAt (x := x)) e
  have hfun : (fun t : ℝ => h (x + t • e) + β * (Φ (x + t • e) - c1)) = fun t => f (x + t • e) - c2 := by
    funext t; exact hid _
  have hW : HasDerivAt (fun t : ℝ => Φ (x + t • e)) ((HRS.MS.S111X1.Wf d s ρ h x) i) 0 := hWf x i
  have hsum : HasDerivAt (fun t : ℝ => h (x + t • e) + β * (Φ (x + t • e) - c1))
      (fderiv ℝ h x e + β * ((HRS.MS.S111X1.Wf d s ρ h x) i)) 0 := hdh.add ((hW.sub_const c1).const_mul β)
  rw [hfun] at hsum
  have huniq := hsum.unique (hdf.sub_const c2)
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [HRS.Whole.movtr_gradient_apply, HRS.Whole.movtr_gradient_apply]
  linarith

end HRS.MS.S111K4

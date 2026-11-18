import HRS.MS.R26T8AO02c

/-!
# S8.2 T8A O02 (part d): `aSource f` is bounded by `Ca A` for `TestBound A f`
`hSource f x y = ⟨∇f x - ∇f y, ∇g(x-y)⟩`, `∇f` is `A ‖Rz‖`-Lipschitz, and `∫ ρ(y) (1+‖x-y‖^(-s)) dy` is bounded uniformly in `x`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o02_grad_lip {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {A : ℝ}
    (hf2 : ∀ w, ‖iteratedFDeriv ℝ 2 f w‖ ≤ A) (x y : Euc d) :
    ‖gradient f x - gradient f y‖ ≤ ‖r26t8a_Rz d‖ * A * ‖x - y‖ := by
  have hf2c : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) f := contDiff_infty.1 hf 2
  have hDf : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf2c.fderiv_right (m := ((1 : ℕ) : WithTop ℕ∞)) (by norm_cast)
  have hDD : ∀ w, DifferentiableAt ℝ (fderiv ℝ f) w := fun w => (hDf.differentiable (by simp)) w
  have hdiff : ∀ w, DifferentiableAt ℝ (gradient f) w := by
    intro w
    rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).differentiableAt.comp w (hDD w)
  have hbd : ∀ w ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (gradient f) w‖ ≤ ‖r26t8a_Rz d‖ * A := by
    intro w _
    refine (r26t8a_fderiv_gradient_le f w (hDD w)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (r26t8a_Rz d))
    have e : ‖fderiv ℝ (fderiv ℝ f) w‖ = ‖iteratedFDeriv ℝ 2 f w‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [e]; exact hf2 w
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := gradient f) (fun w _ => hdiff w) hbd
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  exact this

set_option maxHeartbeats 3200000 in
theorem r26t8a_o02_aSource_bound (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      ∀ x : Euc d, |aSource (HRS.Whole.withDensityReal rho) f x| ≤ Ca * A := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho := (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hρi : Integrable rho := Integrable.of_integral_ne_zero (by rw [hprob.integral_one]; norm_num)
  have hρK : ∀ y, rho y ≤ C := fun y => by
    refine (le_abs_self _).trans ((hb y).1.trans ?_)
    have : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
    nlinarith
  obtain ⟨Ω, hΩ0, hΩ⟩ := r26t8a_f25_conv_bound hd hs0 hsd
  set Rn : ℝ := ‖r26t8a_Rz d‖ with hRn
  have hRn0 : 0 ≤ Rn := norm_nonneg (r26t8a_Rz d)
  refine ⟨Rn * criticalS d * (3 + C * Ω) / 2, by positivity, ?_⟩
  intro f A hA hTB x
  obtain ⟨hf, hj⟩ := hTB
  have hf2 : ∀ w, ‖iteratedFDeriv ℝ 2 f w‖ ≤ A := fun w => hj 2 (by norm_num) (by unfold testOrder; omega) w
  have hae : ∀ᵐ y : Euc d ∂volume, y ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
  set μ := HRS.Whole.withDensityReal rho with hμ
  obtain ⟨hI, hIb⟩ := hΩ rho C (fun y => hprob.nonneg y) hρK hρs.continuous hρi x
  set g : Euc d → ℝ := fun y => Rn * A * criticalS d * (1 + ‖x - y‖ ^ (-criticalS d)) with hg
  have hgi : Integrable g μ := by
    rw [r26t8a_f25_wd_integrable hprob]
    have := hI.const_mul (Rn * A * criticalS d)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hg]; ring
  have hbound : ∀ᵐ y ∂μ, ‖hSource f x y‖ ≤ g y := by
    have hae' : ∀ᵐ y ∂μ, y ≠ x :=
      (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (rho x))).ae_le
        (by filter_upwards [hae] with y hy using hy)
    filter_upwards [hae'] with y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.2 hy.symm
    have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hxy
    have hG := r26t8a_norm_rieszGrad hs0 hxy
    have hL := r26t8a_o02_grad_lip hf hf2 x y
    unfold hSource commutatorKernel
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hG]
    have e : ‖x - y‖ * ‖x - y‖ ^ (-criticalS d - 1) = ‖x - y‖ ^ (-criticalS d) := by
      rw [← Real.rpow_one_add' hn.le (by linarith)]; congr 1; ring
    have hp : 0 ≤ ‖x - y‖ ^ (-criticalS d) := Real.rpow_nonneg hn.le _
    calc ‖gradient f x - gradient f y‖ * (criticalS d * ‖x - y‖ ^ (-criticalS d - 1))
        ≤ (Rn * A * ‖x - y‖) * (criticalS d * ‖x - y‖ ^ (-criticalS d - 1)) :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ = Rn * A * criticalS d * ‖x - y‖ ^ (-criticalS d) := by rw [← e]; ring
      _ ≤ g y := by
          simp only [hg]
          have : 0 ≤ Rn * A * criticalS d := by positivity
          nlinarith
  have h1 := norm_integral_le_of_norm_le hgi hbound
  have h2 : ∫ y, g y ∂μ = Rn * A * criticalS d * ∫ y, rho y * (1 + ‖x - y‖ ^ (-criticalS d)) := by
    rw [r26t8a_f25_wd_integral hprob, ← integral_const_mul]
    congr 1; funext y; simp only [hg]; ring
  have h3 : ∫ y, rho y * (1 + ‖x - y‖ ^ (-criticalS d)) ≤ 3 * 1 + C * Ω := by
    have := hIb; rw [hprob.integral_one] at this; exact this
  unfold aSource
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h4 : |∫ y, hSource f x y ∂μ| ≤ ∫ y, g y ∂μ := by rwa [Real.norm_eq_abs] at h1
  rw [h2] at h4
  have hpos : 0 ≤ Rn * A * criticalS d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hpos]

end HRS.MS.R26T8A

import HRS.MS.SA12NN2J

/-!
# S.A.12 N2 (SA12N), part K: duality, the `L²` bound of `[x_l, H_q]` on a ball

`‖1_B (x_l g*D_q²v - g*D_q²(x_l v))‖₂ ≤ C ‖q‖² ‖v‖₂` for every ball `B` (no dependence on the radius),
by testing against `χ Q` with a continuous cutoff `χ = 1` on `B`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate FourierTransform Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqN1a HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT3
  HRS.MS.UniqN3a

variable {d : ℕ}

theorem sa12n_eLp_eq {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, one_div, Real.norm_eq_abs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq_abs]

theorem sa12n_convFun_continuous {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (HRS.Whole.convFun (rieszKernel d s) f) := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hfun' : HRS.Whole.convFun (rieszKernel d s) f =
      rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * f (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  rw [hfun']
  exact hfc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hf

/-- A continuous cutoff, `1` on `B̄(c', r')`, with values in `[0,1]` and compact support. -/
theorem sa12n_cutoff (c' : Euc d) (r' : ℝ) :
    ∃ χ : Euc d → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x ∈ closedBall c' r', χ x = 1 := by
  set R : ℝ := max r' 1 with hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  let φ : Euc d ≃ₜ Euc d := (Homeomorph.subRight c').trans (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR0.ne'))
  refine ⟨fun x => n1aBump d (φ x), ?_, ?_, fun x => ⟨(n1aBump d).nonneg, (n1aBump d).le_one⟩, ?_⟩
  · exact (n1aBump d).continuous.comp φ.continuous
  · exact (n1aBump d).hasCompactSupport.comp_homeomorph φ
  · intro x hx
    apply (n1aBump d).one_of_mem_closedBall
    rw [mem_closedBall_zero_iff]
    show ‖R⁻¹ • (x - c')‖ ≤ 1
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR0, inv_mul_le_iff₀ hR0, mul_one]
    calc ‖x - c'‖ = dist x c' := (dist_eq_norm _ _).symm
      _ ≤ r' := mem_closedBall.1 hx
      _ ≤ R := le_max_left _ _

theorem sa12n_dual_ball (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Euc d) (l : Fin d) (v : Euc d → ℝ), ContDiff ℝ 2 v →
      HasCompactSupport v → ∀ (c' : Euc d) (r' : ℝ),
      eLpNorm ((closedBall c' r').indicator (fun x =>
        x l * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q v) x -
          HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q (fun y => y l * v y)) x))
        2 volume ≤ ENNReal.ofReal (C * ‖q‖ ^ 2) * eLpNorm v 2 volume := by
  obtain ⟨C, hC0, hC⟩ := sa12n_comm_pair hd
  refine ⟨C, hC0, fun q l v hv hvc c' r' => ?_⟩
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 1 < d := by linarith
  have hv1 : ContDiff ℝ 2 (fun y : Euc d => y l * v y) :=
    (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).contDiff.mul hv
  have hv1c : HasCompactSupport (fun y : Euc d => y l * v y) := hvc.mul_left
  set Q : Euc d → ℝ := fun x => x l * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q v) x -
    HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q (fun y => y l * v y)) x with hQ
  have hQc : Continuous Q := by
    refine ((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).continuous.mul ?_).sub ?_
    · exact sa12n_convFun_continuous hs0 hsd (qq_contDiff hv) (qq_hasCompactSupport hvc)
    · exact sa12n_convFun_continuous hs0 hsd (qq_contDiff hv1) (qq_hasCompactSupport hv1c)
  obtain ⟨χ, hχc, hχcs, hχ01, hχ1⟩ := sa12n_cutoff c' r'
  set u : Euc d → ℝ := fun x => χ x * Q x with hu
  have huc : Continuous u := hχc.mul hQc
  have hucs : HasCompactSupport u := hχcs.mul_right
  have hpair := hC q l u v huc hucs hv hvc
  have hLu : MemLp u 2 volume := huc.memLp_of_hasCompactSupport hucs
  have hLv : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  set K : ℝ := C * ‖q‖ ^ 2 * Real.sqrt (∫ x, v x ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  -- `∫ u² ≤ ∫ u Q`
  have hint1 : Integrable (fun x => u x ^ 2) volume :=
    (show Continuous (fun x => u x ^ 2) from huc.pow 2).integrable_of_hasCompactSupport
      (hucs.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hint2 : Integrable (fun x => u x * Q x) volume :=
    (huc.mul hQc).integrable_of_hasCompactSupport hucs.mul_right
  have hle : ∫ x, u x ^ 2 ≤ ∫ x, u x * Q x := by
    refine integral_mono hint1 hint2 fun x => ?_
    simp only [hu]
    have h0 := hχ01 x
    nlinarith [mul_nonneg h0.1 (sq_nonneg (Q x)), mul_nonneg (sub_nonneg.2 h0.2) (mul_nonneg h0.1 (sq_nonneg (Q x)))]
  set s : ℝ := Real.sqrt (∫ x, u x ^ 2) with hs
  have hs0' : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = ∫ x, u x ^ 2 := Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
  have hsK : s ≤ K := by
    have h1 : s ^ 2 ≤ K * s := by
      calc s ^ 2 = ∫ x, u x ^ 2 := hss
        _ ≤ ∫ x, u x * Q x := hle
        _ ≤ |∫ x, u x * Q x| := le_abs_self _
        _ ≤ C * ‖q‖ ^ 2 * (Real.sqrt (∫ x, u x ^ 2) * Real.sqrt (∫ x, v x ^ 2)) := hpair
        _ = K * s := by rw [hK, hs]; ring
    by_contra hlt
    push Not at hlt
    nlinarith
  have hmono : eLpNorm ((closedBall c' r').indicator Q) 2 volume ≤ eLpNorm u 2 volume := by
    refine eLpNorm_mono (hQc.aestronglyMeasurable.indicator measurableSet_closedBall) fun x => ?_
    by_cases hx : x ∈ closedBall c' r'
    · rw [Set.indicator_of_mem hx]
      simp only [hu, hχ1 x hx, one_mul]
      exact le_rfl
    · rw [Set.indicator_of_notMem hx]; simp
  refine hmono.trans ?_
  rw [sa12n_eLp_eq hLu, sa12n_eLp_eq hLv, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsK

end HRS.MH.AdjointRd.Phase2SA12Near

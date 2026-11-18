import HRS.MS.Fp81S21RawIto2
import HRS.MS.OrbIdAux1

/-! Transfer the empirical Itô martingale from the horizon-truncated gradient
integrand to the raw compact-test integral on `[0,T]`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MH.DualityRd
open HRS.MS.R26T3 HRS.MS.R2Interp

theorem fp81s21_particle_raw_truncation_congr
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (Fp : FilteredParticle A)
    {T : ℝ} (hT : 0 < T) {f : Euc p.d → ℝ} (hf : IsR2Test f) :
    ∀ᵐ ζ ∂A.P, ∀ u ∈ Set.Icc (0 : ℝ) T,
      (fp81s21_b6i_scale N p.β) *
          itoIntegral A.P Fp.ℱ Fp.Wc
            (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ =
        fp81s21_particle_raw_testIto p A Fp f u ζ -
          fp81s21_particle_raw_testIto p A Fp f 0 ζ := by
  classical
  let scale : ℝ := fp81s21_b6i_scale N p.β
  let trunc : ℝ → A.Ω → (Fin N × Fin p.d) → ℝ :=
    HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X
  let scaled : ℝ → A.Ω → (Fin N × Fin p.d) → ℝ :=
    fun r ζ k => scale • trunc r ζ k
  let raw : ℝ → A.Ω → (Fin N × Fin p.d) → ℝ :=
    fp81s21_particle_raw_Phi p A Fp f
  let cut : ℝ → A.Ω → (Fin N × Fin p.d) → ℝ :=
    fun r ζ k => if r ≤ T then raw r ζ k else 0
  have hfMemCb : MemCb 2 f := HRS.MH.DualityRd.db1_memCb_of_compact
    (hf.1.of_le (by norm_num)) hf.2
  have hgradCont : Continuous (gradient f) :=
    HRS.MH.DualityRd.db1_gradient_continuous (hf.1.of_le (by norm_num))
  have hG : Measurable (Function.uncurry
      (fun _ : ℝ => fun Y : EucConfig p.d N =>
        fun k : Fin N × Fin p.d => scale * gradient f (Y k.1) k.2)) := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_const.mul
      (((EuclideanSpace.proj k.2 : Euc p.d →L[ℝ] ℝ).continuous.measurable).comp
        (hgradCont.measurable.comp
          ((measurable_pi_apply k.1).comp measurable_snd)))
  have hrawProg : IsProgressive Fp.ℱ raw := by
    have h := HRS.isProgressive_comp_measurable'
      (HRS.ofNNRealTime Fp.X) Fp.filtered.progressive
      (fun _ : ℝ => fun Y : EucConfig p.d N =>
        fun k : Fin N × Fin p.d => scale * gradient f (Y k.1) k.2) hG
    change IsProgressive Fp.ℱ
      (fun s ζ (k : Fin N × Fin p.d) =>
        scale * gradient f (Fp.X (Real.toNNReal s) ζ k.1) k.2) at h
    change IsProgressive Fp.ℱ
      (fun s ζ (k : Fin N × Fin p.d) =>
        scale * gradient f (Fp.X (Real.toNNReal s) ζ k.1) k.2)
    exact h
  obtain ⟨B, hB⟩ := hfMemCb.2 1 (by norm_num)
  have hiter (x : Euc p.d) :
      ‖iteratedFDeriv ℝ 1 f x‖ ≤ B := hB (Set.mem_range_self x)
  have hgrad (x : Euc p.d) (j : Fin p.d) : |gradient f x j| ≤ B := by
    have hcoord : |gradient f x j| ≤ ‖gradient f x‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ _
    have hdual : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
      rw [← LinearIsometryEquiv.norm_map
        (InnerProductSpace.toDual ℝ (Euc p.d)) (gradient f x), toDual_gradient]
    calc
      |gradient f x j| ≤ ‖gradient f x‖ := hcoord
      _ = ‖fderiv ℝ f x‖ := hdual
      _ ≤ B := by
        rw [← norm_iteratedFDeriv_one]
        exact hiter x
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg _) (hiter 0)
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    rw [fp81s21_b6i_scale_normalization hN p.hβ]
    positivity
  have hrawBound : ∀ r ζ k, |raw r ζ k| ≤ scale * B := by
    intro r ζ k
    change |scale * gradient f (Fp.X (Real.toNNReal r) ζ k.1) k.2| ≤ scale * B
    rw [abs_mul, abs_of_nonneg hscale]
    exact mul_le_mul_of_nonneg_left (hgrad _ _) hscale
  have hrawL2 : IsProgressiveL2 A.P Fp.ℱ raw :=
    IsProgressiveL2.of_bounded A.P hrawProg (scale * B) hrawBound
  let ftime : ℝ → Euc p.d → ℝ := fun _ => f
  let ft : ℝ → Euc p.d → ℝ := fun _ _ => 0
  have hfC12 : IsC12TestRd T ftime ft := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact hf.1.of_le (by norm_num)
    · intro j hj
      obtain ⟨C, hC⟩ := hfMemCb.2 j hj
      exact ⟨C, fun r hr x => by simpa [ftime] using hC (Set.mem_range_self x)⟩
    · intro j hj
      have hc : Continuous (iteratedFDeriv ℝ j f) :=
        hf.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
      simpa [ftime, Function.comp_def] using hc.comp continuous_snd
    · intro x r hr
      simpa [ftime, ft] using (hasDerivAt_const r (f x))
    · exact continuous_const
    · exact ⟨0, fun r hr x => by simp [ft]⟩
  have htrunc : IsProgressiveL2 A.P Fp.ℱ trunc := by
    simpa [trunc] using
      HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof hT.le hfC12
        Fp.filtered.progressive
  have hscaled : IsProgressiveL2 A.P Fp.ℱ scaled := by
    change IsProgressiveL2 A.P Fp.ℱ
      (fun r ζ k => scale • trunc r ζ k)
    exact htrunc.smul scale
  have hcut : IsProgressiveL2 A.P Fp.ℱ cut := by
    simpa [cut] using
      HRS.MS.S52.s52_isProgressiveL2_ite hrawL2 (measurableSet_Iic (a := T))
  have heq : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ζ, scaled r ζ = cut r ζ := by
    intro r hr ζ
    funext k
    simp [scaled, trunc, cut, raw, fp81s21_particle_raw_Phi,
      HRS.MH.DualityRd.truncGradIntegrand, HRS.Whole.gradComp,
      scale, hr.1, hr.2, smul_eq_mul]
  have hcongr := HRS.MS.S52.s52_lc Fp.filtered.brownian
    hscaled hcut hT.le heq
  have hkill := HRS.MS.S52.s52_kill Fp.filtered.brownian hrawL2 hT.le
  have hsmul := HRS.itoIntegral_smul Fp.filtered.brownian htrunc scale
  filter_upwards [hcongr, hkill, hsmul] with ζ hcongrζ hkillζ hsmulζ
  intro u hu
  have hu0 : 0 ≤ u := hu.1
  have hcongrU := hcongrζ u hu0
  rw [min_eq_left hu.2] at hcongrU
  have hkillU := hkillζ u hu0
  have hsmulU := hsmulζ u
  have hmain : scale * itoIntegral A.P Fp.ℱ Fp.Wc trunc u ζ =
      itoIntegral A.P Fp.ℱ Fp.Wc raw u ζ := by
    calc
      scale * itoIntegral A.P Fp.ℱ Fp.Wc trunc u ζ =
          itoIntegral A.P Fp.ℱ Fp.Wc scaled u ζ := hsmulU.symm
      _ = itoIntegral A.P Fp.ℱ Fp.Wc cut u ζ := hcongrU
      _ = itoIntegral A.P Fp.ℱ Fp.Wc raw (min u T) ζ := hkillU
      _ = itoIntegral A.P Fp.ℱ Fp.Wc raw u ζ := by rw [min_eq_left hu.2]
  have hzero : itoIntegral A.P Fp.ℱ Fp.Wc raw 0 ζ = 0 :=
    HRS.itoIntegral_of_nonpos A.P Fp.ℱ Fp.Wc raw (le_rfl : (0 : ℝ) ≤ 0) ζ
  change scale * itoIntegral A.P Fp.ℱ Fp.Wc trunc u ζ =
    itoIntegral A.P Fp.ℱ Fp.Wc raw u ζ - itoIntegral A.P Fp.ℱ Fp.Wc raw 0 ζ
  rw [hzero, sub_zero]
  exact hmain

#print axioms HRS.Fp81.S21.fp81s21_particle_raw_truncation_congr

end HRS.Fp81.S21

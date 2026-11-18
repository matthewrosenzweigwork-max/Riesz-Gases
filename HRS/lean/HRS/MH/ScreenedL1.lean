import HRS.MH.ScreenedL1Aux1

/-! Packet L1 of `B:lem:screened` (S.B.4): proof of `screened_local_lt` in `ScreenedSpec.lean`.
Representative from `gk_rep_L1` (K4). Near case `dist c' c ≤ 3ρ`: the kernel is truncated to
`|u| ≤ 5ρ` on the relevant pairs and Young (`young_l1_l2`) applies. Far case: the kernel is bounded by
`max 1 s` and Cauchy-Schwarz on the ball gives the bound. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem screened_local_lt_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    ∃ C₀ C : ℝ, ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (v : Euc d → ℝ),
      Function.support v ⊆ Metric.closedBall c ρ → sobolevNormE (kgOrder d s) v < ⊤ →
      ∃ w : Euc d → ℝ, IsGradKernelRep d s i v w ∧
        ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
          eLpNorm ((Metric.closedBall c' r').indicator w) 2 volume ≤
            ENNReal.ofReal (C * ρ ^ C₀) * sobolevNormE (kgOrder d s) v := by
  have hd2 : 2 ≤ d := by
    have h1 : (1 : ℝ) < d := by linarith
    have h2 : 1 < d := by exact_mod_cast h1
    omega
  have hk0 : kgOrder d s = 0 := by
    unfold kgOrder
    exact max_eq_right (by linarith)
  obtain ⟨CN, hCN0, hCN⟩ := l1_kernel_trunc_lintegral hd hs0 hs1
  set V1r : ℝ := (volume (Metric.closedBall (0 : Euc d) 1)).toReal with hV1r
  have hV1r0 : 0 ≤ V1r := ENNReal.toReal_nonneg
  set m : ℝ := max 1 s with hm
  have hm0 : 0 ≤ m := le_trans zero_le_one (le_max_left _ _)
  refine ⟨(d : ℝ), CN + m * V1r, fun i ρ hρ c v hsupp hfin => ?_⟩
  rw [hk0] at hfin ⊢
  have hρ0 : 0 ≤ ρ := by linarith
  have hmem : HRS.PDE.ToolboxRd.MemSobolev 0 v := by
    by_contra hn
    unfold sobolevNormE at hfin
    rw [if_neg hn] at hfin
    exact lt_irrefl _ hfin
  have hL2 : MemLp v 2 volume := hmem.1
  rw [l1_sobolev_zero_eq hL2]
  set Nv := eLpNorm v 2 volume with hNv
  have hvae : AEStronglyMeasurable v volume := hL2.aestronglyMeasurable
  have hvm : Measurable (hvae.mk v) := hvae.stronglyMeasurable_mk.measurable
  have hae : v =ᵐ[volume] hvae.mk v := hvae.ae_eq_mk
  have hNv2 : Nv ^ 2 = ∫⁻ x, ‖v x‖ₑ ^ 2 := l1_sq_eLpNorm_ae v hvae
  have hI : Integrable v volume := by
    have h1 : IntegrableOn v (Metric.closedBall c ρ) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall c ρ)) := by
        constructor
        rw [Measure.restrict_apply_univ]
        exact measure_closedBall_lt_top
      exact (hL2.restrict _).integrable one_le_two
    exact (integrableOn_iff_integrable_of_support_subset hsupp).1 h1
  refine ⟨fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y, gk_rep_L1_proof hd2 hs0 hs1 i v hI, ?_⟩
  intro c' r' hr'
  have hwae : AEStronglyMeasurable (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) volume :=
    l1_w_aesm s i hvae
  have hind : AEStronglyMeasurable
      ((Metric.closedBall c' r').indicator (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y)) volume :=
    hwae.indicator measurableSet_closedBall
  have hρd : 0 ≤ ρ ^ (d : ℝ) := Real.rpow_nonneg hρ0 _
  suffices hsq : (eLpNorm ((Metric.closedBall c' r').indicator
      (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y)) 2 volume) ^ 2 ≤
      (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 by
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  rw [l1_sq_eLpNorm_ae _ hind]
  by_cases hnear : dist c' c ≤ 3 * ρ
  · -- near case: truncated kernel and Young
    set k : Euc d → ℝ≥0∞ := fun u =>
      ‖(Metric.closedBall (0 : Euc d) (5 * ρ)).indicator (fun u => rieszKernelGrad d s u i) u‖ₑ with hk
    have hkm : Measurable k :=
      (Measurable.indicator (k4_comp_measurable s i) measurableSet_closedBall).enorm
    have hkI : ∫⁻ u, k u ≤ ENNReal.ofReal (CN * ρ ^ (d : ℝ)) := hCN i ρ hρ
    have hk1 : ∫⁻ u, k u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkI
    set G : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, k (x - y) * ‖hvae.mk v y‖ₑ with hG
    have hpt : ∀ x, ‖(Metric.closedBall c' r').indicator
        (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) x‖ₑ ≤ G x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall c' r'
      · rw [Set.indicator_of_mem hx]
        have hxd : dist x c' ≤ ρ := le_trans (Metric.mem_closedBall.1 hx) hr'
        calc ‖∫ y, rieszKernelGrad d s (x - y) i * v y‖ₑ
            ≤ ∫⁻ y, ‖rieszKernelGrad d s (x - y) i * v y‖ₑ := enorm_integral_le_lintegral_enorm _
          _ = ∫⁻ y, k (x - y) * ‖v y‖ₑ := by
              refine lintegral_congr fun y => ?_
              by_cases hv0 : v y = 0
              · simp [hv0]
              · have hyB : y ∈ Metric.closedBall c ρ := hsupp (Function.mem_support.2 hv0)
                have hcy : dist c y ≤ ρ := by
                  rw [dist_comm]; exact Metric.mem_closedBall.1 hyB
                have hxy : ‖x - y‖ ≤ 5 * ρ := by
                  rw [← dist_eq_norm]
                  linarith [dist_triangle4 x c' c y]
                have hmem5 : x - y ∈ Metric.closedBall (0 : Euc d) (5 * ρ) :=
                  mem_closedBall_zero_iff.2 hxy
                simp only [hk]
                rw [Set.indicator_of_mem hmem5, enorm_mul]
          _ = ∫⁻ y, k (x - y) * ‖hvae.mk v y‖ₑ :=
              lintegral_congr_ae (hae.mono fun y hy => by simp only [hy])
      · rw [Set.indicator_of_notMem hx]
        simp
    have hYoung := young_l1_l2_proof k (fun y => ‖hvae.mk v y‖ₑ) hkm (hvm.enorm) hk1
    have hsq1 : ∫⁻ x, ‖(Metric.closedBall c' r').indicator
        (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) x‖ₑ ^ 2 ≤ ∫⁻ x, G x ^ 2 :=
      lintegral_mono fun x => pow_le_pow_left₀ ((by positivity)) (hpt x) 2
    have hf2 : ∫⁻ y, ‖hvae.mk v y‖ₑ ^ 2 = Nv ^ 2 := by
      rw [hNv2]
      exact lintegral_congr_ae (hae.mono fun y hy => by simp only [hy])
    have hYle : ENNReal.ofReal (CN * ρ ^ (d : ℝ)) ≤ ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hm0 hV1r0)) hρd)
    calc ∫⁻ x, ‖(Metric.closedBall c' r').indicator
          (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) x‖ₑ ^ 2
        ≤ ∫⁻ x, G x ^ 2 := hsq1
      _ ≤ (∫⁻ y, k y) ^ 2 * ∫⁻ y, ‖hvae.mk v y‖ₑ ^ 2 := hYoung
      _ = (∫⁻ y, k y) ^ 2 * Nv ^ 2 := by rw [hf2]
      _ ≤ (ENNReal.ofReal (CN * ρ ^ (d : ℝ)) * Nv) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((by positivity)) hkI 2) ((by positivity))
      _ ≤ (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 :=
          pow_le_pow_left₀ ((by positivity)) (mul_le_mul_of_nonneg_right hYle ((by positivity))) 2
  · -- far case: the kernel is bounded by `max 1 s`
    have hnear' : 3 * ρ < dist c' c := not_le.mp hnear
    set X : ℝ≥0∞ := ENNReal.ofReal (ρ ^ (d : ℝ) * V1r) with hX
    have hvolB : volume (Metric.closedBall c ρ) ≤ X :=
      l1_vol_closedBall_le c le_rfl hρ0
    have hvolB' : volume (Metric.closedBall c' r') ≤ X :=
      l1_vol_closedBall_le c' hr' hρ0
    have hm_pt : ∀ x ∈ Metric.closedBall c' r', ∀ y,
        ‖rieszKernelGrad d s (x - y) i * v y‖ₑ ≤ ENNReal.ofReal m * ‖v y‖ₑ := by
      intro x hx y
      by_cases hv0 : v y = 0
      · simp [hv0]
      · have hyB : y ∈ Metric.closedBall c ρ := hsupp (Function.mem_support.2 hv0)
        have hxd : dist x c' ≤ ρ := le_trans (Metric.mem_closedBall.1 hx) hr'
        have hyd : dist y c ≤ ρ := Metric.mem_closedBall.1 hyB
        have h1 : ρ < ‖x - y‖ := by
          rw [← dist_eq_norm]
          have h3 := dist_triangle4 c' x y c
          rw [dist_comm c' x] at h3
          linarith
        have hge : 1 ≤ ‖x - y‖ := by linarith
        have hne : x - y ≠ 0 := by
          intro h
          rw [h, norm_zero] at hge
          linarith
        have hK := kernel_bound_proof hs0 (x - y) hne
        have hpow : ‖x - y‖ ^ (-s - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
        have hKle : ‖rieszKernelGrad d s (x - y) i‖ ≤ m := by
          calc ‖rieszKernelGrad d s (x - y) i‖ ≤ ‖rieszKernelGrad d s (x - y)‖ :=
                k4_comp_norm_le s (x - y) i
            _ ≤ max 1 s * ‖x - y‖ ^ (-s - 1) := hK
            _ ≤ max 1 s * 1 := mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one (le_max_left _ _))
            _ = m := mul_one _
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hm0]
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hKle (norm_nonneg _)
    have hwb : ∀ x ∈ Metric.closedBall c' r',
        ‖∫ y, rieszKernelGrad d s (x - y) i * v y‖ₑ ≤ ENNReal.ofReal m * ∫⁻ y, ‖v y‖ₑ := by
      intro x hx
      calc ‖∫ y, rieszKernelGrad d s (x - y) i * v y‖ₑ
          ≤ ∫⁻ y, ‖rieszKernelGrad d s (x - y) i * v y‖ₑ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, ENNReal.ofReal m * ‖v y‖ₑ := lintegral_mono fun y => hm_pt x hx y
        _ = ENNReal.ofReal m * ∫⁻ y, ‖v y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsq2 : ∫⁻ x, ‖(Metric.closedBall c' r').indicator
        (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) x‖ₑ ^ 2 ≤
        ∫⁻ x, (Metric.closedBall c' r').indicator
          (fun _ : Euc d => (ENNReal.ofReal m * ∫⁻ y, ‖v y‖ₑ) ^ 2) x := by
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ Metric.closedBall c' r'
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        exact pow_le_pow_left₀ ((by positivity)) (hwb x hx) 2
      · simp [Set.indicator_of_notMem hx]
    rw [lintegral_indicator_const measurableSet_closedBall] at hsq2
    have hL1 : (∫⁻ y, ‖v y‖ₑ) ^ 2 ≤ volume (Metric.closedBall c ρ) * Nv ^ 2 := by
      rw [hNv2]
      exact l1_holder hvae measurableSet_closedBall hsupp
    have hYle : ENNReal.ofReal m * X ≤ ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) := by
      rw [hX, ← ENNReal.ofReal_mul hm0]
      apply ENNReal.ofReal_le_ofReal
      have e1 : (CN + m * V1r) * ρ ^ (d : ℝ) = CN * ρ ^ (d : ℝ) + m * (ρ ^ (d : ℝ) * V1r) := by ring
      rw [e1]
      linarith [mul_nonneg hCN0 hρd]
    calc ∫⁻ x, ‖(Metric.closedBall c' r').indicator
          (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) x‖ₑ ^ 2
        ≤ (ENNReal.ofReal m * ∫⁻ y, ‖v y‖ₑ) ^ 2 * volume (Metric.closedBall c' r') := hsq2
      _ = ENNReal.ofReal m ^ 2 * (∫⁻ y, ‖v y‖ₑ) ^ 2 * volume (Metric.closedBall c' r') := by ring
      _ ≤ ENNReal.ofReal m ^ 2 * (volume (Metric.closedBall c ρ) * Nv ^ 2) * X := by
          gcongr
      _ ≤ ENNReal.ofReal m ^ 2 * (X * Nv ^ 2) * X := by
          gcongr
      _ = (ENNReal.ofReal m * X) ^ 2 * Nv ^ 2 := by ring
      _ ≤ (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ)) * Nv) ^ 2 := by
          rw [mul_pow (ENNReal.ofReal ((CN + m * V1r) * ρ ^ (d : ℝ))) Nv]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hYle 2) (by positivity)

end HRS.MH.Screened

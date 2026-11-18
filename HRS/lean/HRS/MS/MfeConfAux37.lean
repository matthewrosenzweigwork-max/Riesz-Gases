import HRS.MS.MfeConfAux36

/-!
# S.B.1, packet F3 (part 18): the main theorem `sb1_logK_main`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ}

theorem sb1_gibbs_eq_Kpi (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Euc d → ℝ) (β : ℝ) :
    Whole.gibbsNormalizer k N β (Whole.withDensityReal (ρ r)) = sb1Kpi k β N ρ r := by
  unfold Whole.gibbsNormalizer sb1Kpi sb1FF
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [sb1_modEnergy_eq (H.tr.slice r hr).dens]

theorem sb1_EQ_eq (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    sb1EQ D N ρ r = (sb1Kpi (Whole.rieszKernel d D.s) D.invβ⁻¹ N ρ r)⁻¹ *
      sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) D.invβ⁻¹ N ρ r := by
  have hdens := (H.tr.slice r hr).dens
  unfold sb1EQ sb1Q
  rw [sb1_integral_modGibbs (sb1_measurable_rieszKernel D.s) hdens, sb1_gibbs_eq_Kpi H hr]
  congr 1
  unfold sb1Phipi
  rw [sb1_integral_pi hdens]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [sb1FF, sb1CN, sb1_commKernel_eq, mul_assoc]

theorem sb1_logK_main (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) (hβ : 0 < D.invβ) (hN : 1 ≤ N)
    (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc 0 T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t)) :
    SbLogK D N T ρ := by
  have hd := H.tr.hd
  have hs0 := H.tr.hs0
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hIcc0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  unfold SbLogK
  generalize hβdef : D.invβ⁻¹ = β at hβ0 ⊢
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- the smoothed kernels
  have hkn : ∀ n, Sb1KerU d D.s (sb1kn D.s n) := fun n => sb1KerU_gE hs0 (sb1eps_pos n) (sb1eps_le_one n)
  have hkR : ∀ n, Sb1KerR d (sb1kn D.s n) (Whole.movtr_sigma D.s * sb1eps n ^ (-D.s - 1)) := fun n =>
    sb1KerR_gE hs0 (sb1eps_pos n) (sb1eps_le_one n)
  have hg : Sb1KerU d D.s (Whole.rieszKernel d D.s) := sb1KerU_riesz d D.s hs0
  have hconv : ∀ z : Euc d, z ≠ 0 → Tendsto (fun n => sb1kn D.s n z) atTop (𝓝 (Whole.rieszKernel d D.s z)) := fun z hz => sb1gE_tendsto hz
  -- Lipschitz data
  have hL : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ Kf r ∧
      ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kf r * ‖x - y‖ :=
    fun r hr => sb1_lip_of_hasLip (hLip r hr)
  have hσ : 0 ≤ Whole.movtr_sigma D.s := sb1_sigma_nonneg hs0
  have hCs : 0 ≤ sb1Cs d D.s C3 := by
    unfold sb1Cs; have := H.C3nn; have := sb1Isig_nonneg (d := d) D.s; positivity
  have hCw : 0 < sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N := Real.exp_pos _
  let Φb : ℝ → ℝ := fun r => (sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N *
    (2 * (Whole.movtr_sigma D.s * sb1Cs d D.s C3))) * Kf r
  have hΦb : IntegrableOn Φb (Set.Icc 0 T) := hKi.const_mul _
  -- bounds of the transport kernels
  have hbn : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ n x y, |sb1hk (sb1kn D.s n) (Whole.mfeTransportW D (ρ r)) x y| ≤
      Whole.movtr_sigma D.s * Kf r * ‖x - y‖ ^ (-D.s) := fun r hr n x y =>
    sb1_hk_bound hs0 (fun z hz e => sb1gE_grad_le hs0 (sb1eps_pos n).le hz e) (hL r hr).1 (hL r hr).2 x y
  have hbg : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x y, |sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)) x y| ≤
      Whole.movtr_sigma D.s * Kf r * ‖x - y‖ ^ (-D.s) := by
    intro r hr x y
    refine sb1_hk_bound hs0 (fun z hz e => ?_) (hL r hr).1 (hL r hr).2 x y
    have := sb1gE_grad_le hs0 (le_refl (0 : ℝ)) hz e (d := d) (s := D.s)
    rwa [Whole.movtr_gEps_zero] at this
  -- measurability of the kernels
  have hcoord : ∀ kk : Fin d, Measurable (fun v : Euc d => v kk) := fun kk =>
    (EuclideanSpace.proj (𝕜 := ℝ) kk).continuous.measurable
  have hmeas : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ k : Euc d → ℝ,
      Measurable (fun p : Euc d × Euc d => sb1hk k (Whole.mfeTransportW D (ρ r)) p.1 p.2) := by
    intro r hr k
    obtain ⟨L, hLl, -⟩ := hLip r hr
    have hum : Measurable (Whole.mfeTransportW D (ρ r)) := hLl.continuous.measurable
    have : (fun p : Euc d × Euc d => sb1hk k (Whole.mfeTransportW D (ρ r)) p.1 p.2) = fun p =>
        ∑ kk, ((Whole.mfeTransportW D (ρ r) p.1 - Whole.mfeTransportW D (ρ r) p.2) kk) *
          fderiv ℝ k (p.1 - p.2) (sb1e kk) := funext fun p => sb1_clm_expand _ _
    rw [this]
    exact Finset.measurable_sum _ fun kk _ => ((hcoord kk).comp ((hum.comp measurable_fst).sub (hum.comp measurable_snd))).mul
      ((measurable_fderiv_apply_const ℝ k (sb1e kk)).comp (measurable_fst.sub measurable_snd))
  have hconvh : ∀ r : ℝ, ∀ x y : Euc d, x ≠ y →
      Tendsto (fun n => sb1hk (sb1kn D.s n) (Whole.mfeTransportW D (ρ r)) x y) atTop
        (𝓝 (sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)) x y)) := fun r x y hxy =>
    sb1gE_fderiv_tendsto (sub_ne_zero.2 hxy) _
  -- uniform bound on Φ
  have hbd : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) T,
      |sb1Phipi (sb1kn D.s n) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r| ≤ Φb r := by
    intro n r hr
    have := sb1_Phi_abs_le hd hs0 hsd hN hβ0.le (hkn n) (H.rho hd hr) (mul_nonneg hσ (hL r hr).1) (hbn r hr n)
    refine this.trans (le_of_eq ?_)
    simp only [Φb]; ring
  have hbdg : ∀ r ∈ Set.Icc (0 : ℝ) T,
      |sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r| ≤ Φb r := by
    intro r hr
    have := sb1_Phi_abs_le hd hs0 hsd hN hβ0.le hg (H.rho hd hr) (mul_nonneg hσ (hL r hr).1) (hbg r hr)
    refine this.trans (le_of_eq ?_)
    simp only [Φb]; ring
  -- the smoothed identities
  have hM : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T, sb1Kpi (sb1kn D.s n) β N ρ t - sb1Kpi (sb1kn D.s n) β N ρ 0 =
      ∫ r in (0 : ℝ)..t, β * N * sb1Phipi (sb1kn D.s n) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r :=
    fun n t ht => sb1_Mlevel H hT hβ0 hN (hkn n) (hkR n) hΦb (hbd n) ht
  -- one-time limits
  have hKlim : ∀ r ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => sb1Kpi (sb1kn D.s n) β N ρ r) atTop
      (𝓝 (sb1Kpi (Whole.rieszKernel d D.s) β N ρ r)) := fun r hr => sb1_K_tendsto hd hs0 hsd hN hβ0.le hkn hg hconv (H.rho hd hr)
  have hPlim : ∀ r ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => sb1Phipi (sb1kn D.s n) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)
      atTop (𝓝 (sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)) := fun r hr =>
    sb1_Phi_tendsto hd hs0 hsd hN hβ0.le hkn hconv (H.rho hd hr) (mul_nonneg hσ (hL r hr).1)
      (hn := fun n => sb1hk (sb1kn D.s n) (Whole.mfeTransportW D (ρ r))) (h := sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)))
      (hbn r hr) (fun n => hmeas r hr (sb1kn D.s n)) (hconvh r)
  -- the limit identity
  have hid : ∀ t ∈ Set.Icc (0 : ℝ) T, sb1Kpi (Whole.rieszKernel d D.s) β N ρ t - sb1Kpi (Whole.rieszKernel d D.s) β N ρ 0 =
      ∫ r in (0 : ℝ)..t, β * N * sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r := by
    intro t ht
    have h1 := (hKlim t ht).sub (hKlim 0 hIcc0)
    have hsub : ∀ r ∈ Set.Ioc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
    have h2 : Tendsto (fun n => ∫ r in (0 : ℝ)..t, β * N *
        sb1Phipi (sb1kn D.s n) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r) atTop
        (𝓝 (∫ r in (0 : ℝ)..t, β * N * sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun r => β * N * Φb r) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun n => by
          rw [Set.uIoc_of_le ht.1]
          exact ((sb1_Phipi_aesm H hT hβ0 hN (hkn n) (hkR n)).mono_set hsub).const_mul _
      · exact Eventually.of_forall fun n => Eventually.of_forall fun r hr => by
          rw [Set.uIoc_of_le ht.1] at hr
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β * N)]
          exact mul_le_mul_of_nonneg_left (hbd n r (hsub r hr)) (by positivity)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
        exact (hΦb.mono_set hsub).const_mul _
      · exact Eventually.of_forall fun r hr => by
          rw [Set.uIoc_of_le ht.1] at hr
          exact (hPlim r (hsub r hr)).const_mul _
    exact tendsto_nhds_unique (h1.congr fun n => hM n t ht) h2
  -- positivity of the limit normaliser
  have hKpos : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < sb1Kpi (Whole.rieszKernel d D.s) β N ρ t := by
    intro t ht
    haveI : IsProbabilityMeasure (Whole.withDensityReal (ρ t)) :=
      HRS.MS.Thm.cb_withDensityReal_isProb (H.tr.slice t ht).dens
    unfold sb1Kpi sb1FF
    refine integral_exp_pos ?_
    exact Integrable.of_bound (C := sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N)
      (Real.measurable_exp.comp ((sb1_En_meas hg (H.rho hd ht)).const_mul _)).aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact sb1_E_le hd hs0 hsd hN hβ0.le hg (H.rho hd ht) X)
  -- measurability of the limit Φ
  have hPhig_aesm : AEStronglyMeasurable (fun r => sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r)
      (volume.restrict (Set.Icc 0 T)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => sb1_Phipi_aesm H hT hβ0 hN (hkn n) (hkR n)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hPlim r hr
  have hPg_int : IntervalIntegrable
      (fun r => β * N * sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hsub : Set.Ioc (0 : ℝ) T ⊆ Set.Icc 0 T := fun r hr => ⟨hr.1.le, hr.2⟩
    refine Integrable.mono' ((hΦb.mono_set hsub).const_mul (β * N)) ((hPhig_aesm.mono_set hsub).const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β * N)]
    exact mul_le_mul_of_nonneg_left (hbdg r (hsub hr)) (by positivity)
  obtain ⟨m, hm, hmK, hlog⟩ := sb1_log_of_integral_eq hT hKpos hPg_int (fun t ht => by
    have := hid t ht; linarith)
  have hKcont : ContinuousOn (sb1Kpi (Whole.rieszKernel d D.s) β N ρ) (Set.Icc 0 T) :=
    (sb1_Kk_contOn H hg hβ0.le hN).congr (fun r hr => sb1_Kpi_eq H hr (Whole.rieszKernel d D.s) β)
  have hEQ : ∀ r ∈ Set.Icc (0 : ℝ) T, sb1EQ D N ρ r = (sb1Kpi (Whole.rieszKernel d D.s) β N ρ r)⁻¹ *
      sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r := fun r hr => by
    have := sb1_EQ_eq H hr (N := N)
    rwa [hβdef] at this
  refine ⟨?_, fun t ht => ?_⟩
  · refine Integrable.mono' (hΦb.const_mul (1 / m)) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun r => (sb1Kpi (Whole.rieszKernel d D.s) β N ρ r)⁻¹ *
          sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r) (volume.restrict (Set.Icc 0 T)) :=
        ((hKcont.inv₀ fun r hr => (hKpos r hr).ne').aestronglyMeasurable measurableSet_Icc).mul hPhig_aesm
      refine h1.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hEQ r hr).symm
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs, hEQ r hr, abs_mul, abs_inv, abs_of_pos (hKpos r hr)]
      calc (sb1Kpi (Whole.rieszKernel d D.s) β N ρ r)⁻¹ * |sb1Phipi (Whole.rieszKernel d D.s) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r|
          ≤ (1 / m) * Φb r := by
            rw [one_div]
            exact mul_le_mul (inv_anti₀ hm (hmK r hr)) (hbdg r hr) (abs_nonneg _) (inv_nonneg.2 hm.le)
        _ = _ := by simp only [Pi.mul_apply]
  · have h1 := hlog t ht
    rw [← sb1_gibbs_eq_Kpi H ht (Whole.rieszKernel d D.s) β, ← sb1_gibbs_eq_Kpi H hIcc0 (Whole.rieszKernel d D.s) β] at h1
    rw [h1, intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    rw [hEQ r hr']
    have hK0 : sb1Kpi (Whole.rieszKernel d D.s) β N ρ r ≠ 0 := (hKpos r hr').ne'
    field_simp

end Main

end HRS.MS.MfeConf

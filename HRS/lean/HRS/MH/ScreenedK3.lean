import HRS.MH.ScreenedK3Aux3

/-! Packet K3 of `B:lem:screened` (S.B.4): proof of `gk_weak` in `ScreenedSpec.lean`.
Mollify the kernel: `g_ε(x-y)` is smooth, integration by parts applies, and dominated convergence
`ε → 0` (dominators `|x-y|^{-s}`, `|x-y|^{-s-1}` times Schwartz functions) gives the weak derivative. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma k3_dEps_measurable (s ε : ℝ) (e : Euc d) : Measurable fun z : Euc d => movtr_dEps d s ε e z := by
  unfold movtr_dEps
  fun_prop

lemma k3_dEps_mul_le {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 ≤ ε) (e : Euc d) (he : ‖e‖ ≤ 1)
    (z : Euc d) (c : ℝ) :
    ‖movtr_dEps d s ε e z * c‖ ≤ movtr_sigma s * (‖z‖ ^ (-s - 1) * ‖c‖) := by
  rw [norm_mul, Real.norm_eq_abs (movtr_dEps d s ε e z)]
  calc |movtr_dEps d s ε e z| * ‖c‖ ≤ (movtr_sigma s * ‖z‖ ^ (-s - 1)) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (k3_dEps_bound hs0 hε e he z) (norm_nonneg c)
    _ = movtr_sigma s * (‖z‖ ^ (-s - 1) * ‖c‖) := by ring

theorem gk_weak_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (i : Fin d)
    (φ : SchwartzMap (Euc d) ℝ) (y : Euc d) :
    Integrable (fun x => rieszKernelGrad d s (x - y) i * φ x) ∧
    ∫ x, rieszKernelGrad d s (x - y) i * φ x =
      -HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hsd : s + 1 < d := by linarith
  have hsd' : s < d := by linarith
  have hv : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := movtr_norm_single i
  obtain ⟨hcφ, hbφ, h0φ, h1φ⟩ := k3_sch_props φ
  obtain ⟨hcD, hbD, h0D, h1D⟩ := k3_sch_deriv_props φ i
  have hG : Integrable (fun x => ‖x - y‖ ^ (-s - 1) * ‖φ x‖) :=
    k3_integrable_rpow hd1 (by linarith) (by linarith) y hcφ hbφ h0φ
  -- the left integrand is integrable (dominated by `σ |x-y|^{-s-1} |φ|`)
  have hint : Integrable (fun x => rieszKernelGrad d s (x - y) i * φ x) := by
    refine Integrable.mono' (hG.const_mul (movtr_sigma s)) ?_ ?_
    · have hcoord : Measurable fun v : Euc d => v i := (PiLp.continuous_apply _ _ i).measurable
      exact ((((hcoord.comp (movtr_rieszKernelGrad_measurable (d := d) s |>.comp
        (measurable_id.sub_const y)))).mul hcφ.measurable)).aestronglyMeasurable
    · exact (k3_ae_ne hd1 y).mono fun x hx => by
        have hz : x - y ≠ 0 := sub_ne_zero.mpr hx
        rw [movtr_rieszKernelGrad_apply s hz i]
        exact k3_dEps_mul_le hs0 le_rfl (EuclideanSpace.single i 1) hv (x - y) (φ x)
  -- limit `ε → 0` of the smoothed left side
  have hA : Tendsto (fun ε => ∫ x, movtr_gEps d s ε (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1))
      (𝓝[>] 0) (𝓝 (∫ x, rieszKernel d s (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun ε => ?_) ?_
      (k3_gEps_dom_integrable hd1 hs0 hsd' y hcD hbD h0D h1D) ?_
    · exact ((((movtr_gEps_measurable (d := d) s ε).comp (measurable_id.sub_const y))).mul
        hcD.measurable).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      exact (k3_ae_ne hd1 y).mono fun x hx => k3_gEps_dom hs0 hε.1.le hε.2.le y x hx _
    · exact (k3_ae_ne hd1 y).mono fun x hx => by
        have hz : x - y ≠ 0 := sub_ne_zero.mpr hx
        have ht : Tendsto (fun ε => movtr_gEps d s ε (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1))
            (𝓝 0) (𝓝 (rieszKernel d s (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
          have := ((movtr_gEps_cont_eps (d := d) s hz).tendsto 0).mul_const
            (fderiv ℝ φ x (EuclideanSpace.single i 1))
          rw [← congrFun (movtr_gEps_zero d s) (x - y)]
          exact this
        exact tendsto_nhdsWithin_of_tendsto_nhds ht
  -- limit `ε → 0` of the smoothed right side
  have hB : Tendsto (fun ε => ∫ x, movtr_dEps d s ε (EuclideanSpace.single i 1) (x - y) * φ x)
      (𝓝[>] 0) (𝓝 (∫ x, rieszKernelGrad d s (x - y) i * φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun ε => ?_) ?_ (hG.const_mul (movtr_sigma s)) ?_
    · exact (((k3_dEps_measurable s ε (EuclideanSpace.single i 1)).comp
        (measurable_id.sub_const y)).mul hcφ.measurable).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      exact Eventually.of_forall fun x => k3_dEps_mul_le hs0 hε.1.le _ hv (x - y) (φ x)
    · exact (k3_ae_ne hd1 y).mono fun x hx => by
        have hz : x - y ≠ 0 := sub_ne_zero.mpr hx
        have ht : Tendsto (fun ε => movtr_dEps d s ε (EuclideanSpace.single i 1) (x - y) * φ x)
            (𝓝 0) (𝓝 (movtr_dEps d s 0 (EuclideanSpace.single i 1) (x - y) * φ x)) :=
          ((movtr_dEps_cont_eps (d := d) s (EuclideanSpace.single i 1) hz).tendsto 0).mul_const (φ x)
        rw [← movtr_rieszKernelGrad_apply s hz i] at ht
        exact tendsto_nhdsWithin_of_tendsto_nhds ht
  -- the mollified identity
  have hAB : (fun ε => ∫ x, movtr_gEps d s ε (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun ε => -∫ x, movtr_dEps d s ε (EuclideanSpace.single i 1) (x - y) * φ x) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    exact k3_ibp_eps hd1 hs0 hsd i y hε.1 hε.2.le φ
  have hid := tendsto_nhds_unique (hA.congr' hAB) hB.neg
  refine ⟨hint, ?_⟩
  have hk : ∀ x : Euc d, rieszKernel d s (x - y) = rieszKernel d s (y - x) := fun x => by
    unfold rieszKernel
    rw [norm_sub_rev]
  have hconv : ∫ x, rieszKernel d s (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y := by
    unfold HRS.Whole.convFun
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hk x]
  rw [← hconv]
  linarith [hid]

end HRS.MH.Screened

import HRS.MS.UlocMWAux1

/-!
# MS-QMUL, part 1: complex `L¹ ∩ L²` Fourier analysis

* `qm_L1L2`: the `L²` Fourier transform of a complex `L¹ ∩ L²` function is the `L¹` Fourier integral;
* `qm_plancherel`: `∫⁻ ‖𝓕 h‖ₑ² = ∫⁻ ‖h‖ₑ²` on `L¹ ∩ L²`;
* `qm_fourier_pd_norm`: `‖𝓕(∂^i g)(w)‖ = (2π)^n ∏ |w_{i_t}| ‖𝓕 g(w)‖`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}

theorem qm_L1L2 {h : Euc d → ℂ} (h1 : Integrable h) (h2 : MemLp h 2 volume) :
    (FT d (h2.toLp h) : Euc d → ℂ) =ᵐ[volume] 𝓕 h := by
  set G : Euc d → ℂ := 𝓕 h with hG
  have hGc : Continuous G :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  set F : Euc d → ℂ := ⇑(FT d (h2.toLp h)) with hF
  have hFl : LocallyIntegrable F volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hGl : LocallyIntegrable G volume := hGc.locallyIntegrable
  have key := ae_eq_of_integral_contDiff_smul_eq (μ := volume) hFl hGl ?_
  · exact key
  intro g hg hgc
  set gS := um_S g hg hgc with hgS
  have hg1 : Integrable (fun y : Euc d => ((g y : ℝ) : ℂ)) :=
    (hg.continuous.integrable_of_hasCompactSupport hgc).ofReal
  have hR : ∫ ξ, g ξ • G ξ = ∫ x, h x * 𝓕 (fun y => ((g y : ℝ) : ℂ)) x := by
    have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
      (e := Real.fourierChar) (L := innerₗ (Euc d)) Real.continuous_fourierChar
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous₂ h1 hg1
    have e1 : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
      ext x y; simp only [LinearMap.flip_apply, innerₗ_apply_apply]; exact real_inner_comm _ _
    rw [e1] at this
    have e2 : ∫ ξ, g ξ • G ξ = ∫ ξ, 𝓕 h ξ • ((g ξ : ℝ) : ℂ) := by
      congr 1; ext ξ
      rw [Complex.real_smul, mul_comm, smul_eq_mul]
    rw [e2]
    refine this.trans ?_
    rfl
  have hL : ∫ x, g x • F x = ∫ x, h x * 𝓕 (fun y => ((g y : ℝ) : ℂ)) x := by
    have e0 : gS.toLp 2 = FT d ((𝓕⁻ gS : SchwartzMap (Euc d) ℂ).toLp 2) := by
      rw [HRS.MS.SobMul.sobmul_FT_toLp]; simp
    have e1 : inner ℂ (gS.toLp 2) (FT d (h2.toLp h)) = ∫ x, g x • F x := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp gS 2 volume] with ξ hξ
      rw [hξ]
      rw [hgS, um_S_apply]
      simp [Complex.real_smul, mul_comm, hF]
    have e2 : inner ℂ (gS.toLp 2) (FT d (h2.toLp h)) =
        ∫ x, h x * 𝓕 (fun y => ((g y : ℝ) : ℂ)) x := by
      rw [e0, inner_FT, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp (𝓕⁻ gS : SchwartzMap (Euc d) ℂ) 2 volume,
        MemLp.coeFn_toLp h2] with x hx hx2
      rw [hx, hx2]
      have hgf : (⇑gS : Euc d → ℂ) = fun y => ((g y : ℝ) : ℂ) := by
        ext y; rw [hgS, um_S_apply]
      rw [SchwartzMap.fourierInv_coe, hgf]
      simp only [RCLike.inner_apply]
      rw [← um_conj_fourierInv g x, mul_comm]
    rw [← e1, e2]
  rw [hL, hR]

theorem qm_plancherel {h : Euc d → ℂ} (h1 : Integrable h) (h2 : MemLp h 2 volume) :
    ∫⁻ ξ, ‖𝓕 h ξ‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
  have e1 : eLpNorm (𝓕 h) 2 volume = eLpNorm h 2 volume := by
    have a1 : eLpNorm (⇑(FT d (h2.toLp h))) 2 volume = eLpNorm (⇑(h2.toLp h)) 2 volume := by
      have := (FT d).toLinearIsometry.enorm_map (h2.toLp h)
      rw [Lp.enorm_def, Lp.enorm_def] at this
      exact this
    rw [← eLpNorm_congr_ae (qm_L1L2 h1 h2), a1]
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp h2)
  have hm1 : AEStronglyMeasurable (𝓕 h) volume :=
    (Lp.memLp (FT d (h2.toLp h))).aestronglyMeasurable.congr (qm_L1L2 h1 h2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) h2.aestronglyMeasurable] at e1
  simp only [ENNReal.toReal_ofNat] at e1
  have := ENNReal.rpow_left_injective (x := (1 / 2 : ℝ)) (by norm_num) e1
  simpa [ENNReal.rpow_two] using this

/-- the coordinate derivative `∂_{i_1} ⋯ ∂_{i_n} f` -/
def qm_pd {n : ℕ} (i : Fin n → Fin d) (f : Euc d → ℂ) (x : Euc d) : ℂ :=
  iteratedFDeriv ℝ n f x (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))

theorem qm_fourier_pd_norm {m : ℕ} {f : Euc d → ℂ} (hf : ContDiff ℝ m f)
    (hint : ∀ k : ℕ, k ≤ m → Integrable (iteratedFDeriv ℝ k f) volume)
    {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (w : Euc d) :
    ‖𝓕 (qm_pd i f) w‖ = (2 * Real.pi) ^ n * (∏ t, |w (i t)|) * ‖𝓕 f w‖ := by
  have hf' : ContDiff ℝ (m : ℕ∞) f := by exact_mod_cast hf
  have hint' : ∀ k : ℕ, k ≤ (m : ℕ∞) → Integrable (iteratedFDeriv ℝ k f) volume :=
    fun k hk => hint k (by exact_mod_cast hk)
  have key := Real.fourier_iteratedFDeriv hf' hint' (n := n) (by exact_mod_cast hn)
  have h1 := congrFun key w
  have h2 := congrArg (fun T => T (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))) h1
  rw [Real.fourier_continuousMultilinearMap_apply (hint n hn)] at h2
  have hfun : (fun x : Euc d => (iteratedFDeriv ℝ n f x) fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d)) =
      qm_pd i f := rfl
  rw [hfun] at h2
  rw [h2, VectorFourier.fourierPowSMulRight_apply]
  rw [norm_smul, norm_smul, norm_pow, norm_neg]
  have hI : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [hI, norm_prod]
  have hb : ∀ t : Fin n, ‖((-(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w)
      (EuclideanSpace.single (i t) (1:ℝ))‖ = |w (i t)| := by
    intro t
    simp [EuclideanSpace.inner_single_right]
  simp_rw [hb]
  ring

end HRS.MS.QMul

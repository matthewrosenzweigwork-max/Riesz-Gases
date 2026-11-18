import HRS.MS.UlocCutAux1

/-!
# MS-ULOC-MW, part 1: Fourier analysis of `C^m_c` functions

* `um_L1L2`: `fourierL2` agrees with the `L¹` Fourier integral on `L¹ ∩ L²`;
* `um_fourier_partial`: `|\widehat{∂^i g}(w)| ≤ (2π|w|)^n |ĝ(w)|` for `g ∈ C^m_c`, `n ≤ m`;
* `um_sobE_sq`: `‖u‖²_{H^s}` as a lower integral in `ℝ≥0∞`;
* `um_deriv_le`: `∫ |∂^i g|² ≤ ‖g‖²_{H^m}` for `g ∈ C^m_c`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.UlocMW
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- real C_c^∞ as complex Schwartz -/
def um_S (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    SchwartzMap (Euc d) ℂ :=
  (hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hθ)

theorem um_S_apply (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (x : Euc d) : um_S θ hθ hc x = ((θ x : ℝ) : ℂ) := rfl

theorem um_conj_fourierInv (g : Euc d → ℝ) (ξ : Euc d) :
    conj (𝓕⁻ (fun x : Euc d => ((g x : ℝ) : ℂ)) ξ) = 𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) ξ := by
  rw [Real.fourierInv_eq', Real.fourier_eq', ← integral_conj]
  congr 1; ext v
  simp
  left
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]

theorem um_L1L2 {u : Euc d → ℝ} (h1 : Integrable u) (h2 : MemLp u 2 volume) :
    fourierL2 u =ᵐ[volume] 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) := by
  set U : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hU
  have hU1 : Integrable U := h1.ofReal
  set G : Euc d → ℂ := 𝓕 U with hG
  have hGc : Continuous G :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hU1
  set F : Euc d → ℂ := fourierL2 u with hF
  have hFl : LocallyIntegrable F volume :=
    (memLp_fourierL2 h2).locallyIntegrable (by norm_num)
  have hGl : LocallyIntegrable G volume := hGc.locallyIntegrable
  have key := ae_eq_of_integral_contDiff_smul_eq (μ := volume) hFl hGl ?_
  · exact key
  intro g hg hgc
  set gS := um_S g hg hgc with hgS
  have hg1 : Integrable (fun y : Euc d => ((g y : ℝ) : ℂ)) :=
    (hg.continuous.integrable_of_hasCompactSupport hgc).ofReal
  have hR : ∫ ξ, g ξ • G ξ = ∫ x, U x * 𝓕 (fun y => ((g y : ℝ) : ℂ)) x := by
    have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
      (e := Real.fourierChar) (L := innerₗ (Euc d)) Real.continuous_fourierChar
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous₂ hU1 hg1
    have e1 : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
      ext x y; simp only [LinearMap.flip_apply, innerₗ_apply_apply]; exact real_inner_comm _ _
    rw [e1] at this
    have e2 : ∫ ξ, g ξ • G ξ = ∫ ξ, 𝓕 U ξ • ((g ξ : ℝ) : ℂ) := by
      congr 1; ext ξ
      rw [Complex.real_smul, mul_comm, smul_eq_mul]
    rw [e2]
    refine this.trans ?_
    rfl
  have hL : ∫ x, g x • F x = ∫ x, U x * 𝓕 (fun y => ((g y : ℝ) : ℂ)) x := by
    have e0 : gS.toLp 2 = FT d ((𝓕⁻ gS : SchwartzMap (Euc d) ℂ).toLp 2) := by
      rw [HRS.MS.SobMul.sobmul_FT_toLp]; simp
    have e1 : inner ℂ (gS.toLp 2) (FT d (ofRealLp h2)) = ∫ x, g x • F x := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp gS 2 volume] with ξ hξ
      rw [hξ, ← fourierL2_eq h2]
      rw [hgS, um_S_apply]
      simp [Complex.real_smul, mul_comm, hF]
    have e2 : inner ℂ (gS.toLp 2) (FT d (ofRealLp h2)) =
        ∫ x, U x * 𝓕 (fun y => ((g y : ℝ) : ℂ)) x := by
      rw [e0, inner_FT, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp (𝓕⁻ gS : SchwartzMap (Euc d) ℂ) 2 volume,
        ofRealLp_coe h2] with x hx hx2
      rw [hx, hx2]
      have hgf : (⇑gS : Euc d → ℂ) = fun y => ((g y : ℝ) : ℂ) := by
        ext y; rw [hgS, um_S_apply]
      rw [SchwartzMap.fourierInv_coe, hgf]
      simp only [RCLike.inner_apply, hU]
      rw [← um_conj_fourierInv g x, mul_comm]
    rw [← e1, e2]
  rw [hL, hR]

theorem um_fourier_partial {m : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ m g) (hc : HasCompactSupport g)
    {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (w : Euc d) :
    ‖𝓕 (fun x : Euc d => ((HRS.Whole.partialDeriv i g x : ℝ) : ℂ)) w‖ ≤
      (2 * Real.pi * ‖w‖) ^ n * ‖𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) w‖ := by
  set f : Euc d → ℂ := fun x => ((g x : ℝ) : ℂ) with hf
  have hfc : HasCompactSupport f := hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hfd : ContDiff ℝ (m : ℕ∞) f := by
    have := Complex.ofRealCLM.contDiff.comp hg
    exact_mod_cast this
  have hint : ∀ k : ℕ, k ≤ (m : ℕ∞) → Integrable (iteratedFDeriv ℝ k f) volume := by
    intro k hk
    have hk' : (k : WithTop ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast hk
    exact (hfd.continuous_iteratedFDeriv hk').integrable_of_hasCompactSupport (hfc.iteratedFDeriv k)
  have key := Real.fourier_iteratedFDeriv hfd hint (n := n) (by exact_mod_cast hn)
  have h1 := congrFun key w
  have h2 := congrArg (fun T => T (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))) h1
  rw [Real.fourier_continuousMultilinearMap_apply (hint n (by exact_mod_cast hn))] at h2
  have hfun : (fun x : Euc d => (iteratedFDeriv ℝ n f x) fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d)) =
      fun x : Euc d => ((HRS.Whole.partialDeriv i g x : ℝ) : ℂ) := by
    ext x
    have hx : f = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ g := rfl
    have hgx : ContDiffAt ℝ (n : ℕ∞) g x := (hg.of_le (by exact_mod_cast hn)).contDiffAt
    rw [hx, ContinuousLinearMap.iteratedFDeriv_comp_left _ hgx le_rfl]
    rfl
  rw [hfun] at h2
  rw [h2, VectorFourier.fourierPowSMulRight_apply]
  rw [norm_smul, norm_smul, norm_pow, norm_neg]
  have hb : ∀ t : Fin n, ‖((-(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w)
      (EuclideanSpace.single (i t) (1:ℝ))‖ ≤ ‖w‖ := by
    intro t
    simp only [neg_apply, innerSL_apply_apply, norm_neg]
    calc ‖inner ℝ w (EuclideanSpace.single (i t) (1:ℝ))‖
        ≤ ‖w‖ * ‖(EuclideanSpace.single (i t) (1:ℝ) : Euc d)‖ := norm_inner_le_norm _ _
      _ = ‖w‖ := by simp
  have hprod : ‖∏ t : Fin n, ((-(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w)
      (EuclideanSpace.single (i t) (1:ℝ))‖ ≤ ‖w‖ ^ n := by
    rw [norm_prod]
    calc _ ≤ ∏ t : Fin n, ‖w‖ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun t _ => hb t)
      _ = _ := by simp
  have hI : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [hI, mul_pow (2 * Real.pi) ‖w‖ n, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod (norm_nonneg _)) (by positivity)

theorem um_sobE_sq {u : Euc d → ℝ} (hu : MemLp u 2 volume) (s : ℝ) :
    HRS.Whole.sobolevNormE s u ^ 2 = ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2) := by
  have h0 : ∀ ξ : Euc d, 0 ≤ wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
  have hm := aesm_wt_mul (aestronglyMeasurable_fourierL2 hu) s
  by_cases hI : Integrable (fun ξ : Euc d => wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2) volume
  · have hS : HRS.PDE.ToolboxRd.MemSobolev s u := ⟨hu, hI⟩
    unfold HRS.Whole.sobolevNormE
    rw [if_pos hS, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), sobolevNormSq_eq,
      Real.sq_sqrt (integral_nonneg h0), ofReal_integral_eq_lintegral_ofReal hI
        (Filter.Eventually.of_forall h0)]
  · have hS : ¬ HRS.PDE.ToolboxRd.MemSobolev s u := fun h => hI h.2
    unfold HRS.Whole.sobolevNormE
    rw [if_neg hS]
    simp only [ENNReal.top_pow two_ne_zero]
    by_contra hne
    apply hI
    refine ⟨hm, ?_⟩
    unfold HasFiniteIntegral
    have : ∫⁻ ξ, ‖wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2‖ₑ = ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2) := by
      refine lintegral_congr fun ξ => ?_
      rw [Real.enorm_eq_ofReal (h0 ξ)]
    rw [this]
    exact lt_top_iff_ne_top.2 (fun h => hne h.symm)

theorem um_deriv_le {m : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ m g) (hc : HasCompactSupport g)
    {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) :
    ∫⁻ x, ENNReal.ofReal ((HRS.Whole.partialDeriv i g x) ^ 2) ≤
      HRS.Whole.sobolevNormE (m : ℝ) g ^ 2 := by
  set p : Euc d → ℝ := HRS.Whole.partialDeriv i g with hp
  have hpc : Continuous p := by
    have h1 : Continuous (iteratedFDeriv ℝ n g) := hg.continuous_iteratedFDeriv (by exact_mod_cast hn)
    exact (continuous_eval_const (fun t : Fin n => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))).comp h1
  have hpcs : HasCompactSupport p := by
    have := (hc.iteratedFDeriv n).comp_left (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ =>
      T (fun t : Fin n => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))) (by simp)
    exact this
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hc
  have hp2 : MemLp p 2 volume := hpc.memLp_of_hasCompactSupport hpcs
  have hg1 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have hp1 : Integrable p := hpc.integrable_of_hasCompactSupport hpcs
  rw [um_sobE_sq hg2]
  have e1 : ∫⁻ x, ENNReal.ofReal (p x ^ 2) = ∫⁻ ξ, ENNReal.ofReal (‖fourierL2 p ξ‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hp2.integrable_sq (Filter.Eventually.of_forall fun x => sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_fourierL2 hp2)
        (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_norm_sq_fourierL2 hp2]
  rw [e1]
  refine lintegral_mono_ae ?_
  filter_upwards [um_L1L2 hp1 hp2, um_L1L2 hg1 hg2] with ξ h1 h2
  apply ENNReal.ofReal_le_ofReal
  rw [h1]
  have hb := um_fourier_partial hg hc hn i ξ
  rw [h2]
  have hw : (2 * Real.pi * ‖ξ‖) ^ 2 ≤ wt ξ := by
    unfold wt; nlinarith [sq_nonneg ‖ξ‖, sq_nonneg Real.pi]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have h3 : ((2 * Real.pi * ‖ξ‖) ^ n) ^ 2 ≤ wt ξ ^ m := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    exact (pow_le_pow_left₀ (by positivity) hw n).trans (pow_le_pow_right₀ (one_le_wt ξ) hn)
  rw [Real.rpow_natCast]
  calc _ ≤ ((2 * Real.pi * ‖ξ‖) ^ n * ‖𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) ξ‖) ^ 2 := hsq
    _ = ((2 * Real.pi * ‖ξ‖) ^ n) ^ 2 * ‖𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) ξ‖ ^ 2 := by ring
    _ ≤ wt ξ ^ m * ‖𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) ξ‖ ^ 2 := by gcongr

end HRS.MS.UlocMW

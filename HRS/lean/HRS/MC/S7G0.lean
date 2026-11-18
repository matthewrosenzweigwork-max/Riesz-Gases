import HRS.MC.Sec7Vocab
import HRS.PDE.MeanFieldLinearResponse
import HRS.Energy.StaticLimitGauss

/-!
# Packet `s7_G0_gaussian_exists`: the Gaussian `G` of `static_field` exists

The covariance form `C(F, G) = <P W F, R P W G>_{L^2(mu)}` on `E_m` (`W` the evaluation map, `P` the
centring, `R = (I + gamma K P)^{-1}` the resolvent of `PDE/MeanFieldLinearResponse`) is symmetric,
nonnegative and trace class; `exists_centeredGaussian_of_traceClass` gives the centred Gaussian
law, and the covariance on smooth tests is identified with `mu(phi * responseRep psi)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.G0

open HRS HRS.Sec7 HRS.StaticLimitAux Torus

variable {d : ℕ} {m : ℝ}

section Form

variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- the covariance form attached to a bounded operator `R` on `L²(μ)` -/
def s7g_Cmap (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hm : (d : ℝ) < 2 * m) :
    NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ).bilinearComp (Pmap μ ∘L Wmap μ hm)
    ((R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) ∘L (Pmap μ ∘L Wmap μ hm))

theorem s7g_Cmap_apply (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hm : (d : ℝ) < 2 * m)
    (x y : NegSobolev d m) :
    s7g_Cmap μ R hm x y = ⟪Pmap μ (Wmap μ hm x), R (Pmap μ (Wmap μ hm y))⟫ := by
  simp [s7g_Cmap]

theorem s7g_symm (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫)
    (hm : (d : ℝ) < 2 * m) (x y : NegSobolev d m) :
    s7g_Cmap μ R hm x y = s7g_Cmap μ R hm y x := by
  rw [s7g_Cmap_apply, s7g_Cmap_apply, ← hR, real_inner_comm]

theorem s7g_nonneg (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ∀ y, 0 ≤ ⟪R y, y⟫)
    (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) : 0 ≤ s7g_Cmap μ R hm x x := by
  rw [s7g_Cmap_apply, real_inner_comm]; exact hR _

theorem s7g_trace (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hm : (d : ℝ) < 2 * m) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (NegSobolev d m)),
      Summable fun i => s7g_Cmap μ R hm (b i) (b i) := by
  refine ⟨NonzeroLattice d, negBasis d m, ?_⟩
  have hb := negBasis_apply (d := d) (m := m)
  have hP : 0 ≤ ‖Pmap μ‖ := norm_nonneg _
  refine Summable.of_norm_bounded
    ((summable_wgt_sq (m := m) hm).mul_left (2 * ‖R‖ * ‖Pmap μ‖ ^ 2)) (fun k => ?_)
  rw [hb k, s7g_Cmap_apply]
  have h1 : ‖Wmap μ hm (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ))‖
      ≤ Real.sqrt 2 * wgt m k := by
    rw [Wmap_apply]
    refine norm_cl_le μ _ (mul_nonneg (Real.sqrt_nonneg _) (wgt_pos k).le) fun z => ?_
    rw [evalFun_single, abs_mul, abs_of_pos (wgt_pos k)]
    calc wgt m k * |realMode k z| ≤ wgt m k * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left (abs_realMode_le k z) (wgt_pos k).le
      _ = _ := by ring
  set e : Lp ℝ 2 μ := Pmap μ (Wmap μ hm (show NegSobolev d m from
    lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ))) with he
  have h3 : ‖e‖ ≤ ‖Pmap μ‖ * (Real.sqrt 2 * wgt m k) :=
    ((Pmap μ).le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 hP)
  have h4 : ‖e‖ ^ 2 ≤ (‖Pmap μ‖ * (Real.sqrt 2 * wgt m k)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  rw [Real.norm_eq_abs]
  calc |⟪e, R e⟫| ≤ ‖e‖ * ‖R e‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖R‖ * ‖e‖) := mul_le_mul_of_nonneg_left (R.le_opNorm e) (norm_nonneg _)
    _ = ‖R‖ * ‖e‖ ^ 2 := by ring
    _ ≤ ‖R‖ * (‖Pmap μ‖ * (Real.sqrt 2 * wgt m k)) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = 2 * ‖R‖ * ‖Pmap μ‖ ^ 2 * wgt m k ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring

end Form

section Ident

variable {ρ : Torus d → ℝ}

theorem s7g_cov_ident (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hρc : Continuous ρ) {Λ : ℝ} (H : PDE.MFLinear.KS (periodicRiesz d s) ρ Λ) (γ : ℝ) (hγ : 0 ≤ γ)
    [IsProbabilityMeasure (withDensityReal ρ)]
    (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ))
    (hAR : ∀ y, PDE.MFLinear.ALp H γ (R y) = y) (hm : (d : ℝ) < 2 * m) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    s7g_Cmap (withDensityReal ρ) R hm (avec m hφ) (avec m hψ) =
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) := by
  have hcφ := continuous_of_smooth hφ
  have hcψ := continuous_of_smooth hψ
  rw [s7g_Cmap_apply, Pmap_Wmap_avec (withDensityReal ρ) hm hφ, Pmap_Wmap_avec (withDensityReal ρ) hm hψ]
  set y2 := cl (withDensityReal ρ) (fun x => ψ x - pair (withDensityReal ρ) ψ) (hcψ.sub continuous_const) with hy2def
  have hy2 : ⇑y2 =ᵐ[(withDensityReal ρ)] projMean (withDensityReal ρ) ψ := cl_ae (withDensityReal ρ) _
  have hresp : IsResponse (periodicRiesz d s) (withDensityReal ρ) γ ψ ⇑(R y2) :=
    PDE.MFLinear.isResponse_of_A H γ ψ (R y2) (by rw [hAR]; exact hy2)
  obtain ⟨h0, -, huniq⟩ := PDE.MFLinear.exists_unique_response_of_one_le hd s hs0 hsd ρ hρ hρc γ hγ
    ψ (hcψ.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) γ ψ h := ⟨_, hresp⟩
  have hch : responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ =ᵐ[(withDensityReal ρ)] ⇑(R y2) := by
    unfold responseInverse
    simp only [hex, dite_true]
    exact (huniq _ hex.choose_spec).trans (huniq _ hresp).symm
  have hrep : responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ =ᵐ[(withDensityReal ρ)] ⇑(R y2) := by
    have e := PDE.MFLinear.Kop_congr (g := periodicRiesz d s) (ρ := ρ) hch
    filter_upwards [hresp.2.2] with x hx
    unfold responseRep
    rw [e]
    linarith
  have hint : Integrable (fun x => φ x * (R y2) x) (withDensityReal ρ) := by
    have h1 : Integrable (⇑(R y2)) (withDensityReal ρ) := (Lp.memLp (R y2)).integrable one_le_two
    obtain ⟨C, hC⟩ := (isCompact_univ.exists_bound_of_continuousOn hcφ.continuousOn)
    exact h1.bdd_mul hcφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  rw [inner_cl_left]
  have hz : ∫ x, (R y2) x ∂(withDensityReal ρ) = 0 := hresp.2.1
  calc ∫ x, (φ x - pair (withDensityReal ρ) φ) * (R y2) x ∂(withDensityReal ρ)
      = ∫ x, φ x * (R y2) x ∂(withDensityReal ρ) - pair (withDensityReal ρ) φ * ∫ x, (R y2) x ∂(withDensityReal ρ) := by
        simp_rw [sub_mul]
        rw [integral_sub hint ((Lp.memLp (R y2)).integrable one_le_two |>.const_mul _),
          integral_const_mul]
    _ = ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) := by
        rw [hz, mul_zero, sub_zero]
        exact integral_congr_ae (by filter_upwards [hrep] with x hx; rw [hx])

end Ident

theorem s7_G0_gaussian_exists_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) (γ : ℝ) (hγ : 0 ≤ γ) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ (G : Measure (NegSobolev d m)) (_ : IsProbabilityMeasure G),
      IsCenteredGaussianWithCov m G fun φ ψ =>
        ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hm' : (d : ℝ) < 2 * m := by linarith
  have hρc : Continuous ρ := continuous_of_smooth hρ.smooth
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have H : PDE.MFLinear.KS (periodicRiesz d s) ρ Λ :=
    ⟨PDE.MFOneLe.integrable_periodicRiesz hd1 s hs0 hsd, fun x => periodicRiesz_neg x, hρ.density,
      fun x => (le_abs_self _).trans (hΛ x (Set.mem_univ x))⟩
  have hP : IsProbabilityMeasure (withDensityReal ρ) := H.isProb
  obtain ⟨R, hRl, hRr, hRsym, hRpos⟩ := PDE.MFLinear.exists_inverse hd1 s hs0 hsd H hρc γ hγ
  obtain ⟨Gm, hp, hg, hcov⟩ := exists_centeredGaussian_of_traceClass
    (s7g_Cmap (withDensityReal ρ) R hm')
    ⟨s7g_symm _ R hRsym hm', s7g_nonneg _ R hRpos hm', s7g_trace _ R hm'⟩
  refine ⟨Gm, hp, hg, fun φ ψ hφ hψ => ?_⟩
  beta_reduce
  have := hg.1
  have hmem : MemLp id 2 Gm := ProbabilityTheory.IsGaussian.memLp_two_id
  have h := ProbabilityTheory.covarianceBilin_apply hmem (avec m hφ) (avec m hψ)
  rw [hcov, HilbertCLTAux.gaussian_mean_zero hg,
    s7g_cov_ident hd1 hs0 hsd hρ.density hρc H γ hγ R hRr hm' hφ hψ] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
  simp only [Pi.zero_apply, sub_zero, id]
  rw [eval_eq_inner m hφ, eval_eq_inner m hψ, real_inner_comm (avec m hφ), real_inner_comm (avec m hψ)]

end HRS.MC.Sec7.G0

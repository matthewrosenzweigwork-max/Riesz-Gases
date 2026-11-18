import HRS.Main.Headline
import HRS.Energy.StaticLimitGauss

/-!
# THERMLIN, part 1: existence of the Gaussian field with the prepared susceptibility covariance (`β₀ > 0`)

For the periodic Riesz kernel `g = periodicRiesz d s` (integrable, `ĝ ≥ 0`, but `ĝ` NOT summable), the response
operator `R = (I + β P K P)⁻¹` on `L²(μ)` is built from `HRS.ResponseAux` (Lax-Milgram), the form
`C(x, y) = ⟨P W x, R P W y⟩` on `E_m` is a symmetric nonnegative trace-class form, and the centered Gaussian
measure with this covariance (`exists_centeredGaussian_of_traceClass`) has covariance `susceptibilityCov` on smooth
tests.  This is the analogue of `HRS.StaticLimitAux.exists_gauss_spec` for a non-summable spectral kernel.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.ThermLin

open HRS Torus

variable {d : ℕ} {g ρ : Torus d → ℝ} {Λ : ℝ}

section Resp

variable (S : ResponseAux.Setup g ρ Λ) [IsProbabilityMeasure (withDensityReal ρ)]

/-- `K` is self-adjoint on `L²(μ)`. -/
theorem thermlin_KL_selfadjoint (u v : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (ResponseAux.KL S u) v = inner ℝ u (ResponseAux.KL S v) := by
  obtain ⟨ĝ, hĝ, hcoef⟩ := S.hĝ
  have h := ResponseAux.Kt_form_symm S.hρ S.hΛ S.hg S.hgi ĝ hcoef (Lp.memLp u) (Lp.memLp v)
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, inner ℝ ((ResponseAux.KL S u : Lp ℝ 2 (withDensityReal ρ)) x) (v x) ∂(withDensityReal ρ) =
      ∫ x, ResponseAux.Kt g (withDensityReal ρ) u x * v x ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [ResponseAux.KLfun_coe S u] with x hx
    rw [ResponseAux.KL_apply, hx]
    simp [mul_comm]
  have e2 : ∫ x, inner ℝ (u x) ((ResponseAux.KL S v : Lp ℝ 2 (withDensityReal ρ)) x) ∂(withDensityReal ρ) =
      ∫ x, ResponseAux.Kt g (withDensityReal ρ) v x * u x ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [ResponseAux.KLfun_coe S v] with x hx
    rw [ResponseAux.KL_apply, hx]
    simp [mul_comm]
  rw [e1, e2]
  exact h

/-- The operator `T = I + β P K P` is self-adjoint. -/
theorem thermlin_Top_selfadjoint (β : ℝ) (u v : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β u) v =
      inner ℝ u (ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β v) := by
  rw [ResponseAux.Top_apply, ResponseAux.Top_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, ResponseAux.inner_projL_left, thermlin_KL_selfadjoint S,
    ← ResponseAux.inner_projL_left]
  simp only [conj_trivial]

theorem thermlin_Top_bij {β : ℝ} (hβ : 0 ≤ β) :
    Function.Bijective (ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β) :=
  ResponseAux.bijective_of_coercive _
    (ResponseAux.Top_coercive (one := ResponseAux.oneL S.hρ) (ResponseAux.inner_KL_nonneg S) hβ)

/-- The resolvent `(I + β P K P)⁻¹` as a continuous linear equivalence. -/
def thermlinRr {β : ℝ} (hβ : 0 ≤ β) : Lp ℝ 2 (withDensityReal ρ) ≃L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  (ContinuousLinearEquiv.ofBijective (ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β)
    (LinearMap.ker_eq_bot.2 (thermlin_Top_bij S hβ).1) (LinearMap.range_eq_top.2 (thermlin_Top_bij S hβ).2)).symm

theorem thermlinRr_spec {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 (withDensityReal ρ)) :
    ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β (thermlinRr S hβ z) = z := by
  unfold thermlinRr
  exact (ContinuousLinearEquiv.ofBijective (ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β)
    (LinearMap.ker_eq_bot.2 (thermlin_Top_bij S hβ).1)
    (LinearMap.range_eq_top.2 (thermlin_Top_bij S hβ).2)).apply_symm_apply z

theorem thermlinRr_norm_le {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 (withDensityReal ρ)) :
    ‖thermlinRr S hβ z‖ ≤ ‖z‖ := by
  set u := thermlinRr S hβ z with hu
  have hc := ResponseAux.Top_coercive (one := ResponseAux.oneL S.hρ) (ResponseAux.inner_KL_nonneg S) hβ u
  rw [thermlinRr_spec S hβ z] at hc
  have h4 : inner ℝ z u ≤ ‖z‖ * ‖u‖ := real_inner_le_norm z u
  by_cases h0 : ‖u‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- The covariance form of the Gaussian target as a continuous bilinear form on `E_m`. -/
def thermlinCmap (m : ℝ) (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 ≤ β) :
    NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) →L[ℝ] ℝ).bilinearComp
    (ResponseAux.projL (ResponseAux.oneL S.hρ) ∘L StaticLimitAux.Wmap (withDensityReal ρ) hm)
    ((thermlinRr S hβ : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ)) ∘L
      (ResponseAux.projL (ResponseAux.oneL S.hρ) ∘L StaticLimitAux.Wmap (withDensityReal ρ) hm))

theorem thermlinCmap_apply (m : ℝ) (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 ≤ β) (x y : NegSobolev d m) :
    thermlinCmap S m hm hβ x y =
      inner ℝ (ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap (withDensityReal ρ) hm x))
        (thermlinRr S hβ (ResponseAux.projL (ResponseAux.oneL S.hρ)
          (StaticLimitAux.Wmap (withDensityReal ρ) hm y))) := by
  simp [thermlinCmap]

theorem thermlinCmap_symm (m : ℝ) (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 ≤ β) (x y : NegSobolev d m) :
    thermlinCmap S m hm hβ x y = thermlinCmap S m hm hβ y x := by
  rw [thermlinCmap_apply, thermlinCmap_apply]
  set zx := ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap (withDensityReal ρ) hm x)
  set zy := ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap (withDensityReal ρ) hm y)
  have h := thermlin_Top_selfadjoint S β (thermlinRr S hβ zx) (thermlinRr S hβ zy)
  rw [thermlinRr_spec S hβ, thermlinRr_spec S hβ] at h
  exact h.trans (real_inner_comm _ _).symm

theorem thermlinCmap_nonneg (m : ℝ) (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 ≤ β) (x : NegSobolev d m) :
    0 ≤ thermlinCmap S m hm hβ x x := by
  rw [thermlinCmap_apply]
  set zx := ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap (withDensityReal ρ) hm x)
  have hc := ResponseAux.Top_coercive (one := ResponseAux.oneL S.hρ) (ResponseAux.inner_KL_nonneg S) hβ
    (thermlinRr S hβ zx)
  rw [thermlinRr_spec S hβ zx] at hc
  nlinarith [mul_self_nonneg ‖thermlinRr S hβ zx‖]

theorem thermlinCmap_le (m : ℝ) (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 ≤ β) (x : NegSobolev d m) :
    thermlinCmap S m hm hβ x x ≤ ‖ResponseAux.projL (ResponseAux.oneL S.hρ)
      (StaticLimitAux.Wmap (withDensityReal ρ) hm x)‖ ^ 2 := by
  rw [thermlinCmap_apply]
  set zx := ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap (withDensityReal ρ) hm x)
  calc inner ℝ zx (thermlinRr S hβ zx) ≤ ‖zx‖ * ‖thermlinRr S hβ zx‖ := real_inner_le_norm _ _
    _ ≤ ‖zx‖ * ‖zx‖ := mul_le_mul_of_nonneg_left (thermlinRr_norm_le S hβ _) (norm_nonneg _)
    _ = _ := by ring

theorem thermlinCmap_trace (m : ℝ) (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (NegSobolev d m)),
      Summable fun i => thermlinCmap S m hm hβ (b i) (b i) := by
  refine ⟨NonzeroLattice d, StaticLimitAux.negBasis d m, ?_⟩
  have hb := StaticLimitAux.negBasis_apply (d := d) (m := m)
  set Pn := ‖(ResponseAux.projL (ResponseAux.oneL S.hρ) : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] _)‖ with hPn
  refine Summable.of_nonneg_of_le (fun k => thermlinCmap_nonneg S m hm hβ _)
    (fun k => ?_) ((StaticLimitAux.summable_wgt_sq (m := m) hm).mul_left (2 * Pn ^ 2))
  rw [hb k]
  refine (thermlinCmap_le S m hm hβ _).trans ?_
  have h1 : ‖StaticLimitAux.Wmap (withDensityReal ρ) hm
      (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ))‖
      ≤ Real.sqrt 2 * StaticLimitAux.wgt m k := by
    rw [StaticLimitAux.Wmap_apply]
    refine StaticLimitAux.norm_cl_le (withDensityReal ρ) _
      (mul_nonneg (Real.sqrt_nonneg _) (StaticLimitAux.wgt_pos k).le) fun z => ?_
    rw [StaticLimitAux.evalFun_single, abs_mul, abs_of_pos (StaticLimitAux.wgt_pos k)]
    calc StaticLimitAux.wgt m k * |realMode k z| ≤ StaticLimitAux.wgt m k * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left (abs_realMode_le k z) (StaticLimitAux.wgt_pos k).le
      _ = _ := by ring
  have h2 := (ResponseAux.projL (ResponseAux.oneL S.hρ) : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] _).le_opNorm
    (StaticLimitAux.Wmap (withDensityReal ρ) hm
      (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)))
  have h3 : ‖ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap (withDensityReal ρ) hm
      (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)))‖
      ≤ Pn * (Real.sqrt 2 * StaticLimitAux.wgt m k) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  calc _ ≤ (Pn * (Real.sqrt 2 * StaticLimitAux.wgt m k)) ^ 2 := h4
    _ = 2 * Pn ^ 2 * StaticLimitAux.wgt m k ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring

theorem thermlin_Pmap_eq (f : Lp ℝ 2 (withDensityReal ρ)) :
    StaticLimitAux.Pmap (withDensityReal ρ) f = ResponseAux.projL (ResponseAux.oneL S.hρ) f := by
  refine Lp.ext ?_
  filter_upwards [StaticLimitAux.Pmap_ae (withDensityReal ρ) f, ResponseAux.projL_coe S.hρ f] with x h1 h2
  rw [h1, h2]

/-- The covariance form evaluated at two smooth test vectors is the susceptibility covariance. -/
theorem thermlinCmap_avec {g₀ : Torus d → ℝ} (hgg : g =ᵐ[volume] g₀) (m : ℝ) (hm : (d : ℝ) < 2 * m)
    {β : ℝ} (hβ : 0 ≤ β) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    thermlinCmap S m hm hβ (StaticLimitAux.avec m hφ) (StaticLimitAux.avec m hψ) =
      susceptibilityCov g₀ (withDensityReal ρ) β φ ψ := by
  set μ := withDensityReal ρ with hμ
  have hcφ := StaticLimitAux.continuous_of_smooth hφ
  have hcψ := StaticLimitAux.continuous_of_smooth hψ
  have hzφ : ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap μ hm (StaticLimitAux.avec m hφ)) =
      StaticLimitAux.cl μ (fun x => φ x - pair μ φ) (hcφ.sub continuous_const) := by
    rw [← thermlin_Pmap_eq S]
    exact StaticLimitAux.Pmap_Wmap_avec μ hm hφ
  have hzψ : ResponseAux.projL (ResponseAux.oneL S.hρ) (StaticLimitAux.Wmap μ hm (StaticLimitAux.avec m hψ)) =
      StaticLimitAux.cl μ (fun x => ψ x - pair μ ψ) (hcψ.sub continuous_const) := by
    rw [← thermlin_Pmap_eq S]
    exact StaticLimitAux.Pmap_Wmap_avec μ hm hψ
  rw [thermlinCmap_apply, hzφ, hzψ]
  set zψ := StaticLimitAux.cl μ (fun x => ψ x - pair μ ψ) (hcψ.sub continuous_const) with hzψdef
  set u := thermlinRr S hβ zψ with hudef
  have hψmem : MemLp ψ 2 μ := hcψ.memLp_of_hasCompactSupport (μ := μ) (p := 2) (HasCompactSupport.of_compactSpace _)
  have hPz : ResponseAux.projL (ResponseAux.oneL S.hρ) zψ = zψ := by
    rw [← hzψ, ResponseAux.projL_projL (ResponseAux.norm_oneL S.hρ)]
  have hTu : ResponseAux.Top (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β u = zψ := thermlinRr_spec S hβ zψ
  have hPu : ResponseAux.projL (ResponseAux.oneL S.hρ) u = u := by
    have h1 := ResponseAux.Top_apply (ResponseAux.oneL S.hρ) (ResponseAux.KL S) β u
    rw [hTu] at h1
    have h2 : u = zψ - β • ResponseAux.projL (ResponseAux.oneL S.hρ)
        (ResponseAux.KL S (ResponseAux.projL (ResponseAux.oneL S.hρ) u)) := by
      rw [h1]; abel
    conv_lhs => rw [h2]
    rw [map_sub, map_smul, hPz, ResponseAux.projL_projL (ResponseAux.norm_oneL S.hρ)]
    exact h2.symm
  have hwz : ResponseAux.projL (ResponseAux.oneL S.hρ) (hψmem.toLp ψ) = zψ := by
    refine Lp.ext ?_
    have hwint : ∫ x, ((hψmem.toLp ψ : Lp ℝ 2 μ) : Torus d → ℝ) x ∂μ = ∫ x, ψ x ∂μ :=
      integral_congr_ae hψmem.coeFn_toLp
    filter_upwards [ResponseAux.projL_coe S.hρ (hψmem.toLp ψ), hψmem.coeFn_toLp,
      StaticLimitAux.cl_ae μ (f := fun x => ψ x - pair μ ψ) (hcψ.sub continuous_const)] with x h1 h2 h3
    rw [h1, hwint, h2, hzψdef, h3]
    rfl
  have hresp : ResponseAux.RespEq g μ β ψ u := by
    rw [ResponseAux.respEq_iff S β hψmem (Lp.memLp u), Lp.toLp_coeFn]
    exact ⟨hPu, by rw [hTu, hwz]⟩
  have hresp₀ : ResponseAux.RespEq g₀ μ β ψ u :=
    (ResponseAux.RespEq_congr_kernel hgg ρ β ψ u).1 hresp
  have hex : ∃ h, IsResponse g₀ μ β ψ h := ⟨u, hresp₀⟩
  unfold susceptibilityCov responseInverse
  rw [dif_pos hex]
  have hr0 : ResponseAux.RespEq g₀ μ β ψ hex.choose := hex.choose_spec
  obtain ⟨h, -, hu⟩ := ResponseAux.exists_unique_respEq S hβ hψmem
  have h1 : (hex.choose : Torus d → ℝ) =ᵐ[μ] h :=
    hu _ ((ResponseAux.RespEq_congr_kernel hgg ρ β ψ _).2 hr0)
  have h2 : (u : Torus d → ℝ) =ᵐ[μ] h := hu _ hresp
  unfold l2Inner
  rw [StaticLimitAux.inner_cl_left]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with x a b
  simp only [projMean]
  rw [a, ← b]

end Resp

section Final

/-- Existence of the centered Gaussian measure with the susceptibility covariance for a kernel with a
`Setup` (integrable, measurable, nonnegative Fourier coefficients), not necessarily bounded. -/
theorem thermlin_exists_gauss_kernel (S : ResponseAux.Setup g ρ Λ) {g₀ : Torus d → ℝ}
    (hgg : g =ᵐ[volume] g₀) {β : ℝ} (hβ : 0 ≤ β) (m : ℝ) (hm : (d : ℝ) < 2 * m) :
    ∃ γ : Measure (NegSobolev d m), IsProbabilityMeasure γ ∧
      HRS.IsCenteredGaussianWithCov m γ (susceptibilityCov g₀ (withDensityReal ρ) β) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := ResponseAux.isProbabilityMeasure_dens S.hρ
  obtain ⟨γ, hp, hg, hcov⟩ := exists_centeredGaussian_of_traceClass (thermlinCmap S m hm hβ)
    ⟨thermlinCmap_symm S m hm hβ, thermlinCmap_nonneg S m hm hβ, thermlinCmap_trace S m hm hβ⟩
  refine ⟨γ, hp, hg, fun φ ψ hφ hψ => ?_⟩
  have := hg.1
  have hmem : MemLp id 2 γ := ProbabilityTheory.IsGaussian.memLp_two_id
  have h := ProbabilityTheory.covarianceBilin_apply hmem (StaticLimitAux.avec m hφ) (StaticLimitAux.avec m hψ)
  rw [hcov, HilbertCLTAux.gaussian_mean_zero hg, thermlinCmap_avec S hgg m hm hβ hφ hψ] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
  simp only [Pi.zero_apply, sub_zero, id]
  rw [StaticLimitAux.eval_eq_inner m hφ, StaticLimitAux.eval_eq_inner m hψ,
    real_inner_comm (StaticLimitAux.avec m hφ), real_inner_comm (StaticLimitAux.avec m hψ)]

end Final

end HRS.ThermLin

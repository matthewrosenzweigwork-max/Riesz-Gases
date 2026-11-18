import HRS.Main.ThermLin2Mo5

/-!
# THERMLIN2 Mo6: second moment of `⟨Zw^r, φ⟩` (helper for `tl2_Zw_moment`)

`E ⟨Zw^r,φ⟩² = ∫_0^r 2β⁻¹ ∫ |∇ U^β_{σ,r}φ|² ρ^σ dx dσ`, from the Gaussian law `t25p_Zb_gaussian` with `p = 1`
(the diagonal case of `tl2_cov_mixed`; the single-evolution lemma suffices).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q48c

variable {d : ℕ}

theorem tl2Mo6_gauss_sq (v : ℝ≥0) :
    ∫⁻ y : ℝ, ENNReal.ofReal (y ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (v : ℝ) := by
  have hm : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
    have := memLp_id_gaussianReal (μ := 0) (v := v) 2
    simpa using this
  have h2 : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 v) = v := by
    have hv := variance_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_sub hm] at hv
    simp only [Pi.pow_apply] at hv
    simpa using hv
  have hi : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 v) := by
    have := hm.integrable_sq
    simpa using this
  rw [← h2, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun y => sq_nonneg y)]

/-- Second moment of the pairing of the `W`-convolution `Zw` with a smooth test function. -/
theorem tl2Mo6_second_moment (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m)
    {T' : ℝ} (hT' : 0 < T') {W : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution S.dyn (fun _ => ρβ) m W) (hplain : IsPlainEvolution W T')
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖W t r‖ ≤ K)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zw : ℝ → Ω → NegSobolev d m)
    (hZw : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P W (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t))
    (hZm : ∀ t, Measurable (Zw t)) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    ∫⁻ ω, ENNReal.ofReal ((NegSobolev.eval (Zw r ω) φ) ^ 2) ∂P =
      ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) r, 2 * S.β⁻¹ *
        ∫ x, inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x) * S.ρ σ x) := by
  have hmemφ : MemSobolev m φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  have hlaw := t25p_Zb_gaussian hK hT' W hplain.2.2 hKb P G _ hG hGc hGz Zw hZw hZm (p := 1)
    (fun _ => r) (fun _ => hr) (fun _ => φ) (fun _ => hmemφ)
  set v : ℝ := ∫ σ in Set.Icc (0 : ℝ) r, 2 * S.β⁻¹ *
        ∫ x, inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x) * S.ρ σ x with hv
  have hcov : ∀ σ ∈ Set.Icc (0 : ℝ) r,
      covDensT m S.β⁻¹ T' S.ρ σ (pullbackVec (HRS.Uniform.Comp28.plainData W) r σ (gfb4_ell m φ))
        (pullbackVec (HRS.Uniform.Comp28.plainData W) r σ (gfb4_ell m φ)) =
      2 * S.β⁻¹ * ∫ x, inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x) * S.ρ σ x :=
    fun σ hσ => tl2Mo5_cov_diag S h hm hT' hdual hK hKb hσ hr.2 hφ
  have hv0 : 0 ≤ v := by
    refine setIntegral_nonneg measurableSet_Icc fun σ hσ => ?_
    have hq : 0 ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
    refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
    exact mul_nonneg (real_inner_self_nonneg) ((tl2Mo_rho_density S hσ.1).nonneg x)
  have hS : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v) = Matrix.of fun (a b : Fin 1) =>
      ∫ σ in Set.Icc 0 (min ((fun _ : Fin 1 => r) a) ((fun _ : Fin 1 => r) b)),
        covDensT m S.β⁻¹ T' S.ρ σ
          (pullbackVec (HRS.Uniform.Comp28.plainData W) ((fun _ : Fin 1 => r) a) σ (gfb4_ell m ((fun _ : Fin 1 => φ) a)))
          (pullbackVec (HRS.Uniform.Comp28.plainData W) ((fun _ : Fin 1 => r) b) σ (gfb4_ell m ((fun _ : Fin 1 => φ) b))) := by
    ext a b
    simp only [Matrix.of_apply, min_self]
    rw [hv]
    exact (setIntegral_congr_fun measurableSet_Icc fun σ hσ => hcov σ hσ).symm
  rw [← hS] at hlaw
  have hPSD : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v).PosSemidef := by
    have : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v) = Matrix.diagonal (fun _ => v) := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [this]
    exact Matrix.posSemidef_diagonal_iff.2 fun _ => hv0
  have hXm : Measurable (fun ω => (WithLp.toLp 2 fun a : Fin 1 => NegSobolev.eval (Zw ((fun _ : Fin 1 => r) a) ω) ((fun _ : Fin 1 => φ) a) : EuclideanSpace ℝ (Fin 1))) := by
    refine measurable_toLp_eval fun a => ?_
    exact (continuous_eval_const hmemφ).measurable.comp (hZm _)
  have h1 : ∫⁻ ω, ENNReal.ofReal ((NegSobolev.eval (Zw r ω) φ) ^ 2) ∂P =
      ∫⁻ x, ENNReal.ofReal ((x 0) ^ 2) ∂(P.map (fun ω => (WithLp.toLp 2 fun a : Fin 1 => NegSobolev.eval (Zw ((fun _ : Fin 1 => r) a) ω) ((fun _ : Fin 1 => φ) a) : EuclideanSpace ℝ (Fin 1)))) := by
    rw [lintegral_map (by fun_prop) hXm]
  rw [h1, hlaw]
  have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1)))
    (S := Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v) hPSD (i := 0)
  have h2 : ∫⁻ x : EuclideanSpace ℝ (Fin 1), ENNReal.ofReal ((x 0) ^ 2)
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => v)) =
      ∫⁻ y : ℝ, ENNReal.ofReal (y ^ 2) ∂(gaussianReal 0 v.toNNReal) := by
    have hmp' := hmp.map_eq
    simp only [Matrix.of_apply, WithLp.ofLp_zero, Pi.zero_apply] at hmp'
    rw [← hmp', lintegral_map (by fun_prop) hmp.measurable]
  rw [h2, tl2Mo6_gauss_sq]
  simp [Real.coe_toNNReal _ hv0]

end HRS.ThermLin.Plan2

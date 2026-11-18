import HRS.Sections.Sec7Fields
import HRS.Energy.StaticLimitGauss

/-!
# Packet L2C-6, helper 1: Gaussian bookkeeping for the second moment of `η^t(φ)`

Abstract second-moment bound shared by L2C-6a and L2C-6b.  From a centred Gaussian initial law and the
`gaussian_part` of an `IsLinearFluctuationSolution` (with `p = 1`) one gets `η^t(φ) = Y₀(ψ) + g`,
`ψ = U^{0,t}φ`, with `Y₀(ψ)` Gaussian (continuity of `F ↦ F(ψ)` on `E_m`) and `g` the coordinate of a
`multivariateGaussian 0 S` with `S 0 0 = noiseCovariance`; hence `MemLp 2` and
`E[η^t(φ)²] ≤ 2 Cov(ψ,ψ) + 2 max(noiseCovariance, 0)` (no independence is needed for this bound).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HRS.MC.L2C6Aux

variable {d : ℕ}

theorem l2c6_cont_of_smooth {φ : Torus d → ℝ} (h : Torus.IsSmooth φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from h).continuous

/-- `F ↦ F(ψ)` is a continuous linear functional of `E_m` for smooth `ψ`. -/
theorem l2c6_eval_clm (m : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∃ L : StrongDual ℝ (NegSobolev d m), ∀ F, L F = NegSobolev.eval F ψ := by
  refine ⟨innerSL ℝ (HRS.StaticLimitAux.avec m hψ), fun F => ?_⟩
  rw [HRS.StaticLimitAux.eval_eq_inner m hψ F]
  simp [real_inner_comm]

theorem l2c6_eval_continuous (m : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    Continuous fun F : NegSobolev d m => NegSobolev.eval F ψ := by
  obtain ⟨L, hL⟩ := l2c6_eval_clm m hψ
  have : (fun F : NegSobolev d m => NegSobolev.eval F ψ) = fun F => L F := funext fun F => (hL F).symm
  rw [this]
  exact L.continuous

theorem l2c6_eval_memLp (m : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ)
    (γ : Measure (NegSobolev d m)) [IsGaussian γ] :
    MemLp (fun F : NegSobolev d m => NegSobolev.eval F ψ) 2 γ := by
  obtain ⟨L, hL⟩ := l2c6_eval_clm m hψ
  have h := IsGaussian.memLp_dual γ L 2 (by simp)
  have : (fun F : NegSobolev d m => NegSobolev.eval F ψ) = fun F => L F := funext fun F => (hL F).symm
  rw [this]
  exact h

/-- Second moment of a coordinate of a centred multivariate Gaussian on `ℝ¹`. -/
theorem l2c6_gauss_coord_sq (S : Matrix (Fin 1) (Fin 1) ℝ) :
    MemLp (fun s : EuclideanSpace ℝ (Fin 1) => s 0) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) ∧
    ∫ s : EuclideanSpace ℝ (Fin 1), s 0 ^ 2
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) ≤ max (S 0 0) 0 := by
  have hmem : MemLp (fun s : EuclideanSpace ℝ (Fin 1) => s 0) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) := by
    have := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S)
      (EuclideanSpace.proj (0 : Fin 1) : StrongDual ℝ (EuclideanSpace ℝ (Fin 1))) 2 (by norm_num)
    simpa using this
  refine ⟨hmem, ?_⟩
  by_cases hS : S.PosSemidef
  · have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1))) hS 0 0
    have hmean : ∫ s : EuclideanSpace ℝ (Fin 1), s 0
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) = 0 := by
      have h := ContinuousLinearMap.integral_comp_comm
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)
        (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S))
      simp at h
      simpa using h
    rw [covariance_eq_sub hmem hmem, hmean, zero_mul, sub_zero] at h
    have : ∫ s : EuclideanSpace ℝ (Fin 1), s 0 ^ 2
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) S) = S 0 0 := by
      simpa [sq] using h
    rw [this]; exact le_max_left _ _
  · rw [multivariateGaussian_of_not_posSemidef _ hS]
    have : ∫ s : EuclideanSpace ℝ (Fin 1), s 0 ^ 2 ∂(Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))) = 0 := by
      rw [integral_dirac' _ _ (by fun_prop)]
      simp
    rw [this]; exact le_max_right _ _

/-- The abstract second-moment bound. -/
theorem l2c6_second_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m q : ℝ)
    (Cov : (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (Y₀ : Ω → NegSobolev d m) (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsCenteredGaussianWithCov m (P.map Y₀) Cov)
    (hS : ∀ T : ℝ, IsLinearFluctuationSolution P D ρ m q T Y₀ Y)
    {t : ℝ} (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth (propagator D ρ 0 t φ)) :
    MemLp (fun ω => NegSobolev.eval (Y t ω) φ) 2 P ∧
    ∫ ω, NegSobolev.eval (Y t ω) φ ^ 2 ∂P ≤
      2 * Cov (propagator D ρ 0 t φ) (propagator D ρ 0 t φ) +
        2 * max (noiseCovariance D ρ q t φ φ) 0 := by
  have hsol := hS t
  set ψ := propagator D ρ 0 t φ with hψdef
  have hY₀ : AEMeasurable Y₀ P := by
    refine ((hsol.meas 0).aemeasurable).congr ?_
    filter_upwards [hsol.init] with ω h using h
  have : IsGaussian (P.map Y₀) := hY.1.1
  have hcont := l2c6_eval_continuous m hψ
  have hcontφ := l2c6_eval_continuous m hφ
  -- the initial part
  set a : Ω → ℝ := fun ω => NegSobolev.eval (Y₀ ω) ψ with ha
  have hma : MemLp a 2 P := (l2c6_eval_memLp m hψ (P.map Y₀)).comp_of_map hY₀
  have hEa : ∫ ω, a ω ^ 2 ∂P = Cov ψ ψ := by
    have h1 : ∫ ω, a ω ^ 2 ∂P = ∫ F, NegSobolev.eval F ψ ^ 2 ∂(P.map Y₀) :=
      (integral_map (f := fun F : NegSobolev d m => NegSobolev.eval F ψ ^ 2) hY₀
        (show Continuous fun F : NegSobolev d m => NegSobolev.eval F ψ ^ 2 from
          hcont.pow 2).aestronglyMeasurable).symm
    rw [h1, ← hY.2 ψ ψ hψ hψ]
    simp [sq]
  -- the Gaussian part
  obtain ⟨-, hlaw⟩ := hsol.gaussian_part 1 (fun _ => t) (fun _ => φ) (fun _ => ⟨ht, le_rfl⟩)
    (fun _ => hφ)
  set G : Ω → EuclideanSpace ℝ (Fin 1) := fun ω => WithLp.toLp 2 fun _ =>
    NegSobolev.eval (Y t ω) φ - a ω with hG
  set S : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ =>
    noiseCovariance D ρ q t φ φ with hSdef
  have hlaw' : P.map G = multivariateGaussian 0 S := by
    have : S = Matrix.of fun _ _ => 2 * q * ∫ r in Set.Icc 0 (min t t), ∫ x,
        inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) * ρ r x := by
      simp [hSdef, noiseCovariance]
    rw [this]
    exact hlaw
  have hGm : AEMeasurable G P := by
    have hv : AEMeasurable (fun ω => NegSobolev.eval (Y t ω) φ - a ω) P :=
      ((hcontφ.measurable.comp (hsol.meas t)).aemeasurable).sub
        (hcont.measurable.comp_aemeasurable hY₀)
    exact (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun _ => hv)
  obtain ⟨hmg, hEg⟩ := l2c6_gauss_coord_sq S
  rw [← hlaw'] at hmg hEg
  have hMg : MemLp (fun ω => G ω 0) 2 P := hmg.comp_of_map hGm
  have hEg' : ∫ ω, G ω 0 ^ 2 ∂P ≤ max (noiseCovariance D ρ q t φ φ) 0 := by
    have h1 : ∫ ω, G ω 0 ^ 2 ∂P = ∫ s : EuclideanSpace ℝ (Fin 1), s 0 ^ 2 ∂(P.map G) := by
      rw [integral_map hGm (by fun_prop)]
    rw [h1]
    simpa [hSdef] using hEg
  have hsum : ∀ ω, NegSobolev.eval (Y t ω) φ = a ω + G ω 0 := fun ω => by simp [hG]
  have hfun : (fun ω => NegSobolev.eval (Y t ω) φ) = fun ω => a ω + G ω 0 := funext hsum
  refine ⟨by rw [hfun]; exact hma.add hMg, ?_⟩
  simp_rw [hsum]
  have hia := hma.integrable_sq
  have hig := hMg.integrable_sq
  calc ∫ ω, (a ω + G ω 0) ^ 2 ∂P ≤ ∫ ω, (2 * a ω ^ 2 + 2 * G ω 0 ^ 2) ∂P := by
        refine integral_mono ((hma.add hMg).integrable_sq) ((hia.const_mul 2).add (hig.const_mul 2))
          fun ω => ?_
        nlinarith [sq_nonneg (a ω - G ω 0)]
    _ = 2 * ∫ ω, a ω ^ 2 ∂P + 2 * ∫ ω, G ω 0 ^ 2 ∂P := by
        rw [integral_add (hia.const_mul 2) (hig.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by rw [hEa]; linarith [hEg']

end HRS.MC.L2C6Aux

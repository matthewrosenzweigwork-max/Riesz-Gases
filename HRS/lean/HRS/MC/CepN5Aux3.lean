import HRS.Stochastic.Ito

/-!
# Packet N5, helper 3: Dynkin's formula at a bounded stopping time (additive noise)

For the Itô process `X = X₀ + ∫ b + σ W` (`b` progressive and bounded), a bounded stopping time `τ ≤ dur`
with `X ∈ [lo, hi]` up to `τ`, and `f ∈ C²(ℝ)`, for every `A ∈ 𝒢 0`:
`∫_A f(X_τ) = ∫_A f(X₀) + ∫_A ∫_0^τ (f'(X_s) b_s + σ²/2 f''(X_s)) ds`.
(Uses `ito_stopped`; the stochastic integral stopped at `τ` is a martingale started at `0`.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem n5_fderiv_apply (f : ℝ → ℝ) (x v : ℝ) : fderiv ℝ f x v = v * deriv f x := by
  rw [fderiv_eq_smul_deriv]; simp

theorem n5_fderiv2_apply {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x v w : ℝ) :
    fderiv ℝ (fderiv ℝ f) x v w = v * w * deriv (deriv f) x := by
  have e : fderiv ℝ f = fun y => deriv f y • (ContinuousLinearMap.id ℝ ℝ) := by
    funext y; ext1; simp [n5_fderiv_apply]
  have hd : DifferentiableAt ℝ (deriv f) x := hf.differentiable_deriv_two x
  have h := (hd.hasFDerivAt.smul_const (ContinuousLinearMap.id ℝ ℝ)).fderiv
  rw [e, h]
  simp [n5_fderiv_apply]
  ring

/-- The Itô drift of a time-independent `f ∈ C²(ℝ)` with constant noise coefficient `σ`. -/
theorem n5_itoDrift {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (T : ℝ) (X b : ℝ → Ω → ℝ) (σ : ℝ) (s : ℝ)
    (ω : Ω) :
    itoDrift T (fun _ x => f x) X b (fun _ _ (_ : Fin 1) => σ) s ω =
      deriv f (X s ω) * b s ω + σ ^ 2 / 2 * deriv (deriv f) (X s ω) := by
  unfold itoDrift
  have h0 : derivWithin (fun _ : ℝ => f (X s ω)) (Icc 0 T) s = 0 := by rw [derivWithin_fun_const]; rfl
  simp only [h0, Fin.sum_univ_one, n5_fderiv_apply, n5_fderiv2_apply hf]
  ring

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝒢 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin 1 → ℝ}

/-- The Itô process with constant noise coefficient. -/
abbrev n5_X (P : Measure Ω) (𝒢 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin 1 → ℝ) (σ : ℝ)
    (X₀ : Ω → ℝ) (b : ℝ → Ω → ℝ) : ℝ → Ω → ℝ :=
  itoProcess P 𝒢 W X₀ b (fun _ _ (_ : Fin 1) => σ)

theorem n5_locL1 {b : ℝ → Ω → ℝ} (hb : IsProgressive 𝒢 b) {M : ℝ} (hbM : ∀ s ω, |b s ω| ≤ M) :
    IsProgressiveLocL1 P 𝒢 b := by
  refine ⟨hb, fun T => ae_of_all _ fun ω => ?_⟩
  have hm : Measurable fun s => b s ω :=
    (measurable_of_progressive hb).comp (measurable_id.prodMk measurable_const)
  exact (integrableOn_const (by simp)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun s => by simpa using hbM s ω)

omit [IsProbabilityMeasure P] in
theorem n5_locL2E (σ : ℝ) (𝒢 : Filtration ℝ mΩ) :
    IsProgressiveLocL2E P 𝒢 (fun _ _ (_ : Fin 1) => σ) := by
  refine ⟨isProgressive_const 𝒢 (fun _ : Fin 1 => σ), fun T => ae_of_all _ fun ω => ?_⟩
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (by simp) (by simp)


/-- **Dynkin's formula** for the Itô process `X = X₀ + ∫ b + σ W` at a bounded stopping time. -/
theorem n5_core (hW : IsBrownianFiltration P 𝒢 W) {dur σ M lo hi : ℝ} (hdur : 0 ≤ dur)
    {X₀ : Ω → ℝ} (hX₀ : ∀ t : ℝ, Measurable[𝒢 t] X₀)
    {b : ℝ → Ω → ℝ} (hb : IsProgressive 𝒢 b) (hbM : ∀ s ω, |b s ω| ≤ M)
    {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime 𝒢 τ) {τr : Ω → ℝ} (hτr : ∀ ω, τ ω = (τr ω : WithTop ℝ))
    (hτ0 : ∀ ω, 0 ≤ τr ω) (hτd : ∀ ω, τr ω ≤ dur)
    (hXK : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 dur, (t : WithTop ℝ) ≤ τ ω → n5_X P 𝒢 W σ X₀ b t ω ∈ Icc lo hi)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (∀ᵐ ω ∂P, IntegrableOn (fun s => deriv f (n5_X P 𝒢 W σ X₀ b s ω) * b s ω +
        σ ^ 2 / 2 * deriv (deriv f) (n5_X P 𝒢 W σ X₀ b s ω)) (Icc 0 (τr ω))) ∧
    Integrable (fun ω => f (n5_X P 𝒢 W σ X₀ b (τr ω) ω)) P ∧
    Integrable (fun ω => f (X₀ ω)) P ∧
    Integrable (fun ω => ∫ s in Icc 0 (τr ω), (deriv f (n5_X P 𝒢 W σ X₀ b s ω) * b s ω +
        σ ^ 2 / 2 * deriv (deriv f) (n5_X P 𝒢 W σ X₀ b s ω))) P ∧
    ∀ A, MeasurableSet[𝒢 0] A →
      ∫ ω in A, f (n5_X P 𝒢 W σ X₀ b (τr ω) ω) ∂P = ∫ ω in A, f (X₀ ω) ∂P +
        ∫ ω in A, (∫ s in Icc 0 (τr ω), (deriv f (n5_X P 𝒢 W σ X₀ b s ω) * b s ω +
          σ ^ 2 / 2 * deriv (deriv f) (n5_X P 𝒢 W σ X₀ b s ω))) ∂P := by
  set X := n5_X P 𝒢 W σ X₀ b with hXdef
  have hK : IsCompact (Icc lo hi) := isCompact_Icc
  have hf' : IsC12On dur (Set.univ : Set ℝ) (fun _ x => f x) := isC12On_of_contDiff dur univ f hf
  have hLoc := n5_locL1 (P := P) hb hbM
  have hΦ := n5_locL2E (P := P) σ 𝒢
  have hΦσ : ∀ j, IsProgressiveL2 P 𝒢 (stopIntegrand
      (fun s ω k => coordCLM j ((fun (_ : ℝ) (_ : Ω) (_ : Fin 1) => σ) s ω k)) τ) := fun j =>
    (IsProgressiveL2.const P 𝒢 (fun _ : Fin 1 => coordCLM j σ)).stopIntegrand hτ
  have hψσ : IsProgressiveL2 P 𝒢 (stopIntegrand
      (fun s ω k => ‖(fun (_ : ℝ) (_ : Ω) (_ : Fin 1) => σ) s ω k‖) τ) :=
    (IsProgressiveL2.const P 𝒢 (fun _ : Fin 1 => ‖σ‖)).stopIntegrand hτ
  have hmain := ito_stopped hW hdur isOpen_univ hK (subset_univ _) hf' hX₀ hLoc hΦ hτ hΦσ hXK
  have hXprog : IsProgressive 𝒢 X := isProgressive_itoProcess X₀ hX₀ b hb _
  have L2 := isProgressiveL2_stop_itoIntegrand hf' hK (subset_univ _) hXprog hΦ.prog hτ hψσ
  set N := itoIntegral P 𝒢 W (stopIntegrand (itoIntegrand dur (Icc lo hi) (fun _ x => f x) X
    (fun _ _ (_ : Fin 1) => σ)) τ) with hNdef
  have hNm : Martingale N 𝒢 P := martingale_itoIntegral hW L2
  have hNstop := itoIntegral_stopIntegrand hW L2 hτ
  rw [stopIntegrand_stopIntegrand_of_le _ (fun _ => le_rfl)] at hNstop
  have hNeq : ∀ᵐ ω ∂P, N dur ω = N (τr ω) ω := by
    filter_upwards [hNstop] with ω hω
    have h1 : N dur ω = N (min dur (τr ω)) ω := (hω dur).trans (stoppedProcess_apply_coe (hτr ω) dur)
    rw [h1, min_eq_right (hτd ω)]
  set D : ℝ → Ω → ℝ := fun s ω => deriv f (X s ω) * b s ω +
    σ ^ 2 / 2 * deriv (deriv f) (X s ω) with hDdef
  have hmain' : ∀ᵐ ω ∂P, IntegrableOn (fun s => D s ω) (Icc 0 (τr ω)) ∧
      f (X (τr ω) ω) = f (X₀ ω) + (∫ s in Icc 0 (τr ω), D s ω) + N dur ω := by
    filter_upwards [hmain, hNeq] with ω h1 h2
    obtain ⟨hi, he⟩ := h1 (τr ω) ⟨hτ0 ω, hτd ω⟩ (le_of_eq (hτr ω).symm)
    simp only [n5_itoDrift hf] at hi he
    refine ⟨hi, ?_⟩
    rw [he, h2]
  have hX₀m : Measurable X₀ := (hX₀ 0).mono (𝒢.le 0) le_rfl
  obtain ⟨Bf, hBf⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hFm : Measurable (fun ω => f (X (τr ω) ω)) := by
    have h1 := hXprog.isStronglyProgressive
    have h2 := stronglyMeasurable_stoppedValue_of_le h1 hτ (n := dur)
      (fun ω => by rw [hτr ω]; exact_mod_cast hτd ω)
    have h3 : Measurable (stoppedValue X τ) := (h2.mono (𝒢.le dur)).measurable
    have h4 : (fun ω => f (X (τr ω) ω)) = f ∘ stoppedValue X τ := by
      funext ω; simp [stoppedValue, hτr ω]
    rw [h4]
    exact hf.continuous.measurable.comp h3
  have hFi : Integrable (fun ω => f (X (τr ω) ω)) P := by
    refine Integrable.of_bound hFm.aestronglyMeasurable Bf ?_
    filter_upwards [hXK] with ω h
    exact hBf _ (h (τr ω) ⟨hτ0 ω, hτd ω⟩ (le_of_eq (hτr ω).symm))
  have hX₀i : Integrable (fun ω => f (X₀ ω)) P := by
    refine Integrable.of_bound (hf.continuous.measurable.comp hX₀m).aestronglyMeasurable Bf ?_
    filter_upwards [hXK] with ω h
    have := h 0 ⟨le_rfl, hdur⟩ (by rw [hτr ω]; exact_mod_cast hτ0 ω)
    have e : X 0 ω = X₀ ω := itoProcess_zero P 𝒢 W X₀ b _ ω
    rw [e] at this
    exact hBf _ this
  have hNi : Integrable (N dur) P := hNm.integrable dur
  have hDeq : (fun ω => ∫ s in Icc 0 (τr ω), D s ω) =ᵐ[P]
      fun ω => f (X (τr ω) ω) - f (X₀ ω) - N dur ω := by
    filter_upwards [hmain'] with ω h
    rw [h.2]; ring
  have hDi : Integrable (fun ω => ∫ s in Icc 0 (τr ω), D s ω) P :=
    ((hFi.sub hX₀i).sub hNi).congr hDeq.symm
  refine ⟨hmain'.mono fun ω h => h.1, hFi, hX₀i, hDi, fun A hA => ?_⟩
  have hAm : MeasurableSet A := 𝒢.le 0 _ hA
  have hN0 : ∫ ω in A, N dur ω ∂P = 0 := by
    have := hNm.setIntegral_eq hdur hA
    rw [← this]
    simp [hNdef, itoIntegral_of_nonpos P 𝒢 W _ (le_refl (0 : ℝ))]
  have hFeq : (fun ω => f (X (τr ω) ω)) =ᵐ[P] fun ω => f (X₀ ω) + (∫ s in Icc 0 (τr ω), D s ω) + N dur ω := by
    filter_upwards [hmain'] with ω h using h.2
  have hsum : Integrable (fun ω => f (X₀ ω) + ∫ s in Icc 0 (τr ω), D s ω) P := hX₀i.add hDi
  calc ∫ ω in A, f (X (τr ω) ω) ∂P
      = ∫ ω in A, (f (X₀ ω) + (∫ s in Icc 0 (τr ω), D s ω) + N dur ω) ∂P :=
        setIntegral_congr_ae hAm (hFeq.mono fun ω h _ => h)
    _ = ∫ ω in A, (f (X₀ ω) + ∫ s in Icc 0 (τr ω), D s ω) ∂P + ∫ ω in A, N dur ω ∂P :=
        integral_add hsum.integrableOn hNi.integrableOn
    _ = ∫ ω in A, f (X₀ ω) ∂P + ∫ ω in A, (∫ s in Icc 0 (τr ω), D s ω) ∂P := by
        rw [integral_add hX₀i.integrableOn hDi.integrableOn, hN0, add_zero]

end HRS.MC.CepN5

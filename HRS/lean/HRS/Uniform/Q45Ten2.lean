import HRS.Uniform.Q45Ten1

/-!
# Q45 (Lemma 3.20): the Gaussian path tensor of a nonnegative trace density
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

lemma obsForm_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℝ}
    (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ) (y y' : PathSp T E) :
    obsForm t₁ t₂ ℓ₁ ℓ₂ y y' = ℓ₁ (pcm y t₁) * ℓ₂ (pcm y' t₂) := by
  simp [obsForm, PathSp.eval, pcm]
  rfl

/-- For a nonnegative trace density `Db`, the second moment tensor of the Gaussian stochastic convolution. -/
theorem gauss_tensor (T K : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K) (Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (_ : IsDetCovDensity T Db),
        ∃ τ : ProjTensor2 (PathSp T E),
          ‖τ‖ ≤ C * ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Db r) ∧
          (∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ, tensorPairing Ψ τ = tensorPairing Ψ.flip τ) ∧
          (∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
            tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) τ =
              ∫ r in Set.Icc 0 (min (t₁ : ℝ) t₂), Db r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) := by
  obtain ⟨C, hC0, hC⟩ := maximal_estimate_meas T K hT.le
  refine ⟨C, hC0, ?_⟩
  intro H E _ _ _ _ _ _ _ _ _ _ _ _ S hS Db hDb
  obtain ⟨Ω, mΩ, P, hP, ℱ, G, hGc, hG0, hG⟩ := exists_gaussian_martingale T hT.le Db hDb
  haveI := hP
  obtain ⟨Z, hZ, hZc, hZm, hZb⟩ := hC Ω P ℱ H E S hS G (fun r _ => if r ≤ T then Db r else 0) hG
  set W : Ω → PathSp T E := windowPath 0 T Z with hW
  have hWm : AEMeasurable W P := aemeasurable_windowPath' P hT Z hZm hZc
  have hWs : AEStronglyMeasurable W P := hWm.aestronglyMeasurable
  have hTs : AEStronglyMeasurable (fun ω => tmul (W ω) (W ω)) P := by
    have h2 : AEStronglyMeasurable (fun ω => (W ω, W ω)) P := hWs.prodMk hWs
    have h3 := (continuous_tmul (Y := PathSp T E)).comp_aestronglyMeasurable h2
    exact h3
  -- the trace integral
  set Itr : ℝ≥0∞ := ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Db r)) with hItr
  have hItr_lt : Itr < ⊤ := hDb.int.lintegral_lt_top
  have hItr_eq : Itr = ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Db r)) :=
    (ofReal_integral_eq_lintegral_ofReal hDb.int
      (Eventually.of_forall fun r => traceNormForm_nonneg _)).symm
  have hzb : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal C * Itr := by
    refine hZb.trans (le_of_eq ?_)
    congr 1
    have : ∀ ω : Ω, (∫⁻ r in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (traceNormForm ((fun r (_ : Ω) => if r ≤ T then Db r else 0) r ω))) = Itr := by
      intro ω
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp [hr.2]
    calc _ = ∫⁻ _ω, Itr ∂P := lintegral_congr this
      _ = Itr := by simp
  -- pointwise bound of the tensor norm
  have hnorm : ∀ᵐ ω ∂P, ‖tmul (W ω) (W ω)‖ₑ ≤ (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ 2 := by
    filter_upwards [hZc] with ω hω
    have h1 : ‖tmul (W ω) (W ω)‖ₑ ≤ ‖W ω‖ₑ * ‖W ω‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_tmul_le _ _)
    have h2 := enorm_windowPath_le (T := T) Z hω
    calc ‖tmul (W ω) (W ω)‖ₑ ≤ ‖W ω‖ₑ * ‖W ω‖ₑ := h1
      _ ≤ (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) * (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) := mul_le_mul' h2 h2
      _ = _ := (sq _).symm
  have hlint : ∫⁻ ω, ‖tmul (W ω) (W ω)‖ₑ ∂P ≤ ENNReal.ofReal C * Itr :=
    (lintegral_mono_ae hnorm).trans hzb
  have hfin : ENNReal.ofReal C * Itr < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hItr_lt
  have hint : Integrable (fun ω => tmul (W ω) (W ω)) P := ⟨hTs, lt_of_le_of_lt hlint hfin⟩
  refine ⟨∫ ω, tmul (W ω) (W ω) ∂P, ?_, ?_, ?_⟩
  · -- norm bound
    refine (norm_integral_le_lintegral_norm _).trans ?_
    simp only [ofReal_norm]
    have h1 := ENNReal.toReal_mono hfin.ne hlint
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0, hItr_eq,
      ENNReal.toReal_ofReal (integral_nonneg fun r => traceNormForm_nonneg _)]
  · intro Ψ
    rw [tensorPairing_eq, tensorPairing_eq, ← ContinuousLinearMap.integral_comp_comm _ hint,
      ← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [tensorPairingL_tmul]
    rfl
  · intro t₁ t₂ ℓ₁ ℓ₂
    rw [tensorPairing_eq, ← ContinuousLinearMap.integral_comp_comm _ hint]
    have e : ∀ᵐ ω ∂P, tensorPairingL (obsForm t₁ t₂ ℓ₁ ℓ₂) (tmul (W ω) (W ω)) =
        ℓ₁ (Z (t₁ : ℝ) ω) * ℓ₂ (Z (t₂ : ℝ) ω) := by
      filter_upwards [hZc] with ω hω
      rw [tensorPairingL_tmul, obsForm_apply, hW, pcm_windowPath Z hω, pcm_windowPath Z hω]
    rw [integral_congr_ae e]
    exact cov_formula hT.le hS hDb hG hZ hZm t₁.2 t₂.2 ℓ₁ ℓ₂

end HRS.Uniform.Q45

import HRS.MC.E214B2

/-!
# Packet e214b (part 3): `e214_tensor_diff_cube`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214B

open HRS HRS.Main

variable {d : ℕ}

/-- Letting `N → ∞` in `diff_bound`. -/
theorem cube_small (S : PreparedData d) (β₀ m T : ℝ)
    {K K' : ℝ → projTensor (PathSpace d m T) 3} {ε ε' : ℕ → ℝ}
    (h : IsWindowEdgeworth S β₀ m T K ε) (h' : IsWindowEdgeworth S β₀ m T K' ε')
    (hP : ∀ (a : ℝ) (ha : 0 ≤ a) (N : ℕ), 2 ≤ N → ∃ (Ω : Type) (_ : MeasurableSpace Ω)
      (P : Measure Ω) (_ : IsProbabilityMeasure P) (X₀ : Ω → Config d N)
      (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      SelectedFlow P S.dyn (a + T) X₀ W X ∧
      (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) ∧
      law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (a : ℝ) (ha : 0 ≤ a) (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z)
    (L : StrongDual ℝ (PathSpace d m T)) (hL : ‖L‖ ≤ 1) :
    (((K a - K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3))
        (trilin ![L, L, L]) *
      ∫ ω, -((1 / 6) * Real.cos (L (windowPath m T a Z ω))) ∂P' = 0 := by
  set c0 : ℝ := |(1 / 6) * ((((K a - K' a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3)) (trilin ![L, L, L])) *
      ∫ ω, -((1 / 6) * Real.cos (L (windowPath m T a Z ω))) ∂P'| with hc0
  have hle : ∀ N : ℕ, 2 ≤ N → c0 ≤ ε N + ε' N := by
    intro N hN
    obtain ⟨Ω, _, P, _, X₀, W, X, hflow, hfilt, hlaw⟩ := hP a ha N hN
    exact diff_bound S β₀ m T h h' a ha N hN P X₀ W X hflow hfilt hlaw ν hν P' Z₀ Z hZ L hL
  have ht : Tendsto (fun N => ε N + ε' N) atTop (𝓝 0) := by
    simpa using h.eps_tendsto.add h'.eps_tendsto
  have h0 : c0 ≤ 0 :=
    ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨2, hle⟩)
  have h1 : c0 = 0 := le_antisymm h0 (abs_nonneg _)
  rw [hc0, abs_eq_zero] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · rw [h3, zero_mul]
  · rw [h2, mul_zero]

theorem trilin_smul {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (t : ℝ)
    (L : StrongDual ℝ B) : trilin ![t • L, t • L, t • L] = (t ^ 3) • trilin ![L, L, L] := by
  ext x
  simp [trilin_apply]
  ring

/-- **Lemma L1** (`docs/MC_E214_UNIQUENESS_SCOPE.md` §1): the difference of two window Edgeworth
tensors vanishes on cubes `L ⊗ L ⊗ L`. -/
theorem e214_tensor_diff_cube (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) {K K' : ℝ → projTensor (PathSpace d m T) 3} {ε ε' : ℕ → ℝ}
    (h : IsWindowEdgeworth S β₀ m T K ε) (h' : IsWindowEdgeworth S β₀ m T K' ε')
    (hP : ∀ (a : ℝ) (ha : 0 ≤ a) (N : ℕ), 2 ≤ N → ∃ (Ω : Type) (_ : MeasurableSpace Ω)
      (P : Measure Ω) (_ : IsProbabilityMeasure P) (X₀ : Ω → Config d N)
      (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      SelectedFlow P S.dyn (a + T) X₀ W X ∧
      (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) ∧
      law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (hG : ∀ (a : ℝ) (ha : 0 ≤ a), ∃ (ν : Measure (NegSobolev d m)),
      IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z)
    (a : ℝ) (ha : 0 ≤ a) (L : StrongDual ℝ (PathSpace d m T)) :
    (((K a - K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3))
        (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ |>.compContinuousLinearMap ![L, L, L]) = 0 := by
  obtain ⟨ν, hν, Ω', _, P', _, Z₀, Z, hZ⟩ := hG a ha
  change (((K a - K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3))
    (trilin ![L, L, L]) = 0
  set Dv := (((K a - K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3))
    with hDv
  have hae : AEMeasurable (fun ω => L (windowPath m T a Z ω)) P' :=
    L.continuous.measurable.comp_aemeasurable (windowPath_aemeasurable S m T a ha ν P' Z₀ Z hZ)
  have hlim := tendsto_integral_cos P' _ hae
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1
    (hlim.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  set t : ℝ := min (δ / 2) (1 / (‖L‖ + 1)) with ht
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    linarith [min_le_left (δ / 2) (1 / (‖L‖ + 1))]
  have hnorm : ‖t • L‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have h1 : t ≤ 1 / (‖L‖ + 1) := min_le_right _ _
    calc t * ‖L‖ ≤ 1 / (‖L‖ + 1) * ‖L‖ := by gcongr
      _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith
  have hcube := cube_small S β₀ m T h h' hP a ha ν hν P' Z₀ Z hZ (t • L) hnorm
  have hpos : (0 : ℝ) < ∫ ω, Real.cos (t * L (windowPath m T a Z ω)) ∂P' := hδ' htδ
  have hJ : ∫ ω, -((1 / 6) * Real.cos ((t • L) (windowPath m T a Z ω))) ∂P' =
      -((1 / 6) * ∫ ω, Real.cos (t * L (windowPath m T a Z ω)) ∂P') := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [integral_neg, integral_const_mul]
  rw [hJ, trilin_smul, map_smul, smul_eq_mul] at hcube
  have hne : -((1 / 6) * ∫ ω, Real.cos (t * L (windowPath m T a Z ω)) ∂P') ≠ 0 := by
    have : 0 < (1 / 6 : ℝ) * ∫ ω, Real.cos (t * L (windowPath m T a Z ω)) ∂P' := by positivity
    linarith
  have h3 : t ^ 3 * Dv (trilin ![L, L, L]) = 0 := by
    rcases mul_eq_zero.1 hcube with h | h
    · exact h
    · exact absurd h hne
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h (by positivity)
  · exact h

end HRS.MC.E214B

import HRS.MC.E214B1

/-!
# Packet e214b (part 2): `D (L ⊗ L ⊗ L) = 0` for the difference of two window Edgeworth tensors
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214B

open HRS HRS.Main

variable {d : ℕ}

/-- Two expansions at the same system: the difference of the tensors, tested against `L'^{⊗3}`, is
controlled by `ε N + ε' N`. -/
theorem diff_bound (S : PreparedData d) (β₀ m T : ℝ)
    {K K' : ℝ → projTensor (PathSpace d m T) 3} {ε ε' : ℕ → ℝ}
    (h : IsWindowEdgeworth S β₀ m T K ε) (h' : IsWindowEdgeworth S β₀ m T K' ε')
    (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hflow : SelectedFlow P S.dyn (a + T) X₀ W X)
    (hfilt : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hlaw : law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z)
    (L : StrongDual ℝ (PathSpace d m T)) (hL : ‖L‖ ≤ 1) :
    |(1 / 6) * ((((K a - K' a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3)) (trilin ![L, L, L])) *
      ∫ ω, -((1 / 6) * Real.cos (L (windowPath m T a Z ω))) ∂P'| ≤ ε N + ε' N := by
  have hΦ : (fun z => (1 / ((5 : ℕ) + 1 : ℝ)) * Real.sin (L z)) ∈
      CbUnitBall (PathSpace d m T) 5 := sin_dual_mem L hL 5
  have hc : (1 / (((5 : ℕ) : ℝ) + 1)) = 1 / 6 := by norm_num
  rw [hc] at hΦ
  have e1 := h.expansion a ha N hN P X₀ W X hflow hfilt hlaw ν hν P' Z₀ Z hZ _ hΦ
  have e2 := h'.expansion a ha N hN P X₀ W X hflow hfilt hlaw ν hν P' Z₀ Z hZ _ hΦ
  rw [integral_tensor_iteratedFDeriv_sin] at e1 e2
  set A := Real.sqrt N * (∫ z, (fun z => (1 / 6 : ℝ) * Real.sin (L z)) z ∂(law P (windowZeta m T a P X)) -
          ∫ z, (fun z => (1 / 6 : ℝ) * Real.sin (L z)) z ∂(law P' (windowPath m T a Z))) with hA
  set J := ∫ ω, -((1 / 6) * Real.cos (L (windowPath m T a Z ω))) ∂P' with hJ
  have hsub : (((K a - K' a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3)) (trilin ![L, L, L]) =
      ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) -
      ((K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) := by
    simp
  rw [hsub]
  have key : (1 / 6) * (((K a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) -
      ((K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (trilin ![L, L, L])) * J
      = ((A - (1 / 6) * (((K' a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) * J)) -
        (A - (1 / 6) * (((K a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) * J))) := by ring
  rw [key]
  calc _ ≤ |A - (1 / 6) * (((K' a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) * J)| +
        |A - (1 / 6) * (((K a : projTensor (PathSpace d m T) 3) :
        TensorDual (PathSpace d m T) 3) (trilin ![L, L, L]) * J)| := abs_sub _ _
    _ ≤ ε' N + ε N := add_le_add e2 e1
    _ = ε N + ε' N := add_comm _ _

end HRS.MC.E214B

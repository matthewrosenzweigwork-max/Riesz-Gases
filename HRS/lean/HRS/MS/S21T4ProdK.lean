import HRS.MS.S21T4ProdJ

/-! S13: uniform-in-N stochastic approximation of arbitrary L² pair kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

/-- The L²-distance of two symmetric kernels uniformly controls the actual
particle-pair-energy approximation probability. This is a quantitative
converging-together input for R26-T3.S13 and holds for arbitrary Borel
probability measures, including atomic measures. -/
theorem s21t4_s13_approx_tail {N : ℕ} (hN : 2 ≤ N)
    (h h' : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hm' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) (hs' : ∀ x y, h' x y = h' y x)
    (ε : ℝ) :
    ε ^ 2 * (Measure.pi fun _ : Fin N => μ).real
      {X : EucConfig d N | ε ^ 2 ≤
        ((N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
          (1 / 2) * ∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ) ^ 2} ≤
      18 * ∫ z : Euc d × Euc d, (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  let Δ : Euc d → Euc d → ℝ := fun x y => h x y - h' x y
  have hΔ : MemLp (fun z : Euc d × Euc d => Δ z.1 z.2) 2 (μ.prod μ) := hm.sub hm'
  have hΔs : ∀ x y, Δ x y = Δ y x := fun x y => by simp only [Δ, hs x y, hs' x y]
  have htail := s21t4_s13_tail μ hN Δ hΔ hΔs ε
  have he : (fun X : EucConfig d N => pairEnergy Δ X μ)
      =ᵐ[ν] (fun X => pairEnergy h X μ - pairEnergy h' X μ) :=
    s21t4_pairEnergy_sub_ae μ h h' hm hm'
  have hsets : ν
      {X : EucConfig d N | ε ^ 2 ≤
        ((N : ℝ) * pairEnergy Δ X μ +
          (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) ^ 2} =
      ν {X : EucConfig d N | ε ^ 2 ≤
        ((N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
          (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) ^ 2} := by
    apply measure_congr
    filter_upwards [he] with X hx
    rw [hx]
  change ε ^ 2 * (ν.real {X : EucConfig d N | ε ^ 2 ≤
      ((N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
      (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) ^ 2}) ≤ _
  have hsetsR := congrArg ENNReal.toReal hsets
  change (ν.real {X : EucConfig d N | ε ^ 2 ≤
      ((N : ℝ) * pairEnergy Δ X μ +
      (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) ^ 2}) =
    (ν.real {X : EucConfig d N | ε ^ 2 ≤
      ((N : ℝ) * (pairEnergy h X μ - pairEnergy h' X μ) +
      (1 / 2) * ∫ x, ∫ y, Δ x y ∂μ ∂μ) ^ 2}) at hsetsR
  rw [← hsetsR]
  exact htail

end HRS.MS.R26T3

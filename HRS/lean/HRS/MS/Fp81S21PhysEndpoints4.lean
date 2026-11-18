import HRS.MS.Fp81S21MovingHeat3
import HRS.MS.Fp81S21PhysEndpoints3

/-! Preparation-law transfer for the initial heat observable. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The actual preparation law transfers the initial heat observable from the
particle's initial configuration to the exact static preparation integral. -/
theorem fp81s21_physical_initial_heat_integral (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
      (∀ H v, IsProbabilityMeasure (future H v)) →
      ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ Φ : Window p → ℝ, MemCb 5 Φ →
        (∫ ω, initialHeat future a ha Φ 0 (initialWindow R N a (A.X₀ ω)) ∂A.P) =
          ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X) ∂(r26t3_Q R N) := by
  obtain ⟨δ0, hδ0, hδhalf, htransfer⟩ := fp81s21_physical_initial_window_integral p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R future hfuture a ha N hN A Φ hΦ
  apply htransfer δ hδ hδle R a ha N hN A
  exact (fp81s21_windowFuture_heat_derivs future hfuture a ha Φ hΦ 0).1.continuous

#print axioms HRS.Fp81.S21.fp81s21_physical_initial_heat_integral
end HRS.Fp81.S21
end

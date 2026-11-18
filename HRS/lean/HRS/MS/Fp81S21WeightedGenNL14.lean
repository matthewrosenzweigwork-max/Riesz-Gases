import HRS.MS.Fp81S21WeightedGenNL13

/-! Pointwise convergence of finite weighted jet vectors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.ProClosureS111

/-- Pointwise convergence of all derivatives through order `r` entails convergence
of the weighted finite jet vector. -/
theorem fp81s21_weightedJets_tendsto_of_iterated {d r : ℕ} {P : ℝ}
    {g : ℕ → Euc d → ℝ} {f : Euc d → ℝ}
    (ht : ∀ m ≤ r, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ m (g n) x)
      atTop (𝓝 (iteratedFDeriv ℝ m f x))) :
    ∀ x, Tendsto (fun n => weightedJets r P (g n) x) atTop
      (𝓝 (weightedJets r P f x)) := by
  intro x
  have hpi : Tendsto (fun n (a : WeightedJetIndex d r) =>
      jbracket x ^ (-P) * partialDeriv a.2 (g n) x) atTop
      (𝓝 (fun a : WeightedJetIndex d r => jbracket x ^ (-P) * partialDeriv a.2 f x)) := by
    apply tendsto_pi_nhds.2
    intro a
    have hm : (a.1 : ℕ) ≤ r := by have := a.1.isLt; omega
    have h := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin (a.1 : ℕ) => Euc d) ℝ
      (fun i => EuclideanSpace.single (a.2 i) 1)).continuous.tendsto _).comp (ht a.1 hm x)
    simpa [partialDeriv] using tendsto_const_nhds.mul h
  exact ((PiLp.continuous_toLp 2 (fun _ : WeightedJetIndex d r => ℝ)).tendsto _).comp hpi

#print axioms HRS.Fp81.S21.fp81s21_weightedJets_tendsto_of_iterated
end HRS.Fp81.S21

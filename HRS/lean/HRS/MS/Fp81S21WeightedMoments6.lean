import HRS.MS.Fp81S21WeightedMoments5

/-! Finite-section measurability for the weighted-chart coefficient space. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Exact representation contract for a functional on the compact smooth
chart tests: action on every test, forced chart coordinates, and the exact
dual norm. -/
def fp81s21_TestRep {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw)
    (T : (Euc d → ℝ) → ℝ) (z : r26t6_Coeff) : Prop :=
  (∀ f, IsR2Test f → fp81s21_chartAction E z f = T f) ∧
  (∀ j, z j = T (E.test j)) ∧
  dualNormE r Pw T = ENNReal.ofReal ‖z‖

/-- Measurability of all coordinates gives measurability into the chart's
separable `ℓ²` coefficient space, by measurable finite sections. -/
theorem fp81s21_coeff_measurable
    {S : Type*} [MeasurableSpace S]
    (q : S → r26t6_Coeff)
    (hc : ∀ j, Measurable (fun a => q a j)) :
    Measurable q := by
  let finiteSection : ℕ → S → r26t6_Coeff := fun n a =>
    ∑ j ∈ Finset.range n, lp.single 2 j (q a j)
  have hcoords : Measurable (fun a => fun j : ℕ => q a j) :=
    measurable_pi_lambda hc
  have hsection : ∀ n, Measurable (finiteSection n) := by
    intro n
    let finiteLift : (ℕ → ℝ) → r26t6_Coeff := fun c =>
      ∑ j ∈ Finset.range n, lp.single 2 j (c j)
    have hlift : Continuous finiteLift := by
      dsimp [finiteLift]
      exact continuous_finset_sum _ fun j _ =>
        (lp.singleContinuousLinearMap (𝕜 := ℝ)
          (E := fun _ : ℕ => ℝ) 2 j).continuous.comp (continuous_apply j)
    have heq : finiteSection n = finiteLift ∘ fun a j => q a j := by
      funext a
      rfl
    rw [heq]
    exact hlift.measurable.comp hcoords
  have hlim : Tendsto finiteSection atTop (𝓝 q) := by
    rw [tendsto_pi_nhds]
    intro a
    exact coeffSection_tendsto (q a)
  exact measurable_of_tendsto_metrizable hsection hlim

#print axioms HRS.Fp81.S21.fp81s21_TestRep
#print axioms HRS.Fp81.S21.fp81s21_coeff_measurable

end HRS.Fp81.S21

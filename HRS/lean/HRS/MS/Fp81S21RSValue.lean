import HRS.MS.Fp81S21IntervalRSBV
import HRS.MS.Fp81S21IntervalRSRestrict

/-! Measurable selection of scalar interval Riemann--Stieltjes values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- A fixed sequence of fine tagged partitions tests every RS value on the interval. -/
theorem fp81s21_rs_fine_sums {Ω : Type*} {q r : ℝ} (hqr : q < r)
    (S : Ω → ℝ → ℝ → ℝ → ℝ) :
    ∃ (N : ℕ → ℕ) (U : ∀ k, Fin (N k + 1) → ℝ) (Tg : ∀ k, Fin (N k) → ℝ),
      ∀ ω I, fp81s21_IsRSOn q r (S ω) I →
        Tendsto (fun k => ∑ i : Fin (N k),
          S ω (q + Tg k i) (q + U k i.castSucc) (q + U k i.succ)) atTop (𝓝 I) := by
  have hex : ∀ k : ℕ, ∃ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ), StrictMono u ∧
      u 0 = 0 ∧ u (Fin.last n) = r - q ∧
      (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) ∧
      (∀ i : Fin n, u i.succ - u i.castSucc < 1 / ((k : ℝ) + 1)) := by
    intro k
    exact HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition (sub_pos.mpr hqr) (by positivity)
  choose N U Tg hU hU0 hUT hTg hMesh using hex
  refine ⟨N, U, Tg, ?_⟩
  intro ω I hI
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := hI ε hε
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ
  refine ⟨M, ?_⟩
  intro k hk
  have hsmall : ∀ i : Fin (N k), U k i.succ - U k i.castSucc < δ := by
    intro i
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    exact lt_of_lt_of_le (hMesh k i) (le_trans h1 hM.le)
  simpa [Real.dist_eq] using hsum (N k) (U k) (Tg k) (hU k) (hU0 k) (hUT k) (hTg k) hsmall

/-- Every specified RS value is measurable when its deterministic summands are measurable. -/
theorem fp81s21_rs_value_measurable {Ω : Type*} [MeasurableSpace Ω]
    {q r : ℝ} (hqr : q < r) (S : Ω → ℝ → ℝ → ℝ → ℝ) (I : Ω → ℝ)
    (hS : ∀ τ u v, Measurable (fun ω => S ω τ u v))
    (hI : ∀ ω, fp81s21_IsRSOn q r (S ω) (I ω)) : Measurable I := by
  obtain ⟨N, U, Tg, hlim⟩ := fp81s21_rs_fine_sums hqr S
  apply measurable_of_tendsto_metrizable (f := fun k ω => ∑ i : Fin (N k),
    S ω (q + Tg k i) (q + U k i.castSucc) (q + U k i.succ))
  · intro k
    exact Finset.measurable_sum _ (fun i _ => hS _ _ _)
  · exact tendsto_pi_nhds.mpr (fun ω => hlim ω (I ω) (hI ω))

/-- The same conclusion holds almost everywhere, without requiring the exceptional set measurable. -/
theorem fp81s21_rs_value_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {q r : ℝ} (hqr : q < r) (S : Ω → ℝ → ℝ → ℝ → ℝ) (I : Ω → ℝ)
    (hS : ∀ τ u v, Measurable (fun ω => S ω τ u v))
    (hI : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r (S ω) (I ω)) : AEMeasurable I μ := by
  obtain ⟨N, U, Tg, hlim⟩ := fp81s21_rs_fine_sums hqr S
  apply aemeasurable_of_tendsto_metrizable_ae atTop (f := fun k ω => ∑ i : Fin (N k),
    S ω (q + Tg k i) (q + U k i.castSucc) (q + U k i.succ))
  · intro k
    exact (Finset.measurable_sum _ (fun i _ => hS _ _ _)).aemeasurable
  · filter_upwards [hI] with ω hω
    exact hlim ω (I ω) hω

#print axioms fp81s21_rs_fine_sums
#print axioms fp81s21_rs_value_measurable
#print axioms fp81s21_rs_value_aemeasurable
end HRS.Fp81.S21
end

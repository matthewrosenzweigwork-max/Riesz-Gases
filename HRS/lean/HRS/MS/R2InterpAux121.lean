import HRS.MS.R2InterpAux120
import HRS.MS.R2InterpAux105
import HRS.MS.R2InterpAux110
import HRS.MS.R2InterpAux83

/-!
# S10.2 (worker S10S), part 121 (packet M1b): the envelope `Env` of the pair energy

`Env g X μ = (2N²)⁻¹∑_{i≠j} g(x_i,x_j) + N⁻¹∑_i ∫ g(x_i,y)dμ + ½∬ g` dominates `|pairEnergy h X μ|/B` whenever `|h| ≤ B g`; it is
`pairEnergy g X μ + 2N⁻¹∑_i ∫ g(x_i,y)dμ`, hence `L¹` under the time marginals with a uniform bound (S9.5 `s95_conj1` and the marginal moment).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

/-- The envelope of the pair energy. -/
def s102_Env (g : Euc d → Euc d → ℝ) {N : ℕ} (X : EucConfig d N) (μ : Measure (Euc d)) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i) (X j)
    + (1 / (N : ℝ)) * ∑ i, ∫ y, g (X i) y ∂μ + (1 / 2) * ∫ x, ∫ y, g x y ∂μ ∂μ

theorem s102_Env_eq (g : Euc d → Euc d → ℝ) {N : ℕ} (X : EucConfig d N) (μ : Measure (Euc d)) :
    s102_Env g X μ = pairEnergy g X μ + (2 / (N : ℝ)) * ∑ i, ∫ y, g (X i) y ∂μ := by
  unfold s102_Env pairEnergy
  ring

theorem s102_Env_nonneg {g : Euc d → Euc d → ℝ} (hg0 : ∀ x y, 0 ≤ g x y) {N : ℕ} (X : EucConfig d N)
    (μ : Measure (Euc d)) : 0 ≤ s102_Env g X μ := by
  unfold s102_Env
  have h1 : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i) (X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hg0 _ _
  have h2 : 0 ≤ ∑ i, ∫ y, g (X i) y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => hg0 _ _
  have h3 : 0 ≤ ∫ x, ∫ y, g x y ∂μ ∂μ := integral_nonneg fun x => integral_nonneg fun y => hg0 _ _
  positivity

theorem s102_pE_abs_le_Env {μ : Measure (Euc d)} {g h : Euc d → Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg0 : ∀ x y, 0 ≤ g x y) (hgi : ∀ x, Integrable (g x) μ) (hgH : Integrable (fun x => ∫ y, g x y ∂μ) μ)
    (hh : ∀ x y, |h x y| ≤ B * g x y) {N : ℕ} (X : EucConfig d N) :
    |pairEnergy h X μ| ≤ B * s102_Env g X μ := by
  have hrow : ∀ x, |∫ y, h x y ∂μ| ≤ B * ∫ y, g x y ∂μ := fun x => by
    have := norm_integral_le_of_norm_le ((hgi x).const_mul B)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hh x y)
    rw [integral_const_mul] at this
    simpa [Real.norm_eq_abs] using this
  have hdbl : |∫ x, ∫ y, h x y ∂μ ∂μ| ≤ B * ∫ x, ∫ y, g x y ∂μ ∂μ := by
    have := norm_integral_le_of_norm_le (hgH.const_mul B)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hrow x)
    rw [integral_const_mul] at this
    simpa [Real.norm_eq_abs] using this
  have hsum1 : |∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| ≤
      B * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i) (X j) := by
    calc |∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)|
        ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, h (X i) (X j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |h (X i) (X j)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, B * g (X i) (X j) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hh _ _
      _ = _ := by simp_rw [← Finset.mul_sum]
  have hsum2 : |∑ i, ∫ y, h (X i) y ∂μ| ≤ B * ∑ i, ∫ y, g (X i) y ∂μ := by
    calc |∑ i, ∫ y, h (X i) y ∂μ| ≤ ∑ i, |∫ y, h (X i) y ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, B * ∫ y, g (X i) y ∂μ := Finset.sum_le_sum fun i _ => hrow _
      _ = _ := by rw [← Finset.mul_sum]
  have hc1 : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  have hc2 : 0 ≤ 1 / (N : ℝ) := by positivity
  unfold pairEnergy s102_Env
  have e1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| ≤
      B * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i) (X j)) := by
    rw [abs_mul, abs_of_nonneg hc1]
    nlinarith [hsum1, hc1]
  have e2 : |(1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂μ| ≤ B * ((1 / (N : ℝ)) * ∑ i, ∫ y, g (X i) y ∂μ) := by
    rw [abs_mul, abs_of_nonneg hc2]
    nlinarith [hsum2, hc2]
  have e3 : |(1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ| ≤ B * ((1 / 2) * ∫ x, ∫ y, g x y ∂μ ∂μ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith [hdbl]
  calc _ ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| +
        |(1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂μ| + |(1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by nlinarith [e1, e2, e3]

theorem s102_Env_meas {μ : Measure (Euc d)} [SFinite μ] {g : Euc d → Euc d → ℝ}
    (hg : Measurable fun p : Euc d × Euc d => g p.1 p.2) {N : ℕ} :
    Measurable fun X : EucConfig d N => s102_Env g X μ := by
  have hrow : Measurable fun x : Euc d => ∫ y, g x y ∂μ :=
    (hg.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hp := HRS.MS.Wr.wr9_measurable_pairEnergy (N := N) (μ := μ) hg
  have : (fun X : EucConfig d N => s102_Env g X μ) =
      fun X => pairEnergy g X μ + (2 / (N : ℝ)) * ∑ i, ∫ y, g (X i) y ∂μ := by
    funext X; exact s102_Env_eq g X μ
  rw [this]
  exact hp.add (measurable_const.mul (Finset.measurable_sum _ fun i _ => hrow.comp (measurable_pi_apply i)))

end HRS.MS.R2Interp

end

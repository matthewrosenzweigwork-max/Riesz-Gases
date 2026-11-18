import HRS.Main.A8PAux28

/-!
# Packet A8P, part 29: moments of the initial-difference and remainder vectors; Sobolev monotonicity
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_sobolevNorm_mono {φ : Torus d → ℝ} {a b : ℝ} (hb : MemSobolev b φ) (hab : a ≤ b) :
    sobolevNorm a φ ≤ sobolevNorm b φ := by
  have ha : MemSobolev a φ := HRS.PDE.MFAdjoint.memSobolev_mono_idx hb hab
  rw [HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm ha, HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm hb]
  exact Q54c.hsNorm_mono_q hab (HRS.PDE.hsNormSq_coeffOf b φ hb).1

theorem a8p_lp2 (X : ℝ≥0∞) {y : ℝ} (hy : 0 ≤ y) (h : X ≤ ENNReal.ofReal (y ^ 2)) :
    X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal y := by
  refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy]

section Moments

variable {Ω' : Type*} {m : MeasurableSpace Ω'} {P : Measure Ω'} {q : ℕ}

theorem a8p_vec_L1 (v : Ω' → EuclideanSpace ℝ (Fin q)) (hv : ∀ a, Measurable fun ω => v ω a)
    {c : Fin q → ℝ} (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a, ∫⁻ ω, ENNReal.ofReal |v ω a| ∂P ≤ ENNReal.ofReal (c a)) :
    ∫⁻ ω, ENNReal.ofReal (‖v ω‖ ^ (1 : ℝ)) ∂P ≤ ENNReal.ofReal (∑ a, c a) := by
  simp only [Real.rpow_one]
  calc ∫⁻ ω, ENNReal.ofReal ‖v ω‖ ∂P
      ≤ ∫⁻ ω, ∑ a, ENNReal.ofReal |v ω a| ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (a8p_norm_le_sum_abs _)
    _ = ∑ a, ∫⁻ ω, ENNReal.ofReal |v ω a| ∂P :=
        lintegral_finset_sum _ fun a _ => ENNReal.measurable_ofReal.comp (hv a).abs
    _ ≤ ∑ a, ENNReal.ofReal (c a) := Finset.sum_le_sum fun a _ => h a
    _ = ENNReal.ofReal (∑ a, c a) := (ENNReal.ofReal_sum_of_nonneg fun a _ => hc a).symm

theorem a8p_vec_L2 (v : Ω' → EuclideanSpace ℝ (Fin q)) (hv : ∀ a, Measurable fun ω => v ω a)
    {c : Fin q → ℝ} (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a, ∫⁻ ω, ENNReal.ofReal ((v ω a) ^ 2) ∂P ≤ ENNReal.ofReal (c a ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (‖v ω‖ ^ (2 : ℝ)) ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (∑ a, c a) := by
  refine a8p_lp2 _ (Finset.sum_nonneg fun a _ => hc a) ?_
  calc ∫⁻ ω, ENNReal.ofReal (‖v ω‖ ^ (2 : ℝ)) ∂P
      = ∫⁻ ω, ∑ a, ENNReal.ofReal ((v ω a) ^ 2) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
        congr 1
        rw [Real.rpow_two, EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs, sq_abs]
    _ = ∑ a, ∫⁻ ω, ENNReal.ofReal ((v ω a) ^ 2) ∂P :=
        lintegral_finset_sum _ fun a _ => ENNReal.measurable_ofReal.comp ((hv a).pow_const 2)
    _ ≤ ∑ a, ENNReal.ofReal (c a ^ 2) := Finset.sum_le_sum fun a _ => h a
    _ = ENNReal.ofReal (∑ a, c a ^ 2) := (ENNReal.ofReal_sum_of_nonneg fun a _ => sq_nonneg _).symm
    _ ≤ ENNReal.ofReal ((∑ a, c a) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => hc a)

end Moments

end HRS.Main.A8P

import HRS.MS.QMulAux4

/-!
# MS-QMUL, part 5: the quantitative multiplier estimate for `QOk` functions

`qm_stepS`: for `θ ∈ C^m` real with `‖D^jθ‖ ≤ A` (`j ≤ m`) and `f ∈ QOk m`,
`θ f ∈ QOk m` and `∫⁻ ⟨ξ⟩^m |\\widehat{θ f}|² ≤ K A² ∫⁻ ⟨ξ⟩^m |f̂|²`, `K = K(d,m)`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_QOk_mul {m : ℕ} {θ : Euc d → ℝ} {A : ℝ} (hθ : ContDiff ℝ m θ)
    (hA : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j θ x‖ ≤ A) {f : Euc d → ℂ} (hf : QOk m f) :
    QOk m (fun x => (θ x : ℂ) * f x) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hg : ContDiff ℝ m (fun x => (θ x : ℂ) * f x) :=
    (Complex.ofRealCLM.contDiff.comp hθ).mul hf.1
  have hΦ1 : Integrable (qm_Phi m f) volume := by
    unfold qm_Phi
    exact integrable_finset_sum _ fun l hl =>
      (hf.2 l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))).1.norm
  have hΦ2 : MemLp (qm_Phi m f) 2 volume := by
    unfold qm_Phi
    exact memLp_finset_sum (s := Finset.range (m + 1))
      (f := fun l x => ‖iteratedFDeriv ℝ l f x‖) (p := 2) (μ := volume)
      (fun l hl => (hf.2 l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))).2.norm)
  refine ⟨hg, fun k hk => ⟨?_, ?_⟩⟩
  · have hc : Continuous (iteratedFDeriv ℝ k (fun x => (θ x : ℂ) * f x)) :=
      hg.continuous_iteratedFDeriv (by exact_mod_cast hk)
    exact (hΦ1.const_mul (2 ^ m * ((m : ℝ) + 1) * A)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => qm_leibniz hθ hA hf.1 hk x)
  · have hc : Continuous (iteratedFDeriv ℝ k (fun x => (θ x : ℂ) * f x)) :=
      hg.continuous_iteratedFDeriv (by exact_mod_cast hk)
    refine (hΦ2.const_mul (2 ^ m * ((m : ℝ) + 1) * A)).mono hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ 2 ^ m * ((m : ℝ) + 1) * A * qm_Phi m f x := by
      have := qm_Phi_nonneg m f x
      positivity
    rw [Real.norm_of_nonneg h0]
    exact qm_leibniz hθ hA hf.1 hk x

theorem qm_ofReal_sum_sum (m : ℕ) (f : Euc d → ℂ) (x : Euc d) :
    ENNReal.ofReal (∑ l ∈ Finset.range (m + 1), ∑ i : Fin l → Fin d, ‖qm_pd i f x‖ ^ 2) =
      ∑ l ∈ Finset.range (m + 1), ∑ i : Fin l → Fin d, ‖qm_pd i f x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem qm_pointwise {m : ℕ} {θ : Euc d → ℝ} {A : ℝ} (hθ : ContDiff ℝ m θ)
    (hA : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j θ x‖ ≤ A) {f : Euc d → ℂ} (hf : ContDiff ℝ m f)
    {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (x : Euc d) :
    ‖qm_pd i (fun y => (θ y : ℂ) * f y) x‖ₑ ^ 2 ≤
      ENNReal.ofReal ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) *
        ∑ l ∈ Finset.range (m + 1), ∑ i' : Fin l → Fin d, ‖qm_pd i' f x‖ₑ ^ 2 := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have h1 : ‖qm_pd i (fun y => (θ y : ℂ) * f y) x‖ ≤ 2 ^ m * ((m : ℝ) + 1) * A * qm_Phi m f x :=
    (qm_norm_pd_le i _ x).trans (qm_leibniz hθ hA hf hn x)
  have hS := qm_Phi_sq m f x
  have h2 : ‖qm_pd i (fun y => (θ y : ℂ) * f y) x‖ ^ 2 ≤
      (2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) *
        ∑ l ∈ Finset.range (m + 1), ∑ i' : Fin l → Fin d, ‖qm_pd i' f x‖ ^ 2 := by
    calc _ ≤ (2 ^ m * ((m : ℝ) + 1) * A * qm_Phi m f x) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2) * qm_Phi m f x ^ 2 := by ring
      _ ≤ ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2) * ((((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) *
            ∑ l ∈ Finset.range (m + 1), ∑ i' : Fin l → Fin d, ‖qm_pd i' f x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by ring
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← qm_ofReal_sum_sum,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h2

end HRS.MS.QMul

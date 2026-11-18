import HRS.Commutator.Torus.LEIBTAux4

/-!
# LEIB-T helpers, part 5: Schwartz seminorms of a product `θ ψ` (quantitative Leibniz bound)
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_seminorm_mul (θ : 𝔼 → ℂ) (hθ : θ.HasTemperateGrowth) (ψ : SchwartzMap 𝔼 ℂ)
    (k n K : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i ≤ n, ∀ ζ : 𝔼, ‖iteratedFDeriv ℝ i θ ζ‖ ≤ A * (1 + ‖ζ‖) ^ K) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ θ ψ) ≤
      A * 2 ^ n * 2 ^ (k + K) * (Finset.Iic (k + K, n)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ) ψ := by
  set S := (Finset.Iic (k + K, n)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ) ψ with hS
  have hS0 : 0 ≤ S := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) (fun x => ?_)
  have hfun : ⇑(SchwartzMap.smulLeftCLM ℂ θ ψ) = fun y => θ y * ψ y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hθ, smul_eq_mul]
  rw [hfun]
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := θ) (g := ⇑ψ) (N := (n : ℕ∞ω))
    (hθ.1.of_le (by exact_mod_cast le_top)) (ψ.smooth n) x (n := n) le_rfl
  have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
    gcongr; linarith
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => θ y * ψ y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i θ x‖ * ‖iteratedFDeriv ℝ (n - i) ψ x‖ := by gcongr
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (A * (1 + ‖x‖) ^ K) * ‖iteratedFDeriv ℝ (n - i) ψ x‖ := by
      gcongr with i hi
      exact hb i (by have := Finset.mem_range.1 hi; omega) x
    _ = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * A * (‖x‖ ^ k * (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ (n - i) ψ x‖) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * (2 ^ (k + K) * S) := by
      refine Finset.sum_le_sum fun i hi => ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hi' : n - i ≤ n := Nat.sub_le _ _
      have h2 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + K, n)) (k := k + K)
        (n := n - i) le_rfl hi' ψ x
      calc ‖x‖ ^ k * (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ (n - i) ψ x‖
          ≤ (1 + ‖x‖) ^ k * (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ (n - i) ψ x‖ := by gcongr
        _ = (1 + ‖x‖) ^ (k + K) * ‖iteratedFDeriv ℝ (n - i) ψ x‖ := by rw [pow_add]
        _ ≤ 2 ^ (k + K) * S := h2
    _ = A * 2 ^ n * 2 ^ (k + K) * S := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [this]; ring

end HRS.Commutator.TorusNote

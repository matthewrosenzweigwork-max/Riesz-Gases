import HRS.MS.SA16TransferFamilyDefs
import HRS.MS.SA16StrongSL5
import HRS.MS.SA16StrongSL7

/-!
# S.A.16 T10: `cutoff_family_strong_limit`

`cutoffRate d s n = (n+1)^(-(d-s)) → 0` since `s < d`; the dense-data estimate of `CutoffFamily` gives a uniform
Cauchy property on the dense set of compact smooth jets (SL5), the common bound `C e^{C t}` and SL7 give a strong
uniform limit, and the sharper pointwise bound `C e^{C τ}` passes to the limit in the norm.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Cutoff Phase2SA16Evolution

lemma sa16x_rate_tendsto (d : ℕ) (s : ℝ) (hsd : s < d) :
    Tendsto (fun n : ℕ => cutoffRate d s n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hq : 0 < (d : ℝ) - s := by linarith
  have h2 := ((Real.continuousAt_rpow_const (0 : ℝ) ((d : ℝ) - s) (Or.inr hq.le)).tendsto).comp h1
  rw [Real.zero_rpow hq.ne'] at h2
  exact h2

theorem cutoff_family_strong_limit (d m : ℕ) (p s t C : ℝ)
    [Fact (2 ≤ p)] (hsd : s<d) (ht : 0 ≤ t) (hC : 1 ≤ C)
    (κc : LpCase) (coeff : WholeCoeff d)
    (U : ℕ → ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hU : CutoffFamily d m p s t C κc coeff U) :
    ∃ V : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p,
      (∀ G, ContinuousOn (fun τ => V τ G) (Icc (0 : ℝ) t)) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ G, ‖V τ G‖ ≤ C*Real.exp (C*τ)*‖G‖) ∧
      ∀ G, StrongUniformLimit t (fun n τ => U n τ G) (fun τ => V τ G) := by
  have hC0 : 0 ≤ C := by linarith
  have hM0 : 0 ≤ C * Real.exp (C * t) := by positivity
  have hbound : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ‖U n τ‖ ≤ C * Real.exp (C * t) := by
    intro n τ hτ
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun G => ?_
    refine (hU.bound n τ hτ G).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)
      (norm_nonneg G)
    exact mul_le_mul_of_nonneg_left hτ.2 hC0
  have hrate := sa16x_rate_tendsto d s hsd
  have hCauchy : ∀ G ∈ {G : WmpSpace d m p | ∃ u : Euc d → ℝ, IsCcInfty u ∧
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m u},
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k ≥ n₀, ∀ τ ∈ Icc (0 : ℝ) t,
        ‖U n τ G - U k τ G‖ < ε := by
    rintro G ⟨u, hu, heq⟩ ε hε
    have hrep : wrep d m p G =ᵐ[volume] u := by
      filter_upwards [heq] with x hx
      show ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x
      rw [hx]
      simp only [wJet, wZero, partialDeriv]
      exact iteratedFDeriv_zero_apply _
    set w : ℝ := (wNormE (m + 2) p u).toReal with hw
    have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
    have hpos : 0 < C * w + 1 := by positivity
    have hη : 0 < ε / (2 * (C * w + 1)) := by positivity
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hrate.eventually (Iio_mem_nhds hη))
    refine ⟨N0, fun n hn k hk τ hτ => ?_⟩
    have h1 := hU.dense_difference u hu G hrep n k τ hτ
    have hn' : cutoffRate d s n < ε / (2 * (C * w + 1)) := hN0 n hn
    have hk' : cutoffRate d s k < ε / (2 * (C * w + 1)) := hN0 k hk
    refine lt_of_le_of_lt h1 ?_
    have h2 : C * (cutoffRate d s n + cutoffRate d s k) * w ≤ C * w * (2 * (ε / (2 * (C * w + 1)))) := by
      have : cutoffRate d s n + cutoffRate d s k ≤ 2 * (ε / (2 * (C * w + 1))) := by linarith
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hC0 hw0)
      linarith
    refine lt_of_le_of_lt h2 ?_
    have h3 : C * w * (2 * (ε / (2 * (C * w + 1)))) = ε * (C * w / (C * w + 1)) := by
      field_simp
    rw [h3]
    have h4 : C * w / (C * w + 1) < 1 := by
      rw [div_lt_one hpos]; linarith
    nlinarith
  obtain ⟨V, hVb, hVc, hVl⟩ := strong_limit_of_dense_cauchy t (C * Real.exp (C * t)) ht hM0 _
    (wmp_smooth_dense d m p) U hU.cont hbound hCauchy
  refine ⟨V, hVc, fun τ hτ G => ?_, hVl⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n₀, hn₀⟩ := hVl G ε hε
  have h1 := hn₀ n₀ le_rfl τ hτ
  have h2 : ‖V τ G‖ ≤ ‖U n₀ τ G‖ + ‖U n₀ τ G - V τ G‖ := by
    calc ‖V τ G‖ = ‖U n₀ τ G - (U n₀ τ G - V τ G)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖U n₀ τ G‖ + ‖U n₀ τ G - V τ G‖ := norm_sub_le _ _
  linarith [hU.bound n₀ τ hτ G]

end HRS.Whole.AppendixA.Phase2SA16Transfer

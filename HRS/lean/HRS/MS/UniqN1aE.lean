import HRS.MS.UniqN1aD
import HRS.MS.UniqN0d

/-!
# N1a of `UniqPlan.md`, part (e): the truncated Hessian kernel is `L¹` with norm `≤ Cρ^d`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened

variable {d : ℕ}

theorem n1a_DH_meas (s : ℝ) (i j : Fin d) :
    Measurable (fun z : Euc d => q09_DH s j z (EuclideanSpace.single i 1)) := by
  have hc : ∀ k : Fin d, Measurable (fun z : Euc d => z k) := fun k =>
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).measurable
  have : (fun z : Euc d => q09_DH s j z (EuclideanSpace.single i 1)) = fun z =>
      q09_c s * (‖z‖ ^ (-s - 2) * (if j = i then (1 : ℝ) else 0) +
        (z j * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2))) * z i) := funext (n0_qDH_apply s j i)
  rw [this]
  have h1 := hc i
  have h2 := hc j
  fun_prop

/-- Truncated kernel: `∫⁻ |1_{|u| ≤ 5ρ} ∂_i∂_j g(u)| du ≤ C ρ^d` for `ρ ≥ 1`, uniformly in `i, j`. -/
theorem n1a_kernel_trunc (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∫⁻ u, ‖(closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u => q09_DH s j u (EuclideanSpace.single i 1)) u‖ₑ ≤
        ENNReal.ofReal (C * ρ ^ (d : ℝ)) := by
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_ball_rpow_le_proof (d := d) hd (t := s + 2) (by linarith)
  set m : ℝ := max 1 s * (s + 3) with hm
  have hm0 : (0 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
    positivity
  refine ⟨m * CK * (5 : ℝ) ^ (d : ℝ), mul_nonneg (mul_nonneg hm0 hCK0) (Real.rpow_nonneg (by norm_num) _),
    fun i j ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  have h5 : (0 : ℝ) < 5 * ρ := by linarith
  have hpt : ∀ᵐ u ∂(volume : Measure (Euc d)),
      ‖(closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u => q09_DH s j u (EuclideanSpace.single i 1)) u‖ₑ ≤
        (closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u : Euc d => ENNReal.ofReal m * ENNReal.ofReal (‖u‖ ^ (-(s + 2)))) u := by
    filter_upwards [k3_ae_ne hd 0] with u hu
    by_cases hmem : u ∈ closedBall (0 : Euc d) (5 * ρ)
    · simp only [Set.indicator_of_mem hmem]
      rw [← ofReal_norm, ← ENNReal.ofReal_mul hm0]
      apply ENNReal.ofReal_le_ofReal
      have hK := n0_qDH_bound hs0 j i hu
      have hexp : -s - 2 = -(s + 2) := by ring
      rw [hexp] at hK
      rwa [Real.norm_eq_abs]
    · simp [Set.indicator_of_notMem hmem]
  calc ∫⁻ u, ‖(closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u => q09_DH s j u (EuclideanSpace.single i 1)) u‖ₑ
      ≤ ∫⁻ u, (closedBall (0 : Euc d) (5 * ρ)).indicator
          (fun u : Euc d => ENNReal.ofReal m * ENNReal.ofReal (‖u‖ ^ (-(s + 2)))) u :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal m * ∫⁻ u in closedBall (0 : Euc d) (5 * ρ),
          ENNReal.ofReal (‖u‖ ^ (-(s + 2))) := by
        rw [lintegral_indicator measurableSet_closedBall,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal m * ENNReal.ofReal (CK * (5 * ρ) ^ ((d : ℝ) - (s + 2))) :=
        mul_le_mul_of_nonneg_left (hCK (5 * ρ) h5) (by positivity)
    _ = ENNReal.ofReal (m * (CK * (5 * ρ) ^ ((d : ℝ) - (s + 2)))) := by
        rw [ENNReal.ofReal_mul hm0]
    _ ≤ ENNReal.ofReal (m * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have he : (d : ℝ) - (s + 2) ≤ (d : ℝ) := by linarith
        have h5e : (5 : ℝ) ^ ((d : ℝ) - (s + 2)) ≤ (5 : ℝ) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) he
        have hre : ρ ^ ((d : ℝ) - (s + 2)) ≤ ρ ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hρ he
        calc m * (CK * (5 * ρ) ^ ((d : ℝ) - (s + 2)))
            = (m * CK) * ((5 : ℝ) ^ ((d : ℝ) - (s + 2)) * ρ ^ ((d : ℝ) - (s + 2))) := by
              rw [Real.mul_rpow (by norm_num) hρ0.le]; ring
          _ ≤ (m * CK) * ((5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h5e hre (by positivity) (by positivity))
                (mul_nonneg hm0 hCK0)
          _ = m * CK * (5 : ℝ) ^ (d : ℝ) * ρ ^ (d : ℝ) := by ring

end HRS.MS.UniqN1a

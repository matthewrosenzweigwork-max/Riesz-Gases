import HRS.MS.SA12K19

/-!
# S.A.12 L8: elementary bounds for the local terms `νΔψ - div(ψ b)`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MS.ToriCoefA

variable {d : ℕ}

theorem sa12k_movDiv_le {ψ : Euc d → ℝ} {b : Euc d → Euc d} {x : Euc d}
    (hψ : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) :
    |movDiv (fun y => ψ y • b y) x| ≤
      d * (‖fderiv ℝ ψ x‖ * ‖b x‖ + |ψ x| * ‖fderiv ℝ b x‖) := by
  unfold movDiv
  have h1 := hψ.hasFDerivAt.smul hb.hasFDerivAt
  rw [show fderiv ℝ (fun y => ψ y • b y) x = _ from h1.fderiv]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin d, |((ψ x • fderiv ℝ b x + (fderiv ℝ ψ x).smulRight (b x))
      (EuclideanSpace.single i (1 : ℝ))) i| ≤ ‖fderiv ℝ ψ x‖ * ‖b x‖ + |ψ x| * ‖fderiv ℝ b x‖ := by
    intro i
    have he : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    have c1 : |fderiv ℝ ψ x (EuclideanSpace.single i 1) * b x i| ≤ ‖fderiv ℝ ψ x‖ * ‖b x‖ := by
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
      · have := (fderiv ℝ ψ x).le_opNorm (EuclideanSpace.single i (1 : ℝ) : Euc d)
        rw [he, mul_one] at this
        simpa [Real.norm_eq_abs] using this
      · have := PiLp.norm_apply_le (b x) i
        rwa [Real.norm_eq_abs] at this
    have c2 : |ψ x * (fderiv ℝ b x (EuclideanSpace.single i 1)) i| ≤ |ψ x| * ‖fderiv ℝ b x‖ := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h3 := (fderiv ℝ b x).le_opNorm (EuclideanSpace.single i (1 : ℝ) : Euc d)
      rw [he, mul_one] at h3
      have h4 := PiLp.norm_apply_le (fderiv ℝ b x (EuclideanSpace.single i (1 : ℝ))) i
      rw [Real.norm_eq_abs] at h4
      exact h4.trans h3
    linarith
  calc _ ≤ ∑ _i : Fin d, (‖fderiv ℝ ψ x‖ * ‖b x‖ + |ψ x| * ‖fderiv ℝ b x‖) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp; ring

theorem sa12k_lap_le {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : Euc d) :
    |Laplacian.laplacian ψ x| ≤ d * ‖iteratedFDeriv ℝ 2 ψ x‖ := by
  rw [HRS.MS.UniqT3.lap_eq hψ x]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _i : Fin d, ‖iteratedFDeriv ℝ 2 ψ x‖ :=
        Finset.sum_le_sum fun i _ => sa12y_D1D1_le hψ i i x
    _ = _ := by simp

/-- A function supported in `‖x‖ ≤ R` and bounded by `B` decays like `⟨x⟩^{-(d+3)}`. -/
theorem sa12k_cs_decay {g : Euc d → ℝ} {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hin : ∀ x, ‖x‖ ≤ R → |g x| ≤ B) (hout : ∀ x, R < ‖x‖ → g x = 0) (x : Euc d) :
    |g x| ≤ (B * (1 + R) ^ ((d : ℝ) + 3)) * jbracket x ^ (-((d : ℝ) + 3)) := by
  by_cases hx : ‖x‖ ≤ R
  · have hjb0 : 0 < jbracket x := tca_jbracket_pos x
    have hjR : jbracket x ≤ 1 + R := by
      unfold jbracket
      rw [Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith [norm_nonneg x]
    have h1 : (1 + R) ^ (-((d : ℝ) + 3)) ≤ jbracket x ^ (-((d : ℝ) + 3)) :=
      Real.rpow_le_rpow_of_nonpos hjb0 hjR (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    have h2 : (1 + R) ^ ((d : ℝ) + 3) * (1 + R) ^ (-((d : ℝ) + 3)) = 1 := by
      rw [← Real.rpow_add (by linarith)]; simp
    have hone : 1 ≤ (1 + R) ^ ((d : ℝ) + 3) * jbracket x ^ (-((d : ℝ) + 3)) := by
      calc (1 : ℝ) = (1 + R) ^ ((d : ℝ) + 3) * (1 + R) ^ (-((d : ℝ) + 3)) := h2.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc |g x| ≤ B := hin x hx
      _ = B * 1 := by ring
      _ ≤ B * ((1 + R) ^ ((d : ℝ) + 3) * jbracket x ^ (-((d : ℝ) + 3))) :=
          mul_le_mul_of_nonneg_left hone hB
      _ = _ := by ring
  · rw [hout x (not_le.1 hx)]
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (tca_jbracket_pos x).le _)

/-- Radius, jet bound and vanishing outside for a test function. -/
theorem sa12k_psi_data {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∃ R A : ℝ, 1 ≤ R ∧ 0 ≤ A ∧ (∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ A) ∧
      ∀ i, ∀ x : Euc d, R < ‖x‖ → iteratedFDeriv ℝ i ψ x = 0 := by
  obtain ⟨R0, hR0⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hb : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ B := by
    intro i
    have hc : Continuous (iteratedFDeriv ℝ i ψ) :=
      hψ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (hψ.2.iteratedFDeriv i)
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hb
  refine ⟨max R0 1, B 0 + B 1 + B 2, le_max_right _ _, by linarith [hB0 0, hB0 1, hB0 2],
    fun i hi x => ?_, fun i x hx => ?_⟩
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · linarith [hB 0 x, hB0 1, hB0 2]
    · linarith [hB 1 x, hB0 0, hB0 2]
    · linarith [hB 2 x, hB0 0, hB0 1]
  · by_contra hne
    have hmem : x ∈ tsupport ψ := support_iteratedFDeriv_subset i hne
    have := hR0 hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    have h2 : R0 ≤ max R0 1 := le_max_left _ _
    linarith

end HRS.MH.AdjointRd.Phase2SA12Limit

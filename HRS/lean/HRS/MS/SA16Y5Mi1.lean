import HRS.MS.SA16Y5Jc1

/-!
# S.A.16 (SA16Y5) Mi1: mild solution of the fractional-order problem (B8, part 1)

`sa16y5f_kernel Bf Nf s r = Γ_{νs} ∘ Bf r - Qh (νs) (Nf r) : W^{m+2,p} → W^{m+2,p}` (drift part of order one, heat-composed nonlocal part of
order `θ' = s+2-d ∈ (1,2)`).  `sa16y5f_mild`: if `Bf r : W^{m+2} → W^{m+1}` and `Nf r : W^{m+2} → W^m` are bounded and strongly continuous in `r`
and `‖Qh (νs) (Nf r)‖ ≤ CN s^{-γ}` (`1/2 ≤ γ < 1`) then the Volterra equation `u τ = e^{ντΔ}φ + ∫_0^τ Q s (τ-s) u(τ-s) ds` has a unique continuous solution.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mi1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the Volterra kernel `Q s r` -/
def sa16y5f_kernel (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (ν : ℝ)
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) (s r : ℝ) :
    WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1 + 1) p :=
  (sa16r_GamT d (m + 1) p ν s).comp (Bf r) - sa16y5_Qh d m p (ν * s) (Nf r)

set_option maxHeartbeats 800000 in
theorem sa16y5f_voltKer {m : ℕ} {ν T BB CN γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T,
        ‖sa16y5f_kernel d m p ν Bf Nf s r‖ ≤ C * s ^ (-γ)) ∧
      (∀ x : WmpSpace d (m + 1 + 1) p, ContinuousOn (fun q : ℝ × ℝ => sa16y5f_kernel d m p ν Bf Nf q.2 q.1 x)
        {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T}) := by
  have hBB : 0 ≤ BB := (ContinuousLinearMap.opNorm_nonneg _).trans (hBb 0 ⟨le_rfl, hT.le⟩)
  have hCN : 0 ≤ CN := by
    by_contra h
    push_neg at h
    have := hsharp 0 ⟨le_rfl, hT.le⟩ T ⟨hT, le_rfl⟩
    have h2 : 0 ≤ ‖sa16y5_Qh d m p (ν * T) (Nf 0)‖ := ContinuousLinearMap.opNorm_nonneg _
    have h3 : 0 < T ^ (-γ) := Real.rpow_pos_of_pos hT _
    nlinarith
  set Cg := sa16r_Cgam d ν T with hCg
  have hCg0 := sa16r_Cgam_nonneg d hν T
  refine ⟨Cg * BB * T ^ (γ - 1 / 2) + CN, by positivity, fun r hr s hs => ?_, fun x => ?_⟩
  · have h1 : ‖(sa16r_GamT d (m + 1) p ν s).comp (Bf r)‖ ≤ Cg * BB * T ^ (γ - 1 / 2) * s ^ (-γ) := by
      calc _ ≤ ‖sa16r_GamT d (m + 1) p ν s‖ * ‖Bf r‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (Cg * s ^ (-(1 / 2 : ℝ))) * BB :=
            mul_le_mul (sa16r_GamT_bound hν (m + 1) hs.1 hs.2) (hBb r hr) (ContinuousLinearMap.opNorm_nonneg _)
              (mul_nonneg hCg0 (Real.rpow_nonneg hs.1.le _))
        _ = Cg * BB * (s ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ Cg * BB * (T ^ (γ - 1 / 2) * s ^ (-γ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have e : s ^ (-(1 / 2 : ℝ)) = s ^ (γ - 1 / 2) * s ^ (-γ) := by
              rw [← Real.rpow_add hs.1]; congr 1; ring
            rw [e]
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs.1.le hs.2 (by linarith))
              (Real.rpow_nonneg hs.1.le _)
        _ = _ := by ring
    unfold sa16y5f_kernel
    calc _ ≤ ‖(sa16r_GamT d (m + 1) p ν s).comp (Bf r)‖ + ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ := by
          exact @norm_sub_le _ _ ((sa16r_GamT d (m + 1) p ν s).comp (Bf r)) (sa16y5_Qh d m p (ν * s) (Nf r))
      _ ≤ Cg * BB * T ^ (γ - 1 / 2) * s ^ (-γ) + CN * s ^ (-γ) := add_le_add h1 (hsharp r hr s hs)
      _ = _ := by ring
  · -- continuity
    have hg := sa16r_gainData (p := p) hν (m + 1) Bf hBb hBc
    have h1 := sa16r_Gamma_cont hg hCg0 (hBc x)
    have h2 := sa16y5_Qh_joint (p := p) (T := T) hν m Nf hNc x
    unfold sa16y5f_kernel
    exact h1.sub h2

end Mi1

end HRS.Whole.AppendixA.Phase2SA16R

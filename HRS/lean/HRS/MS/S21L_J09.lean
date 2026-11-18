import HRS.MS.R2S11Aux1
import HRS.MS.Comm
import HRS.MS.SuppU1
import HRS.MS.R2ChaosAux11
import HRS.MS.S21F_D00

/-!
# S21L J09 -- `r26t3_commutator_approx` (R26-T3.J09): finite-rank approximation of the physical commutator

Contract of packet R26-T3.J09 (`origin/pro/fine-breakdown`), statement verbatim.  The S9.1 finite-rank approximation is available:
`HRS.Whole.U1.round2_approximation_proof` is the merged native proof (the frozen `round2_approximation` itself is only the specification).
Route: `∇f` of a test function is globally Lipschitz; the commutator kernel is a bounded pair kernel (`HRS.MS.Comm`; at `s = 0` the bound
`|h| ≤ Λ` suffices because `rieszWeight 0 ≥ 0`); the thermal density is a round-2 density (`s11_thermal_round2`); apply S9.1 with
`B ≥ 0` and replace `C` by `max C 0`.  Helpers `s21l_j09_`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T3

open HRS HRS.Whole

theorem s21l_j09_lip {d : ℕ} {f : Euc d → ℝ} (hf : IsR2Test f) : ∃ Λ : ℝ≥0, LipschitzWith Λ (gradient f) := by
  have hd1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.1.fderiv_right (by norm_cast)
  have hg : (gradient f) = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ f := rfl
  have h1 : ContDiff ℝ 1 (gradient f) := by
    rw [hg]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp hd1
  have h2 : HasCompactSupport (gradient f) := by
    rw [hg]
    exact (hf.2.fderiv ℝ).comp_left (map_zero _)
  exact h1.lipschitzWith_of_hasCompactSupport h2 one_ne_zero

theorem s21l_j09_rieszWeight_nonneg {d : ℕ} (s : ℝ) (z : Euc d) : 0 ≤ rieszWeight s z := by
  unfold rieszWeight
  split_ifs
  · exact le_max_right _ _
  · exact Real.rpow_nonneg (norm_nonneg _) _

theorem s21l_j09_bounded {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) {f : Euc d → ℝ} (hf : IsR2Test f) :
    ∃ B : ℝ, IsBoundedPairKernel s B (commutatorKernel d s (gradient f)) := by
  obtain ⟨Λ, hΛ⟩ := s21l_j09_lip hf
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨Λ, HRS.MS.Comm.comm_meas (s := 0) (gradient f) hΛ.continuous.measurable, HRS.MS.Comm.comm_symm (s := 0) (gradient f),
      fun x y hxy => ?_⟩
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
    have hΛ0 : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
    have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
      rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
      norm_num [movtr_sigma, Real.rpow_neg_one]
    have key : |commutatorKernel d 0 (gradient f) x y| ≤ (Λ : ℝ) := by
      unfold commutatorKernel
      calc |inner ℝ (gradient f x - gradient f y) (rieszKernelGrad d 0 (x - y))|
          ≤ ‖gradient f x - gradient f y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ ((Λ : ℝ) * ‖x - y‖) * ‖x - y‖⁻¹ :=
            mul_le_mul (HRS.MS.Comm.comm_lip hΛ x y) hG.le (norm_nonneg _) (by positivity)
        _ = (Λ : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
    have hw := s21l_j09_rieszWeight_nonneg (d := d) 0 (x - y)
    nlinarith [mul_nonneg hΛ0 hw]
  · exact ⟨s * Λ, HRS.MS.Comm.commutatorKernel_isBounded_proof hpos Λ _ hΛ⟩

theorem r26t3_commutator_approx (p : Parameters) (ρβ : Euc p.d → ℝ)
    (hρβ : IsThermalEquilibrium p.d p.s p.a p.β ρβ)
    (f : Euc p.d → ℝ) (hf : IsR2Test f) :
    ∃ C B : ℝ, 0≤C ∧ 0≤B ∧ ∃ h : ℕ → Euc p.d → Euc p.d → ℝ,
      IsBoundedPairKernel p.s B (commutatorKernel p.d p.s (gradient f)) ∧
      IsRound2Approx p.s C B (HRS.Whole.withDensityReal ρβ) (commutatorKernel p.d p.s (gradient f)) h := by
  obtain ⟨B, hB⟩ := s21l_j09_bounded p.hd p.s p.hs0 hf
  have hB0 : 0 ≤ B := HRS.MS.R2Chaos.s94_B_nonneg p.hd hB
  obtain ⟨M, L, c, hρ, -⟩ := HRS.MS.R2S11.s11_thermal_round2 p.hd p.hs0 p.hs p.ha p.hβ hρβ
  obtain ⟨C, hC⟩ := HRS.Whole.U1.round2_approximation_proof p.hd p.s p.hs0 p.hs
  obtain ⟨hj, hA⟩ := hC M L ρβ hρ B (commutatorKernel p.d p.s (gradient f)) hB
  refine ⟨max C 0, B, le_max_right _ _, hB0, hj, hB, hA.finiteRank, fun j x y hxy => ?_, hA.converges⟩
  have h1 := hA.envelope j x y hxy
  have hw := s21l_j09_rieszWeight_nonneg (d := p.d) p.s (x - y)
  have h2 : 0 ≤ B * (1 + rieszWeight p.s (x - y)) := mul_nonneg hB0 (by linarith)
  calc |hj j x y| ≤ C * B * (1 + rieszWeight p.s (x - y)) := h1
    _ = C * (B * (1 + rieszWeight p.s (x - y))) := by ring
    _ ≤ max C 0 * (B * (1 + rieszWeight p.s (x - y))) := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
    _ = max C 0 * B * (1 + rieszWeight p.s (x - y)) := by ring

end HRS.MS.R26T3

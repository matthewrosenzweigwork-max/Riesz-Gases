import HRS.MS.R26T8AP08h
import HRS.MS.R26T8AN5
import HRS.MS.R26T8AP11f23

/-!
# S8.2 T8A P08 (part i): `r26t8a_newton_projection_full` and `_nonneg`
`localNewton μ β⁻¹ chi F = r2CenterKernel μ (rawNewton β⁻¹ chi F)` is a `CanonicalPair` for `μ = ρ dx` and `Conormal k (b+1) M (σ-2) (C A)`.
Under `Conormal (r26t8a_rawGainReg k σ) b M σ A F` (equal to `k` when `0 ≤ σ`, see the handoff note on `σ < 0`).
Combination of P07 (`r26t8a_raw_newton_bound_full`) and the centering lemma `r26t8a_f25_center`; the constant is uniform in `ρ`
because the thermal density is unique (`critical_thermal_eq`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 3200000 in
theorem r26t8a_newton_projection_full (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
        Conormal (r26t8a_rawGainReg k sigma) b M sigma A F →
        CanonicalPair (HRS.Whole.withDensityReal rho)
          (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) ∧
        Conormal k (b + 1) M (sigma - 2) (C * A)
          (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) := by
  classical
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_raw_newton_bound_full d hd k b beta⁻¹ M sigma (inv_pos.2 hbeta) hM hsd chi hchi
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith)
    ha hbeta h0
  obtain ⟨Cρ, cρ, hCρ, hcρ, hρb⟩ := r26t8a_f23_rho_unif hg k
  obtain ⟨Kp, hKp0, hKp⟩ := r26t8a_f25_rho_poly hCρ hcρ hρb (M + (d : ℝ) + 1)
  have hρk : ContDiff ℝ (k : WithTop ℕ∞) ρ0 := hρs.of_le (by exact_mod_cast le_top)
  have hsd2 : sigma - 2 < d := by linarith
  obtain ⟨Cc, hCc0, hCc⟩ := r26t8a_f25_center hchi hd k (b + 1) hM hsd2 h0.1.1 hρk hρs.continuous hKp0 hKp
  refine ⟨Cc * C1, by positivity, ?_⟩
  intro rho hrho F A hA hF
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  obtain ⟨-, hraw⟩ := hC1 F A hA hF
  obtain ⟨hcan, hcon⟩ := hCc (A := C1 * A) (by positivity) hraw
  refine ⟨hcan, ?_⟩
  have e : Cc * C1 * A = Cc * (C1 * A) := by ring
  rw [e]
  exact hcon

theorem r26t8a_newton_projection_nonneg (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hσ : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal k b M sigma A F →
        CanonicalPair (HRS.Whole.withDensityReal rho)
          (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) ∧
        Conormal k (b + 1) M (sigma - 2) (C * A)
          (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_newton_projection_full d hd k b a beta M sigma ha hbeta hM hsd chi hchi
  refine ⟨C, hC0, fun rho hrho F A hA hF => hC rho hrho F A hA ?_⟩
  simpa only [r26t8a_rawGainReg, if_pos hσ] using hF

end HRS.MS.R26T8A

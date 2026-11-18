import HRS.MS.R26T8AP08h
import HRS.MS.R26T8AZ6
import HRS.MS.R26T8AP11f23

/-!
# S8.2 T8A Z7a (= P08 same-k): `r26t8a_newton_projection_same`
The Pro P08 contract verbatim for every `σ < d`: under `Conormal k b M σ A F`, `localNewton` is canonical and `Conormal k (b+1) M (σ-2) (C A)`.
Same proof as `r26t8a_newton_projection_same`, with `r26t8a_raw_newton_bound_same` (Z6) in place of the Taylor-split P07.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 3200000 in
theorem r26t8a_newton_projection_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
        Conormal k b M sigma A F →
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
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_raw_newton_bound_same d hd k b beta⁻¹ M sigma (inv_pos.2 hbeta) hM hsd chi hchi
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

end HRS.MS.R26T8A

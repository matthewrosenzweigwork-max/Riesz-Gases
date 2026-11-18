import HRS.MC.S7S7bAux6
import HRS.MC.S7S7bAux1

/-!
# Packet `s7_S7b_weighted_moments`, helper 7: `|grad g(z)| |z| <= K (g(z) + c)` and the `L^2(mu x mu)` norm of `h_v`
`int int h_v^2 dmu dmu <= C sum_j ||v_j||_{H^1}^2` (translation estimate + the envelope of `grad g`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE

variable {d : ℕ} {s : ℝ}

theorem s7b_grad_dist (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ K c : ℝ, 0 ≤ K ∧ (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) ∧
      ∀ z : Torus d, z ≠ 0 →
        ‖periodicRieszGrad d s z‖ * ‖Torus.centeredRep z‖ ≤ K * (periodicRiesz d s z + c) := by
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨Cg, hCg⟩ := HRS.Quad.periodicRiesz_lower_env hd hs0 hsd
  obtain ⟨C, hC⟩ := HRS.KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd
  have hg1 : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + Cg := fun z hz => by
    have := HRS.Quad.one_le_envT (d := d) (s := s) z
    have := hCg z hz
    linarith
  refine ⟨max C 0 * (1 + d), Cg, by positivity, hg1, fun z hz => ?_⟩
  set t := HRS.KernelGrad.tdist z 0 with ht
  have htpos : 0 < t := by
    rcases (HRS.KernelGrad.tdist_nonneg z 0).lt_or_eq with h | h
    · exact h
    · exact absurd ((HRS.Commutator.EnergyAux.tdist_eq_zero_iff z).1 h.symm) hz
  have htd : t ≤ d := HRS.Commutator.SliceAux.tdist_le_dim z
  have hcr : ‖Torus.centeredRep z‖ = t := HRS.Commutator.EnergyAux.norm_centeredRep_eq z
  rw [hcr]
  have h3 : t * (t ^ (-s - 1) + 1) = t ^ (-s) + t := by
    have : t ^ (-s - 1 + 1) = t ^ (-s - 1) * t := Real.rpow_add_one htpos.ne' _
    rw [show -s - 1 + 1 = -s by ring] at this
    rw [this]; ring
  have h1 : ‖periodicRieszGrad d s z‖ * t ≤ max C 0 * (t ^ (-s) + t) := by
    calc ‖periodicRieszGrad d s z‖ * t ≤ (C * (t ^ (-s - 1) + 1)) * t :=
          mul_le_mul_of_nonneg_right (hC z hz) htpos.le
      _ ≤ (max C 0 * (t ^ (-s - 1) + 1)) * t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
            (by positivity)) htpos.le
      _ = max C 0 * (t * (t ^ (-s - 1) + 1)) := by ring
      _ = max C 0 * (t ^ (-s) + t) := by rw [h3]
  have hg := hCg z hz
  have hg1z := hg1 z hz
  have hr := HRS.MC.SEdge.B2a.b2a_rpow_le_envT (d := d) (s := s) z
  have hmax : 0 ≤ max C 0 := le_max_right _ _
  have hbound : t ^ (-s) + t ≤ (1 + d) * (periodicRiesz d s z + Cg) := by
    have : HRS.Quad.envT s z ≤ periodicRiesz d s z + Cg := by linarith
    nlinarith
  calc ‖periodicRieszGrad d s z‖ * t ≤ max C 0 * (t ^ (-s) + t) := h1
    _ ≤ max C 0 * ((1 + d) * (periodicRiesz d s z + Cg)) :=
        mul_le_mul_of_nonneg_left hbound hmax
    _ = _ := by ring

end HRS.MC.Sec7.S7b

end

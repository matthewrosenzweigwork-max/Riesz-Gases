import HRS.Equilibrium.Parametrix.PXFIDAuxI

/-!
# Packet PX-FID, file J: product measurability and integrability of the envelope
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

theorem measurable_eucDist_prod (d : ℕ) :
    Measurable (fun p : Torus d × Torus d => Torus.eucDist p.1 p.2) := by
  unfold Torus.eucDist
  refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => ?_)
  refine Measurable.pow_const ?_ 2
  exact (((measurable_pi_apply i).comp measurable_fst).sub
    ((measurable_pi_apply i).comp measurable_snd)).norm

theorem measurable_wEnv_prod (d : ℕ) (s : ℝ) :
    Measurable (fun p : Torus d × Torus d => wEnv s p.1 p.2) := by
  unfold wEnv rTrunc
  exact measurable_const.add ((measurable_const.min (measurable_eucDist_prod d)).pow_const _)

theorem integrable_wEnv_prod (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hρΛ : ∀ x, ρ x ≤ Λ) (hρ : IsProbDensity ρ) :
    Integrable (fun p : Torus d × Torus d => wEnv s p.1 p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  refine ⟨(measurable_wEnv_prod d s).aestronglyMeasurable, ?_⟩
  have h0 : 0 ≤ᵐ[(withDensityReal ρ).prod (withDensityReal ρ)]
      (fun p : Torus d × Torus d => wEnv s p.1 p.2) :=
    Filter.Eventually.of_forall (fun p => zero_le_one.trans (PairCorrAux.one_le_wEnv s p.1 p.2))
  rw [hasFiniteIntegral_iff_ofReal h0]
  have hm : Measurable (fun p : Torus d × Torus d => ENNReal.ofReal (wEnv s p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_wEnv_prod d s)
  rw [lintegral_prod (fun p : Torus d × Torus d => ENNReal.ofReal (wEnv s p.1 p.2)) hm.aemeasurable]
  set c : ℝ := PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2 with hc
  have hinner : ∀ x : Torus d, ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * ENNReal.ofReal c := by
    intro x
    calc ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          lintegral_mono' (withDensityReal_le_smul' hρΛ) le_rfl
      _ = ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (wEnv s x y) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal c :=
          by gcongr; exact PairCorrAux.radial_B0 hd hcrit x
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ) ∂(withDensityReal ρ)
      ≤ ∫⁻ _x, ENNReal.ofReal Λ * ENNReal.ofReal c ∂(withDensityReal ρ) := lintegral_mono hinner
    _ = ENNReal.ofReal Λ * ENNReal.ofReal c := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end HRS.Parx.PXFID

end

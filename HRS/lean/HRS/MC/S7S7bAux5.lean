import HRS.MC.S7S7aAux5

/-!
# Packet `s7_S7b_weighted_moments`, helper 5: the transport field with an `H^1` bound
For smooth `a` with `mu(a) = 0` there is a smooth `v` with `-div(rho v) = rho a` and
`||v_j||_{H^1} <= P ||a||_{L^2}` (the `m = 0` version of `s7a_v_exists`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart
open HRS.MC.Sec7.S7a

variable {d : ℕ} {s : ℝ}

theorem s7b_v_exists_H1 (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x ∂(withDensityReal ρ) = 0 →
      ∃ v : Fin d → Torus d → ℝ, (∀ j, Torus.IsSmooth (v j)) ∧
        (∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * a x)) ∧
        ∀ j, MemHs (1 : ℝ) (coeffOf (v j)) ∧
          HRS.PDE.hsNorm (1 : ℝ) (coeffOf (v j)) ≤ P * HRS.PDE.hsNorm (0 : ℝ) (coeffOf a) := by
  have hd0 : 0 < d := by omega
  have hinv : Torus.IsSmooth (fun y => (ρ y)⁻¹) :=
    HRS.Q66.q66_isSmooth_inv hρ.smooth (fun y => (hρ.pos y).ne')
  obtain ⟨Ci, hCi0, hCi⟩ := s7a_mul_smooth hd0 hinv 1
  obtain ⟨Cp, hCp0, hCp⟩ := s7a_mul_smooth hd0 hρ.smooth 0
  refine ⟨Ci * Real.sqrt 2 * Cp, by positivity, fun a ha hmean => ?_⟩
  have hρm : Measurable ρ := hρ.density.measurable
  have hf : Torus.IsSmooth (fun x => ρ x * a x) := HRS.Q66.q66_isSmooth_mul hρ.smooth ha
  have hmean' : ∫ x, ρ x * a x = 0 := by
    rw [← integral_withDensityReal_eq ρ hρm (fun x => (hρ.pos x).le)]; exact hmean
  obtain ⟨ψ, hψ, hΔ⟩ := HRS.Q66.q66_poisson hf hmean'
  refine ⟨fun j y => (ρ y)⁻¹ * Torus.partialDeriv j ψ y, fun j => ?_, fun x => ?_, fun j => ?_⟩
  · exact HRS.Q66.q66_isSmooth_mul hinv (HRS.Q66.q66_isSmooth_partialDeriv hψ j)
  · have h2 : Torus.IsCk 2 ψ := HRS.Q66.q66_isCk_of_smooth hψ 2
    have e2 : ∀ j : Fin d, (fun y => ρ y * ((ρ y)⁻¹ * Torus.partialDeriv j ψ y)) =
        fun y => Torus.partialDeriv j ψ y := fun j => by
      funext y; field_simp [(hρ.pos y).ne']
    simp_rw [e2]
    rw [← laplacian_eq_sum ψ h2 x, hΔ]
  · have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
    have hac : Continuous a := HRS.Q66.q66_cont_of_smooth ha
    have hamem : MemHs ((0 : ℕ) : ℝ) (coeffOf a) :=
      memHs_of_isCk 0 a (HRS.Q66.q66_isCk_of_smooth ha _)
    obtain ⟨hu1, hu2⟩ := hCp a hac hamem
    have hP := s7a_poisson_bound hψ hΔ 0 hu1 j
    have hd1 : ((0 : ℕ) : ℝ) + 1 = (((1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hd1] at hP
    obtain ⟨hP1, hP2⟩ := hP
    obtain ⟨hv1, hv2⟩ := hCi (Torus.partialDeriv j ψ)
      (HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hψ j)) hP1
    simp only [Nat.cast_zero, Nat.cast_one] at hv1 hv2 hP2 hu2
    refine ⟨hv1, ?_⟩
    calc _ ≤ Ci * HRS.PDE.hsNorm (1 : ℝ) (coeffOf (Torus.partialDeriv j ψ)) := hv2
      _ ≤ Ci * (Real.sqrt 2 * HRS.PDE.hsNorm (0 : ℝ) (coeffOf fun x => ρ x * a x)) :=
          mul_le_mul_of_nonneg_left hP2 hCi0
      _ ≤ Ci * (Real.sqrt 2 * (Cp * HRS.PDE.hsNorm (0 : ℝ) (coeffOf a))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu2 (Real.sqrt_nonneg _)) hCi0
      _ = _ := by ring

end HRS.MC.Sec7.S7b

end

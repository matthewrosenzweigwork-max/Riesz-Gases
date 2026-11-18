import HRS.PDE.MovSpec1
import HRS.PDE.MovSXAux3
import HRS.PDE.MovSXAux5
import HRS.PDE.MovSXAux7

/-!
# MOVSX: relocated proofs of MovSpec1 packets (`_proof`, statements verbatim)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_pressure_two_sided_C2_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) (B : ℝ) :
    ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
        Torus.cbNorm 2 ρ ≤ Λ₂ →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) :=
  movsx_pressure_two_sided_C2 hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ₂ B

example := (@movT_pressure_two_sided_C2_proof : type_of% @HRS.movT_pressure_two_sided_C2)

theorem movT_source_exp_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ l C : ℝ, 0 < l ∧ ∀ D : DynData d, D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
        Torus.cbNorm 2 ρ ≤ Λ₂ →
      ∀ Lu : ℝ, 0 < Lu → IsLipschitzVF Lu (mfeTransport D ρ) →
      ∀ N : ℕ, 2 ≤ N →
        Integrable (movT_commAt D N ρ)
          (modulatedGibbs (periodicRiesz d s) N D.invβ⁻¹ (withDensityReal ρ)) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l / Lu) * |movT_sourceAt D N ρ X|))
          ∂(modulatedGibbs (periodicRiesz d s) N D.invβ⁻¹ (withDensityReal ρ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) :=
  movsx_source_exp hd hs0 hsd βm βp hβm c₀ hc₀ Λ₂

example := (@movT_source_exp_proof : type_of% @HRS.movT_source_exp)

/-- `movT_source_exp_uniform` (gap (2), route (i)).  Depends on the sorried packets `movT_srcReg_decomp` (MOV-A) and
`movT_traj_bounds` only through their statements: the clean conditional theorem is
`movsx_source_exp_uniform_of` (Aux7), which has the two conclusions as hypotheses.
Since `movT_srcReg_decomp` is repaired to `0 < T` (SPEC-GF3, ISSUES MOVA), this version carries `0 < T` and no longer matches
`movT_source_exp_uniform`; the tie for all `T` is `movT_source_exp_uniform_proof'` (`MovAFinal`). -/
theorem movT_source_exp_uniform_proof (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) :
    ∃ l C M₀ : ℝ, 0 < l ∧ ∀ M : ℝ, M₀ ≤ M → ∀ r ∈ Set.Icc 0 T,
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) :=
  movsx_source_exp_uniform_of hN htr (movT_srcReg_decomp hN htr hρt hT) (movT_traj_bounds htr)

end HRS

end

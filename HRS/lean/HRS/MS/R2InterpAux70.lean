import HRS.MS.R2InterpAux69
import HRS.MS.ZeroTempAux5
import HRS.MS.UlWitTie

/-!
# S10.2 (worker S102), part 70: linearity of the adjoint propagator on Schwartz data (the quadratic stationary coefficient)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S85 HRS.MS.S52B

variable {d : ℕ}

theorem s102_propagator_comb (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 ≤ T)
    (φ ψ : SchwartzMap (Euc d) ℝ) (c : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) :
    propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t (fun x => φ x + c * ψ x) =
      fun x => propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ x +
        c * propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t ψ x := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  obtain ⟨f₁, h₁⟩ := s102_exists_adjoint hd hs0 hs ha hβ hρ hT φ ht
  obtain ⟨f₂, h₂⟩ := s102_exists_adjoint hd hs0 hs ha hβ hρ hT ψ ht
  rw [HRS.MS.S21.s21_dyn_eq] at h₁ h₂ ⊢
  set D : WholeDyn d := (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d) with hD
  obtain ⟨Λ, hΛ⟩ := HRS.MS.UlW.ulw_coeffHyp hd hs0 hsd 1 hρS.1 hρS.2 T
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 (1 + 3)
  have hslice := HRS.MS.Fcau.fcau_slices_of_hyp (by omega) hs0 hsd 1 le_rfl (∑ i, ∑ j, |(-1 : Matrix (Fin d) (Fin d) ℝ) i j|)
    Λ ΛV G₀ (D := D) (ρ := fun _ => ρ) (T := T) rfl (HRS.MS.Go.s55f_matBound _) hV hΛ ht
  have hcomb := HRS.MS.ZeroTemp.sa11_isClassical_comb (by omega) D hs0 hsd (fun _ => ρ) t hslice c h₁ h₂
  have hu := fun {φ' : Euc d → ℝ} {f' : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW (D.coeff (fun _ => ρ)) t φ' f') =>
    HRS.MS.UlW.ulw_unique hd hs0 hsd (-1) (a • 1) hQ 0 hν hρS.1 hρS.2 T ht hf r hr
  rw [hu hcomb, hu h₁, hu h₂]

end HRS.MS.R2Interp

end

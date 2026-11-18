import HRS.MS.S111X1F1
import HRS.MS.ZeroTempAux5
import HRS.MS.FeatDecAux12

/-!
# S11.1 X1, classical adjoint theory of the stationary model: uniqueness and linear combinations
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem x1C_eq (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) :
    x1C d s a β ρ = (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ) := by
  unfold x1C
  rw [HRS.MS.S21.s21_dyn_eq]

theorem uniq_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∀ t : ℝ, 0 ≤ t → ∀ (φ : Euc d → ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
      IsClassicalAdjointW (x1C d s a β ρ) t φ f₁ → IsClassicalAdjointW (x1C d s a β ρ) t φ f₂ →
      ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by unfold Matrix.IsSymm; simp
  intro t ht φ f₁ f₂ h₁ h₂ r hr
  have hu := HRS.MS.S85.s85_uniq hd hs0 hsd (inv_pos.2 hβ) (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ hSch t
    t ⟨ht, le_rfl⟩ φ f₁ f₂
  rw [x1C_eq, HRS.MS.S85.s85_coeff_fv _ hQ] at h₁ h₂
  exact hu h₁ h₂ r hr

theorem comb_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∀ t : ℝ, 0 ≤ t → ∀ (φ ψ : Euc d → ℝ) (c : ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
      IsClassicalAdjointW (x1C d s a β ρ) t φ f₁ → IsClassicalAdjointW (x1C d s a β ρ) t ψ f₂ →
      IsClassicalAdjointW (x1C d s a β ρ) t (fun x => φ x + c * ψ x) (fun r x => f₁ r x + c * f₂ r x) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  obtain ⟨B, hBdef, hGap, hcb⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρ
  obtain ⟨Mb, hMb⟩ := hcb 1
  have hreg : HRS.MH.DualityRd.RegSliceRd ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_regSlice hd hs0 hsd ha hβ
  intro t ht φ ψ c f₁ f₂ h₁ h₂
  have hslice : HRS.MS.Fcau.FcauSlices (quadraticGradientDyn d s a β) (fun _ => ρ) t := by
    intro r hr
    refine ⟨hreg, fun i => ?_⟩
    have hdr' : ∀ y, meanFieldDriftW (quadraticGradientDyn d s a β) ρ y = β⁻¹ • B y - a • y := by
      intro y
      exact hdrift_aux hd hs0 hsd ha hβ hρ B hBdef y
    simp_rw [hdr']
    have hB1 : ContDiff ℝ 1 B := hMb.1
    have : ContDiff ℝ 1 (fun y => β⁻¹ • B y - a • y) := (hB1.const_smul β⁻¹).sub (contDiff_id.const_smul a)
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp this
  have := HRS.MS.ZeroTemp.sa11_isClassical_comb (by omega) (quadraticGradientDyn d s a β) hs0 hsd (fun _ => ρ) t
    hslice (c := c) h₁ h₂
  exact this

end HRS.MS.S111X1

import HRS.ME.BiasH
import HRS.ME.UnifP8A
import HRS.MD.EQEvoUnif

/-!
# Uniform `critical_bias_constants`, P1: uniform lower bound and `C^k` bound of thermal densities
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main
open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.PDE

/-- P1: uniform lower bound and `C^k` bound of the thermal densities (constants chosen before `β`, `ρβ`). -/
theorem thermal_lower_cbNorm_unif (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (k : ℕ) :
    ∃ c₀ Λ : ℝ, 0 < c₀ ∧ 0 ≤ Λ ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      (∀ x, c₀ ≤ ρβ x ∧ ρβ x ≤ Λ) ∧ Torus.cbNorm k ρβ ≤ Λ := by
  have hd1 : 1 ≤ d := by omega
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set K : ℕ := 6 * d + 30 + k with hKdef
  obtain ⟨Λ₀, c₀', lam, Lam, B, -, hlam, hB0, hmain⟩ :=
    HRS.MD.EQEvoUnif.eqevo_thermal_unif hd ((d : ℝ) / 2) βm βp hs0 hsd hβm hββ V hV 0 K
      (by omega)
  have hKr : (d : ℝ) / 2 + (k : ℝ) < (K : ℝ) := by
    have : (K : ℝ) = 6 * d + 30 + k := by simp [hKdef]
    rw [this]; linarith
  obtain ⟨C, hC⟩ := cbNorm_le_sobolevNorm (d := d) k (K : ℝ) hKr
  have hVc : Continuous V :=
    HRS.PDE.continuous_of_isCk (by exact_mod_cast HRS.MD.EQEvoUnif.eqevo_isCk_nat hV 1)
  refine ⟨lam, max Lam (max C 0 * Real.sqrt B), hlam, ?_, fun β hβ ρβ hρβ => ?_⟩
  · exact le_max_of_le_right (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
  · have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
    obtain ⟨hpos, hc⟩ := HRS.Q41.q41_thermal_pos_cont hd hs0 hsd hβ0 hVc hρβ
    have hSob : MemSobolev (K : ℝ) ρβ :=
      HRS.PDE.MFThermalAssembly.thermal_memSobolev_all hd1 ((d : ℝ) / 2) hs0 hsd K V
        (by exact_mod_cast HRS.MD.EQEvoUnif.eqevo_isCk_nat hV (K + 2)) β hβ0 ρβ hρβ hc hpos
    obtain ⟨hlamB, hLamB⟩ := (hmain β hβ ρβ hρβ).2
    have hB' : hsNormSq (K : ℝ) (coeffOf ρβ) ≤ B := hLamB
    have hEq := (hsNormSq_coeffOf (K : ℝ) ρβ hSob).2
    have hsn : sobolevNorm (K : ℝ) ρβ ≤ Real.sqrt B := by
      have h2 : sobolevNorm (K : ℝ) ρβ ^ 2 ≤ B := hEq ▸ hB'
      calc sobolevNorm (K : ℝ) ρβ = Real.sqrt (sobolevNorm (K : ℝ) ρβ ^ 2) :=
            (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt h2
    have hsm : Torus.IsSmooth ρβ := (smoothPos_of_thermal hd hs0 hsd hβ0 hV hρβ).smooth
    have hCk : Torus.IsCk (k : WithTop ENat) ρβ := HRS.MD.EQEvoUnif.eqevo_isCk_nat hsm k
    have hcb := hC ρβ hSob (by exact_mod_cast hCk)
    refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
    · exact hlamB x |>.1
    · exact (hlamB x).2.trans (le_max_left _ _)
    · refine hcb.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (by
        unfold sobolevNorm; exact Real.sqrt_nonneg _)).trans ?_) |>.trans (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left hsn (le_max_right _ _)

end HRS.ME.Bias

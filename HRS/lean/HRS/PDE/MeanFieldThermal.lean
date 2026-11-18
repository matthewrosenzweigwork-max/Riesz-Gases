import HRS.PDE.MeanFieldThermalTrunc
import HRS.PDE.MeanFieldThermalReg
import HRS.PDE.MeanFieldThermalRegB

/-!
# The thermal density: existence, regularity (package MF-01, assembly)

Assembles the thermal-equation results used by `HRS/PDE/MeanField.lean`:
* `kernelFacts`: the kernel-fact bundle for every `d ≥ 1` (`mfKernelFacts_of_two`,
  `mfKernelFacts_one`);
* `thermal_exists_continuous`: a continuous positive thermal density exists for continuous `V`
  (Fejér-truncated dual minimisation `exists_truncated_thermal` and the compactness limit
  `thermal_exists_continuous_of_truncated`; plan §3.1);
* `thermal_memSobolev_all`, `thermal_isSmooth_all`: regularity, proved for `s < d/2 + 1`
  (`MFThermalReg`) and through `MFThermalRegB.thermal_memSobolev_general` otherwise.
-/

noncomputable section

open MeasureTheory

namespace HRS.PDE.MFThermalAssembly

variable {d : ℕ}

/-- The kernel-fact bundle for every `d ≥ 1`. -/
theorem kernelFacts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    MFInputs.MFKernelFacts d s := by
  rcases Nat.lt_or_ge d 2 with h | h
  · exact MFInputs.mfKernelFacts_one (by omega) s hs0 hsd
  · exact MFInputs.mfKernelFacts_of_two h s hs0 hsd

/-- Existence of a continuous positive thermal density for continuous `V`, every `d ≥ 1`. -/
theorem thermal_exists_continuous (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Continuous V) (β : ℝ) (hβ : 0 < β) :
    ∃ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) V β ρ ∧ Continuous ρ ∧
      ∀ x, 0 < ρ x := by
  have F := kernelFacts hd s hs0 hsd
  obtain ⟨ρ, hρ, hc, lam, Lam, hlam, hb⟩ :=
    MFThermalExist.thermal_exists_continuous_of_truncated hd s hs0 hsd F V hV β hβ
      (fun N hN => MFThermalExist.exists_truncated_thermal hd s hs0 hsd F V hV β hβ N hN)
  exact ⟨ρ, hρ, hc, fun x => lt_of_lt_of_le hlam (hb x).1⟩

/-- `MemSobolev K` regularity of a continuous positive thermal density with `V ∈ C^{K+2}`:
proved for `s < d/2 + 1`, through `MFThermalRegB.thermal_memSobolev_general` otherwise. -/
theorem thermal_memSobolev_all (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    MemSobolev K ρ := by
  by_cases hs : s < (d : ℝ) / 2 + 1
  · exact MFThermalReg.thermal_memSobolev_of_lt hd s hs0 hsd (kernelFacts hd s hs0 hsd) hs K V hV
      β hβ ρ hρ hc hp
  · exact MFThermalRegB.thermal_memSobolev_general hd s hs0 hsd K V hV β hβ ρ hρ hc hp

/-- Smoothness of a continuous positive thermal density for smooth `V`: proved for
`s < d/2 + 1`, through `MFThermalRegB.thermal_memSobolev_general` otherwise. -/
theorem thermal_isSmooth_all (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    Torus.IsSmooth ρ := by
  by_cases hs : s < (d : ℝ) / 2 + 1
  · exact MFThermalReg.thermal_isSmooth_of_lt hd s hs0 hsd (kernelFacts hd s hs0 hsd) hs V hV
      β hβ ρ hρ hc hp
  · have hdec : ∀ N : ℕ, MemHs (N : ℝ) (coeffOf ρ) := fun N =>
      (ProdAux.memHs_of_memSobolev (N : ℝ)
        (MFThermalRegB.thermal_memSobolev_general hd s hs0 hsd N V
          (ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV)
            (WithTop.coe_le_coe.2 le_top)) β hβ ρ hρ hc hp)).1
    have hr : IsRealCoeff (coeffOf ρ) :=
      isRealCoeff_coeffOf ρ (MFThermalReg.integrable_of_cont hc)
    have hsum : Summable fun k => ‖coeffOf ρ k‖ :=
      summable_norm_of_memHs ((d + 1 : ℕ) : ℝ)
        (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) _ (hdec (d + 1))
    have := isSmooth_toFun_of_decay (coeffOf ρ) hr hdec
    rwa [MFThermalReg.toFun_coeffOf hc hsum] at this

end HRS.PDE.MFThermalAssembly

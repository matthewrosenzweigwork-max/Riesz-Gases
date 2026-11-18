import HRS.MD.EQBurnClt
import HRS.MD.EQBurnZero
import HRS.MD.EQBurnEvoFixed
import HRS.MD.EQ29Vocab

/-!
# Packet EQ-BURN P6, unconditional: `eq_static_clt_proof`

The static CLT of `HRS/MD/EQ29Spec.lean` (statement copied verbatim, no extra hypotheses), from `eq_static_clt_of_burn_proof` with the
fixed-`β` burn-in at `T = 0` discharged by P1 (`eq_evo_fixed_proof` at window length `1`, `m = d+2`) and P5 (`eq_burnin_zero_proof`
at `βm = βp = β`).  The tie `HRS/MD/EQBurnCltTie.lean` compares with `HRS.MD.EQ29.eq_static_clt`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnClt

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQ29 HRS.MD.EQBurn

variable {d : ℕ}

theorem eq_static_clt_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) :
    ConvergesInLaw
      (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
        (linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ))
      (gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < (d : ℝ) + 2 :=
    max_lt (by linarith) (by linarith)
  obtain ⟨K, c, Cmax, hK, hc, hCmax, hevo⟩ :=
    HRS.MD.EQBurnEvoFixed.eq_evo_fixed_proof hd hs0 hsd V hV hβ ((d : ℝ) + 2) hm 1 one_pos
  exact eq_static_clt_of_burn_proof hd hs0 hsd V hV β hβ ρβ hρβ φ hφ
    (HRS.MD.EQBurnZero.eq_burnin_zero_proof hd hs0 hsd V hV β β hβ le_rfl ((d : ℝ) + 2) hm
      K c Cmax hK hc hCmax hevo)

end HRS.MD.EQBurnClt

import HRS.PDE.Convention
import HRS.Kernel.GradD1

/-!
# Torus PDE layer: the kernel inputs of `Convention.lean` for all `d ≥ 1`

Case split `d = 1` (`HRS/Kernel/GradD1.lean`, namespace `HRS.KernelGradD1`) / `d ≥ 2`
(`Convention.lean`, from `HRS/Kernel/GradConv.lean`).  A separate file because `HRS.Kernel.D1`
imports `HRS.PDE.Convention`.
-/

noncomputable section

namespace HRS.PDE

variable {d : ℕ} {s : ℝ}

/-! #### The kernel inputs for all `d ≥ 1` (case split `d = 1` / `d ≥ 2`; `HRS/Kernel/GradD1.lean`) -/

theorem periodicRieszGrad_smoothOffZero_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Torus.IsSmoothOffZero (periodicRieszGrad d s) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · exact KernelGradD1.periodicRieszGrad_smoothOffZero (by omega) hs0 hsd
  · exact periodicRieszGrad_smoothOffZero h hs0 hsd

theorem periodicRieszGrad_bound_tdist_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ C * (Torus.tdist z 0 ^ (-s - 1) + 1) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · exact KernelGradD1.periodicRieszGrad_bound_tdist (by omega) hs0 hsd
  · exact periodicRieszGrad_bound_tdist h hs0 hsd

theorem convGradConv_coeff_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Torus d → ℝ) (hh : Torus.IsCk 1 h) (i : Fin d) :
    coeffOf (fun x => convGradConv (periodicRieszGrad d s) h x i) =
      gradRieszCoeff d s i (coeffOf h) := by
  rcases Nat.lt_or_ge d 2 with h' | h'
  · exact KernelGradD1.convGradConv_coeff (by omega) hs0 hsd h hh i
  · exact convGradConv_coeff h' hs0 hsd h hh i

theorem convGradConv_continuous_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Torus d → ℝ) (hh : Torus.IsCk 1 h) : Continuous (convGradConv (periodicRieszGrad d s) h) := by
  rcases Nat.lt_or_ge d 2 with h' | h'
  · exact KernelGradD1.convGradConv_continuous (by omega) hs0 hsd h hh
  · exact convGradConv_continuous h' hs0 hsd h hh

theorem convGradConv_cbNorm_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C : ℝ, ∀ h : Torus d → ℝ, Torus.IsCk (m + 1) h →
      Torus.IsCk m (convGradConv (periodicRieszGrad d s) h) ∧
        Torus.cbNorm m (convGradConv (periodicRieszGrad d s) h) ≤ C * Torus.cbNorm (m + 1) h := by
  rcases Nat.lt_or_ge d 2 with h' | h'
  · exact KernelGradD1.convGradConv_cbNorm (by omega) hs0 hsd m
  · exact convGradConv_cbNorm h' hs0 hsd m


end HRS.PDE

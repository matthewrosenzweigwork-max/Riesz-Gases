import HRS.Whole.AppendixAAdjoint
import HRS.MS.CzPvkAux1
import HRS.MS.CzPvkAux2
import HRS.MS.CzPvkAux3

/-!
# PV-KERNEL tie: frozen `IsOddSmooth` / `pvOdd` versus the abstract kernel development

* `pvk_kernel_of_isOddSmooth`: a frozen `IsOddSmooth Ω` (`HRS/Whole/AppendixAAdjoint.lean`, `ContDiff ℝ ∞ Ω`, odd on
  the unit sphere) gives a kernel `K = pvkOmegaK d Ω` satisfying the hypotheses `PvkKernel` of `kernel_decomp`.
* `pvOdd_one_eq_limUnder_Ktr`: the frozen `pvOdd d 1 Ω u x` is the `limUnder` of the truncated singular integrals
  `∫ pvkKtr K ε z * u (x - z) dz` (the form to which `kernel_decomp` applies).
-/

open MeasureTheory Filter
open scoped Topology
open HRS.Whole.AppendixA

namespace HRS.CZ.Pvk

theorem pvk_kernel_of_isOddSmooth {d : ℕ} (hd : 1 ≤ d) {Ω : Euc d → ℝ} (hΩ : IsOddSmooth Ω) :
    ∃ L : ℝ, PvkKernel d (pvkOmegaK d Ω) L :=
  pvkKernel_of_contDiff hd (hΩ.1.of_le (by exact_mod_cast le_top)) hΩ.2

theorem pvOdd_one_eq_limUnder_Ktr {d : ℕ} (Ω : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) :
    pvOdd d 1 Ω u x =
      limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ => ∫ z, pvkKtr (pvkOmegaK d Ω) ε z * u (x - z) := by
  unfold pvOdd
  congr 1
  funext ε
  rw [← pvk_setIntegral_eq_Ktr (K := pvkOmegaK d Ω)]
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm) fun z _ => ?_
  simp only [pvkOmegaK_eq_rpow]

end HRS.CZ.Pvk

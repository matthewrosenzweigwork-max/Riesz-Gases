import HRS.MS.S111X1Aux4
import HRS.MS.S111BDAux5
import HRS.MS.GapRefAux1
import HRS.MS.MovOpAux1
import HRS.MS.TransOpAux26

/-!
# S11.1 X1, part 5: the analytic input and the osc-test submodule
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- The oscillator test functions as a submodule. -/
def oscSub (d : ℕ) (m : ℝ) : Submodule ℝ (Euc d → ℝ) where
  carrier := {φ | IsOscTest m φ}
  add_mem' := fun {_ _} ha hb =>
    ⟨ha.1.add hb.1, (HRS.MS.MovC1.movc1_osc_add m ha.2 hb.2).1⟩
  zero_mem' := ⟨contDiff_const, HRS.MS.TransOp.s611_memOsc_zero m⟩
  smul_mem' := fun c _ hx =>
    ⟨hx.1.const_smul c, (HRS.MS.MovC1.movc1_osc_smul m c hx.2).1⟩

theorem mem_oscSub {m : ℝ} {φ : Euc d → ℝ} : φ ∈ oscSub d m ↔ IsOscTest m φ := Iff.rfl

/-- osc tests are in `L²(ρ dx)` when `ρ` is bounded -/
theorem x1_osc_memLp {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) {m : ℝ} {ψ : Euc d → ℝ} (hψ : IsOscTest m ψ) :
    MemLp ψ 2 (HRS.Whole.withDensityReal ρ) := by
  refine MemLp.of_measure_le_smul (c := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_ hψ.2.1
  unfold HRS.Whole.withDensityReal
  rw [Measure.le_iff]
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hM x)

end HRS.MS.S111X1

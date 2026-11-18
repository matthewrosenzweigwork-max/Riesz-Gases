import HRS.Commutator.Torus.TEXTAux19
import HRS.Energy.Commutator.EnergyAux
import HRS.Commutator.Whole.LocalAuxSAMP1

/-!
# T-SAMP helpers, part 1: elementary torus facts, Young's inequality, reduction of the transport data
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-! ### `tdist` -/

lemma tsamp_tdist_sub_sub (x y z : Torus d) :
    KernelGrad.tdist (x - z) (y - z) = KernelGrad.tdist x y := by
  rw [KernelGrad.tdist_eq_sub_zero (x - z) (y - z), KernelGrad.tdist_eq_sub_zero x y,
    sub_sub_sub_cancel_right]

lemma tsamp_tdist_triangle (x y z : Torus d) :
    KernelGrad.tdist x z ≤ KernelGrad.tdist x y + KernelGrad.tdist y z := by
  rw [KernelGrad.tdist_eq_sub_zero x z, KernelGrad.tdist_eq_sub_zero x y,
    KernelGrad.tdist_eq_sub_zero y z]
  have := EnergyAux.tdist_add_le (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

lemma tsamp_tdist_symm (x y : Torus d) : KernelGrad.tdist x y = KernelGrad.tdist y x :=
  KernelGrad.tdist_sub_comm x y

lemma tsamp_measurable_tdist (a : Torus d) : Measurable fun x : Torus d => KernelGrad.tdist x a :=
  (CoercAux.continuous_tdist_left a).measurable

/-! ### Young's inequality on the torus (`ℝ≥0∞` form) -/

lemma tsamp_young_enn {k f : Torus d → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f) {p : ℝ}
    (hp : 1 < p) (hA : ∫⁻ y, k y ≠ ⊤) :
    ∫⁻ x, (∫⁻ y, k (x - y) * f y) ^ p ≤ (∫⁻ y, k y) ^ p * ∫⁻ x, f x ^ p := by
  have h := Whole.SAMP1.young_lintegral (volume : Measure (Torus d)) hk hf hp hA
  have e : ∀ x, ∫⁻ y, k (x - y) * f y = ∫⁻ y, k y * f (x - y) := by
    intro x
    rw [← lintegral_sub_left_eq_self (fun y => k (x - y) * f y) (μ := volume) x]
    refine lintegral_congr fun y => ?_
    simp
  simp_rw [e]
  exact h

end HRS.Commutator.TorusNote

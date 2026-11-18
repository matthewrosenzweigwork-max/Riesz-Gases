import HRS.MS.S82WR1

/-!
# S8.2 A05 (S82W), part 9: transfer of `GeneratorClosure` along an a.e. equal generator, gradient of a shifted function
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

section transfer
variable {d N : ℕ}

lemma w_closure_congr {a beta : ℝ} {F LF LF' : EucConfig d N → ℝ}
    (h : GeneratorClosure a beta F LF) (hae : LF =ᵐ[canonicalP d N a beta] LF') :
    GeneratorClosure a beta F LF' := by
  obtain ⟨h1, h2, h3, Fn, hFn, hT0, hT2, hT1⟩ := h
  refine ⟨h1, h2.ae_eq hae, h3, Fn, hFn, hT0, ?_, hT1⟩
  obtain ⟨hm, hl⟩ := hT2
  refine ⟨hm.congr hae, ?_⟩
  refine hl.congr fun n => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with X hX
  rw [hX]

lemma w_configGrad_shift (φ : EucConfig d N → ℝ) (c : ℝ) (X : EucConfig d N) (i : Fin N) :
    Phase2S82.configGrad (fun Y => φ Y - c) X i = Phase2S82.configGrad φ X i := by
  unfold Phase2S82.configGrad gradient
  have : fderiv ℝ (fun y => φ (Function.update X i y) - c) = fderiv ℝ (fun y => φ (Function.update X i y)) :=
    funext fun y => fderiv_sub_const _
  rw [this]

end transfer

end HRS.MS.S82W

import HRS.Sections.Q66AuxF
import HRS.Kernel.GradConv

/-!
# Packet Q66: `∂_i (g * h) = (∂_i g) * h` for `C¹` `h` and `s < d - 1` (plain integral)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.Q66

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ}

theorem q66_gradKernel_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) - 1) :
    Integrable (periodicRieszGrad d s : Torus d → Euc d) := by
  obtain ⟨C, hG⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 (by linarith)
  exact hG.integrable_G (by linarith)

theorem q66_grad_conv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) - 1) {h : Torus d → ℝ}
    (hh : Torus.IsCk 1 h) (i : Fin d) (x : Torus d) :
    ∫ y, h y * (periodicRieszGrad d s (x - y)) i =
      Torus.partialDeriv i (convFun (periodicRiesz d s) h) x := by
  have hsd : s < d := by linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have hhc : Continuous h := Torus.continuous_of_continuous_lift hh.continuous
  obtain ⟨B, hB⟩ := exists_bound_of_cont hhc
  have hconv : Torus.IsCk 1 (convFun (periodicRiesz d s) h) := convFun_isCk_one F.integrable hh
  -- the two continuous functions have the same Fourier coefficients
  have hA : Continuous (fun x => HRS.convGradConv (periodicRieszGrad d s) h x i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
      (HRS.PDE.convGradConv_continuous hd hs0 hsd h hh)
  have hBc : Continuous (Torus.partialDeriv i (convFun (periodicRiesz d s) h)) :=
    continuous_partialDeriv i _ hconv
  have hcoef : ∀ k, coeffOf (fun x => HRS.convGradConv (periodicRieszGrad d s) h x i) k =
      coeffOf (Torus.partialDeriv i (convFun (periodicRiesz d s) h)) k := by
    intro k
    rw [HRS.PDE.convGradConv_coeff hd hs0 hsd h hh i, coeffOf_partialDeriv i _ hconv]
    unfold gradRieszCoeff derivCoeff rieszMult
    rw [HRS.PDE.MFAux.coeffOf_convFun hd s hs0 hsd hhc k]
  have heq : (fun x => HRS.convGradConv (periodicRieszGrad d s) h x i) =
      Torus.partialDeriv i (convFun (periodicRiesz d s) h) :=
    MFAux.eq_of_funFourierCoeff_eq hA hBc hcoef
  have hplain := HRS.PDE.convGradConv_eq_plain hd hs0 hs h hhc.measurable ⟨B, hB⟩ x
  have hint : Integrable (fun y => h y • periodicRieszGrad d s (x - y)) := by
    have h1 : Integrable (fun y => periodicRieszGrad d s (x - y)) :=
      (q66_gradKernel_integrable hd hs0 hs).comp_sub_left x
    exact h1.bdd_smul B hhc.aestronglyMeasurable (Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hB y)
  have hcomp : (HRS.convGradConv (periodicRieszGrad d s) h x) i =
      ∫ y, h y * (periodicRieszGrad d s (x - y)) i := by
    rw [hplain]
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
    simpa using this.symm
  rw [← hcomp]
  exact congrFun heq x

end HRS.Q66

end

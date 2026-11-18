import HRS.Sections.Q66AuxK

/-!
# Packet Q66: the transport kernel `h_v` and the identity for the exponent drift

`h_v(x,y) = (v(x) - v(y))·∇g(x-y)` and, for `∑_k ∂_k(ρ v_k) = -ρ r`,
`∑_{i,k} v_k(x_i) B_{ik}(X) = N F_N^{h_v}(X,μ) - (N/2) ∬ h_v dμ dμ + ∑_i (g*(ρ r))(x_i)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The pair kernel `h_v(x,y) = (v(x) - v(y))·∇g(x-y)` of the transport field `v`. -/
def q66_hv (d : ℕ) (s : ℝ) (v : Fin d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  ∑ k, (v k x - v k y) * (periodicRieszGrad d s (x - y)) k

theorem q66_gradKernel_odd (hsd : s < d) (z : Torus d) (k : Fin d) :
    (periodicRieszGrad d s (-z)) k = -(periodicRieszGrad d s z) k := by
  rw [HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]; simp

theorem q66_hv_symm (hsd : s < d) (v : Fin d → Torus d → ℝ) (x y : Torus d) :
    q66_hv d s v x y = q66_hv d s v y x := by
  unfold q66_hv
  refine Finset.sum_congr rfl fun k _ => ?_
  have : y - x = -(x - y) := by abel
  rw [this, q66_gradKernel_odd hsd]
  ring

theorem q66_hv_measurable (hsd : s < d) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Continuous (v j)) :
    Measurable (Function.uncurry (q66_hv d s v)) := by
  unfold q66_hv
  have hgm : Measurable (periodicRieszGrad d s : Torus d → Euc d) :=
    HRS.KernelGrad.measurable_periodicRieszGrad hsd
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.mul (Measurable.sub ?_ ?_) ?_
  · exact (hv k).measurable.comp measurable_fst
  · exact (hv k).measurable.comp measurable_snd
  · exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous.measurable).comp
      (hgm.comp (measurable_fst.sub measurable_snd))

/-- `∇(-g*ρ)` componentwise. -/
theorem q66_grad_Vrho (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (x : Torus d) (k : Fin d) :
    (Torus.grad (q66_Vrho d s ρ) x) k = -∫ y, ρ y * (periodicRieszGrad d s (x - y)) k := by
  have hsd : s < d := by linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have h1 : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ) :=
    convFun_isCk_one F.integrable (q66_isCk_of_smooth hρ.smooth 1)
  rw [grad_apply, q66_grad_conv hd hs0 hs1 (q66_isCk_of_smooth hρ.smooth 1) k x]
  unfold Torus.partialDeriv q66_Vrho
  have e : Torus.lift (fun x => -convFun (periodicRiesz d s) ρ x) =
      fun y => -(Torus.lift (convFun (periodicRiesz d s) ρ)) y := rfl
  rw [e, fderiv_fun_neg]
  simp

end HRS.Q66

end

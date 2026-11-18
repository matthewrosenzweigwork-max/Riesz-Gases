import HRS.Sections.Q66AuxI

/-!
# Packet Q66: Stein identity under `Q_{N,β}(μ)`, part 3 (the raw identity)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q66_scalar_line_deriv {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (x : Torus d) (k : Fin d) :
    HasDerivAt (fun τ : ℝ => f (x + Torus.mk (τ • ek k))) (Torus.partialDeriv k f x) 0 := by
  have hVd : DifferentiableAt ℝ (fun u : Euc d => f (x + Torus.mk u)) 0 := by
    rw [q84d_slice_eq]
    have hc : ContDiff ℝ 1 (Torus.lift f) := hf
    exact ((hc.differentiable one_ne_zero) _).comp 0 (differentiableAt_id.const_add _)
  have h1 : HasDerivAt (fun τ : ℝ => τ • ek k) (ek k) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (ek k)
  have hF0 : HasFDerivAt (fun u : Euc d => f (x + Torus.mk u))
      (fderiv ℝ (fun u : Euc d => f (x + Torus.mk u)) 0) ((fun τ : ℝ => τ • ek k) 0) := by
    simpa using hVd.hasFDerivAt
  have h2 := hF0.comp_hasDerivAt (0 : ℝ) h1
  have e : (fun τ : ℝ => f (x + Torus.mk (τ • ek k))) =
      (fun u : Euc d => f (x + Torus.mk u)) ∘ fun τ : ℝ => τ • ek k := by
    funext τ; simp
  rw [e]
  convert h2 using 1
  rw [q84d_slice_grad_comp, grad_apply]

theorem q66_Bik_measurable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {V : Torus d → ℝ}
    (hV : Torus.IsCk 1 V) (i : Fin N) (k : Fin d) : Measurable (Bik d s V i k) := by
  have hVc : Continuous (Torus.partialDeriv k V) := continuous_partialDeriv k V hV
  have hgm : Measurable (periodicRieszGrad d s : Torus d → Euc d) :=
    HRS.KernelGrad.measurable_periodicRieszGrad hsd
  unfold Bik
  refine Measurable.add ?_ ?_
  · have : (fun Y : Config d N => (Torus.grad V (Y i)) k) = fun Y => Torus.partialDeriv k V (Y i) := by
      funext Y; rw [grad_apply]
    rw [this]
    exact hVc.measurable.comp (measurable_pi_apply i)
  · refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous.measurable).comp
      (hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j)))

theorem q66_Bik_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) - 1) {V : Torus d → ℝ}
    (hV : Torus.IsCk 1 V) (i : Fin N) (k : Fin d) :
    Integrable (Bik d s V i k) (volume : Measure (Config d N)) := by
  have hsd : s < d := by linarith
  have hVc : Continuous (Torus.partialDeriv k V) := continuous_partialDeriv k V hV
  have hG : Integrable (fun z : Torus d => (periodicRieszGrad d s z) k) := by
    have := (q66_gradKernel_integrable hd hs0 hs)
    exact ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).integrable_comp this)
  have hGp : Integrable (fun p : Torus d × Torus d => (periodicRieszGrad d s (p.1 - p.2)) k)
      (volume : Measure (Torus d × Torus d)) := by
    have h1 : Integrable (fun _ : Torus d => (1 : ℝ)) := integrable_const _
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) h1 hG
    rw [← Measure.volume_eq_prod] at this
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp
  unfold Bik
  refine Integrable.add ?_ ?_
  · have : (fun Y : Config d N => (Torus.grad V (Y i)) k) = fun Y => Torus.partialDeriv k V (Y i) := by
      funext Y; rw [grad_apply]
    rw [this]
    exact (hVc.comp (continuous_apply i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · refine Integrable.const_mul (integrable_finsetSum _ fun j hj => ?_) _
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have := integrable_pair_comp (volume : Measure (Torus d)) hij
      (H := fun p : Torus d × Torus d => (periodicRieszGrad d s (p.1 - p.2)) k) (by
        rw [← Measure.volume_eq_prod]; exact hGp)
    exact this

end HRS.Q66

end

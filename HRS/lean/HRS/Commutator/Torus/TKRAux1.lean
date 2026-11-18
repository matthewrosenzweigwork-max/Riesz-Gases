import HRS.Commutator.Torus.TPOSAux4
import HRS.Kernel.HigherDerivBounds
import HRS.Commutator.Whole.LocalAuxFC

/-!
# T-KR helpers, part 1: Fourier coefficients of the components of `∇g`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

/-- The Fourier coefficient of the `i`-th component of `∇g`: `2πi k_i ĝ(k)`. -/
lemma tkr_fcoef_G (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) (k : Lattice d) (i : Fin d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((periodicRieszGrad d s x i : ℝ) : ℂ) =
      (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ) := by
  obtain ⟨C0, hC0, hGε⟩ := goodKernel_heat hd hs0 (by linarith : s < d)
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  have hbd : Integrable (fun x : Torus d => C0 * (‖x‖ ^ (-(s + 1)) + 1)) :=
    ((integrable_norm_rpow_neg (by omega : 0 < d) hsd1).add (integrable_const (1 : ℝ))).const_mul C0
  have hLHS : Tendsto (fun ε : ℝ => ∫ x : Torus d, Torus.mode (-k) x *
      ((heatRieszGrad d s ε x i : ℝ) : ℂ)) l
      (𝓝 (∫ x : Torus d, Torus.mode (-k) x * ((periodicRieszGrad d s x i : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x : Torus d => C0 * (‖x‖ ^ (-(s + 1)) + 1)) ?_ ?_ hbd ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hc : Continuous fun x : Torus d => Torus.mode (-k) x *
          ((heatRieszGrad d s ε x i : ℝ) : ℂ) :=
        (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp (continuous_heatRieszGrad
            (by linarith : s < d) hε)))
      exact hc.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [torus_ae_ne' (by omega : 0 < d)] with x hx
      rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := (hGε ε hε).bound_norm x hx
      have h2 := PiLp.norm_apply_le (heatRieszGrad d s ε x) i
      rw [Real.norm_eq_abs] at h2
      rw [show -s - 1 = -(s + 1) by ring] at h1
      exact h2.trans h1
    · refine Eventually.of_forall fun x => ?_
      have h := heat_tendsto (by linarith : s < d) x
      have h2 := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp h
      exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h2)
  set R : ℝ → ℂ := fun ε => (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
      ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) with hR
  have hRc : Continuous R := by
    simp only [hR]
    fun_prop
  have hRHS : Tendsto R l (𝓝 ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
      ((rieszCoeff d s k : ℝ) : ℂ))) := by
    have := (hRc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hR] using this
  have hEq : (fun ε : ℝ => ∫ x : Torus d, Torus.mode (-k) x *
      ((heatRieszGrad d s ε x i : ℝ) : ℂ)) =ᶠ[l] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_mode_heat_component (by linarith : s < d) hε k i
  exact tendsto_nhds_unique (hLHS.congr' hEq) hRHS

end HRS.Commutator.TorusNote

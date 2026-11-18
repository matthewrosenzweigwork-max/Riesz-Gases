import HRS.MS.S113EndAux20
import HRS.MS.S113EndAux12

/-!
# S11.3 endpoint (worker S11X), part 21: the almost-everywhere time derivative of `log K_{N,β}(μ^t)`

From `SbLogK` (S.B.1 F3, `sb1_logK_main`): `log K_t - log K_0 = βN ∫_0^t E_{Q_r}[F^{h_{u_r}}] dr`, hence for almost every `t`
`d/dt log K_t = βN E_{Q_t}[F^{h_{u_t}}]` (`s113x_logK_deriv_ae`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d : ℕ}

/-- `E_{Q_N^t}[F_N^{h_{u^t}}]`. -/
def s113x_EQ (d : ℕ) (s q β : ℝ) (ρ : ℝ → Euc d → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∫ Y, pairEnergy (commutatorKernel d s (movU d s q β (ρ t))) Y (HRS.Whole.withDensityReal (ρ t))
    ∂(s113x_Q d s β ρ N t)

theorem s113x_mfeTransport_eq (s q β : ℝ) (f : Euc d → ℝ) :
    mfeTransportW (quadraticGradientDyn d s q β) f = movU d s q β f := by
  funext x
  unfold mfeTransportW mfeTransport0W movU quadraticGradientDyn
  simp only [movtr_gradient_confinement]
  unfold movForce
  abel

theorem s113x_sb1EQ_eq {s q β : ℝ} (hβ : β ≠ 0) (ρ : ℝ → Euc d → ℝ) (N : ℕ) (t : ℝ) :
    MfeConf.sb1EQ (quadraticGradientDyn d s q β) N ρ t = s113x_EQ d s q β ρ N t := by
  unfold MfeConf.sb1EQ MfeConf.sb1CN MfeConf.sb1Q s113x_EQ s113x_Q
  simp only [s113x_mfeTransport_eq]
  have e : (quadraticGradientDyn d s q β).invβ⁻¹ = β := by simp [quadraticGradientDyn]
  rw [e]
  rfl

theorem s113x_logK_deriv_ae {s q β : ℝ} (hβ : β ≠ 0) {ρ : ℝ → Euc d → ℝ} {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hK : MfeConf.SbLogK (quadraticGradientDyn d s q β) N T ρ) :
    ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 T →
      HasDerivAt (fun τ => Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ))))
        (β * N * s113x_EQ d s q β ρ N t) t := by
  obtain ⟨hint, heq⟩ := hK
  have hint' : IntegrableOn (s113x_EQ d s q β ρ N) (Set.Icc 0 T) := by
    refine hint.congr_fun (fun t _ => s113x_sb1EQ_eq hβ ρ N t) measurableSet_Icc
  have hLT : IntervalIntegrable (s113x_EQ d s q β ρ N) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hint'.mono_set Set.Ioc_subset_Icc_self
  have heq' : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ))) =
        Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ 0))) +
          β * N * ∫ r in (0 : ℝ)..τ, s113x_EQ d s q β ρ N r := by
    intro τ hτ
    have h1 := heq τ hτ
    have e : (quadraticGradientDyn d s q β).invβ⁻¹ = β := by simp [quadraticGradientDyn]
    have es : (quadraticGradientDyn d s q β).s = s := rfl
    rw [e, es] at h1
    have h2 : ∫ r in Set.Icc (0 : ℝ) τ, MfeConf.sb1EQ (quadraticGradientDyn d s q β) N ρ r =
        ∫ r in (0 : ℝ)..τ, s113x_EQ d s q β ρ N r := by
      rw [← s113x_Icc_eq_interval _ hτ.1]
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      exact s113x_sb1EQ_eq hβ ρ N r
    rw [h2] at h1
    linarith
  filter_upwards [hLT.ae_hasDerivAt_integral] with t hLt ht
  have hJ : HasDerivAt (fun x => ∫ v in (0 : ℝ)..x, s113x_EQ d s q β ρ N v) (s113x_EQ d s q β ρ N t) t :=
    hLt (by rw [Set.uIcc_of_le hT]; exact ⟨ht.1.le, ht.2.le⟩) 0 (by simp [hT])
  have h3 := (hJ.const_mul (β * N)).const_add
    (Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ 0))))
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  exact heq' τ hτ

end HRS.MS.S113BD

end

import HRS.MS.S111X2Aux17

/-!
# S11.1 X2, packet E03: assembled statement

For classical adjoint solutions `f, h` on `[0,H]` of the thermal model, `E(r) = C_β(f_r, h_r)` is absolutely
continuous with `E' = 2 β⁻¹ D(f_r,h_r)` on `(0,H)`, `D` is integrable on `[0,H]`, and
`E v - E r = 2 β⁻¹ ∫_{[r,v]} D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- **E03.** Classical fluctuation-dissipation (backward time has the plus sign). -/
theorem s111x2_classical_fd (hd : 2 ≤ d) {s a β H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hH : 0 < H) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    {φ ψ : Euc d → ℝ} {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f)
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H ψ h) :
    AbsolutelyContinuousOnInterval (fun r => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal ρ) β (f r) (h r)) 0 H ∧
      (∀ r ∈ Ioo 0 H, HasDerivAt (fun q => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal ρ) β (f q) (h q))
        (2 * β⁻¹ * s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (f r) (h r)) r) ∧
      IntegrableOn (fun r => s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (f r) (h r)) (Icc 0 H) ∧
      ∀ r v : ℝ, 0 ≤ r → r ≤ v → v ≤ H →
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (f v) (h v) -
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (f r) (h r) =
        2 * β⁻¹ * ∫ t in Icc r v, s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (f t) (h t) := by
  obtain ⟨hder, hcont⟩ := s111x2_classical_fd_deriv hd hs0 hs ha hβ hH hρ hf hh
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  obtain ⟨Bh0, Bh1, Bh2, hBh0, hBh1, hBh2, hhB⟩ := HRS.MS.S111X1.classical_bounds hh
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set E : ℝ → ℝ := fun r => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ β (f r) (h r) with hE
  set D : ℝ → ℝ := fun r => s111x2_dirichlet μ (f r) (h r) with hD
  have hDb : ∀ r ∈ Icc (0 : ℝ) H, |D r| ≤ Bf1 * Bh1 := fun r hr =>
    s111x2_dirichlet_bound T (fun x => (hfB r hr x).2.1) (fun x => (hhB r hr x).2.1)
  have hβ2 : 0 < 2 * β⁻¹ := by positivity
  have hbd : ∀ r ∈ Ioo (0 : ℝ) H, |2 * β⁻¹ * D r| ≤ 2 * β⁻¹ * (Bf1 * Bh1) := fun r hr => by
    rw [abs_mul, abs_of_pos hβ2]
    exact mul_le_mul_of_nonneg_left (hDb r ⟨hr.1.le, hr.2.le⟩) hβ2.le
  have hAC := s111x2_ac_of_deriv_bdd hH hcont hder hbd
  refine ⟨hAC, hder, ?_, ?_⟩
  · -- integrability of D
    have hae : ∀ᵐ t ∂(volume.restrict (Icc 0 H)), D t = (2 * β⁻¹)⁻¹ * deriv E t :=
      s111x2_ae_icc_of_ioo fun r hr => by
        rw [(hder r hr).deriv]; field_simp; rfl
    have hmeas : AEStronglyMeasurable D (volume.restrict (Icc 0 H)) := by
      have : AEStronglyMeasurable (fun t => (2 * β⁻¹)⁻¹ * deriv E t) (volume.restrict (Icc 0 H)) :=
        ((measurable_deriv E).const_mul _).aestronglyMeasurable
      exact this.congr (hae.mono fun t ht => ht.symm)
    refine (integrableOn_const (C := Bf1 * Bh1) (by simp)).mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact hDb t ht
  · intro r v hr hrv hv
    have hd' : ∀ᵐ t ∂(volume.restrict (Icc 0 H)), HasDerivAt E (2 * β⁻¹ * D t) t :=
      s111x2_ae_icc_of_ioo fun t ht => hder t ht
    have := s111x2_integral_deriv hAC hd' hr hrv hv
    rw [intervalIntegral.integral_of_le hrv, ← integral_Icc_eq_integral_Ioc, integral_const_mul] at this
    exact this.symm

end HRS.MS.S111X2

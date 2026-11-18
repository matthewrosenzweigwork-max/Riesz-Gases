import HRS.MS.S111X2Aux11

/-!
# S11.1 X2, packet E02: assembled statement for `C_b^k` data on the thermal reference
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS HRS.Whole
open HRS.Whole.Q34 (isProbabilityMeasure_nu)

variable {d : ℕ}

theorem s111x2_cbD_of_memCb2 {h : Euc d → ℝ} (H : MemCb 2 h) : ∃ B1 B2 : ℝ, CbD h B1 B2 := by
  obtain ⟨hc, hb⟩ := H
  obtain ⟨B1, h1⟩ := hb 1 (by norm_num)
  obtain ⟨B2, h2⟩ := hb 2 le_rfl
  refine ⟨B1, B2, hc, fun x => ?_, fun x => ?_⟩
  · have := h1 ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_one] at this
    exact this
  · have := h2 ⟨x, rfl⟩
    simp only at this
    have e1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := h) (x := x) (n := 1)
    rw [norm_iteratedFDeriv_one] at e1
    rw [e1]
    exact this

theorem s111x2_cb1_bounds {f : Euc d → ℝ} (H : MemCb 1 f) :
    ContDiff ℝ 1 f ∧ ∃ B0 B1 : ℝ, (∀ x, ‖f x‖ ≤ B0) ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ B1 := by
  obtain ⟨hc, hb⟩ := H
  obtain ⟨B0, h0⟩ := hb 0 (by norm_num)
  obtain ⟨B1, h1⟩ := hb 1 le_rfl
  refine ⟨hc, B0, B1, fun x => ?_, fun x => ?_⟩
  · have := h0 ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_zero] at this
    exact this
  · have := h1 ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_one] at this
    exact this

/-- **E02.** `R_β P_μ G h = -β⁻¹ L h` with the physical factor `β⁻¹`, and `C_β(f, G h) = -β⁻¹ D(f,h)`. -/
theorem s111x2_response_generator (hd : 2 ≤ d)
    (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    (f h : Euc d → ℝ) (hf : MemCb 1 f) (hh : MemCb 2 h) :
    MemL2Zero (HRS.Whole.withDensityReal ρ) (s111x2_L ρ h) ∧
      MemLp (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 h) 2
        (HRS.Whole.withDensityReal ρ) ∧
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
        (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 h)
        (fun x => -β⁻¹ * s111x2_L ρ h x) ∧
      Integrable (fun x => inner ℝ (gradient f x) (gradient h x)) (HRS.Whole.withDensityReal ρ) ∧
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f
        (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 h) =
        -β⁻¹ * s111x2_dirichlet (HRS.Whole.withDensityReal ρ) f h := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨B1, B2, H⟩ := s111x2_cbD_of_memCb2 hh
  obtain ⟨hfc, B0, Bf, h0, h1⟩ := s111x2_cb1_bounds hf
  exact ⟨s111x2_L_memL2Zero T H, s111x2_gen_memLp T H, s111x2_isResponse_gen T H,
    s111x2_dirichlet_integrable T H hfc h1, s111x2_susc_gen T H hfc h0 h1⟩

end HRS.MS.S111X2

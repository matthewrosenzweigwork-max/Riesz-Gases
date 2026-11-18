import HRS.MS.Fp81S21CovRS10
import HRS.MS.Fp81S21RSValue5

/-!
# HRS S2.1(iii), packet 19d: finite-projection endpoint integrability

The partition expectation argument needs the two endpoint random variables to
be separately integrable before their integrals can be subtracted.  This file
proves that fact from the selected probability-valued heat future and the
measurable prediction version supplied by packets 19b/19c.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Every finite-projection moving heat endpoint is integrable.  The actual
endpoint uses `s102_Y`; the measurable version `Yh` agrees with it almost
everywhere simultaneously on the full horizon. -/
theorem fp81s21_moving_heat_ito_endpoint_integrable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℕ) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hYae : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) (a + p.T),
      Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (a + p.T) A.P A.X ω t)
    (t : ℝ) (ht0 : 0 ≤ t) (htH : t ≤ a + p.T) :
    Integrable
      (fun ω => fp81s21_moving_heat_ito_endpoint
        p R A a ha hH future L Φ t ω) A.P := by
  classical
  let H : ℝ := a + p.T
  let B_H := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  let Pj : B_H →L[ℝ] B_H := s102_Pj H hH L
  let W : B_H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let G : B_H → ℝ := fun w => Φ (W (Pj w))
  have hG : MemCb 5 G := by
    dsimp [G]
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof
      (W.comp Pj) hΦ).1
  have hp := hfuture.2.2.2 H hH
  have hheat := hp.2.2.2.2 G hG t
  let f : A.Ω → ℝ := fun ω =>
    r2HeatFn (future H) G t (Yh ω t)
  have hfMeas : Measurable f := by
    exact hheat.1.continuous.measurable.comp (hYm t)
  have hGbound : ∀ z : B_H, ‖G z‖ ≤ cbNorm 5 G := by
    intro z
    have hz := HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hG
      (i := 0) (by norm_num) z
    simpa [iteratedFDeriv_zero_apply] using hz
  have hfBound : ∀ ω, ‖f ω‖ ≤ cbNorm 5 G := by
    intro ω
    letI : IsProbabilityMeasure (future H t) := hfuture.1 H t
    have hi := norm_integral_le_of_norm_le_const
      (μ := future H t) (f := fun z : B_H => G (Yh ω t + z))
      (C := cbNorm 5 G)
      (Filter.Eventually.of_forall fun z => hGbound (Yh ω t + z))
    have hprob : IsProbabilityMeasure (future H t) := inferInstance
    simpa [f, r2HeatFn, hprob.measure_univ] using hi
  have hfInt : Integrable f A.P :=
    Integrable.of_bound hfMeas.aestronglyMeasurable (cbNorm 5 G)
      (Filter.Eventually.of_forall hfBound)
  have hpoint :
      (fun ω => fp81s21_moving_heat_ito_endpoint
        p R A a ha hH future L Φ t ω) =ᵐ[A.P] f := by
    filter_upwards [hYae] with ω hω
    have hωt := hω t ⟨ht0, by simpa [H] using htH⟩
    simp only [f, fp81s21_moving_heat_ito_endpoint]
    simpa [G, W, Pj, H] using congrArg
      (fun y : B_H => r2HeatFn (future H)
        (fun w => Φ (W (Pj w))) t y) hωt.symm
  exact hfInt.congr hpoint.symm

#print axioms HRS.Fp81.S21.fp81s21_moving_heat_ito_endpoint_integrable

end HRS.Fp81.S21

end

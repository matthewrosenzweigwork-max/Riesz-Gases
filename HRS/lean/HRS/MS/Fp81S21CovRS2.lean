import HRS.MS.Fp81S21CovRS

/-! Measurability and time-continuity for the projective covariance pairing. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- The projective covariance pairing depends continuously, in operator norm,
on its bilinear form. -/
theorem fp81s21_covariance_pairingCLM_continuous
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] :
    Continuous (fun Q : B [×2]→L[ℝ] ℝ => fp81s21_covariance_pairingCLM Q) := by
  have hev : Continuous (fun Q : B [×2]→L[ℝ] ℝ =>
      ContinuousLinearMap.apply ℝ ℝ Q) :=
    (ContinuousLinearMap.apply ℝ ℝ).continuous
  simpa [fp81s21_covariance_pairingCLM] using
    hev.clm_comp continuous_const

/-- Scalar increments of the second-derivative pairing are measurable when
the prediction and projective cumulative sections are strongly measurable. -/
theorem fp81s21_covariance_derivative_increment_measurable
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace (projTensor B 2)]
    (u : ℝ → B → ℝ) (Y : Ω → ℝ → B)
    (F : Ω → ℝ → projTensor B 2)
    (hu : ∀ τ, ContDiff ℝ 2 (u τ))
    (hY : ∀ τ, StronglyMeasurable (fun ω => Y ω τ))
    (hF : ∀ t, StronglyMeasurable (fun ω => F ω t)) :
    ∀ τ a b, Measurable (fun ω =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (u τ) (Y ω τ)) (F ω b - F ω a)) := by
  intro τ a b
  have hD : Continuous (iteratedFDeriv ℝ 2 (u τ)) :=
    (hu τ).continuous_iteratedFDeriv (by norm_num)
  have hA : Continuous (fun y : B =>
      fp81s21_covariance_pairingCLM (iteratedFDeriv ℝ 2 (u τ) y)) :=
    (fp81s21_covariance_pairingCLM_continuous.comp hD)
  have hE : Continuous (fun z : B × projTensor B 2 =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (u τ) z.1) z.2) :=
    (hA.comp continuous_fst).clm_apply continuous_snd
  have hinc : StronglyMeasurable (fun ω => F ω b - F ω a) :=
    (hF b).sub (hF a)
  exact (hE.comp_stronglyMeasurable ((hY τ).prodMk hinc)).measurable

/-- Along a continuous prediction, the covariance functional of each
projected heat Hessian is continuous in time on the whole horizon. -/
theorem fp81s21_projected_heat_covariance_pairing_continuousOn
    {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hP : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hLP : S102LipProj γ Pj)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (L : ℕ) (Y : ℝ → OscPath d m H)
    (hY : ContinuousOn Y (Icc 0 H)) :
    ContinuousOn (fun τ => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y τ))) (Icc 0 H) := by
  have hΨP : MemCb 5 (fun w => Ψ (Pj L w)) :=
    (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (Pj L) hΨ).1
  have hheat := (s102_conv_equicont γ hγ Pj hP hconv hLP hΨP Y hY
    2 (by norm_num)).1
  exact (fp81s21_covariance_pairingCLM_continuous.comp_continuousOn hheat)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_covariance_pairingCLM_continuous
#print axioms HRS.Fp81.S21.fp81s21_covariance_derivative_increment_measurable
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_covariance_pairing_continuousOn
end

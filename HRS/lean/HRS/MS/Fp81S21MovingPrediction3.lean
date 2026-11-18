import HRS.MS.Fp81S21MovingPrediction2

/-! A measurable full-horizon version from the moving Itô observations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.FixEq

/-- A measurable version of the moving prediction, continuous on the full horizon. -/
theorem fp81s21_moving_prediction
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    fp81s21_moving_prediction_statement p R hH A := by
  classical
  have hr : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  have hObs : ∀ L : ℕ, ∃ O : ℝ → A.Ω → EuclideanSpace ℝ (Fin (s102_q p.d L)),
      (∀ v, Measurable (O v)) ∧
      ∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) H,
        s102_obs (s102_tauk hH L) (s102_alk L)
          (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω v) = O v ω := by
    intro L
    obtain ⟨bd, Φc, hbd, hΦc, hinit, hform, hnoise, hrep⟩ :=
      fp81s21_moving_itoRep p R hδ hδh hH hN A F hstd hlin hr hphys L
    let O := itoProcess A.P F.ℱ F.Wc
      (fun ω => s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_y0 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P F.X ω)) bd Φc
    refine ⟨O, ?_, ?_⟩
    · intro v
      exact ((adapted_itoProcess _ hinit bd hbd.prog Φc) v).mono (F.ℱ.le v) le_rfl
    · exact hrep
  choose O hOm hOeq using hObs
  let Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d) H :=
    fun ω v => limUnder atTop (fun L => s102_Lam H L (O L v ω))
  have hYm : ∀ v, Measurable (fun ω => Yh ω v) := by
    intro v
    exact (StronglyMeasurable.limUnder (fun L =>
      ((s102_Lam H L : EuclideanSpace ℝ (Fin (s102_q p.d L)) →L[ℝ]
        OscPath p.d (wholeSpaceIndex p.d) H).continuous.measurable.comp (hOm L v)).stronglyMeasurable)).measurable
  have heq : ∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) H,
      Yh ω v = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω v := by
    filter_upwards [ae_all_iff.2 hOeq] with ω hω v hv
    have ht := (s102_projection_strong (d := p.d) (wholeSpaceIndex p.d) H hH).2.1
      (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω v)
    have he : ∀ L : ℕ, s102_Lam H L (O L v ω) =
        s102_Pj H hH L (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω v) := by
      intro L
      rw [s102_Pj_eq_Lam hH L, hω L v hv]
    have ht' : Tendsto (fun L => s102_Lam H L (O L v ω)) atTop
        (𝓝 (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω v)) := by
      simpa only [he] using ht
    exact ht'.limUnder_eq
  refine ⟨Yh, hYm, heq, ?_⟩
  filter_upwards [heq, fp81s21_moving_prediction_continuous p R hδ hδh hH hN A F hstd hlin hphys] with ω he hc
  exact hc.congr (fun v hv => he v hv)

#print axioms HRS.Fp81.S21.fp81s21_moving_prediction
end HRS.Fp81.S21
end

import HRS.MS.Fp81S21DriftCumulative2

/-! Continuity of the physical drift cumulative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The cumulative is norm-continuous, using the scalar integral primitive as
its modulus of continuity. -/
theorem fp81s21_drift_cumulative_continuousOn
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    {Pw : ℝ} {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m H r c)
    (hlin : S102Lin C m H) (hb : S102Drift C m H r Pw b Mb) (hH : 0 ≤ H) :
    ContinuousOn (fun t => r2DriftInc C m H b 0 t) (Icc 0 H) := by
  let F : ℝ → OscPath d m H := fun t => r2DriftInc C m H b 0 t
  let K : ℝ := s102_KV d r Pw c
  have hK : 0 ≤ K := s102_KV_nonneg d r Pw c
  have hinc := (fp81s21_drift_cumulative_variation hP hD hlin hb hH).2.2.1
  have hmono : MonotoneOn (s102_H Mb) (Icc 0 H) := by
    intro x hx y hy hxy
    have hdiff := s102_setIntegral_Mb hx.1 hxy hy.2 hb.Mb_int
    have hnonneg : 0 ≤ ∫ u in Ioc x y, Mb u :=
      setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
    linarith
  have hbound : ∀ x y, x ∈ Icc (0 : ℝ) H → y ∈ Icc (0 : ℝ) H →
      ‖F y - F x‖ ≤ K * |s102_H Mb y - s102_H Mb x| := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.2 (hmono hx hy hxy))]
      rw [show F y - F x = r2DriftInc C m H b x y from hinc x y hx.1 hxy hy.2]
      have h := s102_driftInc_norm_le hP hD hlin hb hH hx.1 hxy hy.2
      rw [s102_setIntegral_Mb hx.1 hxy hy.2 hb.Mb_int] at h
      exact h
    · rw [abs_of_nonpos (sub_nonpos.2 (hmono hy hx hyx)), neg_sub, norm_sub_rev]
      rw [show F x - F y = r2DriftInc C m H b y x from hinc y x hy.1 hyx hx.2]
      have h := s102_driftInc_norm_le hP hD hlin hb hH hy.1 hyx hx.2
      rw [s102_setIntegral_Mb hy.1 hyx hx.2 hb.Mb_int] at h
      exact h
  have hprim := s102_H_continuousOn hH hb.Mb_int
  intro x hx
  have hrhs : ContinuousWithinAt (fun y => K * |s102_H Mb y - s102_H Mb x|)
      (Icc 0 H) x := ((hprim x hx).sub continuousWithinAt_const).abs.const_mul K
  have hlim := hrhs.tendsto
  have hz : K * |s102_H Mb x - s102_H Mb x| = 0 := by simp
  rw [hz] at hlim
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [dist_eq_norm]
  exact hbound x y hx hy

/-- For the actual moving field, the cumulative is continuous on one
full-measure event. -/
theorem fp81s21_moving_drift_cumulative_continuousOn
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∀ᵐ ω ∂A.P, ContinuousOn
      (fun t => r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
        (fun v f => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω f) 0 t) (Icc 0 H) := by
  have hr : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨Mb, hMb, -⟩ := fp81s21_moving_M1 p R hH hN A hstd hr hphys
  filter_upwards [hMb] with ω hω
  exact fp81s21_drift_cumulative_continuousOn hP hstd.hD (fp81s21_S102Lin p R H) hω hH.le

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_drift_cumulative_continuousOn
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_cumulative_continuousOn

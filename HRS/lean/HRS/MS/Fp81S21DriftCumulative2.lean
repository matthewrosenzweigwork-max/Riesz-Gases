import HRS.MS.Fp81S21DriftCumulative

/-! Pathwise drift increments and an integrable variation bound from moving M1. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.FixEq HRS.MS.CovMeas

/-- The deterministic cumulative has the exact interval increments and a
quantitative variation bound. -/
theorem fp81s21_drift_cumulative_variation
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    {Pw : ℝ} {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m H r c)
    (hlin : S102Lin C m H) (hb : S102Drift C m H r Pw b Mb) (hH : 0 ≤ H) :
    let F := fun s => r2DriftInc C m H b 0 s
    F 0 = 0 ∧ BoundedVariationOn F (Icc 0 H) ∧
      (∀ q t, 0 ≤ q → q ≤ t → t ≤ H → F t - F q = r2DriftInc C m H b q t) ∧
      (eVariationOn F (Icc 0 H)).toReal ≤
        s102_KV d r Pw c * ∫ u in Ioc (0 : ℝ) H, Mb u := by
  dsimp only
  have hK : 0 ≤ s102_KV d r Pw c := s102_KV_nonneg d r Pw c
  have hinc : ∀ q t, 0 ≤ q → q ≤ t → t ≤ H →
      r2DriftInc C m H b 0 t - r2DriftInc C m H b 0 q = r2DriftInc C m H b q t := by
    intro q t hq hqt ht
    have hadd := s102_driftInc_add hP hD hlin hb hH (a := 0) (a' := q) (a'' := t) le_rfl hq hqt
    rw [← hadd]
    abel
  let Φ : ℝ → ℝ := fun t => s102_KV d r Pw c * s102_H Mb t
  have hmono : MonotoneOn Φ (Icc 0 H) := by
    intro x hx y hy hxy
    apply mul_le_mul_of_nonneg_left _ hK
    have hdiff := s102_setIntegral_Mb hx.1 hxy hy.2 hb.Mb_int
    have hnonneg : 0 ≤ ∫ u in Ioc x y, Mb u :=
      setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
    linarith
  have hstep : ∀ x y, x ∈ Icc (0 : ℝ) H → y ∈ Icc (0 : ℝ) H → x ≤ y →
      ‖r2DriftInc C m H b 0 y - r2DriftInc C m H b 0 x‖ ≤ Φ y - Φ x := by
    intro x y hx hy hxy
    rw [hinc x y hx.1 hxy hy.2]
    refine (s102_driftInc_norm_le hP hD hlin hb hH hx.1 hxy hy.2).trans ?_
    rw [s102_setIntegral_Mb hx.1 hxy hy.2 hb.Mb_int]
    dsimp [Φ]
    apply le_of_eq
    ring
  have hv := fp81s21_variation_le_of_increment hH _ Φ hmono hstep
  have hΦ : Φ H - Φ 0 = s102_KV d r Pw c * ∫ u in Ioc (0 : ℝ) H, Mb u := by
    rw [s102_setIntegral_Mb le_rfl hH le_rfl hb.Mb_int]
    dsimp [Φ]
    ring
  rw [hΦ] at hv
  have hI : 0 ≤ ∫ u in Ioc (0 : ℝ) H, Mb u :=
    setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
  have hvreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  rw [ENNReal.toReal_ofReal (mul_nonneg hK hI)] at hvreal
  exact ⟨(s102_drift_bv hP hD hlin hb hH).2,
    (s102_drift_bv hP hD hlin hb hH).1, hinc, hvreal⟩

/-- At a fixed positive horizon, M1 supplies an integrable bound and a single
full-measure event for all physical drift intervals. -/
theorem fp81s21_moving_drift_cumulative_variation
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Mb : A.Ω → ℝ → ℝ,
      Integrable (fun ω => s102_KV p.d (2 * p.d + 8) ((p.d : ℝ) + 2) c *
        ∫ u in Ioc (0 : ℝ) H, Mb ω u) A.P ∧
      ∀ᵐ ω ∂A.P,
        let F := fun t => r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fun v f => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω f) 0 t
        F 0 = 0 ∧ BoundedVariationOn F (Icc 0 H) ∧
          (∀ q t, 0 ≤ q → q ≤ t → t ≤ H → F t - F q =
            r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
              (fun v f => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω f) q t) ∧
          (eVariationOn F (Icc 0 H)).toReal ≤
            s102_KV p.d (2 * p.d + 8) ((p.d : ℝ) + 2) c *
              ∫ u in Ioc (0 : ℝ) H, Mb ω u := by
  have hr : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _; linarith
  obtain ⟨Mb, hMb, hInt⟩ := fp81s21_moving_M1 p R hH hN A hstd hr hphys
  refine ⟨Mb, hInt.const_mul _, ?_⟩
  filter_upwards [hMb] with ω hω
  exact fp81s21_drift_cumulative_variation hP hstd.hD (fp81s21_S102Lin p R H) hω hH.le

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_drift_cumulative_variation
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_cumulative_variation

import HRS.MS.Fp81S21DriftCumulative3

/-! Coordinate formula for physical drift increments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Each observation coordinate is the scalar time integral of the actual
drift field; this is the interface needed for path-space measurability. -/
theorem fp81s21_drift_increment_coord
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    {Pw : ℝ} {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m H r c)
    (hlin : S102Lin C m H) (hb : S102Drift C m H r Pw b Mb) (hH : 0 ≤ H)
    {q v t : ℝ} (hq : 0 ≤ q) (hv : 0 ≤ v) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex d) :
    OscDual.coord (r2PathAt (r2DriftInc C m H b q v) t) α =
      ∫ u in Ioc q (min v t), b u (propagatorW C u t (oscTestFun m α)) := by
  rw [s102_driftInc_at hP hD hlin hb hH hq hv ht]
  change s102_coordCLM α (s102_g C m b q v t) = _
  unfold s102_g
  have hs : Ioc q (min v t) ⊆ Icc (0 : ℝ) t := fun u hu =>
    ⟨hq.trans hu.1.le, hu.2.trans (min_le_right _ _)⟩
  have hint := s102_w_integrableOn hP hD hlin hb ht hs measurableSet_Ioc
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have huH : u ∈ Icc (0 : ℝ) H := ⟨hq.trans hu.1.le,
    (hu.2.trans (min_le_right _ _)).trans ht.2⟩
  exact s102_Vprop_coord hP hD (hb.hZ u huH) hlin huH
    ⟨hu.2.trans (min_le_right _ _), ht.2⟩ α

/-- The coordinate formula holds simultaneously at all admissible observation
and cumulative times for the moving physical quadratic field. -/
theorem fp81s21_moving_drift_increment_coord
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∀ᵐ ω ∂A.P, ∀ q v t : ℝ, 0 ≤ q → 0 ≤ v → t ∈ Icc (0 : ℝ) H →
      ∀ α : MultiIndex p.d,
      OscDual.coord (r2PathAt (r2DriftInc (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) H
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q v) t) α =
      ∫ u in Ioc q (min v t), r2QuadField p.s (r26t3_mu R u) A.P A.X u ω
        (propagatorW (r26t3_coeff R) u t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
  have hr : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨Mb, hMb, -⟩ := fp81s21_moving_M1 p R hH hN A hstd hr hphys
  filter_upwards [hMb] with ω hω
  intro q v t hq hv ht α
  exact fp81s21_drift_increment_coord hP hstd.hD (fp81s21_S102Lin p R H) hω hH.le hq hv ht α

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_drift_increment_coord
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_increment_coord

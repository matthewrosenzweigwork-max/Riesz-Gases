import HRS.MS.Fp81S21DriftRS4
import HRS.MS.Fp81S21DriftRS12
import HRS.MS.Fp81S21DriftRS14
import HRS.MS.Fp81S21MovingGram
import HRS.MS.Fp81S21MovingAllInputs

/-! Physical specification of the cylindrical drift RS family. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- One radius and one future yield the physical projected drift RS families,
whose values are the unsigned cylindrical drift integrals. -/
theorem fp81s21_moving_drift_rs (p : Parameters) : fp81s21_moving_drift_rs_statement p := by
  obtain ⟨δi, hδi, hihalf, hinputs⟩ := fp81s21_moving_inputs_all p
  obtain ⟨δh, hδh, hhhalf, hheat⟩ := fp81s21_moving_heat_family_window_derivs p
  refine ⟨min δi δh, lt_min hδi hδh, (min_le_left _ _).trans hihalf, ?_⟩
  intro δ hδ hδle R
  have hδi' : δ ≤ δi := hδle.trans (min_le_left _ _)
  have hδh' : δ ≤ δh := hδle.trans (min_le_right _ _)
  obtain ⟨future, hfuture, -⟩ := hheat δ hδ hδh' R
  refine ⟨future, hfuture, ?_⟩
  intro a ha hH N hN A F
  obtain ⟨c, hstd, hphys⟩ := hinputs δ hδ hδi' R a ha
  have hlin := fp81s21_S102Lin p R (a + p.T)
  obtain ⟨Yh, Fd, V, hYm, hFm, hVi, hgood, hfamily⟩ :=
    fp81s21_moving_drift_rsbv_window_fixed p R hδ (hδh'.trans hhhalf) a ha hH hN A F
      hstd hlin (hphys N hN A) future hfuture
  have hr0 : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  obtain ⟨Mb, hMb, -⟩ := fp81s21_moving_M1 p R hH hN A hstd hr0 (hphys N hN A)
  refine ⟨Yh, Fd, V, hYm, hFm, hVi, hgood, ?_⟩
  intro Φ hΦ
  obtain ⟨M, hMi, hlevels⟩ := hfamily Φ hΦ
  refine ⟨M, hMi, ?_⟩
  intro L
  obtain ⟨⟨WS⟩, hmajor⟩ := hlevels L
  refine ⟨WS, ?_⟩
  intro q r hq hqr hr
  refine ⟨(hmajor q r hq hqr hr).1, ?_, (hmajor q r hq hqr hr).2⟩
  let τ := s102_tauk (d := p.d) hH L
  let α := s102_alk (d := p.d) L
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := a + p.T) ha le_rfl
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ := fun x => Φ (W (s102_Lam (a + p.T) L x))
  have hG5 : MemCb 5 G := by
    have hΨ : MemCb 5 (fun w => Φ (W w)) :=
      (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    exact (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (s102_Lam (a + p.T) L) hΨ).1
  have hG : MemCb 2 G := ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hfun : (fun w => Φ (W (s102_Pj (a + p.T) hH L w))) =
      fun w => G (s102_obs τ α w) := by
    funext w
    dsimp only [G, τ, α]
    rw [s102_Pj_eq_Lam hH L w]
  have hcov : ∀ i j, ContinuousOn
      (fun u => s102_obsCov (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) τ α u i j)
      (Icc 0 (a + p.T)) :=
    fun i j => s102_obsCov_cont hH L (fp81s21_moving_gramInt hstd L) i j
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  filter_upwards [hgood, hMb, F.indist, WS.value_isRS q r hq hqr hr] with ω hg hb hind hRS
  have hfield : (fun u f => r2QuadField p.s (r26t3_mu R u) A.P F.X u ω f) =
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) := by
    funext u f
    unfold r2QuadField
    have hInt : (fun ζ => pairEnergy (commutatorKernel p.d p.s (fun x => gradient f x))
        (F.X u.toNNReal ζ) (r26t3_mu R u)) =ᵐ[A.P]
        (fun ζ => pairEnergy (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ζ) (r26t3_mu R u)) := by
      filter_upwards [F.indist] with ζ hz
      rw [hz u.toNNReal]
    rw [hind u.toNNReal, integral_congr_ae hInt]
  have hRS' : fp81s21_IsRSOn q r (fun t u v =>
      fderiv ℝ (r2HeatFn (future (a + p.T)) (fun w => G (s102_obs τ α w)) t)
        (Yh ω t) (Fd ω v - Fd ω u)) (WS.value q r ω) := by
    change fp81s21_IsRSOn q r (fun t u v =>
      fderiv ℝ (r2HeatFn (future (a + p.T))
        (fun w => Φ (W (s102_Pj (a + p.T) hH L w))) t)
        (Yh ω t) (Fd ω v - Fd ω u)) (WS.value q r ω) at hRS
    rw [hfun] at hRS
    exact hRS
  have hval := fp81s21_cylindrical_drift_rs_value hP hstd.hD hlin hb hH
    (future (a + p.T)) (hfuture.2.1 (a + p.T) hH) τ α hcov G hG (Yh ω) (Fd ω)
    hg.2.1 hg.2.2.2.2.2.2 q r hq hqr hr (WS.value q r ω) hRS'
  have heq : ∀ u ∈ Ioc q r,
      (∑ i, fderiv ℝ (gaussHeat (s102_obsCov (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) τ α) G u)
        (s102_obs τ α (Yh ω u)) (EuclideanSpace.single i 1) *
        s102_hh (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) τ α
          (fun v => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω) i u) =
      fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
    intro u hu
    have huH : u ∈ Icc (0 : ℝ) (a + p.T) := ⟨hq.trans hu.1.le, hu.2.trans hr⟩
    simp only [fp81s21_moving_drift_cyl_sum, ← hfield, hg.1 u huH, τ, α, G, W]
  exact ⟨hval.1.congr_fun heq measurableSet_Ioc, hval.2.trans (setIntegral_congr_fun measurableSet_Ioc heq)⟩

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_rs

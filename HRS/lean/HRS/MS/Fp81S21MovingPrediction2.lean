import HRS.MS.Fp81S21MovingPrediction
import HRS.MS.R2InterpAux127
import HRS.MS.R2InterpAux89

/-! Almost sure path-space continuity for the moving physical prediction. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.FixEq

/-- The actual full-horizon prediction has continuous paths almost surely. -/
theorem fp81s21_moving_prediction_continuous
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∀ᵐ ω ∂A.P, ContinuousOn
      (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω) (Icc 0 H) := by
  classical
  have hN0 : 0 < N := by omega
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide) p.hd
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by linarith
  have hP0 : 0 ≤ (p.d : ℝ) + 2 := by linarith
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  have hm : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by unfold wholeSpaceIndex; omega)
  obtain ⟨Cm, hCm⟩ := hphys.particle_moment
  have hmom : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
        (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) :=
    fun u hu => (hCm u hu).1
  have hbound : ∀ u ∈ Icc (0 : ℝ) H,
      ∫ x, jbracket x ^ ((p.d : ℝ) + 2) ∂(HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) ≤ Cm :=
    fun u hu => (hCm u hu).2
  have hXm : ∀ t, Measurable (A.X t) := (A.strong H).adapted
  have hcont := (A.strong H).cont
  have hzc := s102_zeta_cont hm hN0 A.P A.X hXm hcont
  have horbF : ∀ᵐ ω ∂A.P, ∀ q ∈ s102_Qset H, ∀ α : MultiIndex p.d,
      ContinuousOn (fun u => s102_zf A.P F.X ω u
        (propagatorW (r26t3_coeff R) u q (oscTestFun (wholeSpaceIndex p.d) α))) (Icc 0 q) := by
    rw [ae_ball_iff (s102_Qset_countable H)]
    intro q hq
    rw [ae_all_iff]
    intro α
    exact fp81s21_moving_orbit_continuous p R hδ hδh hH hN A F hstd hphys q hq α
  filter_upwards [hcont, hzc, horbF, F.indist] with ω hc hz horb hind
  have hmap (v : ℝ≥0) : A.P.map (F.X v) = A.P.map (A.X v) := by
    apply Measure.map_congr
    filter_upwards [F.indist] with ω' hω'
    exact hω' v
  have hzf (u : ℝ) (f : Euc p.d → ℝ) :
      s102_zf A.P F.X ω u f = s102_zf A.P A.X ω u f := by
    unfold s102_zf
    rw [hind u.toNNReal, hmap u.toNNReal]
  have horb : ∀ q ∈ s102_Qset H, ∀ α : MultiIndex p.d,
      ContinuousOn (fun u => s102_zf A.P A.X ω u
        (propagatorW (r26t3_coeff R) u q (oscTestFun (wholeSpaceIndex p.d) α))) (Icc 0 q) := by
    intro q hq α
    exact (horb q hq α).congr (fun u hu => (hzf u _).symm)
  obtain ⟨M, hM⟩ := s102_zf_unif hd1 hP0 (2 * p.d + 8) hr hN0 A.P A.X hmom hbound ω hc
  exact fp81s21_moving_Y_continuousOn hstd.hD hstd.hcls hP hlin hH hd1 hP0 hr hm hN0
    A.P A.X hXm hmom ω hz hM horb

#print axioms HRS.Fp81.S21.fp81s21_moving_prediction_continuous
end HRS.Fp81.S21
end

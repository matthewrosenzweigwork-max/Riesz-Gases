import HRS.MS.Fp81S21RemotePhysicalG

/-! Packet 38G: the supplied Gaussian RS correction has a uniform remote
exponential bound. The radius precedes every realization and retained package;
constants precede the future, realization, shift, test, histories and lag.
The complete heat clause is consumed without selecting another future.
`UG/UB` are supplied origin-zero histories for the weak canonical/Wick fields.
The prediction uses chart action on propagated tests, not raw OscDual.eval. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.S111K2

local instance fp81s21_remoteG_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_remoteG_meas (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_remoteG_borel (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Physical full-horizon prediction, restricted to the observation window. -/
def fp81s21_remote_G_prediction {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R) (G : GaussianRealization R)
    (a : ℝ) (ha : 0 ≤ a) (ω : G.Ω) (t : ℝ) : Window p :=
  HRS.MS.ProClosureS111.physicalWindowRestriction ha le_rfl
    (r2Predicted (r26t3_coeff R)
      (processWindow (wholeSpaceIndex p.d) (a + p.T) 0 G.Z ω)
      (fun s => fp81s21_chartAction Q.E
        (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G) s ω)) t)

/-- The exact G-side packet-20 RS type: two derivative kernels and the
literal cumulatives of the supplied histories and retained operators. -/
abbrev fp81s21_remote_G_RS {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (Φ : Window p → ℝ) :=
  fp81s21_WindowRS G.P (a + p.T)
    (fun ω t => fderiv ℝ (initialHeat future a ha Φ t)
      (fp81s21_remote_G_prediction Q G a ha ω t))
    (fun ω t => fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) UB t ω)
    (fun ω t => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t)
        (fp81s21_remote_G_prediction Q G a ha ω t)))
    (fun ω t => fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) UG t ω)

private theorem fp81s21_remoteG_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → r26t6_Coeff) (M : ℝ) (hf : MemLp f 2 P)
    (hM : (∫ ω, ‖f ω‖ ^ 2 ∂P) ≤ M) :
    Integrable (fun ω => ‖f ω‖) P ∧ (∫ ω, ‖f ω‖ ∂P) ≤ 1 + M := by
  have hi := hf.integrable one_le_two |>.norm
  have hs := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, ‖f ω‖ ∂P) ≤ ∫ ω, (1 : ℝ) + ‖f ω‖ ^ 2 ∂P := by
      apply integral_mono hi ((integrable_const 1).add hs)
      intro ω
      change ‖f ω‖ ≤ 1 + ‖f ω‖ ^ 2
      nlinarith [sq_nonneg (‖f ω‖ - 1)]
    _ = 1 + ∫ ω, ‖f ω‖ ^ 2 ∂P := by rw [integral_add (integrable_const 1) hs]; simp
    _ ≤ 1 + M := by linarith

/-- Remote Gaussian correction, uniform in every supplied realization,
history, future and RS certificate, with constants before the window start. -/
theorem fp81s21_remote_physical_G (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∃ CG cG : ℝ, 0 < CG ∧ 0 < cG ∧
      ∀ (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)),
      fp81s21_moving_heat_full_clause p R future →
      ∀ (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
        (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))),
      fp81s21_TimeL2Rep G.P (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G))
        Q.MUG 0 (a + p.T) UG →
      fp81s21_TimeL2Rep G.P (Q.S.qe G) (Q.S.Kstar ^ 4 * Q.S.B / 2) 0 (a + p.T) UB →
      ∀ (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∀ (WG : fp81s21_remote_G_RS Q future G a ha UG UB Φ) (L : ℝ), 0 < L →
        |fp81s21_WindowRS_corr WG 0 (max (a - L) 0)| ≤ CG * Real.exp (-cG * L)) := by
  refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
  intro δ hδ hδhalf R Q
  let md := 1 + Q.S.Kstar ^ 4 * Q.S.B / 2
  let mj := 1 + Q.MUG
  let kd := Q.KD * (md * Q.cD⁻¹)
  let kj := (Q.KJ * |2 * (r26t3_coeff R).ν|) * (mj * (2 * Q.cJ)⁻¹)
  let c := min Q.cD (2 * Q.cJ)
  have hmd : 0 ≤ md := by
    have hb := Q.S.B_nonneg
    dsimp [md]; positivity
  have hmj : 0 ≤ mj := by dsimp [mj]; linarith [Q.MUG_nonneg]
  have hkd : 0 ≤ kd := mul_nonneg Q.hKD (mul_nonneg hmd (inv_nonneg.mpr Q.hcD.le))
  have hcJ : 0 < 2 * Q.cJ := mul_pos (by norm_num) Q.hcJ
  have hkj : 0 ≤ kj := mul_nonneg (mul_nonneg Q.hKJ (abs_nonneg _))
    (mul_nonneg hmj (inv_nonneg.mpr hcJ.le))
  refine ⟨1 + kd + kj / 2, c, by positivity, lt_min Q.hcD hcJ, ?_⟩
  intro future hf G a ha UG UB hUG hUB Φ hΦ WG L hL
  have hΦm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hder (j : ℕ) (hj : j ≤ 5) (t : ℝ) (y : Window p) :
      ‖iteratedFDeriv ℝ j (initialHeat future a ha Φ t) y‖ ≤ 1 := by
    refine ((fp81s21_windowFuture_heat_derivs future hf.1 a ha Φ hΦm t).2 j hj y).2.trans ?_
    apply ciSup_le
    intro z
    exact (HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦm hj z).trans hΦ.2.2
  have hdA : ∀ ω t, 0 ≤ t → t ≤ a + p.T →
      ‖fderiv ℝ (initialHeat future a ha Φ t)
        (fp81s21_remote_G_prediction Q G a ha ω t)‖ ≤ 1 := by
    intro ω t _ _
    rw [← norm_iteratedFDeriv_one]
    exact hder 1 (by norm_num) t _
  have hjA : ∀ ω t, 0 ≤ t → t ≤ a + p.T →
      ‖fp81s21_covariance_pairingCLM (iteratedFDeriv ℝ 2
        (initialHeat future a ha Φ t) (fp81s21_remote_G_prediction Q G a ha ω t))‖ ≤ 1 := by
    intro ω t _ _
    exact (fp81s21_covariance_pairingCLM_norm_le _).trans (hder 2 (by norm_num) t _)
  have hB := (Q.S.payload G).2.2.2.2.1
  have hG := (Q.canon.payload G).coefficients.weak_momentRep
  have hd := fp81s21_remote_history_rs_bound G.P (Q.S.qe G)
    (Q.S.Kstar ^ 4 * Q.S.B / 2) md (a + p.T) a Q.cD Q.KD
    (add_nonneg ha p.hT.le) (le_add_of_nonneg_right p.hT.le) Q.hcD Q.hKD
    hB.1 hmd (fun s hs => fp81s21_remoteG_moment G.P _ _
      (hB.2 s hs).1 (hB.2 s hs).2.1) UB hUB _ _ WG.drift hdA ?_ ha L hL
  · have hj := fp81s21_remote_history_rs_bound G.P
      (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)) Q.MUG mj
      (a + p.T) a (2 * Q.cJ) (Q.KJ * |2 * (r26t3_coeff R).ν|)
      (add_nonneg ha p.hT.le) (le_add_of_nonneg_right p.hT.le) hcJ
      (mul_nonneg Q.hKJ (abs_nonneg _)) hG.1 hmj
      (fun s hs => fp81s21_remoteG_moment G.P _ _ (hG.2 s hs).1 (hG.2 s hs).2.1)
      UG hUG _ _ WG.covariance hjA ?_ ha L hL
    · have heD : Real.exp (-Q.cD * L) ≤ Real.exp (-c * L) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hL.le
      have heJ : Real.exp (-(2 * Q.cJ) * L) ≤ Real.exp (-c * L) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hL.le
      have hd' : |∫ ω, WG.drift.value 0 (max (a - L) 0) ω ∂G.P| ≤
          kd * Real.exp (-c * L) := by
        exact hd.trans (by dsimp [kd]; nlinarith [mul_le_mul_of_nonneg_left heD hkd])
      have hj' : |∫ ω, WG.covariance.value 0 (max (a - L) 0) ω ∂G.P| ≤
          kj * Real.exp (-c * L) := by
        exact hj.trans (by dsimp [kj]; nlinarith [mul_le_mul_of_nonneg_left heJ hkj])
      unfold fp81s21_WindowRS_corr
      calc
        _ ≤ |∫ ω, WG.drift.value 0 (max (a - L) 0) ω ∂G.P| +
            (1 / 2 : ℝ) * |∫ ω, WG.covariance.value 0 (max (a - L) 0) ω ∂G.P| := by
          simpa only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            using abs_add_le (-(∫ ω, WG.drift.value 0 (max (a - L) 0) ω ∂G.P))
              ((1 / 2 : ℝ) * ∫ ω, WG.covariance.value 0 (max (a - L) 0) ω ∂G.P)
        _ ≤ (1 + kd + kj / 2) * Real.exp (-c * L) := by
          nlinarith [Real.exp_pos (-c * L)]
    · intro ω u v hu huv hv
      let V := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UG ω)
      have he := congrArg (fun O => O V) ((Q.OJ a ha).covariance_add 0 u v le_rfl hu huv hv)
      change (Q.OJ a ha).covariance 0 v V =
        (Q.OJ a ha).covariance 0 u V + (Q.OJ a ha).covariance u v V at he
      change ‖(Q.OJ a ha).covariance 0 v V - (Q.OJ a ha).covariance 0 u V‖ ≤ _
      rw [he, add_sub_cancel_left]
      have hw : ∀ s, s111k2_age Q.cJ a s ^ 2 = s111k2_age (2 * Q.cJ) a s := by
        intro s
        simp only [s111k2_age, pow_two, ← Real.exp_add]
        congr 1; ring
      simpa only [hw, mul_assoc] using (Q.OJ a ha).covariance_norm u v hu huv hv V
  · intro ω u v hu huv hv
    let V := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)
    have he := congrArg (fun O => O V) ((Q.OD a ha).drift_add 0 u v le_rfl hu huv hv)
    change (Q.OD a ha).drift 0 v V =
      (Q.OD a ha).drift 0 u V + (Q.OD a ha).drift u v V at he
    change ‖(Q.OD a ha).drift 0 v V - (Q.OD a ha).drift 0 u V‖ ≤ _
    rw [he, add_sub_cancel_left]
    exact (Q.OD a ha).drift_norm u v hu huv hv V

#print axioms fp81s21_remote_G_prediction
#print axioms fp81s21_remote_G_RS
#print axioms fp81s21_remote_physical_G
end HRS.Fp81.S21
end

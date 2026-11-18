import HRS.MS.Fp81S21RecentRSPhysical6
import HRS.MS.Fp81S21RecentRSPhysical5

/-! Gaussian value specialization on supplied predictions and same-field recent
BV carriers. Origin histories and recent histories need not agree as functions:
their physical increments refer to the same retained canonical/quadratic fields. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_recentRS7_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_recentRS7_meas (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_recentRS7_borel (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Both Gaussian RS values for an arbitrary realization with supplied physical
prediction and origin histories. The recent BVLaw uses the literal Q fields;
its separate operator is retained. No RS value equality is an input. -/
theorem fp81s21_recentRS_gaussian_values_supplied
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (coef : MultiIndex p.d → ℝ)
    (hstd : Fp81MovingStd (r26t3_coeff R) (m p) (a + p.T)
      (2 * p.d + 8) coef (add_pos_of_nonneg_of_pos ha p.hT))
    (Q : fp81s21_Physical35 p R) (G : GaussianRealization R)
    (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (hUG : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)) Q.MUG 0 (a + p.T) UG)
    (hUB : fp81s21_TimeL2Rep G.P (Q.S.qe G)
      (Q.S.Kstar ^ 4 * Q.S.B / 2) 0 (a + p.T) UB)
    (Y : G.Ω → C(I (a + p.T), Window p))
    (hY : ∀ r : I (a + p.T), ∀ τ : I p.T, ∀ᵐ ω ∂G.P,
      OscPath.at' (Y ω r) τ =
        r2Vprop (r26t3_coeff R) (m p) (a + τ) (min (r : ℝ) (a + τ))
          (fp81s21_chartAction Q.E
            (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)
              (min (r : ℝ) (a + τ)) ω)))
    (L : ℝ) (hL : 0 < L) (X : G.Ω → CH (L + p.T))
    (hX : CD Q.E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
      (max (a - L) 0) (L + p.T) X)
    (hmean : (∫ ω, X ω ∂G.P) = 0)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T)) (hP : PSpec p R Q.E L a P)
    (YG : G.Ω → YH p (L + p.T)) (hYG : YG = fun ω => P (cen G.P X ω))
    (c K : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (O : r26t6_IntervalOperators Q.E (r26t3_coeff R) p.T a c K)
    (dG : G.Ω → fp81s21_VD p a ha L hL c K O hK hc)
    (jG : G.Ω → fp81s21_VJ p a ha L hL c K O hK hc)
    (hBV : fp81s21_BVLaw p R G.P Q.E
      (fun s ω f => fp81s21_chartAction Q.E
        (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G) s ω) f)
      (fun s ω f => fp81s21_chartAction Q.E (Q.S.qe G s ω) f)
      Q.MUG (Q.S.Kstar ^ 4 * Q.S.B / 2) a L c K ha hL O hK hc dG jG)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (Φ : Window p → ℝ)
    (WG : fp81s21_remote_G_RS_at Q future G a ha UG UB Φ
      (fp81s21_remote_G_extend G a ha Y))
    {KD KJ : ℝ}
    (FD : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VD p a ha L hL c K O hK hc) KD)
    (FJ : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VJ p a ha L hL c K O hK hc) KJ)
    (hRS : fp81s21_recentHeatKernelRS p future L hL a ha Φ FD FJ) :
    ∀ᵐ ω ∂G.P,
      WG.drift.value (max (a - L) 0) (a + p.T) ω = FD.kernel (YG ω) (dG ω) ∧
      WG.covariance.value (max (a - L) 0) (a + p.T) ω = FJ.kernel (YG ω) (jG ω) := by
  obtain ⟨hd, hj⟩ := fp81s21_recentRS_gaussian_increments_of_std p R a ha coef hstd
    Q G UG UB hUG hUB
  have hp := fp81s21_recentRS_gaussian_prediction_restrict_supplied p R Q G
    L hL a ha Y hY X hX hmean P hP
  have hpred : ∀ᵐ ω ∂G.P, ∀ v : I (L + p.T),
      (v : ℝ) ≤ a - max (a - L) 0 + p.T →
      YG ω v = fp81s21_remote_G_extend G a ha Y ω (max (a - L) 0 + (v : ℝ)) := by
    filter_upwards [hp] with ω hω
    intro v hv
    simpa only [hYG, min_eq_left hv] using hω v
  exact fp81s21_recentRS_physical_values p R G.P Q.E
    (fun s ω f => fp81s21_chartAction Q.E
      (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G) s ω) f)
    (fun s ω f => fp81s21_chartAction Q.E (Q.S.qe G s ω) f)
    Q.MUG (Q.S.Kstar ^ 4 * Q.S.B / 2) a L c K ha hL O hK hc dG jG hBV
    future Φ YG (fp81s21_remote_G_extend G a ha Y)
    (fun ω t => fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) UB t ω)
    (fun ω t => fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) UG t ω)
    WG FD FJ hRS hpred hd hj

/-- The supplied GRS record discharges the prediction-section and origin-history
interfaces. Its Y and WG remain the literal supplied record fields. -/
theorem fp81s21_recentRS_gaussian_values
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (coef : MultiIndex p.d → ℝ)
    (hstd : Fp81MovingStd (r26t3_coeff R) (m p) (a + p.T)
      (2 * p.d + 8) coef (add_pos_of_nonneg_of_pos ha p.hT))
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (Φ : Window p → ℝ) (W : fp81s21_GRS Q future a ha Φ)
    (L : ℝ) (hL : 0 < L) (X : Q.src.G0.Ω → CH (L + p.T))
    (hX : CD Q.E Q.src.G0.P (fun u ω f => OscDual.eval (Q.src.G0.Z u ω) f)
      (max (a - L) 0) (L + p.T) X)
    (hmean : (∫ ω, X ω ∂Q.src.G0.P) = 0)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T)) (hP : PSpec p R Q.E L a P)
    (YG : Q.src.G0.Ω → YH p (L + p.T))
    (hYG : YG = fun ω => P (cen Q.src.G0.P X ω))
    (c K : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (O : r26t6_IntervalOperators Q.E (r26t3_coeff R) p.T a c K)
    (dG : Q.src.G0.Ω → fp81s21_VD p a ha L hL c K O hK hc)
    (jG : Q.src.G0.Ω → fp81s21_VJ p a ha L hL c K O hK hc)
    (hBV : fp81s21_BVLaw p R Q.src.G0.P Q.E
      (fun s ω f => fp81s21_chartAction Q.E
        (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection s ω) f)
      (fun s ω f => fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 s ω) f)
      Q.MUG (Q.S.Kstar ^ 4 * Q.S.B / 2) a L c K ha hL O hK hc dG jG)
    {KD KJ : ℝ}
    (FD : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VD p a ha L hL c K O hK hc) KD)
    (FJ : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VJ p a ha L hL c K O hK hc) KJ)
    (hRS : fp81s21_recentHeatKernelRS p future L hL a ha Φ FD FJ) :
    ∀ᵐ ω ∂Q.src.G0.P,
      W.WG.drift.value (max (a - L) 0) (a + p.T) ω = FD.kernel (YG ω) (dG ω) ∧
      W.WG.covariance.value (max (a - L) 0) (a + p.T) ω = FJ.kernel (YG ω) (jG ω) := by
  exact fp81s21_recentRS_gaussian_values_supplied p R a ha coef hstd Q Q.src.G0
    (Q.UG a ha) (Q.UB a ha) (Q.hUG a ha) (Q.hUB a ha) W.Y W.physical
    L hL X hX hmean P hP YG hYG c K hK hc O dG jG hBV future Φ W.WG FD FJ hRS

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_gaussian_values_supplied
#print axioms HRS.Fp81.S21.fp81s21_recentRS_gaussian_values
end

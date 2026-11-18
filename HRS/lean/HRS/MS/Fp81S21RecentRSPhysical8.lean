import HRS.MS.Fp81S21RecentRSPhysical3
import HRS.MS.Fp81S21RecentRSPhysical5
import HRS.MS.Fp81S21WindowCovId6

/-! Particle value specialization for the supplied physical RS record. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111 HRS.MS.CovMeas

local instance fp81s21_recentRS8_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

/-- The particle recent carriers evaluate the literal supplied window RS record. -/
theorem fp81s21_recentRS_particle_values
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ} (hN : 2 ≤ N)
    (A : Particle R N) (F : FilteredParticle A) (a : ℝ) (ha : 0 ≤ a)
    (D20 : fp81s21_finproj_shared_data p R a A F)
    (L : ℝ) (hL : 0 < L) (coef : MultiIndex p.d → ℝ)
    (hDs : S101Data (r26t3_coeff R) (m p) (a + p.T) (r p) coef)
    (hDl : S101Data (r26t3_coeff R) (m p)
      (max (a - L) 0 + (L + p.T)) (r p) coef)
    (hmom : ∀ u ∈ I (max (a - L) 0 + (L + p.T)),
      Integrable (fun x : Euc p.d => jbracket x ^ (Pw p))
        (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (Mη MB c K : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (dN : A.Ω → fp81s21_VD p a ha L hL c K O hK hc)
    (jN : A.Ω → fp81s21_VJ p a ha L hL c K O hK hc)
    (hBV : fp81s21_BVLaw p R A.P E (fp81s21_particleEmpField R N A)
      (fp81s21_particleQuadField R N A) Mη MB a L c K ha hL O hK hc dN jN)
    (YN : A.Ω → YH p (L + p.T)) (hYN : NId p R A L a YN)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (Φ : Window p → ℝ)
    (WN : fp81s21_WindowRS A.P (a + p.T)
      (fun ω t => fderiv ℝ (initialHeat future a ha Φ t)
        (physicalWindowRestriction ha le_rfl (D20.Yh ω t)))
      (fun ω t => fp81s21_weightedDrift_windowCum (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R)
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t)
      (fun ω t => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t)
          (physicalWindowRestriction ha le_rfl (D20.Yh ω t))))
      (fun ω t => fp81s21_windowCovarianceMap p a ha (D20.Fj ω t)))
    {KD KJ : ℝ}
    (FD : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VD p a ha L hL c K O hK hc) KD)
    (FJ : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VJ p a ha L hL c K O hK hc) KJ)
    (hRS : fp81s21_recentHeatKernelRS p future L hL a ha Φ FD FJ) :
    ∀ᵐ ω ∂A.P,
      WN.drift.value (max (a - L) 0) (a + p.T) ω = FD.kernel (YN ω) (dN ω) ∧
      WN.covariance.value (max (a - L) 0) (a + p.T) ω = FJ.kernel (YN ω) (jN ω) := by
  have hp := fp81s21_recentRS_particle_prediction_restrict p R hN A F L hL a ha
    D20 coef hDs hDl hmom YN hYN
  have hd : ∀ᵐ ω ∂A.P, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      fp81s21_weightedDrift_windowCum (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R)
        (fun s f => r2QuadField p.s (r26t3_mu R s) A.P A.X s ω f) v -
      fp81s21_weightedDrift_windowCum (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R)
        (fun s f => r2QuadField p.s (r26t3_mu R s) A.P A.X s ω f) u =
      fp81s21_weightedDrift_windowInc (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R)
        (fun s f => fp81s21_particleQuadField R N A s ω f) u v := by
    filter_upwards [D20.Fd_good] with ω hω
    intro u v hu huv hv
    have h0 (t : ℝ) (ht : 0 ≤ t) (htH : t ≤ a + p.T) := hω.2.2.2.2 0 t le_rfl ht htH
    have hu' := h0 u hu (huv.trans hv)
    have hv' := h0 v (hu.trans huv) hv
    rw [hω.1, sub_zero] at hu' hv'
    have hinc := hω.2.2.2.2 u v hu huv hv
    have hh := congrArg (physicalWindowRestriction (d := p.d) (m := m p)
      (T := p.T) (H := a + p.T) ha le_rfl) hinc
    simpa [fp81s21_weightedDrift_windowCum, fp81s21_weightedDrift_windowInc,
      fp81s21_particleQuadField, ← hu', ← hv'] using hh
  have hj : ∀ᵐ ω ∂A.P, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => fp81s21_particleEmpField R N A s ω f) (Ioc u v)
        ((fp81s21_windowCovarianceMap p a ha (D20.Fj ω v) -
          fp81s21_windowCovarianceMap p a ha (D20.Fj ω u) : projTensor (Window p) 2) :
            TensorDual (Window p) 2) := by
    filter_upwards [D20.Fj_good] with ω hω
    intro u v hu huv hv
    have hh := fp81s21_restrict_isWindowJValue (r26t3_coeff R) ha
      (fp81s21_movingRawEtaField p R A ω) (Ioc u v) (hω.1 u v hu huv hv)
    have heq : ((fp81s21_windowCovarianceMap p a ha (D20.Fj ω v) -
        fp81s21_windowCovarianceMap p a ha (D20.Fj ω u) : projTensor (Window p) 2) :
          TensorDual (Window p) 2) =
        HRS.MC.E213O.tensorPow' 2 (physicalWindowRestriction (d := p.d) (m := m p)
          (T := p.T) (H := a + p.T) ha le_rfl)
          ((D20.Fj ω v - D20.Fj ω u : projTensor _ 2) : TensorDual _ 2) := by
      rw [← map_sub]
      rfl
    rw [heq]
    exact hh
  exact fp81s21_recentRS_physical_values p R A.P E
    (fp81s21_particleEmpField R N A) (fp81s21_particleQuadField R N A)
    Mη MB a L c K ha hL O hK hc dN jN hBV future Φ YN
    (fun ω t => physicalWindowRestriction ha le_rfl (D20.Yh ω t))
    (fun ω t => fp81s21_weightedDrift_windowCum (m := m p) (T := p.T) (H := a + p.T) ha le_rfl (r26t3_coeff R)
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t)
    (fun ω t => fp81s21_windowCovarianceMap p a ha (D20.Fj ω t))
    WN FD FJ hRS hp hd hj

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_particle_values
end

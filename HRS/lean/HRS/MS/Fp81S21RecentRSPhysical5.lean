import HRS.MS.Fp81S21RecentRSPhysical
import HRS.MS.Fp81S21RecentJointPhysical
import HRS.MS.Fp81S21RecentHeatKernelPhysical2
import HRS.MS.Fp81S21GaussianPhysicalIncrements
import HRS.MS.Fp81S21RSValue5

/-! Value transport for either supplied physical law. The increment hypotheses
are physical certificates for the same fields as BVLaw; covariance equality is
derived from two certificates. Predictions and RS records are not reselected. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

local instance fp81s21_recentRS5_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

/-- Same-field physical increment certificates and the simultaneous prediction
restriction identify both supplied RS values with their recent heat kernels.
This applies to particle and Gaussian laws separately. -/
theorem fp81s21_recentRS_physical_values
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (z B : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (hK : 0 ≤ K) (hc : 0 ≤ c)
    (D : Ω → fp81s21_VD p a ha L hL c K O hK hc)
    (J : Ω → fp81s21_VJ p a ha L hL c K O hK hc)
    (hBV : fp81s21_BVLaw p R μ E z B Mη MB a L c K ha hL O hK hc D J)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (Φ : Window p → ℝ) (Y : Ω → YH p (L + p.T)) (Z : Ω → ℝ → Window p)
    (Fd : Ω → ℝ → Window p) (Fj : Ω → ℝ → projTensor (Window p) 2)
    (W : fp81s21_WindowRS μ (a + p.T)
      (fun ω t => fderiv ℝ (initialHeat future a ha Φ t) (Z ω t)) Fd
      (fun ω t => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t) (Z ω t))) Fj)
    {KD KJ : ℝ}
    (FD : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VD p a ha L hL c K O hK hc) KD)
    (FJ : fp81s21_RecentRSKernel (YH p (L + p.T))
      (fp81s21_VJ p a ha L hL c K O hK hc) KJ)
    (hRS : fp81s21_recentHeatKernelRS p future L hL a ha Φ FD FJ)
    (hpred : ∀ᵐ ω ∂μ, ∀ v : I (L + p.T),
      (v : ℝ) ≤ a - max (a - L) 0 + p.T →
      Y ω v = Z ω (max (a - L) 0 + (v : ℝ)))
    (hd : ∀ᵐ ω ∂μ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      Fd ω v - Fd ω u = fp81s21_weightedDrift_windowInc ha le_rfl
        (r26t3_coeff R) (fun s f => B s ω f) u v)
    (hj : ∀ᵐ ω ∂μ, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => z s ω f) (Ioc u v)
        ((Fj ω v - Fj ω u : projTensor (Window p) 2) : TensorDual (Window p) 2)) :
    ∀ᵐ ω ∂μ,
      W.drift.value (max (a - L) 0) (a + p.T) ω = FD.kernel (Y ω) (D ω) ∧
      W.covariance.value (max (a - L) 0) (a + p.T) ω = FJ.kernel (Y ω) (J ω) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  let b := max (a - L) 0
  let h := a - b + p.T
  have hend : b + h = a + p.T := by dsimp [h]; ring
  have hh : 0 ≤ h := g.duration_nonneg
  have hbend : b ≤ a + p.T := by linarith
  have hwd := W.drift.value_isRS b (a + p.T) g.start_nonneg hbend le_rfl
  have hwj := W.covariance.value_isRS b (a + p.T) g.start_nonneg hbend le_rfl
  filter_upwards [hBV.2.2.2.2.2.2, hpred, hd, hj, hwd, hwj]
    with ω hbv hp hdω hjω hwdω hwjω
  have hextD (s : I (L + p.T)) :
      fp81s21_bvExt g.horizon_nonneg (D ω).val s =
        fp81s21_bvPath g.horizon_nonneg (D ω).val s := by
    rw [fp81s21_bvExt_apply, fp81s21_bvPath_apply]
  have hextJ (s : I (L + p.T)) :
      fp81s21_bvExt g.horizon_nonneg (J ω).val s =
        fp81s21_bvPath g.horizon_nonneg (J ω).val s := by
    rw [fp81s21_bvExt_apply, fp81s21_bvPath_apply]
  have hinc (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ h) :
      fp81s21_bvExt g.horizon_nonneg (D ω).val v -
        fp81s21_bvExt g.horizon_nonneg (D ω).val u = Fd ω (b + v) - Fd ω (b + u) ∧
      fp81s21_bvExt g.horizon_nonneg (J ω).val v -
        fp81s21_bvExt g.horizon_nonneg (J ω).val u = Fj ω (b + v) - Fj ω (b + u) := by
    have huH : u ∈ I (L + p.T) := ⟨hu, huv.trans (hv.trans g.duration_le_horizon)⟩
    have hvH : v ∈ I (L + p.T) := ⟨hu.trans huv, hv.trans g.duration_le_horizon⟩
    have hi := hbv.2.2.2 ⟨u, huH⟩ ⟨v, hvH⟩ huv
    have hminu : min u (a - max (a - L) 0 + p.T) = u := min_eq_left (huv.trans hv)
    have hminv : min v (a - max (a - L) 0 + p.T) = v := min_eq_left hv
    simp only [hminu, hminv] at hi
    have hbu : 0 ≤ b + u := add_nonneg g.start_nonneg hu
    have hbuv : b + u ≤ b + v := by linarith
    have hbv' : b + v ≤ a + p.T := by linarith
    constructor
    · rw [hextD ⟨v, hvH⟩, hextD ⟨u, huH⟩]
      exact hi.1.trans (hdω _ _ hbu hbuv hbv').symm
    · rw [hextJ ⟨v, hvH⟩, hextJ ⟨u, huH⟩]
      apply Subtype.ext
      exact fp81s21_window_J_unique (r26t3_coeff R) p.hT _ _ hi.2
        (hjω _ _ hbu hbuv hbv')
  have htail (u v : ℝ) (hu : h ≤ u) (huv : u ≤ v) (hv : v ≤ L + p.T) :
      fp81s21_bvExt g.horizon_nonneg (D ω).val v -
        fp81s21_bvExt g.horizon_nonneg (D ω).val u = 0 ∧
      fp81s21_bvExt g.horizon_nonneg (J ω).val v -
        fp81s21_bvExt g.horizon_nonneg (J ω).val u = 0 := by
    have huH : u ∈ I (L + p.T) := ⟨g.duration_nonneg.trans hu, huv.trans hv⟩
    have hvH : v ∈ I (L + p.T) := ⟨g.duration_nonneg.trans (hu.trans huv), hv⟩
    have he := hbv.2.2.1 ⟨v, hvH⟩ ⟨u, huH⟩ (hu.trans huv) hu
    rw [hextD ⟨v, hvH⟩, hextD ⟨u, huH⟩, hextJ ⟨v, hvH⟩, hextJ ⟨u, huH⟩]
    exact ⟨sub_eq_zero.mpr he.1, sub_eq_zero.mpr he.2⟩
  have hclip (t : ℝ) (ht : 0 ≤ t) (hth : t ≤ h) :
      fp81s21_recentHeatClip p L hL a ha (projIcc 0 (L + p.T) g.horizon_nonneg t) =
        (⟨t, ht, hth.trans g.duration_le_horizon⟩ : I (L + p.T)) := by
    have htH : t ∈ I (L + p.T) := ⟨ht, hth.trans g.duration_le_horizon⟩
    have he : projIcc 0 (L + p.T) g.horizon_nonneg t = ⟨t, htH⟩ :=
      projIcc_val g.horizon_nonneg ⟨t, htH⟩
    apply Subtype.ext
    change min (projIcc 0 (L + p.T) g.horizon_nonneg t : ℝ) h = t
    rw [he, min_eq_left hth]
  nth_rw 1 [← hend] at hwdω
  nth_rw 1 [← hend] at hwjω
  constructor
  · apply fp81s21_recentRS_value_of_shift_tail g.duration_nonneg g.duration_le_horizon
      hwdω (hRS.1 (Y ω) (D ω))
    · intro τ u v hu huτ hτv hv
      dsimp only
      rw [hclip τ (hu.trans huτ) (hτv.trans hv)]
      rw [hp _ (hτv.trans hv), (hinc u v hu (huτ.trans hτv) hv).1]
    · intro τ u v hu huτ hτv hv
      dsimp only
      rw [(htail u v hu (huτ.trans hτv) hv).1, map_zero]
  · apply fp81s21_recentRS_value_of_shift_tail g.duration_nonneg g.duration_le_horizon
      hwjω (hRS.2 (Y ω) (J ω))
    · intro τ u v hu huτ hτv hv
      dsimp only [fp81s21_recentHeatEval]
      rw [hclip τ (hu.trans huτ) (hτv.trans hv)]
      rw [hp _ (hτv.trans hv), (hinc u v hu (huτ.trans hτv) hv).2]
    · intro τ u v hu huτv hτv hv
      rw [(htail u v hu (huτv.trans hτv) hv).2, map_zero]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_physical_values
end

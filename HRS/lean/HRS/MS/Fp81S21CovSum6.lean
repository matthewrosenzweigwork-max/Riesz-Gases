import HRS.MS.Fp81V01Insert
import HRS.MS.Fp81S21CovSum5

/-!
# S2.1(iii), packet 16b: continuity of the cumulative block sum

The cumulative path is the actual tsum of packet-15 block values over
`(q0,u]`. Its continuity follows from the interval-local summed domination
and the continuity of the weighted source primitive. Dual-norm
AEMeasurability remains an explicit premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter
open scoped ENNReal NNReal BigOperators Topology

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.FixEq

/-- The cumulative covariance path formed by summing the block values over
`(q0,u]`. -/
noncomputable def fp81s21_window_covariance_cumulative
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (q0 u : ℝ) : projTensor (OscPath d m H) 2 :=
  ∑' k : ℕ, fp81s21_blockValue D (Ioc q0 u) k

/-- The physical block-value cumulative is continuous on its source-time
interval. The same localized input and block contracts are used throughout,
and AEMeasurability of the dual norm on the full physical source interval is
explicit. -/
theorem fp81s21_window_covariance_cumulative_continuousOn
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    {q0 T : ℝ} (hq0 : 0 ≤ q0) (hq0T : q0 ≤ T)
    (hT : T ≤ a + H) :
    ContinuousOn (fp81s21_window_covariance_cumulative D q0) (Icc q0 T) := by
  letI : CompleteSpace (projTensor (OscPath d m H) 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete (OscPath d m H) 2
  let T0 : Set ℝ := Icc (0 : ℝ) (a + H)
  let w : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (-2 * cdec * max (a - v) 0))
  let density : ℝ → ℝ≥0∞ := T0.indicator
    (fun v => dualNormE r P (z v) * w v)
  let amp : ℝ := fp81s21_windowCovBlockAmp d r H Cmix
  let A : ℝ≥0∞ := ENNReal.ofReal |2 * C.ν|
  let B0 : ℝ := s57pC d r P * ((d : ℝ) * 2 ^ r * amp ^ 2)
  let B : ℝ≥0∞ := ENNReal.ofReal B0
  let K0 : ℝ≥0∞ := ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0)
  let Kfac : ℝ≥0∞ := A * B
  let K : ℝ≥0∞ := K0 * Kfac
  let source : ℝ → ℝ≥0∞ := fun v => K * density v
  let J : ℝ → projTensor (OscPath d m H) 2 :=
    fp81s21_window_covariance_cumulative D q0
  have hT0 : MeasurableSet T0 := measurableSet_Icc
  have hdualFinite : (∫⁻ v in T0, dualNormE r P (z v)) < ∞ := by
    have hz := D.fp81s21_hz
    unfold IsR2L1F at hz
    exact hz.2.2
  have hwmeas : Measurable w := by fun_prop
  have hdensityMeas : AEMeasurable density volume :=
    (aemeasurable_indicator_iff hT0).2
      (hdual.mul (hwmeas.aemeasurable.restrict))
  have hsourceMeas : AEMeasurable source volume :=
    aemeasurable_const.mul hdensityMeas
  have hwle : ∀ v, w v ≤ 1 := by
    intro v
    have hexp : Real.exp (-2 * cdec * max (a - v) 0) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hmax : 0 ≤ max (a - v) 0 := le_max_right _ _
      nlinarith [D.fp81s21_hcdec]
    calc
      w v ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hexp
      _ = 1 := by simp [w]
  have hKfinite : K < ∞ := by
    dsimp [K, Kfac, K0, A, B]
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · apply ENNReal.mul_lt_top <;> exact ENNReal.ofReal_lt_top
  have hdenBound :
      (∫⁻ v in T0, density v) ≤ ∫⁻ v in T0, dualNormE r P (z v) := by
    apply setLIntegral_mono' hT0
    intro v hv
    have hmul : dualNormE r P (z v) * w v ≤ dualNormE r P (z v) := by
      calc
        _ = w v * dualNormE r P (z v) := mul_comm _ _
        _ ≤ 1 * dualNormE r P (z v) :=
          mul_le_mul_left (hwle v) (dualNormE r P (z v))
        _ = _ := one_mul _
    simp [density, Set.indicator_of_mem hv, hmul]
  have hdenFinite : (∫⁻ v in T0, density v) < ∞ :=
    lt_of_le_of_lt hdenBound hdualFinite
  have hsourceT0 :
      (∫⁻ v in T0, source v) = K * (∫⁻ v in T0, density v) :=
    lintegral_const_mul'' K (hdensityMeas.restrict)
  have hIccSub : Icc q0 T ⊆ T0 := by
    intro v hv
    exact ⟨hq0.trans hv.1, hv.2.trans hT⟩
  have hsourceFinite : (∫⁻ v in Icc q0 T, source v) < ∞ := by
    calc
      (∫⁻ v in Icc q0 T, source v) ≤ ∫⁻ v in T0, source v :=
        lintegral_mono_set hIccSub
      _ = K * (∫⁻ v in T0, density v) := hsourceT0
      _ ≤ K * (∫⁻ v in T0, dualNormE r P (z v)) := by
        simpa [mul_comm] using (mul_le_mul_left hdenBound K)
      _ < ∞ := ENNReal.mul_lt_top hKfinite hdualFinite
  let G : ℝ → ℝ := fun u => (∫⁻ v in Ioc q0 u, source v).toReal
  have hforward : ∀ x ∈ Icc q0 T, ∀ y ∈ Icc q0 T, x ≤ y →
      dist (J y) (J x) ≤ dist (G y) (G x) := by
    intro x hx y hy hxy
    have hq0x : q0 ≤ x := hx.1
    have hq0y : q0 ≤ y := hy.1
    have hyleft : y ≤ T := hy.2
    let Ixy : Set ℝ := Ioc x y
    have hsumXY := fp81s21_window_covariance_blocks_tsum_weighted
      D hlin Ixy (by dsimp [Ixy]; exact measurableSet_Ioc)
      (by intro k; exact hblocks Ixy (by dsimp [Ixy]; exact measurableSet_Ioc) k)
      hdual
    have hKshape :
        (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
          ENNReal.ofReal |2 * C.ν| *
          ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
            (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))) = K := by
      dsimp [K, Kfac, K0, A, B, B0, amp]
      ac_rfl
    have hsumXYBound :
        (∑' k, ‖fp81s21_blockValue D Ixy k‖ₑ) ≤
          K * (∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
            dualNormE r P (z v) * w v) := by
      calc
        _ ≤ (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
            ENNReal.ofReal |2 * C.ν| *
            ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
              (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))) *
            (∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
              dualNormE r P (z v) *
                ENNReal.ofReal (Real.exp (-2 * cdec * max (a - v) 0))) :=
          hsumXY.1
        _ = K * (∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
              dualNormE r P (z v) * w v) := by
          rw [hKshape]
    have hsubsetT : Ixy ⊆ Ioc (0 : ℝ) (a + H) := by
      intro v hv
      exact ⟨lt_of_le_of_lt (hq0.trans hq0x) hv.1,
        hv.2.trans (hyleft.trans hT)⟩
    have hintersection : Ixy ∩ Ioc (0 : ℝ) (a + H) = Ixy :=
      Set.inter_eq_left.mpr hsubsetT
    have hdensityEq :
        (∫⁻ v in Ixy, density v) =
          ∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
            dualNormE r P (z v) * w v := by
      rw [hintersection]
      apply setLIntegral_congr_fun (by dsimp [Ixy]; exact measurableSet_Ioc)
      intro v hv
      have hvT : v ∈ T0 := ⟨le_of_lt (lt_of_le_of_lt (hq0.trans hq0x) hv.1),
        hv.2.trans (hyleft.trans hT)⟩
      simp [density, Set.indicator_of_mem hvT]
    have hsourceEq :
        (∫⁻ v in Ixy, source v) =
          K * (∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
            dualNormE r P (z v) * w v) := by
      calc
        (∫⁻ v in Ixy, source v) = K * (∫⁻ v in Ixy, density v) :=
          lintegral_const_mul'' K (hdensityMeas.restrict)
        _ = K * (∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
            dualNormE r P (z v) * w v) := by rw [hdensityEq]
    have hsumXYFinite : (∑' k, ‖fp81s21_blockValue D Ixy k‖ₑ) < ∞ :=
      hsumXY.2.1
    have hsumXYLeSource :
        (∑' k, ‖fp81s21_blockValue D Ixy k‖ₑ) ≤
          ∫⁻ v in Ixy, source v := by
      calc
        _ ≤ K * (∫⁻ v in Ixy ∩ Ioc (0 : ℝ) (a + H),
            dualNormE r P (z v) * w v) := hsumXYBound
        _ = ∫⁻ v in Ixy, source v := hsourceEq.symm
    have hsumCumY := fp81s21_window_covariance_blocks_tsum_weighted
      D hlin (Ioc q0 y) measurableSet_Ioc
      (hblocks (Ioc q0 y) measurableSet_Ioc) hdual
    have hsumCumX := fp81s21_window_covariance_blocks_tsum_weighted
      D hlin (Ioc q0 x) measurableSet_Ioc
      (hblocks (Ioc q0 x) measurableSet_Ioc) hdual
    have hcumYsummable :
        Summable (fun k => fp81s21_blockValue D (Ioc q0 y) k) :=
      Summable.of_enorm (ne_top_of_lt hsumCumY.2.1)
    have hcumXsummable :
        Summable (fun k => fp81s21_blockValue D (Ioc q0 x) k) :=
      Summable.of_enorm (ne_top_of_lt hsumCumX.2.1)
    have hincSummable : Summable (fun k => fp81s21_blockValue D Ixy k) :=
      Summable.of_enorm (ne_top_of_lt hsumXYFinite)
    have hunion : Ioc q0 x ∪ Ioc x y = Ioc q0 y :=
      Set.Ioc_union_Ioc_eq_Ioc hq0x hxy
    have hdisj : Disjoint (Ioc q0 x) (Ioc x y) :=
      Set.Ioc_disjoint_Ioc_of_le le_rfl
    have hoverlap : volume (Ioc q0 x ∩ Ioc x y) = 0 := by
      rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
      simp
    have hblockAdd : ∀ k,
        fp81s21_blockValue D (Ioc q0 y) k =
          fp81s21_blockValue D (Ioc q0 x) k + fp81s21_blockValue D Ixy k := by
      intro k
      calc
        fp81s21_blockValue D (Ioc q0 y) k =
            fp81s21_blockValue D (Ioc q0 x ∪ Ioc x y) k := by rw [← hunion]
        _ = fp81s21_blockValue D (Ioc q0 x) k +
              fp81s21_blockValue D Ixy k := by
          exact fp81s21_blockValue_union D measurableSet_Ioc measurableSet_Ioc
            hoverlap k
    have hJadd : J y = J x + (∑' k, fp81s21_blockValue D Ixy k) := by
      dsimp [J, fp81s21_window_covariance_cumulative]
      calc
        (∑' k, fp81s21_blockValue D (Ioc q0 y) k) =
            ∑' k, (fp81s21_blockValue D (Ioc q0 x) k +
              fp81s21_blockValue D Ixy k) := tsum_congr hblockAdd
        _ = (∑' k, fp81s21_blockValue D (Ioc q0 x) k) +
              ∑' k, fp81s21_blockValue D Ixy k :=
          hcumXsummable.tsum_add hincSummable
    have hsourceXYFinite : (∫⁻ v in Ixy, source v) < ∞ := by
      have hsubset : Ixy ⊆ Icc q0 T := by
        intro v hv
        exact ⟨hq0x.trans hv.1.le, hv.2.trans hyleft⟩
      exact lt_of_le_of_lt (lintegral_mono_set hsubset) hsourceFinite
    have hsourceQ0xFinite : (∫⁻ v in Ioc q0 x, source v) < ∞ := by
      have hsubset : Ioc q0 x ⊆ Icc q0 T := by
        intro v hv
        exact ⟨hv.1.le, hv.2.trans hx.2⟩
      exact lt_of_le_of_lt (lintegral_mono_set hsubset) hsourceFinite
    have hsourceQ0yFinite : (∫⁻ v in Ioc q0 y, source v) < ∞ := by
      have hsubset : Ioc q0 y ⊆ Icc q0 T := by
        intro v hv
        exact ⟨hv.1.le, hv.2.trans hy.2⟩
      exact lt_of_le_of_lt (lintegral_mono_set hsubset) hsourceFinite
    have hsplit : (∫⁻ v in Ioc q0 y, source v) =
        (∫⁻ v in Ioc q0 x, source v) + (∫⁻ v in Ixy, source v) := by
      rw [← Set.Ioc_union_Ioc_eq_Ioc hq0x hxy,
        lintegral_union measurableSet_Ioc hdisj]
    have hGdiff : G y - G x = (∫⁻ v in Ixy, source v).toReal := by
      dsimp [G]
      rw [hsplit, ENNReal.toReal_add hsourceQ0xFinite.ne hsourceXYFinite.ne]
      ring
    have hGnonneg : 0 ≤ G y - G x := by
      rw [hGdiff]
      exact ENNReal.toReal_nonneg
    have hGdist : dist (G y) (G x) = (∫⁻ v in Ixy, source v).toReal := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hGnonneg, hGdiff]
    have htsumBound := enorm_tsum_le_tsum_enorm
      (f := fun k => fp81s21_blockValue D Ixy k)
    have hJdist : dist (J y) (J x) ≤ (∫⁻ v in Ixy, source v).toReal := by
      rw [hJadd, dist_eq_norm, add_sub_cancel_left]
      have hnorm :
          ‖(∑' k, fp81s21_blockValue D Ixy k : projTensor (OscPath d m H) 2)‖ₑ ≤
            ∫⁻ v in Ixy, source v := htsumBound.trans hsumXYLeSource
      exact (ENNReal.toReal_mono hsourceXYFinite.ne hnorm).trans_eq (by
        simp [toReal_enorm'])
    rw [hGdist]
    exact hJdist
  have hmodulus : ∀ x ∈ Icc q0 T, ∀ y ∈ Icc q0 T,
      dist (J y) (J x) ≤ dist (G y) (G x) := by
    intro x hx y hy
    by_cases hxy : x ≤ y
    · exact hforward x hx y hy hxy
    · have hyx : y ≤ x := le_of_not_ge hxy
      have hrev := hforward y hy x hx hyx
      simpa [dist_comm] using hrev
  exact fp81s21_continuousOn_of_lintegral_modulus J source
    hsourceMeas hsourceFinite hmodulus

#print axioms fp81s21_window_covariance_cumulative
#print axioms fp81s21_window_covariance_cumulative_continuousOn

end HRS.Fp81.S21

end

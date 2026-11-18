import HRS.MS.Fp81S21CovMeasure3

/-!
# S2.1(iii), packet 16-close: cumulative interval variation

The cumulative block tsum has interval-local total-variation control by the
same weighted source density as the interval-value norm estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.FixEq

private theorem fp81s21_eVariationOn_le_of_increment_Icc
    {E : Type*} [NormedAddCommGroup E] {q s : ℝ}
    (hqs : q ≤ s) (F : ℝ → E) (Φ : ℝ → ℝ)
    (hΦ : MonotoneOn Φ (Icc q s))
    (hstep : ∀ x y, x ∈ Icc q s → y ∈ Icc q s → x ≤ y →
      ‖F y - F x‖ ≤ Φ y - Φ x) :
    eVariationOn F (Icc q s) ≤ ENNReal.ofReal (Φ s - Φ q) := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc
    ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i)) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (Φ (u (i + 1)) - Φ (u i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal
        (hstep _ _ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal
        (∑ i ∈ Finset.range n, (Φ (u (i + 1)) - Φ (u i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact sub_nonneg.mpr
        (hΦ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (Φ (u n) - Φ (u 0)) := by
      rw [Finset.sum_range_sub (fun i => Φ (u i))]
    _ ≤ ENNReal.ofReal (Φ s - Φ q) := by
      apply ENNReal.ofReal_le_ofReal
      have h1 := hΦ (hus n) (show s ∈ Icc q s from ⟨hqs, le_rfl⟩) (hus n).2
      have h2 := hΦ (show q ∈ Icc q s from ⟨le_rfl, hqs⟩) (hus 0) (hus 0).1
      linarith

private theorem fp81s21_window_covariance_source_lintegral_finite
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
    {u t : ℝ} (hu : 0 ≤ u) (ht : t ≤ a + H) :
    (∫⁻ v in Ioc u t,
      dualNormE r P (z v) * ENNReal.ofReal
        (Real.exp (-2 * cdec * max (a - v) 0))) < ∞ := by
  have hsum := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc u t) measurableSet_Ioc
    (fun k => hblocks (Ioc u t) measurableSet_Ioc k) hdual
  have hsubset : Ioc u t ⊆ Ioc (0 : ℝ) (a + H) := by
    intro v hv
    exact ⟨lt_of_le_of_lt hu hv.1, hv.2.trans ht⟩
  have hinter : Ioc u t ∩ Ioc (0 : ℝ) (a + H) = Ioc u t :=
    Set.inter_eq_left.mpr hsubset
  simpa [hinter] using hsum.2.2

/-- The cumulative covariance on `(q,·]` has interval-local total variation
bounded by the same weighted source density as the interval-value norm bound.
Here `K` is the displayed common finite constant; it depends on the fixed
coefficient and localization parameters, but not on `z`, `q`, `s`, or `a`.
Because `dualNormE` is ENNReal-valued, the source integral is a `lintegral`;
the second conjunct is its finite `toReal` form. -/
theorem fp81s21_window_covariance_cumulative_eVariationOn_le
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
    {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hs : s ≤ a + H) :
    let K : ℝ :=
      ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) * |2 * C.ν| *
        (s57pC d r P * ((d : ℝ) * 2 ^ r *
          (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))
    eVariationOn (fp81s21_window_covariance_cumulative D q) (Icc q s) ≤
        ENNReal.ofReal (K * (∫⁻ v in Ioc q s,
          dualNormE r P (z v) * ENNReal.ofReal
            (Real.exp (-2 * cdec * max (a - v) 0))).toReal) ∧
      (eVariationOn (fp81s21_window_covariance_cumulative D q) (Icc q s)).toReal ≤
        K * (∫⁻ v in Ioc q s,
          dualNormE r P (z v) * ENNReal.ofReal
            (Real.exp (-2 * cdec * max (a - v) 0))).toReal := by
  let A : ℝ := (3 + Real.sqrt H) ^ 2 * fp81s21_blockC0
  let B : ℝ := |2 * C.ν|
  let C0 : ℝ := s57pC d r P * ((d : ℝ) * 2 ^ r *
    (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2)
  let K : ℝ := A * B * C0
  let Kext : ℝ≥0∞ := ENNReal.ofReal K
  let w : ℝ → ℝ≥0∞ := fun v => dualNormE r P (z v) *
    ENNReal.ofReal (Real.exp (-2 * cdec * max (a - v) 0))
  let F : ℝ → projTensor (OscPath d m H) 2 :=
    fp81s21_window_covariance_cumulative D q
  let G : ℝ → ℝ := fun t => (∫⁻ v in Ioc q t, w v).toReal
  let Φ : ℝ → ℝ := fun t => K * G t
  have hA : 0 ≤ A := by
    dsimp [A]
    apply mul_nonneg
    · positivity
    · exact fp81s21_blockC0_nonneg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (s57pC_nonneg d r P) (by positivity)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hA hB) hC0
  have hKext : Kext < ∞ := by
    dsimp [Kext]
    exact ENNReal.ofReal_lt_top
  have hKreal : K = Kext.toReal := by
    simp [Kext, ENNReal.toReal_ofReal hK]
  have hfinite : ∀ t, t ∈ Icc q s →
      (∫⁻ v in Ioc q t, w v) < ∞ := by
    intro t ht
    have htUpper : t ≤ a + H := ht.2.trans hs
    have hfin := fp81s21_window_covariance_source_lintegral_finite
      D hlin hblocks hdual hq htUpper
    simpa [w] using hfin
  have hPhi : MonotoneOn Φ (Icc q s) := by
    intro x hx y hy hxy
    have hset : Ioc q x ⊆ Ioc q y := Ioc_subset_Ioc_right hxy
    have hlintegral : (∫⁻ v in Ioc q x, w v) ≤
        (∫⁻ v in Ioc q y, w v) := lintegral_mono_set hset
    have hreal := ENNReal.toReal_mono (hfinite y hy).ne hlintegral
    dsimp [Φ, G]
    exact mul_le_mul_of_nonneg_left hreal hK
  have hstep : ∀ x y, x ∈ Icc q s → y ∈ Icc q s → x ≤ y →
      ‖F y - F x‖ ≤ Φ y - Φ x := by
    intro x y hx hy hxy
    have hqx : q ≤ x := hx.1
    have hqy : q ≤ y := hy.1
    have hya : y ≤ a + H := hy.2.trans hs
    have hxyFin := fp81s21_window_covariance_source_lintegral_finite
      D hlin hblocks hdual (hq.trans hqx) hya
    have hqxFin := hfinite x hx
    have hqyFin := hfinite y hy
    have hsplit : (∫⁻ v in Ioc q y, w v) =
        (∫⁻ v in Ioc q x, w v) + (∫⁻ v in Ioc x y, w v) := by
      have hunion : Ioc q x ∪ Ioc x y = Ioc q y :=
        Set.Ioc_union_Ioc_eq_Ioc hqx hxy
      have hdisj : Disjoint (Ioc q x) (Ioc x y) :=
        Set.Ioc_disjoint_Ioc_of_le le_rfl
      rw [← hunion, lintegral_union measurableSet_Ioc hdisj]
    have hGdiff : G y - G x = (∫⁻ v in Ioc x y, w v).toReal := by
      dsimp [G]
      rw [hsplit, ENNReal.toReal_add hqxFin.ne hxyFin.ne]
      ring
    have hcumAdd : F y = F x + fp81s21_window_covariance_measure D x y := by
      change fp81s21_window_covariance_measure D q y = _
      exact fp81s21_window_covariance_measure_add D hlin hblocks hdual hqx hxy
    have hFinc : F y - F x = fp81s21_window_covariance_measure D x y := by
      rw [hcumAdd]
      abel
    have hsubset : Ioc x y ⊆ Ioc (0 : ℝ) (a + H) := by
      intro v hv
      exact ⟨lt_of_le_of_lt (hq.trans hqx) hv.1, hv.2.trans hya⟩
    have hinter : Ioc x y ∩ Ioc (0 : ℝ) (a + H) = Ioc x y :=
      Set.inter_eq_left.mpr hsubset
    have hbound := fp81s21_window_covariance_measure_norm_le D hlin hblocks
      hdual (hq.trans hqx) hxy hya
    have hconst :
        ENNReal.ofReal A * ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal C0 =
          ENNReal.ofReal K := by
      calc
        _ = ENNReal.ofReal ((A * |2 * C.ν|) * C0) := by
          rw [← ENNReal.ofReal_mul hA]
          rw [← ENNReal.ofReal_mul (mul_nonneg hA (abs_nonneg _))]
        _ = ENNReal.ofReal K := by
          congr 1
    have hbound' :
        ‖fp81s21_window_covariance_measure D x y‖ₑ ≤
          Kext * (∫⁻ v in Ioc x y, w v) := by
      calc
        _ ≤ (ENNReal.ofReal A * ENNReal.ofReal |2 * C.ν| *
            ENNReal.ofReal C0) * (∫⁻ v in Ioc x y, w v) := by
          simpa [A, C0, w] using hbound
        _ = Kext * (∫⁻ v in Ioc x y, w v) := by rw [hconst]
    have hrealBound := ENNReal.toReal_mono
      (ENNReal.mul_lt_top hKext hxyFin).ne hbound'
    have hnorm :
        ‖fp81s21_window_covariance_measure D x y‖ ≤
          Kext.toReal * (∫⁻ v in Ioc x y, w v).toReal := by
      simpa [toReal_enorm', ENNReal.toReal_mul, w] using hrealBound
    have hPhiDiff : Φ y - Φ x =
        K * (∫⁻ v in Ioc x y, w v).toReal := by
      dsimp [Φ]
      calc
        K * G y - K * G x = K * (G y - G x) := by ring
        _ = K * (∫⁻ v in Ioc x y, w v).toReal := by rw [hGdiff]
    calc
      ‖F y - F x‖ =
          ‖fp81s21_window_covariance_measure D x y‖ := by rw [hFinc]
      _ ≤ Kext.toReal * (∫⁻ v in Ioc x y, w v).toReal := hnorm
      _ = Φ y - Φ x := by
        calc
          Kext.toReal * (∫⁻ v in Ioc x y, w v).toReal =
              K * (∫⁻ v in Ioc x y, w v).toReal := by rw [← hKreal]
          _ = Φ y - Φ x := hPhiDiff.symm
  have hvar := fp81s21_eVariationOn_le_of_increment_Icc
    hqs F Φ hPhi hstep
  have hvar' : eVariationOn F (Icc q s) ≤
      ENNReal.ofReal (K * (∫⁻ v in Ioc q s, w v).toReal) := by
    calc
      _ ≤ ENNReal.ofReal (Φ s - Φ q) := hvar
      _ = ENNReal.ofReal (K * (∫⁻ v in Ioc q s, w v).toReal) := by
        simp [Φ, G]
  have hRhsFinite : ENNReal.ofReal
      (K * (∫⁻ v in Ioc q s, w v).toReal) < ∞ := ENNReal.ofReal_lt_top
  have hvarReal := ENNReal.toReal_mono hRhsFinite.ne hvar'
  rw [ENNReal.toReal_ofReal
    (mul_nonneg hK ENNReal.toReal_nonneg)] at hvarReal
  refine ⟨?_, ?_⟩
  · simpa [F, w, A, B, C0, K] using hvar'
  · simpa [F, w, A, B, C0, K] using hvarReal

#print axioms fp81s21_window_covariance_cumulative_eVariationOn_le

end HRS.Fp81.S21

end

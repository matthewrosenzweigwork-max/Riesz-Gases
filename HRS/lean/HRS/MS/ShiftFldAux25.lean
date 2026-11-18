import HRS.MS.ShiftFldAux24

/-!
# S79P: FTC for `r ↦ C(u_r, v_r)`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_gam_continuousOn (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} {u v : ℝ → Euc d → ℝ} (hu : GoodPath d s a β T u) (hv : GoodPath d s a β T v) :
    ContinuousOn (fun r => Gam d s a β (u r) (v r)) (Icc (0 : ℝ) T) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨B1u, hB1u⟩ := hu.bound1
  obtain ⟨B1v, hB1v⟩ := hv.bound1
  unfold Gam
  refine continuousOn_finset_sum _ fun i _ => ?_
  refine continuousOn_of_dominated (bound := fun x => thermalDensity d s a β x * (B1u * B1v))
    (fun r hr => ?_) (fun r hr => Filter.Eventually.of_forall fun x => ?_) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · have h1 := (D1_contDiff (hu.memCb r hr).1 i).continuous
    have h2 := (D1_contDiff (hv.memCb r hr).1 i).continuous
    exact (hT.smooth.continuous.mul (h1.mul h2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hT.prob.nonneg x), abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hB1u r hr i x) (hB1v r hr i x) (abs_nonneg _)
      ((abs_nonneg _).trans (hB1u r hr i x))) (hT.prob.nonneg x)
  · exact (HRS.MH.CoercLower.isProbDensity_integrable hT.prob).mul_const _
  · exact continuousOn_const.mul ((hu.cont1 i x).mul (hv.cont1 i x))

theorem s79g_FTC (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β)) {T : ℝ} (hT : 0 ≤ T)
    {u v : ℝ → Euc d → ℝ} (hu : GoodPath d s a β T u) (hv : GoodPath d s a β T v) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (u T) (v T) -
      HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (u 0) (v 0) =
      2 * β⁻¹ * ∫ r in (0 : ℝ)..T, Gam d s a β (u r) (v r) := by
  classical
  haveI := s79g_prob hd hs.le hsd ha hβ
  obtain ⟨K, hK⟩ := s79g_kdata hd hs.le hsd ha hβ
  have hint2 := s21_thermal_second_integrable hd hs.le hsd ha hβ
  obtain ⟨BLu, hBLu⟩ := hu.Lbound
  obtain ⟨BLv, hBLv⟩ := hv.Lbound
  obtain ⟨B0u, hB0u⟩ := hu.bound0
  obtain ⟨B0v, hB0v⟩ := hv.bound0
  have hIcc : ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) T → r ∈ Icc (0 : ℝ) T := fun h => Ioo_subset_Icc_self h
  have hmemU : ∀ r ∈ Icc (0 : ℝ) T, MemLp (u r) 2 (thermalMeasure d s a β) := fun r hr =>
    s79g_memLp_lin hd hs.le hsd ha hβ (hu.memCb r hr).1.continuous (K := B0u)
      (fun x => s79g_lin_of_le (hB0u r hr x) x)
  have hmemV : ∀ r ∈ Icc (0 : ℝ) T, MemLp (v r) 2 (thermalMeasure d s a β) := fun r hr =>
    s79g_memLp_lin hd hs.le hsd ha hβ (hv.memCb r hr).1.continuous (K := B0v)
      (fun x => s79g_lin_of_le (hB0v r hr x) x)
  have hmemLU : ∀ r ∈ Icc (0 : ℝ) T, MemLp (generatorW (Cst d s a β) 0 (u r)) 2 (thermalMeasure d s a β) := fun r hr =>
    s79g_memLp_lin hd hs.le hsd ha hβ (hu.Lcont r hr) (K := BLu) (hBLu r hr)
  have hmemLV : ∀ r ∈ Icc (0 : ℝ) T, MemLp (generatorW (Cst d s a β) 0 (v r)) 2 (thermalMeasure d s a β) := fun r hr =>
    s79g_memLp_lin hd hs.le hsd ha hβ (hv.Lcont r hr) (K := BLv) (hBLv r hr)
  have hnegU : ∀ r ∈ Icc (0 : ℝ) T,
      MemLp (fun x => -(generatorW (Cst d s a β) 0 (u r) x)) 2 (thermalMeasure d s a β) :=
    fun r hr => (hmemLU r hr).neg
  have hnegV : ∀ r ∈ Icc (0 : ℝ) T,
      MemLp (fun x => -(generatorW (Cst d s a β) 0 (v r) x)) 2 (thermalMeasure d s a β) :=
    fun r hr => (hmemLV r hr).neg
  -- the Lp paths
  let Fu : ℝ → Lp ℝ 2 (thermalMeasure d s a β) := fun r => if h : MemLp (u r) 2 (thermalMeasure d s a β) then h.toLp (u r) else 0
  let Fv : ℝ → Lp ℝ 2 (thermalMeasure d s a β) := fun r => if h : MemLp (v r) 2 (thermalMeasure d s a β) then h.toLp (v r) else 0
  let Gu : ℝ → Lp ℝ 2 (thermalMeasure d s a β) := fun r => if h : MemLp (fun x => -(generatorW (Cst d s a β) 0 (u r) x)) 2 (thermalMeasure d s a β)
    then h.toLp _ else 0
  let Gv : ℝ → Lp ℝ 2 (thermalMeasure d s a β) := fun r => if h : MemLp (fun x => -(generatorW (Cst d s a β) 0 (v r) x)) 2 (thermalMeasure d s a β)
    then h.toLp _ else 0
  have hFu : ∀ r ∈ Icc (0 : ℝ) T, (Fu r : Euc d → ℝ) =ᵐ[(thermalMeasure d s a β)] u r := fun r hr => by
    simp only [Fu, dif_pos (hmemU r hr)]; exact MemLp.coeFn_toLp _
  have hFv : ∀ r ∈ Icc (0 : ℝ) T, (Fv r : Euc d → ℝ) =ᵐ[(thermalMeasure d s a β)] v r := fun r hr => by
    simp only [Fv, dif_pos (hmemV r hr)]; exact MemLp.coeFn_toLp _
  have hGu : ∀ r ∈ Icc (0 : ℝ) T, (Gu r : Euc d → ℝ) =ᵐ[(thermalMeasure d s a β)] fun x => -(generatorW (Cst d s a β) 0 (u r) x) :=
    fun r hr => by simp only [Gu, dif_pos (hnegU r hr)]; exact MemLp.coeFn_toLp _
  have hGv : ∀ r ∈ Icc (0 : ℝ) T, (Gv r : Euc d → ℝ) =ᵐ[(thermalMeasure d s a β)] fun x => -(generatorW (Cst d s a β) 0 (v r) x) :=
    fun r hr => by simp only [Gv, dif_pos (hnegV r hr)]; exact MemLp.coeFn_toLp _
  set R : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β) := (S45.s45_Rr hK hβ.le).toContinuousLinearMap with hR
  set Pc := HRS.Whole.Q34.Pc (thermalMeasure d s a β) with hPc
  let Φ : ℝ → ℝ := fun r => ⟪Pc (Fu r), R (Pc (Fv r))⟫
  -- identification with the covariance
  have hΦcov : ∀ r ∈ Icc (0 : ℝ) T, HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (u r) (v r) = Φ r := by
    intro r hr
    rw [S45.s45_susceptibilityCov_eq hK hβ (hmemU r hr) (hmemV r hr), s79g_U_eq_Pc, s79g_U_eq_Pc]
    simp only [Φ, Fu, Fv, dif_pos (hmemU r hr), dif_pos (hmemV r hr), hR]
    rfl
  -- continuity of Φ
  have hcontLp : ∀ {w : ℝ → Euc d → ℝ} {B0 : ℝ} {F : ℝ → Lp ℝ 2 (thermalMeasure d s a β)}, (∀ x, ContinuousOn (fun r => w r x) (Icc (0 : ℝ) T)) →
      (∀ r ∈ Icc (0 : ℝ) T, ∀ x, |w r x| ≤ B0) → (∀ r ∈ Icc (0 : ℝ) T, (F r : Euc d → ℝ) =ᵐ[(thermalMeasure d s a β)] w r) →
      ContinuousOn F (Icc (0 : ℝ) T) := by
    intro w B0 F hc hB hF r₀ hr₀
    exact s79g_lp_continuousWithinAt hint2 hc (B := B0) (fun r hr x => s79g_lin_of_le (hB r hr x) x) hF hr₀
  have hFuc := hcontLp hu.cont0 hB0u hFu
  have hFvc := hcontLp hv.cont0 hB0v hFv
  have hΦc : ContinuousOn Φ (Icc (0 : ℝ) T) := by
    have h1 : ContinuousOn (fun r => Pc (Fu r)) (Icc (0 : ℝ) T) := Pc.continuous.comp_continuousOn hFuc
    have h2 : ContinuousOn (fun r => R (Pc (Fv r))) (Icc (0 : ℝ) T) :=
      R.continuous.comp_continuousOn (Pc.continuous.comp_continuousOn hFvc)
    exact h1.inner h2
  -- derivative
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) T, HasDerivAt Φ (2 * β⁻¹ * Gam d s a β (u r) (v r)) r := by
    intro r hr
    have hδ : 0 < min r (T - r) := lt_min hr.1 (by linarith [hr.2])
    have hball : ball r (min r (T - r)) ⊆ Ioo (0 : ℝ) T := by
      intro y hy
      rw [mem_ball, Real.dist_eq] at hy
      have h1 := (abs_lt.1 (lt_of_lt_of_le hy (min_le_left _ _)))
      have h2 := (abs_lt.1 (lt_of_lt_of_le hy (min_le_right _ _)))
      exact ⟨by linarith [h1.1], by linarith [h2.2]⟩
    have hFu' : HasDerivAt Fu (Gu r) r := by
      refine s79g_lp_hasDerivAt hint2 (f := u) (D := fun r x => -(generatorW (Cst d s a β) 0 (u r) x))
        (B := BLu) hδ (fun x r' hr' => hu.deriv x r' (hball hr')) (fun r' hr' x => ?_)
        (fun r' hr' => hFu r' (hIcc (hball hr'))) (hGu r (hIcc hr))
      rw [abs_neg]; exact hBLu r' (hIcc (hball hr')) x
    have hFv' : HasDerivAt Fv (Gv r) r := by
      refine s79g_lp_hasDerivAt hint2 (f := v) (D := fun r x => -(generatorW (Cst d s a β) 0 (v r) x))
        (B := BLv) hδ (fun x r' hr' => hv.deriv x r' (hball hr')) (fun r' hr' x => ?_)
        (fun r' hr' => hFv r' (hIcc (hball hr'))) (hGv r (hIcc hr))
      rw [abs_neg]; exact hBLv r' (hIcc (hball hr')) x
    have hE1 : HasDerivAt (fun r => Pc (Fu r)) (Pc (Gu r)) r := Pc.hasFDerivAt.comp_hasDerivAt r hFu'
    have hE2 : HasDerivAt (fun r => R (Pc (Fv r))) (R (Pc (Gv r))) r :=
      R.hasFDerivAt.comp_hasDerivAt r (Pc.hasFDerivAt.comp_hasDerivAt r hFv')
    have hI := hE1.inner ℝ hE2
    convert hI using 1
    -- value of the derivative
    have hr' := hIcc hr
    have hc1 : ⟪Pc (Gu r), R (Pc (Fv r))⟫ =
        HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (fun x => -(generatorW (Cst d s a β) 0 (u r) x)) (v r) := by
      rw [S45.s45_susceptibilityCov_eq hK hβ (hnegU r hr') (hmemV r hr'), s79g_U_eq_Pc, s79g_U_eq_Pc]
      simp only [Gu, Fv, dif_pos (hnegU r hr'), dif_pos (hmemV r hr'), hR]
      rfl
    have hc2 : ⟪Pc (Fu r), R (Pc (Gv r))⟫ =
        HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (u r) (fun x => -(generatorW (Cst d s a β) 0 (v r) x)) := by
      rw [S45.s45_susceptibilityCov_eq hK hβ (hmemU r hr') (hnegV r hr'), s79g_U_eq_Pc, s79g_U_eq_Pc]
      simp only [Gv, Fu, dif_pos (hnegV r hr'), dif_pos (hmemU r hr'), hR]
      rfl
    have hlyap := s79g_lyap hd hs hsd ha hβ hρ (hu.memCb r hr') (hv.memCb r hr') (hu.Lcont r hr')
      ⟨BLu, hBLu r hr'⟩ (hv.Lcont r hr') ⟨BLv, hBLv r hr'⟩
    rw [hc1, hc2, s79g_cov_neg_left hK hβ (hmemLU r hr') (hmemV r hr'),
      s79g_cov_neg_right hK hβ (hmemU r hr') (hmemLV r hr')]
    linarith
  have hint : IntervalIntegrable (fun r => 2 * β⁻¹ * Gam d s a β (u r) (v r)) volume 0 T :=
    (continuousOn_const.mul (s79g_gam_continuousOn hd hs.le hsd ha hβ hu hv)).intervalIntegrable_of_Icc hT
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hΦc hderiv hint
  rw [hΦcov T ⟨hT, le_rfl⟩, hΦcov 0 ⟨le_rfl, hT⟩, ← hftc, intervalIntegral.integral_const_mul]

end HRS.MS.S79G

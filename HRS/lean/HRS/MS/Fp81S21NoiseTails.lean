import HRS.MS.Fp81S21MovingNoiseBounds2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.CovMeas

private def fp81s21_noiseTailsClipTime (H : ℝ) (hH : 0 < H) (r : ℝ) : Icc (0 : ℝ) H :=
  ⟨max 0 (min r H), ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩⟩

private theorem fp81s21_noiseTailsClipTime_continuous {H : ℝ} (hH : 0 < H) :
    Continuous (fp81s21_noiseTailsClipTime H hH) := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun r => ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩)

private theorem fp81s21_noiseTailsClipTime_eq
    {H u t r : ℝ} (hH : 0 < H)
    (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hr : r ∈ Icc u t) :
    fp81s21_noiseTailsClipTime H hH r = ⟨r, ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩⟩ := by
  apply Subtype.ext
  change max 0 (min r H) = r
  rw [min_eq_left (hr.2.trans ht.2), max_eq_right (hu.1.trans hr.1)]

/-- The existing orbit envelope bounds each moving-noise Hermite coordinate.
The cutoff and endpoint occur after the common S101 profile. -/
theorem fp81s21_movingNoiseCoordinate_sq_bound_of_S101Data
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {c : MultiIndex p.d → ℝ}
    (hD : HRS.MS.CovMeas.S101Data (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8) c)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hut : u ≤ t)
    (α : MultiIndex p.d) :
    ‖movingNoiseCoordinate R u t α‖ ^ 2 ≤
      (2 * p.β⁻¹) * H * c α ^ 2 := by
  classical
  let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let μprod : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let K : ℝ := (2 * p.β⁻¹) * c α ^ 2
  let env : ℝ × Euc p.d → ℝ := fun q =>
    if q.1 ∈ Icc u t then
      K * R.ρ (fp81s21_noiseTailsClipTime H hH q.1) q.2 else 0
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    HRS.MS.GenPath.s56_isOscTest _ α
  have hmem := (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu t ht φ hφ
  have hρjoint := fp81s21_moving_density_joint_meas (H := H) p R hδ hδhalf
  have hρclip : Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_noiseTailsClipTime H hH q.1) q.2) := by
    have htime : Continuous fun q : ℝ × Euc p.d =>
        fp81s21_noiseTailsClipTime H hH q.1 :=
      (fp81s21_noiseTailsClipTime_continuous hH).comp continuous_fst
    have hmap : Continuous fun q : ℝ × Euc p.d =>
        (fp81s21_noiseTailsClipTime H hH q.1, q.2) := htime.prodMk continuous_snd
    exact hρjoint.comp hmap.measurable
  have henvMeas : Measurable env := by
    apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    · exact measurable_const.mul hρclip
    · exact measurable_const
  have hρnonneg : ∀ q : ℝ × Euc p.d,
      0 ≤ R.ρ (fp81s21_noiseTailsClipTime H hH q.1) q.2 := by
    intro q
    exact (R.resulting.global H).density
      (fp81s21_noiseTailsClipTime H hH q.1).1
      ⟨(fp81s21_noiseTailsClipTime H hH q.1).2.1,
        (fp81s21_noiseTailsClipTime H hH q.1).2.2⟩ |>.nonneg q.2
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
      (sq_nonneg (c α))
  have henvSect : ∀ᵐ r ∂(volume : Measure ℝ),
      Integrable (fun x : Euc p.d => env (r, x)) (volume : Measure (Euc p.d)) := by
    filter_upwards with r
    by_cases hr : r ∈ Icc u t
    · have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩
      have hρr := (R.resulting.global H).density r hrH
      have hρi : Integrable (R.ρ r) :=
        HRS.Whole.Q34.integrable_of_isProbDensity hρr
      have hclip := fp81s21_noiseTailsClipTime_eq hH hu ht hr
      have hclip' : (fp81s21_noiseTailsClipTime H hH r : ℝ) = r :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have heq : (fun x : Euc p.d => env (r, x)) = fun x => K * R.ρ r x := by
        funext x
        simp [env, Set.mem_Icc, hr.1, hr.2, hclip']
      rw [heq]
      exact hρi.const_mul K
    · have heq : (fun x : Euc p.d => env (r, x)) = fun _ => 0 := by
        funext x
        have hr' : ¬ (u ≤ r ∧ r ≤ t) := by simpa only [Set.mem_Icc] using hr
        simp [env, Set.mem_Icc, hr']
      rw [heq]
      simpa using (integrable_zero : Integrable (fun _ : Euc p.d => (0 : ℝ)) volume)
  have henvRowVal : ∀ r : ℝ,
      (∫ x : Euc p.d, env (r, x)) = (Icc u t).indicator (fun _ : ℝ => K) r := by
    intro r
    by_cases hr : r ∈ Icc u t
    · have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩
      have hρr := (R.resulting.global H).density r hrH
      have hclip := fp81s21_noiseTailsClipTime_eq hH hu ht hr
      have hclip' : (fp81s21_noiseTailsClipTime H hH r : ℝ) = r :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have heq : (fun x : Euc p.d => env (r, x)) = fun x => K * R.ρ r x := by
        funext x
        simp [env, Set.mem_Icc, hr.1, hr.2, hclip']
      rw [heq, Set.indicator_of_mem hr, integral_const_mul, hρr.integral_one]
      simp [K]
    · have hr' : ¬ (u ≤ r ∧ r ≤ t) := by simpa only [Set.mem_Icc] using hr
      simp [env, Set.indicator, Set.mem_Icc, hr']
  have henvRow : ∀ r : ℝ,
      (∫ x : Euc p.d, ‖env (r, x)‖) = (Icc u t).indicator (fun _ : ℝ => K) r := by
    intro r
    have hnonneg : ∀ x, 0 ≤ env (r, x) := by
      intro x
      by_cases hr : r ∈ Icc u t
      · simp only [env, Set.mem_Icc, hr.1, hr.2, ite_true]
        exact mul_nonneg hK0 (hρnonneg (r, x))
      · have hr' : ¬ (u ≤ r ∧ r ≤ t) := by simpa only [Set.mem_Icc] using hr
        simp [env, Set.mem_Icc, hr']
    calc
      _ = ∫ x : Euc p.d, env (r, x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (hnonneg x)
      _ = (Icc u t).indicator (fun _ : ℝ => K) r := henvRowVal r
  have hrowInt : Integrable
      (fun r : ℝ => ∫ x : Euc p.d, ‖env (r, x)‖) (volume : Measure ℝ) := by
    have hindicator : Integrable ((Icc u t).indicator (fun _ : ℝ => K))
        (volume : Measure ℝ) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (measure_Icc_lt_top.ne)
    have heq : (fun r : ℝ => ∫ x : Euc p.d, ‖env (r, x)‖) =
        (Icc u t).indicator (fun _ : ℝ => K) := funext henvRow
    rw [heq]
    exact hindicator
  have henvInt : Integrable env μprod :=
    (integrable_prod_iff henvMeas.aestronglyMeasurable).2 ⟨henvSect, hrowInt⟩
  let sq : ℝ × Euc p.d → ℝ := fun q => ‖movingNoiseKernel R u t φ q‖ ^ 2
  have hsqInt : Integrable sq μprod := by
    exact hmem.integrable_norm_pow (by norm_num)
  have hsol := R.resulting.global H
  have hsqBound : ∀ q : ℝ × Euc p.d, sq q ≤ env q := by
    intro q
    by_cases hq : q.1 ∈ Icc u t
    · have hqH : q.1 ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hq.1, hq.2.trans ht.2⟩
      have hρq := hsol.density q.1 hqH
      have hclip := fp81s21_noiseTailsClipTime_eq hH hu ht hq
      have hclip' : (fp81s21_noiseTailsClipTime H hH q.1 : ℝ) = q.1 :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have hgrad := hD.bddU α q.1 hqH t ⟨hq.2, ht.2⟩ 1 (by omega) q.2
      have hgrad' : ‖gradient (r26t3_U R q.1 t φ) q.2‖ ≤ c α := by
        rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
        simpa [r26t3_U, φ] using hgrad
      have hgradSq : ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 ≤ c α ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hgrad' 2
      have hfactor : (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) ^ 2 =
          (2 * p.β⁻¹) * R.ρ q.1 q.2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num)
          (inv_nonneg.mpr p.hβ.le)), Real.sq_sqrt (hρq.nonneg q.2)]
      have hnorm :
          ‖(Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 =
              ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
                ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 := by
        calc
          _ = (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) ^ 2 *
                ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 := by
              rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          _ = _ := by rw [hfactor]
      have hcoeff : 0 ≤ (2 * p.β⁻¹) * R.ρ q.1 q.2 :=
        mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
          (hρq.nonneg q.2)
      have hbound :
          ‖(Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 ≤ K * R.ρ q.1 q.2 := by
        rw [hnorm]
        calc
          ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
            ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 ≤
            ((2 * p.β⁻¹) * R.ρ q.1 q.2) * c α ^ 2 :=
              mul_le_mul_of_nonneg_left hgradSq hcoeff
          _ = K * R.ρ q.1 q.2 := by dsimp [K]; ring
      change ‖(if q.1 ∈ Icc u t then
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2 else 0)‖ ^ 2 ≤
        (if q.1 ∈ Icc u t then
          K * R.ρ (fp81s21_noiseTailsClipTime H hH q.1) q.2 else 0)
      rw [if_pos hq, if_pos hq, hclip']
      exact hbound
    · have hq' : ¬ (u ≤ q.1 ∧ q.1 ≤ t) := by simpa only [Set.mem_Icc] using hq
      change ‖(if q.1 ∈ Icc u t then
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2 else 0)‖ ^ 2 ≤
        (if q.1 ∈ Icc u t then
          K * R.ρ (fp81s21_noiseTailsClipTime H hH q.1) q.2 else 0)
      rw [if_neg hq, if_neg hq]
      simp
  have hfeatureAE :
      (movingNoiseFeature R u t φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μprod]
        movingNoiseKernel R u t φ := by
    rw [movingNoiseFeature, dif_pos hmem]
    exact hmem.coeFn_toLp
  have hnormIntegral : ‖movingNoiseCoordinate R u t α‖ ^ 2 =
      ∫ q, sq q ∂μprod := by
    change ‖movingNoiseFeature R u t φ‖ ^ 2 = ∫ q, sq q ∂μprod
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hfun : (fun q => inner ℝ
        ((movingNoiseFeature R u t φ : ℝ × Euc p.d → Euc p.d) q)
        ((movingNoiseFeature R u t φ : ℝ × Euc p.d → Euc p.d) q)) =ᵐ[μprod]
          sq := by
      filter_upwards [hfeatureAE] with q hq
      simp [sq, hq, real_inner_self_eq_norm_sq]
    rw [integral_congr_ae hfun]
  have hcompare : ∫ q, sq q ∂μprod ≤ ∫ q, env q ∂μprod :=
    integral_mono hsqInt henvInt hsqBound
  have henvIntegral : ∫ q, env q ∂μprod = K * (t - u) := by
    rw [integral_prod env henvInt]
    simp_rw [henvRowVal]
    rw [integral_indicator (measurableSet_Icc), integral_const]
    simp [Measure.real, Real.volume_Icc, sub_nonneg.2 hut,
      mul_comm, mul_left_comm, mul_assoc]
  rw [hnormIntegral]
  calc
    _ ≤ K * (t - u) := by
      calc
        _ ≤ ∫ q, env q ∂μprod := hcompare
        _ = K * (t - u) := henvIntegral
    _ ≤ (2 * p.β⁻¹) * H * c α ^ 2 := by
      dsimp [K]
      have htu : t - u ≤ H := by linarith [hu.1, ht.2]
      have hcoef : 0 ≤ (2 * p.β⁻¹) * c α ^ 2 := by positivity
      nlinarith

/-- Starting the forcing interval at zero dominates every later cutoff. -/
theorem fp81s21_movingNoiseCoordinate_norm_le_zero_of_cutoff
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex p.d) :
    ‖movingNoiseCoordinate R u t α‖ ≤ ‖movingNoiseCoordinate R 0 t α‖ := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let f := movingNoiseKernel R u t φ
  let g := movingNoiseKernel R 0 t φ
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    HRS.MS.GenPath.s56_isOscTest _ α
  have hmemF := (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu t ht φ hφ
  have hmemG := (movingNoiseFeature_spec p R hδ hδhalf hH).1 0
    ⟨le_rfl, hH.le⟩ t ht φ hφ
  have hpoint : ∀ q : ℝ × Euc p.d, ‖f q‖ ≤ ‖g q‖ := by
    intro q
    by_cases hq : q.1 ∈ Icc u t
    · have hq0 : q.1 ∈ Icc (0 : ℝ) t := ⟨hu.1.trans hq.1, hq.2⟩
      simp [f, g, movingNoiseKernel, hq, hq0]
    · simp [f, g, movingNoiseKernel, hq]
  have hLp : eLpNorm f 2 μ ≤ eLpNorm g 2 μ :=
    eLpNorm_mono_ae hmemF.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hnormF : ‖movingNoiseFeature R u t φ‖ = (eLpNorm f 2 μ).toReal := by
    rw [movingNoiseFeature, dif_pos hmemF, Lp.norm_toLp]
  have hnormG : ‖movingNoiseFeature R 0 t φ‖ = (eLpNorm g 2 μ).toReal := by
    rw [movingNoiseFeature, dif_pos hmemG, Lp.norm_toLp]
  change ‖movingNoiseFeature R u t φ‖ ≤ ‖movingNoiseFeature R 0 t φ‖
  rw [hnormF, hnormG]
  exact ENNReal.toReal_mono hmemG.eLpNorm_ne_top hLp

#print axioms fp81s21_movingNoiseCoordinate_sq_bound_of_S101Data
#print axioms fp81s21_movingNoiseCoordinate_norm_le_zero_of_cutoff

end HRS.Fp81.S21

end

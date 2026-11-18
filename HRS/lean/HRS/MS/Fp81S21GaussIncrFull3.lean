import HRS.MS.Fp81S21GaussIncrFull2

/-!
# HRS S2.1(iii), SOL71 G2: full noise-feature increment

The old and new noise-time regions are estimated separately in the actual
space-time L² feature.  The old region uses the product of the G1 terminal
Lipschitz and decay bounds; the new region uses gradient decay directly.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr

private def fp81s21_gaussianNoiseClipTime (T : ℝ) (hT : 0 < T) (r : ℝ) :
    Set.Icc (0 : ℝ) T :=
  ⟨max 0 (min r T), ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩⟩

private theorem fp81s21_gaussianNoiseClipTime_continuous {T : ℝ} (hT : 0 < T) :
    Continuous (fp81s21_gaussianNoiseClipTime T hT) := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun r => ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩)

private theorem fp81s21_gaussianNoiseClipTime_eq
    {T r : ℝ} (hT : 0 < T) (hr : r ∈ Icc (0 : ℝ) T) :
    fp81s21_gaussianNoiseClipTime T hT r = ⟨r, hr⟩ := by
  apply Subtype.ext
  change max 0 (min r T) = r
  rw [min_eq_left hr.2, max_eq_right hr.1]

private theorem fp81s21_gaussianNoise_exp_integral_le
    {c v : ℝ} (hc : 0 < c) (hv : 0 ≤ v) :
    ∫ r in Icc (0 : ℝ) v, Real.exp (-c * (v - r)) ≤ c⁻¹ := by
  let F : ℝ → ℝ := fun r => Real.exp (-c * (v - r)) / c
  have hder : ∀ r ∈ Set.uIcc (0 : ℝ) v,
      HasDerivAt F (Real.exp (-c * (v - r))) r := by
    intro r _
    have harg : HasDerivAt (fun r : ℝ => -c * (v - r)) c r := by
      have hbase : HasDerivAt (fun z : ℝ => v - z) (-1) r := by
        convert (hasDerivAt_const r v).sub (hasDerivAt_id r) using 1
        · funext z
          simp
        · ring
      convert hbase.const_mul (-c) using 1 <;> ring
    have hexp := harg.exp
    convert hexp.div_const c using 1 <;> field_simp [ne_of_gt hc] <;> ring
  have hcont : Continuous (fun r : ℝ => Real.exp (-c * (v - r))) := by
    fun_prop
  have hint : IntervalIntegrable (fun r : ℝ => Real.exp (-c * (v - r))) volume 0 v :=
    hcont.intervalIntegrable 0 v
  have hEq :
      (∫ r in Icc (0 : ℝ) v, Real.exp (-c * (v - r))) =
        ∫ r in (0 : ℝ)..v, Real.exp (-c * (v - r)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv]
  have hpos : 0 ≤ Real.exp (-c * v) / c :=
    div_nonneg (Real.exp_pos _).le hc.le
  have hEval : F v - F 0 = 1 / c - Real.exp (-c * v) / c := by
    simp [F, sub_self, sub_zero, mul_zero]
  calc
    ∫ r in Icc (0 : ℝ) v, Real.exp (-c * (v - r)) = F v - F 0 := by
      rw [hEq, intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
    _ = 1 / c - Real.exp (-c * v) / c := hEval
    _ ≤ 1 / c := by linarith
    _ = c⁻¹ := by simp [one_div]

/-- The noise feature itself has a start-uniform linear increment bound.  The
constants are selected after `R`, before the two physical times and the mode. -/
theorem fp81s21_gaussian_noise_feature_increment_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ g g' c gN cN : ℝ, 0 ≤ g ∧ 0 ≤ g' ∧ 0 < c ∧
          0 ≤ gN ∧ 0 < cN ∧
          ∀ v w : ℝ, 0 ≤ v → v ≤ w → ∀ α : MultiIndex p.d,
            ‖movingNoiseFeature R 0 w
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
              movingNoiseFeature R 0 v
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 ≤
              2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) *
                (s104_b p.d α) ^ 2 * (w - v) := by
  obtain ⟨δo, hδo, hδohalf, hold⟩ :=
    fp81s21_gaussian_old_noise_gradient_sq_bound p
  obtain ⟨δd, hδd, hδdhalf, hdecay⟩ :=
    fp81s21_gauss_incr_gradient_decay p
  let δ0 := min δo δd
  have hδ0 : 0 < δ0 := lt_min hδo hδd
  have hδ0half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hδohalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδoR := hδle.trans (min_le_left _ _)
  have hδdR := hδle.trans (min_le_right _ _)
  obtain ⟨g, g', c, hg, hg', hc, holdR⟩ := hold δ hδ hδoR R
  obtain ⟨gN, cN, hgN, hcN, hdecayR⟩ := hdecay δ hδ hδdR R
  refine ⟨g, g', c, gN, cN, hg, hg', hc, hgN, hcN, ?_⟩
  intro v w hv hvw α
  let T := w + 1
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let f : ℝ × Euc p.d → Euc p.d := movingNoiseKernel R 0 w φ
  let gfun : ℝ × Euc p.d → Euc p.d := movingNoiseKernel R 0 v φ
  let diff : ℝ × Euc p.d → Euc p.d := fun q => f q - gfun q
  let b := s104_b p.d α
  let Aold := 4 * p.β⁻¹ * g * g' * b ^ 2 * (w - v)
  let Anew := 2 * p.β⁻¹ * gN ^ 2 * b ^ 2
  let ρclip : ℝ × Euc p.d → ℝ := fun q =>
    R.ρ (fp81s21_gaussianNoiseClipTime T (by dsimp [T]; linarith) q.1) q.2
  let env : ℝ × Euc p.d → ℝ := fun q =>
    if q.1 ∈ Icc (0 : ℝ) v then
      Aold * Real.exp (-c * (v - q.1)) * ρclip q
    else if q.1 ∈ Ioc v w then Anew * ρclip q else 0
  let sq : ℝ × Euc p.d → ℝ := fun q => ‖diff q‖ ^ 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hvT : v ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith
  have hwT : w ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    HRS.MS.GenPath.s56_isOscTest _ α
  have hmemW := (movingNoiseFeature_spec p R hδ
    (hδle.trans hδ0half) hT).1 0 ⟨le_rfl, hT.le⟩ w hwT φ hφ
  have hmemV := (movingNoiseFeature_spec p R hδ
    (hδle.trans hδ0half) hT).1 0 ⟨le_rfl, hT.le⟩ v hvT φ hφ
  have hdiffMem : MemLp diff 2 μ := by
    dsimp [diff, f, gfun, μ]
    exact hmemW.sub hmemV
  have hsqInt : Integrable sq μ := by
    dsimp [sq]
    exact hdiffMem.integrable_norm_pow (by norm_num)
  have hfeatureW : (movingNoiseFeature R 0 w φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ] f := by
    dsimp [f, μ]
    rw [movingNoiseFeature, dif_pos hmemW]
    exact hmemW.coeFn_toLp
  have hfeatureV : (movingNoiseFeature R 0 v φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ] gfun := by
    dsimp [gfun, μ]
    rw [movingNoiseFeature, dif_pos hmemV]
    exact hmemV.coeFn_toLp
  have hsubAE :
      (fun q : ℝ × Euc p.d =>
        (movingNoiseFeature R 0 w φ - movingNoiseFeature R 0 v φ) q) =ᵐ[μ] diff := by
    filter_upwards [Lp.coeFn_sub (movingNoiseFeature R 0 w φ)
        (movingNoiseFeature R 0 v φ), hfeatureW, hfeatureV] with q hsub hW hV
    rw [hsub, Pi.sub_apply, hW, hV]
  have hnormIntegral :
      ‖movingNoiseFeature R 0 w φ - movingNoiseFeature R 0 v φ‖ ^ 2 =
        ∫ q, sq q ∂μ := by
    calc
      _ = inner ℝ (movingNoiseFeature R 0 w φ - movingNoiseFeature R 0 v φ)
          (movingNoiseFeature R 0 w φ - movingNoiseFeature R 0 v φ) :=
            (real_inner_self_eq_norm_sq _).symm
      _ = ∫ q, inner ℝ
          ((movingNoiseFeature R 0 w φ - movingNoiseFeature R 0 v φ) q)
          ((movingNoiseFeature R 0 w φ - movingNoiseFeature R 0 v φ) q) ∂μ := by
            rw [L2.inner_def]
      _ = ∫ q, sq q ∂μ := by
        apply integral_congr_ae
        filter_upwards [hsubAE] with q hq
        rw [hq]
        simp [sq, diff, real_inner_self_eq_norm_sq]
  have hclipMeas : Measurable ρclip := by
    dsimp [ρclip]
    have hjoint := fp81s21_moving_density_joint_meas (H := T) p R hδ
      (hδle.trans hδ0half)
    have htime : Continuous (fp81s21_gaussianNoiseClipTime T hT) :=
      fp81s21_gaussianNoiseClipTime_continuous hT
    have hmap : Continuous (fun q : ℝ × Euc p.d =>
        (fp81s21_gaussianNoiseClipTime T hT q.1, q.2)) :=
      (htime.comp continuous_fst).prodMk continuous_snd
    exact hjoint.comp hmap.measurable
  have hOldWeightMeas : Measurable (fun r : ℝ =>
      Aold * Real.exp (-c * (v - r))) := by fun_prop
  have henvMeas : Measurable env := by
    dsimp [env]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_fst)
      (hOldWeightMeas.comp measurable_fst |>.mul hclipMeas)
      (Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
        (measurable_const.mul hclipMeas) measurable_const)
  have hsol := R.resulting.global T
  have hρnn : ∀ q : ℝ × Euc p.d, 0 ≤ ρclip q := by
    intro q
    exact (hsol.density
      (fp81s21_gaussianNoiseClipTime T hT q.1).1
      (fp81s21_gaussianNoiseClipTime T hT q.1).2).nonneg q.2
  have hdiff0 : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hAold0 : 0 ≤ Aold := by
    dsimp [Aold]
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)
          · exact hg
        · exact hg'
      · exact sq_nonneg b
    · exact hdiff0
  have hAnew0 : 0 ≤ Anew := by
    dsimp [Anew]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)
      · exact sq_nonneg gN
    · exact sq_nonneg b
  have henvNonneg : ∀ q : ℝ × Euc p.d, 0 ≤ env q := by
    intro q
    by_cases hrOld : q.1 ∈ Icc (0 : ℝ) v
    · simp only [env, if_pos hrOld]
      exact mul_nonneg (mul_nonneg hAold0 (Real.exp_pos _).le) (hρnn q)
    · by_cases hrNew : q.1 ∈ Ioc v w
      · simp only [env, if_neg hrOld, if_pos hrNew]
        exact mul_nonneg hAnew0 (hρnn q)
      · have hnotOld : ¬ (0 ≤ q.1 ∧ q.1 ≤ v) := by
          simpa only [Set.mem_Icc] using hrOld
        have hnotNew : ¬ (v < q.1 ∧ q.1 ≤ w) := by
          simpa only [Set.mem_Ioc] using hrNew
        simp [env, Set.mem_Icc, Set.mem_Ioc, hnotOld, hnotNew]
  have hclipEq : ∀ r, r ∈ Icc (0 : ℝ) T →
      (fp81s21_gaussianNoiseClipTime T hT r : ℝ) = r := by
    intro r hr
    exact congrArg (fun z : Icc (0 : ℝ) T => (z : ℝ))
      (fp81s21_gaussianNoiseClipTime_eq hT hr)
  have henvSect : ∀ᵐ r ∂(volume : Measure ℝ),
      Integrable (fun x : Euc p.d => env (r, x)) (volume : Measure (Euc p.d)) := by
    filter_upwards with r
    by_cases hrOld : r ∈ Icc (0 : ℝ) v
    · have hrT : r ∈ Icc (0 : ℝ) T := by
        constructor
        · exact hrOld.1
        · dsimp [T]; linarith [hrOld.2, hvw]
      have hρr := hsol.density r hrT
      have hρi : Integrable (R.ρ r) :=
        HRS.Whole.Q34.integrable_of_isProbDensity hρr
      have hnotNew : r ∉ Ioc v w := by
        simp only [Set.mem_Ioc]
        exact fun h => (not_lt_of_ge hrOld.2) h.1
      have heq : (fun x : Euc p.d => env (r, x)) =
          fun x => (Aold * Real.exp (-c * (v - r))) * R.ρ r x := by
        funext x
        simp [env, Set.mem_Icc, Set.mem_Ioc, hrOld.1, hrOld.2,
          hnotNew, ρclip, hclipEq r hrT]
      rw [heq]
      exact hρi.const_mul _
    · by_cases hrNew : r ∈ Ioc v w
      · have hrT : r ∈ Icc (0 : ℝ) T := by
          constructor
          · exact le_trans hv hrNew.1.le
          · dsimp [T]; linarith [hrNew.2]
        have hρr := hsol.density r hrT
        have hρi : Integrable (R.ρ r) :=
          HRS.Whole.Q34.integrable_of_isProbDensity hρr
        have hnotOld : ¬ (0 ≤ r ∧ r ≤ v) := by
          simpa only [Set.mem_Icc] using hrOld
        have hrNew' : v < r ∧ r ≤ w := by
          simpa only [Set.mem_Ioc] using hrNew
        have heq : (fun x : Euc p.d => env (r, x)) =
            fun x => Anew * R.ρ r x := by
          funext x
          simp [env, Set.mem_Icc, Set.mem_Ioc, hnotOld, hrNew',
            ρclip, hclipEq r hrT]
        rw [heq]
        exact hρi.const_mul _
      · have heq : (fun x : Euc p.d => env (r, x)) = fun _ => 0 := by
          funext x
          have hnotOld : ¬ (0 ≤ r ∧ r ≤ v) := by
            simpa only [Set.mem_Icc] using hrOld
          have hnotNew : ¬ (v < r ∧ r ≤ w) := by
            simpa only [Set.mem_Ioc] using hrNew
          simp [env, Set.mem_Icc, Set.mem_Ioc, hnotOld, hnotNew]
        rw [heq]
        simpa using (integrable_zero : Integrable (fun _ : Euc p.d => (0 : ℝ)) volume)
  have hOldWeightCont : Continuous (fun r : ℝ =>
      Aold * Real.exp (-c * (v - r))) := by fun_prop
  have hOldRowInt : Integrable
      ((Icc (0 : ℝ) v).indicator (fun r : ℝ => Aold * Real.exp (-c * (v - r))))
      (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hOldWeightCont.continuousOn.integrableOn_Icc
  have hNewRowInt : Integrable ((Ioc v w).indicator (fun _ : ℝ => Anew))
      (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (measure_Ioc_lt_top.ne)
  have hrowVal : ∀ r : ℝ,
      (∫ x : Euc p.d, env (r, x)) =
        (Icc (0 : ℝ) v).indicator
            (fun z : ℝ => Aold * Real.exp (-c * (v - z))) r +
          (Ioc v w).indicator (fun _ : ℝ => Anew) r := by
    intro r
    by_cases hrOld : r ∈ Icc (0 : ℝ) v
    · have hrT : r ∈ Icc (0 : ℝ) T := by
        constructor
        · exact hrOld.1
        · dsimp [T]; linarith [hrOld.2, hvw]
      have hρr := hsol.density r hrT
      have hnotNew : r ∉ Ioc v w := by
        simp only [Set.mem_Ioc]
        exact fun h => (not_lt_of_ge hrOld.2) h.1
      have heq : (fun x : Euc p.d => env (r, x)) =
          fun x => (Aold * Real.exp (-c * (v - r))) * R.ρ r x := by
        funext x
        simp [env, Set.mem_Icc, Set.mem_Ioc, hrOld.1, hrOld.2,
          hnotNew, ρclip, hclipEq r hrT]
      rw [heq, Set.indicator_of_mem hrOld, Set.indicator_of_notMem hnotNew,
        integral_const_mul, hρr.integral_one]
      ring
    · by_cases hrNew : r ∈ Ioc v w
      · have hrT : r ∈ Icc (0 : ℝ) T := by
          constructor
          · exact le_trans hv hrNew.1.le
          · dsimp [T]; linarith [hrNew.2]
        have hρr := hsol.density r hrT
        have hnotOld : ¬ (0 ≤ r ∧ r ≤ v) := by
          simpa only [Set.mem_Icc] using hrOld
        have hrNew' : v < r ∧ r ≤ w := by
          simpa only [Set.mem_Ioc] using hrNew
        have heq : (fun x : Euc p.d => env (r, x)) =
            fun x => Anew * R.ρ r x := by
          funext x
          simp [env, Set.mem_Icc, Set.mem_Ioc, hnotOld, hrNew',
            ρclip, hclipEq r hrT]
        rw [heq, Set.indicator_of_notMem hrOld, Set.indicator_of_mem hrNew,
          integral_const_mul, hρr.integral_one]
        ring
      · have heq : (fun x : Euc p.d => env (r, x)) = fun _ => 0 := by
          funext x
          have hnotOld : ¬ (0 ≤ r ∧ r ≤ v) := by
            simpa only [Set.mem_Icc] using hrOld
          have hnotNew : ¬ (v < r ∧ r ≤ w) := by
            simpa only [Set.mem_Ioc] using hrNew
          simp [env, Set.mem_Icc, Set.mem_Ioc, hnotOld, hnotNew]
        rw [heq, Set.indicator_of_notMem hrOld,
          Set.indicator_of_notMem hrNew]
        simp
  have hrowInt : Integrable
      (fun r : ℝ => ∫ x : Euc p.d, env (r, x)) (volume : Measure ℝ) := by
    have heq : (fun r : ℝ => ∫ x : Euc p.d, env (r, x)) =
        (Icc (0 : ℝ) v).indicator
            (fun z : ℝ => Aold * Real.exp (-c * (v - z))) +
          (Ioc v w).indicator (fun _ : ℝ => Anew) := funext hrowVal
    rw [heq]
    exact hOldRowInt.add hNewRowInt
  have hrowNorm : ∀ r : ℝ,
      (∫ x : Euc p.d, ‖env (r, x)‖) =
        (Icc (0 : ℝ) v).indicator
            (fun z : ℝ => Aold * Real.exp (-c * (v - z))) r +
          (Ioc v w).indicator (fun _ : ℝ => Anew) r := by
    intro r
    calc
      _ = ∫ x : Euc p.d, env (r, x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          Real.norm_of_nonneg (henvNonneg (r, x))
      _ = _ := hrowVal r
  have hrowNormInt : Integrable
      (fun r : ℝ => ∫ x : Euc p.d, ‖env (r, x)‖) (volume : Measure ℝ) := by
    have heq : (fun r : ℝ => ∫ x : Euc p.d, ‖env (r, x)‖) =
        (Icc (0 : ℝ) v).indicator
            (fun z : ℝ => Aold * Real.exp (-c * (v - z))) +
          (Ioc v w).indicator (fun _ : ℝ => Anew) := funext hrowNorm
    rw [heq]
    exact hOldRowInt.add hNewRowInt
  have henvInt : Integrable env μ :=
    (integrable_prod_iff henvMeas.aestronglyMeasurable).2
      ⟨henvSect, hrowNormInt⟩
  have hsqBound : ∀ q : ℝ × Euc p.d, sq q ≤ env q := by
    intro q
    by_cases hrOld : q.1 ∈ Icc (0 : ℝ) v
    · have hrT : q.1 ∈ Icc (0 : ℝ) T := by
        constructor
        · exact hrOld.1
        · dsimp [T]; linarith [hrOld.2, hvw]
      have hρr := hsol.density q.1 hrT
      have hρnonneg := hρr.nonneg q.2
      have hclip := hclipEq q.1 hrT
      let S := Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)
      have hSsq : S ^ 2 = (2 * p.β⁻¹) * R.ρ q.1 q.2 := by
        dsimp [S]
        rw [mul_pow, Real.sq_sqrt
          (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)),
          Real.sq_sqrt hρnonneg]
      have hkernel : diff q = S •
          (gradient (r26t3_U R q.1 w φ) q.2 -
            gradient (r26t3_U R q.1 v φ) q.2) := by
        dsimp [diff, f, gfun, movingNoiseKernel]
        have hqW : q.1 ∈ Icc (0 : ℝ) w :=
          ⟨hrOld.1, le_trans hrOld.2 hvw⟩
        rw [if_pos hqW, if_pos hrOld]
        dsimp [S]
        rw [smul_sub]
      have hgradRaw := holdR q.1 v w hrOld.1 hrOld.2 hvw α q.2
      have hgrad :
          ‖gradient (r26t3_U R q.1 w φ) q.2 -
            gradient (r26t3_U R q.1 v φ) q.2‖ ^ 2 ≤
            2 * g * g' * b ^ 2 * (w - v) * Real.exp (-c * (v - q.1)) := by
        simpa [r26t3_U, φ, b] using hgradRaw
      have hsqEq : sq q =
          ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
            ‖gradient (r26t3_U R q.1 w φ) q.2 -
              gradient (r26t3_U R q.1 v φ) q.2‖ ^ 2 := by
        dsimp [sq]
        rw [hkernel]
        calc
          _ = S ^ 2 *
              ‖gradient (r26t3_U R q.1 w φ) q.2 -
                gradient (r26t3_U R q.1 v φ) q.2‖ ^ 2 := by
              calc
                _ = (‖S‖ *
                    ‖gradient (r26t3_U R q.1 w φ) q.2 -
                      gradient (r26t3_U R q.1 v φ) q.2‖) ^ 2 := by
                  rw [norm_smul]
                _ = ‖S‖ ^ 2 *
                    ‖gradient (r26t3_U R q.1 w φ) q.2 -
                      gradient (r26t3_U R q.1 v φ) q.2‖ ^ 2 := by rw [mul_pow]
                _ = _ := by rw [Real.norm_eq_abs, sq_abs]
          _ = _ := by rw [hSsq]
      have hcoef0 : 0 ≤ (2 * p.β⁻¹) * R.ρ q.1 q.2 :=
        mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)) hρnonneg
      simp only [env, if_pos hrOld]
      calc
        sq q ≤ ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
            (2 * g * g' * b ^ 2 * (w - v) * Real.exp (-c * (v - q.1))) := by
          rw [hsqEq]
          exact mul_le_mul_of_nonneg_left hgrad hcoef0
        _ = Aold * Real.exp (-c * (v - q.1)) * ρclip q := by
          dsimp [Aold, b, ρclip]
          rw [hclip]
          ring
    · by_cases hrNew : q.1 ∈ Ioc v w
      · have hrT : q.1 ∈ Icc (0 : ℝ) T := by
          constructor
          · exact le_trans hv hrNew.1.le
          · dsimp [T]; linarith [hrNew.2]
        have hρr := hsol.density q.1 hrT
        have hρnonneg := hρr.nonneg q.2
        have hclip := hclipEq q.1 hrT
        have hr0 : 0 ≤ q.1 := le_trans hv hrNew.1.le
        have hdec := (hdecayR q.1 w hr0 hrNew.2 α q.2).1
        have hExpOne : Real.exp (-cN * (w - q.1)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hrNew.2)
        have hgradSq :
            ‖gradient (r26t3_U R q.1 w φ) q.2‖ ^ 2 ≤ gN ^ 2 * b ^ 2 := by
          have hnonneg : 0 ≤ gN * b := mul_nonneg hgN (s104_b_nonneg α)
          have hbound : ‖gradient (r26t3_U R q.1 w φ) q.2‖ ≤ gN * b := by
            calc
              _ ≤ gN * b * Real.exp (-cN * (w - q.1)) := by
                simpa [r26t3_U, φ, b] using hdec
              _ ≤ gN * b * 1 := mul_le_mul_of_nonneg_left hExpOne hnonneg
              _ = gN * b := by ring
          have hsq := (sq_le_sq₀ (norm_nonneg _) hnonneg).2 hbound
          nlinarith
        let S := Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)
        have hSsq : S ^ 2 = (2 * p.β⁻¹) * R.ρ q.1 q.2 := by
          dsimp [S]
          rw [mul_pow, Real.sq_sqrt
            (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)),
            Real.sq_sqrt hρnonneg]
        have hqW : q.1 ∈ Icc (0 : ℝ) w := ⟨le_trans hv hrNew.1.le, hrNew.2⟩
        have hqV : q.1 ∉ Icc (0 : ℝ) v := by
          simp only [Set.mem_Icc]
          exact fun h => (not_le_of_gt hrNew.1) h.2
        have hkernel : diff q = S • gradient (r26t3_U R q.1 w φ) q.2 := by
          dsimp [diff, f, gfun, movingNoiseKernel]
          rw [if_pos hqW, if_neg hqV]
          simp [S]
        have hsqEq : sq q = ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
            ‖gradient (r26t3_U R q.1 w φ) q.2‖ ^ 2 := by
          dsimp [sq]
          rw [hkernel]
          calc
            _ = S ^ 2 * ‖gradient (r26t3_U R q.1 w φ) q.2‖ ^ 2 := by
                calc
                  _ = (‖S‖ * ‖gradient (r26t3_U R q.1 w φ) q.2‖) ^ 2 := by
                    rw [norm_smul]
                  _ = ‖S‖ ^ 2 * ‖gradient (r26t3_U R q.1 w φ) q.2‖ ^ 2 := by
                    rw [mul_pow]
                  _ = _ := by rw [Real.norm_eq_abs, sq_abs]
            _ = _ := by rw [hSsq]
        have hcoef0 : 0 ≤ (2 * p.β⁻¹) * R.ρ q.1 q.2 :=
          mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)) hρnonneg
        simp only [env, if_neg hrOld, if_pos hrNew]
        calc
          sq q ≤ ((2 * p.β⁻¹) * R.ρ q.1 q.2) * (gN ^ 2 * b ^ 2) := by
            rw [hsqEq]
            exact mul_le_mul_of_nonneg_left hgradSq hcoef0
          _ = Anew * ρclip q := by
            dsimp [Anew, b, ρclip]
            rw [hclip]
            ring
      · have hqW : q.1 ∉ Icc (0 : ℝ) w := by
          intro h
          have hle : q.1 ≤ w := h.2
          have hnonold : v < q.1 := by
            by_contra hh
            have : q.1 ≤ v := le_of_not_gt hh
            exact hrOld ⟨h.1, this⟩
          exact hrNew ⟨hnonold, hle⟩
        have hqV : q.1 ∉ Icc (0 : ℝ) v := by
          intro h
          exact hrOld h
        have hqW' : ¬ (0 ≤ q.1 ∧ q.1 ≤ w) := by
          simpa only [Set.mem_Icc] using hqW
        have hqV' : ¬ (0 ≤ q.1 ∧ q.1 ≤ v) := by
          simpa only [Set.mem_Icc] using hqV
        have hnotOld : ¬ (0 ≤ q.1 ∧ q.1 ≤ v) := by
          simpa only [Set.mem_Icc] using hrOld
        have hnotNew : ¬ (v < q.1 ∧ q.1 ≤ w) := by
          simpa only [Set.mem_Ioc] using hrNew
        simp [sq, diff, f, gfun, movingNoiseKernel, Set.mem_Icc,
          hqW', hqV', env, Set.mem_Ioc, hnotOld, hnotNew]
  have henvIntegral : ∫ q, env q ∂μ =
      (Aold * (∫ r in Icc (0 : ℝ) v, Real.exp (-c * (v - r)))) +
        Anew * (w - v) := by
    rw [integral_prod env henvInt]
    simp_rw [hrowVal]
    rw [integral_add hOldRowInt hNewRowInt, integral_indicator measurableSet_Icc,
      integral_indicator measurableSet_Ioc]
    rw [integral_const_mul]
    rw [integral_const]
    simp [Measure.real, Real.volume_Ioc, sub_nonneg.mpr hvw,
      mul_comm, mul_left_comm, mul_assoc]
    <;> ring
  have hEnvBound : ∫ q, env q ∂μ ≤
      2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) * b ^ 2 * (w - v) := by
    rw [henvIntegral]
    have htime := fp81s21_gaussianNoise_exp_integral_le hc (show 0 ≤ v by exact hv)
    calc
      (Aold * (∫ r in Icc (0 : ℝ) v, Real.exp (-c * (v - r)))) + Anew * (w - v)
        ≤ Aold * c⁻¹ + Anew * (w - v) :=
          add_le_add (mul_le_mul_of_nonneg_left htime hAold0)
            (show Anew * (w - v) ≤ Anew * (w - v) from le_rfl)
      _ = 2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) * b ^ 2 * (w - v) := by
        dsimp [Aold, Anew, b]
        field_simp [ne_of_gt hc]
        ring
  rw [hnormIntegral]
  calc
    ∫ q, sq q ∂μ ≤ ∫ q, env q ∂μ := integral_mono hsqInt henvInt hsqBound
    _ ≤ 2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) * b ^ 2 * (w - v) := hEnvBound

#print axioms fp81s21_gaussian_noise_feature_increment_bound

end HRS.Fp81.S21

end

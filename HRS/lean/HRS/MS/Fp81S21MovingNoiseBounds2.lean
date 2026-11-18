import HRS.MS.Fp81S21MovingNoiseBounds
import HRS.MS.Fp81S21Uniform2
import HRS.MS.CovMeasAux9
import HRS.MS.MovDecAux3
import HRS.MS.S104gJc2

/-!
# HRS S2.1(iii), SOL39 packet 2: Hermite coordinates and increment estimates

This file packages the moving feature on the Hermite tests.  The path
constructor's operator estimate is proved in `Fp81S21MovingNoiseBounds`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3 HRS.MS.CovMeas

/-- The moving noise feature associated with one Hermite test. -/
def movingNoiseCoordinate
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u t : ℝ) (α : MultiIndex p.d) : MovingNoiseHilbert p.d :=
  movingNoiseFeature R u t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)

private theorem fp81s21_movingNoiseCoordinate_test
    (p : Parameters) (α : MultiIndex p.d) :
    IsOscTest (wholeSpaceIndex p.d : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) := by
  exact HRS.MS.GenPath.s56_isOscTest _ α

private def fp81s21_noiseClipTime (H : ℝ) (hH : 0 < H) (r : ℝ) : Icc (0 : ℝ) H :=
  ⟨max 0 (min r H), ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩⟩

private theorem fp81s21_noiseClipTime_continuous {H : ℝ} (hH : 0 < H) :
    Continuous (fp81s21_noiseClipTime H hH) := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun r => ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩)

private theorem fp81s21_noiseClipTime_eq
    {H u t r : ℝ} (hH : 0 < H)
    (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hr : r ∈ Icc u t) :
    fp81s21_noiseClipTime H hH r = ⟨r, ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩⟩ := by
  apply Subtype.ext
  change max 0 (min r H) = r
  rw [min_eq_left (hr.2.trans ht.2), max_eq_right (hu.1.trans hr.1)]

/-- Squared feature norms are controlled by the modewise orbit envelope. -/
private theorem fp81s21_movingNoiseCoordinate_norm_sq_le
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
      K * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    fp81s21_movingNoiseCoordinate_test p α
  have hmem := (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu t ht φ hφ
  have hρjoint := fp81s21_moving_density_joint_meas (H := H) p R hδ hδhalf
  have hρclip : Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_noiseClipTime H hH q.1) q.2) := by
    have htime : Continuous fun q : ℝ × Euc p.d =>
        fp81s21_noiseClipTime H hH q.1 :=
      (fp81s21_noiseClipTime_continuous hH).comp continuous_fst
    have hmap : Continuous fun q : ℝ × Euc p.d =>
        (fp81s21_noiseClipTime H hH q.1, q.2) := htime.prodMk continuous_snd
    exact hρjoint.comp hmap.measurable
  have henvMeas : Measurable env := by
    apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    · exact measurable_const.mul hρclip
    · exact measurable_const
  have hρnonneg : ∀ q : ℝ × Euc p.d,
      0 ≤ R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 := by
    intro q
    exact (R.resulting.global H).density
      (fp81s21_noiseClipTime H hH q.1).1
      ⟨(fp81s21_noiseClipTime H hH q.1).2.1,
        (fp81s21_noiseClipTime H hH q.1).2.2⟩ |>.nonneg q.2
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
      have hclip := fp81s21_noiseClipTime_eq hH hu ht hr
      have hclip' : (fp81s21_noiseClipTime H hH r : ℝ) = r :=
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
      have hclip := fp81s21_noiseClipTime_eq hH hu ht hr
      have hclip' : (fp81s21_noiseClipTime H hH r : ℝ) = r :=
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
      ·
        simp only [env, Set.mem_Icc, hr.1, hr.2, ite_true]
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
      have hclip := fp81s21_noiseClipTime_eq hH hu ht hq
      have hclip' : (fp81s21_noiseClipTime H hH q.1 : ℝ) = q.1 :=
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
              mul_le_mul_of_nonneg_left hgradSq
              hcoeff
          _ = K * R.ρ q.1 q.2 := by dsimp [K]; ring
      change ‖(if q.1 ∈ Icc u t then
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2 else 0)‖ ^ 2 ≤
        (if q.1 ∈ Icc u t then
          K * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0)
      rw [if_pos hq, if_pos hq, hclip']
      exact hbound
    · have hq' : ¬ (u ≤ q.1 ∧ q.1 ≤ t) := by simpa only [Set.mem_Icc] using hq
      change ‖(if q.1 ∈ Icc u t then
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2 else 0)‖ ^ 2 ≤
        (if q.1 ∈ Icc u t then
          K * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0)
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

private theorem fp81s21_movingNoiseCoordinate_norm_le_zero
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
    fp81s21_movingNoiseCoordinate_test p α
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

private theorem fp81s21_movingNoise_terminal_derivative
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen p.d p.s p.a p.β R.ρβ
      δ p.c₁ p.C₁)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (huH : u < H)
    (α : MultiIndex p.d) :
    ∀ t ∈ Icc u H,
      (fun x => s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        H u t α x) =
        propagatorW (r26t3_coeff R) u t
          (generatorW (r26t3_coeff R) t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have horb : HRS.MS.R2WinErr.S104nOrbit C φ H :=
    HRS.MS.R2WinErr.s104b_orbit_of_termRegGen hterm
      R.admissible R.resulting α H hH.le
  have hder : ∀ t ∈ Icc u H, ∀ x : Euc p.d,
      HasDerivWithinAt (fun z => propagatorW C u z φ x)
        (propagatorW C u t (generatorW C t φ) x) (Icc u H) t := by
    intro t ht x
    let Fa : ℝ → Euc p.d → ℝ := fun τ => propagatorW C u (u + τ) φ
    let Fb : ℝ → Euc p.d → ℝ := fun τ =>
      propagatorW C u (u + τ) (generatorW C (u + τ) φ)
    have hτ : t - u ∈ Icc (0 : ℝ) (H - u) := by
      constructor <;> linarith [ht.1, ht.2]
    have hcdA : ∀ τ ∈ Icc (0 : ℝ) (H - u),
        ContDiff ℝ (0 : WithTop ℕ∞) (Fa τ) := by
      intro τ hτ'
      have hz : u + τ ∈ Icc (0 : ℝ) H := by
        constructor <;> linarith [hu.1, hτ'.1, hτ'.2]
      obtain ⟨f, hf⟩ := horb.ex0 (u + τ) hz
      have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
      have hc := hcanonical.c2 u ⟨hu.1, by linarith [hτ'.1]⟩
      exact hc.of_le (by norm_num)
    have hcdB : ∀ τ ∈ Icc (0 : ℝ) (H - u),
        ContDiff ℝ (0 : WithTop ℕ∞) (Fb τ) := by
      intro τ hτ'
      have hz : u + τ ∈ Icc (0 : ℝ) H := by
        constructor <;> linarith [hu.1, hτ'.1, hτ'.2]
      obtain ⟨f, hf⟩ := horb.ex1 (u + τ) hz
      have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
      have hc := hcanonical.c2 u ⟨hu.1, by linarith [hτ'.1]⟩
      exact hc.of_le (by norm_num)
    have hdiff : ∀ τ ∈ Icc (0 : ℝ) (H - u), ∀ e : ℝ, 0 < e →
        ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, h ≠ 0 → |h| < η →
          τ + h ∈ Icc (0 : ℝ) (H - u) → ∀ y : Euc p.d,
            ‖iteratedFDeriv ℝ 0
              (fun z => h⁻¹ * (Fa (τ + h) z - Fa τ z) - Fb τ z) y‖ ≤ e := by
      intro τ hτ' e he
      obtain ⟨η, hη, hq⟩ := horb.diff01 u hu τ hτ' e he
      refine ⟨η, hη, fun h hne hlt hτh y => ?_⟩
      exact hq h hne hlt hτh 0 (by norm_num) y
    have hderτ := HRS.MS.R2WinOrb.s103_hasDeriv_val hcdA hcdB hdiff x
      (t - u) hτ
    have hshift : HasDerivWithinAt (fun z : ℝ => z - u) 1 (Icc u H) t :=
      ((hasDerivAt_id t).sub_const u).hasDerivWithinAt
    have hmaps : MapsTo (fun z => z - u) (Icc u H)
        (Icc (0 : ℝ) (H - u)) := by
      intro z hz
      constructor <;> linarith [hz.1, hz.2]
    have hcomp := hderτ.comp t hshift hmaps
    have hcomp' : HasDerivWithinAt (fun z => Fa (z - u) x)
        (Fb (t - u) x) (Icc u H) t := by
      simpa [Function.comp_def] using hcomp
    have heq : ∀ z ∈ Icc u H,
        Fa (z - u) x = propagatorW C u z φ x := by
      intro z hz
      dsimp [Fa]
      congr 1
      ring
    have hactual := hcomp'.congr_of_mem (fun z hz => (heq z hz).symm) ht
    have htarget : Fb (t - u) x =
        propagatorW C u t (generatorW C t φ) x := by
      dsimp [Fb]
      congr 2 <;> ring
    exact hactual.congr_deriv htarget
  intro t ht
  funext x
  change derivWithin (fun z => propagatorW C u z φ x) (Icc u H) t =
    propagatorW C u t (generatorW C t φ) x
  exact (hder t ht x).derivWithin (uniqueDiffOn_Icc huH t ht)

private theorem fp81s21_movingNoise_gradient_terminal_lip
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen p.d p.s p.a p.β R.ρβ
      δ p.c₁ p.C₁)
    {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H (2 * p.d + 8) c)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (huH : u < H)
    (α : MultiIndex p.d) :
    ∀ s ∈ Icc u H, ∀ t ∈ Icc u H, ∀ x : Euc p.d,
      ‖gradient (propagatorW (r26t3_coeff R) u t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
        gradient (propagatorW (r26t3_coeff R) u s
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
        c α * |t - s| := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let U1 : ℝ → ℝ → Euc p.d → ℝ := fun t r =>
    if r = u then propagatorW C u t φ else 0
  let U2 : ℝ → ℝ → Euc p.d → ℝ := fun t r =>
    if r = u then propagatorW C u t (generatorW C t φ) else 0
  have horb : HRS.MS.R2WinErr.S104nOrbit C φ H :=
    HRS.MS.R2WinErr.s104b_orbit_of_termRegGen hterm
      R.admissible R.resulting α H hH.le
  have horder : 2 ≤ 2 * p.d + 8 + 1 := by
    have := p.hd
    omega
  have hsm1 : ∀ t ∈ Icc (0 : ℝ) H, ∀ r ∈ Icc (0 : ℝ) t,
      ContDiff ℝ 2 (U1 t r) := by
    intro t ht r hr
    by_cases hru : r = u
    · subst r
      have htt : t ∈ Icc u H := ⟨hr.2, ht.2⟩
      simpa [U1] using
        (hD.smoothU α u hu t htt).of_le (by exact_mod_cast horder)
    · simpa [U1, hru, Pi.zero_def] using
        (contDiff_const : ContDiff ℝ 2 (fun _ : Euc p.d => (0 : ℝ)))
  have hsm2 : ∀ t ∈ Icc (0 : ℝ) H, ∀ r ∈ Icc (0 : ℝ) t,
      ContDiff ℝ 1 (U2 t r) := by
    intro t ht r hr
    by_cases hru : r = u
    · subst r
      have htt : t ∈ Icc u H := ⟨hr.2, ht.2⟩
      have hder := fp81s21_movingNoise_terminal_derivative
        p R hH hterm hu huH α t htt
      have hcont : ContDiff ℝ 2 (fun x => s101Dt C
          (wholeSpaceIndex p.d : ℝ) H u t α x) :=
        (hD.smoothD α u hu t htt).of_le (by exact_mod_cast horder)
      have hcont1 : ContDiff ℝ 1 (fun x => s101Dt C
          (wholeSpaceIndex p.d : ℝ) H u t α x) := hcont.of_le (by norm_num)
      rw [hder] at hcont1
      simpa [U2] using hcont1
    · simpa [U2, hru, Pi.zero_def] using
        (contDiff_const : ContDiff ℝ 1 (fun _ : Euc p.d => (0 : ℝ)))
  have hdq : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ H → ∀ e : ℝ, 0 < e →
      ∃ η : ℝ, 0 < η ∧
        ∀ h : ℝ, h ≠ 0 → |h| < η → r ≤ t + h → t + h ≤ H →
          ∀ x : Euc p.d,
            ‖iteratedFDeriv ℝ 1
              (fun y => h⁻¹ * (U1 (t + h) r y - U1 t r y) - U2 t r y) x‖ ≤ e := by
    intro r t hr hrt ht e he
    by_cases hru : r = u
    · subst r
      have hτ : t - u ∈ Icc (0 : ℝ) (H - u) := by
        constructor <;> linarith
      obtain ⟨η, hη, hq⟩ := horb.diff01 u hu (t - u) hτ e he
      refine ⟨η, hη, fun h hne hlt hrt' ht' x => ?_⟩
      have hτh : (t - u) + h ∈ Icc (0 : ℝ) (H - u) := by
        constructor <;> linarith
      have hq' := hq h hne hlt hτh 1 (by norm_num) x
      have hshift0 : u + (t - u) = t := by ring
      have hshift1 : u + ((t - u) + h) = t + h := by ring
      simpa [U1, U2, hshift0, hshift1] using hq'
    · refine ⟨1, by norm_num, fun h hne hlt hrt' ht' x => ?_⟩
      simpa [U1, U2, hru] using le_of_lt he
  have hb : ∀ t ∈ Icc (0 : ℝ) H, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ x : Euc p.d, ‖gradient (U2 t r) x‖ ≤ c α := by
    intro t ht r hr x
    by_cases hru : r = u
    · subst r
      have htt : t ∈ Icc u H := ⟨hr.2, ht.2⟩
      have hder := fp81s21_movingNoise_terminal_derivative
        p R hH hterm hu huH α t htt
      have hbd := hD.bddD α u hu t htt 1 (by omega) x
      simp only [U2, if_pos rfl]
      rw [← hder]
      rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
      simpa using hbd
    · have hgrad0 : gradient (0 : Euc p.d → ℝ) x = 0 := by simp [gradient]
      simpa [U2, hru, hgrad0] using hD.nonneg α
  have hLip := HRS.MS.R2WinOrbNL.s104g_lipT hsm1 hsm2 hdq
    (Gb := c α) hb
  intro s hs t ht x
  have ht0 : t ∈ Icc (0 : ℝ) H := ⟨hu.1.trans ht.1, ht.2⟩
  have hs0 : s ∈ Icc (0 : ℝ) H := ⟨hu.1.trans hs.1, hs.2⟩
  have hresult := hLip t ht0 s hs0 u hu.1 ht.1 hs.1 x
  simpa [U1, U2] using hresult

private theorem fp81s21_movingNoiseCoordinate_increment_sq_le_ordered
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen p.d p.s p.a p.β R.ρβ
      δ p.c₁ p.C₁)
    {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H (2 * p.d + 8) c)
    {u s t : ℝ} (hu : u ∈ Icc (0 : ℝ) H)
    (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hst : s ≤ t) (α : MultiIndex p.d) :
    ‖movingNoiseCoordinate R u t α - movingNoiseCoordinate R u s α‖ ^ 2 ≤
      (2 * p.β⁻¹) * (H ^ 2 + 1) * c α ^ 2 * |t - s| := by
  classical
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let Ft : MovingNoiseHilbert p.d := movingNoiseFeature R u t φ
  let Fs : MovingNoiseHilbert p.d := movingNoiseFeature R u s φ
  let f : ℝ × Euc p.d → Euc p.d := movingNoiseKernel R u t φ
  let g : ℝ × Euc p.d → Euc p.d := movingNoiseKernel R u s φ
  let diffKernel : ℝ × Euc p.d → Euc p.d := fun q => f q - g q
  let κ : ℝ := (2 * p.β⁻¹) * c α ^ 2
  let Δ : ℝ := |t - s|
  let A : ℝ := κ * Δ ^ 2
  let env : ℝ × Euc p.d → ℝ := fun q =>
    (if q.1 ∈ Icc u s then A * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0) +
    (if q.1 ∈ Ioc s t then κ * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0)
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    fp81s21_movingNoiseCoordinate_test p α
  have hmemF := (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu t ht φ hφ
  have hmemG := (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu s hs φ hφ
  have hρjoint := fp81s21_moving_density_joint_meas (H := H) p R hδ hδhalf
  have hρclip : Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_noiseClipTime H hH q.1) q.2) := by
    have htime : Continuous fun q : ℝ × Euc p.d =>
        fp81s21_noiseClipTime H hH q.1 :=
      (fp81s21_noiseClipTime_continuous hH).comp continuous_fst
    have hmap : Continuous fun q : ℝ × Euc p.d =>
        (fp81s21_noiseClipTime H hH q.1, q.2) := htime.prodMk continuous_snd
    exact hρjoint.comp hmap.measurable
  have hIccMeas : MeasurableSet {q : ℝ × Euc p.d | q.1 ∈ Icc u s} :=
    measurableSet_Icc.preimage measurable_fst
  have hIocMeas : MeasurableSet {q : ℝ × Euc p.d | q.1 ∈ Ioc s t} :=
    measurableSet_Ioc.preimage measurable_fst
  have henv1 : Measurable (fun q : ℝ × Euc p.d =>
      if q.1 ∈ Icc u s then A * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0) := by
    exact Measurable.ite hIccMeas (measurable_const.mul hρclip) measurable_const
  have henv2 : Measurable (fun q : ℝ × Euc p.d =>
      if q.1 ∈ Ioc s t then κ * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0) := by
    exact Measurable.ite hIocMeas (measurable_const.mul hρclip) measurable_const
  have henvMeas : Measurable env := by
    exact henv1.add henv2
  have hκ0 : 0 ≤ κ := by
    dsimp [κ]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
      (sq_nonneg (c α))
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg hκ0 (sq_nonneg Δ)
  have hρnonneg : ∀ q : ℝ × Euc p.d,
      0 ≤ R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 := by
    intro q
    exact (R.resulting.global H).density
      (fp81s21_noiseClipTime H hH q.1).1
      ⟨(fp81s21_noiseClipTime H hH q.1).2.1,
        (fp81s21_noiseClipTime H hH q.1).2.2⟩ |>.nonneg q.2
  have henvNonneg : ∀ q, 0 ≤ env q := by
    intro q
    change 0 ≤
      (if q.1 ∈ Icc u s then A * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0) +
      (if q.1 ∈ Ioc s t then κ * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0)
    by_cases hqC : q.1 ∈ Icc u s
    · rw [if_pos hqC]
      by_cases hqA : q.1 ∈ Ioc s t
      · rw [if_pos hqA]
        exact add_nonneg (mul_nonneg hA0 (hρnonneg q))
          (mul_nonneg hκ0 (hρnonneg q))
      · rw [if_neg hqA, add_zero]
        exact mul_nonneg hA0 (hρnonneg q)
    · rw [if_neg hqC]
      by_cases hqA : q.1 ∈ Ioc s t
      · rw [if_pos hqA, zero_add]
        exact mul_nonneg hκ0 (hρnonneg q)
      · rw [if_neg hqA]
        simp
  have hgradTime : ∀ r : ℝ, r ∈ Icc u s → ∀ x : Euc p.d,
      ‖gradient (r26t3_U R r t φ) x -
        gradient (r26t3_U R r s φ) x‖ ≤ c α * |t - s| := by
    intro r hr x
    have hrH : r ∈ Icc (0 : ℝ) H :=
      ⟨hu.1.trans hr.1, hr.2.trans hs.2⟩
    by_cases hrlt : r < H
    · have hsR : s ∈ Icc r H := ⟨hr.2, hs.2⟩
      have htR : t ∈ Icc r H := ⟨le_trans hr.2 hst, ht.2⟩
      have hLip := fp81s21_movingNoise_gradient_terminal_lip
        p R hH hterm hD (u := r) hrH hrlt α s hsR t htR x
      simpa [r26t3_U, φ] using hLip
    · have hrEq : r = H := by linarith [hrH.2]
      have hsEq : s = H := le_antisymm hs.2 (hrEq ▸ hr.2)
      have htEq : t = H := le_antisymm ht.2 (hsEq ▸ hst)
      have htsEq : t = s := htEq.trans hsEq.symm
      rw [htsEq]
      simp
  have henvSect : ∀ᵐ r ∂(volume : Measure ℝ),
      Integrable (fun x : Euc p.d => env (r, x)) (volume : Measure (Euc p.d)) := by
    filter_upwards with r
    by_cases hrC : r ∈ Icc u s
    · have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hrC.1, hrC.2.trans hs.2⟩
      have hρr := (R.resulting.global H).density r hrH
      have hρi : Integrable (R.ρ r) :=
        HRS.Whole.Q34.integrable_of_isProbDensity hρr
      have hnotA : r ∉ Ioc s t := by
        simp only [Set.mem_Ioc]
        exact fun hh => (not_lt_of_ge hrC.2) hh.1
      have hrC' : u ≤ r ∧ r ≤ s := by simpa only [Set.mem_Icc] using hrC
      have hnotA' : ¬ (s < r ∧ r ≤ t) := by
        simpa only [Set.mem_Ioc] using hnotA
      have hclip := fp81s21_noiseClipTime_eq hH hu hs hrC
      have hclip' : (fp81s21_noiseClipTime H hH r : ℝ) = r :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have heq : (fun x : Euc p.d => env (r, x)) = fun x => A * R.ρ r x := by
        funext x
        dsimp [env]
        rw [if_pos hrC, if_neg hnotA, hclip']
        simp
      rw [heq]
      exact hρi.const_mul A
    · by_cases hrA : r ∈ Ioc s t
      · have hrH : r ∈ Icc (0 : ℝ) H :=
          ⟨hs.1.trans hrA.1.le, hrA.2.trans ht.2⟩
        have hρr := (R.resulting.global H).density r hrH
        have hρi : Integrable (R.ρ r) :=
          HRS.Whole.Q34.integrable_of_isProbDensity hρr
        have hnotC : r ∉ Icc u s := by
          simp only [Set.mem_Icc]
          exact fun hh => (not_le_of_gt hrA.1) hh.2
        have hnotC' : ¬ (u ≤ r ∧ r ≤ s) := by
          simpa only [Set.mem_Icc] using hnotC
        have hrA' : s < r ∧ r ≤ t := by simpa only [Set.mem_Ioc] using hrA
        have hclip := fp81s21_noiseClipTime_eq hH ⟨le_rfl, hH.le⟩ ht
          ⟨hs.1.trans hrA.1.le, hrA.2⟩
        have hclip' : (fp81s21_noiseClipTime H hH r : ℝ) = r :=
          congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
        have heq : (fun x : Euc p.d => env (r, x)) = fun x => κ * R.ρ r x := by
          funext x
          dsimp [env]
          rw [if_neg hnotC, if_pos hrA, hclip']
          simp
        rw [heq]
        exact hρi.const_mul κ
      · have heq : (fun x : Euc p.d => env (r, x)) = fun _ => 0 := by
          funext x
          have hrC' : ¬ (u ≤ r ∧ r ≤ s) := by
            simpa only [Set.mem_Icc] using hrC
          have hrA' : ¬ (s < r ∧ r ≤ t) := by
            simpa only [Set.mem_Ioc] using hrA
          dsimp [env]
          rw [if_neg hrC, if_neg hrA]
          simp
        rw [heq]
        simpa using (integrable_zero : Integrable (fun _ : Euc p.d => (0 : ℝ)) volume)
  have hrowVal : ∀ r : ℝ,
      (∫ x : Euc p.d, env (r, x)) =
        (Icc u s).indicator (fun _ : ℝ => A) r +
        (Ioc s t).indicator (fun _ : ℝ => κ) r := by
    intro r
    by_cases hrC : r ∈ Icc u s
    · have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hrC.1, hrC.2.trans hs.2⟩
      have hρr := (R.resulting.global H).density r hrH
      have hρi : Integrable (R.ρ r) :=
        HRS.Whole.Q34.integrable_of_isProbDensity hρr
      have hnotA : r ∉ Ioc s t := by
        simp only [Set.mem_Ioc]
        exact fun hh => (not_lt_of_ge hrC.2) hh.1
      have hrC' : u ≤ r ∧ r ≤ s := by simpa only [Set.mem_Icc] using hrC
      have hnotA' : ¬ (s < r ∧ r ≤ t) := by
        simpa only [Set.mem_Ioc] using hnotA
      have hclip := fp81s21_noiseClipTime_eq hH hu hs hrC
      have hclip' : (fp81s21_noiseClipTime H hH r : ℝ) = r :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have heq : (fun x : Euc p.d => env (r, x)) = fun x => A * R.ρ r x := by
        funext x
        dsimp [env]
        rw [if_pos hrC, if_neg hnotA, hclip']
        simp
      rw [heq, integral_const_mul, hρr.integral_one]
      simp [Set.indicator, hrC, hnotA]
    · by_cases hrA : r ∈ Ioc s t
      · have hrH : r ∈ Icc (0 : ℝ) H :=
          ⟨hs.1.trans hrA.1.le, hrA.2.trans ht.2⟩
        have hρr := (R.resulting.global H).density r hrH
        have hρi : Integrable (R.ρ r) :=
          HRS.Whole.Q34.integrable_of_isProbDensity hρr
        have hnotC : r ∉ Icc u s := by
          simp only [Set.mem_Icc]
          exact fun hh => (not_le_of_gt hrA.1) hh.2
        have hnotC' : ¬ (u ≤ r ∧ r ≤ s) := by
          simpa only [Set.mem_Icc] using hnotC
        have hrA' : s < r ∧ r ≤ t := by simpa only [Set.mem_Ioc] using hrA
        have hclip := fp81s21_noiseClipTime_eq hH ⟨le_rfl, hH.le⟩ ht
          ⟨hs.1.trans hrA.1.le, hrA.2⟩
        have hclip' : (fp81s21_noiseClipTime H hH r : ℝ) = r :=
          congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
        have heq : (fun x : Euc p.d => env (r, x)) = fun x => κ * R.ρ r x := by
          funext x
          dsimp [env]
          rw [if_neg hnotC, if_pos hrA, hclip']
          simp
        rw [heq, integral_const_mul, hρr.integral_one]
        simp [Set.indicator, hrC, hrA]
      · have heq : (fun x : Euc p.d => env (r, x)) = fun _ => 0 := by
          funext x
          have hrC' : ¬ (u ≤ r ∧ r ≤ s) := by
            simpa only [Set.mem_Icc] using hrC
          have hrA' : ¬ (s < r ∧ r ≤ t) := by
            simpa only [Set.mem_Ioc] using hrA
          dsimp [env]
          rw [if_neg hrC, if_neg hrA]
          simp
        rw [heq]
        simp [Set.indicator, hrC, hrA]
  have henvRowNorm : ∀ r : ℝ,
      (∫ x : Euc p.d, ‖env (r, x)‖) =
        (Icc u s).indicator (fun _ : ℝ => A) r +
        (Ioc s t).indicator (fun _ : ℝ => κ) r := by
    intro r
    calc
      _ = ∫ x : Euc p.d, env (r, x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (henvNonneg (r, x))
      _ = _ := hrowVal r
  have hrowInt : Integrable
      (fun r : ℝ => ∫ x : Euc p.d, ‖env (r, x)‖) (volume : Measure ℝ) := by
    have hIcc : Integrable ((Icc u s).indicator (fun _ : ℝ => A))
        (volume : Measure ℝ) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (measure_Icc_lt_top.ne)
    have hIoc : Integrable ((Ioc s t).indicator (fun _ : ℝ => κ))
        (volume : Measure ℝ) := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (measure_Ioc_lt_top.ne)
    have heq : (fun r : ℝ => ∫ x : Euc p.d, ‖env (r, x)‖) =
        (Icc u s).indicator (fun _ : ℝ => A) +
        (Ioc s t).indicator (fun _ : ℝ => κ) := funext henvRowNorm
    rw [heq]
    exact hIcc.add hIoc
  have henvInt : Integrable env μ :=
    (integrable_prod_iff henvMeas.aestronglyMeasurable).2 ⟨henvSect, hrowInt⟩
  have hmemDiff : MemLp diffKernel 2 μ := by
    exact hmemF.sub hmemG
  have hsqInt : Integrable (fun q => ‖diffKernel q‖ ^ 2) μ := by
    simpa [diffKernel] using hmemDiff.integrable_norm_pow (by norm_num)
  have hsqBound : ∀ q : ℝ × Euc p.d, ‖diffKernel q‖ ^ 2 ≤ env q := by
    intro q
    by_cases hqt : q.1 ∈ Icc u t
    · by_cases hqs : q.1 ∈ Icc u s
      · have hqH : q.1 ∈ Icc (0 : ℝ) H :=
          ⟨hu.1.trans hqs.1, hqs.2.trans hs.2⟩
        have hρq := (R.resulting.global H).density q.1 hqH
        have hclip := fp81s21_noiseClipTime_eq hH hu hs hqs
        have hclip' : (fp81s21_noiseClipTime H hH q.1 : ℝ) = q.1 :=
          congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
        let a : ℝ := Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)
        let v : Euc p.d :=
          gradient (r26t3_U R q.1 t φ) q.2 - gradient (r26t3_U R q.1 s φ) q.2
        have hker : diffKernel q = a • v := by
          dsimp [diffKernel, f, g, movingNoiseKernel, a, v]
          rw [if_pos hqt, if_pos hqs, ← smul_sub]
        have hgradSq : ‖v‖ ^ 2 ≤ c α ^ 2 * Δ ^ 2 := by
          have hgradLip := hgradTime q.1 hqs q.2
          dsimp [v, Δ] at hgradLip ⊢
          calc
            _ ≤ (c α * |t - s|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hgradLip 2
            _ = _ := by rw [mul_pow]
        have hfactor : a ^ 2 = (2 * p.β⁻¹) * R.ρ q.1 q.2 := by
          dsimp [a]
          rw [mul_pow, Real.sq_sqrt
            (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)),
            Real.sq_sqrt (hρq.nonneg q.2)]
        have hnorm : ‖a • v‖ ^ 2 =
            ((2 * p.β⁻¹) * R.ρ q.1 q.2) * ‖v‖ ^ 2 := by
          calc
            _ = a ^ 2 * ‖v‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
            _ = _ := by rw [hfactor]
        have hcoeff : 0 ≤ (2 * p.β⁻¹) * R.ρ q.1 q.2 :=
          mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
            (hρq.nonneg q.2)
        have hpoint : ‖diffKernel q‖ ^ 2 ≤ A * R.ρ q.1 q.2 := by
          rw [hker, hnorm]
          calc
            ((2 * p.β⁻¹) * R.ρ q.1 q.2) * ‖v‖ ^ 2 ≤
                ((2 * p.β⁻¹) * R.ρ q.1 q.2) * (c α ^ 2 * Δ ^ 2) :=
              mul_le_mul_of_nonneg_left hgradSq hcoeff
            _ = A * R.ρ q.1 q.2 := by dsimp [A, κ, Δ]; ring
        have hnotA : q.1 ∉ Ioc s t := by
          simp only [Set.mem_Ioc]
          exact fun hh => (not_lt_of_ge hqs.2) hh.1
        change ‖diffKernel q‖ ^ 2 ≤
          (if q.1 ∈ Icc u s then A * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0) +
          (if q.1 ∈ Ioc s t then κ * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0)
        rw [if_pos hqs, if_neg hnotA, hclip']
        simpa using hpoint
      · have hqAdd : q.1 ∈ Ioc s t := by
          have hlt : s < q.1 := by
            by_contra hnot
            have hle : q.1 ≤ s := le_of_not_gt hnot
            exact hqs ⟨hqt.1, hle⟩
          exact ⟨hlt, hqt.2⟩
        have hqH : q.1 ∈ Icc (0 : ℝ) H :=
          ⟨hu.1.trans hqt.1, hqt.2.trans ht.2⟩
        have hρq := (R.resulting.global H).density q.1 hqH
        have hclip := fp81s21_noiseClipTime_eq hH hu ht hqt
        have hclip' : (fp81s21_noiseClipTime H hH q.1 : ℝ) = q.1 :=
          congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
        let a : ℝ := Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)
        have hgrad : ‖gradient (r26t3_U R q.1 t φ) q.2‖ ≤ c α := by
          have hbd := hD.bddU α q.1 hqH t ⟨hqt.2, ht.2⟩ 1 (by omega) q.2
          rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
          simpa [r26t3_U, φ] using hbd
        have hfactor : a ^ 2 = (2 * p.β⁻¹) * R.ρ q.1 q.2 := by
          dsimp [a]
          rw [mul_pow, Real.sq_sqrt
            (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)),
            Real.sq_sqrt (hρq.nonneg q.2)]
        have hnorm : ‖a • gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 =
            ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
              ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 := by
          calc
            _ = a ^ 2 * ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
            _ = _ := by rw [hfactor]
        have hcoeff : 0 ≤ (2 * p.β⁻¹) * R.ρ q.1 q.2 :=
          mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
            (hρq.nonneg q.2)
        have hpoint : ‖diffKernel q‖ ^ 2 ≤ κ * R.ρ q.1 q.2 := by
          have hker : diffKernel q = a • gradient (r26t3_U R q.1 t φ) q.2 := by
            dsimp [diffKernel, f, g, movingNoiseKernel, a]
            rw [if_pos hqt, if_neg hqs]
            simp
          rw [hker, hnorm]
          calc
            ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
                ‖gradient (r26t3_U R q.1 t φ) q.2‖ ^ 2 ≤
              ((2 * p.β⁻¹) * R.ρ q.1 q.2) * c α ^ 2 :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg _) hgrad 2) hcoeff
            _ = κ * R.ρ q.1 q.2 := by dsimp [κ]; ring
        have hnotC : q.1 ∉ Icc u s := by
          simp only [Set.mem_Icc]
          exact fun hh => (not_le_of_gt hqAdd.1) hh.2
        change ‖diffKernel q‖ ^ 2 ≤
          (if q.1 ∈ Icc u s then A * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0) +
          (if q.1 ∈ Ioc s t then κ * R.ρ (fp81s21_noiseClipTime H hH q.1) q.2 else 0)
        rw [if_neg hnotC, if_pos hqAdd, hclip']
        simpa using hpoint
    · have hqs : q.1 ∉ Icc u s := by
        intro hqs
        exact hqt ⟨hqs.1, hqs.2.trans hst⟩
      have hker : diffKernel q = 0 := by
        dsimp [diffKernel, f, g, movingNoiseKernel]
        have hnotS : q.1 ∉ Icc u s := hqs
        rw [if_neg hqt, if_neg hnotS]
        simp
      rw [hker]
      simpa using henvNonneg q
  have hnormIntegral : ‖Ft - Fs‖ ^ 2 = ∫ q, ‖diffKernel q‖ ^ 2 ∂μ := by
    have hFtAE : (Ft : ℝ × Euc p.d → Euc p.d) =ᵐ[μ] f := by
      change (movingNoiseFeature R u t φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
        movingNoiseKernel R u t φ
      rw [movingNoiseFeature, dif_pos hmemF]
      exact hmemF.coeFn_toLp
    have hFsAE : (Fs : ℝ × Euc p.d → Euc p.d) =ᵐ[μ] g := by
      change (movingNoiseFeature R u s φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
        movingNoiseKernel R u s φ
      rw [movingNoiseFeature, dif_pos hmemG]
      exact hmemG.coeFn_toLp
    have hdiffAE : (fun q : ℝ × Euc p.d => (Ft - Fs) q) =ᵐ[μ] diffKernel := by
      filter_upwards [Lp.coeFn_sub Ft Fs, hFtAE, hFsAE] with q hsub hF hG
      calc
        (Ft - Fs) q = Ft q - Fs q := hsub
        _ = f q - g q := by rw [hF, hG]
        _ = diffKernel q := rfl
    have hfun : (fun q : ℝ × Euc p.d =>
        inner ℝ ((Ft - Fs : MovingNoiseHilbert p.d) q)
          ((Ft - Fs : MovingNoiseHilbert p.d) q)) =ᵐ[μ]
        (fun q => ‖diffKernel q‖ ^ 2) := by
      filter_upwards [hdiffAE] with q hq
      rw [hq]
      simp [real_inner_self_eq_norm_sq]
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, integral_congr_ae hfun]
  have hcompare : ∫ q, ‖diffKernel q‖ ^ 2 ∂μ ≤ ∫ q, env q ∂μ :=
    integral_mono hsqInt henvInt hsqBound
  have hIccConst : Integrable ((Icc u s).indicator (fun _ : ℝ => A))
      (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (measure_Icc_lt_top.ne)
  have hIocConst : Integrable ((Ioc s t).indicator (fun _ : ℝ => κ))
      (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (measure_Ioc_lt_top.ne)
  have henvIntegral : ∫ q, env q ∂μ = A * max (s - u) 0 + κ * (t - s) := by
    rw [integral_prod env henvInt]
    have hrow : (fun r : ℝ => ∫ x : Euc p.d, env (r, x)) =
        (Icc u s).indicator (fun _ : ℝ => A) +
        (Ioc s t).indicator (fun _ : ℝ => κ) := funext hrowVal
    rw [hrow]
    calc
      (∫ r : ℝ, ((Icc u s).indicator (fun _ : ℝ => A) +
          (Ioc s t).indicator (fun _ : ℝ => κ)) r ∂volume) =
          (∫ r : ℝ, (Icc u s).indicator (fun _ : ℝ => A) r ∂volume) +
            ∫ r : ℝ, (Ioc s t).indicator (fun _ : ℝ => κ) r ∂volume := by
        exact integral_add hIccConst hIocConst
      _ = A * max (s - u) 0 + κ * (t - s) := by
        rw [integral_indicator_const _ measurableSet_Icc,
          integral_indicator_const _ measurableSet_Ioc]
        have hlen : (ENNReal.ofReal (s - u)).toReal = max (s - u) 0 := by
          by_cases hsu : 0 ≤ s - u
          · rw [ENNReal.toReal_ofReal hsu, max_eq_left hsu]
          · have hsu' : s - u ≤ 0 := le_of_not_ge hsu
            rw [ENNReal.ofReal_of_nonpos hsu', ENNReal.toReal_zero,
              max_eq_right hsu']
        simp [Measure.real, Real.volume_Icc, Real.volume_Ioc, hst, hlen,
          mul_comm, mul_left_comm, mul_assoc]
  have hnormBound : ‖Ft - Fs‖ ^ 2 ≤ A * max (s - u) 0 + κ * (t - s) := by
    rw [hnormIntegral]
    exact hcompare.trans_eq henvIntegral
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have hsuH : max (s - u) 0 ≤ H := by
    rw [max_le_iff]
    constructor <;> linarith [hu.1, hs.2]
  have htsH : t - s ≤ H := by linarith [hs.1, ht.2]
  have hquad : (t - s) ^ 2 * H ≤ H ^ 2 * (t - s) := by
    have hmul : (t - s) * H ≤ H * H :=
      mul_le_mul_of_nonneg_right htsH hH.le
    calc
      (t - s) ^ 2 * H = (t - s) * ((t - s) * H) := by ring
      _ ≤ (t - s) * (H * H) := mul_le_mul_of_nonneg_left hmul hts
      _ = H ^ 2 * (t - s) := by ring
  have hfinal : A * max (s - u) 0 + κ * (t - s) ≤
      (2 * p.β⁻¹) * (H ^ 2 + 1) * c α ^ 2 * |t - s| := by
    have h1 : (t - s) ^ 2 * max (s - u) 0 ≤ (t - s) ^ 2 * H :=
      mul_le_mul_of_nonneg_left hsuH (sq_nonneg (t - s))
    have h2 : (t - s) ^ 2 * H ≤ H ^ 2 * (t - s) := hquad
    have hK : 0 ≤ (2 * p.β⁻¹) * c α ^ 2 := by positivity
    have habs : |t - s| = t - s := abs_of_nonneg hts
    have hsum : (t - s) ^ 2 * max (s - u) 0 + (t - s) ≤
        (H ^ 2 + 1) * (t - s) := by
      calc
        _ ≤ (t - s) ^ 2 * H + (t - s) := add_le_add h1 le_rfl
        _ ≤ H ^ 2 * (t - s) + (t - s) := add_le_add h2 le_rfl
        _ = (H ^ 2 + 1) * (t - s) := by ring
    calc
      _ = ((2 * p.β⁻¹) * c α ^ 2) *
          ((t - s) ^ 2 * max (s - u) 0 + (t - s)) := by
            dsimp [A, κ, Δ]
            rw [habs]
            ring
      _ ≤ ((2 * p.β⁻¹) * c α ^ 2) * ((H ^ 2 + 1) * (t - s)) :=
        mul_le_mul_of_nonneg_left hsum hK
      _ = (2 * p.β⁻¹) * (H ^ 2 + 1) * c α ^ 2 * |t - s| := by
        rw [habs]
        ring
  exact hnormBound.trans hfinal

private theorem fp81s21_movingNoiseCoordinate_increment_sq_le
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    (hterm : HRS.MS.R2WinErr.S104bTermRegGen p.d p.s p.a p.β R.ρβ
      δ p.c₁ p.C₁)
    {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H (2 * p.d + 8) c)
    {u s t : ℝ} (hu : u ∈ Icc (0 : ℝ) H)
    (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex p.d) :
    ‖movingNoiseCoordinate R u t α - movingNoiseCoordinate R u s α‖ ^ 2 ≤
      (2 * p.β⁻¹) * (H ^ 2 + 1) * c α ^ 2 * |t - s| := by
  rcases le_total s t with hst | hts
  · exact fp81s21_movingNoiseCoordinate_increment_sq_le_ordered
      p R hδ hδhalf hH hterm hD hu hs ht hst α
  · have hswap := fp81s21_movingNoiseCoordinate_increment_sq_le_ordered
      p R hδ hδhalf hH hterm hD hu ht hs hts α
    simpa only [norm_sub_rev, abs_sub_comm] using hswap

/-- Hermite feature energies are square summable, uniformly in the forcing
cutoff and terminal time on each finite horizon. -/
theorem fp81s21_movingNoiseCoordinate_summable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H →
      ∀ u ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc (0 : ℝ) H,
        Summable (fun α : MultiIndex p.d => ‖movingNoiseCoordinate R u t α‖ ^ 2) := by
  obtain ⟨δ0, hδ0, hδ0half, huniform⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH u hu t ht
  obtain ⟨Co, co, hco, hsquare, hdata⟩ := huniform δ hδ hδle R
  have hD := hdata H hH
  let c : MultiIndex p.d → ℝ := fp81s21_uniform_orbit_coefficient p Co
  have hD' : HRS.MS.CovMeas.S101Data (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8) c := by
    simpa [c] using hD
  let C : ℝ := (2 * p.β⁻¹) * H
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)) hH.le
  have hmajor : Summable (fun α : MultiIndex p.d => C * c α ^ 2) := by
    exact hsquare.mul_left C
  apply Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) hmajor
  have hcut := fp81s21_movingNoiseCoordinate_norm_le_zero
    p R hδ (hδle.trans hδ0half) hH hu ht α
  have hbase := fp81s21_movingNoiseCoordinate_norm_sq_le
    p R hδ (hδle.trans hδ0half) hH hD' ⟨le_rfl, hH.le⟩ ht ht.1 α
  calc
    ‖movingNoiseCoordinate R u t α‖ ^ 2 ≤
        ‖movingNoiseCoordinate R 0 t α‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcut
    _ ≤ (2 * p.β⁻¹) * H * c α ^ 2 := hbase
    _ = C * c α ^ 2 := by dsimp [C]

/-- The summed Hermite-coordinate increment bound has one constant chosen
before the forcing cutoff and terminal times. -/
theorem fp81s21_movingNoiseCoordinate_increment_summable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H →
        ∃ L : ℝ, 0 ≤ L ∧
          ∀ u ∈ Icc (0 : ℝ) H,
          ∀ s ∈ Icc (0 : ℝ) H,
          ∀ t ∈ Icc (0 : ℝ) H,
            Summable (fun α : MultiIndex p.d =>
              ‖movingNoiseCoordinate R u t α -
                movingNoiseCoordinate R u s α‖ ^ 2) ∧
            (∑' α : MultiIndex p.d,
              ‖movingNoiseCoordinate R u t α -
                movingNoiseCoordinate R u s α‖ ^ 2) ≤ L * |t - s| := by
  obtain ⟨δ0, Co, co, hδ0, hδ0half, hco, hcommon⟩ :=
    fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH
  obtain ⟨hclaims, -, hterm, -⟩ :=
    hcommon δ hδ hδle R.ρβ R.thermal
  obtain ⟨c, hD⟩ := fp81s21_moving_s101data_of_common
    p R hH hclaims hterm
  let K : ℝ := (2 * p.β⁻¹) * (H ^ 2 + 1)
  let L : ℝ := K * (∑' α : MultiIndex p.d, c α ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
      (add_nonneg (sq_nonneg H) (by norm_num))
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hK (tsum_nonneg fun α => sq_nonneg (c α))
  refine ⟨L, hL, ?_⟩
  intro u hu s hs t ht
  have hmajor : Summable (fun α : MultiIndex p.d =>
      K * c α ^ 2 * |t - s|) :=
    (hD.summable.mul_left K).mul_right |t - s|
  have hpoint : ∀ α : MultiIndex p.d,
      ‖movingNoiseCoordinate R u t α -
        movingNoiseCoordinate R u s α‖ ^ 2 ≤
        K * c α ^ 2 * |t - s| := by
    intro α
    simpa only [K] using fp81s21_movingNoiseCoordinate_increment_sq_le
      p R hδ (hδle.trans hδ0half) hH hterm hD hu hs ht α
  have hsum : Summable (fun α : MultiIndex p.d =>
      ‖movingNoiseCoordinate R u t α -
        movingNoiseCoordinate R u s α‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun α => sq_nonneg _) hpoint hmajor
  refine ⟨hsum, ?_⟩
  calc
    (∑' α : MultiIndex p.d,
        ‖movingNoiseCoordinate R u t α -
          movingNoiseCoordinate R u s α‖ ^ 2) ≤
        ∑' α : MultiIndex p.d, K * c α ^ 2 * |t - s| :=
      hsum.tsum_le_tsum hpoint hmajor
    _ = L * |t - s| := by
      dsimp [L]
      rw [tsum_mul_right, tsum_mul_left]

/-- Quantitative feature hypotheses required by the continuous Gaussian path
constructor: an all-test operator bound, Hermite square summability, and a
summed terminal-time increment estimate. -/
theorem movingNoiseFeature_bounds (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H →
        (∀ u ∈ Icc (0 : ℝ) H,
          ∀ t ∈ Icc (0 : ℝ) H,
          ∃ B : ℝ, 0 ≤ B ∧
            ∀ φ : Euc p.d → ℝ,
              IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
              ‖movingNoiseFeature R u t φ‖ ≤
                B * oscNorm (wholeSpaceIndex p.d : ℝ) φ) ∧
        (∀ u ∈ Icc (0 : ℝ) H,
          ∀ t ∈ Icc (0 : ℝ) H,
            Summable (fun α : MultiIndex p.d =>
              ‖movingNoiseCoordinate R u t α‖ ^ 2)) ∧
        (∃ L : ℝ, 0 ≤ L ∧
          ∀ u ∈ Icc (0 : ℝ) H,
          ∀ s ∈ Icc (0 : ℝ) H,
          ∀ t ∈ Icc (0 : ℝ) H,
            Summable (fun α : MultiIndex p.d =>
              ‖movingNoiseCoordinate R u t α -
                movingNoiseCoordinate R u s α‖ ^ 2) ∧
            (∑' α : MultiIndex p.d,
              ‖movingNoiseCoordinate R u t α -
                movingNoiseCoordinate R u s α‖ ^ 2) ≤
              L * |t - s|) := by
  obtain ⟨δop, hop, hopHalf, hopBound⟩ :=
    fp81s21_movingNoiseFeature_operator_bound p
  obtain ⟨δsum, hsum, hsumHalf, hsumBound⟩ :=
    fp81s21_movingNoiseCoordinate_summable p
  obtain ⟨δinc, hinc, hincHalf, hincBound⟩ :=
    fp81s21_movingNoiseCoordinate_increment_summable p
  let δinner : ℝ := min δsum δinc
  let δ0 : ℝ := min δop δinner
  have hδinner : 0 < δinner := lt_min hsum hinc
  have hδ0 : 0 < δ0 := lt_min hop hδinner
  have hδ0Half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hopHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R H hH
  have hδop : δ ≤ δop := hδle.trans (min_le_left _ _)
  have hδsum : δ ≤ δsum :=
    hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδinc : δ ≤ δinc :=
    hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨B, hB, hBbound⟩ := hopBound δ hδ hδop R H hH
  have hsumAll := hsumBound δ hδ hδsum R H hH
  have hincAll := hincBound δ hδ hδinc R H hH
  refine ⟨?_, hsumAll, hincAll⟩
  intro u hu t ht
  exact ⟨B, hB, fun φ hφ => hBbound u hu t ht φ hφ⟩

/-- Hermite coordinates inherit the genuine kernel integrability of the
moving feature. -/
theorem fp81s21_movingNoiseCoordinate_kernel_memLp
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (α : MultiIndex p.d) :
    MemLp
      (movingNoiseKernel R u t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := by
  exact (movingNoiseFeature_spec p R hδ hδhalf hH).1 u hu t ht _
    (fp81s21_movingNoiseCoordinate_test p α)

#print axioms movingNoiseCoordinate
#print axioms fp81s21_movingNoiseCoordinate_test
#print axioms fp81s21_movingNoiseCoordinate_kernel_memLp
#print axioms fp81s21_movingNoiseCoordinate_norm_sq_le
#print axioms fp81s21_movingNoiseCoordinate_summable
#print axioms fp81s21_movingNoiseCoordinate_increment_summable
#print axioms movingNoiseFeature_bounds
#print axioms fp81s21_movingNoise_terminal_derivative
#print axioms fp81s21_movingNoise_gradient_terminal_lip
#print axioms fp81s21_movingNoiseCoordinate_increment_sq_le_ordered

end HRS.Fp81.S21

end

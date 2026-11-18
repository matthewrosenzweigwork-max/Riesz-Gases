import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.Fp81S21MovingMeas
import HRS.MS.S111X1Aux1
import HRS.MS.ProClosureS111NoiseLinear
import Mathlib.MeasureTheory.Integral.Prod

/-!
# HRS S2.1(iii), SOL39 packet 1: deterministic moving noise features

The feature space is the fixed Lebesgue `L²` space on time and space.  The
trajectory density is incorporated into the vector-valued kernel by its square
root, so the feature Gram form has the moving covariance normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open Classical

abbrev MovingNoiseHilbert (d : ℕ) :=
  Lp (Euc d) 2
    ((volume : Measure ℝ).prod (volume : Measure (Euc d)))

private def fp81s21_movingNoiseClippedTime (H : ℝ) (hH : 0 < H) (u : ℝ) :
    Set.Icc (0 : ℝ) H :=
  ⟨max 0 (min u H), ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩⟩

private theorem fp81s21_movingNoiseClippedTime_continuous
    {H : ℝ} (hH : 0 < H) :
    Continuous (fp81s21_movingNoiseClippedTime H hH) := by
  exact (continuous_const.max (continuous_id.min continuous_const)).subtype_mk
    (fun u => ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩)

private theorem fp81s21_movingNoise_densityClipped_meas
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H) :
    Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_movingNoiseClippedTime H hH q.1) q.2) := by
  have hρ := fp81s21_moving_density_joint_meas (H := H) p R hδ hδh
  have hclip : Continuous (fun q : ℝ × Euc p.d =>
      fp81s21_movingNoiseClippedTime H hH q.1) :=
    (fp81s21_movingNoiseClippedTime_continuous hH).comp continuous_fst
  have hmap : Continuous (fun q : ℝ × Euc p.d =>
      (fp81s21_movingNoiseClippedTime H hH q.1, q.2)) :=
    hclip.prodMk continuous_snd
  exact hρ.comp hmap.measurable

private theorem fp81s21_movingNoise_clip_eq
    {H u t r : ℝ} (hH : 0 < H)
    (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hr : r ∈ Icc u t) :
    fp81s21_movingNoiseClippedTime H hH r = ⟨r, ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩⟩ := by
  apply Subtype.ext
  change max 0 (min r H) = r
  rw [min_eq_left (hr.2.trans ht.2), max_eq_right (hu.1.trans hr.1)]

def movingNoiseKernel
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u t : ℝ) (φ : Euc p.d → ℝ)
    (q : ℝ × Euc p.d) : Euc p.d :=
  if q.1 ∈ Set.Icc u t then
    (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
      gradient (r26t3_U R q.1 t φ) q.2
  else 0

def movingNoiseFeature
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u t : ℝ) (φ : Euc p.d → ℝ) :
    MovingNoiseHilbert p.d :=
  if h : MemLp (movingNoiseKernel R u t φ) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) then
    h.toLp (movingNoiseKernel R u t φ)
  else 0

private theorem fp81s21_movingNoiseKernel_measurable
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ) :
    Measurable (movingNoiseKernel R u t φ) := by
  let f : ℝ → Euc p.d → ℝ := fun r => r26t3_U R r t φ
  have hf : IsClassicalAdjointW (r26t3_coeff R) t φ f := by
    simpa [f] using fp81s21_U_osc_test_classical p R hφ ht.1
  have hgrad : Measurable (fun q : ℝ × Euc p.d =>
      if q.1 ∈ Icc (0 : ℝ) t then gradient (f q.1) q.2 else 0) := by
    simpa [f, r26t3_U] using HRS.MS.R2Interp.s102_gradJoint_meas hf
  have hρ := fp81s21_movingNoise_densityClipped_meas p R hδ hδh hH
  let a : ℝ × Euc p.d → ℝ := fun q =>
    if q.1 ∈ Icc u t then
      Real.sqrt (2 * p.β⁻¹) * Real.sqrt
        (R.ρ (fp81s21_movingNoiseClippedTime H hH q.1) q.2)
    else 0
  have ha : Measurable a := by
    apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hρ)
    · exact measurable_const
  have heq : movingNoiseKernel R u t φ = fun q =>
      a q • (if q.1 ∈ Icc (0 : ℝ) t then gradient (f q.1) q.2 else 0) := by
    funext q
    by_cases hq : q.1 ∈ Icc u t
    · have hqt : q.1 ∈ Icc (0 : ℝ) t := ⟨hu.1.trans hq.1, hq.2⟩
      have hclip := fp81s21_movingNoise_clip_eq hH hu ht hq
      have hclip' : (fp81s21_movingNoiseClippedTime H hH q.1 : ℝ) = q.1 :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      change (if q.1 ∈ Icc u t then
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2 else 0) =
        a q • (if q.1 ∈ Icc (0 : ℝ) t then gradient (f q.1) q.2 else 0)
      rw [if_pos hq, if_pos hqt]
      simp only [a, if_pos hq]
      rw [hclip']
    · change (if q.1 ∈ Icc u t then
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (r26t3_U R q.1 t φ) q.2 else 0) =
        a q • (if q.1 ∈ Icc (0 : ℝ) t then gradient (f q.1) q.2 else 0)
      rw [if_neg hq]
      simp only [a, if_neg hq, zero_smul]
  rw [heq]
  exact ha.smul hgrad

private theorem fp81s21_movingNoiseKernel_memLp
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ) :
    MemLp (movingNoiseKernel R u t φ) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := by
  classical
  let f : ℝ → Euc p.d → ℝ := fun r => r26t3_U R r t φ
  have hf : IsClassicalAdjointW (r26t3_coeff R) t φ f := by
    simpa [f] using fp81s21_U_osc_test_classical p R hφ ht.1
  obtain ⟨B, hB0, hB⟩ := HRS.MS.S111X1.x1_fderiv_bdd hf
  have hρmeas := fp81s21_movingNoise_densityClipped_meas p R hδ hδh hH
  have hsol := R.resulting.global H
  let K : ℝ := 2 * p.β⁻¹ * B ^ 2
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)) (sq_nonneg B)
  let env : ℝ × Euc p.d → ℝ := fun q =>
    if q.1 ∈ Icc u t then
      K * R.ρ (fp81s21_movingNoiseClippedTime H hH q.1) q.2
    else 0
  have henvMeas : Measurable env := by
    apply Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    · exact measurable_const.mul hρmeas
    · exact measurable_const
  have henvSect : ∀ᵐ r ∂(volume : Measure ℝ),
      Integrable (fun x : Euc p.d => env (r, x)) (volume : Measure (Euc p.d)) := by
    filter_upwards with r
    by_cases hr : r ∈ Icc u t
    · have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩
      have hρr := hsol.density r hrH
      have hρi : Integrable (R.ρ r) := HRS.Whole.Q34.integrable_of_isProbDensity hρr
      have hclip := fp81s21_movingNoise_clip_eq hH hu ht hr
      have hclip' : (fp81s21_movingNoiseClippedTime H hH r : ℝ) = r :=
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
  have henvRow : ∀ r : ℝ,
      (∫ x : Euc p.d, ‖env (r, x)‖) =
        (Icc u t).indicator (fun _ : ℝ => K) r := by
    intro r
    by_cases hr : r ∈ Icc u t
    · have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hr.1, hr.2.trans ht.2⟩
      have hρr := hsol.density r hrH
      have hclip := fp81s21_movingNoise_clip_eq hH hu ht hr
      have hclip' : (fp81s21_movingNoiseClippedTime H hH r : ℝ) = r :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have hpoint : (fun x : Euc p.d => ‖env (r, x)‖) =
          fun x => K * R.ρ r x := by
        funext x
        rw [show env (r, x) = K * R.ρ r x by
          simp [env, Set.mem_Icc, hr.1, hr.2, hclip']]
        exact Real.norm_of_nonneg (mul_nonneg hK0 (hρr.nonneg x))
      rw [hpoint, Set.indicator_of_mem hr, integral_const_mul, hρr.integral_one]
      ring
    · have hr' : ¬ (u ≤ r ∧ r ≤ t) := by simpa only [Set.mem_Icc] using hr
      simp [env, Set.indicator, Set.mem_Icc, hr']
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
  have henvInt : Integrable env
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) :=
    (integrable_prod_iff henvMeas.aestronglyMeasurable).2 ⟨henvSect, hrowInt⟩
  have hkernelMeas := fp81s21_movingNoiseKernel_measurable
    p R hδ hδh hH hu ht hφ
  let sq : ℝ × Euc p.d → ℝ := fun q => ‖movingNoiseKernel R u t φ q‖ ^ 2
  have hsqMeas : Measurable sq := hkernelMeas.norm.pow_const 2
  have hsqBound : ∀ q : ℝ × Euc p.d, sq q ≤ env q := by
    intro q
    by_cases hq : q.1 ∈ Icc u t
    · have hrH : q.1 ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hq.1, hq.2.trans ht.2⟩
      have hρr := hsol.density q.1 hrH
      have hρnn := hρr.nonneg q.2
      have hclip := fp81s21_movingNoise_clip_eq hH hu ht hq
      have hclip' : (fp81s21_movingNoiseClippedTime H hH q.1 : ℝ) = q.1 :=
        congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
      have hgrad := hB q.1 ⟨hu.1.trans hq.1, hq.2⟩ q.2
      have hgradSq : ‖gradient (f q.1) q.2‖ ^ 2 ≤ B ^ 2 := by
        have hgrad0 : 0 ≤ ‖gradient (f q.1) q.2‖ := norm_nonneg _
        nlinarith [hgrad, hB0, hgrad0]
      have hfactor :
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) ^ 2 =
            (2 * p.β⁻¹) * R.ρ q.1 q.2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num)
          (inv_nonneg.mpr p.hβ.le)), Real.sq_sqrt hρnn]
      have hnorm :
          ‖(Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) •
            gradient (f q.1) q.2‖ ^ 2 =
              ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
                ‖gradient (f q.1) q.2‖ ^ 2 := by
        calc
          _ = (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)) ^ 2 *
                ‖gradient (f q.1) q.2‖ ^ 2 := by
              calc
                _ = (‖Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)‖ *
                    ‖gradient (f q.1) q.2‖) ^ 2 := by rw [norm_smul]
                _ = ‖Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ q.1 q.2)‖ ^ 2 *
                    ‖gradient (f q.1) q.2‖ ^ 2 := by rw [mul_pow]
                _ = _ := by rw [Real.norm_eq_abs, sq_abs]
          _ = _ := by rw [hfactor]
      change ‖movingNoiseKernel R u t φ q‖ ^ 2 ≤
        (if q.1 ∈ Icc u t then
          K * R.ρ (fp81s21_movingNoiseClippedTime H hH q.1) q.2 else 0)
      rw [if_pos hq, movingNoiseKernel, if_pos hq, hnorm]
      calc
        ((2 * p.β⁻¹) * R.ρ q.1 q.2) *
            ‖gradient (f q.1) q.2‖ ^ 2 ≤
          ((2 * p.β⁻¹) * R.ρ q.1 q.2) * B ^ 2 :=
            mul_le_mul_of_nonneg_left hgradSq
              (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)) hρnn)
        _ = K * R.ρ q.1 q.2 := by dsimp [K]; ring
        _ = K * R.ρ (fp81s21_movingNoiseClippedTime H hH q.1) q.2 := by rw [hclip']
    · have hq' : ¬ (u ≤ q.1 ∧ q.1 ≤ t) := by simpa only [Set.mem_Icc] using hq
      simp [sq, env, movingNoiseKernel, Set.mem_Icc, hq']
  have hsqInt : Integrable sq
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := by
    apply henvInt.mono' hsqMeas.aestronglyMeasurable
    filter_upwards with q
    have hsq0 : 0 ≤ sq q := sq_nonneg _
    have henv0 : 0 ≤ env q := by
      by_cases hq : q.1 ∈ Icc u t
      · rcases hq with ⟨hqu, hqt⟩
        simp only [env, Set.mem_Icc, hqu, hqt, ite_true]
        have hclip := fp81s21_movingNoise_clip_eq hH hu ht ⟨hqu, hqt⟩
        have hclip' : (fp81s21_movingNoiseClippedTime H hH q.1 : ℝ) = q.1 :=
          congrArg (fun z : Icc (0 : ℝ) H => (z : ℝ)) hclip
        rw [hclip']
        exact mul_nonneg hK0 ((hsol.density q.1
          ⟨hu.1.trans hqu, hqt.trans ht.2⟩).nonneg q.2)
      · have hq' : ¬ (u ≤ q.1 ∧ q.1 ≤ t) := by simpa only [Set.mem_Icc] using hq
        simp [env, Set.mem_Icc, hq']
    rw [Real.norm_of_nonneg hsq0]
    exact hsqBound q
  exact (memLp_two_iff_integrable_sq_norm hkernelMeas.aestronglyMeasurable).2 hsqInt

private theorem fp81s21_movingNoiseFeature_ae
    {p : Parameters} {δ u t : ℝ} {R : Trajectory p δ} {φ : Euc p.d → ℝ}
    (hmem : MemLp (movingNoiseKernel R u t φ) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d)))) :
    (movingNoiseFeature R u t φ : ℝ × Euc p.d → Euc p.d) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure (Euc p.d))]
        movingNoiseKernel R u t φ := by
  rw [movingNoiseFeature, dif_pos hmem]
  exact hmem.coeFn_toLp

private theorem fp81s21_movingNoiseKernel_gram
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {u ta tb : ℝ} (hu : u ∈ Icc (0 : ℝ) H)
    (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    (hψ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ) :
    ∫ q : ℝ × Euc p.d,
      inner ℝ (movingNoiseKernel R u ta φ q) (movingNoiseKernel R u tb ψ q)
        ∂((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) =
      2 * p.β⁻¹ * ∫ r in Icc u (min ta tb), ∫ x,
        inner ℝ (gradient (r26t3_U R r ta φ) x)
          (gradient (r26t3_U R r tb ψ) x) * R.ρ r x := by
  classical
  have hmemA := fp81s21_movingNoiseKernel_memLp p R hδ hδh hH hu hta hφ
  have hmemB := fp81s21_movingNoiseKernel_memLp p R hδ hδh hH hu htb hψ
  let FA := movingNoiseFeature R u ta φ
  let FB := movingNoiseFeature R u tb ψ
  have hFA : MemLp (movingNoiseKernel R u ta φ) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := hmemA
  have hFB : MemLp (movingNoiseKernel R u tb ψ) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := hmemB
  have haeA := fp81s21_movingNoiseFeature_ae hFA
  have haeB := fp81s21_movingNoiseFeature_ae hFB
  have hae : (fun q : ℝ × Euc p.d => inner ℝ (FA q) (FB q)) =ᵐ[
      (volume : Measure ℝ).prod (volume : Measure (Euc p.d))]
      (fun q => inner ℝ (movingNoiseKernel R u ta φ q)
        (movingNoiseKernel R u tb ψ q)) := by
    filter_upwards [haeA, haeB] with q hqA hqB
    rw [hqA, hqB]
  have hi : Integrable (fun q : ℝ × Euc p.d =>
      inner ℝ (movingNoiseKernel R u ta φ q)
        (movingNoiseKernel R u tb ψ q))
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) :=
    (L2.integrable_inner (𝕜 := ℝ) FA FB).congr hae
  have hprod := integral_prod
    (f := fun q : ℝ × Euc p.d =>
      inner ℝ (movingNoiseKernel R u ta φ q)
        (movingNoiseKernel R u tb ψ q)) hi
  let J : Set ℝ := Icc u (min ta tb)
  have hkernelPoint : ∀ r : ℝ, ∀ x : Euc p.d,
      inner ℝ (movingNoiseKernel R u ta φ (r, x))
        (movingNoiseKernel R u tb ψ (r, x)) =
      J.indicator (fun s => (2 * p.β⁻¹) *
        (inner ℝ (gradient (r26t3_U R s ta φ) x)
          (gradient (r26t3_U R s tb ψ) x) * R.ρ s x)) r := by
    intro r x
    have hboth : r ∈ Icc u ta ∧ r ∈ Icc u tb ↔ r ∈ J := by
      simp only [J, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hru, hra⟩, ⟨_, hrb⟩⟩
        exact ⟨hru, le_min hra hrb⟩
      · rintro ⟨hru, hrmin⟩
        exact ⟨⟨hru, hrmin.trans (min_le_left _ _)⟩,
          ⟨hru, hrmin.trans (min_le_right _ _)⟩⟩
    by_cases hr : r ∈ J
    · have hra : r ∈ Icc u ta :=
        ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
      have hrb : r ∈ Icc u tb :=
        ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
      have hrH : r ∈ Icc (0 : ℝ) H :=
        ⟨hu.1.trans hra.1, hra.2.trans hta.2⟩
      have hρnn := (R.resulting.global H).density r hrH |>.nonneg x
      have hfactor :
          (Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ r x)) ^ 2 =
            (2 * p.β⁻¹) * R.ρ r x := by
        rw [mul_pow, Real.sq_sqrt
          (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)),
          Real.sq_sqrt hρnn]
      have hscale :
          inner ℝ
              ((Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ r x)) •
                gradient (r26t3_U R r ta φ) x)
              ((Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ r x)) •
                gradient (r26t3_U R r tb ψ) x) =
            ((2 * p.β⁻¹) * R.ρ r x) *
              inner ℝ (gradient (r26t3_U R r ta φ) x)
                (gradient (r26t3_U R r tb ψ) x) := by
        rw [inner_smul_left, inner_smul_right]
        simp only [conj_trivial, smul_eq_mul]
        calc
          _ = ((Real.sqrt (2 * p.β⁻¹) * Real.sqrt (R.ρ r x)) ^ 2) *
              inner ℝ (gradient (r26t3_U R r ta φ) x)
                (gradient (r26t3_U R r tb ψ) x) := by ring
          _ = _ := by rw [hfactor]
      simp only [J, Set.indicator_of_mem hr, movingNoiseKernel,
        if_pos hra, if_pos hrb]
      rw [hscale]
      ring
    · have hnot : ¬ (r ∈ Icc u ta ∧ r ∈ Icc u tb) := by
        intro hh
        exact hr (hboth.mp hh)
      by_cases hra : r ∈ Icc u ta
      · have hrb : r ∉ Icc u tb := fun hrb => hnot ⟨hra, hrb⟩
        simp [J, Set.indicator, hr, movingNoiseKernel, hra, hrb]
      · simp [J, Set.indicator, hr, movingNoiseKernel, hra]
  have hrow : ∀ r : ℝ,
      (∫ x : Euc p.d, inner ℝ (movingNoiseKernel R u ta φ (r, x))
        (movingNoiseKernel R u tb ψ (r, x))) =
      J.indicator (fun s => (2 * p.β⁻¹) *
        ∫ x : Euc p.d,
          inner ℝ (gradient (r26t3_U R s ta φ) x)
            (gradient (r26t3_U R s tb ψ) x) * R.ρ s x) r := by
    intro r
    by_cases hr : r ∈ J
    · have hfun : (fun x : Euc p.d =>
          inner ℝ (movingNoiseKernel R u ta φ (r, x))
            (movingNoiseKernel R u tb ψ (r, x))) =
        fun x => (2 * p.β⁻¹) *
          (inner ℝ (gradient (r26t3_U R r ta φ) x)
            (gradient (r26t3_U R r tb ψ) x) * R.ρ r x) := by
        funext x
        simpa [J, Set.indicator_of_mem hr] using hkernelPoint r x
      rw [integral_congr_ae (ae_of_all _ (fun x => congrFun hfun x)),
        Set.indicator_of_mem hr, integral_const_mul]
    · have hfun : ∀ x : Euc p.d,
          inner ℝ (movingNoiseKernel R u ta φ (r, x))
            (movingNoiseKernel R u tb ψ (r, x)) = 0 := by
        intro x
        simpa [J, Set.indicator, hr] using hkernelPoint r x
      rw [integral_congr_ae (ae_of_all _ hfun)]
      simp [J, Set.indicator, hr]
  calc
    ∫ q : ℝ × Euc p.d,
        inner ℝ (movingNoiseKernel R u ta φ q) (movingNoiseKernel R u tb ψ q)
          ∂((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) =
        ∫ r : ℝ, ∫ x : Euc p.d,
          inner ℝ (movingNoiseKernel R u ta φ (r, x))
            (movingNoiseKernel R u tb ψ (r, x)) := hprod
    _ = ∫ r : ℝ, J.indicator (fun s => (2 * p.β⁻¹) *
          ∫ x : Euc p.d,
            inner ℝ (gradient (r26t3_U R s ta φ) x)
              (gradient (r26t3_U R s tb ψ) x) * R.ρ s x) r := by
        exact integral_congr_ae (ae_of_all _ hrow)
    _ = ∫ r in J, (2 * p.β⁻¹) *
          ∫ x : Euc p.d,
            inner ℝ (gradient (r26t3_U R r ta φ) x)
              (gradient (r26t3_U R r tb ψ) x) * R.ρ r x := by
        rw [integral_indicator measurableSet_Icc]
    _ = 2 * p.β⁻¹ * ∫ r in Icc u (min ta tb), ∫ x : Euc p.d,
          inner ℝ (gradient (r26t3_U R r ta φ) x)
            (gradient (r26t3_U R r tb ψ) x) * R.ρ r x := by
        rw [integral_const_mul]

theorem movingNoiseFeature_spec
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H) :
    (∀ u ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ∀ φ : Euc p.d → ℝ,
        IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ →
        MemLp (movingNoiseKernel R u t φ) 2
          ((volume : Measure ℝ).prod (volume : Measure (Euc p.d)))) ∧
    (∀ u ∈ Icc (0 : ℝ) H,
      ∀ ta ∈ Icc (0 : ℝ) H, ∀ tb ∈ Icc (0 : ℝ) H,
        ∀ φ ψ : Euc p.d → ℝ,
          IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ →
          IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ →
          inner ℝ (movingNoiseFeature R u ta φ) (movingNoiseFeature R u tb ψ) =
            2 * p.β⁻¹ * ∫ r in Icc u (min ta tb), ∫ x,
              inner ℝ (gradient (r26t3_U R r ta φ) x)
                (gradient (r26t3_U R r tb ψ) x) * R.ρ r x) := by
  constructor
  · intro u hu t ht φ hφ
    exact fp81s21_movingNoiseKernel_memLp p R hδ hδhalf hH hu ht hφ
  · intro u hu ta hta tb htb φ ψ hφ hψ
    have hmemA := fp81s21_movingNoiseKernel_memLp p R hδ hδhalf hH hu hta hφ
    have hmemB := fp81s21_movingNoiseKernel_memLp p R hδ hδhalf hH hu htb hψ
    have haeA := fp81s21_movingNoiseFeature_ae hmemA
    have haeB := fp81s21_movingNoiseFeature_ae hmemB
    have hae : (fun q : ℝ × Euc p.d =>
        inner ℝ (movingNoiseFeature R u ta φ q)
          (movingNoiseFeature R u tb ψ q)) =ᵐ[
        (volume : Measure ℝ).prod (volume : Measure (Euc p.d))]
        (fun q => inner ℝ (movingNoiseKernel R u ta φ q)
          (movingNoiseKernel R u tb ψ q)) := by
      filter_upwards [haeA, haeB] with q hqA hqB
      rw [hqA, hqB]
    have hgram := fp81s21_movingNoiseKernel_gram p R hδ hδhalf hH hu hta htb hφ hψ
    calc
      inner ℝ (movingNoiseFeature R u ta φ) (movingNoiseFeature R u tb ψ) =
          ∫ q : ℝ × Euc p.d,
            inner ℝ (movingNoiseFeature R u ta φ q)
              (movingNoiseFeature R u tb ψ q)
              ∂((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) := by
            rw [L2.inner_def]
      _ = ∫ q : ℝ × Euc p.d,
          inner ℝ (movingNoiseKernel R u ta φ q)
            (movingNoiseKernel R u tb ψ q)
            ∂((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) :=
              integral_congr_ae hae
      _ = 2 * p.β⁻¹ * ∫ r in Icc u (min ta tb), ∫ x,
          inner ℝ (gradient (r26t3_U R r ta φ) x)
            (gradient (r26t3_U R r tb ψ) x) * R.ρ r x := hgram

theorem fp81s21_movingNoiseFeature_add_smul
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    (hψ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ) (c : ℝ) :
    movingNoiseFeature R u t (fun x => φ x + c * ψ x) =
      movingNoiseFeature R u t φ + c • movingNoiseFeature R u t ψ := by
  classical
  have hsum : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ)
      (fun x => φ x + c * ψ x) := by
    let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
    have hsmulMem := (HRS.MS.S111X1.oscSub p.d m).smul_mem c hψ
    have hsumMem := (HRS.MS.S111X1.oscSub p.d m).add_mem hφ hsmulMem
    change IsOscTest m (fun x => φ x + c * ψ x) at hsumMem
    simpa [m] using hsumMem
  have hmem0 := fp81s21_movingNoiseKernel_memLp p R hδ hδhalf hH hu ht hsum
  have hmem1 := fp81s21_movingNoiseKernel_memLp p R hδ hδhalf hH hu ht hφ
  have hmem2 := fp81s21_movingNoiseKernel_memLp p R hδ hδhalf hH hu ht hψ
  have hU0 := fp81s21_U_osc_test_classical p R hsum ht.1
  have hU1 := fp81s21_U_osc_test_classical p R hφ ht.1
  have hU2 := fp81s21_U_osc_test_classical p R hψ ht.1
  have hraw : movingNoiseKernel R u t (fun x => φ x + c * ψ x) =
      fun q => movingNoiseKernel R u t φ q + c • movingNoiseKernel R u t ψ q := by
    funext q
    by_cases hq : q.1 ∈ Icc u t
    · have hqt : q.1 ∈ Icc (0 : ℝ) t := ⟨hu.1.trans hq.1, hq.2⟩
      have hUlin := fp81s21_U_linear_of_osc_test p R hφ hψ c
        (t := t) (r := q.1) ht.1 hqt
      have hgradLin := HRS.MS.ProClosureS111.gradient_add_const_mul
        ((hU1.c2 q.1 hqt).differentiable (by norm_num) q.2)
        ((hU2.c2 q.1 hqt).differentiable (by norm_num) q.2) c
      simp only [movingNoiseKernel, if_pos hq]
      rw [hUlin, hgradLin]
      simp [smul_add, smul_smul, mul_comm]
    · simp [movingNoiseKernel, hq]
  apply Lp.ext
  filter_upwards [fp81s21_movingNoiseFeature_ae hmem0,
    fp81s21_movingNoiseFeature_ae hmem1,
    fp81s21_movingNoiseFeature_ae hmem2,
    Lp.coeFn_add (movingNoiseFeature R u t φ)
      (c • movingNoiseFeature R u t ψ),
    Lp.coeFn_smul c (movingNoiseFeature R u t ψ)]
      with q h0 h1 h2 h3 h4
  rw [h0, h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2]
  exact congrFun hraw q

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.movingNoiseFeature_spec
#print axioms HRS.Fp81.S21.fp81s21_movingNoiseFeature_add_smul

end

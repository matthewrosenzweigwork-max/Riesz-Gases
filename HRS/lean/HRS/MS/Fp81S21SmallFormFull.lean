import HRS.MS.Fp81S21ConvSplit2
import HRS.MS.Fp81S21SmallFormAttempt4
import HRS.MS.S111X2Aux35
import HRS.MS.WadAux33
import HRS.MS.WadAux184

/-!
# S2.1(iii), packet 3: full small-form estimate

This file builds the uniform weighted estimate for the moving-minus-thermal
generator.  The initial group extracts a uniform thermal density bound from
the Gaussian regularity of the thermal reference.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovAdj

namespace HRS.Fp81.S21

/-- A thermal density bound uniform over all trajectories at fixed class
parameters.  The bound is chosen before the perturbation parameter and the
trajectory. -/
theorem sol13_uniform_thermal_sup_bound (p : HRS.MS.R26T3.Parameters) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, ∀ R : HRS.MS.R26T3.Trajectory p δ,
      ∀ x : Euc p.d, R.ρβ x ≤ M := by
  obtain ⟨Λ, hΛ⟩ := HRS.MS.S21.s21_thermal_bounded p.hd p.hs0
    (by linarith [p.hs]) p.ha p.hβ
  refine ⟨max Λ 0, le_max_right _ _, fun δ R x => ?_⟩
  exact (hΛ R.ρβ R.thermal).2.1 x |>.trans (le_max_left _ _)

private theorem fp81s21_product_source_estimates {d : ℕ}
    {v q : Euc d → ℝ} {V Q : ℝ}
    (hvm : Measurable v) (hqm : Measurable q)
    (hv : MemLp v 2 (volume : Measure (Euc d)))
    (hq : MemLp q 2 (volume : Measure (Euc d)))
    (hV : 0 ≤ V) (hVb : ∀ x, ‖v x‖ ≤ V)
    (hQ : 0 ≤ Q) (hQb : ∀ x, ‖q x‖ ≤ Q) :
    let g : Euc d → ℝ := fun x => v x * q x
    Measurable g ∧ (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) ∧
      Integrable g ∧ MemLp g 2 (volume : Measure (Euc d)) ∧
      Real.sqrt (∫ x, g x ^ 2) ≤ V * Real.sqrt (∫ x, q x ^ 2) ∧
      (∫ x, ‖g x‖) ≤
        Real.sqrt (∫ x, v x ^ 2) * Real.sqrt (∫ x, q x ^ 2) := by
  dsimp
  let g : Euc d → ℝ := fun x => v x * q x
  have hgm : Measurable g := hvm.mul hqm
  have hvmem : MemLp (fun x => ‖v x‖) 2 (volume : Measure (Euc d)) := hv.norm
  have hqmem : MemLp (fun x => ‖q x‖) 2 (volume : Measure (Euc d)) := hq.norm
  have hgsq : Integrable (fun x => g x ^ 2) (volume : Measure (Euc d)) := by
    have hmajor : Integrable (fun x => V ^ 2 * q x ^ 2) (volume : Measure (Euc d)) :=
      hq.integrable_sq.const_mul (V ^ 2)
    refine hmajor.mono' (hgm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg (g x))]
    have hvabs : |v x| ≤ V := by simpa [Real.norm_eq_abs] using hVb x
    have habsSq : |v x| ^ 2 ≤ V ^ 2 := by
      calc
        |v x| ^ 2 = |v x| * |v x| := by ring
        _ ≤ V * V := mul_le_mul hvabs hvabs (abs_nonneg _) hV
        _ = V ^ 2 := by ring
    have hvSq : v x ^ 2 ≤ V ^ 2 := by
      rw [← sq_abs]
      exact habsSq
    dsimp [g]
    nlinarith [sq_nonneg (q x)]
  have hgLp : MemLp g 2 (volume : Measure (Euc d)) :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hgsq
  have hgI : Integrable g (volume : Measure (Euc d)) := hv.integrable_mul hq
  have hgBound : ∀ x, ‖g x‖ ≤ V * Q := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    have hvabs : |v x| ≤ V := by simpa [Real.norm_eq_abs] using hVb x
    have hqabs : |q x| ≤ Q := by simpa [Real.norm_eq_abs] using hQb x
    exact mul_le_mul hvabs hqabs (abs_nonneg _) hV
  have hsqIneq : (∫ x, g x ^ 2) ≤ V ^ 2 * ∫ x, q x ^ 2 := by
    calc
      (∫ x, g x ^ 2) ≤ ∫ x, V ^ 2 * q x ^ 2 :=
        integral_mono hgsq (hq.integrable_sq.const_mul (V ^ 2)) (fun x => by
          have hvabs : |v x| ≤ V := by simpa [Real.norm_eq_abs] using hVb x
          have habsSq : |v x| ^ 2 ≤ V ^ 2 := by
            calc
              |v x| ^ 2 = |v x| * |v x| := by ring
              _ ≤ V * V := mul_le_mul hvabs hvabs (abs_nonneg _) hV
              _ = V ^ 2 := by ring
          have hvSq : v x ^ 2 ≤ V ^ 2 := by
            rw [← sq_abs]
            exact habsSq
          dsimp [g]
          nlinarith [sq_nonneg (q x)])
      _ = V ^ 2 * ∫ x, q x ^ 2 := by rw [integral_const_mul]
  have hnormL2 : Real.sqrt (∫ x, g x ^ 2) ≤ V * Real.sqrt (∫ x, q x ^ 2) := by
    calc
      Real.sqrt (∫ x, g x ^ 2) ≤ Real.sqrt (V ^ 2 * ∫ x, q x ^ 2) := Real.sqrt_le_sqrt hsqIneq
      _ = V * Real.sqrt (∫ x, q x ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg V), Real.sqrt_sq_eq_abs, abs_of_nonneg hV]
  have hL1 : (∫ x, ‖g x‖) ≤
      Real.sqrt (∫ x, v x ^ 2) * Real.sqrt (∫ x, q x ^ 2) := by
    have hp : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    have hvmem' : MemLp (fun x => ‖v x‖) (ENNReal.ofReal 2) (volume : Measure (Euc d)) := by
      rw [hp]
      exact hvmem
    have hqmem' : MemLp (fun x => ‖q x‖) (ENNReal.ofReal 2) (volume : Measure (Euc d)) := by
      rw [hp]
      exact hqmem
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure (Euc d))) (p := 2) (q := 2)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => norm_nonneg (v x))
      (Filter.Eventually.of_forall fun x => norm_nonneg (q x)) hvmem' hqmem'
    calc
      (∫ x, ‖g x‖) = ∫ x, ‖v x‖ * ‖q x‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [g, norm_mul]
      _ ≤ Real.sqrt (∫ x, ‖v x‖ ^ (2 : ℝ)) *
          Real.sqrt (∫ x, ‖q x‖ ^ (2 : ℝ)) := by
        simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hCS
      _ = Real.sqrt (∫ x, v x ^ 2) * Real.sqrt (∫ x, q x ^ 2) := by
        congr 2 <;> {
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [Real.norm_eq_abs, sq_abs]
        }
  exact ⟨hvm.mul hqm, ⟨V * Q, hgBound⟩, hgI, hgLp, hnormL2, hL1⟩

private theorem fp81s21_eLpNorm_two_toReal {d : ℕ} {μ : Measure (Euc d)}
    {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  simp [Real.sqrt_eq_rpow]

private theorem fp81s21_eLpNorm_two_toReal_norm {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {μ : Measure (Euc d)} {u : Euc d → F}
    (hu : MemLp u 2 μ) :
    (eLpNorm u 2 μ).toReal = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  rw [hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  simp [Real.sqrt_eq_rpow]

private theorem fp81s21_weighted_L2_transfer {d : ℕ}
    {ρ : Euc d → ℝ} {M : ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρM : ∀ x, ρ x ≤ M) {u : Euc d → ℝ}
    (hum : Measurable u) (hu : MemLp u 2 (volume : Measure (Euc d))) :
    MemLp u 2 (HRS.Whole.withDensityReal ρ) ∧
      Real.sqrt (∫ x, u x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        Real.sqrt M * Real.sqrt (∫ x, u x ^ 2) := by
  have hM : 0 ≤ M := (hρ.nonneg 0).trans (hρM 0)
  have huSq : Integrable (fun x => u x ^ 2) (volume : Measure (Euc d)) := hu.integrable_sq
  have hρI : Integrable ρ (volume : Measure (Euc d)) :=
    HRS.Whole.Q34.integrable_of_isProbDensity hρ
  have hρuSq : Integrable (fun x => ρ x * u x ^ 2) (volume : Measure (Euc d)) := by
    have hmajor : Integrable (fun x => M * u x ^ 2) (volume : Measure (Euc d)) :=
      huSq.const_mul M
    refine hmajor.mono' (hρ.measurable.mul (hum.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (hρ.nonneg x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hρM x) (sq_nonneg _)
  have hweightedSq : Integrable (fun x => u x ^ 2) (HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.withDensityReal
    rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hρuSq.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x), mul_comm]
  have humLp : AEStronglyMeasurable u (HRS.Whole.withDensityReal ρ) :=
    hum.aestronglyMeasurable
  have hweightedMem : MemLp u 2 (HRS.Whole.withDensityReal ρ) :=
    (memLp_two_iff_integrable_sq humLp).2 hweightedSq
  have hIntegral : (∫ x, u x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
      M * ∫ x, u x ^ 2 := by
    calc
      (∫ x, u x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) =
          ∫ x, ρ x * u x ^ 2 :=
        HRS.MP.RdRem.mrr_integral_withDensityReal ρ hρ.measurable hρ.nonneg
          (fun x => u x ^ 2)
      _ ≤ ∫ x, M * u x ^ 2 :=
        integral_mono hρuSq (huSq.const_mul M) (fun x =>
          mul_le_mul_of_nonneg_right (hρM x) (sq_nonneg _))
      _ = M * ∫ x, u x ^ 2 := by rw [integral_const_mul]
  have hM' : 0 ≤ M * ∫ x, u x ^ 2 := mul_nonneg hM (integral_nonneg fun x => sq_nonneg (u x))
  refine ⟨hweightedMem, ?_⟩
  calc
    Real.sqrt (∫ x, u x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        Real.sqrt (M * ∫ x, u x ^ 2) := Real.sqrt_le_sqrt hIntegral
    _ = Real.sqrt M * Real.sqrt (∫ x, u x ^ 2) := by
      rw [Real.sqrt_mul hM]

private theorem fp81s21_weighted_L2_transfer_vector {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {ρ : Euc d → ℝ} {M : ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hρM : ∀ x, ρ x ≤ M)
    {u : Euc d → F} (hum : Measurable u)
    (hu : MemLp u 2 (volume : Measure (Euc d))) :
    MemLp u 2 (HRS.Whole.withDensityReal ρ) ∧
      Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        Real.sqrt M * Real.sqrt (∫ x, ‖u x‖ ^ 2) := by
  have hM : 0 ≤ M := (hρ.nonneg 0).trans (hρM 0)
  have huSq : Integrable (fun x => ‖u x‖ ^ 2) (volume : Measure (Euc d)) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hρuSq : Integrable (fun x => ρ x * ‖u x‖ ^ 2)
      (volume : Measure (Euc d)) := by
    have hmajor : Integrable (fun x => M * ‖u x‖ ^ 2)
        (volume : Measure (Euc d)) := huSq.const_mul M
    refine hmajor.mono'
      (hρ.measurable.mul ((measurable_norm.comp hum).pow_const 2)).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (hρ.nonneg x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hρM x) (sq_nonneg _)
  have hweightedSq : Integrable (fun x => ‖u x‖ ^ 2)
      (HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.withDensityReal
    rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hρuSq.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x), mul_comm]
  have huWeighted : AEStronglyMeasurable u (HRS.Whole.withDensityReal ρ) :=
    hum.aestronglyMeasurable
  have huWeightedMem : MemLp u 2 (HRS.Whole.withDensityReal ρ) :=
    (memLp_two_iff_integrable_sq_norm huWeighted).2 hweightedSq
  have hIntegral : (∫ x, ‖u x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
      M * ∫ x, ‖u x‖ ^ 2 := by
    calc
      (∫ x, ‖u x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)) =
          ∫ x, ρ x * ‖u x‖ ^ 2 :=
        HRS.MP.RdRem.mrr_integral_withDensityReal ρ hρ.measurable hρ.nonneg
          (fun x => ‖u x‖ ^ 2)
      _ ≤ ∫ x, M * ‖u x‖ ^ 2 :=
        integral_mono hρuSq (huSq.const_mul M) (fun x =>
          mul_le_mul_of_nonneg_right (hρM x) (sq_nonneg _))
      _ = M * ∫ x, ‖u x‖ ^ 2 := by rw [integral_const_mul]
  refine ⟨huWeightedMem, ?_⟩
  calc
    Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        Real.sqrt (M * ∫ x, ‖u x‖ ^ 2) := Real.sqrt_le_sqrt hIntegral
    _ = Real.sqrt M * Real.sqrt (∫ x, ‖u x‖ ^ 2) := by rw [Real.sqrt_mul hM]

private theorem fp81s21_cancel_integrable_of_bounded {d : ℕ} (hd : 2 ≤ d)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    (g : Euc d → ℝ) (hgm : Measurable g) (hg : Integrable g)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y, ‖g y‖ ≤ B) (x : Euc d) :
    Integrable (fun y : Euc d =>
      if ‖x - y‖ ≤ 1 / 4 then
        (g y - g x) • rieszKernelGrad d s (x - y)
      else g y • rieszKernelGrad d s (x - y)) := by
  have hfacts := fp81s21_kernel_facts (d := d) hd hs0 hs1
  have hlocalK : Integrable (fun z : Euc d => fp81s21_localKernel (d := d) s z) :=
    hfacts.2.2.1
  have hlocalKx : Integrable (fun y : Euc d =>
      fp81s21_localKernel (d := d) s (x - y)) := hlocalK.comp_sub_left x
  have hnearMajor : Integrable (fun y : Euc d =>
      (2 * B) * fp81s21_localKernel (d := d) s (x - y)) := hlocalKx.const_mul (2 * B)
  have hkernelM : Measurable (rieszKernelGrad d s) := HRS.MS.S111X1.kG_measurable s
  have hsubM : Measurable (fun y : Euc d =>
      rieszKernelGrad d s (x - y)) := hkernelM.comp (measurable_const.sub measurable_id)
  have hnearSet : MeasurableSet {y : Euc d | ‖x - y‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_norm.comp (measurable_const.sub measurable_id)) measurable_const
  have hnearM : Measurable (fun y : Euc d =>
      if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y) else 0) :=
    Measurable.ite hnearSet ((hgm.sub measurable_const).smul hsubM) measurable_const
  have hnear : Integrable (fun y : Euc d =>
      if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y) else 0) := by
    refine hnearMajor.mono' hnearM.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · rw [if_pos hy, norm_smul]
      have hdiff : ‖g y - g x‖ ≤ 2 * B := by
        calc
          ‖g y - g x‖ ≤ ‖g y‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hbound y) (hbound x)
          _ = 2 * B := by ring
      have hK : fp81s21_localKernel (d := d) s (x - y) =
          ‖rieszKernelGrad d s (x - y)‖ := by
        change (if ‖x - y‖ ≤ 1 / 4 then ‖rieszKernelGrad d s (x - y)‖ else 0) = _
        rw [if_pos hy]
      change ‖g y - g x‖ * ‖rieszKernelGrad d s (x - y)‖ ≤
        (2 * B) * fp81s21_localKernel (d := d) s (x - y)
      rw [hK]
      exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
    · rw [if_neg hy, norm_zero]
      change 0 ≤ (2 * B) * fp81s21_localKernel (d := d) s (x - y)
      apply mul_nonneg (by positivity)
      unfold fp81s21_localKernel
      split_ifs <;> positivity
  rcases hfacts.2.2.2.2 with ⟨C, hC, hfarK⟩
  have hfarMajor : Integrable (fun y : Euc d => C * ‖g y‖) := hg.norm.const_mul C
  have hfarSet : MeasurableSet {y : Euc d | 1 / 4 < ‖x - y‖} :=
    measurableSet_lt measurable_const
      (measurable_norm.comp (measurable_const.sub measurable_id))
  have hfarM : Measurable (fun y : Euc d =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) :=
    Measurable.ite hfarSet (hgm.smul hsubM) measurable_const
  have hfar : Integrable (fun y : Euc d =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    refine hfarMajor.mono' hfarM.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases hy : 1 / 4 < ‖x - y‖
    · rw [if_pos hy, norm_smul]
      change ‖g y‖ * ‖rieszKernelGrad d s (x - y)‖ ≤ C * ‖g y‖
      calc
        ‖g y‖ * ‖rieszKernelGrad d s (x - y)‖ ≤ ‖g y‖ * C :=
          mul_le_mul_of_nonneg_left (hfarK (x - y) hy) (norm_nonneg (g y))
        _ = C * ‖g y‖ := by ring
    · rw [if_neg hy, norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
  have hsum : Integrable (fun y : Euc d =>
      (if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y) else 0) +
      (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0)) := hnear.add hfar
  refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
  change (if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y) else 0) +
      (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) =
    if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y) else
      g y • rieszKernelGrad d s (x - y)
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · have hy' : ¬ (1 / 4 : ℝ) < ‖x - y‖ := not_lt.mpr hy
    simp only [if_pos hy, if_neg hy', add_zero]
  · have hy' : 1 / 4 < ‖x - y‖ := lt_of_not_ge hy
    simp only [if_neg hy, if_pos hy', zero_add]

private theorem fp81s21_density_component_source {d : ℕ}
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ)
    (φ : Euc d → ℝ) (hφm : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ x, ‖φ x‖ ≤ B) :
    Measurable (fun x => ρ x * φ x) ∧
      (∀ x, ‖ρ x * φ x‖ ≤ B * ‖ρ x‖) ∧
      Integrable (fun x => ρ x * φ x) := by
  have hρI : Integrable ρ (volume : Measure (Euc d)) :=
    HRS.Whole.Q34.integrable_of_isProbDensity hρ
  have hρm : Measurable ρ := hρ.measurable
  have hsourceM : Measurable (fun x => ρ x * φ x) := hρm.mul hφm
  have hmajor : Integrable (fun x : Euc d => B * ‖ρ x‖) := hρI.norm.const_mul B
  have hsourceI : Integrable (fun x => ρ x * φ x) := by
    refine hmajor.mono' hsourceM.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
    calc
      ρ x * |φ x| ≤ ρ x * B := mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using hφ x) (hρ.nonneg x)
      _ = B * ‖ρ x‖ := by rw [Real.norm_of_nonneg (hρ.nonneg x)]; ring
  refine ⟨hsourceM, ?_, hsourceI⟩
  intro x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
  calc
    ρ x * |φ x| ≤ ρ x * B := mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using hφ x) (hρ.nonneg x)
    _ = B * ‖ρ x‖ := by rw [Real.norm_of_nonneg (hρ.nonneg x)]; ring

private theorem fp81s21_coordinate_L2 {d : ℕ} {μ : Measure (Euc d)}
    {u : Euc d → Euc d} (hu : Measurable u) (hmu : MemLp u 2 μ) (j : Fin d) :
    MemLp (fun x => u x j) 2 μ ∧
      Real.sqrt (∫ x, (u x j) ^ 2 ∂μ) ≤
        Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  let uj : Euc d → ℝ := fun x => u x j
  have hujm : Measurable uj := by
    dsimp [uj]
    exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable.comp hu
  have huAES : AEStronglyMeasurable uj μ := hujm.aestronglyMeasurable
  have hnormLE : eLpNorm uj 2 μ ≤ eLpNorm u 2 μ := by
    apply eLpNorm_mono huAES
    intro x
    dsimp [uj]
    have hc := PiLp.norm_apply_le (u x) j
    simpa [Real.norm_eq_abs] using hc
  have htop : eLpNorm uj 2 μ ≠ ⊤ := ne_top_of_le_ne_top hmu.eLpNorm_ne_top hnormLE
  letI : AEStronglyMeasurable uj μ := huAES
  have hujMem : MemLp uj 2 μ :=
    memLp_iff.mpr (lt_top_iff_ne_top.mpr htop)
  have hscalar := fp81s21_eLpNorm_two_toReal hujMem
  have hvector := fp81s21_eLpNorm_two_toReal_norm hmu
  refine ⟨by simpa [uj] using hujMem, ?_⟩
  calc
    Real.sqrt (∫ x, (u x j) ^ 2 ∂μ) = (eLpNorm uj 2 μ).toReal := hscalar.symm
    _ ≤ (eLpNorm u 2 μ).toReal := ENNReal.toReal_mono hmu.eLpNorm_ne_top hnormLE
    _ = Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := hvector

private theorem fp81s21_memLp_probably_bounded {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (u : Euc d → F) (hum : Measurable u) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖u x‖ ≤ B) :
    MemLp u 2 μ ∧ Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ B := by
  have hsqI : Integrable (fun x => ‖u x‖ ^ 2) μ := by
    have hmajor : Integrable (fun _ : Euc d => B ^ 2) μ := integrable_const _
    refine hmajor.mono' ((measurable_norm.comp hum).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg (‖u x‖))]
    have hsq : ‖u x‖ ^ 2 ≤ B ^ 2 := by
      calc
        ‖u x‖ ^ 2 = ‖u x‖ * ‖u x‖ := by ring
        _ ≤ B * B := mul_le_mul (hbound x) (hbound x) (norm_nonneg _) hB
        _ = B ^ 2 := by ring
    exact hsq
  have huMem : MemLp u 2 μ := (memLp_two_iff_integrable_sq_norm hum.aestronglyMeasurable).2 hsqI
  have hIntegral : (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ B ^ 2 := by
    calc
      (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ ∫ _x, B ^ 2 ∂μ :=
        integral_mono hsqI (integrable_const _) (fun x => by
          have hsq : ‖u x‖ ^ 2 ≤ B ^ 2 := by
            calc
              ‖u x‖ ^ 2 = ‖u x‖ * ‖u x‖ := by ring
              _ ≤ B * B := mul_le_mul (hbound x) (hbound x) (norm_nonneg _) hB
              _ = B ^ 2 := by ring
          exact hsq)
      _ = B ^ 2 := by simp
  exact ⟨huMem, (Real.sqrt_le_iff).2 ⟨hB, hIntegral⟩⟩

private theorem fp81s21_L2_add {d : ℕ} {μ : Measure (Euc d)}
    {u v : Euc d → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    MemLp (fun x => u x + v x) 2 μ ∧
      Real.sqrt (∫ x, (u x + v x) ^ 2 ∂μ) ≤
        Real.sqrt (∫ x, u x ^ 2 ∂μ) + Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
  have huv : MemLp (fun x => u x + v x) 2 μ := hu.add hv
  have hsum : eLpNorm (fun x => u x + v x) 2 μ ≤ eLpNorm u 2 μ + eLpNorm v 2 μ :=
    eLpNorm_add_le (by norm_num)
  have htop : eLpNorm u 2 μ + eLpNorm v 2 μ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hu.eLpNorm_ne_top, hv.eLpNorm_ne_top⟩
  refine ⟨huv, ?_⟩
  calc
    Real.sqrt (∫ x, (u x + v x) ^ 2 ∂μ) = (eLpNorm (fun x => u x + v x) 2 μ).toReal :=
      (fp81s21_eLpNorm_two_toReal huv).symm
    _ ≤ (eLpNorm u 2 μ + eLpNorm v 2 μ).toReal := ENNReal.toReal_mono htop hsum
    _ = (eLpNorm u 2 μ).toReal + (eLpNorm v 2 μ).toReal :=
      ENNReal.toReal_add hu.eLpNorm_ne_top hv.eLpNorm_ne_top
    _ = Real.sqrt (∫ x, u x ^ 2 ∂μ) + Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
      rw [fp81s21_eLpNorm_two_toReal hu, fp81s21_eLpNorm_two_toReal hv]

private def fp81s21_relaxationField {p : HRS.MS.R26T3.Parameters} {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) (t : ℝ) : Euc p.d → ℝ := fun x =>
  (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x)

private def fp81s21_componentWeight {p : HRS.MS.R26T3.Parameters} {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) (f : Euc p.d → ℝ) (j : Fin p.d) : Euc p.d → ℝ :=
  fun x => Real.sqrt (R.ρβ x) * gradient f x j

private def fp81s21_h_input {p : HRS.MS.R26T3.Parameters} {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) (t : ℝ) (f : Euc p.d → ℝ) (j : Fin p.d) : Euc p.d → ℝ :=
  fun x => fp81s21_relaxationField R t x * fp81s21_componentWeight R f j x

private def fp81s21_h_component_claim
    {p : HRS.MS.R26T3.Parameters} {δ : ℝ} (Cinf Ctwo : ℝ)
    (R : HRS.MS.R26T3.Trajectory p δ) (t : ℝ)
    (f : Euc p.d → ℝ) (j : Fin p.d) : Prop :=
  Measurable (fp81s21_h_input R t f j) ∧
    (∃ B : ℝ, ∀ x, ‖fp81s21_h_input R t f j x‖ ≤ B) ∧
    Integrable (fp81s21_h_input R t f j) ∧
    MemLp (fp81s21_h_input R t f j) 2 (volume : Measure (Euc p.d)) ∧
    Real.sqrt (∫ x, fp81s21_h_input R t f j x ^ 2) ≤
      (Cinf * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ)) ∧
    (∫ x, ‖fp81s21_h_input R t f j x‖) ≤
      (Ctwo * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ))

/-- Component form of the moving nonlocal source.  It is measurable, bounded,
integrable and square integrable; its two source norms are controlled by the
class-uniform relative-density bounds and the test's thermal gradient norm. -/
theorem sol13_h_component_estimates (p : HRS.MS.R26T3.Parameters) :
    ∃ Cinf Ctwo M : ℝ, 0 ≤ Cinf ∧ 0 ≤ Ctwo ∧ 0 ≤ M ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
      ∀ (R : HRS.MS.R26T3.Trajectory p δ),
      ∀ (t : ℝ), 0 ≤ t → ∀ (f : Euc p.d → ℝ), MemCb 2 f → ∀ (j : Fin p.d),
        fp81s21_h_component_claim Cinf Ctwo R t f j := by
  obtain ⟨Ctwo, hCtwo, hrelax⟩ := sol13_class_relaxation_bounds p
  obtain ⟨Cinf, hCinf, hlinf⟩ := sol13_class_relaxation_linf p
  obtain ⟨M, hM, hthermal⟩ := sol13_uniform_thermal_sup_bound p
  refine ⟨Cinf, Ctwo, M, hCinf, hCtwo, hM, ?_⟩
  intro δ hδ hδh R t ht f hf j
  let μstar := HRS.Whole.withDensityReal R.ρβ
  let v : Euc p.d → ℝ := fp81s21_relaxationField R t
  let φ : Euc p.d → ℝ := fun x => gradient f x j
  let q : Euc p.d → ℝ := fp81s21_componentWeight R f j
  let g : Euc p.d → ℝ := fp81s21_h_input R t f j
  change Measurable g ∧ (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) ∧
    Integrable g ∧ MemLp g 2 (volume : Measure (Euc p.d)) ∧
    Real.sqrt (∫ x, g x ^ 2) ≤
      (Cinf * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) ∧
    (∫ x, ‖g x‖) ≤
      (Ctwo * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar)
  have hprob : HRS.Whole.IsProbDensity R.ρβ := R.thermal.1.1
  have hμprob : IsProbabilityMeasure μstar := HRS.Whole.Q34.isProbabilityMeasure_nu hprob
  letI : IsProbabilityMeasure μstar := hμprob
  have hcb := HRS.MS.S111X2.s111x2_cbNorm_bounds hf
  let B1 : ℝ := HRS.cbNorm 2 f
  let B2 : ℝ := HRS.cbNorm 2 f
  have Hf : HRS.MS.S111X2.CbD f B1 B2 := by
    simpa [B1, B2] using hcb.2
  have hB1 : 0 ≤ B1 := Hf.B1_nonneg
  have hgradCont : Continuous (gradient f) :=
    HRS.MS.S111X2.s111x2_gradient_continuous (Hf.smooth.of_le (by norm_num))
  have hφm : Measurable φ := by
    have hφcont : Continuous φ := by
      dsimp [φ]
      exact (EuclideanSpace.proj j : Euc p.d →L[ℝ] ℝ).continuous.comp hgradCont
    exact hφcont.measurable
  have hgradm : Measurable (gradient f) := hgradCont.measurable
  have hgradB : ∀ x, ‖gradient f x‖ ≤ B1 := by
    intro x
    rw [HRS.MS.S111X2.s111x2_norm_gradient]
    exact Hf.d1 x
  have hφB : ∀ x, ‖φ x‖ ≤ B1 := by
    intro x
    dsimp [φ]
    calc
      ‖gradient f x j‖ = |gradient f x j| := Real.norm_eq_abs _
      _ ≤ ‖gradient f x‖ := by
        have hc := PiLp.norm_apply_le (gradient f x) j
        simpa [Real.norm_eq_abs] using hc
      _ ≤ B1 := hgradB x
  have hthermalB : ∀ x, R.ρβ x ≤ M := hthermal δ R
  have hρm : Measurable R.ρβ := hprob.measurable
  have hsd : p.s < (p.d : ℝ) := by
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    linarith [p.hs]
  obtain ⟨_, _, hGap, _⟩ := HRS.MS.Mov0.mv0_gapref
    p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hroot : Continuous (fun x => Real.sqrt (R.ρβ x)) :=
    (HRS.MS.Mov0.mov0_sqrt_smooth hGap).continuous
  have hqm : Measurable q := by
    dsimp [q, fp81s21_componentWeight, φ]
    exact hroot.measurable.mul hφm
  have hqB : ∀ x, ‖q x‖ ≤ Real.sqrt M * B1 := by
    intro x
    have hqnorm : ‖q x‖ = Real.sqrt (R.ρβ x) * ‖φ x‖ := by
      dsimp [q, fp81s21_componentWeight, φ]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hqnorm]
    exact mul_le_mul (Real.sqrt_le_sqrt (hthermalB x)) (hφB x)
      (norm_nonneg _) (Real.sqrt_nonneg _)
  have hρI : Integrable R.ρβ (volume : Measure (Euc p.d)) :=
    HRS.Whole.Q34.integrable_of_isProbDensity hprob
  have hφSqI : Integrable (fun x => φ x ^ 2) μstar := by
    have hmajor : Integrable (fun _ : Euc p.d => B1 ^ 2) μstar := integrable_const _
    refine hmajor.mono' (hφm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg (φ x))]
    have habs : |φ x| ≤ B1 := by simpa [Real.norm_eq_abs] using hφB x
    have habsSq : |φ x| ^ 2 ≤ B1 ^ 2 := by
      calc
        |φ x| ^ 2 = |φ x| * |φ x| := by ring
        _ ≤ B1 * B1 := mul_le_mul habs habs (abs_nonneg _) hB1
        _ = B1 ^ 2 := by ring
    rw [← sq_abs]
    exact habsSq
  have hgradSqI : Integrable (fun x => ‖gradient f x‖ ^ 2) μstar := by
    have hmajor : Integrable (fun _ : Euc p.d => B1 ^ 2) μstar := integrable_const _
    refine hmajor.mono' (measurable_norm.comp hgradm |>.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hnorm := hgradB x
    nlinarith [sq_nonneg (B1 - ‖gradient f x‖), hB1, norm_nonneg (gradient f x)]
  have hφleGrad : (∫ x, φ x ^ 2 ∂μstar) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂μstar := by
    apply integral_mono hφSqI hgradSqI
    intro x
    have hc := PiLp.norm_apply_le (gradient f x) j
    dsimp [φ]
    have hcSq : ‖(gradient f x).ofLp j‖ ^ 2 ≤ ‖gradient f x‖ ^ 2 :=
      calc
        ‖(gradient f x).ofLp j‖ ^ 2 =
            ‖(gradient f x).ofLp j‖ * ‖(gradient f x).ofLp j‖ := by ring
        _ ≤ ‖gradient f x‖ * ‖gradient f x‖ :=
          mul_le_mul hc hc (norm_nonneg _) (norm_nonneg _)
        _ = ‖gradient f x‖ ^ 2 := by ring
    rw [Real.norm_eq_abs, sq_abs] at hcSq
    exact hcSq
  have hqSqI : Integrable (fun x => q x ^ 2) (volume : Measure (Euc p.d)) := by
    have hmajor : Integrable (fun x => B1 ^ 2 * R.ρβ x) (volume : Measure (Euc p.d)) :=
      hρI.const_mul (B1 ^ 2)
    refine hmajor.mono' (hqm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg (q x))]
    have hφSq : φ x ^ 2 ≤ B1 ^ 2 := by
      have habs : |φ x| ≤ B1 := by simpa [Real.norm_eq_abs] using hφB x
      have habsSq : |φ x| ^ 2 ≤ B1 ^ 2 := by
        calc
          |φ x| ^ 2 = |φ x| * |φ x| := by ring
          _ ≤ B1 * B1 := mul_le_mul habs habs (abs_nonneg _) hB1
          _ = B1 ^ 2 := by ring
      rw [← sq_abs]
      exact habsSq
    have hqeq : q x ^ 2 = R.ρβ x * φ x ^ 2 := by
      dsimp [q, fp81s21_componentWeight]
      rw [mul_pow, Real.sq_sqrt (hprob.nonneg x)]
    rw [hqeq]
    calc
      R.ρβ x * φ x ^ 2 ≤ R.ρβ x * B1 ^ 2 :=
        mul_le_mul_of_nonneg_left hφSq (hprob.nonneg x)
      _ = B1 ^ 2 * R.ρβ x := by ring
  have hqLp : MemLp q 2 (volume : Measure (Euc p.d)) :=
    (memLp_two_iff_integrable_sq hqm.aestronglyMeasurable).2 hqSqI
  have hqIntegral : (∫ x, q x ^ 2) = ∫ x, φ x ^ 2 ∂μstar := by
    calc
      (∫ x, q x ^ 2) = ∫ x, R.ρβ x * φ x ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp [q, fp81s21_componentWeight]
        rw [mul_pow, Real.sq_sqrt (hprob.nonneg x)]
      _ = ∫ x, φ x ^ 2 ∂μstar :=
        (HRS.MP.RdRem.mrr_integral_withDensityReal R.ρβ hprob.measurable hprob.nonneg
          (fun x => φ x ^ 2)).symm
  have hrel := hrelax δ hδ hδh R t ht
  have hv : MemLp v 2 (volume : Measure (Euc p.d)) := by
    change MemLp (fun x => (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x))
      2 (volume : Measure (Euc p.d))
    exact hrel.2.1
  have hvmeas : Measurable v := by
    dsimp [v, fp81s21_relaxationField]
    have hreg := R.resulting.regular t ht
    exact (((hreg.sub hGap.smooth.continuous).div hroot fun x => by
      exact (Real.sqrt_pos.2 (hGap.pos x)).ne').measurable)
  have hvB : ∀ x, ‖v x‖ ≤ Cinf * δ * Real.exp (-p.c₁ * t) := by
    simpa [v, fp81s21_relaxationField] using hlinf δ hδ hδh R t ht
  have hV : 0 ≤ Cinf * δ * Real.exp (-p.c₁ * t) :=
    mul_nonneg (mul_nonneg hCinf hδ.le) (Real.exp_pos _).le
  have hQ : 0 ≤ Real.sqrt M * B1 := mul_nonneg (Real.sqrt_nonneg _) hB1
  have hprod := fp81s21_product_source_estimates hvmeas hqm hv hqLp hV hvB hQ hqB
  have hvnorm := fp81s21_eLpNorm_two_toReal hv
  have hvs := hrel.2.2
  have hvs' : Real.sqrt (∫ x, v x ^ 2) ≤ Ctwo * δ * Real.exp (-p.c₁ * t) := by
    rw [← hvnorm]
    change (eLpNorm (fun x => (R.ρ t x - R.ρβ x) / Real.sqrt (R.ρβ x))
      2 (volume : Measure (Euc p.d))).toReal ≤ _
    exact hvs
  have hweightedNorm : Real.sqrt (∫ x, q x ^ 2) ≤
      Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    rw [hqIntegral]
    exact Real.sqrt_le_sqrt hφleGrad
  refine ⟨hprod.1, hprod.2.1, hprod.2.2.1, hprod.2.2.2.1, ?_, ?_⟩
  · calc
      Real.sqrt (∫ x, g x ^ 2) ≤
          (Cinf * δ * Real.exp (-p.c₁ * t)) * Real.sqrt (∫ x, q x ^ 2) := hprod.2.2.2.2.1
      _ ≤ (Cinf * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
        mul_le_mul_of_nonneg_left hweightedNorm hV
  · calc
      (∫ x, ‖g x‖) ≤ Real.sqrt (∫ x, v x ^ 2) * Real.sqrt (∫ x, q x ^ 2) :=
        hprod.2.2.2.2.2
      _ ≤ (Ctwo * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
        mul_le_mul hvs' hweightedNorm (Real.sqrt_nonneg _) (by positivity)

/-- The difference of the two cancellation convolutions is the convolution
of the signed relative-density source.  The cancellation integrands are
integrable because their near part is controlled by the locally integrable
kernel and their far part by the integrable densities. -/
theorem sol13_conv_difference_linearity (p : HRS.MS.R26T3.Parameters) :
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
      ∀ (R : HRS.MS.R26T3.Trajectory p δ),
      ∀ (t : ℝ), 0 ≤ t → ∀ (f : Euc p.d → ℝ), MemCb 2 f →
      ∀ (j : Fin p.d) (x : Euc p.d),
        convGradConvW (rieszKernelGrad p.d p.s)
            (fun y => R.ρ t y *
              (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
                (gradient f y)) j) x -
          convGradConvW (rieszKernelGrad p.d p.s)
            (fun y => R.ρβ y *
              (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
                (gradient f y)) j) x =
          convGradConvW (rieszKernelGrad p.d p.s)
            (fun y => -fp81s21_h_input R t f j y) x := by
  intro δ hδ hδh R t ht f hf j x
  obtain ⟨M, hM, hthermal⟩ := sol13_uniform_thermal_sup_bound p
  have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hs1 : p.s + 1 < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨_, _, hGap, _⟩ := HRS.MS.Mov0.mv0_gapref
    p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρstar : HRS.Whole.IsProbDensity R.ρβ := R.thermal.1.1
  have hρt : HRS.Whole.IsProbDensity (R.ρ t) := by
    have hsolution := R.resulting.global t
    exact hsolution.density t ⟨ht, le_rfl⟩
  have hC1 : 0 ≤ p.C₁ := by
    have hr := R.resulting.ratio t ht 0
    have hρt0 := hρt.nonneg 0
    have hβ0 := hGap.pos 0
    by_contra hn
    have hn' : p.C₁ < 0 := lt_of_not_ge hn
    have hneg : p.C₁ * R.ρβ 0 < 0 := mul_neg_of_neg_of_pos hn' hβ0
    exact (not_lt_of_ge (le_trans hρt0 hr.2)) hneg
  have hρtBound : ∀ y, R.ρ t y ≤ p.C₁ * M := by
    intro y
    calc
      R.ρ t y ≤ p.C₁ * R.ρβ y := (R.resulting.ratio t ht y).2
      _ ≤ p.C₁ * M := mul_le_mul_of_nonneg_left (hthermal δ R y) hC1
  have hcb := HRS.MS.S111X2.s111x2_cbNorm_bounds hf
  let B1 : ℝ := HRS.cbNorm 2 f
  let B2 : ℝ := HRS.cbNorm 2 f
  have Hf : HRS.MS.S111X2.CbD f B1 B2 := by
    simpa [B1, B2] using hcb.2
  have hB1 : 0 ≤ B1 := Hf.B1_nonneg
  have hgradCont : Continuous (gradient f) :=
    HRS.MS.S111X2.s111x2_gradient_continuous (Hf.smooth.of_le (by norm_num))
  have hgradB : ∀ y, ‖gradient f y‖ ≤ B1 := by
    intro y
    rw [HRS.MS.S111X2.s111x2_norm_gradient]
    exact Hf.d1 y
  let φ : Euc p.d → ℝ := fun y =>
    -gradient f y j
  have hmatCoord : ∀ y,
      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
        (gradient f y)) j = -gradient f y j := by
    intro y
    simpa using congrArg (fun w : Euc p.d => w j)
      (HRS.MS.Wad.s84_matVec_neg_T (gradient f y))
  have hφm : Measurable φ := by
    have hφc : Continuous φ := by
      dsimp [φ]
      exact ((EuclideanSpace.proj j : Euc p.d →L[ℝ] ℝ).continuous.comp hgradCont).neg
    exact hφc.measurable
  have hφB : ∀ y, ‖φ y‖ ≤ B1 := by
    intro y
    rw [Real.norm_eq_abs, abs_neg]
    calc
      |gradient f y j| ≤ ‖gradient f y‖ := by
        have hc := PiLp.norm_apply_le (gradient f y) j
        simpa [Real.norm_eq_abs] using hc
      _ ≤ B1 := hgradB y
  have hBmove : 0 ≤ (p.C₁ * M) * B1 :=
    mul_nonneg (mul_nonneg hC1 hM) hB1
  have hBstar : 0 ≤ M * B1 := mul_nonneg hM hB1
  let uMove : Euc p.d → ℝ := fun y => R.ρ t y * φ y
  let uStar : Euc p.d → ℝ := fun y => R.ρβ y * φ y
  have hMoveSrc := fp81s21_density_component_source (R.ρ t) hρt φ hφm hB1 hφB
  have hStarSrc := fp81s21_density_component_source R.ρβ hρstar φ hφm hB1 hφB
  have huMoveM : Measurable uMove := by simpa [uMove] using hMoveSrc.1
  have huMoveI : Integrable uMove := by simpa [uMove] using hMoveSrc.2.2
  have huStarM : Measurable uStar := by simpa [uStar] using hStarSrc.1
  have huStarI : Integrable uStar := by simpa [uStar] using hStarSrc.2.2
  have huMoveB : ∀ y, ‖uMove y‖ ≤ (p.C₁ * M) * B1 := by
    intro y
    calc
      ‖uMove y‖ ≤ B1 * ‖R.ρ t y‖ := by simpa [uMove] using hMoveSrc.2.1 y
      _ = B1 * R.ρ t y := by rw [Real.norm_of_nonneg (hρt.nonneg y)]
      _ ≤ B1 * (p.C₁ * M) := mul_le_mul_of_nonneg_left (hρtBound y) hB1
      _ = (p.C₁ * M) * B1 := by ring
  have huStarB : ∀ y, ‖uStar y‖ ≤ M * B1 := by
    intro y
    calc
      ‖uStar y‖ ≤ B1 * ‖R.ρβ y‖ := by simpa [uStar] using hStarSrc.2.1 y
      _ = B1 * R.ρβ y := by rw [Real.norm_of_nonneg (hρstar.nonneg y)]
      _ ≤ B1 * M := mul_le_mul_of_nonneg_left (hthermal δ R y) hB1
      _ = M * B1 := by ring
  have hcancelMove := fp81s21_cancel_integrable_of_bounded
    (d := p.d) p.hd p.hs0 hs1 uMove huMoveM huMoveI hBmove huMoveB x
  have hcancelStar := fp81s21_cancel_integrable_of_bounded
    (d := p.d) p.hd p.hs0 hs1 uStar huStarM huStarI hBstar huStarB x
  have hlin := HRS.MS.Wad.s84_conv_sub (d := p.d) (s := p.s)
    (u₁ := uMove) (u₂ := uStar) x hcancelMove hcancelStar
  have hmoveFun : (fun y => R.ρ t y *
      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
        (gradient f y)) j) = uMove := by
    funext y
    have hmul := congrArg (fun z : ℝ => R.ρ t y * z) (hmatCoord y)
    simpa [uMove, φ, Matrix.transpose_neg] using hmul
  have hstarFun : (fun y => R.ρβ y *
      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
        (gradient f y)) j) = uStar := by
    funext y
    have hmul := congrArg (fun z : ℝ => R.ρβ y * z) (hmatCoord y)
    simpa [uStar, φ, Matrix.transpose_neg] using hmul
  calc
    convGradConvW (rieszKernelGrad p.d p.s)
        (fun y => R.ρ t y *
          (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
            (gradient f y)) j) x -
        convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρβ y *
            (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
              (gradient f y)) j) x =
        convGradConvW (rieszKernelGrad p.d p.s) uMove x -
          convGradConvW (rieszKernelGrad p.d p.s) uStar x := by
            rw [hmoveFun, hstarFun]
    _ = convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => uMove y - uStar y) x := hlin.symm
    _ = convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => -fp81s21_h_input R t f j y) x := by
      congr 1
      funext y
      simp only [uMove, uStar, φ]
      dsimp [fp81s21_h_input, fp81s21_componentWeight, fp81s21_relaxationField]
      have hroot : Real.sqrt (R.ρβ y) ≠ 0 := (Real.sqrt_pos.2 (hGap.pos y)).ne'
      field_simp [hroot]
      ring

/-- Each component of the moving-minus-thermal nonlocal force is square
integrable in the thermal measure, with the uniform decaying gradient bound. -/
theorem sol13_nonlocal_component_estimates (p : HRS.MS.R26T3.Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
        ∀ (R : HRS.MS.R26T3.Trajectory p δ),
          ∀ (t : ℝ), 0 ≤ t → ∀ (f : Euc p.d → ℝ), MemCb 2 f →
            ∀ (j : Fin p.d),
              MemLp (fun x =>
                (convGradConvW (rieszKernelGrad p.d p.s)
                    (fun y => R.ρ t y *
                      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
                        (gradient f y)) j) x -
                  convGradConvW (rieszKernelGrad p.d p.s)
                    (fun y => R.ρβ y *
                      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
                        (gradient f y)) j) x) j)
                2 (HRS.Whole.withDensityReal R.ρβ) ∧
              Real.sqrt (∫ x,
                ((convGradConvW (rieszKernelGrad p.d p.s)
                    (fun y => R.ρ t y *
                      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
                        (gradient f y)) j) x -
                  convGradConvW (rieszKernelGrad p.d p.s)
                    (fun y => R.ρβ y *
                      (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
                        (gradient f y)) j) x) j) ^ 2
                ∂(HRS.Whole.withDensityReal R.ρβ)) ≤
                (C * δ * Real.exp (-p.c₁ * t)) *
                  Real.sqrt (∫ x, ‖gradient f x‖ ^ 2
                    ∂(HRS.Whole.withDensityReal R.ρβ)) := by
  obtain ⟨Cinf, Ctwo, _, hCinf, hCtwo, _, hsource⟩ :=
    sol13_h_component_estimates p
  obtain ⟨Mth, hMth, hthermal⟩ := sol13_uniform_thermal_sup_bound p
  have hsd : p.s < (p.d : ℝ) := by
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    linarith [p.hs]
  have hs1 : p.s + 1 < (p.d : ℝ) := by
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    linarith [p.hs]
  obtain ⟨CL, CF, hCL, hCF, hconvBound⟩ :=
    fp81s21_conv_split_bound (d := p.d) p.hd p.hs0 hs1
  let CNL : ℝ := Real.sqrt Mth * CL * Cinf + CF * Ctwo
  have hCNL : 0 ≤ CNL := by
    dsimp [CNL]
    positivity
  refine ⟨CNL, hCNL, ?_⟩
  intro δ hδ hδh R t ht f hf j
  let μstar := HRS.Whole.withDensityReal R.ρβ
  have hρstar : HRS.Whole.IsProbDensity R.ρβ := R.thermal.1.1
  have hμprob : IsProbabilityMeasure μstar := HRS.Whole.Q34.isProbabilityMeasure_nu hρstar
  letI : IsProbabilityMeasure μstar := hμprob
  have hthermalB : ∀ x, R.ρβ x ≤ Mth := hthermal δ R
  have hclaim := hsource δ hδ hδh R t ht f hf j
  dsimp [fp81s21_h_component_claim] at hclaim
  let gpos : Euc p.d → ℝ := fp81s21_h_input R t f j
  let gneg : Euc p.d → ℝ := fun x => -gpos x
  have hgposM : Measurable gpos := by simpa [gpos] using hclaim.1
  have hgnegM : Measurable gneg := by
    dsimp [gneg]
    exact hgposM.neg
  obtain ⟨B, hB⟩ := hclaim.2.1
  have hB0 : 0 ≤ B := (norm_nonneg (gpos 0)).trans (by
    simpa [Real.norm_eq_abs] using hB 0)
  have hgnegBound : ∀ x, ‖gneg x‖ ≤ B := by
    intro x
    simpa [gneg] using hB x
  have hgnegI : Integrable gneg := by
    simpa [gneg] using hclaim.2.2.1.neg
  have hgnegLp : MemLp gneg 2 (volume : Measure (Euc p.d)) := by
    change MemLp (fun x => -fp81s21_h_input R t f j x) 2
      (volume : Measure (Euc p.d))
    exact hclaim.2.2.2.1.neg
  have hnegL2 : Real.sqrt (∫ x, gneg x ^ 2) = Real.sqrt (∫ x, gpos x ^ 2) := by
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [gneg]
  have hnegL1 : (∫ x, ‖gneg x‖) = ∫ x, ‖gpos x‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [gneg]
  have hconvData := hconvBound gneg hgnegM ⟨B, hgnegBound⟩ hgnegI hgnegLp
  let localV : Euc p.d → Euc p.d :=
    fp81s21_localConv (d := p.d) p.s gneg
  let farV : Euc p.d → Euc p.d :=
    fp81s21_farConv (d := p.d) p.s gneg
  have hlocalVM : Measurable localV :=
    fp81s21_localConv_measurable (d := p.d) (s := p.s) gneg hgnegM
  have hlocalProductTop : ENNReal.ofReal CL * eLpNorm gneg 2
      (volume : Measure (Euc p.d)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgnegLp.eLpNorm_ne_top
  have hlocalTop : eLpNorm localV 2 (volume : Measure (Euc p.d)) ≠ ⊤ :=
    ne_top_of_le_ne_top hlocalProductTop hconvData.2.1
  letI : AEStronglyMeasurable localV (volume : Measure (Euc p.d)) :=
    hlocalVM.aestronglyMeasurable
  have hlocalMem : MemLp localV 2 (volume : Measure (Euc p.d)) :=
    memLp_iff.mpr (lt_top_iff_ne_top.mpr hlocalTop)
  have hthermalBound : ∀ x, R.ρβ x ≤ Mth := hthermalB
  have hlocalTransfer := fp81s21_weighted_L2_transfer_vector
    hρstar hthermalBound hlocalVM hlocalMem
  have hlocalDx : Real.sqrt (∫ x, ‖localV x‖ ^ 2) ≤
      CL * Real.sqrt (∫ x, gneg x ^ 2) := by
    have hlocalNorm := fp81s21_eLpNorm_two_toReal_norm hlocalMem
    have hgNorm := fp81s21_eLpNorm_two_toReal hgnegLp
    calc
      Real.sqrt (∫ x, ‖localV x‖ ^ 2) =
          (eLpNorm localV 2 (volume : Measure (Euc p.d))).toReal := hlocalNorm.symm
      _ ≤ (ENNReal.ofReal CL * eLpNorm gneg 2 (volume : Measure (Euc p.d))).toReal :=
        ENNReal.toReal_mono hlocalProductTop hconvData.2.1
      _ = CL * Real.sqrt (∫ x, gneg x ^ 2) := by
        rw [ENNReal.toReal_mul,
          ENNReal.toReal_ofReal hCL, hgNorm]
  have hfarMeasConv : Measurable (convGradConvW (rieszKernelGrad p.d p.s) gneg) :=
    HRS.MS.Wad.s8h2_conv_meas (HRS.MS.S111X1.kG_measurable p.s) hgnegM
  have hfarEq : farV = fun x =>
      convGradConvW (rieszKernelGrad p.d p.s) gneg x - localV x := by
    funext x
    rw [hconvData.1 x]
    simp [localV, farV]
  have hfarVM : Measurable farV := by
    rw [hfarEq]
    exact hfarMeasConv.sub hlocalVM
  let Bfar : ℝ := CF * ∫ x, ‖gneg x‖
  have hBfar : 0 ≤ Bfar := by
    dsimp [Bfar]
    exact mul_nonneg hCF (integral_nonneg fun x => abs_nonneg (gneg x))
  have hfarBound : ∀ x, ‖farV x‖ ≤ Bfar := by
    intro x
    simpa [farV, Bfar] using hconvData.2.2 x
  have hfarProb := fp81s21_memLp_probably_bounded
    (d := p.d) (μ := μstar) farV hfarVM hBfar hfarBound
  have hfarSourceL1 : (∫ x, ‖gneg x‖) ≤
      (Ctwo * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    rw [hnegL1]
    exact hclaim.2.2.2.2.2
  have hfarL2Final : Real.sqrt (∫ x, ‖farV x‖ ^ 2 ∂μstar) ≤
      (CF * Ctwo * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    calc
      Real.sqrt (∫ x, ‖farV x‖ ^ 2 ∂μstar) ≤ Bfar := hfarProb.2
      _ ≤ CF * ((Ctwo * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar)) := by
        dsimp [Bfar]
        exact mul_le_mul_of_nonneg_left hfarSourceL1 hCF
      _ = (CF * Ctwo * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by ring
  have hlocalCoord := fp81s21_coordinate_L2 hlocalVM hlocalTransfer.1 j
  have hfarCoord := fp81s21_coordinate_L2 hfarVM hfarProb.1 j
  let nfun : Euc p.d → ℝ := fun x =>
    (convGradConvW (rieszKernelGrad p.d p.s) gneg x) j
  have hsplitCoord : ∀ x, nfun x = localV x j + farV x j := by
    intro x
    have heq := congrArg (fun z : Euc p.d => z j) (hconvData.1 x)
    simpa [nfun, localV, farV] using heq
  have hsumMem : MemLp (fun x => localV x j + farV x j) 2 μstar :=
    hlocalCoord.1.add hfarCoord.1
  have hnMem : MemLp nfun 2 μstar :=
    (memLp_congr_ae (Filter.Eventually.of_forall hsplitCoord)).2 hsumMem
  have hlin := sol13_conv_difference_linearity p δ hδ hδh R t ht f hf j
  let target : Euc p.d → ℝ := fun x =>
    (convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρ t y *
            (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
              (gradient f y)) j) x -
      convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρβ y *
            (Torus.matVec (-1 : Matrix (Fin p.d) (Fin p.d) ℝ).transpose
              (gradient f y)) j) x) j
  have htargetEq : ∀ x, target x = localV x j + farV x j := by
    intro x
    calc
      target x = nfun x := by
        dsimp [target, nfun]
        exact congrArg (fun z : Euc p.d => z j) (hlin x)
      _ = localV x j + farV x j := hsplitCoord x
  have htargetMem : MemLp target 2 μstar := by
    have htargetConv : MemLp target 2 μstar :=
      (memLp_congr_ae (Filter.Eventually.of_forall fun x => htargetEq x)).2 hsumMem
    exact htargetConv
  have hL2add := fp81s21_L2_add hlocalCoord.1 hfarCoord.1
  have hlocalL2Final : Real.sqrt (∫ x, (localV x j) ^ 2 ∂μstar) ≤
      (Real.sqrt Mth * CL * Cinf * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    have hsourceL2 : Real.sqrt (∫ x, gneg x ^ 2) ≤
        (Cinf * δ * Real.exp (-p.c₁ * t)) *
          Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
      rw [hnegL2]
      exact hclaim.2.2.2.2.1
    calc
      Real.sqrt (∫ x, (localV x j) ^ 2 ∂μstar) ≤
          Real.sqrt Mth * Real.sqrt (∫ x, ‖localV x‖ ^ 2) := hlocalCoord.2.trans hlocalTransfer.2
      _ ≤ Real.sqrt Mth * (CL * Real.sqrt (∫ x, gneg x ^ 2)) :=
        mul_le_mul_of_nonneg_left hlocalDx (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt Mth * (CL * ((Cinf * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsourceL2 hCL) (Real.sqrt_nonneg _)
      _ = (Real.sqrt Mth * CL * Cinf * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by ring
  have htargetIntegral : (∫ x, target x ^ 2 ∂μstar) =
      ∫ x, (localV x j + farV x j) ^ 2 ∂μstar := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [htargetEq x]
  have hfarCoordL2Final : Real.sqrt (∫ x, (farV x j) ^ 2 ∂μstar) ≤
      (CF * Ctwo * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
    hfarCoord.2.trans hfarL2Final
  have htargetL2 : Real.sqrt (∫ x, target x ^ 2 ∂μstar) ≤
      (CNL * δ * Real.exp (-p.c₁ * t)) *
        Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
    calc
      Real.sqrt (∫ x, target x ^ 2 ∂μstar) =
          Real.sqrt (∫ x, (localV x j + farV x j) ^ 2 ∂μstar) := by rw [htargetIntegral]
      _ ≤ Real.sqrt (∫ x, (localV x j) ^ 2 ∂μstar) +
            Real.sqrt (∫ x, (farV x j) ^ 2 ∂μstar) := hL2add.2
      _ ≤ (Real.sqrt Mth * CL * Cinf * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) +
          (CF * Ctwo * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) :=
        add_le_add hlocalL2Final hfarCoordL2Final
      _ = (CNL * δ * Real.exp (-p.c₁ * t)) *
            Real.sqrt (∫ x, ‖gradient f x‖ ^ 2 ∂μstar) := by
        dsimp [CNL]
        ring
  refine ⟨by simpa [target, μstar] using htargetMem, ?_⟩
  simpa [target, μstar] using htargetL2

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.sol13_uniform_thermal_sup_bound
#print axioms HRS.Fp81.S21.sol13_h_component_estimates
#print axioms HRS.Fp81.S21.sol13_conv_difference_linearity
#print axioms HRS.Fp81.S21.sol13_nonlocal_component_estimates

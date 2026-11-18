import HRS.MS.Fp81S21ChaosLimit
import HRS.MC.E213U13k
import HRS.MS.Fp81S21EmbedField12
import HRS.MS.Fp81S21TimeRep9
import HRS.MS.ProClosureS111PairingLimits
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6 HRS.MS.ProClosureS111

namespace HRS.Fp81.S21

/-- A continuous linear observation preserves membership in the first chaos
of the same Gaussian sequence. -/
theorem fp81s21_firstChaos_clm
    {B₁ B₂ Ω : Type*} [NormedAddCommGroup B₁] [NormedSpace ℝ B₁]
    [NormedAddCommGroup B₂] [NormedSpace ℝ B₂]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {W : Ω → B₁}
    (hW : InFirstChaos P ξ 2 W) (Λ : B₁ →L[ℝ] B₂) :
    InFirstChaos P ξ 2 (fun ω => Λ (W ω)) := by
  exact InFirstChaos.clm Λ (by norm_num) hW

private theorem fp81s21_InQ1_of_prod_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {ν : Measure ℝ} [SFinite ν]
    {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)}
    {f : ℕ → Ω → ℝ → ℝ} {g B : Ω → ℝ → ℝ} {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hfm : ∀ n, Measurable (Function.uncurry (f n))) (hgm : Measurable (Function.uncurry g))
    (hBm : Measurable (Function.uncurry B)) (hB0 : ∀ ω v, 0 ≤ B ω v)
    (hfQ : ∀ n, ∀ᵐ v ∂ν, InQ1 hξ hm (fun ω => f n ω v))
    (hlim : ∀ ω v, Tendsto (fun n => f n ω v) atTop (𝓝 (g ω v)))
    (hdom : ∀ n ω v, |f n ω v| ≤ B ω v)
    (hBint : ∀ᵐ ω ∂P, Integrable (B ω) ν)
    (hBL2 : MemLp (fun ω => ∫ v, B ω v ∂ν) 2 P)
    (hZ : Z =ᵐ[P] fun ω => ∫ v, g ω v ∂ν) : InQ1 hξ hm Z := by
  classical
  refine ⟨hZ2, ?_⟩
  set Q : Submodule ℝ (Lp ℝ 2 P) := Qc (K1 hξ hm) with hQdef
  have hQclosed : IsClosed (Q : Set (Lp ℝ 2 P)) := Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace Q := hQclosed.completeSpace_coe
  haveI : Q.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace Q
  suffices h : hZ2.toLp Z ∈ Qᗮᗮ by rwa [Submodule.orthogonal_orthogonal] at h
  rw [Submodule.mem_orthogonal]
  intro w hw
  set wf : Ω → ℝ := (w : Ω → ℝ) with hwf
  have hwL : MemLp wf 2 P := Lp.memLp w
  have hwm : Measurable wf := (Lp.stronglyMeasurable w).measurable
  have hBdomm : AEStronglyMeasurable (fun p : Ω × ℝ => ‖wf p.1‖ * B p.1 p.2) (P.prod ν) :=
    (((hwm.comp measurable_fst).norm).mul hBm).aestronglyMeasurable
  have hBdom : Integrable (fun p : Ω × ℝ => ‖wf p.1‖ * B p.1 p.2) (P.prod ν) := by
    rw [integrable_prod_iff hBdomm]
    refine ⟨?_, ?_⟩
    · filter_upwards [hBint] with ω hω
      exact (hω.const_mul ‖wf ω‖)
    · have : (fun ω => ∫ v, ‖‖wf ω‖ * B ω v‖ ∂ν) = fun ω => ‖wf ω‖ * ∫ v, B ω v ∂ν := by
        funext ω
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [norm_mul, norm_norm, Real.norm_eq_abs, abs_of_nonneg (hB0 ω v), abs_abs]
      rw [this]
      exact hwL.norm.integrable_mul hBL2
  have hGint : ∀ n, Integrable (fun p : Ω × ℝ => wf p.1 * f n p.1 p.2) (P.prod ν) := by
    intro n
    refine hBdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hwm.comp measurable_fst).mul (hfm n)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (f n p.1 p.2)]
      exact mul_le_mul_of_nonneg_left (hdom n p.1 p.2) (norm_nonneg _)
  have hgB : ∀ ω v, |g ω v| ≤ B ω v := fun ω v =>
    le_of_tendsto (continuous_abs.continuousAt.tendsto.comp (hlim ω v)) (Eventually.of_forall fun n => hdom n ω v)
  have hgint : Integrable (fun p : Ω × ℝ => wf p.1 * g p.1 p.2) (P.prod ν) := by
    refine hBdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hwm.comp measurable_fst).mul hgm).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (g p.1 p.2)]
      exact mul_le_mul_of_nonneg_left (hgB p.1 p.2) (norm_nonneg _)
  have hT : Tendsto (fun n => ∫ p, wf p.1 * f n p.1 p.2 ∂(P.prod ν)) atTop
      (𝓝 (∫ p, wf p.1 * g p.1 p.2 ∂(P.prod ν))) := by
    refine tendsto_integral_of_dominated_convergence (fun p => ‖wf p.1‖ * B p.1 p.2)
      (fun n => (hGint n).aestronglyMeasurable) hBdom (fun n => Eventually.of_forall fun p => ?_)
      (Eventually.of_forall fun p => (hlim p.1 p.2).const_mul (wf p.1))
    rw [norm_mul, Real.norm_eq_abs (f n p.1 p.2)]
    exact mul_le_mul_of_nonneg_left (hdom n p.1 p.2) (norm_nonneg _)
  have hzero : ∀ n, ∫ p, wf p.1 * f n p.1 p.2 ∂(P.prod ν) = 0 := by
    intro n
    rw [integral_prod_symm _ (hGint n)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfQ n] with v hv
    obtain ⟨h1, hc⟩ := hv
    have := integral_mul_eq_inner w (h1.toLp _) (a := wf) (b := fun ω => f n ω v) Filter.EventuallyEq.rfl h1.coeFn_toLp
    simp only [Pi.zero_apply]
    rw [this]
    exact Submodule.inner_left_of_mem_orthogonal hc hw
  have hlimzero : ∫ p, wf p.1 * g p.1 p.2 ∂(P.prod ν) = 0 := by
    refine tendsto_nhds_unique hT ?_
    simp only [hzero]
    exact tendsto_const_nhds
  rw [← integral_mul_eq_inner w (hZ2.toLp Z) (a := wf) (b := Z) Filter.EventuallyEq.rfl hZ2.coeFn_toLp]
  calc ∫ ω, wf ω * Z ω ∂P = ∫ ω, wf ω * ∫ v, g ω v ∂ν ∂P :=
        integral_congr_ae (by filter_upwards [hZ] with ω h; rw [h])
    _ = ∫ ω, ∫ v, wf ω * g ω v ∂ν ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only
        rw [integral_const_mul]
    _ = ∫ p, wf p.1 * g p.1 p.2 ∂(P.prod ν) := (integral_prod _ hgint).symm
    _ = 0 := hlimzero


section ScalarClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

private theorem fp81s21_InQ1_add {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {Y Z : Ω → ℝ} (hY : InQ1 hξ hm Y) (hZ : InQ1 hξ hm Z) :
    InQ1 hξ hm (fun ω => Y ω + Z ω) := by
  obtain ⟨h1, c1⟩ := hY
  obtain ⟨h2, c2⟩ := hZ
  refine ⟨h1.add h2, ?_⟩
  have e : MemLp.toLp (fun ω => Y ω + Z ω) (h1.add h2) = h1.toLp Y + h2.toLp Z := MemLp.toLp_add h1 h2
  rw [e]
  exact add_mem c1 c2

private theorem fp81s21_InQ1_const_mul {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {Y : Ω → ℝ} (c : ℝ) (hY : InQ1 hξ hm Y) :
    InQ1 hξ hm (fun ω => c * Y ω) := by
  obtain ⟨h1, c1⟩ := hY
  refine ⟨h1.const_mul c, ?_⟩
  have e : MemLp.toLp (fun ω => c * Y ω) (h1.const_mul c) = c • h1.toLp Y := by
    have := MemLp.toLp_const_smul (μ := P) c h1
    exact this
  rw [e]
  exact Submodule.smul_mem _ _ c1

private theorem fp81s21_InQ1_zero {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} : InQ1 hξ hm (fun _ : Ω => (0 : ℝ)) := by
  have hz : MemLp (fun _ : Ω => (0 : ℝ)) 2 P := MemLp.zero
  refine ⟨hz, ?_⟩
  have e : hz.toLp (fun _ : Ω => (0 : ℝ)) = 0 := MemLp.toLp_zero hz
  rw [e]
  exact zero_mem _

private theorem fp81s21_InQ1_sum {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {ι : Type*} (s : Finset ι) {Y : ι → Ω → ℝ}
    (hY : ∀ i ∈ s, InQ1 hξ hm (Y i)) : InQ1 hξ hm (fun ω => ∑ i ∈ s, Y i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fp81s21_InQ1_zero (hξ := hξ)
  | insert a s ha ih =>
    have h1 := fp81s21_InQ1_add (hY a (Finset.mem_insert_self _ _)) (ih fun i hi => hY i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

private theorem fp81s21_InQ1_congr_ae {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {Y Z : Ω → ℝ} (h : Y =ᵐ[P] Z) (hY : InQ1 hξ hm Y) :
    InQ1 hξ hm Z := by
  obtain ⟨h1, c1⟩ := hY
  refine ⟨h1.ae_eq h, ?_⟩
  rwa [← MemLp.toLp_congr h1 (h1.ae_eq h) h]

private theorem fp81s21_InQ1_of_tendsto {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {ι : Type*} {l : Filter ι} [l.NeBot] {Y : ι → Ω → ℝ}
    {Z : Ω → ℝ} (hY : ∀ i, InQ1 hξ hm (Y i)) (hZ : AEStronglyMeasurable Z P)
    (hlim : Tendsto (fun i => ∫⁻ ω, ‖Y i ω - Z ω‖ₑ ^ (2 : ℝ) ∂P) l (𝓝 0)) : InQ1 hξ hm Z := by
  choose h hc using hY
  have hsub : ∀ i, AEStronglyMeasurable (fun ω => Y i ω - Z ω) P := fun i =>
    (h i).aestronglyMeasurable.sub hZ
  have hE : ∀ i, ∫⁻ ω, ‖Y i ω - Z ω‖ₑ ^ (2 : ℝ) ∂P = eLpNorm (fun ω => Y i ω - Z ω) 2 P ^ (2 : ℝ) :=
    fun i => lintegral_enorm_rpow_two (hsub i)
  have hN : Tendsto (fun i => eLpNorm (fun ω => Y i ω - Z ω) 2 P) l (𝓝 0) := by
    have h1 : Tendsto (fun i => eLpNorm (fun ω => Y i ω - Z ω) 2 P ^ (2 : ℝ)) l (𝓝 0) := by
      simpa only [hE] using hlim
    have h2 := ((ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr fun i => ?_
    simp only [Function.comp]
    exact ENNReal.rpow_rpow_inv (by norm_num) _
  have hfin : ∀ᶠ i in l, eLpNorm (fun ω => Y i ω - Z ω) 2 P < ∞ :=
    hN.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  obtain ⟨i0, hi0⟩ := hfin.exists
  have hd : MemLp (fun ω => Y i0 ω - Z ω) 2 P := hi0
  have hZ2 : MemLp Z 2 P := by
    have h3 : MemLp (fun ω => Y i0 ω - (Y i0 ω - Z ω)) 2 P := (h i0).sub hd
    have e : (fun ω => Y i0 ω - (Y i0 ω - Z ω)) = Z := by funext ω; ring
    rwa [e] at h3
  refine ⟨hZ2, ?_⟩
  have hcl : IsClosed ((Qc (K1 hξ hm) : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    Submodule.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto (b := l) (f := fun i => (h i).toLp (Y i)) ?_ (Eventually.of_forall hc)
  rw [tendsto_iff_dist_tendsto_zero]
  have hd2 : ∀ i, dist ((h i).toLp (Y i)) (hZ2.toLp Z) = (eLpNorm (fun ω => Y i ω - Z ω) 2 P).toReal := by
    intro i
    have := eLpNorm_sub_eq_dist ((h i).toLp (Y i)) hZ2
    have h1 : eLpNorm ((((h i).toLp (Y i) : Lp ℝ 2 P) : Ω → ℝ) - Z) 2 P =
        eLpNorm (fun ω => Y i ω - Z ω) 2 P :=
      eLpNorm_congr_ae (by filter_upwards [(h i).coeFn_toLp] with ω hω; simp [hω])
    rw [h1] at this
    rw [this, ENNReal.toReal_ofReal dist_nonneg]
  simp_rw [hd2]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hN
  exact this.congr fun i => rfl |>.trans (by simp)

end ScalarClosure

private theorem fp81s21_InQ1_coeff_functional
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hmξ : ∀ i, Measurable (ξ i))
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hc : ∀ j, InQ1 hξ hmξ (fun ω => q ω j))
    (ℓ : r26t6_Coeff →L[ℝ] ℝ) :
    InQ1 hξ hmξ (fun ω => ℓ (q ω)) := by
  let Y : ℕ → Ω → ℝ := fun n ω => ℓ (fp81s21_projectField n (q ω))
  have hY : ∀ n, InQ1 hξ hmξ (Y n) := by
    intro n
    have heq : Y n = fun ω => ∑ j ∈ Finset.range n,
        ℓ (fp81s21_coeffBasis j) * q ω j := by
      funext ω
      simp [Y, fp81s21_projectField_apply_coordinate, mul_comm]
    rw [heq]
    exact fp81s21_InQ1_sum _ fun j _ => fp81s21_InQ1_const_mul _ (hc j)
  have hz : AEStronglyMeasurable (fun ω => ℓ (q ω)) P :=
    ℓ.continuous.comp_aestronglyMeasurable hq.aestronglyMeasurable
  have ht : Tendsto (fun n => eLpNorm (fun ω => fp81s21_projectField n (q ω) - q ω) 2 P)
      atTop (𝓝 0) := by
    have hq' : MemLp q (ENNReal.ofReal (2 : ℝ)) P := by simpa using hq
    simpa using dct_proj hq.aestronglyMeasurable (q := 2) (by norm_num) hq'
      fp81s21_projectField fp81s21_projectField_norm_le fp81s21_projectField_tendsto
  have hm : ∀ n, AEStronglyMeasurable (fun ω => Y n ω - ℓ (q ω)) P :=
    fun n => (hY n).1.aestronglyMeasurable.sub hz
  have hb : ∀ n, eLpNorm (fun ω => Y n ω - ℓ (q ω)) 2 P ≤
      ENNReal.ofReal ‖ℓ‖ * eLpNorm (fun ω => fp81s21_projectField n (q ω) - q ω) 2 P := by
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm n)
      (Filter.Eventually.of_forall fun ω => ?_) 2
    simpa [Y, ← map_sub] using ℓ.le_opNorm (fp81s21_projectField n (q ω) - q ω)
  have ht' : Tendsto (fun n => eLpNorm (fun ω => Y n ω - ℓ (q ω)) 2 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr (by simp))
  apply fp81s21_InQ1_of_tendsto (l := atTop) hY hz
  exact (tendsto_lintegral_iff_eLpNorm hm (by norm_num)).2 (by simpa using ht')


local instance fp81s21_GaussianCovChaos_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianCovChaos_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The finite-horizon representative supplies the time-integral domination
needed for scalar second-chaos closure. -/
private theorem fp81s21_firstChaos_TimeL2Rep_norm_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U) :
    (∀ᵐ ω ∂P, Integrable (fun t => ‖q (a + t) ω‖)
      (volume.restrict (Set.Icc (0 : ℝ) H))) ∧
    MemLp (fun ω => ∫ t, ‖q (a + t) ω‖
      ∂(volume.restrict (Set.Icc (0 : ℝ) H))) 2 P := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : Ω × ℝ → r26t6_Coeff := fun z => q (a + z.2) z.1
  have hg : Measurable g :=
    hq.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
  have hi : ∀ᵐ ω ∂P, Integrable (fun t => ‖g (ω, t)‖) dt := by
    filter_upwards [hrep.2.2.2] with ω hω
    exact memLp_one_iff_integrable.mp (hω.1.norm.mono_exponent (by norm_num))
  have hb : ∀ᵐ ω ∂P, (∫ t, ‖g (ω, t)‖ ∂dt) ≤ Real.sqrt H * ‖U ω‖ := by
    filter_upwards [hrep.2.2.2] with ω hω
    have hf : MemLp (fun t => ‖g (ω, t)‖) (ENNReal.ofReal (2 : ℝ)) dt := by
      simpa [g] using hω.1.norm
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) dt := memLp_const 1
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := dt)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun t => norm_nonneg (g (ω, t)))
      (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hf hc
    have he : (∫ t, ‖g (ω, t)‖ ^ 2 ∂dt) = ‖U ω‖ ^ 2 := by
      calc
        _ = ∫ t, inner ℝ ((U ω : ℝ → r26t6_Coeff) t) ((U ω : ℝ → r26t6_Coeff) t) ∂dt := by
          apply integral_congr_ae
          filter_upwards [hω.2] with t ht
          rw [real_inner_self_eq_norm_sq, ht]
        _ = inner ℝ (U ω) (U ω) := (L2.inner_def _ _).symm
        _ = ‖U ω‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hh' : (∫ t, ‖g (ω, t)‖ ∂dt) ≤
        Real.sqrt (∫ t, ‖g (ω, t)‖ ^ 2 ∂dt) * Real.sqrt H := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two, dt, Measure.real,
        Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal hH] using hh
    rw [he, Real.sqrt_sq (norm_nonneg _)] at hh'
    simpa [mul_comm] using hh'
  refine ⟨hi, ?_⟩
  have hm : AEStronglyMeasurable (fun ω => ∫ t, ‖g (ω, t)‖ ∂dt) P :=
    hg.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  apply (hrep.2.1.norm.const_mul (Real.sqrt H)).mono' hm
  filter_upwards [hb] with ω hω
  rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
  exact hω


private theorem fp81s21_InQ1_coeff_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hmξ : ∀ i, Measurable (ξ i))
    (ν : Measure ℝ) [SFinite ν] (q : ℝ → Ω → r26t6_Coeff)
    (hqmeas : Measurable (fun p : Ω × ℝ => q p.2 p.1))
    (hfield : ∀ᵐ t ∂ν, ∀ L : r26t6_Coeff →L[ℝ] ℝ, InQ1 hξ hmξ (fun ω => L (q t ω)))
    (hqint : ∀ᵐ ω ∂P, Integrable (fun t => ‖q t ω‖) ν)
    (hqL2 : MemLp (fun ω => ∫ t, ‖q t ω‖ ∂ν) 2 P)
    (ℓ : ℝ → r26t6_Coeff →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hℓ : ∀ t, ‖ℓ t‖ ≤ C)
    (hℓmeas : Measurable (fun p : ℝ × r26t6_Coeff => ℓ p.1 p.2))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hZeq : Z =ᵐ[P] fun ω => ∫ t, ℓ t (q t ω) ∂ν) : InQ1 hξ hmξ Z := by
  let g : Ω → ℝ → ℝ := fun ω t => ℓ t (q t ω)
  let B : Ω → ℝ → ℝ := fun ω t => C * ‖q t ω‖
  have hgm : Measurable (Function.uncurry g) :=
    hℓmeas.comp (measurable_snd.prodMk hqmeas)
  refine fp81s21_InQ1_of_prod_limit (ν := ν) (f := fun _ => g) (g := g) (B := B)
    hZ (fun _ => hgm) hgm (measurable_const.mul hqmeas.norm) ?_ ?_ ?_ ?_ ?_ ?_ hZeq
  · intro ω t
    exact mul_nonneg hC (norm_nonneg _)
  · intro n
    filter_upwards [hfield] with t ht
    exact ht (ℓ t)
  · intro ω t
    exact tendsto_const_nhds
  · intro n ω t
    change |ℓ t (q t ω)| ≤ C * ‖q t ω‖
    rw [← Real.norm_eq_abs]
    exact ((ℓ t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hℓ t) (norm_nonneg _))
  · filter_upwards [hqint] with ω hω
    exact hω.const_mul C
  · have he : (fun ω => ∫ t, B ω t ∂ν) = fun ω => C * ∫ t, ‖q t ω‖ ∂ν := by
      funext ω
      exact integral_const_mul _ _
    rw [he]
    exact hqL2.const_mul C


private theorem fp81s21_TimeL2Rep_InQ1_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hmξ : ∀ i, Measurable (ξ i))
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hfield : ∀ u, 0 ≤ u → ∀ L : r26t6_Coeff →L[ℝ] ℝ, InQ1 hξ hmξ (fun ω => L (q u ω)))
    (ℓ : ℝ → r26t6_Coeff →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hℓ : ∀ t, ‖ℓ t‖ ≤ C)
    (hℓmeas : Measurable (fun p : ℝ × r26t6_Coeff => ℓ p.1 p.2))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hZeq : Z =ᵐ[P] fun ω => ∫ t, ℓ t (q (a + t) ω)
      ∂(volume.restrict (Set.Icc (0 : ℝ) H))) : InQ1 hξ hmξ Z := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  have hg : Measurable (fun p : Ω × ℝ => q (a + p.2) p.1) :=
    hq.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
  have hc : ∀ᵐ t ∂dt, ∀ L : r26t6_Coeff →L[ℝ] ℝ, InQ1 hξ hmξ (fun ω => L (q (a + t) ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hfield (a + t) (add_nonneg ha ht.1)
  obtain ⟨hi, hL2⟩ := fp81s21_firstChaos_TimeL2Rep_norm_integral P q M a H hH U hq hrep
  exact fp81s21_InQ1_coeff_time_integral hξ hmξ dt (fun t ω => q (a + t) ω)
    hg hc hi hL2 ℓ C hC hℓ hℓmeas hZ hZeq


private theorem fp81s21_TimeL2Rep_InQ1_bounded_test
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hmξ : ∀ i, Measurable (ξ i))
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hfield : ∀ u, 0 ≤ u → ∀ L : r26t6_Coeff →L[ℝ] ℝ, InQ1 hξ hmξ (fun ω => L (q u ω)))
    (v : ℝ → r26t6_Coeff) (hv : Measurable v)
    (hv2 : MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (C : ℝ) (hC : 0 ≤ C) (hvbound : ∀ t, ‖v t‖ ≤ C) :
    InQ1 hξ hmξ (fun ω => inner ℝ (hv2.toLp v) (U ω)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  let ℓ : ℝ → r26t6_Coeff →L[ℝ] ℝ := fun t => innerSL ℝ (v t)
  have hnorm : ∀ t, ‖ℓ t‖ ≤ C := fun t => (innerSL_apply_norm ℝ (v t)).le.trans (hvbound t)
  have hmeas : Measurable (fun p : ℝ × r26t6_Coeff => ℓ p.1 p.2) := by
    exact (hv.comp measurable_fst).inner measurable_snd
  have hZ : MemLp (fun ω => inner ℝ (hv2.toLp v) (U ω)) 2 P :=
    hrep.2.1.continuousLinearMap_comp (innerSL ℝ (hv2.toLp v))
  apply fp81s21_TimeL2Rep_InQ1_integral hξ hmξ q M a H ha hH U hq hrep hfield
    ℓ C hC hnorm hmeas hZ
  filter_upwards [hrep.2.2.2] with ω hω
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hv2, hω.2] with t ht hu
  simp [ℓ, ht, hu]


private theorem fp81s21_TimeL2Rep_InQ1_inner
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hmξ : ∀ i, Measurable (ξ i))
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hfield : ∀ u, 0 ≤ u → ∀ L : r26t6_Coeff →L[ℝ] ℝ, InQ1 hξ hmξ (fun ω => L (q u ω)))
    (v : Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) :
    InQ1 hξ hmξ (fun ω => inner ℝ v (U ω)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  have hdense := BoundedContinuousFunction.toLp_denseRange r26t6_Coeff dt ℝ (p := 2) (by norm_num)
  obtain ⟨vn, hvn, hlim⟩ := mem_closure_iff_seq_limit.1 (hdense v)
  choose f hf using hvn
  have hfn : ∀ n, MemLp (f n : ℝ → r26t6_Coeff) 2 dt := fun n =>
    (f n).memLp_top.mono_exponent (by simp)
  have hfeq : ∀ n, (hfn n).toLp (f n) = vn n := by
    intro n
    rw [← hf n]
    apply Lp.ext
    exact ((hfn n).coeFn_toLp).trans (BoundedContinuousFunction.coeFn_toLp 2 dt ℝ (f n)).symm
  have hQn : ∀ n, InQ1 hξ hmξ (fun ω => inner ℝ (vn n) (U ω)) := by
    intro n
    rw [← hfeq n]
    apply fp81s21_TimeL2Rep_InQ1_bounded_test hξ hmξ q M a H ha hH U hq hrep hfield
      (f n) (f n).continuous.measurable (hfn n) ‖f n‖ (norm_nonneg _)
    exact (f n).norm_coe_le_norm
  let Yn : ℕ → Ω → ℝ := fun n ω => inner ℝ (vn n) (U ω)
  let Y : Ω → ℝ := fun ω => inner ℝ v (U ω)
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n =>
    hrep.2.1.continuousLinearMap_comp (innerSL ℝ (vn n))
  have hY : MemLp Y 2 P := hrep.2.1.continuousLinearMap_comp (innerSL ℝ v)
  have hsquare : Tendsto (fun n => ∫ ω, (Yn n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [Yn, Y, real_inner_comm] using
      inner_pairing_square_tendsto P U hrep.2.1 v vn hlim
  apply fp81s21_InQ1_of_tendsto (l := atTop) hQn hY.aestronglyMeasurable
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp hsquare
  simp only [Function.comp_def, ENNReal.ofReal_zero] at ht
  refine ht.congr fun n => ?_
  have hi : Integrable (fun ω => (Yn n ω - Y ω) ^ 2) P := ((hYn n).sub hY).integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  apply lintegral_congr
  intro ω
  rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    Real.norm_eq_abs, sq_abs]


private theorem fp81s21_firstChaos_of_hilbert_projections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {W : Ω → B} (hW : AEStronglyMeasurable W P) {q r : ℝ} (hq : 2 ≤ q) (hqr : q < r)
    (hWq : MemLp W (ENNReal.ofReal q) P)
    (Pn : ℕ → B →L[ℝ] B) (hPn : ∀ n x, ‖Pn n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x))
    {ι : Type*} (S : ℕ → Finset ι) (ℓ : ι → B →L[ℝ] ℝ) (b : ℕ → ι → B)
    (hfin : ∀ n x, Pn n x = ∑ s ∈ S n, ℓ s x • b n s)
    (hscal : ∀ n, ∀ s ∈ S n, InQ1 hξ hm (fun ω => ℓ s (W ω))) :
    InFirstChaos P ξ q W := by
  classical
  have hq1 : 1 ≤ q := by linarith
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq1
  have hex : ∀ n, ∀ s ∈ S n, ∃ c : ℕ → ℕ → ℝ, Tendsto (fun m => ∫⁻ ω,
      ‖(∑ i ∈ Finset.range m, ξ i ω • c m i) - ℓ s (W ω)‖ₑ ^ q ∂P) atTop (𝓝 0) := fun n s hs =>
    firstApprox_of_InQ1 hξ hm (hscal n s hs) hq hqr (by
      rw [ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ r by linarith)]
      exact InQ1.memLp hξ hm (hscal n s hs) ⟨r, by linarith⟩)
  choose! c hc using hex
  -- scalar polynomials
  set poly : ℕ → ι → ℕ → Ω → ℝ := fun n s m ω => ∑ i ∈ Finset.range m, ξ i ω • c n s m i with hpoly
  have hpm : ∀ n s m, Measurable (poly n s m) := by
    intro n s m
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (hm i).smul_const _
  have hum : ∀ n s m, AEStronglyMeasurable (fun ω => poly n s m ω - ℓ s (W ω)) P := fun n s m =>
    (hpm n s m).aestronglyMeasurable.sub ((ℓ s).continuous.comp_aestronglyMeasurable hW)
  have hu0 : ∀ n, ∀ s ∈ S n, Tendsto (fun m => eLpNorm (fun ω => poly n s m ω - ℓ s (W ω))
      (ENNReal.ofReal q) P) atTop (𝓝 0) := fun n s hs =>
    (tendsto_lintegral_iff_eLpNorm (hum n s) (by linarith)).1 (hc n s hs)
  set g : ℕ → ℕ → Ω → B := fun n m ω => ∑ s ∈ S n, poly n s m ω • b n s with hg
  set F : ℕ → Ω → B := fun n ω => Pn n (W ω) with hF
  have h1 : ∀ n, Tendsto (fun m => eLpNorm (g n m - F n) (ENNReal.ofReal q) P) atTop (𝓝 0) := by
    intro n
    have heq : ∀ m, g n m - F n = fun ω => ∑ s ∈ S n, (poly n s m ω - ℓ s (W ω)) • b n s := by
      intro m; funext ω
      simp only [hg, hF, Pi.sub_apply, hfin n (W ω), sub_smul, Finset.sum_sub_distrib]
    simp_rw [heq]
    have hb : ∀ m, eLpNorm (fun ω => ∑ s ∈ S n, (poly n s m ω - ℓ s (W ω)) • b n s) (ENNReal.ofReal q) P ≤
        ∑ s ∈ S n, ‖b n s‖ₑ * eLpNorm (fun ω => poly n s m ω - ℓ s (W ω)) (ENNReal.ofReal q) P := fun m =>
      eLpNorm_finsum_smul_le (S n) (b n) (fun s ω => poly n s m ω - ℓ s (W ω)) (fun s _ => hum n s m) hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hb
    have : Tendsto (fun m => ∑ s ∈ S n, ‖b n s‖ₑ * eLpNorm (fun ω => poly n s m ω - ℓ s (W ω))
        (ENNReal.ofReal q) P) atTop (𝓝 (∑ s ∈ S n, ‖b n s‖ₑ * 0)) := by
      refine tendsto_finsetSum _ fun s hs => ?_
      exact ENNReal.Tendsto.const_mul (hu0 n s hs) (Or.inr (by simp))
    simpa using this
  have h2 : Tendsto (fun n => eLpNorm (F n - W) (ENNReal.ofReal q) P) atTop (𝓝 0) :=
    dct_proj hW hq1 hWq Pn hPn hlim
  obtain ⟨mm, hmm⟩ := exists_diag hp g F W h1 h2
  apply fp81s21_firstChaos_closed P ξ hξ hm q hq (fun j => g j (mm j)) W hW hmm
  intro j
  have heq : g j (mm j) = fun ω => ∑ i ∈ Finset.range (mm j),
      ξ i ω • (∑ s ∈ S j, c j s (mm j) i • b j s) := by
    funext ω
    simp only [hg, hpoly, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp
  rw [heq]
  refine ⟨?_, fun _ => mm j, fun _ i => ∑ s ∈ S j, c j s (mm j) i • b j s, ?_⟩
  · exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (hm i).aestronglyMeasurable.smul_const _
  · have hq0 : 0 < q := by linarith
    simpa [ENNReal.zero_rpow_of_pos hq0] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))


/-- Scalar first-chaos coordinates lift to a separable Hilbert-valued field. -/
private theorem fp81s21_firstChaos_of_hilbert_coordinates
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    {ι : Type} [Countable ι] (b : HilbertBasis ι ℝ B)
    (W : Ω → B) (hW : MemLp W 2 P)
    (hc : ∀ s, InQ1 hξ hm (fun ω => inner ℝ (b s) (W ω))) :
    InFirstChaos P ξ 2 W := by
  classical
  obtain ⟨S, hS⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  let proj : ℕ → B →L[ℝ] B := fun n => ∑ s ∈ S n, (innerSL ℝ (b s)).smulRight (b s)
  have hproj : ∀ n x, proj n x = ∑ s ∈ S n, inner ℝ (b s) x • b s := by
    intro n x
    simp [proj, ContinuousLinearMap.sum_apply]
  have hnorm : ∀ n x, ‖proj n x‖ ≤ ‖x‖ := by
    intro n x
    have hy : ‖proj n x‖ ^ 2 = ∑ s ∈ S n, (inner ℝ (b s) x) ^ 2 := by
      rw [hproj, ← real_inner_self_eq_norm_sq]
      have h := b.orthonormal.inner_sum (fun s => inner ℝ (b s) x)
        (fun s => inner ℝ (b s) x) (S n)
      simp only [innerSL_apply_apply, conj_trivial, sq] at h ⊢
      exact h
    have hz := b.orthonormal.sum_inner_products_le x (s := S n)
    simp only [Real.norm_eq_abs, sq_abs] at hz
    by_contra h
    push_neg at h
    nlinarith [norm_nonneg x, norm_nonneg (proj n x)]
  have hpoint : ∀ x, Tendsto (fun n => proj n x) atTop (𝓝 x) := by
    intro x
    have hs := b.hasSum_repr x
    refine (hs.comp hS).congr fun n => ?_
    rw [hproj]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [HilbertBasis.repr_apply_apply]
  apply fp81s21_firstChaos_of_hilbert_projections hξ hm hW.aestronglyMeasurable
    (q := 2) (r := 3) (by norm_num) (by norm_num) (by simpa using hW)
    proj hnorm hpoint S (fun s => innerSL ℝ (b s)) (fun _ s => b s)
  · exact hproj
  · intro n s hs
    exact hc s

/-- A time-L² history is in first chaos when its coefficient-valued
slices have all scalar functionals in the same first-chaos subspace. -/
theorem fp81s21_TimeL2Rep_firstChaos_of_functionals
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q)) (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hfield : ∀ u, 0 ≤ u → ∀ L : r26t6_Coeff →L[ℝ] ℝ,
      InQ1 hξ hm (fun ω => L (q u ω))) : InFirstChaos P ξ 2 U := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff := UniformSpace.secondCountable_of_separable _
  obtain ⟨ι, hι, b, -⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type
    (H := Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
  letI : Countable ι := hι
  exact fp81s21_firstChaos_of_hilbert_coordinates hξ hm b U hrep.2.1
    (fun s => fp81s21_TimeL2Rep_InQ1_inner hξ hm q M a H ha hH U hq hrep hfield (b s))

section ScalarFirstChaos

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

private theorem fp81s21_firstChaos_coeFn_poly (hξ : HRS.IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) (N : ℕ) (c : ℕ → ℝ) :
    ((∑ i : Fin N, c i • g1 hξ hm i : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω => ∑ i : Fin N, c i * ξ i ω := by
  have key : ∀ s : Finset (Fin N), ((∑ i ∈ s, c i • g1 hξ hm i : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ i ∈ s, c i * ξ i ω := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω h
      simpa using h
    | insert j s hj ih =>
      filter_upwards [Lp.coeFn_add (c j • g1 hξ hm j) (∑ i ∈ s, c i • g1 hξ hm i),
        Lp.coeFn_smul (c j) (g1 hξ hm j), coe_g1 hξ hm j, ih] with ω h1 h2 h3 h4
      rw [Finset.sum_insert hj, h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert hj,
        smul_eq_mul]
  exact key Finset.univ

private theorem fp81s21_InQ1_of_firstChaos (hξ : HRS.IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {W : Ω → ℝ}
    (h : HRS.InFirstChaos P ξ 2 W) : InQ1 hξ hm W := by
  obtain ⟨hW, n, c, hlim⟩ := h
  have hpm : ∀ m, MemLp (fun ω => ∑ i ∈ Finset.range (n m), ξ i ω • c m i) 2 P := fun m =>
    memLp_finsetSum _ fun i _ => (memLp_xi hξ hm i).mul_const (c m i)
  have hsub : ∀ m, AEStronglyMeasurable (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) P :=
    fun m => (hpm m).aestronglyMeasurable.sub hW
  have h2 := (tendsto_lintegral_iff_eLpNorm hsub (by norm_num : (0 : ℝ) < 2)).1 hlim
  simp only [ENNReal.ofReal_ofNat] at h2
  have hfin : ∀ᶠ m in atTop, eLpNorm (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) 2 P < ∞ :=
    h2.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  obtain ⟨m0, hm0⟩ := hfin.exists
  have hW2 : MemLp W 2 P := by
    have h1 : MemLp (fun ω => (∑ i ∈ Finset.range (n m0), ξ i ω • c m0 i) - W ω) 2 P := hm0
    have := (hpm m0).sub h1
    refine this.ae_eq (Eventually.of_forall fun ω => ?_)
    simp
  refine ⟨hW2, ?_⟩
  rw [mem_Qc_iff (K1_mono hξ hm)]
  intro ε hε
  have hev : ∀ᶠ m in atTop, eLpNorm (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) 2 P <
      ENNReal.ofReal ε := h2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨m, hm'⟩ := hev.exists
  refine ⟨n m, ∑ i : Fin (n m), c m i • g1 hξ hm i, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have hco := fp81s21_firstChaos_coeFn_poly hξ hm (n m) (c m)
    have e1 : eLpNorm (((∑ i : Fin (n m), c m i • g1 hξ hm i : Lp ℝ 2 P) : Ω → ℝ) - W) 2 P =
        eLpNorm (fun ω => (∑ i ∈ Finset.range (n m), ξ i ω • c m i) - W ω) 2 P := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hco] with ω h
      simp only [Pi.sub_apply, h, Finset.sum_range, smul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have e2 := eLpNorm_sub_eq_dist (∑ i : Fin (n m), c m i • g1 hξ hm i : Lp ℝ 2 P) hW2
    rw [e1] at e2
    rw [e2] at hm'
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hm'

end ScalarFirstChaos

/-- The origin-zero Gaussian history and a correction represented by a
continuous linear observation belong to the first chaos of the same sequence. -/
theorem fp81s21_gaussian_J_firstChaos
    {d r : ℕ} {Pw : ℝ} {B Ω : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : r26t6_WeightedChart d r Pw)
    (QG : ℝ → Ω → (HRS.Euc d → ℝ) → ℝ)
    (qG : ℝ → Ω → r26t6_Coeff) (MG H : ℝ) (hH : 0 ≤ H)
    (UG : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (hm : ∀ i, Measurable (ξ i))
    (hqG : fp81s21_MomentRep E P QG qG MG)
    (hcoord : ∀ u, 0 ≤ u → ∀ j, InFirstChaos P ξ 2 (fun ω => qG u ω j))
    (hUG : fp81s21_TimeL2Rep P qG MG 0 H UG)
    (Λ : Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)) →L[ℝ] B)
    (Jcum : ℝ → Ω → B) (hJ : Jcum H = fun ω => Λ (UG ω)) :
    InFirstChaos P ξ 2 UG ∧ InFirstChaos P ξ 2 (Jcum H) := by
  have hc : InFirstChaos P ξ 2 UG := by
    apply fp81s21_TimeL2Rep_firstChaos_of_functionals hξ hm qG MG 0 H
      (by norm_num) hH UG hqG.1 hUG
    intro u hu L
    apply fp81s21_InQ1_coeff_functional hξ hm (qG u) (hqG.2 u hu).1
    intro j
    exact fp81s21_InQ1_of_firstChaos hξ hm (hcoord u hu j)
  refine ⟨hc, ?_⟩
  rw [hJ]
  exact fp81s21_firstChaos_clm hc Λ

#print axioms fp81s21_firstChaos_coeFn_poly
#print axioms fp81s21_InQ1_of_firstChaos
#print axioms fp81s21_gaussian_J_firstChaos
#print axioms fp81s21_TimeL2Rep_firstChaos_of_functionals
#print axioms fp81s21_firstChaos_of_hilbert_coordinates
#print axioms fp81s21_firstChaos_of_hilbert_projections
#print axioms fp81s21_InQ1_coeff_time_integral
#print axioms fp81s21_TimeL2Rep_InQ1_integral
#print axioms fp81s21_TimeL2Rep_InQ1_bounded_test
#print axioms fp81s21_TimeL2Rep_InQ1_inner
#print axioms fp81s21_firstChaos_TimeL2Rep_norm_integral
#print axioms fp81s21_InQ1_coeff_functional
#print axioms fp81s21_firstChaos_clm
#print axioms fp81s21_InQ1_of_prod_limit
#print axioms fp81s21_InQ1_add
#print axioms fp81s21_InQ1_const_mul
#print axioms fp81s21_InQ1_zero
#print axioms fp81s21_InQ1_sum
#print axioms fp81s21_InQ1_congr_ae
#print axioms fp81s21_InQ1_of_tendsto

end HRS.Fp81.S21
end

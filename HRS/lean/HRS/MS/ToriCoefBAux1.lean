import HRS.MS.ToriCoefA
import HRS.MS.Ker1

/-!
# MS-TORI-COEFB, helper file 1: differentiation under the integral sign for the cancellation convolution

For a scalar kernel `k` on `ℝ^d` and `g : ℝ^d → W` (`W` a real Banach space) put
`T g (x) = ∫_{z ∈ Q_L} k(z) • (g(x - z) - 1_{|z| ≤ 1/4} g(x)) dz`, `Q_L = [-L/2, L/2)^d`.  Under the kernel
hypotheses `tcb_Kern` (measurable, `|k||z|` integrable on the near ball, `|k|` bounded on the far part of the
cube), for `g ∈ C²` with bounded `g, Dg, D²g` one has `D (T g) = T (D g)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- The centred cube `Q_L = [-L/2, L/2)^d`. -/
def tcb_Q (d : ℕ) (L : ℝ) : Set (Euc d) := {z | ∀ i, -(L / 2) ≤ z i ∧ z i < L / 2}

/-- The near ball `{|z| ≤ 1/4}`. -/
def tcb_N (d : ℕ) : Set (Euc d) := Metric.closedBall 0 (1 / 4)

theorem tcb_compact_Icc (a b : ℝ) : IsCompact {x : Euc d | ∀ i, x i ∈ Icc a b} := by
  have h : IsCompact ((fun f : Fin d → ℝ => (WithLp.toLp 2 f : Euc d)) ''
      (Set.pi univ fun _ : Fin d => Icc a b)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro hx; exact ⟨x.ofLp, fun i _ => hx i, rfl⟩
  · rintro ⟨f, hf, rfl⟩ i; exact hf i (mem_univ i)

theorem tcb_measurableSet_Q (L : ℝ) : MeasurableSet (tcb_Q d L) := by
  have : tcb_Q d L = ⋂ i : Fin d, ({z : Euc d | -(L / 2) ≤ z i} ∩ {z : Euc d | z i < L / 2}) := by
    ext z; simp [tcb_Q]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hc : Continuous fun z : Euc d => z i := by fun_prop
  exact (measurableSet_le measurable_const hc.measurable).inter
    (measurableSet_lt hc.measurable measurable_const)

theorem tcb_Q_subset (L : ℝ) : tcb_Q d L ⊆ {x : Euc d | ∀ i, x i ∈ Icc (-(L / 2)) (L / 2)} :=
  fun z hz i => ⟨(hz i).1, (hz i).2.le⟩

theorem tcb_measure_Q_lt_top (L : ℝ) : volume (tcb_Q d L) < ⊤ :=
  ((tcb_compact_Icc (d := d) (-(L / 2)) (L / 2)).measure_lt_top).trans_le' (measure_mono (tcb_Q_subset L))

theorem tcb_measurableSet_N : MeasurableSet (tcb_N d) := Metric.isClosed_closedBall.measurableSet

theorem tcb_N_subset_Q {L : ℝ} (hL : 1 ≤ L) : tcb_N d ⊆ tcb_Q d L := by
  intro z hz i
  have h1 : ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hz
  have h2 : |z i| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z i
    rwa [Real.norm_eq_abs] at this
  have := abs_le.1 (h2.trans h1)
  constructor <;> linarith [this.1, this.2]

/-- The operator `T_k` (cancellation convolution on the cube). -/
def tcb_F {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (k : Euc d → ℝ) (g : Euc d → W)
    (x z : Euc d) : W :=
  k z • (g (x - z) - (tcb_N d).indicator (fun _ => g x) z)

def tcb_T {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : ℝ) (k : Euc d → ℝ)
    (g : Euc d → W) (x : Euc d) : W :=
  ∫ z in tcb_Q d L, tcb_F k g x z

/-- Kernel hypotheses. -/
structure tcb_Kern (L : ℝ) (k : Euc d → ℝ) (Kf : ℝ) : Prop where
  hL : 1 ≤ L
  hKf : 0 ≤ Kf
  meas : Measurable k
  intN : IntegrableOn (fun z => |k z| * ‖z‖) (tcb_N d) volume
  far : ∀ z ∈ tcb_Q d L, ¬ ‖z‖ ≤ 1 / 4 → |k z| ≤ Kf

/-- The near constant `a = ∫_N |k||z|`. -/
def tcb_a (k : Euc d → ℝ) : ℝ := ∫ z in tcb_N d, |k z| * ‖z‖

theorem tcb_a_nonneg (k : Euc d → ℝ) : 0 ≤ tcb_a k :=
  setIntegral_nonneg tcb_measurableSet_N fun z _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)

/-- Mean value bound. -/
theorem tcb_mvt {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (g : Euc d → W)
    (hg : Differentiable ℝ g) (B : ℝ) (hB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (x z : Euc d) :
    ‖g (x - z) - g x‖ ≤ B * ‖z‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (fun y _ => hg y) (fun y _ => hB y)
    convex_univ (mem_univ x) (mem_univ (x - z))
  simpa [sub_sub_cancel_left, norm_neg] using this

theorem tcb_F_aesm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {L : ℝ} {k : Euc d → ℝ}
    {Kf : ℝ} (hk : tcb_Kern L k Kf) (g : Euc d → W) (hg : Continuous g) (x : Euc d)
    (μ : Measure (Euc d)) :
    AEStronglyMeasurable (tcb_F k g x) μ := by
  unfold tcb_F
  refine AEStronglyMeasurable.smul hk.meas.aestronglyMeasurable ?_
  refine AEStronglyMeasurable.sub ?_ ?_
  · exact (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact (aestronglyMeasurable_const).indicator tcb_measurableSet_N

/-- Pointwise bound of the integrand on the cube. -/
theorem tcb_F_bound {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {L : ℝ} {k : Euc d → ℝ}
    {Kf : ℝ} (hk : tcb_Kern L k Kf) (g : Euc d → W) (hg : Differentiable ℝ g) (B1 : ℝ)
    (hB1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1) (x z : Euc d) (hz : z ∈ tcb_Q d L) :
    ‖tcb_F k g x z‖ ≤ (tcb_N d).indicator (fun z => |k z| * ‖z‖ * B1) z + Kf * ‖g (x - z)‖ := by
  have hK0 : 0 ≤ Kf * ‖g (x - z)‖ := mul_nonneg hk.hKf (norm_nonneg _)
  by_cases hzN : z ∈ tcb_N d
  · rw [Set.indicator_of_mem hzN]
    have h1 : ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hzN
    unfold tcb_F
    rw [Set.indicator_of_mem hzN, norm_smul, Real.norm_eq_abs]
    have := tcb_mvt g hg B1 hB1 x z
    have h2 : |k z| * ‖g (x - z) - g x‖ ≤ |k z| * (B1 * ‖z‖) :=
      mul_le_mul_of_nonneg_left this (abs_nonneg _)
    nlinarith
  · rw [Set.indicator_of_notMem hzN, zero_add]
    have h1 : ¬ ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hzN
    unfold tcb_F
    rw [Set.indicator_of_notMem hzN, sub_zero, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hk.far z hz h1) (norm_nonneg _)

theorem tcb_dom_integrable {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (B C : ℝ) :
    Integrable (fun z => (tcb_N d).indicator (fun z => |k z| * ‖z‖ * B) z + Kf * C)
      (volume.restrict (tcb_Q d L)) := by
  refine Integrable.add ?_ ?_
  · rw [integrable_indicator_iff tcb_measurableSet_N]
    exact (hk.intN.mul_const B).mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self _)
  · have : IsFiniteMeasure (volume.restrict (tcb_Q d L)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact tcb_measure_Q_lt_top L⟩
    exact integrable_const _

theorem tcb_F_integrable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {L : ℝ}
    {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (g : Euc d → W) (hg : Differentiable ℝ g)
    (B0 B1 : ℝ) (hB0 : ∀ y, ‖g y‖ ≤ B0) (hB1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1) (x : Euc d) :
    Integrable (tcb_F k g x) (volume.restrict (tcb_Q d L)) := by
  refine Integrable.mono' (tcb_dom_integrable hk B1 B0)
    (tcb_F_aesm hk g hg.continuous x _) ?_
  filter_upwards [ae_restrict_mem (tcb_measurableSet_Q L)] with z hz
  refine (tcb_F_bound hk g hg B1 hB1 x z hz).trans ?_
  have := mul_le_mul_of_nonneg_left (hB0 (x - z)) hk.hKf
  linarith

/-- Differentiation under the integral sign: `D (T g) = T (D g)`. -/
theorem tcb_hasFDerivAt {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (g : Euc d → W)
    (hg : ContDiff ℝ 2 g) (B0 B1 B2 : ℝ) (h0 : ∀ y, ‖g y‖ ≤ B0) (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1)
    (h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ B2) (x : Euc d) :
    HasFDerivAt (tcb_T L k g) (tcb_T L k (fderiv ℝ g) x) x := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg' : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hd' : Differentiable ℝ (fderiv ℝ g) := hg'.differentiable (by norm_num)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (μ := volume.restrict (tcb_Q d L)) (F := fun x z => tcb_F k g x z)
    (F' := fun x z => tcb_F k (fderiv ℝ g) x z) (x₀ := x) (s := univ)
    (bound := fun z => (tcb_N d).indicator (fun z => |k z| * ‖z‖ * B2) z + Kf * B1)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun y => tcb_F_aesm hk g hd.continuous y _)
    (tcb_F_integrable hk g hd B0 B1 h0 h1 x)
    (tcb_F_aesm hk (fderiv ℝ g) hg'.continuous x _) ?_ (tcb_dom_integrable hk B2 B1) ?_
  · exact key
  · filter_upwards [ae_restrict_mem (tcb_measurableSet_Q L)] with z hz y _
    exact tcb_F_bound hk (fderiv ℝ g) hd' B2 h2 y z hz |>.trans (by
      have := mul_le_mul_of_nonneg_left (h1 (y - z)) hk.hKf
      linarith)
  · refine Filter.Eventually.of_forall fun z y _ => ?_
    have e1 : HasFDerivAt (fun y : Euc d => g (y - z)) (fderiv ℝ g (y - z)) y :=
      (hd (y - z)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const z) |>.congr_fderiv (by simp)
    by_cases hzN : z ∈ tcb_N d
    · have e2 : HasFDerivAt (fun y : Euc d => (tcb_N d).indicator (fun _ => g y) z)
          ((tcb_N d).indicator (fun _ => fderiv ℝ g y) z) y := by
        simp only [Set.indicator_of_mem hzN]
        exact (hd y).hasFDerivAt
      exact (e1.sub e2).const_smul (k z)
    · have e2 : HasFDerivAt (fun y : Euc d => (tcb_N d).indicator (fun _ => g y) z)
          ((tcb_N d).indicator (fun _ => fderiv ℝ g y) z) y := by
        simp only [Set.indicator_of_notMem hzN]
        exact hasFDerivAt_const _ _
      exact (e1.sub e2).const_smul (k z)

end HRS.MS.ToriCoefB

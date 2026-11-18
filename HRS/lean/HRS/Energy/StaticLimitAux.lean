import HRS.Torus.Sobolev
import HRS.Kernel.Riesz

/-!
# Auxiliary lemmas for the static field limits (work package STAT-4.21)

Spectral kernels `specKernel a x = ∑_k a_k cos(2π k·x)` with summable nonnegative `a`, their
feature maps, positive-definiteness, and the variational fixed-point argument behind the
existence of the thermal equilibrium density for bounded positive-definite kernels.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

open HRS Torus

variable {d : ℕ}

/-- The spectral kernel `x ↦ ∑_k a_k cos(2π k·x)`. -/
def specKernel (a : Lattice d → ℝ) (x : Torus d) : ℝ := ∑' k, a k * cosMode k x

/-- Feature index set: a cosine and a sine coordinate for every frequency. -/
abbrev Idx (d : ℕ) := Lattice d ⊕ Lattice d

/-- The feature map `Ψ_i(x)`. -/
def feat (a : Lattice d → ℝ) : Idx d → Torus d → ℝ
  | Sum.inl k, x => Real.sqrt (a k) * cosMode k x
  | Sum.inr k, x => Real.sqrt (a k) * sinMode k x

/-- The weights `b_i = √a_k`, bounding the features. -/
def fbound (a : Lattice d → ℝ) : Idx d → ℝ
  | Sum.inl k => Real.sqrt (a k)
  | Sum.inr k => Real.sqrt (a k)

theorem mode_add_arg' (k : Lattice d) (x y : Torus d) :
    mode k (x + y) = mode k x * mode k y := by
  simp only [mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem cosMode_sub' (k : Lattice d) (x y : Torus d) :
    cosMode k (x - y) = cosMode k x * cosMode k y + sinMode k x * sinMode k y := by
  have h : mode k (x - y) = mode k x * mode (-k) y := by
    have : mode k x = mode k (x - y) * mode k y := by
      rw [← mode_add_arg']; simp
    rw [mode_neg]
    have hn : mode k y * (starRingEnd ℂ) (mode k y) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mode]; simp
    calc mode k (x - y) = mode k (x - y) * (mode k y * (starRingEnd ℂ) (mode k y)) := by
          rw [hn, mul_one]
      _ = mode k x * (starRingEnd ℂ) (mode k y) := by rw [this]; ring
  simp only [cosMode, sinMode, h, mode_neg, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

section Features

variable {a : Lattice d → ℝ}

theorem abs_feat_le (i : Idx d) (x : Torus d) : |feat a i x| ≤ fbound a i := by
  rcases i with k | k
  · simp only [feat, fbound, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by simpa using norm_cosMode_le k x)
  · simp only [feat, fbound, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by simpa using norm_sinMode_le k x)

theorem fbound_nonneg (i : Idx d) : 0 ≤ fbound a i := by
  rcases i with k | k <;> exact Real.sqrt_nonneg _

theorem continuous_feat (i : Idx d) : Continuous (feat a i) := by
  rcases i with k | k
  · exact continuous_const.mul (continuous_cosMode k)
  · exact continuous_const.mul (continuous_sinMode k)

theorem fbound_mul_self (ha0 : ∀ k, 0 ≤ a k) (i : Idx d) :
    fbound a i * fbound a i = a (Sum.elim id id i) := by
  rcases i with k | k <;> simp [fbound, Real.mul_self_sqrt (ha0 k)]

theorem summable_fbound_sq (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) :
    Summable fun i : Idx d => fbound a i * fbound a i := by
  have h : (fun i : Idx d => fbound a i * fbound a i) = Sum.elim a a := by
    funext i; rw [fbound_mul_self ha0]; rcases i with k | k <;> rfl
  rw [h]
  exact Summable.sum (f := Sum.elim a a) has has

theorem norm_mul_cos_le (ha0 : ∀ k, 0 ≤ a k) (k : Lattice d) (x : Torus d) :
    ‖a k * cosMode k x‖ ≤ a k := by
  rw [norm_mul, Real.norm_of_nonneg (ha0 k)]
  exact mul_le_of_le_one_right (ha0 k) (norm_cosMode_le k x)

theorem abs_specKernel_le (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x : Torus d) :
    |specKernel a x| ≤ ∑' k, a k := by
  unfold specKernel
  have hs : Summable fun k => ‖a k * cosMode k x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_mul_cos_le ha0 k x) has
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hs).trans
    (Summable.tsum_le_tsum (fun k => norm_mul_cos_le ha0 k x) hs has)

theorem continuous_specKernel (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) :
    Continuous (specKernel a) :=
  continuous_tsum (u := a) (fun k => continuous_const.mul (continuous_cosMode k)) has
    fun k x => norm_mul_cos_le ha0 k x

theorem summable_feat_prod (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (f : Lattice d → Torus d → ℝ)
    (hf : ∀ k z, |f k z| ≤ 1) (x y : Torus d) :
    Summable fun k => a k * (f k x * f k y) := by
  refine Summable.of_norm_bounded has fun k => ?_
  have h1 : |f k x * f k y| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (f k x), abs_nonneg (f k y), hf k x, hf k y]
  rw [norm_mul, Real.norm_of_nonneg (ha0 k), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (ha0 k) h1

theorem sqrt_mul_sqrt_mul (k : Lattice d) (ha : 0 ≤ a k) (p q : ℝ) :
    Real.sqrt (a k) * p * (Real.sqrt (a k) * q) = a k * (p * q) := by
  have := Real.mul_self_sqrt ha
  calc Real.sqrt (a k) * p * (Real.sqrt (a k) * q)
      = (Real.sqrt (a k) * Real.sqrt (a k)) * (p * q) := by ring
    _ = a k * (p * q) := by rw [this]

theorem hasSum_feat_mul (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x y : Torus d) :
    HasSum (fun i : Idx d => feat a i x * feat a i y) (specKernel a (x - y)) := by
  have hc : Summable fun k => a k * (cosMode k x * cosMode k y) :=
    summable_feat_prod ha0 has cosMode (fun k z => by simpa using norm_cosMode_le k z) x y
  have hsn : Summable fun k => a k * (sinMode k x * sinMode k y) :=
    summable_feat_prod ha0 has sinMode (fun k z => by simpa using norm_sinMode_le k z) x y
  have e : specKernel a (x - y) = ∑' k, a k * (cosMode k x * cosMode k y) +
      ∑' k, a k * (sinMode k x * sinMode k y) := by
    rw [← hc.tsum_add hsn]
    unfold specKernel
    refine tsum_congr fun k => ?_
    rw [cosMode_sub']; ring
  have h3 : HasSum (Sum.elim (fun k => a k * (cosMode k x * cosMode k y))
      (fun k => a k * (sinMode k x * sinMode k y)))
      (∑' k, a k * (cosMode k x * cosMode k y) + ∑' k, a k * (sinMode k x * sinMode k y)) :=
    HasSum.sum (f := Sum.elim (fun k => a k * (cosMode k x * cosMode k y))
      (fun k => a k * (sinMode k x * sinMode k y))) hc.hasSum hsn.hasSum
  rw [e]
  have hf : (fun i : Idx d => feat a i x * feat a i y) =
      Sum.elim (fun k => a k * (cosMode k x * cosMode k y))
        (fun k => a k * (sinMode k x * sinMode k y)) := by
    funext i
    rcases i with k | k
    · exact sqrt_mul_sqrt_mul k (ha0 k) _ _
    · exact sqrt_mul_sqrt_mul k (ha0 k) _ _
  rw [hf]
  exact h3

theorem integrable_feat_mul (μ : Measure (Torus d)) {h : Torus d → ℝ} (hh : Integrable h μ)
    (i : Idx d) : Integrable (fun x => feat a i x * h x) μ :=
  hh.bdd_mul (c := fbound a i) (continuous_feat i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_feat_le i x)

theorem norm_integral_feat_le (μ : Measure (Torus d)) {h : Torus d → ℝ} (hh : Integrable h μ)
    (i : Idx d) : ∫ x, ‖feat a i x * h x‖ ∂μ ≤ fbound a i * ∫ x, ‖h x‖ ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_feat_mul μ hh i).norm (hh.norm.const_mul _) fun x => ?_
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_feat_le i x) (norm_nonneg _)

/-- Positive-definiteness of a spectral kernel against an integrable weight, in the form of an
explicit sum of squares. -/
theorem posdef_hasSum (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] {h : Torus d → ℝ} (hh : Integrable h μ) :
    HasSum (fun i : Idx d => (∫ x, feat a i x * h x ∂μ) ^ 2)
      (∫ x, h x * ∫ y, specKernel a (x - y) * h y ∂μ ∂μ) := by
  set H : ℝ := ∫ x, ‖h x‖ ∂μ with hH
  have hH0 : 0 ≤ H := integral_nonneg fun _ => norm_nonneg _
  have hb2 := summable_fbound_sq ha0 has (d := d)
  -- the inner integral
  have hinner : ∀ x, HasSum (fun i : Idx d => feat a i x * ∫ y, feat a i y * h y ∂μ)
      (∫ y, specKernel a (x - y) * h y ∂μ) := by
    intro x
    have hF : ∀ i : Idx d, Integrable (fun y => feat a i x * (feat a i y * h y)) μ :=
      fun i => (integrable_feat_mul μ hh i).const_mul _
    have hnorm : Summable fun i : Idx d => ∫ y, ‖feat a i x * (feat a i y * h y)‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
        (fun i => ?_) (hb2.mul_right H)
      calc ∫ y, ‖feat a i x * (feat a i y * h y)‖ ∂μ
          = |feat a i x| * ∫ y, ‖feat a i y * h y‖ ∂μ := by
            simp_rw [norm_mul, Real.norm_eq_abs]; rw [integral_const_mul]
        _ ≤ fbound a i * (fbound a i * H) :=
            mul_le_mul (abs_feat_le i x) (norm_integral_feat_le μ hh i) (integral_nonneg fun _ => norm_nonneg _) (fbound_nonneg i)
        _ = fbound a i * fbound a i * H := by ring
    have := hasSum_integral_of_summable_integral_norm hF hnorm
    have e1 : ∀ i : Idx d, ∫ y, feat a i x * (feat a i y * h y) ∂μ =
        feat a i x * ∫ y, feat a i y * h y ∂μ := fun i => integral_const_mul _ _
    have e2 : ∀ y, ∑' i : Idx d, feat a i x * (feat a i y * h y) = specKernel a (x - y) * h y := by
      intro y
      have := (hasSum_feat_mul ha0 has x y).mul_right (h y)
      rw [← this.tsum_eq]
      exact tsum_congr fun i => by ring
    simp_rw [e1, e2] at this
    exact this
  set c : Idx d → ℝ := fun i => ∫ x, feat a i x * h x ∂μ with hc
  have hc_le : ∀ i, |c i| ≤ fbound a i * H := fun i =>
    abs_integral_le_integral_abs.trans (norm_integral_feat_le μ hh i)
  have hF : ∀ i : Idx d, Integrable (fun x => c i * (feat a i x * h x)) μ :=
    fun i => (integrable_feat_mul μ hh i).const_mul _
  have hnorm : Summable fun i : Idx d => ∫ x, ‖c i * (feat a i x * h x)‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) (hb2.mul_right (H * H))
    calc ∫ x, ‖c i * (feat a i x * h x)‖ ∂μ
        = |c i| * ∫ x, ‖feat a i x * h x‖ ∂μ := by
          simp_rw [norm_mul, Real.norm_eq_abs]; rw [integral_const_mul]
      _ ≤ (fbound a i * H) * (fbound a i * H) :=
          mul_le_mul (hc_le i) (norm_integral_feat_le μ hh i)
            (integral_nonneg fun _ => norm_nonneg _) (mul_nonneg (fbound_nonneg i) hH0)
      _ = fbound a i * fbound a i * (H * H) := by ring
  have := hasSum_integral_of_summable_integral_norm hF hnorm
  have e1 : ∀ i : Idx d, ∫ x, c i * (feat a i x * h x) ∂μ = (c i) ^ 2 := by
    intro i; rw [integral_const_mul]; ring
  have e2 : ∀ x, ∑' i : Idx d, c i * (feat a i x * h x) =
      h x * ∫ y, specKernel a (x - y) * h y ∂μ := by
    intro x
    rw [← (hinner x).tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun i => by ring
  simp_rw [e1, e2] at this
  exact this

theorem posdef_nonneg (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] {h : Torus d → ℝ} (hh : Integrable h μ) :
    0 ≤ ∫ x, h x * ∫ y, specKernel a (x - y) * h y ∂μ ∂μ :=
  (posdef_hasSum ha0 has μ hh).nonneg fun _ => sq_nonneg _

/-- Termwise integration of a feature expansion against an integrable weight. -/
theorem hasSum_integral_tsum_mul (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] {e : Idx d → Torus d → ℝ}
    (he : ∀ i, Continuous (e i)) {B : ℝ} (hb : ∀ i x, |e i x| ≤ B * fbound a i)
    {c : Idx d → ℝ} {C : ℝ} (hc : ∀ i, |c i| ≤ C * fbound a i) {k : Torus d → ℝ}
    (hk : Integrable k μ) :
    HasSum (fun i => c i * ∫ x, e i x * k x ∂μ) (∫ x, (∑' i, c i * e i x) * k x ∂μ) := by
  set H : ℝ := ∫ x, ‖k x‖ ∂μ with hH
  have hint : ∀ i, Integrable (fun x => c i * (e i x * k x)) μ := fun i =>
    (hk.bdd_mul (c := B * fbound a i) (he i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb i x)).const_mul _
  have hnorm : Summable fun i : Idx d => ∫ x, ‖c i * (e i x * k x)‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) ((summable_fbound_sq ha0 has).mul_right (C * B * H))
    calc ∫ x, ‖c i * (e i x * k x)‖ ∂μ ≤ ∫ x, (C * fbound a i) * ((B * fbound a i) * ‖k x‖) ∂μ := by
          refine integral_mono (hint i).norm ?_ fun x => ?_
          · exact (hk.norm.const_mul _).const_mul _
          · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            exact mul_le_mul (hc i) (mul_le_mul_of_nonneg_right (hb i x) (norm_nonneg _))
              (mul_nonneg (abs_nonneg _) (norm_nonneg _)) ((abs_nonneg _).trans (hc i))
      _ = fbound a i * fbound a i * (C * B * H) := by
          rw [integral_const_mul, integral_const_mul]; ring
  have h := hasSum_integral_of_summable_integral_norm hint hnorm
  have e1 : ∀ i : Idx d, ∫ x, c i * (e i x * k x) ∂μ = c i * ∫ x, e i x * k x ∂μ :=
    fun i => integral_const_mul _ _
  have e2 : ∀ x, ∑' i : Idx d, c i * (e i x * k x) = (∑' i, c i * e i x) * k x := by
    intro x
    rw [← tsum_mul_right]
    exact tsum_congr fun i => by ring
  simp_rw [e1, e2] at h
  exact h

theorem hasSum_kernel_integral (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] {f : Torus d → ℝ} (hf : Integrable f μ)
    (x : Torus d) :
    HasSum (fun i : Idx d => feat a i x * ∫ y, feat a i y * f y ∂μ)
      (∫ y, specKernel a (x - y) * f y ∂μ) := by
  have := hasSum_integral_tsum_mul ha0 has μ (e := feat a) (fun i => continuous_feat i)
    (B := 1) (fun i y => by simpa using abs_feat_le i y) (c := fun i => feat a i x) (C := 1)
    (fun i => by simpa using abs_feat_le i x) hf
  have e : ∀ y, ∑' i : Idx d, feat a i x * feat a i y = specKernel a (x - y) := fun y =>
    (hasSum_feat_mul ha0 has x y).tsum_eq
  simp_rw [e] at this
  exact this

theorem continuous_kernel_integral (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] {f : Torus d → ℝ} (hf : Integrable f μ) :
    Continuous fun x => ∫ y, specKernel a (x - y) * f y ∂μ := by
  refine continuous_of_dominated (bound := fun y => (∑' k, a k) * |f y|) ?_ ?_ ?_ ?_
  · intro x
    exact ((continuous_specKernel ha0 has).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_specKernel_le ha0 has _) (abs_nonneg _)
  · exact hf.abs.const_mul _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((continuous_specKernel ha0 has).comp (continuous_id.sub continuous_const)).mul continuous_const

end Features

section ThermalUnique

variable {a : Lattice d → ℝ}

/-- `convolution with the spectral kernel is continuous` for an integrable density. -/
theorem continuous_conv (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {ρ : Torus d → ℝ}
    (hρ : Integrable ρ) : Continuous fun x => ∫ y, specKernel a (x - y) * ρ y := by
  refine continuous_of_dominated (bound := fun y => (∑' k, a k) * |ρ y|) ?_ ?_ ?_ ?_
  · intro x
    exact ((continuous_specKernel ha0 has).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hρ.aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_specKernel_le ha0 has _) (abs_nonneg _)
  · exact hρ.abs.const_mul _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((continuous_specKernel ha0 has).comp (continuous_id.sub continuous_const)).mul continuous_const

theorem abs_conv_le (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {ρ : Torus d → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) (x : Torus d) :
    |∫ y, specKernel a (x - y) * ρ y| ≤ ∑' k, a k := by
  have hρ : Integrable ρ := by
    by_contra h; rw [integral_undef h] at hρ1; norm_num at hρ1
  calc |∫ y, specKernel a (x - y) * ρ y| ≤ ∫ y, |specKernel a (x - y) * ρ y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, (∑' k, a k) * ρ y := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hρ.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
        show |specKernel a (x - y) * ρ y| ≤ (∑' k, a k) * ρ y
        rw [abs_mul, abs_of_nonneg (hρ0 y)]
        exact mul_le_mul_of_nonneg_right (abs_specKernel_le ha0 has _) (hρ0 y)
    _ = ∑' k, a k := by rw [integral_const_mul, hρ1, mul_one]

theorem integrable_kernel_mul (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x : Torus d)
    {ρ : Torus d → ℝ} (hρ : Integrable ρ) :
    Integrable (fun y => specKernel a (x - y) * ρ y) :=
  hρ.bdd_mul (f := fun y => specKernel a (x - y)) (c := ∑' k, a k)
    ((continuous_specKernel ha0 has).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_specKernel_le ha0 has _)

theorem integrable_of_integral_one {ρ : Torus d → ℝ} (h : ∫ x, ρ x = 1) : Integrable ρ := by
  by_contra hn; rw [integral_undef hn] at h; norm_num at h

theorem log_mono_aux {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : 0 ≤ (r - s) * (Real.log r - Real.log s) := by
  rcases le_total r s with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [Real.log_le_log hr h])
  · exact mul_nonneg (by linarith) (by linarith [Real.log_le_log hs h])

/-- The Gibbs fixed-point equation determines the density: strict convexity of the free energy
for a positive-definite bounded kernel. -/
theorem thermal_unique (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (V : Torus d → ℝ)
    (hV : Continuous V) (β : ℝ) (hβ : 0 ≤ β) (ρ₁ ρ₂ : Torus d → ℝ)
    (h1 : ∀ x, 0 ≤ ρ₁ x) (m1 : Measurable ρ₁) (i1 : ∫ x, ρ₁ x = 1)
    (h2 : ∀ x, 0 ≤ ρ₂ x) (m2 : Measurable ρ₂) (i2 : ∫ x, ρ₂ x = 1)
    (e1 : ∀ x, ρ₁ x = Real.exp (-β * (V x + ∫ y, specKernel a (x - y) * ρ₁ y)) /
        ∫ y, Real.exp (-β * (V y + ∫ z, specKernel a (y - z) * ρ₁ z)))
    (e2 : ∀ x, ρ₂ x = Real.exp (-β * (V x + ∫ y, specKernel a (x - y) * ρ₂ y)) /
        ∫ y, Real.exp (-β * (V y + ∫ z, specKernel a (y - z) * ρ₂ z))) : ρ₁ = ρ₂ := by
  have I1 := integrable_of_integral_one i1
  have I2 := integrable_of_integral_one i2
  set A1 : Torus d → ℝ := fun x => ∫ y, specKernel a (x - y) * ρ₁ y with hA1
  set A2 : Torus d → ℝ := fun x => ∫ y, specKernel a (x - y) * ρ₂ y with hA2
  have cA1 : Continuous A1 := continuous_conv ha0 has I1
  have cA2 : Continuous A2 := continuous_conv ha0 has I2
  set Z1 : ℝ := ∫ y, Real.exp (-β * (V y + A1 y)) with hZ1
  set Z2 : ℝ := ∫ y, Real.exp (-β * (V y + A2 y)) with hZ2
  have hZ1p : 0 < Z1 := integral_exp_pos
    ((Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)))
  have hZ2p : 0 < Z2 := integral_exp_pos
    ((Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)))
  have e1' : ∀ x, ρ₁ x = Real.exp (-β * (V x + A1 x)) / Z1 := e1
  have e2' : ∀ x, ρ₂ x = Real.exp (-β * (V x + A2 x)) / Z2 := e2
  have p1 : ∀ x, 0 < ρ₁ x := fun x => by rw [e1' x]; positivity
  have p2 : ∀ x, 0 < ρ₂ x := fun x => by rw [e2' x]; positivity
  have l1 : ∀ x, Real.log (ρ₁ x) = -β * (V x + A1 x) - Real.log Z1 := fun x => by
    rw [e1' x, Real.log_div (Real.exp_pos _).ne' hZ1p.ne', Real.log_exp]
  have l2 : ∀ x, Real.log (ρ₂ x) = -β * (V x + A2 x) - Real.log Z2 := fun x => by
    rw [e2' x, Real.log_div (Real.exp_pos _).ne' hZ2p.ne', Real.log_exp]
  set σ : Torus d → ℝ := fun x => ρ₁ x - ρ₂ x with hσ
  have Iσ : Integrable σ := I1.sub I2
  have hdiff : ∀ x, A1 x - A2 x = ∫ y, specKernel a (x - y) * σ y := by
    intro x
    have f1 := integrable_kernel_mul ha0 has x I1
    have f2 := integrable_kernel_mul ha0 has x I2
    simp only [hA1, hA2, hσ, mul_sub]
    rw [integral_sub f1 f2]
  -- the integrand
  set Dfun : Torus d → ℝ := fun x => σ x * (Real.log (ρ₁ x) - Real.log (ρ₂ x)) with hD
  have hDnn : ∀ x, 0 ≤ Dfun x := fun x => log_mono_aux (p1 x) (p2 x)
  have hDeq : ∀ x, Dfun x = σ x * (-β * (A1 x - A2 x) - (Real.log Z1 - Real.log Z2)) := by
    intro x; simp only [hD, l1, l2]; ring
  have hDint : Integrable Dfun := by
    have : Continuous fun x => -β * (A1 x - A2 x) - (Real.log Z1 - Real.log Z2) := by fun_prop
    have h3 : Integrable fun x => σ x * (-β * (A1 x - A2 x) - (Real.log Z1 - Real.log Z2)) := by
      obtain ⟨C, hC⟩ := (isCompact_univ.exists_bound_of_continuousOn this.continuousOn)
      exact Iσ.mul_bdd (c := C) this.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
    exact h3.congr (Filter.Eventually.of_forall fun x => (hDeq x).symm)
  have hDle : ∫ x, Dfun x ≤ 0 := by
    have hsum0 : ∫ x, σ x = 0 := by
      simp only [hσ]; rw [integral_sub I1 I2, i1, i2]; ring
    have hpd := posdef_nonneg ha0 has volume Iσ
    have hrew : ∫ x, Dfun x = -β * ∫ x, σ x * ∫ y, specKernel a (x - y) * σ y := by
      have hb1 : Integrable fun x => σ x * (A1 x - A2 x) := by
        obtain ⟨C, hC⟩ := (isCompact_univ.exists_bound_of_continuousOn (cA1.sub cA2).continuousOn)
        exact Iσ.mul_bdd (c := C) (cA1.sub cA2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
      calc ∫ x, Dfun x = ∫ x, (-β * (σ x * (A1 x - A2 x)) - (Real.log Z1 - Real.log Z2) * σ x) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [hDeq]; ring
        _ = -β * (∫ x, σ x * (A1 x - A2 x)) - (Real.log Z1 - Real.log Z2) * ∫ x, σ x := by
            rw [integral_sub (hb1.const_mul _) (Iσ.const_mul _), integral_const_mul,
              integral_const_mul]
        _ = -β * ∫ x, σ x * ∫ y, specKernel a (x - y) * σ y := by
            rw [hsum0]; simp only [hdiff]; ring
    rw [hrew]
    nlinarith
  have hD0 : ∫ x, Dfun x = 0 :=
    le_antisymm hDle (integral_nonneg hDnn)
  have hae : Dfun =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hDnn hDint).mp hD0
  have hρae : ρ₁ =ᵐ[volume] ρ₂ := by
    filter_upwards [hae] with x hx
    by_contra hne
    have : 0 < σ x * (Real.log (ρ₁ x) - Real.log (ρ₂ x)) := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact mul_pos_of_neg_of_neg (by simp only [hσ]; linarith)
          (by linarith [Real.log_lt_log (p1 x) h])
      · exact mul_pos (by simp only [hσ]; linarith) (by linarith [Real.log_lt_log (p2 x) h])
    have hx' : σ x * (Real.log (ρ₁ x) - Real.log (ρ₂ x)) = 0 := hx
    linarith
  have hA : A1 = A2 := by
    funext x
    simp only [hA1, hA2]
    exact integral_congr_ae (by filter_upwards [hρae] with y hy; rw [hy])
  funext x
  rw [e1' x, e2' x, hA]
  have : Z1 = Z2 := by simp only [hZ1, hZ2, hA]
  rw [this]

end ThermalUnique

section Existence

variable {a : Lattice d → ℝ}

/-- The feature field `A u (x) = ∑_i Ψ_i(x) u_i`. -/
def Aop (a : Lattice d → ℝ) (u : Idx d → ℝ) (x : Torus d) : ℝ := ∑' i, feat a i x * u i

/-- The box `|u_i| ≤ b_i`. -/
def box (a : Lattice d → ℝ) : Set (Idx d → ℝ) := Set.pi Set.univ fun i => Set.Icc (-fbound a i) (fbound a i)

theorem mem_box_iff {u : Idx d → ℝ} : u ∈ box a ↔ ∀ i, |u i| ≤ fbound a i := by
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]

theorem isCompact_box : IsCompact (box a) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem summable_feat_u (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {C : ℝ} {u : Idx d → ℝ}
    (hu : ∀ i, |u i| ≤ C * fbound a i) (x : Torus d) : Summable fun i => feat a i x * u i := by
  refine Summable.of_norm_bounded ((summable_fbound_sq ha0 has).mul_left C) fun i => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |feat a i x| * |u i| ≤ fbound a i * (C * fbound a i) :=
        mul_le_mul (abs_feat_le i x) (hu i) (abs_nonneg _) (fbound_nonneg i)
    _ = C * (fbound a i * fbound a i) := by ring

theorem abs_Aop_le (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {C : ℝ} {u : Idx d → ℝ}
    (hu : ∀ i, |u i| ≤ C * fbound a i) (x : Torus d) :
    |Aop a u x| ≤ C * ∑' i : Idx d, fbound a i * fbound a i := by
  have hs := summable_feat_u ha0 has hu x
  unfold Aop
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) hs.norm ((summable_fbound_sq ha0 has).mul_left C)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |feat a i x| * |u i| ≤ fbound a i * (C * fbound a i) :=
        mul_le_mul (abs_feat_le i x) (hu i) (abs_nonneg _) (fbound_nonneg i)
    _ = C * (fbound a i * fbound a i) := by ring

theorem continuousOn_Aop (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) :
    ContinuousOn (fun p : (Idx d → ℝ) × Torus d => Aop a p.1 p.2) (box a ×ˢ Set.univ) := by
  refine continuousOn_tsum (u := fun i => fbound a i * fbound a i) (fun i => ?_)
    (summable_fbound_sq ha0 has) ?_
  · exact ((continuous_feat i).comp continuous_snd).mul ((continuous_apply i).comp continuous_fst)
      |>.continuousOn
  · rintro i ⟨u, x⟩ ⟨hu, -⟩
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (abs_feat_le i x) (mem_box_iff.mp hu i) (abs_nonneg _) (fbound_nonneg i)

theorem continuous_Aop_x (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {u : Idx d → ℝ}
    (hu : u ∈ box a) : Continuous (Aop a u) := by
  refine continuous_tsum (u := fun i => fbound a i * fbound a i) (fun i => ?_)
    (summable_fbound_sq ha0 has) ?_
  · exact (continuous_feat i).mul continuous_const
  · intro i x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (abs_feat_le i x) (mem_box_iff.mp hu i) (abs_nonneg _) (fbound_nonneg i)

theorem continuousOn_Aop_u (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (x : Torus d) :
    ContinuousOn (fun u : Idx d → ℝ => Aop a u x) (box a) := by
  have := (continuousOn_Aop ha0 has (d := d)).comp (f := fun u : Idx d → ℝ => (u, x))
    (s := box a) (by fun_prop) (fun u hu => ⟨hu, Set.mem_univ _⟩)
  exact this

/-- The Gibbs weight. -/
def Wt (a : Lattice d → ℝ) (V : Torus d → ℝ) (β : ℝ) (u : Idx d → ℝ) (x : Torus d) : ℝ :=
  Real.exp (-β * (V x + Aop a u x))

/-- The partition function. -/
def Zt (a : Lattice d → ℝ) (V : Torus d → ℝ) (β : ℝ) (u : Idx d → ℝ) : ℝ := ∫ x, Wt a V β u x

theorem exists_bound_V {V : Torus d → ℝ} (hV : Continuous V) : ∃ M, ∀ x, |V x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hV.continuousOn
  exact ⟨M, fun x => by simpa using hM x (Set.mem_univ x)⟩

theorem Wt_bounds (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ} {MV : ℝ}
    (hMV : ∀ x, |V x| ≤ MV) {β : ℝ} (hβ : 0 ≤ β) {u : Idx d → ℝ} (hu : u ∈ box a) (x : Torus d) :
    Real.exp (-(β * (MV + ∑' i : Idx d, fbound a i * fbound a i))) ≤ Wt a V β u x ∧
      Wt a V β u x ≤ Real.exp (β * (MV + ∑' i : Idx d, fbound a i * fbound a i)) := by
  have hA := abs_Aop_le ha0 has (C := 1) (u := u) (fun i => by simpa using mem_box_iff.mp hu i) x
  have hV := hMV x
  rw [one_mul] at hA
  unfold Wt
  have h1 : |V x + Aop a u x| ≤ MV + ∑' i : Idx d, fbound a i * fbound a i := by
    calc |V x + Aop a u x| ≤ |V x| + |Aop a u x| := abs_add_le _ _
      _ ≤ _ := add_le_add hV hA
  have h2 := abs_le.mp h1
  constructor
  · apply Real.exp_le_exp.mpr; nlinarith [h2.1, h2.2]
  · apply Real.exp_le_exp.mpr; nlinarith [h2.1, h2.2]

theorem continuousOn_Zt (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) : ContinuousOn (Zt a V β) (box a) := by
  obtain ⟨MV, hMV⟩ := exists_bound_V hV
  refine continuousOn_of_dominated (bound := fun _ => Real.exp (β * (MV + ∑' i : Idx d, fbound a i * fbound a i))) ?_ ?_ ?_ ?_
  · intro u hu
    exact (Real.continuous_exp.comp (continuous_const.mul
      (hV.add (continuous_Aop_x ha0 has hu)))).aestronglyMeasurable
  · intro u hu
    refine Filter.Eventually.of_forall fun x => ?_
    show |Wt a V β u x| ≤ _
    rw [abs_of_pos (show 0 < Wt a V β u x from Real.exp_pos _)]
    exact (Wt_bounds ha0 has hMV hβ hu x).2
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (continuousOn_const.add (continuousOn_Aop_u ha0 has x))))

theorem Zt_pos (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) {u : Idx d → ℝ} (hu : u ∈ box a) : 0 < Zt a V β u := by
  obtain ⟨MV, hMV⟩ := exists_bound_V hV
  have hcont : Continuous (Wt a V β u) :=
    Real.continuous_exp.comp (continuous_const.mul (hV.add (continuous_Aop_x ha0 has hu)))
  have hint : Integrable (Wt a V β u) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have : (Real.exp (-(β * (MV + ∑' i : Idx d, fbound a i * fbound a i)))) ≤ Zt a V β u := by
    calc Real.exp (-(β * (MV + ∑' i : Idx d, fbound a i * fbound a i)))
        = ∫ _x : Torus d, Real.exp (-(β * (MV + ∑' i : Idx d, fbound a i * fbound a i))) := by simp
      _ ≤ Zt a V β u := integral_mono (integrable_const _) hint fun x => (Wt_bounds ha0 has hMV hβ hu x).1
  exact lt_of_lt_of_le (Real.exp_pos _) this

theorem continuousOn_sumsq (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) :
    ContinuousOn (fun u : Idx d → ℝ => ∑' i, u i ^ 2) (box a) := by
  refine continuousOn_tsum (u := fun i => fbound a i * fbound a i) (fun i => ?_)
    (summable_fbound_sq ha0 has) ?_
  · exact ((continuous_apply i).pow 2).continuousOn
  · intro i u hu
    have := mem_box_iff.mp hu i
    rw [Real.norm_eq_abs, abs_pow, sq]
    exact mul_le_mul this this (abs_nonneg _) (fbound_nonneg i)

/-- The free-energy functional in the feature variable. -/
def Phi (a : Lattice d → ℝ) (V : Torus d → ℝ) (β : ℝ) (u : Idx d → ℝ) : ℝ :=
  (β / 2) * ∑' i, u i ^ 2 + Real.log (Zt a V β u)

theorem continuousOn_Phi (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) : ContinuousOn (Phi a V β) (box a) := by
  unfold Phi
  refine ((continuousOn_sumsq ha0 has).const_smul (β / 2) |>.congr (fun u _ => by simp [smul_eq_mul])).add ?_
  exact (continuousOn_Zt ha0 has hV hβ).log fun u hu => (Zt_pos ha0 has hV hβ hu).ne'

theorem exists_min_box (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) : ∃ u ∈ box a, ∀ v ∈ box a, Phi a V β u ≤ Phi a V β v := by
  have hne : (box a).Nonempty := ⟨0, mem_box_iff.mpr fun i => by simpa using fbound_nonneg i⟩
  obtain ⟨u, hu, hmin⟩ := isCompact_box.exists_isMinOn hne (continuousOn_Phi ha0 has hV hβ)
  exact ⟨u, hu, fun v hv => hmin hv⟩

theorem continuous_Aop_x' (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {C : ℝ} {u : Idx d → ℝ}
    (hu : ∀ i, |u i| ≤ C * fbound a i) : Continuous (Aop a u) := by
  refine continuous_tsum (u := fun i => C * (fbound a i * fbound a i)) (fun i => ?_)
    ((summable_fbound_sq ha0 has).mul_left C) ?_
  · exact (continuous_feat i).mul continuous_const
  · intro i x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |feat a i x| * |u i| ≤ fbound a i * (C * fbound a i) :=
          mul_le_mul (abs_feat_le i x) (hu i) (abs_nonneg _) (fbound_nonneg i)
      _ = C * (fbound a i * fbound a i) := by ring

theorem Aop_add_smul (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {C C' : ℝ} {u w : Idx d → ℝ}
    (hu : ∀ i, |u i| ≤ C * fbound a i) (hw : ∀ i, |w i| ≤ C' * fbound a i) (t : ℝ) (x : Torus d) :
    Aop a (u + t • w) x = Aop a u x + t * Aop a w x := by
  unfold Aop
  have h1 := summable_feat_u ha0 has hu x
  have h2 := (summable_feat_u ha0 has hw x).mul_left t
  rw [← tsum_mul_left, ← h1.tsum_add h2]
  refine tsum_congr fun i => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Differentiation of the partition function along a direction. -/
theorem hasDerivAt_integral_exp {K L : Torus d → ℝ} (hK : Continuous K) (hL : Continuous L) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (K x + t * L x)) (∫ x, L x * Real.exp (K x)) 0 := by
  obtain ⟨MK, hMK⟩ := exists_bound_V hK
  obtain ⟨ML, hML⟩ := exists_bound_V hL
  have hcont : ∀ t : ℝ, Continuous fun x => Real.exp (K x + t * L x) := fun t =>
    Real.continuous_exp.comp (hK.add (continuous_const.mul hL))
  have hint : ∀ t : ℝ, Integrable fun x => Real.exp (K x + t * L x) := fun t =>
    (hcont t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (t : ℝ) (x : Torus d) => Real.exp (K x + t * L x))
    (F' := fun (t : ℝ) (x : Torus d) => L x * Real.exp (K x + t * L x)) (x₀ := 0)
    (s := Metric.ball 0 1) (bound := fun _ => ML * Real.exp (MK + ML))
    (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t => (hcont t).aestronglyMeasurable) (hint 0)
    (by exact (hL.mul (hcont 0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x t ht => by
      have ht' : |t| < 1 := by simpa [Real.dist_eq] using ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul (hML x) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
        ((abs_nonneg _).trans (hML x))
      have h1 := (abs_le.mp (hMK x)).2
      have h2 : t * L x ≤ ML :=
        calc t * L x ≤ |t * L x| := le_abs_self _
          _ = |t| * |L x| := abs_mul _ _
          _ ≤ 1 * ML := mul_le_mul ht'.le (hML x) (abs_nonneg _) zero_le_one
          _ = ML := one_mul _
      linarith)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ => by
      have h1 : HasDerivAt (fun t : ℝ => K x + t * L x) (L x) t := by
        simpa using ((hasDerivAt_id t).mul_const (L x)).const_add (K x)
      simpa [mul_comm] using h1.exp)
  simpa using this.2

/-- The feature moments of the Gibbs density `W_u / Z_u`. -/
def Fm (a : Lattice d → ℝ) (V : Torus d → ℝ) (β : ℝ) (u : Idx d → ℝ) (i : Idx d) : ℝ :=
  (∫ x, feat a i x * Wt a V β u x) / Zt a V β u

theorem continuous_Wt (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) (β : ℝ) {C : ℝ} {u : Idx d → ℝ} (hu : ∀ i, |u i| ≤ C * fbound a i) :
    Continuous (Wt a V β u) :=
  Real.continuous_exp.comp (continuous_const.mul (hV.add (continuous_Aop_x' ha0 has hu)))

theorem integrable_feat_Wt (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) (β : ℝ) {u : Idx d → ℝ} (hu : u ∈ box a) (i : Idx d) :
    Integrable fun x => feat a i x * Wt a V β u x :=
  (((continuous_feat i).mul (continuous_Wt ha0 has hV β (C := 1) (fun j => by
    simpa using mem_box_iff.mp hu j)))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem abs_Fm_le (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) {u : Idx d → ℝ} (hu : u ∈ box a) (i : Idx d) :
    |Fm a V β u i| ≤ fbound a i := by
  have hZ := Zt_pos ha0 has hV hβ hu
  have hW : Integrable (Wt a V β u) :=
    (continuous_Wt ha0 has hV β (C := 1) (fun j => by simpa using mem_box_iff.mp hu j)
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold Fm
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  calc |∫ x, feat a i x * Wt a V β u x| ≤ ∫ x, |feat a i x * Wt a V β u x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, fbound a i * Wt a V β u x := by
        refine integral_mono (integrable_feat_Wt ha0 has hV β hu i).abs (hW.const_mul _) fun x => ?_
        rw [abs_mul, abs_of_pos (show 0 < Wt a V β u x from Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (abs_feat_le i x) (Real.exp_pos _).le
    _ = fbound a i * Zt a V β u := by unfold Zt; rw [integral_const_mul]

theorem Fm_mem_box (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) {u : Idx d → ℝ} (hu : u ∈ box a) :
    Fm a V β u ∈ box a :=
  mem_box_iff.mpr fun i => abs_Fm_le ha0 has hV hβ hu i

theorem integral_Aop_mul (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} {u : Idx d → ℝ} (hu : u ∈ box a) {w : Idx d → ℝ} {C : ℝ}
    (hw : ∀ i, |w i| ≤ C * fbound a i) :
    HasSum (fun i => w i * ∫ x, feat a i x * Wt a V β u x)
      (∫ x, Aop a w x * Wt a V β u x) := by
  set Z1 : ℝ := ∫ x, |Wt a V β u x| with hZ1
  have hF : ∀ i : Idx d, Integrable (fun x => w i * (feat a i x * Wt a V β u x)) :=
    fun i => (integrable_feat_Wt ha0 has hV β hu i).const_mul _
  have hnorm : Summable fun i : Idx d => ∫ x, ‖w i * (feat a i x * Wt a V β u x)‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) ((summable_fbound_sq ha0 has).mul_right (C * Z1))
    calc ∫ x, ‖w i * (feat a i x * Wt a V β u x)‖
        ≤ ∫ x, (C * fbound a i) * (fbound a i * |Wt a V β u x|) := by
          refine integral_mono (hF i).norm ?_ fun x => ?_
          · exact ((continuous_Wt ha0 has hV β (C := 1) (fun j => by
              simpa using mem_box_iff.mp hu j)).abs.integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)).const_mul _ |>.const_mul _
          · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
            exact mul_le_mul (hw i) (mul_le_mul_of_nonneg_right (abs_feat_le i x) (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg _).trans (hw i))
      _ = fbound a i * fbound a i * (C * Z1) := by
          rw [integral_const_mul, integral_const_mul]; ring
  have := hasSum_integral_of_summable_integral_norm hF hnorm
  have e1 : ∀ i : Idx d, ∫ x, w i * (feat a i x * Wt a V β u x) =
      w i * ∫ x, feat a i x * Wt a V β u x := fun i => integral_const_mul _ _
  have e2 : ∀ x, ∑' i : Idx d, w i * (feat a i x * Wt a V β u x) =
      Aop a w x * Wt a V β u x := by
    intro x
    unfold Aop
    rw [← tsum_mul_right]
    exact tsum_congr fun i => by ring
  simp_rw [e1, e2] at this
  exact this

theorem deriv_nonneg_of_min {g : ℝ → ℝ} {g' : ℝ} (h : HasDerivAt g g' 0)
    (hmin : ∀ t ∈ Set.Icc (0:ℝ) 1, g 0 ≤ g t) : 0 ≤ g' := by
  by_contra hneg
  push_neg at hneg
  have h1 := h.tendsto_slope_zero_right
  have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (g (0 + t) - g 0) < 0 :=
    h1.eventually (gt_mem_nhds hneg)
  have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨t, ht2, ht3⟩ := (h2.and h3).exists
  have := hmin t ⟨ht3.1.le, ht3.2.le⟩
  simp only [zero_add, smul_eq_mul] at ht2
  have : 0 ≤ t⁻¹ * (g t - g 0) := mul_nonneg (inv_nonneg.mpr ht3.1.le) (by linarith)
  linarith

/-- A minimiser of the free energy on the box is a fixed point of the Gibbs map. -/
theorem fixed_point_of_min (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 < β) {u : Idx d → ℝ} (hu : u ∈ box a)
    (hmin : ∀ v ∈ box a, Phi a V β u ≤ Phi a V β v) : ∀ i, u i = Fm a V β u i := by
  have hsq : Summable fun i : Idx d => fbound a i * fbound a i := summable_fbound_sq ha0 has
  set c : Idx d → ℝ := Fm a V β u with hc
  have hcb : c ∈ box a := Fm_mem_box ha0 has hV hβ.le hu
  set w : Idx d → ℝ := c - u with hw
  have hu1 : ∀ i, |u i| ≤ 1 * fbound a i := fun i => by simpa using mem_box_iff.mp hu i
  have hc1 : ∀ i, |c i| ≤ 1 * fbound a i := fun i => by simpa using mem_box_iff.mp hcb i
  have hw2 : ∀ i, |w i| ≤ 2 * fbound a i := by
    intro i
    simp only [hw, Pi.sub_apply]
    have h1 := hu1 i
    have h2 := hc1 i
    calc |c i - u i| ≤ |c i| + |u i| := abs_sub _ _
      _ ≤ 2 * fbound a i := by linarith
  -- summability
  have sq_le : ∀ (p q : Idx d → ℝ) (C D : ℝ), (∀ i, |p i| ≤ C * fbound a i) →
      (∀ i, |q i| ≤ D * fbound a i) → Summable fun i => p i * q i := by
    intro p q C D hp hq
    refine Summable.of_norm_bounded ((hsq).mul_left (C * D)) fun i => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |p i| * |q i| ≤ (C * fbound a i) * (D * fbound a i) :=
          mul_le_mul (hp i) (hq i) (abs_nonneg _) ((abs_nonneg _).trans (hp i))
      _ = C * D * (fbound a i * fbound a i) := by ring
  have su2 : Summable fun i => u i ^ 2 := by simpa [sq] using sq_le u u 1 1 hu1 hu1
  have suw : Summable fun i => u i * w i := sq_le u w 1 2 hu1 hw2
  have sw2 : Summable fun i => w i ^ 2 := by simpa [sq] using sq_le w w 2 2 hw2 hw2
  have swc : Summable fun i => w i * c i := sq_le w c 2 1 hw2 hc1
  set S0 := ∑' i, u i ^ 2 with hS0
  set S1 := ∑' i, u i * w i with hS1
  set S2 := ∑' i, w i ^ 2 with hS2
  -- K and L
  set K : Torus d → ℝ := fun x => -β * (V x + Aop a u x) with hK
  set L : Torus d → ℝ := fun x => -β * Aop a w x with hL
  have hAu : Continuous (Aop a u) := continuous_Aop_x' ha0 has hu1
  have hAw : Continuous (Aop a w) := continuous_Aop_x' ha0 has hw2
  have hKc : Continuous K := continuous_const.mul (hV.add hAu)
  have hLc : Continuous L := continuous_const.mul hAw
  have hZt : ∀ t : ℝ, Zt a V β (u + t • w) = ∫ x, Real.exp (K x + t * L x) := by
    intro t
    unfold Zt Wt
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (-β * (V x + Aop a (u + t • w) x)) = Real.exp (K x + t * L x)
    rw [Aop_add_smul ha0 has hu1 hw2 t x]
    congr 1; simp only [hK, hL]; ring
  have hquad : ∀ t : ℝ, ∑' i, (u + t • w) i ^ 2 = S0 + 2 * t * S1 + t ^ 2 * S2 := by
    intro t
    have h := (su2.hasSum.add (suw.hasSum.mul_left (2 * t))).add (sw2.hasSum.mul_left (t ^ 2))
    have e : (fun i => u i ^ 2 + 2 * t * (u i * w i) + t ^ 2 * w i ^ 2) =
        fun i => (u + t • w) i ^ 2 := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e] at h
    rw [h.tsum_eq]
  set g : ℝ → ℝ := fun t => Phi a V β (u + t • w) with hg
  have hgeq : ∀ t, g t = β / 2 * (S0 + 2 * t * S1 + t ^ 2 * S2) +
      Real.log (∫ x, Real.exp (K x + t * L x)) := by
    intro t
    simp only [hg, Phi, hquad, hZt]
  -- the derivative of g at 0
  have hZ0 : ∫ x, Real.exp (K x + (0:ℝ) * L x) = Zt a V β u := by
    simp [Zt, Wt, hK]
  have hZpos : 0 < Zt a V β u := Zt_pos ha0 has hV hβ.le hu
  have hlog := (hasDerivAt_integral_exp hKc hLc).log (by rw [hZ0]; exact hZpos.ne')
  have hq : HasDerivAt (fun t : ℝ => β / 2 * (S0 + 2 * t * S1 + t ^ 2 * S2)) (β * S1) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    have h := ((((h1.const_mul 2).mul_const S1).const_add S0).add ((h1.pow 2).mul_const S2)).const_mul (β / 2)
    refine h.congr_deriv ?_
    norm_num; ring
  have hg' : HasDerivAt g (β * S1 + (∫ x, L x * Real.exp (K x)) / Zt a V β u) 0 := by
    have := hq.add hlog
    rw [hZ0] at this
    convert this using 1
    funext t; exact hgeq t
  -- evaluate the integral
  have hint : ∫ x, L x * Real.exp (K x) = -β * (Zt a V β u * ∑' i, w i * c i) := by
    have h1 := integral_Aop_mul ha0 has hV (β := β) hu hw2
    have h2 : ∀ i, w i * ∫ x, feat a i x * Wt a V β u x = Zt a V β u * (w i * c i) := by
      intro i
      simp only [hc, Fm]
      field_simp
    have h3 : HasSum (fun i => Zt a V β u * (w i * c i)) (∫ x, Aop a w x * Wt a V β u x) := by
      simpa only [h2] using h1
    have h4 : ∫ x, Aop a w x * Wt a V β u x = Zt a V β u * ∑' i, w i * c i := by
      rw [← h3.tsum_eq, tsum_mul_left]
    calc ∫ x, L x * Real.exp (K x) = ∫ x, -β * (Aop a w x * Wt a V β u x) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [hL, hK, Wt]; ring
      _ = _ := by rw [integral_const_mul, h4]
  rw [hint] at hg'
  have hg'val : β * S1 + -β * (Zt a V β u * ∑' i, w i * c i) / Zt a V β u = -β * S2 := by
    have : S1 - ∑' i, w i * c i = -S2 := by
      rw [hS1, hS2, ← suw.tsum_sub swc, ← tsum_neg]
      refine tsum_congr fun i => ?_
      have : w i = c i - u i := by simp [hw]
      rw [this]; ring
    field_simp
    nlinarith [this]
  rw [hg'val] at hg'
  have hmin' : ∀ t ∈ Set.Icc (0:ℝ) 1, g 0 ≤ g t := by
    intro t ht
    have hmem : u + t • w ∈ box a := by
      refine mem_box_iff.mpr fun i => ?_
      have h1 := mem_box_iff.mp hu i
      have h2 := mem_box_iff.mp hcb i
      simp only [hw, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have : u i + t * (c i - u i) = (1 - t) * u i + t * c i := by ring
      rw [this]
      calc |(1 - t) * u i + t * c i| ≤ |(1 - t) * u i| + |t * c i| := abs_add_le _ _
        _ = (1 - t) * |u i| + t * |c i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t),
              abs_of_nonneg ht.1]
        _ ≤ (1 - t) * fbound a i + t * fbound a i := by
            gcongr <;> linarith [ht.1, ht.2]
        _ = fbound a i := by ring
    have h0 : g 0 = Phi a V β u := by simp [hg]
    rw [h0]; exact hmin _ hmem
  have hnn := deriv_nonneg_of_min hg' hmin'
  have hS2le : S2 ≤ 0 := by nlinarith
  intro i
  have hwi : w i ^ 2 ≤ S2 := sw2.le_tsum i (fun j _ => sq_nonneg _)
  have : w i = 0 := by nlinarith [sq_nonneg (w i)]
  have : c i = u i := by
    have h' : w i = c i - u i := by simp [hw]
    linarith
  exact this.symm

/-- The convolution of the spectral kernel with the Gibbs density of a fixed point is the
feature field. -/
theorem conv_gibbs_eq_Aop (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) {u : Idx d → ℝ} (hu : u ∈ box a)
    (hfix : ∀ i, u i = Fm a V β u i) (x : Torus d) :
    ∫ y, specKernel a (x - y) * (Wt a V β u y / Zt a V β u) = Aop a u x := by
  have hZ := Zt_pos ha0 has hV hβ hu
  set ρ : Torus d → ℝ := fun y => Wt a V β u y / Zt a V β u with hρ
  have hρc : Continuous ρ :=
    (continuous_Wt ha0 has hV β (C := 1) (fun j => by simpa using mem_box_iff.mp hu j)).div_const _
  have hρ0 : ∀ y, 0 < ρ y := fun y => div_pos (Real.exp_pos _) hZ
  have hρint : ∫ y, ρ y = 1 := by
    simp only [hρ]; rw [integral_div]; exact div_self hZ.ne'
  have hFi : ∀ i : Idx d, Integrable (fun y => feat a i x * (feat a i y * ρ y)) := by
    intro i
    exact (((continuous_feat i).mul hρc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have hnorm : Summable fun i : Idx d => ∫ y, ‖feat a i x * (feat a i y * ρ y)‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) (summable_fbound_sq ha0 has)
    calc ∫ y, ‖feat a i x * (feat a i y * ρ y)‖ ≤ ∫ y, fbound a i * (fbound a i * ρ y) := by
          refine integral_mono (hFi i).norm ?_ fun y => ?_
          · exact ((hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _).const_mul _
          · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (hρ0 y)]
            exact mul_le_mul (abs_feat_le i x) (mul_le_mul_of_nonneg_right (abs_feat_le i y) (hρ0 y).le)
              (mul_nonneg (abs_nonneg _) (hρ0 y).le) (fbound_nonneg i)
      _ = fbound a i * fbound a i := by
          rw [integral_const_mul, integral_const_mul, hρint]; ring
  have h := hasSum_integral_of_summable_integral_norm hFi hnorm
  have e1 : ∀ i : Idx d, ∫ y, feat a i x * (feat a i y * ρ y) = feat a i x * u i := by
    intro i
    have h1 : ∫ y, feat a i y * ρ y = Fm a V β u i := by
      simp only [Fm, hρ]
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
    rw [integral_const_mul, h1, ← hfix i]
  have e2 : ∀ y, ∑' i : Idx d, feat a i x * (feat a i y * ρ y) = specKernel a (x - y) * ρ y := by
    intro y
    have := (hasSum_feat_mul ha0 has x y).mul_right (ρ y)
    rw [← this.tsum_eq]
    exact tsum_congr fun i => by ring
  simp_rw [e1, e2] at h
  exact h.tsum_eq.symm

/-- Existence of the thermal equilibrium density for a bounded positive-definite spectral
kernel (the Gibbs fixed-point equation). -/
theorem exists_thermal_density (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {V : Torus d → ℝ}
    (hV : Continuous V) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ ρ : Torus d → ℝ, Continuous ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x = 1 ∧
      ∀ x, ρ x = Real.exp (-β * (V x + ∫ y, specKernel a (x - y) * ρ y)) /
        ∫ y, Real.exp (-β * (V y + ∫ z, specKernel a (y - z) * ρ z)) := by
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨fun _ => 1, continuous_const, fun _ => one_pos, by simp, fun x => by simp⟩
  · obtain ⟨u, hu, hmin⟩ := exists_min_box ha0 has hV hβ
    have hfix := fixed_point_of_min ha0 has hV hpos hu hmin
    have hZ := Zt_pos ha0 has hV hβ hu
    have hconv := conv_gibbs_eq_Aop ha0 has hV hβ hu hfix
    refine ⟨fun y => Wt a V β u y / Zt a V β u, ?_, fun y => div_pos (Real.exp_pos _) hZ, ?_, ?_⟩
    · exact (continuous_Wt ha0 has hV β (C := 1) (fun j => by
        simpa using mem_box_iff.mp hu j)).div_const _
    · rw [integral_div]; exact div_self hZ.ne'
    · intro x
      have e : ∀ y, Real.exp (-β * (V y + ∫ z, specKernel a (y - z) * (Wt a V β u z / Zt a V β u))) =
          Wt a V β u y := fun y => by rw [hconv y]; rfl
      simp only [e]
      rfl

end Existence


end HRS.StaticLimitAux

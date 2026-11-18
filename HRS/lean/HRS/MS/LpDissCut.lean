import HRS.MS.LpDissConvex
import HRS.MS.LpDissCoeff
import HRS.MS.LpDissDual
import HRS.MS.CzElemBAux1

/-!
# S.A.16.C4: weighted cutoff coercivity for Schwartz tensors

`sa16bd_weighted_cutoff`: for a nonnegative `C_b²` weight `μ` and a Schwartz tensor `W`, the weighted
positive-radius dissipation is finite and controlled by the signed leading energy plus a coefficient
error, uniformly in the cutoff.  Pointwise in `x` the vector Bregman inequality (C1) is integrated
against the cutoff kernel; in `x` the exchange of the scalar fractional difference of `V^p` onto `μ`
is the finite-cutoff duality (C3), and the coefficient term is bounded by C2.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemB

universe u

namespace HRS.Whole.AppendixA.BreakdownSA16

/-! ### elementary facts on the kernel and on cutoff differences -/

lemma sa16bd_K_nonneg (d : ℕ) (θ ε : ℝ) (z : Euc d) : 0 ≤ sa16bd_K d θ ε z :=
  Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z

lemma sa16bd_vnorm_le_sum {ι : Type u} [Fintype ι] (v : ι → ℝ) : vnorm v ≤ ∑ i, |v i| := by
  unfold vnorm
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |v i|)
    (fun i _ => abs_nonneg _)
  simpa only [sq_abs] using this

lemma sa16bd_vnorm_sub_le {ι : Type u} [Fintype ι] (a b : ι → ℝ) :
    vnorm (fun i => a i - b i) ≤ vnorm a + vnorm b := by
  have := sa16bd_vnorm_le (fun i => a i - b i) a b (-1) (fun i => by ring)
  simpa using this

lemma sa16bd_diff_integrable {d : ℕ} (hd : 1 ≤ d) {θ ε : ℝ} (hθ0 : 0 < θ) (hε : 0 < ε)
    {f : Euc d → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : Euc d) :
    Integrable (fun z : Euc d => (f x - f (x - z)) * sa16bd_K d θ ε z) := by
  have hKi := sa16bd_K_integrable hd θ hθ0 hε
  have hm : AEStronglyMeasurable (fun z : Euc d => f x - f (x - z)) volume :=
    (continuous_const.sub (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  refine hKi.bdd_mul (c := B + B) hm (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hB x
  have h2 := hB (x - z)
  calc |f x - f (x - z)| ≤ |f x| + |f (x - z)| := abs_sub _ _
    _ ≤ B + B := by linarith

lemma sa16bd_lapCut_abs_le {d : ℕ} (hd : 1 ≤ d) {θ ε : ℝ} (hθ0 : 0 < θ) (hε : 0 < ε)
    {f : Euc d → ℝ} (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : Euc d) :
    |sa16bd_lapCut d θ ε f x| ≤ (B + B) * ∫ z, sa16bd_K d θ ε z := by
  have hKi := sa16bd_K_integrable hd θ hθ0 hε
  rw [sa16bd_lapCut_eq]
  have hi := sa16bd_diff_integrable hd hθ0 hε hf hB x
  calc |∫ z, (f x - f (x - z)) * sa16bd_K d θ ε z|
      ≤ ∫ z, |(f x - f (x - z)) * sa16bd_K d θ ε z| := by
        have := norm_integral_le_integral_norm (μ := (volume : Measure (Euc d)))
          (fun z : Euc d => (f x - f (x - z)) * sa16bd_K d θ ε z)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ z, (B + B) * sa16bd_K d θ ε z := by
        refine integral_mono hi.abs (hKi.const_mul (B + B)) fun z => ?_
        rw [abs_mul, abs_of_nonneg (sa16bd_K_nonneg d θ ε z)]
        refine mul_le_mul_of_nonneg_right ?_ (sa16bd_K_nonneg d θ ε z)
        have h1 := hB x
        have h2 := hB (x - z)
        calc |f x - f (x - z)| ≤ |f x| + |f (x - z)| := abs_sub _ _
          _ ≤ B + B := by linarith
    _ = (B + B) * ∫ z, sa16bd_K d θ ε z := by rw [integral_const_mul]

lemma sa16bd_lapCut_aesm (d : ℕ) (θ ε : ℝ) {f : Euc d → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable (fun x : Euc d => sa16bd_lapCut d θ ε f x) volume := by
  have h : (fun x : Euc d => sa16bd_lapCut d θ ε f x) = fun x : Euc d =>
      ∫ z, (fun p : Euc d × Euc d => (f p.1 - f (p.1 - p.2)) * sa16bd_K d θ ε p.2) (x, z) := by
    funext x
    exact sa16bd_lapCut_eq d θ ε f x
  rw [h]
  have h1 : Measurable (fun p : Euc d × Euc d => f p.1) := hf.measurable.comp measurable_fst
  have h2 : Measurable (fun p : Euc d × Euc d => f (p.1 - p.2)) :=
    hf.measurable.comp (measurable_fst.sub measurable_snd :
      Measurable fun p : Euc d × Euc d => p.1 - p.2)
  have h3 : Measurable (fun p : Euc d × Euc d => sa16bd_K d θ ε p.2) :=
    (sa16bd_K_measurable d θ ε).comp measurable_snd
  have hF : AEStronglyMeasurable (fun p : Euc d × Euc d =>
      (f p.1 - f (p.1 - p.2)) * sa16bd_K d θ ε p.2) (volume.prod volume) :=
    ((h1.sub h2).mul h3).aestronglyMeasurable
  exact hF.integral_prod_right'

/-! ### pointwise (in `x`) estimates for a continuous bounded tensor field -/

/-- the cutoff dissipation integral at `x`, as a real Bochner integral against the kernel `K` -/
def sa16bd_Dint {ι : Type u} [Fintype ι] (d : ℕ) (θ p ε : ℝ) (w : ι → Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z, (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
    vnorm (fun i => w i x - w i (x - z)) ^ 2 * sa16bd_K d θ ε z

lemma sa16bd_V_le {ι : Type u} [Fintype ι] {d : ℕ} (w : ι → Euc d → ℝ) {Bw : ℝ}
    (hwb : ∀ i y, |w i y| ≤ Bw) (y : Euc d) : vnorm (fun i => w i y) ≤ (Fintype.card ι : ℝ) * Bw := by
  refine (sa16bd_vnorm_le_sum _).trans ?_
  calc ∑ i, |w i y| ≤ ∑ _i : ι, Bw := Finset.sum_le_sum fun i _ => hwb i y
    _ = _ := by simp


lemma sa16bd_Dint_integrand_bound {ι : Type u} [Fintype ι] {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (w : ι → Euc d → ℝ) {Bw : ℝ} (hwb : ∀ i y, |w i y| ≤ Bw) (x z : Euc d) :
    0 ≤ (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
        vnorm (fun i => w i x - w i (x - z)) ^ 2 ∧
    (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
        vnorm (fun i => w i x - w i (x - z)) ^ 2 ≤ (2 * ((Fintype.card ι : ℝ) * Bw)) ^ p := by
  set a : ι → ℝ := fun i => w i x with ha
  set b : ι → ℝ := fun i => w i (x - z) with hb
  have hRa : 0 ≤ vnorm a := Real.sqrt_nonneg _
  have hRb : 0 ≤ vnorm b := Real.sqrt_nonneg _
  set R := vnorm a + vnorm b with hR
  have hR0 : 0 ≤ R := add_nonneg hRa hRb
  have hRle : R ≤ 2 * ((Fintype.card ι : ℝ) * Bw) := by
    have h1 := sa16bd_V_le w hwb x
    have h2 := sa16bd_V_le w hwb (x - z)
    simp only [hR, ha, hb]
    linarith
  have hΔ : vnorm (fun i => a i - b i) ≤ R := sa16bd_vnorm_sub_le a b
  have hΔ0 : 0 ≤ vnorm (fun i => a i - b i) := Real.sqrt_nonneg _
  have hp0 : (0 : ℝ) < p := by linarith
  refine ⟨mul_nonneg (Real.rpow_nonneg hR0 _) (sq_nonneg _), ?_⟩
  calc R ^ (p - 2) * vnorm (fun i => a i - b i) ^ 2 ≤ R ^ (p - 2) * R ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΔ0 hΔ 2) (Real.rpow_nonneg hR0 _)
    _ = R ^ p := by
        rw [← Real.rpow_natCast R 2, ← Real.rpow_add' hR0 (by norm_num; linarith)]
        congr 1
        push_cast
        ring
    _ ≤ (2 * ((Fintype.card ι : ℝ) * Bw)) ^ p := Real.rpow_le_rpow hR0 hRle hp0.le

lemma sa16bd_Dint_integrable {ι : Type u} [Fintype ι] {d : ℕ} (hd : 1 ≤ d) {θ ε : ℝ} (hθ0 : 0 < θ)
    (hε : 0 < ε) {p : ℝ} (hp : 2 ≤ p) (w : ι → Euc d → ℝ) (hwc : ∀ i, Continuous (w i)) {Bw : ℝ}
    (hwb : ∀ i y, |w i y| ≤ Bw) (x : Euc d) :
    Integrable (fun z : Euc d =>
      (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
        vnorm (fun i => w i x - w i (x - z)) ^ 2 * sa16bd_K d θ ε z) := by
  have hKi := sa16bd_K_integrable hd θ hθ0 hε
  have hc : Continuous (fun z : Euc d =>
      (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
        vnorm (fun i => w i x - w i (x - z)) ^ 2) := by
    have hv : Continuous (fun z : Euc d => vnorm (fun i => w i (x - z))) :=
      elemb_vnorm_continuous (f := fun i z => w i (x - z))
        fun i => (hwc i).comp (continuous_const.sub continuous_id)
    have hv2 : Continuous (fun z : Euc d => vnorm (fun i => w i x - w i (x - z))) :=
      elemb_vnorm_continuous (f := fun i z => w i x - w i (x - z))
        fun i => continuous_const.sub ((hwc i).comp (continuous_const.sub continuous_id))
    refine Continuous.mul (Continuous.rpow_const (continuous_const.add hv) ?_) (hv2.pow 2)
    intro z
    right
    linarith
  refine hKi.bdd_mul (c := (2 * ((Fintype.card ι : ℝ) * Bw)) ^ p) hc.aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  obtain ⟨h0, h1⟩ := sa16bd_Dint_integrand_bound hp w hwb x z
  rwa [Real.norm_eq_abs, abs_of_nonneg h0]

lemma sa16bd_dissCut_eq {ι : Type u} [Fintype ι] {d : ℕ} (hd : 1 ≤ d) {θ ε : ℝ} (hθ0 : 0 < θ)
    (hε : 0 < ε) {p : ℝ} (hp : 2 ≤ p) (w : ι → Euc d → ℝ) (hwc : ∀ i, Continuous (w i)) {Bw : ℝ}
    (hwb : ∀ i y, |w i y| ≤ Bw) (x : Euc d) :
    sa16bd_dissCut d θ p ε (fun y i => w i y) x = ENNReal.ofReal (sa16bd_Dint d θ p ε w x) := by
  have hS : MeasurableSet {z : Euc d | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hi := sa16bd_Dint_integrable hd hθ0 hε hp w hwc hwb x
  have hnn : 0 ≤ᵐ[volume] (fun z : Euc d =>
      (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
        vnorm (fun i => w i x - w i (x - z)) ^ 2 * sa16bd_K d θ ε z) :=
    Eventually.of_forall fun z =>
      mul_nonneg (sa16bd_Dint_integrand_bound hp w hwb x z).1 (sa16bd_K_nonneg d θ ε z)
  unfold sa16bd_Dint
  rw [ofReal_integral_eq_lintegral_ofReal hi hnn]
  unfold sa16bd_dissCut
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ {z : Euc d | ε < ‖z‖}
  · simp only [Set.indicator_of_mem hz, sa16bd_K]
    rw [Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]
  · simp [Set.indicator_of_notMem hz, sa16bd_K]


lemma sa16bd_Vp_bounds {ι : Type u} [Fintype ι] {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (w : ι → Euc d → ℝ) (hwc : ∀ i, Continuous (w i)) {Bw : ℝ} (hwb : ∀ i y, |w i y| ≤ Bw) :
    Continuous (fun y : Euc d => vnorm (fun i => w i y) ^ p) ∧
      ∀ y, |vnorm (fun i => w i y) ^ p| ≤ ((Fintype.card ι : ℝ) * Bw) ^ p := by
  have hVc : Continuous (fun y : Euc d => vnorm (fun i => w i y)) := elemb_vnorm_continuous hwc
  refine ⟨hVc.rpow_const (fun _ => Or.inr (by linarith)), fun y => ?_⟩
  have h0 : 0 ≤ vnorm (fun i => w i y) := Real.sqrt_nonneg _
  rw [abs_of_nonneg (Real.rpow_nonneg h0 _)]
  exact Real.rpow_le_rpow h0 (sa16bd_V_le w hwb y) (by linarith)

lemma sa16bd_Dint_le {ι : Type u} [Fintype ι] {d : ℕ} (hd : 1 ≤ d) {θ ε : ℝ} (hθ0 : 0 < θ)
    (hε : 0 < ε) {p : ℝ} (hp : 2 ≤ p) (w : ι → Euc d → ℝ) (hwc : ∀ i, Continuous (w i)) {Bw : ℝ}
    (hwb : ∀ i y, |w i y| ≤ Bw) (x : Euc d) :
    sa16bd_convexityConst p * sa16bd_Dint d θ p ε w x ≤
      vnorm (fun i => w i x) ^ (p - 2) * (∑ i, w i x * sa16bd_lapCut d θ ε (w i) x) -
        (1 / p) * sa16bd_lapCut d θ ε (fun y => vnorm (fun i => w i y) ^ p) x := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hVpc, hVpb⟩ := sa16bd_Vp_bounds hp w hwc hwb
  have hIi : ∀ i, Integrable (fun z : Euc d => (w i x - w i (x - z)) * sa16bd_K d θ ε z) :=
    fun i => sa16bd_diff_integrable hd hθ0 hε (hwc i) (hwb i) x
  have hIV : Integrable (fun z : Euc d =>
      (vnorm (fun i => w i x) ^ p - vnorm (fun i => w i (x - z)) ^ p) * sa16bd_K d θ ε z) :=
    sa16bd_diff_integrable hd hθ0 hε (f := fun y => vnorm (fun i => w i y) ^ p) hVpc hVpb x
  set r : Euc d → ℝ := fun z =>
    vnorm (fun i => w i x) ^ (p - 2) * ∑ i, w i x * ((w i x - w i (x - z)) * sa16bd_K d θ ε z) -
      (1 / p) * ((vnorm (fun i => w i x) ^ p - vnorm (fun i => w i (x - z)) ^ p) *
        sa16bd_K d θ ε z) with hr
  have hri : Integrable r := by
    refine Integrable.sub ?_ (hIV.const_mul (1 / p))
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun i _ => by
      have := (hIi i).const_mul (w i x)
      exact this
  have hint : ∫ z, r z = vnorm (fun i => w i x) ^ (p - 2) * (∑ i, w i x * sa16bd_lapCut d θ ε (w i) x) -
      (1 / p) * sa16bd_lapCut d θ ε (fun y => vnorm (fun i => w i y) ^ p) x := by
    simp only [hr]
    rw [integral_sub, integral_const_mul, integral_const_mul, integral_finset_sum]
    · simp only [integral_const_mul, sa16bd_lapCut_eq]
    · exact fun i _ => (hIi i).const_mul (w i x)
    · exact Integrable.const_mul (integrable_finset_sum _ fun i _ => (hIi i).const_mul (w i x)) _
    · exact hIV.const_mul _
  rw [← hint]
  unfold sa16bd_Dint
  rw [← integral_const_mul]
  refine integral_mono ((sa16bd_Dint_integrable hd hθ0 hε hp w hwc hwb x).const_mul _) hri
    fun z => ?_
  have hK := sa16bd_K_nonneg d θ ε z
  have hb := (sa16bd_power_bregman p hp (fun i => w i x) (fun i => w i (x - z))).2
  have e : (∑ i, w i x * (w i x - w i (x - z))) * sa16bd_K d θ ε z =
      ∑ i, w i x * ((w i x - w i (x - z)) * sa16bd_K d θ ε z) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 := mul_le_mul_of_nonneg_right hb hK
  have key : (vnorm (fun i => w i x) ^ (p - 2) * (∑ i, w i x * (w i x - w i (x - z))) -
      (vnorm (fun i => w i x) ^ p - vnorm (fun i => w i (x - z)) ^ p) / p) *
        sa16bd_K d θ ε z = r z := by
    simp only [hr]
    rw [sub_mul, mul_assoc, e]
    ring
  have h4 : sa16bd_convexityConst p * ((vnorm (fun i => w i x) +
        vnorm (fun i => w i (x - z))) ^ (p - 2) *
      vnorm (fun i => w i x - w i (x - z)) ^ 2 * sa16bd_K d θ ε z) =
      (sa16bd_convexityConst p * (vnorm (fun i => w i x) + vnorm (fun i => w i (x - z))) ^ (p - 2) *
        vnorm (fun i => w i x - w i (x - z)) ^ 2) * sa16bd_K d θ ε z := by ring
  rw [h4, ← key]
  exact h3


/-! ### Schwartz tensors -/

section Schwartz

variable {d : ℕ} {ι : Type u} [Fintype ι]

lemma sa16bd_schwartz_bound (W : ι → 𝓢(Euc d, ℝ)) :
    ∃ Bw : ℝ, 0 ≤ Bw ∧ ∀ i y, |W i y| ≤ Bw := by
  refine ⟨∑ i, SchwartzMap.seminorm ℝ 0 0 (W i),
    Finset.sum_nonneg fun i _ => apply_nonneg _ _, fun i y => ?_⟩
  have h1 : |W i y| ≤ SchwartzMap.seminorm ℝ 0 0 (W i) := by
    have := (W i).le_seminorm ℝ 0 0 y
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun i => SchwartzMap.seminorm ℝ 0 0 (W i))
    (fun i _ => apply_nonneg _ _) (Finset.mem_univ i)

lemma sa16bd_V_integrable (W : ι → 𝓢(Euc d, ℝ)) :
    Integrable (fun y : Euc d => vnorm (fun i => W i y)) := by
  have hc : Continuous (fun y : Euc d => vnorm (fun i => W i y)) :=
    elemb_vnorm_continuous (f := fun i y => W i y) fun i => (W i).continuous
  refine Integrable.mono' (integrable_finset_sum (Finset.univ : Finset ι)
    (f := fun i y => |W i y|) fun i _ => (W i).integrable.abs) hc.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ vnorm (fun i => W i y) := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg h0]
  have := sa16bd_vnorm_le_sum (fun i => W i y)
  simpa using this

lemma sa16bd_Vq_integrable (W : ι → 𝓢(Euc d, ℝ)) {q : ℝ} (hq : 1 ≤ q) :
    Integrable (fun y : Euc d => vnorm (fun i => W i y) ^ q) := by
  obtain ⟨Bw, -, hBw⟩ := sa16bd_schwartz_bound W
  have hc : Continuous (fun y : Euc d => vnorm (fun i => W i y)) :=
    elemb_vnorm_continuous (f := fun i y => W i y) fun i => (W i).continuous
  refine Integrable.mono' ((sa16bd_V_integrable W).const_mul (((Fintype.card ι : ℝ) * Bw) ^ (q - 1)))
    (hc.rpow_const (fun _ => Or.inr (by linarith))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ vnorm (fun i => W i y) := Real.sqrt_nonneg _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 _)]
  have e : vnorm (fun i => W i y) ^ q = vnorm (fun i => W i y) ^ (q - 1) * vnorm (fun i => W i y) := by
    conv_lhs => rw [show q = (q - 1) + 1 by ring]
    rw [Real.rpow_add' h0 (by linarith), Real.rpow_one]
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ h0
  exact Real.rpow_le_rpow h0 (sa16bd_V_le (fun i y => W i y) hBw y) (by linarith)

end Schwartz

theorem sa16bd_weighted_cutoff {d : ℕ} (hd : 1 ≤ d) (θ p : ℝ)
    (hθ0 : 0 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p) (ι : Type u) [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : Euc d → ℝ, MemCb 2 μ → (∀ x, 0 ≤ μ x) →
      ∀ W : ι → SchwartzMap (Euc d) ℝ, ∀ ε : ℝ, 0 < ε →
        Integrable (fun x : Euc d => vnorm (fun i => W i x) ^ p) ∧
        Integrable (fun x : Euc d => μ x * vnorm (fun i => W i x) ^ (p - 2) *
          (∑ i, W i x * sa16bd_lapCut d θ ε (fun y => W i y) x)) ∧
        (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
          sa16bd_dissCut d θ p ε (fun y i => W i y) x) < ⊤ ∧
        sa16bd_convexityConst p *
            (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
              sa16bd_dissCut d θ p ε (fun y i => W i y) x).toReal ≤
          (∫ x : Euc d, μ x * vnorm (fun i => W i x) ^ (p - 2) *
            (∑ i, W i x * sa16bd_lapCut d θ ε (fun y => W i y) x)) +
          C * cbNorm 2 μ * (∫ x : Euc d, vnorm (fun i => W i x) ^ p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C0, hC0, hC0b⟩ := sa16bd_lapCut_cb2 hd θ hθ0 hθ2
  refine ⟨C0 / p, div_nonneg hC0 hp0.le, fun μ hμ hμ0 W ε hε => ?_⟩
  set c := sa16bd_convexityConst p with hcdef
  have hc : 0 < c := by simp only [hcdef, sa16bd_convexityConst]; positivity
  obtain ⟨Bw, hBw0, hBw⟩ := sa16bd_schwartz_bound W
  set w : ι → Euc d → ℝ := fun i y => W i y with hw
  have hwc : ∀ i, Continuous (w i) := fun i => (W i).continuous
  have hwb : ∀ i y, |w i y| ≤ Bw := hBw
  have hμc : Continuous μ := by
    have : ContDiff ℝ 2 μ := by simpa using hμ.1
    exact this.continuous
  obtain ⟨Bμ, hBμ⟩ : ∃ B : ℝ, ∀ x, |μ x| ≤ B := by
    obtain ⟨B, hB⟩ := hμ.2 0 (by norm_num)
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB ⟨x, rfl⟩⟩
  have hVc : Continuous (fun y : Euc d => vnorm (fun i => W i y)) :=
    elemb_vnorm_continuous (f := fun i y => W i y) fun i => (W i).continuous
  obtain ⟨hVpc, hVpb⟩ := sa16bd_Vp_bounds hp w hwc hwb
  have hVp_int : Integrable (fun x : Euc d => vnorm (fun i => W i x) ^ p) :=
    sa16bd_Vq_integrable W (by linarith)
  -- the integrand T
  set T : Euc d → ℝ := fun x => μ x * vnorm (fun i => W i x) ^ (p - 2) *
    (∑ i, W i x * sa16bd_lapCut d θ ε (fun y => W i y) x) with hT
  have hTi : Integrable T := by
    set Mℓ : ℝ := (Bw + Bw) * ∫ z, sa16bd_K d θ ε z with hMℓ
    have hg : Integrable (fun x : Euc d =>
        (Bμ * ((Fintype.card ι : ℝ) * Mℓ)) * vnorm (fun i => W i x) ^ (p - 1)) :=
      (sa16bd_Vq_integrable W (by linarith)).const_mul _
    have hmeas : AEStronglyMeasurable T volume := by
      refine (hμc.aestronglyMeasurable.mul
        ((hVc.rpow_const (fun _ => Or.inr (by linarith))).aestronglyMeasurable)).mul ?_
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (W i).continuous.aestronglyMeasurable.mul (sa16bd_lapCut_aesm d θ ε (W i).continuous)
    refine hg.mono' hmeas (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ vnorm (fun i => W i x) := Real.sqrt_nonneg _
    have hMℓ0 : 0 ≤ Mℓ := by
      refine mul_nonneg (by linarith) (integral_nonneg fun z => sa16bd_K_nonneg d θ ε z)
    have hsum : |∑ i, W i x * sa16bd_lapCut d θ ε (fun y => W i y) x| ≤
        (Fintype.card ι : ℝ) * (vnorm (fun i => W i x) * Mℓ) := by
      calc |∑ i, W i x * sa16bd_lapCut d θ ε (fun y => W i y) x|
          ≤ ∑ i, |W i x * sa16bd_lapCut d θ ε (fun y => W i y) x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : ι, vnorm (fun i => W i x) * Mℓ := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul (elemb_abs_le_vnorm (fun i => W i x) i)
              (sa16bd_lapCut_abs_le hd hθ0 hε (W i).continuous (hBw i) x) (abs_nonneg _) h0
        _ = _ := by simp
    rw [Real.norm_eq_abs, hT]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    have e : vnorm (fun i => W i x) ^ (p - 2) * vnorm (fun i => W i x) =
        vnorm (fun i => W i x) ^ (p - 1) := by
      rw [← Real.rpow_add_one' h0 (by linarith)]
      congr 1
      ring
    calc |μ x| * vnorm (fun i => W i x) ^ (p - 2) *
          |∑ i, W i x * sa16bd_lapCut d θ ε (fun y => W i y) x|
        ≤ Bμ * vnorm (fun i => W i x) ^ (p - 2) *
            ((Fintype.card ι : ℝ) * (vnorm (fun i => W i x) * Mℓ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hBμ x) (Real.rpow_nonneg h0 _)) hsum
            (abs_nonneg _) (le_trans (abs_nonneg _) (hBμ x) |> fun h => mul_nonneg h (Real.rpow_nonneg h0 _))
      _ = (Bμ * ((Fintype.card ι : ℝ) * Mℓ)) * vnorm (fun i => W i x) ^ (p - 1) := by
          rw [← e]; ring
  -- duality for V^p
  obtain ⟨hμL, hLμ, hdual⟩ := sa16bd_lapCut_duality hd θ ε hθ0 hε μ
    (fun y => vnorm (fun i => W i y) ^ p) hμ hVpc ⟨_, hVpb⟩ hVp_int
  set G : Euc d → ℝ := fun x => T x - (1 / p) * (μ x * sa16bd_lapCut d θ ε
    (fun y => vnorm (fun i => W i y) ^ p) x) with hG
  have hGi : Integrable G := hTi.sub (hμL.const_mul (1 / p))
  -- pointwise
  have hpt : ∀ x, ENNReal.ofReal c * (ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p ε (fun y i => w i y) x) ≤ ENNReal.ofReal (G x) ∧ 0 ≤ G x := by
    intro x
    have hD := sa16bd_Dint_le hd hθ0 hε hp w hwc hwb x
    have hD0 : 0 ≤ sa16bd_Dint d θ p ε w x :=
      integral_nonneg fun z => mul_nonneg (sa16bd_Dint_integrand_bound hp w hwb x z).1
        (sa16bd_K_nonneg d θ ε z)
    have hμx := hμ0 x
    have hkey : c * (μ x * sa16bd_Dint d θ p ε w x) ≤ G x := by
      have := mul_le_mul_of_nonneg_left hD hμx
      simp only [hG, hT]
      nlinarith [this]
    refine ⟨?_, le_trans (mul_nonneg hc.le (mul_nonneg hμx hD0)) hkey⟩
    rw [sa16bd_dissCut_eq hd hθ0 hε hp w hwc hwb x, ← ENNReal.ofReal_mul hμx,
      ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal hkey
  have hGnn : 0 ≤ᵐ[volume] G := Eventually.of_forall fun x => (hpt x).2
  have hlin : ENNReal.ofReal c * (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p ε (fun y i => W i y) x) ≤ ENNReal.ofReal (∫ x, G x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGi hGnn,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun x => (hpt x).1
  have hfin : (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p ε (fun y i => W i y) x) < ⊤ := by
    by_contra hcon
    have htop : (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
        sa16bd_dissCut d θ p ε (fun y i => W i y) x) = ⊤ := not_lt_top_iff.1 hcon
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne'] at hlin
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hlin)
  refine ⟨hVp_int, hTi, hfin, ?_⟩
  have hGint : 0 ≤ ∫ x, G x := integral_nonneg fun x => (hpt x).2
  have h1 : c * (∫⁻ x : Euc d, ENNReal.ofReal (μ x) *
      sa16bd_dissCut d θ p ε (fun y i => W i y) x).toReal ≤ ∫ x, G x := by
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal hGint] at h2
  refine h1.trans ?_
  have hGeq : ∫ x, G x = (∫ x, T x) - (1 / p) * ∫ x, μ x * sa16bd_lapCut d θ ε
      (fun y => vnorm (fun i => W i y) ^ p) x := by
    simp only [hG]
    rw [integral_sub hTi (hμL.const_mul _), integral_const_mul]
  have hlow : (∫ x : Euc d, vnorm (fun i => W i x) ^ p) * (-(C0 * cbNorm 2 μ)) ≤
      ∫ x : Euc d, vnorm (fun i => W i x) ^ p * sa16bd_lapCut d θ ε μ x := by
    rw [← integral_mul_const]
    refine integral_mono (hVp_int.mul_const _) hLμ fun x => ?_
    have hb := (hC0b μ hμ ε hε x).2
    have hV0 : 0 ≤ vnorm (fun i => W i x) ^ p := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have := abs_le.1 hb
    simp only
    exact mul_le_mul_of_nonneg_left this.1 hV0
  rw [hGeq, hdual]
  have hpinv : 0 < 1 / p := by positivity
  calc (∫ x, T x) - (1 / p) * ∫ x : Euc d, vnorm (fun i => W i x) ^ p * sa16bd_lapCut d θ ε μ x
      ≤ (∫ x, T x) - (1 / p) * ((∫ x : Euc d, vnorm (fun i => W i x) ^ p) * (-(C0 * cbNorm 2 μ))) := by
        have := mul_le_mul_of_nonneg_left hlow hpinv.le
        linarith
    _ = (∫ x, T x) + C0 / p * cbNorm 2 μ * (∫ x : Euc d, vnorm (fun i => W i x) ^ p) := by
        field_simp
        ring

end HRS.Whole.AppendixA.BreakdownSA16

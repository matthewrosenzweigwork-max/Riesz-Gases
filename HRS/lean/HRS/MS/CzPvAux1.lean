import HRS.Whole.AppendixAAdjoint

/-!
# PV-API, part 1: the truncated odd kernel `pvTrunc`, kernel bounds, difference representation

Packet PV-API (CZ development).  Namespace `HRS.CZ.Pv`.  (`HRS/CZ/Defs.lean` does not exist, so the definitions
`pvTrunc`, `pvK` live here.)  The frozen `HRS.Whole.AppendixA.pvOdd` is only read.

* `pvTrunc d θ Ω u ε x = ∫_{ε<|z|} Ω(z/|z|)|z|^{-(d+θ-1)} u(x-z) dz` and `pvOdd_def` (`rfl`).
* `pvK d θ Ω z = Ω(z/|z|)/|z|^{d+θ-1}` is the odd kernel.  `IsPvKernel Ω B` packages the data used about `Ω`:
  measurable, `|Ω| ≤ B` on the unit sphere, odd on the unit sphere (a linear `Ω(u) = u_i`, `isPvKernel_coord`, and a
  smooth odd `Ω`, `isPvKernel_of_oddSmooth`, both qualify).
* `pvTrunc_diff_repr` (difference representation): for `0 < θ < 2` (the packet brief says `1 < θ < 2`; the proof works
  for the whole range `0 < θ < 2`), `u` globally Lipschitz and `x` such that `z ↦ K(z)u(x-z)` is integrable on
  `{|z| > 1}`, and `0 < ε ≤ 1`:
  `pvTrunc ε x = ∫_{ε<|z|≤1} K(z)(u(x-z)-u(x)) dz + ∫_{|z|>1} K(z)u(x-z) dz`.
  The far integrability hypothesis holds for `u ∈ L¹` (`pvK_far_integrable_of_integrable`) and, for `1 < θ < 2`,
  for bounded measurable `u` (`pvK_far_integrable_of_bdd`).
* `pvOdd_eq_of_lip` (the brief's `pvOdd_eq_of_C1`, which is its `C¹` corollary `pvOdd_eq_of_C1` for `u` with bounded
  derivative): the limit exists and `pvOdd d θ Ω u x = ∫_{|z|≤1} K(z)(u(x-z)-u(x)) + ∫_{|z|>1} K(z)u(x-z)`.

Adjustment relative to the sketch: "u bounded `C¹` with `u, Du` integrable decay" is replaced by the weaker pair
"`u` Lipschitz" and "far integrability at `x`", which is what the proofs use.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Pv

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the truncated odd integral `∫_{ε<|z|} Ω(z/|z|)|z|^{-(d+θ-1)} u(x-z) dz` -/
def pvTrunc (d : ℕ) (θ : ℝ) (Ω : EuclideanSpace ℝ (Fin d) → ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z in {z : EuclideanSpace ℝ (Fin d) | ε < ‖z‖}, Ω (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + θ - 1) * u (x - z)

/-- `pvOdd` is the `limUnder` of `pvTrunc` -/
theorem pvOdd_def (d : ℕ) (θ : ℝ) (Ω : EuclideanSpace ℝ (Fin d) → ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    HRS.Whole.AppendixA.pvOdd d θ Ω u x =
      limUnder (𝓝[>] (0 : ℝ)) (fun ε => pvTrunc d θ Ω u ε x) := rfl

/-- the odd kernel `K(z) = Ω(z/|z|)/|z|^{d+θ-1}` -/
def pvK (d : ℕ) (θ : ℝ) (Ω : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Ω (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + θ - 1)

lemma pvTrunc_eq (θ : ℝ) (Ω u : 𝔼 → ℝ) (ε : ℝ) (x : 𝔼) :
    pvTrunc d θ Ω u ε x = ∫ z in {z : 𝔼 | ε < ‖z‖}, pvK d θ Ω z * u (x - z) := rfl

/-- the data on `Ω` used by the calculus: measurable, `|Ω| ≤ B` and odd on the unit sphere -/
structure IsPvKernel (Ω : 𝔼 → ℝ) (B : ℝ) : Prop where
  measurable : Measurable Ω
  nonneg : 0 ≤ B
  bound : ∀ w : 𝔼, ‖w‖ = 1 → |Ω w| ≤ B
  odd : ∀ w : 𝔼, ‖w‖ = 1 → Ω (-w) = -Ω w

/-- a smooth odd `Ω` (`IsOddSmooth`) is bounded on the sphere (`h`) -/
lemma isPvKernel_of_oddSmooth {Ω : 𝔼 → ℝ} (hΩ : HRS.Whole.AppendixA.IsOddSmooth Ω) :
    ∃ B, IsPvKernel Ω B := by
  have hc : Continuous Ω := hΩ.1.continuous
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : 𝔼) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, ⟨hc.measurable, le_max_right _ _, fun w hw => ?_, hΩ.2⟩⟩
  have := hC w (by simpa using hw)
  exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)

/-- the linear `Ω(u) = u_i` -/
lemma isPvKernel_coord (i : Fin d) : IsPvKernel (fun u : 𝔼 => u i) 1 := by
  refine ⟨(EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous.measurable, zero_le_one, fun w hw => ?_, fun w _ => ?_⟩
  · have := PiLp.norm_apply_le w i
    rw [Real.norm_eq_abs] at this
    exact this.trans hw.le
  · simp

lemma pvapi_norm_unit {z : 𝔼} (hz : z ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

lemma pvapi_exp_pos (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) : 0 < (d : ℝ) + θ - 1 := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma pvK_zero (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) (Ω : 𝔼 → ℝ) : pvK d θ Ω 0 = 0 := by
  unfold pvK
  rw [norm_zero, Real.zero_rpow (pvapi_exp_pos hd hθ).ne', div_zero]

/-- `K(-z) = -K(z)` -/
lemma pvK_neg (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B) (z : 𝔼) :
    pvK d θ Ω (-z) = - pvK d θ Ω z := by
  by_cases hz : z = 0
  · subst hz
    simp [pvK_zero hd hθ]
  · unfold pvK
    have h1 : ‖z‖⁻¹ • (-z) = -(‖z‖⁻¹ • z) := smul_neg _ _
    rw [norm_neg, h1, hK.odd _ (pvapi_norm_unit hz), neg_div]

/-- `|K(z)| ≤ B |z|^{1-d-θ}` -/
lemma pvK_abs_le (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B) (z : 𝔼) :
    |pvK d θ Ω z| ≤ B * ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  by_cases hz : z = 0
  · subst hz
    rw [pvK_zero hd hθ, abs_zero]
    exact mul_nonneg hK.nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    unfold pvK
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _)]
    have h1 : 1 - ((d : ℝ) + θ) = -((d : ℝ) + θ - 1) := by ring
    rw [h1, Real.rpow_neg hn.le, ← div_eq_mul_inv]
    gcongr
    exact hK.bound _ (pvapi_norm_unit hz)

lemma pvK_measurable {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B) (θ : ℝ) : Measurable (pvK d θ Ω) := by
  unfold pvK
  exact (hK.measurable.comp (measurable_norm.inv.smul measurable_id)).div (measurable_norm.pow_const _)

/-- `|K(z)| ≤ B` for `|z| ≥ 1` -/
lemma pvK_abs_le_far (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B)
    {z : 𝔼} (hz : 1 ≤ ‖z‖) : |pvK d θ Ω z| ≤ B := by
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine (pvK_abs_le hd hθ hK z).trans ?_
  have : ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
  calc B * ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ B * 1 := by gcongr; exact hK.nonneg
    _ = B := mul_one B

/-! ### integrability -/

lemma pvapi_integrableOn_ball_rpow (hd : 1 ≤ d) {α : ℝ} (hα : α < d) (r : ℝ) :
    IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-α)) (ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun z : 𝔼 => ‖z‖ ^ (-α)) (C := 1)
    (α := α) (r := r) (by rw [finrank_euclideanSpace_fin]; exact hd)
    (by rw [finrank_euclideanSpace_fin]; exact hα) (Eventually.of_forall fun x => ?_)
    (measurable_norm.pow_const _).aestronglyMeasurable
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]

lemma pvapi_integrableOn_tail_rpow (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-s)) {z : 𝔼 | 1 < ‖z‖} := by
  have hS : MeasurableSet {z : 𝔼 | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have h := integrable_one_add_norm (E := 𝔼) (μ := volume) (r := s) (by rw [finrank_euclideanSpace_fin]; exact hs)
  refine Integrable.mono' (h.const_mul ((2 : ℝ) ^ s)).integrableOn
    (measurable_norm.pow_const _).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
  have hz1 : 1 < ‖z‖ := hz
  have hn : 0 < ‖z‖ := by linarith
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  have h1 : (2 * ‖z‖) ^ (-s) ≤ (1 + ‖z‖) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : (2 * ‖z‖) ^ (-s) = (2 : ℝ) ^ (-s) * ‖z‖ ^ (-s) := Real.mul_rpow (by norm_num) hn.le
  have h3 : (2 : ℝ) ^ s * (2 : ℝ) ^ (-s) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h4 : ‖z‖ ^ (-s) = (2 : ℝ) ^ s * ((2 : ℝ) ^ (-s) * ‖z‖ ^ (-s)) := by
    rw [← mul_assoc, h3, one_mul]
  rw [h4, ← h2]
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)

/-- local integrability of `K · h` when `|h(z)| ≤ C |z|` -/
lemma pvK_mul_integrableOn_closedBall (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {h : 𝔼 → ℝ} (hm : AEStronglyMeasurable h volume) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, |h z| ≤ C * ‖z‖) :
    IntegrableOn (fun z => pvK d θ Ω z * h z) (closedBall 0 1) := by
  have hint : IntegrableOn (fun z : 𝔼 => (B * C) * ‖z‖ ^ (-((d : ℝ) + θ - 2))) (closedBall 0 1) := by
    have : IntegrableOn (fun z : 𝔼 => (B * C) * ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
      (pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2).const_mul (B * C)
    exact this.mono_set (closedBall_subset_ball (by norm_num))
  refine Integrable.mono' hint ((pvK_measurable hK θ).aestronglyMeasurable.mul hm).restrict
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hBC : 0 ≤ B * C := mul_nonneg hK.nonneg hC0
  by_cases hz : z = 0
  · subst hz
    rw [pvK_zero hd hθ0, abs_zero, zero_mul]
    exact mul_nonneg hBC (Real.rpow_nonneg (norm_nonneg _) _)
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h1 := pvK_abs_le hd hθ0 hK z
    have h2 : |pvK d θ Ω z| * |h z| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * (C * ‖z‖) :=
      mul_le_mul h1 (hC z) (abs_nonneg _) (mul_nonneg hK.nonneg (Real.rpow_nonneg hn.le _))
    refine h2.trans (le_of_eq ?_)
    have h3 : ‖z‖ ^ (-((d : ℝ) + θ - 2)) = ‖z‖ ^ (1 - ((d : ℝ) + θ)) * ‖z‖ := by
      have : -((d : ℝ) + θ - 2) = (1 - ((d : ℝ) + θ)) + 1 := by ring
      rw [this, Real.rpow_add hn, Real.rpow_one]
    rw [h3]
    ring

/-! ### the generic truncation limit -/

/-- `∫_{ε<|z|} g → ∫ g` as `ε → 0+` for integrable `g` with `g 0 = 0` -/
lemma pvapi_tendsto_trunc {g : 𝔼 → ℝ} (hg : Integrable g) (hg0 : g 0 = 0) :
    Tendsto (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖}, g z) (𝓝[>] 0) (𝓝 (∫ z, g z)) := by
  have hS : ∀ ε : ℝ, MeasurableSet {z : 𝔼 | ε < ‖z‖} := fun ε =>
    measurableSet_lt measurable_const measurable_norm
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε : ℝ => Set.indicator {z : 𝔼 | ε < ‖z‖} g) (f := g) (fun z => ‖g z‖)
    (Eventually.of_forall fun ε => hg.aestronglyMeasurable.indicator (hS ε))
    (Eventually.of_forall fun ε => ae_of_all _ fun z => by
      by_cases hz : z ∈ {z : 𝔼 | ε < ‖z‖}
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]; simp)
    hg.norm
    (ae_of_all _ fun z => by
      by_cases hz : z = 0
      · subst hz
        refine tendsto_const_nhds.congr (fun ε => ?_)
        simp [Set.indicator_apply, hg0]
      · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hn] with ε hε
        rw [Set.indicator_of_mem (show z ∈ {z : 𝔼 | ε < ‖z‖} from hε.2)])
  refine h.congr (fun ε => ?_)
  rw [integral_indicator (hS ε)]

/-! ### difference representation -/

lemma pvapi_lip_bound {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x z : 𝔼) :
    |u (x - z) - u x| ≤ (L : ℝ) * ‖z‖ := by
  have := hu.dist_le_mul (x - z) x
  rw [Real.dist_eq, dist_eq_norm] at this
  simpa using this

/-- `K` is integrable on the annuli `{ε < |z| ≤ 1}` -/
lemma pvK_integrableOn_annulus (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (pvK d θ Ω) ({z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1) := by
  have hfin : volume ({z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1) ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  have hS : MeasurableSet ({z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1) :=
    (measurableSet_lt measurable_const measurable_norm).inter measurableSet_closedBall
  refine Integrable.mono' (integrableOn_const (C := B * ε ^ (1 - ((d : ℝ) + θ))) hfin)
    (pvK_measurable hK θ).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
  have hz' : ε < ‖z‖ := hz.1
  rw [Real.norm_eq_abs]
  refine (pvK_abs_le hd hθ hK z).trans ?_
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ ε ^ (1 - ((d : ℝ) + θ)) :=
    Real.rpow_le_rpow_of_nonpos hε hz'.le (by linarith)
  exact mul_le_mul_of_nonneg_left h2 hK.nonneg

/-- far integrability for `u ∈ L¹` -/
lemma pvK_far_integrable_of_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} (hu : Integrable u) (x : 𝔼) :
    IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖} := by
  have hS : MeasurableSet {z : 𝔼 | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  refine Integrable.mono' ((hu.comp_sub_left x).norm.const_mul B).integrableOn
    (((pvK_measurable hK θ).aestronglyMeasurable.mul (hu.comp_sub_left x).aestronglyMeasurable).restrict)
    ((ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_))
  have hz' : 1 < ‖z‖ := hz
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (pvK_abs_le_far hd hθ hK hz'.le) (norm_nonneg _)

/-- far integrability for bounded measurable `u`, `1 < θ` -/
lemma pvK_far_integrable_of_bdd (hd : 1 ≤ d) {θ : ℝ} (hθ : 1 < θ) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} (hm : AEStronglyMeasurable u volume) {M : ℝ}
    (hM : ∀ y, |u y| ≤ M) (x : 𝔼) :
    IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖} := by
  have hS : MeasurableSet {z : 𝔼 | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hθ0 : 0 < θ := by linarith
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have htail : IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 1))) {z : 𝔼 | 1 < ‖z‖} :=
    pvapi_integrableOn_tail_rpow hd (by linarith)
  have hmx : AEStronglyMeasurable (fun z : 𝔼 => u (x - z)) volume :=
    hm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  have htail' : IntegrableOn (fun z : 𝔼 => (B * M) * ‖z‖ ^ (-((d : ℝ) + θ - 1))) {z : 𝔼 | 1 < ‖z‖} :=
    htail.const_mul (B * M)
  refine Integrable.mono' htail' (((pvK_measurable hK θ).aestronglyMeasurable.mul hmx).restrict)
    ((ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_))
  have hz' : 1 < ‖z‖ := hz
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hK1 := pvK_abs_le hd hθ0 hK z
  have h2 : 1 - ((d : ℝ) + θ) = -((d : ℝ) + θ - 1) := by ring
  rw [h2] at hK1
  calc |pvK d θ Ω z| * |u (x - z)| ≤ (B * ‖z‖ ^ (-((d : ℝ) + θ - 1))) * M :=
        mul_le_mul hK1 (hM _) (abs_nonneg _) (mul_nonneg hK.nonneg (Real.rpow_nonneg (norm_nonneg _) _))
    _ = (B * M) * ‖z‖ ^ (-((d : ℝ) + θ - 1)) := by ring

/-- (a) the difference representation of the truncations -/
theorem pvTrunc_diff_repr (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : 𝔼)
    (hfar : IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    pvTrunc d θ Ω u ε x =
      (∫ z in {z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1, pvK d θ Ω z * (u (x - z) - u x)) +
        ∫ z in {z : 𝔼 | 1 < ‖z‖}, pvK d θ Ω z * u (x - z) := by
  set A : Set 𝔼 := {z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1 with hA
  set T : Set 𝔼 := {z : 𝔼 | 1 < ‖z‖} with hT
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_norm).inter measurableSet_closedBall
  have hTm : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
  have hdiff_cont : Continuous (fun z : 𝔼 => u (x - z) - u x) :=
    (hu.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hloc := pvK_mul_integrableOn_closedBall hd hθ0 hθ2 hK (h := fun z => u (x - z) - u x)
    hdiff_cont.aestronglyMeasurable L.2 (pvapi_lip_bound hu x)
  have hKA : IntegrableOn (pvK d θ Ω) A := pvK_integrableOn_annulus hd hθ0 hK hε
  have hlocA : IntegrableOn (fun z => pvK d θ Ω z * (u (x - z) - u x)) A :=
    hloc.mono_set inter_subset_right
  have hfA : IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) A := by
    have h := hlocA.add (hKA.const_mul (u x))
    refine h.congr_fun (fun z _ => ?_) hAm
    simp only [Pi.add_apply]
    ring
  have hsplit : {z : 𝔼 | ε < ‖z‖} = A ∪ T := by
    ext z
    simp only [hA, hT, Set.mem_ofPred_eq, mem_union, mem_inter_iff, mem_closedBall, dist_zero_right]
    constructor
    · intro h
      by_cases h1 : ‖z‖ ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_le.1 h1)
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  have hdisj : Disjoint A T := by
    rw [Set.disjoint_left]
    intro z hzA hzT
    have h1 : ‖z‖ ≤ 1 := by simpa using hzA.2
    have h2 : 1 < ‖z‖ := hzT
    linarith
  have hAneg : ∀ z, -z ∈ A ↔ z ∈ A := fun z => by simp [hA, norm_neg]
  have hodd : ∫ z in A, pvK d θ Ω z = 0 := by
    rw [← integral_indicator hAm]
    have key := integral_neg_eq_self (fun z => A.indicator (pvK d θ Ω) z) volume
    have h2 : ∫ z, A.indicator (pvK d θ Ω) (-z) = - ∫ z, A.indicator (pvK d θ Ω) z := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show A.indicator (pvK d θ Ω) (-z) = -A.indicator (pvK d θ Ω) z
      by_cases hz : z ∈ A
      · rw [indicator_of_mem ((hAneg z).2 hz), indicator_of_mem hz, pvK_neg hd hθ0 hK]
      · rw [indicator_of_notMem (mt (hAneg z).1 hz), indicator_of_notMem hz]
        simp
    linarith
  rw [pvTrunc_eq, hsplit, setIntegral_union hdisj hTm hfA hfar]
  congr 1
  have hpt : ∀ z, pvK d θ Ω z * u (x - z) =
      pvK d θ Ω z * (u (x - z) - u x) + u x * pvK d θ Ω z := fun z => by ring
  simp_rw [hpt]
  rw [integral_add hlocA (hKA.const_mul (u x)), integral_const_mul, hodd, mul_zero, add_zero]

/-- (b) the truncations converge as `ε → 0+` -/
theorem pvTrunc_tendsto (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : 𝔼)
    (hfar : IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖}) :
    Tendsto (fun ε : ℝ => pvTrunc d θ Ω u ε x) (𝓝[>] 0)
      (𝓝 ((∫ z in closedBall (0 : 𝔼) 1, pvK d θ Ω z * (u (x - z) - u x)) +
        ∫ z in {z : 𝔼 | 1 < ‖z‖}, pvK d θ Ω z * u (x - z))) := by
  have hdiff_cont : Continuous (fun z : 𝔼 => u (x - z) - u x) :=
    (hu.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hloc := pvK_mul_integrableOn_closedBall hd hθ0 hθ2 hK (h := fun z => u (x - z) - u x)
    hdiff_cont.aestronglyMeasurable L.2 (pvapi_lip_bound hu x)
  set g : 𝔼 → ℝ := fun z => pvK d θ Ω z * (u (x - z) - u x) with hg
  have hGi : Integrable ((closedBall (0 : 𝔼) 1).indicator g) :=
    (integrable_indicator_iff measurableSet_closedBall).2 hloc
  have hG0 : (closedBall (0 : 𝔼) 1).indicator g 0 = 0 := by
    rw [indicator_of_mem (by simp)]
    simp [hg, pvK_zero hd hθ0]
  have h := (pvapi_tendsto_trunc hGi hG0).add_const (∫ z in {z : 𝔼 | 1 < ‖z‖}, pvK d θ Ω z * u (x - z))
  rw [integral_indicator measurableSet_closedBall] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
  rw [pvTrunc_diff_repr hd hθ0 hθ2 hK hu x hfar hε.1 hε.2.le]
  congr 1
  rw [setIntegral_indicator measurableSet_closedBall]

/-- (b) `pvOdd_eq_of_C1`, Lipschitz form: the limit exists and `pvOdd` is the absolutely convergent
`∫_{|z|≤1} K(z)(u(x-z)-u(x)) dz + ∫_{|z|>1} K(z)u(x-z) dz` -/
theorem pvOdd_eq_of_lip (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : 𝔼)
    (hfar : IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖}) :
    HRS.Whole.AppendixA.pvOdd d θ Ω u x =
      (∫ z in closedBall (0 : 𝔼) 1, pvK d θ Ω z * (u (x - z) - u x)) +
        ∫ z in {z : 𝔼 | 1 < ‖z‖}, pvK d θ Ω z * u (x - z) := by
  rw [pvOdd_def]
  exact (pvTrunc_tendsto hd hθ0 hθ2 hK hu x hfar).limUnder_eq

end HRS.CZ.Pv

import HRS.MS.CzPvAux2

/-!
# PV-API, part 3: pointwise domination, `θ < 1`, measurability, commutator kernel

Packet PV-API (CZ development), namespace `HRS.CZ.Pv`.  Uses `pvK`, `IsPvKernel` of `CzPvAux1`.

* `pvOdd_eq_of_C1`: the `C¹` corollary of `pvOdd_eq_of_lip` (`u ∈ C¹` with bounded derivative).
* `pvOdd_abs_le_loc_far` (c): for Lipschitz `u` and `0 < θ < 2`, with `e = 1-(d+θ)`,
  `ofReal |pvOdd u x| ≤ B ∫⁻_{|z|≤1} |z|^e |u(x-z)-u(x)| + B ∫⁻_{|z|>1} |z|^e |u(x-z)|`
  (in `ℝ≥0∞`, no integrability hypothesis; `B` the bound of `Ω` on the sphere).
* `pvOdd_eq_of_integrable` and `pvOdd_abs_le_riesz` (d): for `0 < θ` and `u` a.e. strongly measurable,
  `ofReal |pvOdd u x| ≤ ofReal B * ∫⁻ ofReal (|z|^{1-θ-d} |u(x-z)|)` (the Riesz potential bound of order `1-θ`;
  `ℝ≥0∞`-valued so that the Bochner-integral junk value `0` of a non-integrable function cannot enter) and, when
  `K(z)u(x-z)` is integrable, `pvOdd u x = ∫ K(z)u(x-z) dz`.
* `pvOdd_measurable_of_lip`, `pvOdd_aesm` (g): `pvOdd d θ Ω W` is measurable for Schwartz `W`
  (via measurability of the truncations in `x`, Fubini, and the convergence along `ε = 1/(n+1)`).
* `pvOdd_comm_kernel`: the commutator kernel representation used by ELEM-A (ii-a):
  for `a`, `W` bounded Lipschitz with `W ∈ L¹`, the function `K(z)(a(x-z)-a(x))W(x-z)` is integrable and
  `pvOdd(aW)(x) - a(x) pvOdd W(x) = ∫ K(z)(a(x-z)-a(x))W(x-z) dz`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Pv

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma PvC2.lipschitzWith {f : 𝔼 → ℝ} {B L M : ℝ} (hf : PvC2 f B L M) :
    LipschitzWith ⟨L, hf.L_nonneg⟩ f :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, dist_eq_norm]
    exact hf.lip a b

lemma pvapi_ball_union_tail : closedBall (0 : 𝔼) 1 ∪ {z : 𝔼 | 1 < ‖z‖} = univ := by
  ext z
  simp only [mem_univ, mem_union, mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, iff_true]
  by_cases h : ‖z‖ ≤ 1
  · exact Or.inl h
  · exact Or.inr (not_le.1 h)

lemma pvapi_ball_tail_disjoint : Disjoint (closedBall (0 : 𝔼) 1) {z : 𝔼 | 1 < ‖z‖} := by
  rw [Set.disjoint_left]
  intro z h1 h2
  have : ‖z‖ ≤ 1 := by simpa using h1
  have h3 : 1 < ‖z‖ := h2
  linarith

lemma pvapi_tail_meas : MeasurableSet {z : 𝔼 | 1 < ‖z‖} :=
  measurableSet_lt measurable_const measurable_norm

/-- local integrability of `K(z)(u(x-z)-u(x))` for Lipschitz `u` -/
lemma pvapi_loc_lip (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : 𝔼) :
    IntegrableOn (fun z => pvK d θ Ω z * (u (x - z) - u x)) (closedBall 0 1) :=
  pvK_mul_integrableOn_closedBall hd hθ0 hθ2 hK (h := fun z => u (x - z) - u x)
    ((hu.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).aestronglyMeasurable
    L.2 (pvapi_lip_bound hu x)

/-! ### the `C¹` form -/

/-- (b) `pvOdd_eq_of_C1`: `u ∈ C¹` with `‖Du‖ ≤ L`; far integrability as in `pvOdd_eq_of_lip` -/
theorem pvOdd_eq_of_C1 (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) {L : ℝ≥0}
    (hL : ∀ y, ‖fderiv ℝ u y‖₊ ≤ L) (x : 𝔼)
    (hfar : IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖}) :
    HRS.Whole.AppendixA.pvOdd d θ Ω u x =
      (∫ z in closedBall (0 : 𝔼) 1, pvK d θ Ω z * (u (x - z) - u x)) +
        ∫ z in {z : 𝔼 | 1 < ‖z‖}, pvK d θ Ω z * u (x - z) :=
  pvOdd_eq_of_lip hd hθ0 hθ2 hK (lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable one_ne_zero) hL)
    x hfar

/-! ### (c) pointwise domination -/

lemma pvapi_enorm_le {a b : ℝ} (h : |a| ≤ b) : ‖a‖ₑ ≤ ENNReal.ofReal b := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

lemma pvapi_ofReal_B_mul (S : Set 𝔼) {B : ℝ} (hB : 0 ≤ B) (w : 𝔼 → ℝ) :
    ∫⁻ z in S, ENNReal.ofReal (B * w z) = ENNReal.ofReal B * ∫⁻ z in S, ENNReal.ofReal (w z) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  rw [ENNReal.ofReal_mul hB]

/-- (c) pointwise domination of `pvOdd` for Lipschitz `u` -/
theorem pvOdd_abs_le_loc_far (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : 𝔼) :
    ENNReal.ofReal |HRS.Whole.AppendixA.pvOdd d θ Ω u x| ≤
      ENNReal.ofReal B * (∫⁻ z in closedBall (0 : 𝔼) 1,
          ENNReal.ofReal (‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z) - u x|)) +
        ENNReal.ofReal B * (∫⁻ z in {z : 𝔼 | 1 < ‖z‖},
          ENNReal.ofReal (‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z)|)) := by
  rw [← pvapi_ofReal_B_mul _ hK.nonneg (fun z => ‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z) - u x|),
    ← pvapi_ofReal_B_mul _ hK.nonneg (fun z => ‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z)|)]
  have hTm := pvapi_tail_meas (d := d)
  by_cases hTop : ∫⁻ z in {z : 𝔼 | 1 < ‖z‖},
      ENNReal.ofReal (B * (‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z)|)) = ⊤
  · rw [hTop]
    exact le_of_le_of_eq le_top (by simp)
  · have hmx : AEStronglyMeasurable (fun z : 𝔼 => u (x - z)) volume :=
      (hu.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have hint : Integrable (fun z : 𝔼 => B * (‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z)|))
        (volume.restrict {z : 𝔼 | 1 < ‖z‖}) := by
      refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).1 hTop
      · exact (aestronglyMeasurable_const.mul
          (((measurable_norm.pow_const _).aestronglyMeasurable).mul hmx.norm)).restrict
      · exact ae_of_all _ fun z => mul_nonneg hK.nonneg
          (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (abs_nonneg _))
    have hfar : IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖} := by
      refine Integrable.mono' hint ?_ ?_
      · exact ((pvK_measurable hK θ).aestronglyMeasurable.mul hmx).restrict
      · refine (ae_restrict_iff' hTm).2 (ae_of_all _ fun z hz => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        calc |pvK d θ Ω z| * |u (x - z)| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * |u (x - z)| :=
              mul_le_mul_of_nonneg_right (pvK_abs_le hd hθ0 hK z) (abs_nonneg _)
          _ = _ := by ring
    have hloc := pvapi_loc_lip hd hθ0 hθ2 hK hu x
    rw [pvOdd_eq_of_lip hd hθ0 hθ2 hK hu x hfar, ← Real.enorm_eq_ofReal_abs]
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
      refine pvapi_enorm_le ?_
      rw [abs_mul]
      calc |pvK d θ Ω z| * |u (x - z) - u x| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * |u (x - z) - u x| :=
            mul_le_mul_of_nonneg_right (pvK_abs_le hd hθ0 hK z) (abs_nonneg _)
        _ = _ := by ring
    · refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
      refine pvapi_enorm_le ?_
      rw [abs_mul]
      calc |pvK d θ Ω z| * |u (x - z)| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * |u (x - z)| :=
            mul_le_mul_of_nonneg_right (pvK_abs_le hd hθ0 hK z) (abs_nonneg _)
        _ = _ := by ring

/-! ### (d) the absolutely convergent case -/

/-- if `K(z)u(x-z)` is integrable on `ℝ^d` then `pvOdd` is that integral -/
theorem pvOdd_eq_of_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) {Ω : 𝔼 → ℝ} (u : 𝔼 → ℝ) (x : 𝔼)
    (hint : Integrable (fun z => pvK d θ Ω z * u (x - z))) :
    HRS.Whole.AppendixA.pvOdd d θ Ω u x = ∫ z, pvK d θ Ω z * u (x - z) := by
  rw [pvOdd_def]
  exact (pvapi_tendsto_trunc hint (by simp [pvK_zero hd hθ0])).limUnder_eq

/-- (d) the Riesz potential bound `|pvOdd u x| ≤ B ∫ |z|^{1-θ-d} |u(x-z)| dz`, in `ℝ≥0∞`, valid for every
`u` (if the right side is `∞` there is nothing to prove, otherwise the integral converges absolutely) -/
theorem pvOdd_abs_le_riesz (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} (hm : AEStronglyMeasurable u volume) (x : 𝔼) :
    ENNReal.ofReal |HRS.Whole.AppendixA.pvOdd d θ Ω u x| ≤
      ENNReal.ofReal B * ∫⁻ z : 𝔼, ENNReal.ofReal (‖z‖ ^ (1 - θ - (d : ℝ)) * |u (x - z)|) := by
  have he : ∀ z : 𝔼, ‖z‖ ^ (1 - θ - (d : ℝ)) = ‖z‖ ^ (1 - ((d : ℝ) + θ)) := fun z => by
    congr 1; ring
  simp_rw [he]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmx : AEStronglyMeasurable (fun z : 𝔼 => u (x - z)) volume :=
    hm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  have hpt : ∀ z : 𝔼, ‖pvK d θ Ω z * u (x - z)‖ₑ ≤
      ENNReal.ofReal B * ENNReal.ofReal (‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z)|) := fun z => by
    rw [← ENNReal.ofReal_mul hK.nonneg]
    refine pvapi_enorm_le ?_
    rw [abs_mul]
    calc |pvK d θ Ω z| * |u (x - z)| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * |u (x - z)| :=
          mul_le_mul_of_nonneg_right (pvK_abs_le hd hθ0 hK z) (abs_nonneg _)
      _ = _ := by ring
  by_cases hTop : ∫⁻ z : 𝔼, ENNReal.ofReal B * ENNReal.ofReal (‖z‖ ^ (1 - ((d : ℝ) + θ)) * |u (x - z)|) = ⊤
  · rw [hTop]; exact le_top
  · have hgm : AEStronglyMeasurable (fun z : 𝔼 => pvK d θ Ω z * u (x - z)) volume :=
      (pvK_measurable hK θ).aestronglyMeasurable.mul hmx
    have hint : Integrable (fun z : 𝔼 => pvK d θ Ω z * u (x - z)) :=
      ⟨hgm, (lintegral_mono hpt).trans_lt (lt_top_iff_ne_top.2 hTop)⟩
    rw [pvOdd_eq_of_integrable hd hθ0 u x hint, ← Real.enorm_eq_ofReal_abs]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono hpt)

/-! ### (g) measurability -/

lemma pvTrunc_measurable {θ : ℝ} {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ}
    (hu : Continuous u) (ε : ℝ) : Measurable (fun x : 𝔼 => pvTrunc d θ Ω u ε x) := by
  have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hF : Measurable (fun p : 𝔼 × 𝔼 => if ε < ‖p.2‖ then pvK d θ Ω p.2 * u (p.1 - p.2) else 0) := by
    refine Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp measurable_snd)) ?_
      measurable_const
    exact ((pvK_measurable hK θ).comp measurable_snd).mul
      (hu.measurable.comp (measurable_fst.sub measurable_snd))
  have h := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun x : 𝔼 => pvTrunc d θ Ω u ε x) =
      fun x : 𝔼 => ∫ z, (if ε < ‖z‖ then pvK d θ Ω z * u (x - z) else 0) := by
    funext x
    rw [pvTrunc_eq, ← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [Set.indicator_apply]
  rw [heq]
  exact h

/-- (g) measurability of `pvOdd` for Lipschitz `u` with far integrability at every point -/
theorem pvOdd_measurable_of_lip (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hfar : ∀ x, IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | 1 < ‖z‖}) :
    Measurable (HRS.Whole.AppendixA.pvOdd d θ Ω u) := by
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [Set.mem_Ioi]; positivity⟩
  refine measurable_of_tendsto_metrizable (f := fun n x => pvTrunc d θ Ω u (1 / ((n : ℝ) + 1)) x)
    (fun n => pvTrunc_measurable hK hu.continuous _) (tendsto_pi_nhds.2 fun x => ?_)
  have hlim := pvTrunc_tendsto hd hθ0 hθ2 hK hu x (hfar x)
  have hv := pvOdd_eq_of_lip hd hθ0 hθ2 hK hu x (hfar x)
  rw [hv]
  exact hlim.comp hseq

/-- (g) `AEStronglyMeasurable (pvOdd d θ Ω W)` for Schwartz `W` -/
theorem pvOdd_aesm (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) (W : 𝓢(𝔼, ℝ)) :
    AEStronglyMeasurable (HRS.Whole.AppendixA.pvOdd d θ Ω W) volume := by
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_schwartz W
  exact (pvOdd_measurable_of_lip hd hθ0 hθ2 hK h1.lipschitzWith
    (fun x => pvK_far_integrable_of_integrable hd hθ0 hK W.integrable x)).aestronglyMeasurable

/-! ### the commutator kernel -/

lemma pvapi_lipschitz_mul {f g : 𝔼 → ℝ} {Lf Lg : ℝ≥0} {Bf Bg : ℝ} (hf : LipschitzWith Lf f)
    (hg : LipschitzWith Lg g) (hfb : ∀ y, |f y| ≤ Bf) (hgb : ∀ y, |g y| ≤ Bg) :
    LipschitzWith ⟨Bf * Lg + Bg * Lf, add_nonneg (mul_nonneg ((abs_nonneg _).trans (hfb 0)) Lg.coe_nonneg)
      (mul_nonneg ((abs_nonneg _).trans (hgb 0)) Lf.coe_nonneg)⟩ (fun y => f y * g y) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have h1 := hf.dist_le_mul a b
  have h2 := hg.dist_le_mul a b
  rw [Real.dist_eq] at h1 h2 ⊢
  have h3 : f a * g a - f b * g b = f a * (g a - g b) + g b * (f a - f b) := by ring
  rw [h3]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have e1 : |f a| * |g a - g b| ≤ Bf * (Lg * dist a b) :=
    mul_le_mul (hfb a) h2 (abs_nonneg _) ((abs_nonneg _).trans (hfb 0))
  have e2 : |g b| * |f a - f b| ≤ Bg * (Lf * dist a b) :=
    mul_le_mul (hgb b) h1 (abs_nonneg _) ((abs_nonneg _).trans (hgb 0))
  show _ ≤ (Bf * Lg + Bg * Lf) * dist a b
  nlinarith [e1, e2]

/-- the commutator kernel representation (ELEM-A (ii-a)): `pvOdd(aW) - a pvOdd W` is the absolutely convergent
integral of `K(z)(a(x-z)-a(x))W(x-z)` -/
theorem pvOdd_comm_kernel (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {a W : 𝔼 → ℝ} {La LW : ℝ≥0} {Ba BW : ℝ} (ha : LipschitzWith La a)
    (hab : ∀ y, |a y| ≤ Ba) (hW : LipschitzWith LW W) (hWi : Integrable W) (hWb : ∀ y, |W y| ≤ BW)
    (x : 𝔼) :
    Integrable (fun z => pvK d θ Ω z * ((a (x - z) - a x) * W (x - z))) ∧
    HRS.Whole.AppendixA.pvOdd d θ Ω (fun y => a y * W y) x - a x * HRS.Whole.AppendixA.pvOdd d θ Ω W x =
      ∫ z, pvK d θ Ω z * ((a (x - z) - a x) * W (x - z)) := by
  have hBa : 0 ≤ Ba := (abs_nonneg _).trans (hab 0)
  have hBW : 0 ≤ BW := (abs_nonneg _).trans (hWb 0)
  have haW := pvapi_lipschitz_mul ha hW hab hWb
  have hmx : AEStronglyMeasurable (fun z : 𝔼 => W (x - z)) volume :=
    (hW.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have haWi : Integrable (fun y => a y * W y) := by
    refine Integrable.mono' (hWi.norm.const_mul Ba)
      ((ha.continuous.aestronglyMeasurable).mul hWi.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hab y) (abs_nonneg _)
  have fa := pvK_far_integrable_of_integrable hd hθ0 hK haWi x
  have fW := pvK_far_integrable_of_integrable hd hθ0 hK hWi x
  have la := pvapi_loc_lip hd hθ0 hθ2 hK haW x
  have lW := pvapi_loc_lip hd hθ0 hθ2 hK hW x
  -- the combined function
  set F : 𝔼 → ℝ := fun z => pvK d θ Ω z * ((a (x - z) - a x) * W (x - z)) with hF
  have hFloc : IntegrableOn F (closedBall 0 1) := by
    refine pvK_mul_integrableOn_closedBall hd hθ0 hθ2 hK (h := fun z => (a (x - z) - a x) * W (x - z))
      ((((ha.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).mul
        (hW.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (C := La * BW) (mul_nonneg La.2 hBW) (fun z => ?_)
    rw [abs_mul]
    calc |a (x - z) - a x| * |W (x - z)| ≤ (La * ‖z‖) * BW :=
          mul_le_mul (by simpa using pvapi_lip_bound ha x z) (hWb _) (abs_nonneg _)
            (mul_nonneg La.2 (norm_nonneg _))
      _ = _ := by ring
  have hFfar : IntegrableOn F {z : 𝔼 | 1 < ‖z‖} := by
    have hdom : IntegrableOn (fun z : 𝔼 => (2 * Ba) * (B * |W (x - z)|)) {z : 𝔼 | 1 < ‖z‖} :=
      ((hWi.comp_sub_left x).norm.const_mul B |>.const_mul (2 * Ba)).integrableOn
    refine Integrable.mono' hdom ?_ ?_
    · exact ((pvK_measurable hK θ).aestronglyMeasurable.mul
        ((((ha.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).mul
          (hW.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)).restrict
    · refine (ae_restrict_iff' pvapi_tail_meas).2 (ae_of_all _ fun z hz => ?_)
      have hz' : 1 < ‖z‖ := hz
      rw [hF, Real.norm_eq_abs]
      simp only
      rw [abs_mul, abs_mul]
      have hK1 := pvK_abs_le_far hd hθ0 hK hz'.le
      have hd1 : |a (x - z) - a x| ≤ 2 * Ba := by
        have := hab (x - z)
        have := hab x
        calc |a (x - z) - a x| ≤ |a (x - z)| + |a x| := abs_sub _ _
          _ ≤ 2 * Ba := by linarith
      calc |pvK d θ Ω z| * (|a (x - z) - a x| * |W (x - z)|) ≤ B * ((2 * Ba) * |W (x - z)|) :=
            mul_le_mul hK1 (mul_le_mul_of_nonneg_right hd1 (abs_nonneg _)) (by positivity) hK.nonneg
        _ = _ := by ring
  have hFint : Integrable F := by
    rw [← integrableOn_univ, ← pvapi_ball_union_tail]
    exact hFloc.union hFfar
  refine ⟨hFint, ?_⟩
  rw [pvOdd_eq_of_lip hd hθ0 hθ2 hK haW x fa, pvOdd_eq_of_lip hd hθ0 hθ2 hK hW x fW,
    mul_add, ← integral_const_mul, ← integral_const_mul]
  have hsplit := setIntegral_union (f := F) pvapi_ball_tail_disjoint pvapi_tail_meas hFloc hFfar
  rw [pvapi_ball_union_tail, setIntegral_univ] at hsplit
  rw [hsplit]
  have e : ∀ (p q r s : ℝ), p + q - (r + s) = (p - r) + (q - s) := fun p q r s => by ring
  rw [e, ← integral_sub la (lW.const_mul (a x)), ← integral_sub fa (fW.const_mul (a x))]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF]
    ring
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF]
    ring

end HRS.CZ.Pv

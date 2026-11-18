import HRS.MS.CzPvAux1
import HRS.Prob.Metrics

/-!
# PV-API, part 2: `fracLap` and `lamComm` calculus (second-difference form, kernel identity)

Packet PV-API (CZ development), namespace `HRS.CZ.Pv`.  Frozen definitions read only:
`HRS.Whole.AppendixA.fracLap`, `lamComm`.

`PvC2 f Bf L M` records what is used about a function `f` on `ℝ^d`: continuous, `|f| ≤ Bf`, Lipschitz with constant
`L`, and the second difference bound `|f(x+z)+f(x-z)-2f(x)| ≤ M|z|²` (this follows from `C²` with bounded second
derivative).  It is available for Schwartz functions (`PvC2.of_schwartz`), for `C_b²` functions (`PvC2.of_memCb`) and
is stable under products (`PvC2.mul`).

For `0 < θ < 2` and `PvC2 f ..`:

* `fracLap_tendsto`: the truncations `∫_{ε<|z|} (f(x)-f(x-z))/|z|^{d+θ}` converge as `ε → 0+` to the absolutely
  convergent `∫ (2f(x)-f(x-z)-f(x+z))/2/|z|^{d+θ}`; `fracLap_eq_symm` (the frozen `fracLap` is that integral) and
  `fracLap_split` (the `|z| ≤ 1` / `|z| > 1` splitting: `fracLap f x = ∫_{|z|≤1} symmetrised + ∫_{|z|>1}
  (f(x)-f(x-z))/|z|^{d+θ}`, the brief's `fracLap_eq_diff`).
* `lamComm_kernel` (e): for `μ ∈ C_b²`, `W` Schwartz, `0 < θ < 2`,
  `lamComm d θ μ W x = limUnder (𝓝[>] 0) (ε ↦ ∫_{ε<|z|} (μ(x) - μ(x-z)) W(x-z)/|z|^{d+θ})` (both `fracLap` limits
  exist and subtract; the limit exists, `lamComm_kernel_tendsto`).  `lamComm_kernel_of` is the same for abstract
  `PvC2` data and `lamComm_split` gives the `|z| ≤ 1` / `|z| > 1` splitting.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Pv

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### second differences -/

/-- the function data used by the `fracLap`/`lamComm` calculus -/
structure PvC2 (f : 𝔼 → ℝ) (Bf L M : ℝ) : Prop where
  cont : Continuous f
  Bf_nonneg : 0 ≤ Bf
  L_nonneg : 0 ≤ L
  M_nonneg : 0 ≤ M
  bdd : ∀ y, |f y| ≤ Bf
  lip : ∀ a b, |f a - f b| ≤ L * ‖a - b‖
  second : ∀ x z, |f (x + z) + f (x - z) - 2 * f x| ≤ M * ‖z‖ ^ 2

lemma pvapi_lip_of_fderiv {f : 𝔼 → ℝ} (hf : Differentiable ℝ f) {L : ℝ} (hL : ∀ y, ‖fderiv ℝ f y‖ ≤ L)
    (a b : 𝔼) : |f a - f b| ≤ L * ‖a - b‖ := by
  have := (convex_univ : Convex ℝ (Set.univ : Set 𝔼)).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (fun x _ => hf x) (fun x _ => hL x) (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

lemma pvapi_fderiv_fderiv_norm (f : 𝔼 → ℝ) (y : 𝔼) :
    ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- second difference bound from a bound on the second derivative -/
lemma pvapi_second_diff {f : 𝔼 → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M) (x z : 𝔼) :
    |f (x + z) + f (x - z) - 2 * f x| ≤ M * ‖z‖ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hddf : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable (by norm_num)
  have hlipD : ∀ a b : 𝔼, ‖fderiv ℝ f a - fderiv ℝ f b‖ ≤ M * ‖a - b‖ := by
    intro a b
    have := (convex_univ : Convex ℝ (Set.univ : Set 𝔼)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ f) (fun x _ => hddf x)
      (fun x _ => by rw [pvapi_fderiv_fderiv_norm]; exact hM x) (mem_univ b) (mem_univ a)
    exact this
  -- one-variable function
  set φ : ℝ → ℝ := fun t => f (x + t • z) + f (x - t • z) - 2 * f x with hφ
  have hd1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • z) z t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have hd2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x - t • z) (-z) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const z).const_sub x
  have hφd : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ f (x + t • z) z - fderiv ℝ f (x - t • z) (z)) t := by
    intro t
    have h1 := (hdf (x + t • z)).hasFDerivAt.comp_hasDerivAt t (hd1 t)
    have h2 := (hdf (x - t • z)).hasFDerivAt.comp_hasDerivAt t (hd2 t)
    have h3 := (h1.add h2).sub_const (2 * f x)
    simpa [hφ, sub_eq_add_neg] using h3
  have hBd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => M * ‖z‖ ^ 2 * t ^ 2) (2 * M * ‖z‖ ^ 2 * t) t := by
    intro t
    have := (hasDerivAt_pow 2 t).const_mul (M * ‖z‖ ^ 2)
    convert this using 1
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := φ) (f' := fun t => fderiv ℝ f (x + t • z) z - fderiv ℝ f (x - t • z) z) (a := 0) (b := 1)
    (B := fun t : ℝ => M * ‖z‖ ^ 2 * t ^ 2) (B' := fun t => 2 * M * ‖z‖ ^ 2 * t)
    (fun t _ => (hφd t).continuousAt.continuousWithinAt)
    (fun t _ => (hφd t).hasDerivWithinAt)
    (by simp [hφ]; ring) hBd
    (fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      have h1 : ‖fderiv ℝ f (x + t • z) z - fderiv ℝ f (x - t • z) z‖ ≤
          ‖fderiv ℝ f (x + t • z) - fderiv ℝ f (x - t • z)‖ * ‖z‖ := by
        rw [← sub_apply]
        exact ContinuousLinearMap.le_opNorm _ _
      have h2 := hlipD (x + t • z) (x - t • z)
      have h3 : ‖(x + t • z) - (x - t • z)‖ = 2 * t * ‖z‖ := by
        have : (x + t • z) - (x - t • z) = (2 * t) • z := by
          rw [mul_smul, two_smul]; abel
        rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
      rw [h3] at h2
      calc _ ≤ ‖fderiv ℝ f (x + t • z) - fderiv ℝ f (x - t • z)‖ * ‖z‖ := h1
        _ ≤ (M * (2 * t * ‖z‖)) * ‖z‖ := by gcongr
        _ = 2 * M * ‖z‖ ^ 2 * t := by ring)
  have := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simpa [hφ, Real.norm_eq_abs] using this

/-! ### products and constructors -/

lemma PvC2.mul {f g : 𝔼 → ℝ} {Bf Lf Mf Bg Lg Mg : ℝ} (hf : PvC2 f Bf Lf Mf) (hg : PvC2 g Bg Lg Mg) :
    PvC2 (fun y => f y * g y) (Bf * Bg) (Bf * Lg + Bg * Lf) (Bf * Mg + Bg * Mf + 2 * (Lf * Lg)) where
  cont := hf.cont.mul hg.cont
  Bf_nonneg := mul_nonneg hf.Bf_nonneg hg.Bf_nonneg
  L_nonneg := add_nonneg (mul_nonneg hf.Bf_nonneg hg.L_nonneg) (mul_nonneg hg.Bf_nonneg hf.L_nonneg)
  M_nonneg := add_nonneg (add_nonneg (mul_nonneg hf.Bf_nonneg hg.M_nonneg)
    (mul_nonneg hg.Bf_nonneg hf.M_nonneg)) (mul_nonneg zero_le_two (mul_nonneg hf.L_nonneg hg.L_nonneg))
  bdd y := by
    rw [abs_mul]
    exact mul_le_mul (hf.bdd y) (hg.bdd y) (abs_nonneg _) hf.Bf_nonneg
  lip a b := by
    have h : f a * g a - f b * g b = f a * (g a - g b) + g b * (f a - f b) := by ring
    rw [h]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |f a| * |g a - g b| ≤ Bf * (Lg * ‖a - b‖) :=
      mul_le_mul (hf.bdd a) (hg.lip a b) (abs_nonneg _) hf.Bf_nonneg
    have h2 : |g b| * |f a - f b| ≤ Bg * (Lf * ‖a - b‖) :=
      mul_le_mul (hg.bdd b) (hf.lip a b) (abs_nonneg _) hg.Bf_nonneg
    nlinarith [h1, h2]
  second x z := by
    have hz := sq_nonneg ‖z‖
    have h : f (x + z) * g (x + z) + f (x - z) * g (x - z) - 2 * (f x * g x) =
        f x * (g (x + z) + g (x - z) - 2 * g x) + g x * (f (x + z) + f (x - z) - 2 * f x) +
          (f (x + z) - f x) * (g (x + z) - g x) + (f (x - z) - f x) * (g (x - z) - g x) := by ring
    show |f (x + z) * g (x + z) + f (x - z) * g (x - z) - 2 * (f x * g x)| ≤ _
    rw [h]
    have e1 : |f x * (g (x + z) + g (x - z) - 2 * g x)| ≤ Bf * (Mg * ‖z‖ ^ 2) := by
      rw [abs_mul]; exact mul_le_mul (hf.bdd x) (hg.second x z) (abs_nonneg _) hf.Bf_nonneg
    have e2 : |g x * (f (x + z) + f (x - z) - 2 * f x)| ≤ Bg * (Mf * ‖z‖ ^ 2) := by
      rw [abs_mul]; exact mul_le_mul (hg.bdd x) (hf.second x z) (abs_nonneg _) hg.Bf_nonneg
    have hp : ‖(x + z) - x‖ = ‖z‖ := by simp
    have hm : ‖(x - z) - x‖ = ‖z‖ := by simp
    have a1 := hf.lip (x + z) x
    have b1 := hg.lip (x + z) x
    have a2 := hf.lip (x - z) x
    have b2 := hg.lip (x - z) x
    rw [hp] at a1 b1
    rw [hm] at a2 b2
    have e3 : |(f (x + z) - f x) * (g (x + z) - g x)| ≤ Lf * Lg * ‖z‖ ^ 2 := by
      rw [abs_mul]
      calc _ ≤ (Lf * ‖z‖) * (Lg * ‖z‖) := mul_le_mul a1 b1 (abs_nonneg _) (mul_nonneg hf.L_nonneg (norm_nonneg _))
        _ = _ := by ring
    have e4 : |(f (x - z) - f x) * (g (x - z) - g x)| ≤ Lf * Lg * ‖z‖ ^ 2 := by
      rw [abs_mul]
      calc _ ≤ (Lf * ‖z‖) * (Lg * ‖z‖) := mul_le_mul a2 b2 (abs_nonneg _) (mul_nonneg hf.L_nonneg (norm_nonneg _))
        _ = _ := by ring
    refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [abs_le.1 e1, abs_le.1 e2, abs_le.1 e3, abs_le.1 e4]

lemma PvC2.of_contDiff {f : 𝔼 → ℝ} (hf : ContDiff ℝ 2 f) {B L M : ℝ} (hB : ∀ y, ‖f y‖ ≤ B)
    (hL : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ L) (hM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M) :
    PvC2 f B L M where
  cont := hf.continuous
  Bf_nonneg := (norm_nonneg _).trans (hB 0)
  L_nonneg := (norm_nonneg _).trans (hL 0)
  M_nonneg := (norm_nonneg _).trans (hM 0)
  bdd y := by simpa [Real.norm_eq_abs] using hB y
  lip a b := pvapi_lip_of_fderiv (hf.differentiable (by norm_num))
    (fun y => by simpa using hL y) a b
  second x z := pvapi_second_diff hf hM x z

/-- Schwartz functions -/
lemma PvC2.of_schwartz (W : 𝓢(𝔼, ℝ)) : ∃ B L M : ℝ, PvC2 W B L M := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 W, SchwartzMap.seminorm ℝ 0 1 W, SchwartzMap.seminorm ℝ 0 2 W,
    PvC2.of_contDiff (W.smooth 2) (fun y => ?_) (fun y => ?_) (fun y => ?_)⟩
  · simpa using W.le_seminorm ℝ 0 0 y
  · simpa using W.le_seminorm ℝ 0 1 y
  · simpa using W.le_seminorm ℝ 0 2 y

/-- `C_b²` functions -/
lemma PvC2.of_memCb {μ : 𝔼 → ℝ} (hμ : HRS.MemCb 2 μ) : ∃ B L M : ℝ, PvC2 μ B L M := by
  have hc : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B, hB⟩ := hμ.2 0 (by norm_num)
  obtain ⟨L, hL⟩ := hμ.2 1 (by norm_num)
  obtain ⟨M, hM⟩ := hμ.2 2 le_rfl
  exact ⟨B, L, M, PvC2.of_contDiff hc (fun y => by simpa using hB ⟨y, rfl⟩)
    (fun y => hL ⟨y, rfl⟩) (fun y => hM ⟨y, rfl⟩)⟩

/-! ### integrability of kernels outside a ball -/

lemma pvapi_integrableOn_rpow_outside (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-s)) {z : 𝔼 | ε < ‖z‖} := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsub : {z : 𝔼 | ε < ‖z‖} ⊆ ({z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1) ∪ {z : 𝔼 | 1 < ‖z‖} := by
    intro z hz
    by_cases h : ‖z‖ ≤ 1
    · exact Or.inl ⟨hz, by simpa using h⟩
    · exact Or.inr (not_le.1 h)
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ (pvapi_integrableOn_tail_rpow hd hs)) hsub
  have hfin : volume ({z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1) ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  have hS : MeasurableSet ({z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1) :=
    (measurableSet_lt measurable_const measurable_norm).inter measurableSet_closedBall
  refine Integrable.mono' (integrableOn_const (C := ε ^ (-s)) hfin)
    (measurable_norm.pow_const _).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
  have hz' : ε < ‖z‖ := hz.1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow_of_nonpos hε hz'.le (by linarith)

/-- bounded measurable `g` over `|z|^s`, `s > d`, is integrable outside every ball -/
lemma pvapi_integrableOn_div_pow (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) {ε : ℝ} (hε : 0 < ε)
    {g : 𝔼 → ℝ} (hg : Measurable g) {C : ℝ} (hb : ∀ z, |g z| ≤ C) :
    IntegrableOn (fun z => g z / ‖z‖ ^ s) {z : 𝔼 | ε < ‖z‖} := by
  have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  refine Integrable.mono' ((pvapi_integrableOn_rpow_outside hd hs hε).const_mul C)
    (hg.div (measurable_norm.pow_const _)).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
  have hz' : ε < ‖z‖ := hz
  have hn : 0 < ‖z‖ := hε.trans hz'
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), Real.rpow_neg hn.le,
    ← div_eq_mul_inv]
  gcongr
  exact hb z

/-- reflection invariance of integrals over symmetric sets -/
lemma pvapi_reflect {S : Set 𝔼} (hS : MeasurableSet S) (hsym : ∀ z, -z ∈ S ↔ z ∈ S) (F : 𝔼 → ℝ) :
    ∫ z in S, F (-z) = ∫ z in S, F z := by
  rw [← integral_indicator hS, ← integral_indicator hS]
  have key := integral_neg_eq_self (fun z => S.indicator F z) volume
  refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans key
  show S.indicator (fun z => F (-z)) z = S.indicator F (-z)
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem ((hsym z).2 hz)]
  · rw [indicator_of_notMem hz, indicator_of_notMem (mt (hsym z).1 hz)]

lemma pvapi_integrableOn_h1 (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z => (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)) {z : 𝔼 | ε < ‖z‖} := by
  refine pvapi_integrableOn_div_pow hd (by linarith) hε
    ((continuous_const.sub (hf.cont.comp (continuous_const.sub continuous_id))).measurable)
    (C := 2 * Bf) (fun z => ?_)
  have := hf.bdd x
  have := hf.bdd (x - z)
  calc |f x - f (x - z)| ≤ |f x| + |f (x - z)| := abs_sub _ _
    _ ≤ 2 * Bf := by linarith

lemma pvapi_integrableOn_h2 (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z => (f x - f (x + z)) / ‖z‖ ^ ((d : ℝ) + θ)) {z : 𝔼 | ε < ‖z‖} := by
  refine pvapi_integrableOn_div_pow hd (by linarith) hε
    ((continuous_const.sub (hf.cont.comp (continuous_const.add continuous_id))).measurable)
    (C := 2 * Bf) (fun z => ?_)
  have := hf.bdd x
  have := hf.bdd (x + z)
  calc |f x - f (x + z)| ≤ |f x| + |f (x + z)| := abs_sub _ _
    _ ≤ 2 * Bf := by linarith

/-- the symmetrised kernel integrand is absolutely integrable on `ℝ^d` (`θ < 2`) -/
lemma pvapi_hsym_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) :
    Integrable (fun z : 𝔼 => (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)) := by
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmeas : Measurable (fun z : 𝔼 => (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)) :=
    ((((continuous_const.sub (hf.cont.comp (continuous_const.sub continuous_id))).sub
      (hf.cont.comp (continuous_const.add continuous_id))).measurable).div_const 2).div
      (measurable_norm.pow_const _)
  have hU : (univ : Set 𝔼) = closedBall 0 1 ∪ {z : 𝔼 | 1 < ‖z‖} := by
    ext z
    simp only [mem_univ, mem_union, mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, true_iff]
    by_cases h : ‖z‖ ≤ 1
    · exact Or.inl h
    · exact Or.inr (not_le.1 h)
  rw [← integrableOn_univ, hU]
  refine IntegrableOn.union ?_ ?_
  · -- near zero
    have hint : IntegrableOn (fun z : 𝔼 => (M / 2) * ‖z‖ ^ (-((d : ℝ) + θ - 2))) (closedBall 0 1) := by
      have : IntegrableOn (fun z : 𝔼 => (M / 2) * ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
        (pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2).const_mul (M / 2)
      exact this.mono_set (closedBall_subset_ball (by norm_num))
    refine Integrable.mono' hint hmeas.aestronglyMeasurable.restrict (ae_of_all _ fun z => ?_)
    by_cases hz : z = 0
    · subst hz
      simp only [sub_zero, add_zero, norm_zero]
      have : 2 * f x - f x - f x = 0 := by ring
      rw [this, zero_div, zero_div, norm_zero]
      exact mul_nonneg (div_nonneg hf.M_nonneg zero_le_two) (Real.rpow_nonneg le_rfl _)
    · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hs := hf.second x z
      have hneg : 2 * f x - f (x - z) - f (x + z) = -(f (x + z) + f (x - z) - 2 * f x) := by ring
      rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), hneg, abs_neg,
        abs_two]
      have h3 : ‖z‖ ^ (-((d : ℝ) + θ - 2)) = ‖z‖ ^ 2 / ‖z‖ ^ ((d : ℝ) + θ) := by
        rw [show -((d : ℝ) + θ - 2) = (2 : ℝ) - ((d : ℝ) + θ) by ring, Real.rpow_sub hn, Real.rpow_two]
      rw [h3]
      have hpos : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
      calc |f (x + z) + f (x - z) - 2 * f x| / 2 / ‖z‖ ^ ((d : ℝ) + θ)
          ≤ (M * ‖z‖ ^ 2) / 2 / ‖z‖ ^ ((d : ℝ) + θ) := by gcongr
        _ = M / 2 * (‖z‖ ^ 2 / ‖z‖ ^ ((d : ℝ) + θ)) := by ring
  · -- far
    refine pvapi_integrableOn_div_pow (g := fun z => (2 * f x - f (x - z) - f (x + z)) / 2) hd
      (by linarith) one_pos
      ((((continuous_const.sub (hf.cont.comp (continuous_const.sub continuous_id))).sub
        (hf.cont.comp (continuous_const.add continuous_id))).measurable).div_const 2)
      (C := 2 * Bf) (fun z => ?_)
    have a1 := hf.bdd x
    have a2 := hf.bdd (x - z)
    have a3 := hf.bdd (x + z)
    rw [abs_div, abs_two, div_le_iff₀ zero_lt_two]
    have : |2 * f x - f (x - z) - f (x + z)| ≤ 4 * Bf := by
      rw [abs_le]
      constructor <;> linarith [abs_le.1 a1, abs_le.1 a2, abs_le.1 a3]
    linarith

/-- the symmetrisation of the truncated integral -/
lemma pvapi_sym_trunc_eq (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) {ε : ℝ} (hε : 0 < ε) :
    ∫ z in {z : 𝔼 | ε < ‖z‖}, (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) =
      ∫ z in {z : 𝔼 | ε < ‖z‖}, (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ) := by
  have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hsym : ∀ z : 𝔼, -z ∈ {z : 𝔼 | ε < ‖z‖} ↔ z ∈ {z : 𝔼 | ε < ‖z‖} := fun z => by
    simp [norm_neg]
  have i1 := pvapi_integrableOn_h1 hd hθ0 hf x hε
  have i2 := pvapi_integrableOn_h2 hd hθ0 hf x hε
  have hrefl := pvapi_reflect hS hsym (fun z => (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ))
  have hh2 : ∀ z : 𝔼, (f x - f (x + z)) / ‖z‖ ^ ((d : ℝ) + θ) =
      (fun z => (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ)) (-z) := fun z => by
    simp [norm_neg]
  have hpt : ∀ z : 𝔼, (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) =
      ((f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ) + (f x - f (x + z)) / ‖z‖ ^ ((d : ℝ) + θ)) / 2 :=
    fun z => by ring
  simp_rw [hpt]
  rw [integral_div, integral_add i1 i2]
  simp_rw [hh2]
  rw [hrefl]
  ring

/-- (e, part 1) the `fracLap` truncations converge -/
theorem fracLap_tendsto (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) :
    Tendsto (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖}, (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ))
      (𝓝[>] 0) (𝓝 (∫ z, (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ))) := by
  have hg := pvapi_hsym_integrable hd hθ0 hθ2 hf x
  have hg0 : (2 * f x - f (x - 0) - f (x + 0)) / 2 / ‖(0 : 𝔼)‖ ^ ((d : ℝ) + θ) = 0 := by
    have : 2 * f x - f (x - 0) - f (x + 0) = 0 := by simp; ring
    rw [this, zero_div, zero_div]
  refine (pvapi_tendsto_trunc hg hg0).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact pvapi_sym_trunc_eq hd hθ0 hf x hε

/-- the frozen `fracLap` is the absolutely convergent symmetrised integral -/
theorem fracLap_eq_symm (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) :
    HRS.Whole.AppendixA.fracLap d θ f x =
      ∫ z, (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) :=
  (fracLap_tendsto hd hθ0 hθ2 hf x).limUnder_eq

/-- (f) splitting `|z| ≤ 1`, `|z| > 1` -/
theorem fracLap_split (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {f : 𝔼 → ℝ} {Bf L M : ℝ}
    (hf : PvC2 f Bf L M) (x : 𝔼) :
    HRS.Whole.AppendixA.fracLap d θ f x =
      (∫ z in closedBall (0 : 𝔼) 1, (2 * f x - f (x - z) - f (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)) +
        ∫ z in {z : 𝔼 | 1 < ‖z‖}, (f x - f (x - z)) / ‖z‖ ^ ((d : ℝ) + θ) := by
  have hg := pvapi_hsym_integrable hd hθ0 hθ2 hf x
  have hTm : MeasurableSet {z : 𝔼 | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hU : closedBall (0 : 𝔼) 1 ∪ {z : 𝔼 | 1 < ‖z‖} = univ := by
    ext z
    simp only [mem_univ, mem_union, mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, iff_true]
    by_cases h : ‖z‖ ≤ 1
    · exact Or.inl h
    · exact Or.inr (not_le.1 h)
  have hdisj : Disjoint (closedBall (0 : 𝔼) 1) {z : 𝔼 | 1 < ‖z‖} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    have : ‖z‖ ≤ 1 := by simpa using h1
    have h3 : 1 < ‖z‖ := h2
    linarith
  have := setIntegral_union hdisj hTm hg.integrableOn hg.integrableOn
  rw [hU, setIntegral_univ] at this
  rw [fracLap_eq_symm hd hθ0 hθ2 hf x, this, pvapi_sym_trunc_eq hd hθ0 hf x one_pos]

/-! ### `lamComm` -/

/-- (e) the commutator kernel, abstract data -/
theorem lamComm_kernel_tendsto_of (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    {μ W : 𝔼 → ℝ} {Bμ Lμ Mμ BW LW MW : ℝ} (hμ : PvC2 μ Bμ Lμ Mμ) (hW : PvC2 W BW LW MW) (x : 𝔼) :
    Tendsto (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖},
        (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)) (𝓝[>] 0)
      (𝓝 (HRS.Whole.AppendixA.lamComm d θ μ W x)) := by
  have hμW := hμ.mul hW
  have t1 := fracLap_tendsto hd hθ0 hθ2 hμW x
  have t2 := fracLap_tendsto hd hθ0 hθ2 hW x
  have t := t1.sub (t2.const_mul (μ x))
  have hlim : (∫ z, (2 * (fun y => μ y * W y) x - (fun y => μ y * W y) (x - z) -
        (fun y => μ y * W y) (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ)) -
      μ x * ∫ z, (2 * W x - W (x - z) - W (x + z)) / 2 / ‖z‖ ^ ((d : ℝ) + θ) =
      HRS.Whole.AppendixA.lamComm d θ μ W x := by
    unfold HRS.Whole.AppendixA.lamComm
    rw [fracLap_eq_symm hd hθ0 hθ2 hμW x, fracLap_eq_symm hd hθ0 hθ2 hW x]
  rw [hlim] at t
  refine t.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have i1 := pvapi_integrableOn_h1 hd hθ0 hμW x hε
  have i2 := pvapi_integrableOn_h1 hd hθ0 hW x hε
  rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul (μ x))]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- (e) `lamComm_kernel`: for `μ ∈ C_b²`, `W` Schwartz and `0 < θ < 2` the limit exists and
`lamComm d θ μ W x = lim_{ε→0+} ∫_{ε<|z|} (μ(x)-μ(x-z)) W(x-z)/|z|^{d+θ} dz` -/
theorem lamComm_kernel_tendsto (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    Tendsto (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖},
        (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)) (𝓝[>] 0)
      (𝓝 (HRS.Whole.AppendixA.lamComm d θ μ W x)) := by
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_memCb hμ
  obtain ⟨B2, L2, M2, h2⟩ := PvC2.of_schwartz W
  exact lamComm_kernel_tendsto_of hd hθ0 hθ2 h1 h2 x

theorem lamComm_kernel (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    HRS.Whole.AppendixA.lamComm d θ μ W x =
      limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖},
        (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)) :=
  (lamComm_kernel_tendsto hd hθ0 hθ2 hμ W x).limUnder_eq.symm

/-- (f) `lamComm` splitting at `|z| = 1` (abstract data): the local part is the symmetrised kernel -/
theorem lamComm_split (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2)
    {μ W : 𝔼 → ℝ} {Bμ Lμ Mμ BW LW MW : ℝ} (hμ : PvC2 μ Bμ Lμ Mμ) (hW : PvC2 W BW LW MW) (x : 𝔼) :
    HRS.Whole.AppendixA.lamComm d θ μ W x =
      (∫ z in closedBall (0 : 𝔼) 1, ((μ x - μ (x - z)) * W (x - z) + (μ x - μ (x + z)) * W (x + z)) / 2 /
          ‖z‖ ^ ((d : ℝ) + θ)) +
        ∫ z in {z : 𝔼 | 1 < ‖z‖}, (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ) := by
  have hμW := hμ.mul hW
  have e1 := fracLap_split hd hθ0 hθ2 hμW x
  have e2 := fracLap_split hd hθ0 hθ2 hW x
  have g1 := (pvapi_hsym_integrable hd hθ0 hθ2 hμW x).integrableOn (s := closedBall (0 : 𝔼) 1)
  have g2 := (pvapi_hsym_integrable hd hθ0 hθ2 hW x).integrableOn (s := closedBall (0 : 𝔼) 1)
  have i1 := pvapi_integrableOn_h1 hd hθ0 hμW x one_pos
  have i2 := pvapi_integrableOn_h1 hd hθ0 hW x one_pos
  unfold HRS.Whole.AppendixA.lamComm
  rw [e1, e2]
  rw [mul_add, ← integral_const_mul, ← integral_const_mul]
  have : ∀ (a b c e : ℝ), a + b - (c + e) = (a - c) + (b - e) := fun a b c e => by ring
  rw [this, ← integral_sub g1 (g2.const_mul (μ x)), ← integral_sub i1 (i2.const_mul (μ x))]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    ring
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    ring

end HRS.CZ.Pv

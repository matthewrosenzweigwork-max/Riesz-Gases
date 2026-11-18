import HRS.MS.UniqN2aB

/-!
# N2a of `UniqPlan.md`, part (c): `truncPairing → - ∫ f a (g * ∂_i(ς f))`

For `d - 1 < s < d`, `κ = ∂_i g`, `a` continuous, `f` measurable with `a f` integrable and
`ψ = ς f ∈ C¹_c`:  `truncPairing ε κ a f ς = - ∫ y, a(y) f(y) A_ε(y) dy` (Fubini, `κ` odd) with
`A_ε` the truncated principal value of part (b), hence
`truncPairing ε κ a f ς → - ∫ y, f(y) a(y) kernelConvDeriv d s i (ς f) y` as `ε → 0⁺`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN0 HRS.MS.UniqM1
  HRS.MS.UniqT3

variable {d : ℕ}

theorem trunc_integrable {s : ℝ} (hs0 : 0 < s) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {a f ς : Euc d → ℝ} (ha : Continuous a) (hf : Measurable f)
    (haf : Integrable (fun y => a y * f y))
    (hψ : ContDiff ℝ 1 (fun x => ς x * f x)) (hψc : HasCompactSupport (fun x => ς x * f x))
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : Euc d × Euc d => if ε < ‖p.1 - p.2‖ then
      kap d s i (p.1 - p.2) * a p.2 * f p.2 * ς p.1 * f p.1 else 0) (volume.prod volume) := by
  set K0 : ℝ := max 1 s with hK0
  have hK00 : 0 ≤ K0 := le_trans zero_le_one (le_max_left _ _)
  have hψi : Integrable (fun x => ς x * f x) := hψ.continuous.integrable_of_hasCompactSupport hψc
  have hb := ((hψi.norm.mul_prod haf.norm).const_mul (K0 * ε ^ (-s - 1)))
  have hψm : Measurable (fun x => ς x * f x) := hψ.continuous.measurable
  have hmeas : Measurable (fun p : Euc d × Euc d => if ε < ‖p.1 - p.2‖ then
      kap d s i (p.1 - p.2) * (a p.2 * f p.2) * (ς p.1 * f p.1) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp
      (measurable_fst.sub measurable_snd)))
      ((((kap_measurable s i).comp (measurable_fst.sub measurable_snd)).mul
        ((ha.measurable.comp measurable_snd).mul (hf.comp measurable_snd))).mul
        (hψm.comp measurable_fst)) measurable_const
  have hrew : (fun p : Euc d × Euc d => if ε < ‖p.1 - p.2‖ then
      kap d s i (p.1 - p.2) * a p.2 * f p.2 * ς p.1 * f p.1 else 0) =
      fun p => if ε < ‖p.1 - p.2‖ then
      kap d s i (p.1 - p.2) * (a p.2 * f p.2) * (ς p.1 * f p.1) else 0 := by
    funext p; split_ifs <;> ring
  rw [hrew]
  refine hb.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  by_cases hp : ε < ‖p.1 - p.2‖
  · rw [if_pos hp]
    have hzp : 0 < ‖p.1 - p.2‖ := hε.trans hp
    have hk := kap_bound hs0.le i (norm_pos_iff.1 hzp)
    have h1 : ‖p.1 - p.2‖ ^ (-s - 1) ≤ ε ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hε hp.le (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hk' : |kap d s i (p.1 - p.2)| ≤ K0 * ε ^ (-s - 1) := hk.trans (by gcongr)
    calc |kap d s i (p.1 - p.2)| * |a p.2 * f p.2| * |ς p.1 * f p.1|
        ≤ (K0 * ε ^ (-s - 1)) * ‖a p.2 * f p.2‖ * ‖ς p.1 * f p.1‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
      _ = _ := by ring
  · rw [if_neg hp]; simp only [norm_zero]
    positivity

/-- The inner integral over `x` (substitution `x = y - z`, `κ` odd). -/
theorem trunc_inner {s : ℝ} (i : Fin d) (a f ς : Euc d → ℝ) {ε : ℝ} (y : Euc d) :
    ∫ x, (if ε < ‖x - y‖ then kap d s i (x - y) * a y * f y * ς x * f x else 0) =
      - ((a y * f y) * ∫ z, (if ε < ‖z‖ then kap d s i z * (fun x => ς x * f x) (y - z) else 0)) := by
  have hrew : ∀ x : Euc d, (if ε < ‖x - y‖ then
      kap d s i (x - y) * a y * f y * ς x * f x else 0) =
      (a y * f y) * (if ε < ‖x - y‖ then kap d s i (x - y) * (ς x * f x) else 0) := by
    intro x; split_ifs <;> ring
  simp only [hrew]
  rw [integral_const_mul, ← mul_neg, ← integral_neg]
  congr 1
  rw [← integral_sub_left_eq_self (fun x => (if ε < ‖x - y‖ then
      kap d s i (x - y) * (ς x * f x) else 0)) volume y]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sub_sub_cancel_left, norm_neg, kap_neg]
  split_ifs <;> ring

/-- Fubini. -/
theorem trunc_eq_neg {s : ℝ} (hs0 : 0 < s) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {a f ς : Euc d → ℝ} (ha : Continuous a) (hf : Measurable f)
    (haf : Integrable (fun y => a y * f y))
    (hψ : ContDiff ℝ 1 (fun x => ς x * f x)) (hψc : HasCompactSupport (fun x => ς x * f x))
    {ε : ℝ} (hε : 0 < ε) :
    truncPairing ε (kap d s i) a f ς = - ∫ y, (a y * f y) *
      ∫ z, (if ε < ‖z‖ then kap d s i z * (fun x => ς x * f x) (y - z) else 0) := by
  have hI := trunc_integrable hs0 hs1 i ha hf haf hψ hψc hε
  unfold truncPairing
  rw [Measure.volume_eq_prod, integral_prod_symm _ hI, ← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun y => trunc_inner i a f ς y)

/-- `truncPairing ε κ a f ς → - ∫ f a (g * ∂_i(ς f))`. -/
theorem trunc_tendsto {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {a f ς : Euc d → ℝ} (ha : Continuous a) (hf : Measurable f)
    (haf : Integrable (fun y => a y * f y))
    (hψ : ContDiff ℝ 1 (fun x => ς x * f x)) (hψc : HasCompactSupport (fun x => ς x * f x)) :
    Tendsto (fun ε : ℝ => truncPairing ε (kap d s i) a f ς) (𝓝[>] (0 : ℝ))
      (𝓝 (- ∫ y, f y * a y * kernelConvDeriv d s i (fun x => ς x * f x) y)) := by
  obtain ⟨C0, hC0⟩ := pv_bound hs0 hsd hs1 i hψ hψc
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), truncPairing ε (kap d s i) a f ς =
      - ∫ y, (a y * f y) * ∫ z, (if ε < ‖z‖ then kap d s i z * (fun x => ς x * f x) (y - z) else 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact trunc_eq_neg hs0 hs1 i ha hf haf hψ hψc hε
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  refine Tendsto.neg ?_
  have : (fun y => f y * a y * kernelConvDeriv d s i (fun x => ς x * f x) y) =
      fun y => (a y * f y) * kernelConvDeriv d s i (fun x => ς x * f x) y := by
    funext y; ring
  rw [this]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => |a y * f y| * C0) ?_ ?_
    (haf.abs.mul_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hI := trunc_integrable hs0 hs1 i ha hf haf hψ hψc hε
    have h1 := hI.integral_prod_right.aestronglyMeasurable.neg
    refine h1.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply]
    rw [trunc_inner i a f ς y, neg_neg]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC0 y hε) (abs_nonneg _)
  · exact Eventually.of_forall fun y => (pv_tendsto hs0 hsd hs1 i hψ hψc y).const_mul _

end HRS.MS.UniqN2a

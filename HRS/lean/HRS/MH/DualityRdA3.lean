import HRS.MH.DualityRdDefs
import HRS.MH.DualityRdA1
import HRS.Stochastic.EmpiricalIto

/-!
# DualityRd packet A3: progressive measurability and `L²` of the truncated Itô integrand on `ℝ^d`

Ports `HRS.isProgressiveL2_empiricalNoiseIntegrand` (`HRS/Stochastic/EmpiricalIto.lean:765`) with its ingredients
`continuousOn_gradient_time`, `continuous_gradient_clamp`, `grad_bound`, `measurable_uncurry_noiseG`, `abs_noiseG_le`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem da3_continuousOn_gradient {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ContinuousOn (fun p : ℝ × Euc d => gradient (f p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (f p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ) := by
    have h := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn
      (da1_contOn_iter hf (j := 1) (by norm_num))
    exact h.congr fun p _ => by simp [HRS.fderiv_eq_curry]
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous).comp_continuousOn h1

theorem da3_continuous_gradient_clamp {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    Continuous (fun p : ℝ × Euc d => gradient (f (HRS.clampTI t p.1)) p.2) := by
  have hq : Continuous fun p : ℝ × Euc d => (HRS.clampTI t p.1, p.2) :=
    ((HRS.continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  exact ContinuousOn.comp_continuous
    (g := fun p : ℝ × Euc d => gradient (f p.1) p.2)
    (f := fun p : ℝ × Euc d => (HRS.clampTI t p.1, p.2)) (da3_continuousOn_gradient hf) hq
    (fun p => (⟨HRS.clampTI_mem ht p.1, Set.mem_univ _⟩ : (HRS.clampTI t p.1, p.2) ∈ Set.Icc 0 t ×ˢ Set.univ))

theorem da3_measurable_uncurry {N : ℕ} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    Measurable (Function.uncurry (fun (r : ℝ) (Y : EucConfig d N) (k : Fin N × Fin d) =>
      if r ∈ Set.Icc (0 : ℝ) t then Whole.gradComp k.2 (f r) (Y k.1) else 0)) := by
  refine measurable_pi_iff.2 fun k => ?_
  change Measurable fun p : ℝ × EucConfig d N =>
    if p.1 ∈ Set.Icc (0 : ℝ) t then Whole.gradComp k.2 (f p.1) (p.2 k.1) else 0
  have hG : Measurable fun p : ℝ × EucConfig d N => Whole.gradComp k.2 (f (HRS.clampTI t p.1)) (p.2 k.1) := by
    have hcoord : Measurable fun v : Euc d => v k.2 := by fun_prop
    have hq : Measurable fun p : ℝ × EucConfig d N => ((p.1, p.2 k.1) : ℝ × Euc d) :=
      measurable_fst.prodMk ((measurable_pi_apply k.1).comp measurable_snd)
    exact (hcoord.comp ((da3_continuous_gradient_clamp ht hf).measurable)).comp hq
  have heq : (fun p : ℝ × EucConfig d N =>
      if p.1 ∈ Set.Icc (0 : ℝ) t then Whole.gradComp k.2 (f p.1) (p.2 k.1) else 0) =
      fun p : ℝ × EucConfig d N =>
        if p.1 ∈ Set.Icc (0 : ℝ) t then Whole.gradComp k.2 (f (HRS.clampTI t p.1)) (p.2 k.1) else 0 := by
    funext p
    split_ifs with h
    · rw [HRS.clampTI_of_mem h]
    · rfl
  rw [heq]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hG measurable_const

theorem da3_abs_gradComp_le {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {B : ℝ}
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d, ‖iteratedFDeriv ℝ 1 (f r) x‖ ≤ B)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (x : Euc d) (a : Fin d) :
    |Whole.gradComp a (f r) x| ≤ |B| := by
  have h1 : |gradient (f r) x a| ≤ ‖gradient (f r) x‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le _ _
  have h2 : ‖gradient (f r) x‖ = ‖fderiv ℝ (f r) x‖ := by
    rw [← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ (Euc d)) (gradient (f r) x),
      toDual_gradient]
  have h3 : |gradient (f r) x a| ≤ B :=
    h1.trans ((le_of_eq h2).trans (by rw [← norm_iteratedFDeriv_one]; exact hB r hr x))
  exact h3.trans (le_abs_self B)

/-- **Packet A3** (M, ~150 lines).  Ports `isProgressiveL2_empiricalNoiseIntegrand` (`EmpiricalIto.lean:765`) with its ingredients
`clampTI` (`:653-662`, generic), `continuousOn_gradient_time`/`continuous_gradient_clamp`/`measurable_grad_clamp` (`:665-690`),
`grad_bound` (`:707`; here the bound is `bdd 1`: `‖gradient g x‖ = ‖fderiv ℝ g x‖ ≤ B`), `noiseG` and `measurable_uncurry_noiseG`
(`:723-747`), `abs_noiseG_le` (`:749`), `isProgressive_comp_measurable'` (`:642`, generic) and `IsProgressiveL2.of_bounded`
(`Integral.lean`).  Without the truncation to `[0,t]` this is false (`f r` is unconstrained outside `[0,t]`; see `StatementRepairs.lean`
`DualityIdentityRdTrunc`).  Only the measurability of `(r,x) ↦ gradient (f (clamp r)) x` (continuity from `cont_c2`, `j = 1`) and the
bound are needed. -/
theorem isProgressiveL2_truncGrad_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {N : ℕ} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft)
    {X : ℝ≥0 → Ω → EucConfig d N} (hX : IsProgressive ℱ (HRS.ofNNRealTime X)) :
    HRS.IsProgressiveL2 P ℱ (truncGradIntegrand t f X) := by
  obtain ⟨B, hB⟩ := hf.bdd 1 (by norm_num)
  have hprog : IsProgressive ℱ (truncGradIntegrand t f X) :=
    HRS.isProgressive_comp_measurable' (HRS.ofNNRealTime X) hX
      (fun (r : ℝ) (Y : EucConfig d N) (k : Fin N × Fin d) =>
        if r ∈ Set.Icc (0 : ℝ) t then Whole.gradComp k.2 (f r) (Y k.1) else 0)
      (da3_measurable_uncurry ht hf)
  refine IsProgressiveL2.of_bounded P hprog |B| fun s ζ k => ?_
  unfold truncGradIntegrand
  split_ifs with h
  · exact da3_abs_gradComp_le hf hB h _ k.2
  · rw [abs_zero]
    exact abs_nonneg _

end HRS.MH.DualityRd

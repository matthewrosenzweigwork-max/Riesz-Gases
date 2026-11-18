import HRS.MS.UniqT3
import HRS.Whole.AppendixBKernel

/-!
# N0 of `UniqPlan.md`, part (a): `H_i = g * ∂_i ψ` represents `∂_i g * ψ`

For `ψ ∈ C¹_c(ℝ^d)` and `0 ≤ s < d` the function `H_i := kernelConvDeriv d s i ψ`
(`y ↦ ∫ g(y-x) ∂_iψ(x) dx`, the function used by `forwardPairing`) satisfies
`IsGradKernelRep d s i ψ H_i` (`n0_gradKernelRep`): for every Schwartz `φ`,
`H_i φ` and `ψ (g * ∂_iφ)` are integrable and `∫ H_i φ = - ∫ ψ (g * ∂_iφ)`.

Route: Fubini on `(x,y) ↦ g(x-y) a(x) b(y)` (`n0_pair_integrable`), the substitution `y = x - u`, the
integration by parts `∫ ∂_iψ(x) φ(x-u) dx = - ∫ ψ(x) ∂_iφ(x-u) dx` for each fixed `u`, and Fubini back.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN0

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3

variable {d : ℕ}

/-- Schwartz functions: `φ` and `‖y‖ φ` are integrable. -/
theorem n0_schwartz_int (φ : SchwartzMap (Euc d) ℝ) :
    Integrable (fun y => φ y) volume ∧ Integrable (fun y : Euc d => ‖y‖ * φ y) volume := by
  refine ⟨φ.integrable, ?_⟩
  have h := φ.integrable_pow_mul volume 1
  refine h.mono ((continuous_norm.mul φ.continuous).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  simp [norm_mul]

/-- The pairing `(x,y) ↦ g(x-y) (a(x) b(y))` is integrable on `ℝ^d × ℝ^d` for `a` continuous with
compact support and `b` continuous with `b, ‖y‖ b` integrable. -/
theorem n0_pair_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a b : Euc d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) (hb : Continuous b)
    (hb1 : Integrable b volume) (hb2 : Integrable (fun y : Euc d => ‖y‖ * b y) volume) :
    Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (a p.1 * b p.2)) := by
  set g := rieszKernel d s with hg
  obtain ⟨G0, hG0i, hG0n, hgG⟩ := g_dom (d := d) hs0 hsd
  obtain ⟨R1, hR1⟩ := hac.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R1 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hRs : tsupport a ⊆ closedBall (0 : Euc d) R :=
    hR1.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨M, hM⟩ := ha.bounded_above_of_compact_support hac
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hind : Integrable ((closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  have hT1 : Integrable (fun p : Euc d × Euc d => |b p.2| * G0 (p.1 - p.2)) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hb1.abs hG0i
  have hw : Integrable (fun y : Euc d => (R + ‖y‖) * |b y|) volume := by
    have h1 : (fun y : Euc d => (R + ‖y‖) * |b y|) = fun y => R * |b y| + |‖y‖ * b y| := by
      funext y; rw [abs_mul, abs_of_nonneg (norm_nonneg y)]; ring
    rw [h1]
    exact (hb1.abs.const_mul R).add hb2.abs
  have hT2 : Integrable (fun p : Euc d × Euc d =>
      (closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ)) p.1 * ((R + ‖p.2‖) * |b p.2|))
      (volume.prod volume) := hind.mul_prod hw
  have hm : Measurable (fun p : Euc d × Euc d => g (p.1 - p.2) * (a p.1 * b p.2)) :=
    ((g_meas s).comp (measurable_fst.sub measurable_snd)).mul
      ((ha.measurable.comp measurable_fst).mul (hb.measurable.comp measurable_snd))
  refine ((hT1.const_mul M).add (hT2.const_mul M)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [Pi.add_apply]
  by_cases hax : a x = 0
  · rw [hax, zero_mul, mul_zero, norm_zero]
    have h1 : 0 ≤ |b y| * G0 (x - y) := mul_nonneg (abs_nonneg _) (hG0n _)
    have h2 : 0 ≤ (closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ)) x *
        ((R + ‖y‖) * |b y|) :=
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (mul_nonneg (by positivity) (abs_nonneg _))
    exact add_nonneg (mul_nonneg hM0 h1) (mul_nonneg hM0 h2)
  · have hxc : x ∈ closedBall (0 : Euc d) R := hRs (subset_tsupport a hax)
    have hxn : ‖x‖ ≤ R := by simpa using hxc
    rw [Set.indicator_of_mem hxc]
    have hxy : ‖x - y‖ ≤ R + ‖y‖ := (norm_sub_le _ _).trans (by linarith)
    have hgx : |g (x - y)| ≤ G0 (x - y) + (R + ‖y‖) := (hgG _).trans (by linarith)
    have hax' : |a x| ≤ M := by simpa [Real.norm_eq_abs] using hM x
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hb0 := abs_nonneg (b y)
    have hG := hG0n (x - y)
    calc |g (x - y)| * (|a x| * |b y|) ≤ (G0 (x - y) + (R + ‖y‖)) * (M * |b y|) := by
          apply mul_le_mul hgx (mul_le_mul_of_nonneg_right hax' hb0) (by positivity) (by positivity)
      _ = _ := by ring

theorem n0_D1_apply (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) :
    LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) φ y = D1 i φ y := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]; rfl

theorem n0_kcd_eq (s : ℝ) (i : Fin d) (ψ : Euc d → ℝ) :
    kernelConvDeriv d s i ψ = HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) := rfl

theorem n0_gradKernelRep {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    IsGradKernelRep d s i ψ (kernelConvDeriv d s i ψ) := by
  intro φ
  set g := rieszKernel d s with hg
  set a : Euc d → ℝ := D1 i ψ with ha
  have hac : Continuous a := (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hacs : HasCompactSupport a := D1_supp hψc i
  set φ' : SchwartzMap (Euc d) ℝ := LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) φ
    with hφ'
  have hφ'a : ∀ y, φ' y = D1 i φ y := n0_D1_apply φ i
  obtain ⟨hφ1, hφ2⟩ := n0_schwartz_int φ
  obtain ⟨hφ'1, hφ'2⟩ := n0_schwartz_int φ'
  have P1 := n0_pair_integrable hs0 hsd hac hacs φ.continuous hφ1 hφ2
  have P2 := n0_pair_integrable hs0 hsd hψ.continuous hψc φ'.continuous hφ'1 hφ'2
  have hgev : ∀ z : Euc d, g (-z) = g z := fun z => rieszKernel_neg z
  -- the representative `H` and the second convolution `K`
  set K : Euc d → ℝ := HRS.Whole.convFun g (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
    with hK
  have hKφ' : K = HRS.Whole.convFun g φ' := by
    funext y; simp only [hK, HRS.Whole.convFun, hφ'a]; rfl
  have hH : ∀ y, kernelConvDeriv d s i ψ y * φ y = ∫ x, g (x - y) * (a x * φ y) := by
    intro y
    simp only [kernelConvDeriv]
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : g (x - y) = g (y - x) := by rw [← hgev (x - y), neg_sub]
    simp only [this, ha, D1, ← hg]
    ring
  have hK' : ∀ x, ψ x * K x = ∫ y, g (x - y) * (ψ x * φ' y) := by
    intro x
    rw [hKφ']
    simp only [HRS.Whole.convFun]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  -- Claim 1 and 2
  have C1 : Integrable (fun y => kernelConvDeriv d s i ψ y * φ y) volume := by
    have := P1.integral_prod_right
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [← hg]
    rw [hH y]
  have C2 : Integrable (fun y => ψ y * K y) volume := by
    have := P2.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [← hg]
    rw [hK' x]
  refine ⟨C1, C2, ?_⟩
  -- coordinates `(x,u)`, `u = x - y`
  have he : MeasurePreserving (fun p : Euc d × Euc d => (p.1, p.1 - p.2))
      (volume.prod volume) (volume.prod volume) := by
    have h1 := (MeasurePreserving.id (volume : Measure (Euc d))).prod
      (Measure.measurePreserving_neg (volume : Measure (Euc d)))
    have h2 := h1.comp (measurePreserving_prod_sub (volume : Measure (Euc d)) (volume : Measure (Euc d)))
    convert h2 using 1
    funext p
    simp
  have T1 : Integrable (fun p : Euc d × Euc d => g p.2 * (a p.1 * φ (p.1 - p.2)))
      (volume.prod volume) := by
    have := he.integrable_comp_of_integrable P1
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, sub_sub_cancel, hg]
  have T2 : Integrable (fun p : Euc d × Euc d => g p.2 * (ψ p.1 * φ' (p.1 - p.2)))
      (volume.prod volume) := by
    have := he.integrable_comp_of_integrable P2
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, sub_sub_cancel, hg]
  -- the chain of equalities
  have step1 : ∫ y, kernelConvDeriv d s i ψ y * φ y = ∫ x, a x * ∫ u, g u * φ (x - u) := by
    calc ∫ y, kernelConvDeriv d s i ψ y * φ y = ∫ y, ∫ x, g (x - y) * (a x * φ y) :=
          integral_congr_ae (Eventually.of_forall hH)
      _ = ∫ x, ∫ y, g (x - y) * (a x * φ y) := (integral_integral_swap (f := fun y x => g (x - y) * (a x * φ y)) P1.swap)
      _ = ∫ x, a x * ∫ u, g u * φ (x - u) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [← integral_const_mul]
          have := integral_sub_left_eq_self (fun u => g u * (a x * φ (x - u))) volume x
          simp only [sub_sub_cancel] at this
          rw [this]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          ring
  have step2 : ∫ x, a x * ∫ u, g u * φ (x - u) = ∫ u, g u * ∫ x, a x * φ (x - u) := by
    calc ∫ x, a x * ∫ u, g u * φ (x - u) = ∫ x, ∫ u, g u * (a x * φ (x - u)) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          ring
      _ = ∫ u, ∫ x, g u * (a x * φ (x - u)) := integral_integral_swap T1
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          beta_reduce
          rw [← integral_const_mul]
  have hibp : ∀ u : Euc d, ∫ x, a x * φ (x - u) = -∫ x, ψ x * φ' (x - u) := by
    intro u
    have hφsh : Continuous (fun x : Euc d => φ (x - u)) := φ.continuous.comp (continuous_id.sub continuous_const)
    have hφ'sh : Continuous (fun x : Euc d => φ' (x - u)) :=
      φ'.continuous.comp (continuous_id.sub continuous_const)
    have hfd : ∀ x, fderiv ℝ (fun x => φ (x - u)) x (EuclideanSpace.single i 1) = φ' (x - u) := by
      intro x
      have := D1_shift i φ u
      have h2 := congrFun this x
      simp only [D1] at h2
      rw [h2, hφ'a]; rfl
    have hI1 : Integrable (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1) * φ (x - u)) volume :=
      (hac.mul hφsh).integrable_of_hasCompactSupport hacs.mul_right
    have hI2 : Integrable (fun x => ψ x * fderiv ℝ (fun x => φ (x - u)) x (EuclideanSpace.single i 1)) volume := by
      simp_rw [hfd]
      exact (hψ.continuous.mul hφ'sh).integrable_of_hasCompactSupport hψc.mul_right
    have hI3 : Integrable (fun x => ψ x * φ (x - u)) volume :=
      (hψ.continuous.mul hφsh).integrable_of_hasCompactSupport hψc.mul_right
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := ψ)
      (g := fun x => φ (x - u)) (v := EuclideanSpace.single i 1) hI1 hI2 hI3
      (fun x _ => (hψ.differentiable one_ne_zero) x)
      (fun x _ => (φ.smooth ⊤ |>.differentiable (by simp)) (x - u) |>.comp x
        ((differentiableAt_id).sub_const u))
    simp_rw [hfd] at this
    have h2 : ∫ x, a x * φ (x - u) =
        ∫ x, fderiv ℝ ψ x (EuclideanSpace.single i 1) * φ (x - u) := rfl
    rw [h2]; linarith
  have step3 : ∫ u, g u * ∫ x, a x * φ (x - u) = -∫ x, ψ x * K x := by
    calc ∫ u, g u * ∫ x, a x * φ (x - u) = ∫ u, -(g u * ∫ x, ψ x * φ' (x - u)) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          beta_reduce
          rw [hibp u]; ring
      _ = -∫ u, ∫ x, g u * (ψ x * φ' (x - u)) := by
          rw [← integral_neg]
          congr 1; funext u
          rw [integral_const_mul]
      _ = -∫ x, ∫ u, g u * (ψ x * φ' (x - u)) := by
          rw [integral_integral_swap (f := fun u x => g u * (ψ x * φ' (x - u))) T2.swap]
      _ = -∫ x, ψ x * K x := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [hKφ']
          simp only [HRS.Whole.convFun]
          rw [← integral_const_mul]
          have := integral_sub_left_eq_self (fun u => g u * (ψ x * φ' (x - u))) volume x
          simp only [sub_sub_cancel] at this
          rw [← this]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          ring
  rw [step1, step2, step3]

end HRS.MS.UniqN0

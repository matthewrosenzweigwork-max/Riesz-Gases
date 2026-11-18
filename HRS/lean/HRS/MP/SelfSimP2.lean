import HRS.MP.SelfSimSpec
import HRS.Stochastic.DDS
import HRS.Stochastic.QuadraticVariation
import HRS.Stochastic.Ito

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.SelfSimP2

variable {d : ℕ}

/-! ### Homogeneity of the Riesz force -/

theorem ssp2_gradient_comp_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) {c : ℝ} (hc : c ≠ 0) (y : E) :
    gradient (fun z => f (c • z)) y = c • gradient f (c • y) := by
  by_cases h : DifferentiableAt ℝ f (c • y)
  · have h1 : HasFDerivAt f (fderiv ℝ f (c • y)) (c • y) := h.hasFDerivAt
    have h2 : HasFDerivAt (fun z : E => c • z) (c • ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_smul c
    have h3 := h1.comp y h2
    have h4 : HasGradientAt (fun z => f (c • z)) (c • gradient f (c • y)) y := by
      have e : InnerProductSpace.toDual ℝ E (c • gradient f (c • y)) =
          (fderiv ℝ f (c • y)).comp (c • ContinuousLinearMap.id ℝ E) := by
        ext v
        simp [real_inner_smul_left, inner_gradient_left]
      rw [hasGradientAt_iff_hasFDerivAt, e]
      exact h3
    exact h4.gradient
  · have h5 : ¬ DifferentiableAt ℝ (fun z => f (c • z)) y := by
      intro hd
      apply h
      have h6 : DifferentiableAt ℝ (fun z : E => c⁻¹ • z) (c • y) :=
        (differentiableAt_id.const_smul c⁻¹)
      have hd' : DifferentiableAt ℝ (fun z => f (c • z)) (c⁻¹ • (c • y)) := by
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul]
      have h7 := hd'.comp (c • y) h6
      have : (fun z => f (c • z)) ∘ (fun z : E => c⁻¹ • z) = f := by
        funext z; simp [Function.comp, smul_smul, mul_inv_cancel₀ hc]
      rw [this] at h7
      exact h7
    rw [gradient_eq_zero_of_not_differentiableAt h5, gradient_eq_zero_of_not_differentiableAt h]
    simp

theorem ssp2_gradient_const_mul_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) (y : E) :
    gradient (fun z => a * f z - b) y = a • gradient f y := by
  by_cases h : DifferentiableAt ℝ f y
  · have h1 : HasFDerivAt (fun z => a * f z - b) (a • fderiv ℝ f y) y :=
      (h.hasFDerivAt.const_mul a).sub_const b
    simp only [gradient, h1.fderiv, map_smul]
  · have h5 : ¬ DifferentiableAt ℝ (fun z => a * f z - b) y := by
      intro hd
      apply h
      have : f = fun z => a⁻¹ * ((fun z => a * f z - b) z + b) := by
        funext z; field_simp; ring
      rw [this]
      exact (hd.add_const b).const_mul a⁻¹
    rw [gradient_eq_zero_of_not_differentiableAt h5, gradient_eq_zero_of_not_differentiableAt h]
    simp

/-- `∇g` is not defined (junk `0`) at the origin: `g` is unbounded there (`d ≥ 1`). -/
theorem ssp2_riesz_grad_zero (hd : 1 ≤ d) (s : ℝ) (hs : 0 ≤ s) : rieszKernelGrad d s 0 = 0 := by
  apply gradient_eq_zero_of_not_differentiableAt
  intro hdiff
  have hc : ContinuousAt (rieszKernel d s) 0 := hdiff.continuousAt
  have hg0 : rieszKernel d s 0 = 0 := by
    by_cases h0 : s = 0
    · simp [rieszKernel, h0]
    · simp [rieszKernel, h0, Real.zero_rpow (neg_ne_zero.2 h0)]
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc 1 one_pos
  let e : Euc d := EuclideanSpace.single ⟨0, hd⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  set t : ℝ := min (δ / 2) (Real.exp (-1)) with ht
  have htpos : 0 < t := lt_min (by positivity) (Real.exp_pos _)
  have hte : ‖t • e‖ = t := by rw [norm_smul, he, Real.norm_eq_abs, abs_of_pos htpos, mul_one]
  have hdist : dist (t • e) 0 < δ := by
    rw [dist_zero_right, hte]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have := hδ' hdist
  rw [hg0, Real.dist_eq, sub_zero] at this
  have ht1 : t ≤ Real.exp (-1) := min_le_right _ _
  by_cases h0 : s = 0
  · have : |rieszKernel d s (t • e)| < 1 := this
    simp only [rieszKernel, h0, if_true, hte] at this
    have hlog : Real.log t ≤ -1 := by
      rw [← Real.log_exp (-1)]; exact Real.log_le_log htpos ht1
    rw [abs_lt] at this
    linarith [this.2]
  · have h1 : |rieszKernel d s (t • e)| < 1 := this
    simp only [rieszKernel, h0, if_false, hte] at h1
    have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    have htlt : t < 1 := lt_of_le_of_lt ht1 (by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      simpa using this)
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg htpos htlt (neg_neg_of_pos hs')
    rw [abs_of_pos (by linarith)] at h1
    linarith

/-- Homogeneity: `∇g(λy) = λ^{-s-1} ∇g(y)` (`λ > 0`), also at `y = 0` (junk `0`). -/
theorem ssp2_riesz_grad_smul (hd : 1 ≤ d) (s : ℝ) (hs : 0 ≤ s) {c : ℝ} (hc : 0 < c) (y : Euc d) :
    rieszKernelGrad d s (c • y) = c ^ (-s - 1) • rieszKernelGrad d s y := by
  by_cases hy : y = 0
  · subst hy
    simp [ssp2_riesz_grad_zero hd s hs]
  · have key := ssp2_gradient_comp_smul (rieszKernel d s) hc.ne' y
    have hev : (fun z => rieszKernel d s (c • z)) =ᶠ[𝓝 y]
        fun z => c ^ (-s) * rieszKernel d s z - (if s = 0 then Real.log c else 0) := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz
      have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
      have hnorm : ‖c • z‖ = c * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      by_cases h0 : s = 0
      · simp only [rieszKernel, h0, if_true, hnorm, neg_zero, Real.rpow_zero, one_mul]
        rw [Real.log_mul hc.ne' hz']; ring
      · simp only [rieszKernel, h0, if_false, hnorm, sub_zero]
        rw [Real.mul_rpow hc.le (norm_nonneg _)]
    have h2 : gradient (fun z => rieszKernel d s (c • z)) y =
        c ^ (-s) • gradient (rieszKernel d s) y := by
      rw [hev.gradient_eq]
      exact ssp2_gradient_const_mul_sub _ (Real.rpow_pos_of_pos hc _).ne' _ y
    rw [h2] at key
    have hpos : c ≠ 0 := hc.ne'
    have h3 : c • (c ^ (-s - 1) • gradient (rieszKernel d s) y) =
        c ^ (-s) • gradient (rieszKernel d s) y := by
      rw [smul_smul]
      congr 1
      rw [Real.rpow_sub hc, Real.rpow_one]
      field_simp
    unfold rieszKernelGrad
    apply smul_right_injective _ hpos
    simp only
    rw [h3]
    exact key.symm

/-! ### The drift identity -/

theorem ssp2_matVec_neg_one (v : Euc d) :
    HRS.Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [HRS.Torus.matVec]

/-- The self-similar drift of the rescaled configuration equals `e^{r/2} b(x) - ½ ξ`. -/
theorem ssp2_drift_identity (hd : 1 ≤ d) (s : ℝ) (hs : 0 ≤ s) (N : ℕ) (invβ : ℝ) (r : ℝ)
    (x : EucConfig d N) (i : Fin N) :
    HRS.MP.SelfSim.ssDrift d s N r (fun j => Real.exp (-r / 2) • x j) i =
      Real.exp (r / 2) • particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) x i -
        (1 / 2 : ℝ) • (Real.exp (-r / 2) • x i) := by
  have hc : 0 < Real.exp (-r / 2) := Real.exp_pos _
  have hsc : aSelfSim s r * Real.exp (-r / 2) ^ (-s - 1) = Real.exp (r / 2) := by
    rw [aSelfSim, ← Real.exp_mul, ← Real.exp_add]
    congr 1; ring
  have hsum : ∑ j ∈ Finset.univ.erase i,
      rieszKernelGrad d s (Real.exp (-r / 2) • x i - Real.exp (-r / 2) • x j) =
      Real.exp (-r / 2) ^ (-s - 1) • ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (x i - x j) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_sub, ssp2_riesz_grad_smul hd s hs hc]
  simp only [HRS.MP.SelfSim.ssDrift, particleDriftW, ssp2_matVec_neg_one, hsum, smul_smul]
  simp only [gradient_fun_const, sub_zero, Finset.sum_neg_distrib, smul_neg, neg_add]
  have h2 : aSelfSim s r / ↑N * Real.exp (-r / 2) ^ (-s - 1) = Real.exp (r / 2) * (1 / (N : ℝ)) := by
    rw [← hsc]; ring
  rw [h2, sub_eq_add_neg, smul_smul]

/-! ### The weight `h(s) = (1+s)^{-1/2}` and integration by parts -/

/-- `h(s) = (1+s)^{-1/2}`. -/
def ssp2_h (s : ℝ) : ℝ := (1 + s) ^ (-(1 / 2 : ℝ))

/-- `h'(s) = -½ (1+s)^{-3/2}`. -/
def ssp2_h' (s : ℝ) : ℝ := -(1 / 2 : ℝ) * (1 + s) ^ (-(3 / 2 : ℝ))

theorem ssp2_hasDerivAt_h {s : ℝ} (hs : -1 < s) : HasDerivAt ssp2_h (ssp2_h' s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
  have h := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (by linarith : 1 + s ≠ 0))
  have e : ssp2_h = fun y : ℝ => (1 + y) ^ (-(1 / 2 : ℝ)) := rfl
  rw [e]
  convert h using 1
  simp only [ssp2_h', one_mul]
  have : -(1 / 2 : ℝ) - 1 = -(3 / 2) := by norm_num
  rw [this]

theorem ssp2_continuousOn_h : ContinuousOn ssp2_h (Set.Ici 0) := fun s hs =>
  (ssp2_hasDerivAt_h (by have := Set.mem_Ici.1 hs; linarith)).continuousAt.continuousWithinAt

theorem ssp2_continuousOn_h' : ContinuousOn ssp2_h' (Set.Ici 0) := by
  refine ContinuousOn.mul continuousOn_const ?_
  intro s hs
  have hs' : 0 ≤ s := hs
  exact ((continuousAt_const.add continuousAt_id).rpow_const
    (Or.inl (by simp; linarith))).continuousWithinAt

theorem ssp2_h_zero : ssp2_h 0 = 1 := by simp [ssp2_h]

theorem ssp2_integral_h' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ q in Set.Icc a b, ssp2_h' q = ssp2_h b - ssp2_h a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
  · rw [Set.uIcc_of_le hab] at hx
    exact ssp2_hasDerivAt_h (by linarith [hx.1])
  · refine (ContinuousOn.intervalIntegrable ?_)
    exact ssp2_continuousOn_h'.mono (fun x hx => by
      rw [Set.uIcc_of_le hab] at hx; exact Set.mem_Ici.2 (by linarith [hx.1]))

/-- Integration by parts against the primitive of an integrable function (Fubini on a triangle). -/
theorem ssp2_ibp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {β : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (hβ : IntegrableOn β (Set.Icc 0 t)) :
    ssp2_h t • ∫ s in Set.Icc 0 t, β s =
      (∫ s in Set.Icc 0 t, ssp2_h s • β s) +
        ∫ q in Set.Icc 0 t, ssp2_h' q • ∫ s in Set.Icc 0 q, β s := by
  have hh'c : ContinuousOn ssp2_h' (Set.Icc 0 t) := ssp2_continuousOn_h'.mono Set.Icc_subset_Ici_self
  have hhc : ContinuousOn ssp2_h (Set.Icc 0 t) := ssp2_continuousOn_h.mono Set.Icc_subset_Ici_self
  have hh' : IntegrableOn ssp2_h' (Set.Icc 0 t) := hh'c.integrableOn_Icc
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 t) with hμ
  let F : ℝ → ℝ → E := fun q s => if s ≤ q then ssp2_h' q • β s else 0
  have hF : Integrable (Function.uncurry F) (μ.prod μ) := by
    have h1 := (hh'.smul_prod hβ).indicator
      (measurableSet_le measurable_snd measurable_fst : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1})
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq, F, Function.uncurry]
  have hswap := integral_integral_swap hF
  -- inner integrals
  have hin1 : ∀ q ∈ Set.Icc (0 : ℝ) t, ∫ s, F q s ∂μ = ssp2_h' q • ∫ s in Set.Icc 0 q, β s := by
    intro q hq
    have : ∫ s, F q s ∂μ = ∫ s in Set.Icc 0 t, Set.indicator (Set.Iic q)
        (fun s => ssp2_h' q • β s) s := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [F, Set.indicator, Set.mem_Iic]
    rw [this, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      integral_smul]
    have hset : Set.Iic q ∩ Set.Icc 0 t = Set.Icc 0 q := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · intro h; exact ⟨h.2.1, h.1⟩
      · intro h; exact ⟨h.2, h.1, h.2.trans hq.2⟩
    rw [hset]
  have hin2 : ∀ s ∈ Set.Icc (0 : ℝ) t, ∫ q, F q s ∂μ = (ssp2_h t - ssp2_h s) • β s := by
    intro s hs
    have : ∫ q, F q s ∂μ = ∫ q in Set.Icc 0 t, Set.indicator (Set.Ici s)
        (fun q => ssp2_h' q • β s) q := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [F, Set.indicator, Set.mem_Ici]
    rw [this, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Set.Ici s ∩ Set.Icc 0 t = Set.Icc s t := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · intro h; exact ⟨h.1, h.2.2⟩
      · intro h; exact ⟨h.1, hs.1.trans h.1, h.2⟩
    rw [hset, integral_smul_const, ssp2_integral_h' hs.1 hs.2]
  have e1 : ∫ q, ∫ s, F q s ∂μ ∂μ = ∫ q in Set.Icc 0 t, ssp2_h' q • ∫ s in Set.Icc 0 q, β s := by
    refine setIntegral_congr_fun measurableSet_Icc fun q hq => ?_
    exact hin1 q hq
  have e2 : ∫ s, ∫ q, F q s ∂μ ∂μ =
      ssp2_h t • (∫ s in Set.Icc 0 t, β s) - ∫ s in Set.Icc 0 t, ssp2_h s • β s := by
    have : ∫ s, ∫ q, F q s ∂μ ∂μ = ∫ s in Set.Icc 0 t, (ssp2_h t - ssp2_h s) • β s :=
      setIntegral_congr_fun measurableSet_Icc fun s hs => hin2 s hs
    rw [this]
    simp_rw [sub_smul]
    rw [integral_sub (f := fun s => ssp2_h t • β s) (g := fun s => ssp2_h s • β s) (hβ.smul _)
      (hβ.continuousOn_smul hhc isCompact_Icc), integral_smul]
  rw [e1, e2] at hswap
  rw [hμ] at *
  rw [← sub_eq_iff_eq_add'.1 hswap.symm]

/-! ### The pathwise identity in the original time -/

/-- The weighted noise `J w t = h(t) w_t - ∫_0^t h'(s) w_s ds` (`= ∫_0^t (1+u)^{-1/2} dw_u`). -/
def ssp2_J {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ℝ≥0 → E) (t : ℝ) : E :=
  ssp2_h t • w (Real.toNNReal t) - ∫ s in Set.Icc 0 t, ssp2_h' s • w (Real.toNNReal s)

theorem ssp2_J_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ℝ≥0 → E) :
    ssp2_J w 0 = w 0 := by
  simp [ssp2_J, ssp2_h_zero]

theorem ssp2_pathwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x w : ℝ≥0 → E) (hxc : Continuous x) (hwc : Continuous w) (β : ℝ → E) (c : ℝ) {T : ℝ}
    (hβ : IntegrableOn β (Set.Icc 0 T))
    (hx : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      x t = x 0 + (∫ s in Set.Icc (0 : ℝ) t, β s) + c • (w t - w 0))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ T) :
    ssp2_h t • x (Real.toNNReal t) = x 0 +
      (∫ s in Set.Icc 0 t, (ssp2_h s • β s + ssp2_h' s • x (Real.toNNReal s))) +
      c • (ssp2_J w t - ssp2_J w 0) := by
  have hβt : IntegrableOn β (Set.Icc 0 t) := hβ.mono_set (Set.Icc_subset_Icc_right ht)
  have hXc : Continuous fun s : ℝ => x (Real.toNNReal s) := hxc.comp continuous_real_toNNReal
  have hWc : Continuous fun s : ℝ => w (Real.toNNReal s) := hwc.comp continuous_real_toNNReal
  have hh'c : ContinuousOn ssp2_h' (Set.Icc 0 t) := ssp2_continuousOn_h'.mono Set.Icc_subset_Ici_self
  have hhc : ContinuousOn ssp2_h (Set.Icc 0 t) := ssp2_continuousOn_h.mono Set.Icc_subset_Ici_self
  -- the primitive `B`
  set B : ℝ → E := fun s => ∫ q in Set.Icc 0 s, β q with hBdef
  have hBeq : ∀ s ∈ Set.Icc (0 : ℝ) t, B s = x (Real.toNNReal s) - x 0 -
      c • (w (Real.toNNReal s) - w 0) := by
    intro s hs
    have h1 := hx (Real.toNNReal s) (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans ht)
    rw [Real.coe_toNNReal _ hs.1] at h1
    simp only [hBdef]
    rw [h1]; abel
  have hBc : ContinuousOn B (Set.Icc 0 t) := by
    have : ContinuousOn (fun s : ℝ => x (Real.toNNReal s) - x 0 -
        c • (w (Real.toNNReal s) - w 0)) (Set.Icc 0 t) :=
      (((hXc.sub continuous_const).sub
        ((hWc.sub continuous_const).const_smul c))).continuousOn
    exact this.congr hBeq
  have hIBP := ssp2_ibp ht0 hβt
  -- integrability of the pieces
  have iA : IntegrableOn (fun s => ssp2_h s • β s) (Set.Icc 0 t) :=
    hβt.continuousOn_smul hhc isCompact_Icc
  have iB : IntegrableOn (fun s => ssp2_h' s • B s) (Set.Icc 0 t) :=
    (hh'c.smul hBc).integrableOn_Icc
  have iX : IntegrableOn (fun s => ssp2_h' s • x (Real.toNNReal s)) (Set.Icc 0 t) :=
    (hh'c.smul hXc.continuousOn).integrableOn_Icc
  have iW : IntegrableOn (fun s => ssp2_h' s • w (Real.toNNReal s)) (Set.Icc 0 t) :=
    (hh'c.smul hWc.continuousOn).integrableOn_Icc
  have iC : IntegrableOn (fun s => ssp2_h' s • x 0) (Set.Icc 0 t) :=
    (hh'c.smul continuousOn_const).integrableOn_Icc
  have iD : IntegrableOn (fun s => ssp2_h' s • w 0) (Set.Icc 0 t) :=
    (hh'c.smul continuousOn_const).integrableOn_Icc
  have hint : ∫ s in Set.Icc 0 t, ssp2_h' s = ssp2_h t - 1 := by
    rw [ssp2_integral_h' le_rfl ht0, ssp2_h_zero]
  -- the integral of `h' x`
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, ssp2_h' s • x (Real.toNNReal s) =
      (ssp2_h' s • x 0 + ssp2_h' s • B s) +
        (c • (ssp2_h' s • w (Real.toNNReal s)) - c • (ssp2_h' s • w 0)) := by
    intro s hs
    have h1 : x (Real.toNNReal s) = x 0 + B s + c • (w (Real.toNNReal s) - w 0) := by
      rw [hBeq s hs]; abel
    rw [h1]; module
  have hXint : ∫ s in Set.Icc 0 t, ssp2_h' s • x (Real.toNNReal s) =
      (ssp2_h t - 1) • x 0 + (∫ s in Set.Icc 0 t, ssp2_h' s • B s) +
        (c • (∫ s in Set.Icc 0 t, ssp2_h' s • w (Real.toNNReal s)) -
          c • (ssp2_h t - 1) • w 0) := by
    rw [setIntegral_congr_fun measurableSet_Icc hpt]
    rw [integral_add (f := fun s => ssp2_h' s • x 0 + ssp2_h' s • B s)
      (g := fun s => c • (ssp2_h' s • w (Real.toNNReal s)) - c • (ssp2_h' s • w 0))
      (iC.add iB) ((iW.smul c).sub (iD.smul c)),
      integral_add (f := fun s => ssp2_h' s • x 0) (g := fun s => ssp2_h' s • B s) iC iB,
      integral_sub (f := fun s => c • (ssp2_h' s • w (Real.toNNReal s)))
        (g := fun s => c • (ssp2_h' s • w 0)) (iW.smul c) (iD.smul c),
      integral_smul, integral_smul, integral_smul_const, integral_smul_const, hint]
  have hsplit : ∫ s in Set.Icc 0 t, (ssp2_h s • β s + ssp2_h' s • x (Real.toNNReal s)) =
      (∫ s in Set.Icc 0 t, ssp2_h s • β s) + ∫ s in Set.Icc 0 t, ssp2_h' s • x (Real.toNNReal s) :=
    integral_add iA iX
  have hXt := hx (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht0]; exact ht)
  rw [Real.coe_toNNReal _ ht0] at hXt
  rw [hsplit, hXint, ssp2_J, ssp2_J_zero]
  have hBt : ∫ s in Set.Icc 0 t, β s = B t := rfl
  rw [hBt] at hXt
  rw [hXt]
  have hI2 : (∫ s in Set.Icc 0 t, ssp2_h' s • B s) = ∫ q in Set.Icc 0 t, ssp2_h' q • ∫ s in Set.Icc 0 q, β s := rfl
  rw [hI2]
  rw [hBt] at hIBP
  linear_combination (norm := module) hIBP

/-! ### Change of variables `t = e^r - 1` -/

theorem ssp2_image_exp_sub_one {τ : ℝ} (hτ : 0 ≤ τ) :
    (fun r : ℝ => Real.exp r - 1) '' Set.Icc 0 τ = Set.Icc 0 (Real.exp τ - 1) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨?_, by linarith [Real.exp_le_exp.2 hr.2]⟩
    have := Real.exp_le_exp.2 hr.1
    rw [Real.exp_zero] at this; linarith
  · intro hy
    refine ⟨Real.log (1 + y), ⟨Real.log_nonneg (by linarith [hy.1]), ?_⟩, ?_⟩
    · rw [← Real.log_exp τ]
      exact Real.log_le_log (by linarith [hy.1]) (by linarith [hy.2])
    · simp only
      rw [Real.exp_log (by linarith [hy.1])]; ring

theorem ssp2_h_exp (r : ℝ) : ssp2_h (Real.exp r - 1) = Real.exp (-r / 2) := by
  simp only [ssp2_h]
  rw [show 1 + (Real.exp r - 1) = Real.exp r by ring, ← Real.exp_mul]
  congr 1; ring

theorem ssp2_h'_exp (r : ℝ) :
    ssp2_h' (Real.exp r - 1) = -(1 / 2 : ℝ) * Real.exp (-(3 * r) / 2) := by
  simp only [ssp2_h']
  rw [show 1 + (Real.exp r - 1) = Real.exp r by ring, ← Real.exp_mul]
  congr 2; ring

theorem ssp2_cov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : ℝ≥0 → E) {β : ℝ → E} {T τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : Real.exp τ - 1 ≤ T)
    (hβ : IntegrableOn β (Set.Icc 0 T)) :
    IntegrableOn (fun r => Real.exp (r / 2) • β (Real.exp r - 1)) (Set.Icc 0 τ) ∧
    ∫ s in Set.Icc 0 (Real.exp τ - 1), (ssp2_h s • β s + ssp2_h' s • x (Real.toNNReal s)) =
      ∫ r in Set.Icc 0 τ, (Real.exp (r / 2) • β (Real.exp r - 1) -
        (1 / 2 : ℝ) • (Real.exp (-r / 2) • x (Real.toNNReal (Real.exp r - 1)))) := by
  have hd : ∀ r ∈ Set.Icc (0 : ℝ) τ, HasDerivWithinAt (fun r : ℝ => Real.exp r - 1) (Real.exp r)
      (Set.Icc 0 τ) r := fun r _ => ((Real.hasDerivAt_exp r).sub_const 1).hasDerivWithinAt
  have hinj : Set.InjOn (fun r : ℝ => Real.exp r - 1) (Set.Icc 0 τ) := fun a _ b _ hab =>
    Real.exp_injective (by simpa using hab)
  have hsub : Set.Icc 0 (Real.exp τ - 1) ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right hτT
  have hhc : ContinuousOn ssp2_h (Set.Icc 0 (Real.exp τ - 1)) :=
    ssp2_continuousOn_h.mono Set.Icc_subset_Ici_self
  have hg : IntegrableOn (fun u => ssp2_h u • β u) (Set.Icc 0 (Real.exp τ - 1)) :=
    (hβ.mono_set hsub).continuousOn_smul hhc isCompact_Icc
  have hpt1 : ∀ r : ℝ, |Real.exp r| • (ssp2_h (Real.exp r - 1) • β (Real.exp r - 1)) =
      Real.exp (r / 2) • β (Real.exp r - 1) := by
    intro r
    rw [abs_of_pos (Real.exp_pos r), ssp2_h_exp, smul_smul, ← Real.exp_add]
    congr 2; ring
  refine ⟨?_, ?_⟩
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj _).1
      (by rw [ssp2_image_exp_sub_one hτ0]; exact hg)
    simpa only [hpt1] using this
  · rw [← ssp2_image_exp_sub_one hτ0,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj]
    refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
    simp only [smul_add]
    rw [hpt1 r, ssp2_h'_exp, abs_of_pos (Real.exp_pos r), smul_smul, smul_smul, sub_eq_add_neg]
    have e : Real.exp r * (-(1 / 2 : ℝ) * Real.exp (-(3 * r) / 2)) = -(1 / 2 * Real.exp (-r / 2)) := by
      have h1 : Real.exp r * Real.exp (-(3 * r) / 2) = Real.exp (-r / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc _ = -(1 / 2 : ℝ) * (Real.exp r * Real.exp (-(3 * r) / 2)) := by ring
        _ = _ := by rw [h1]; ring
    rw [e]
    module

/-! ### The time-changed Brownian motion: Itô identification -/

section Brownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The deterministic integrand `1_{s ≥ 0} (1+s)^{-1/2} e_k`. -/
def ssp2_Phi (k : ι) : ℝ → Ω → ι → ℝ := fun s _ j =>
  Set.indicator (Set.Ici (0 : ℝ)) ssp2_h s * (if j = k then 1 else 0)

/-- The direction `e_k` as a vector of `ℝ^ι → ℝ`-coefficients. -/
def ssp2_sig (k : ι) (j : ι) : ℝ := if j = k then 1 else 0

theorem ssp2_h_le_one {s : ℝ} (hs : 0 ≤ s) : ssp2_h s ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)

theorem ssp2_h_pos' {s : ℝ} (hs : 0 ≤ s) : 0 < ssp2_h s :=
  Real.rpow_pos_of_pos (by linarith) _

theorem ssp2_measurable_h : Measurable ssp2_h :=
  (measurable_const.add measurable_id).pow_const _

theorem ssp2_isProgressive_Phi {ℱ : Filtration ℝ mΩ} (k : ι) :
    IsProgressive ℱ (ssp2_Phi (Ω := Ω) k) := by
  have hk : ∀ j : ι, IsProgressive ℱ (fun (s : ℝ) (_ : Ω) =>
      Set.indicator (Set.Ici (0 : ℝ)) ssp2_h s * (if j = k then (1:ℝ) else 0)) := by
    intro j i
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    have hm : Measurable (fun s : ℝ =>
        Set.indicator (Set.Ici (0 : ℝ)) ssp2_h s * (if j = k then (1:ℝ) else 0)) :=
      ((ssp2_measurable_h.indicator measurableSet_Ici).mul_const _)
    exact hm.comp (measurable_subtype_coe.comp measurable_fst)
  exact isProgressive_pi hk

theorem ssp2_isProgressiveL2_Phi (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (k : ι) : IsProgressiveL2 P ℱ (ssp2_Phi k) := by
  refine IsProgressiveL2.of_bounded P (ssp2_isProgressive_Phi k) 1 fun s ω j => ?_
  simp only [ssp2_Phi]
  by_cases hs : 0 ≤ s
  · rw [Set.indicator_of_mem (Set.mem_Ici.2 hs), abs_mul, abs_of_pos (ssp2_h_pos' hs)]
    have : |(if j = k then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc ssp2_h s * |(if j = k then (1:ℝ) else 0)| ≤ 1 * 1 :=
          mul_le_mul (ssp2_h_le_one hs) this (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [Set.indicator_of_notMem (by simpa using hs)]; simp

theorem ssp2_fderiv_f (s : ℝ) : fderiv ℝ (fun y : ℝ => ssp2_h s * y) =
    fun _ => ssp2_h s • ContinuousLinearMap.id ℝ ℝ :=
  funext fun x => ((hasFDerivAt_id x).const_mul (ssp2_h s)).fderiv

theorem ssp2_fderiv2_f (s x : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y : ℝ => ssp2_h s * y)) x = 0 := by
  rw [ssp2_fderiv_f s]; simp

/-- `f(t,x) = h(t) x` is `C^{1,2}` on `[0,T]`. -/
theorem ssp2_isC12On {T : ℝ} (hT : 0 < T) :
    IsC12On T Set.univ (fun (s : ℝ) (x : ℝ) => ssp2_h s * x) := by
  have hIcc : Set.Icc 0 T ⊆ Set.Ici (0 : ℝ) := Set.Icc_subset_Ici_self
  have hhc : ContinuousOn ssp2_h (Set.Icc 0 T) := ssp2_continuousOn_h.mono hIcc
  have hh'c : ContinuousOn ssp2_h' (Set.Icc 0 T) := ssp2_continuousOn_h'.mono hIcc
  have hfd : ∀ (s : ℝ) (x : ℝ), HasFDerivAt (fun y : ℝ => ssp2_h s * y)
      (ssp2_h s • ContinuousLinearMap.id ℝ ℝ) x := fun s x =>
    (hasFDerivAt_id x).const_mul (ssp2_h s)
  have hfd' : ∀ s : ℝ, fderiv ℝ (fun y : ℝ => ssp2_h s * y) =
      fun _ => ssp2_h s • ContinuousLinearMap.id ℝ ℝ := fun s => funext fun x => (hfd s x).fderiv
  have hfd2 : ∀ (s x : ℝ), fderiv ℝ (fderiv ℝ (fun y : ℝ => ssp2_h s * y)) x = 0 := by
    intro s x; rw [hfd' s]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun p : ℝ × ℝ => ssp2_h p.1) (Set.Icc 0 T ×ˢ Set.univ) :=
      hhc.comp continuousOn_fst (fun p hp => hp.1)
    exact h1.mul continuousOn_snd
  · intro t _ x _; exact hfd t x |>.differentiableAt.hasFDerivAt
  · intro t _ x _
    rw [hfd' t, show fderiv ℝ (fun _ : ℝ => ssp2_h t • ContinuousLinearMap.id ℝ ℝ) x = 0 from by simp]
    exact hasFDerivAt_const _ x
  · simp only [hfd']
    exact (hhc.comp continuousOn_fst (fun p hp => hp.1)).smul continuousOn_const
  · simp only [hfd2]; exact continuousOn_const
  · intro x _ t ht
    have : HasDerivAt (fun r : ℝ => ssp2_h r * x) (ssp2_h' t * x) t :=
      (ssp2_hasDerivAt_h (by linarith [ht.1])).mul_const x
    exact this.differentiableAt.differentiableWithinAt.hasDerivWithinAt
  · have hder : ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ),
        derivWithin (fun r : ℝ => ssp2_h r * p.2) (Set.Icc 0 T) p.1 = ssp2_h' p.1 * p.2 := by
      intro p hp
      have : HasDerivAt (fun r : ℝ => ssp2_h r * p.2) (ssp2_h' p.1 * p.2) p.1 :=
        (ssp2_hasDerivAt_h (by linarith [hp.1.1])).mul_const p.2
      exact this.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT p.1 hp.1)
    refine ContinuousOn.congr ?_ hder
    exact (hh'c.comp continuousOn_fst (fun p hp => hp.1)).mul continuousOn_snd

section Ito

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → ι → ℝ}

theorem ssp2_itoDrift_eq {T : ℝ} (hT : 0 < T) (k : ι) (s : ℝ) (hs : s ∈ Set.Icc 0 T)
    (X' : ℝ → Ω → ℝ) (ζ : Ω) :
    itoDrift T (fun (s : ℝ) (x : ℝ) => ssp2_h s * x) X' (fun _ _ => (0 : ℝ))
      (fun _ _ => ssp2_sig k) s ζ = ssp2_h' s * X' s ζ := by
  unfold itoDrift
  have h1 : derivWithin (fun r : ℝ => ssp2_h r * X' s ζ) (Set.Icc 0 T) s = ssp2_h' s * X' s ζ := by
    have : HasDerivAt (fun r : ℝ => ssp2_h r * X' s ζ) (ssp2_h' s * X' s ζ) s :=
      (ssp2_hasDerivAt_h (by linarith [hs.1])).mul_const _
    exact this.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT s hs)
  simp only [ssp2_fderiv2_f, ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero, map_zero]
  rw [h1]; ring

theorem ssp2_itoIntegrand_eq {T : ℝ} (k : ι) (X' : ℝ → Ω → ℝ) :
    itoIntegrand T Set.univ (fun (s : ℝ) (x : ℝ) => ssp2_h s * x) X' (fun _ _ => ssp2_sig k) =
      stopIntegrand (ssp2_Phi k) (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) := by
  funext s ζ j
  by_cases hs : s ∈ Set.Icc 0 T
  · have e1 : itoIntegrand T Set.univ (fun (s : ℝ) (x : ℝ) => ssp2_h s * x) X'
        (fun _ _ => ssp2_sig k) s ζ j = ssp2_h s * ssp2_sig k j := by
      simp [itoIntegrand, Set.indicator, hs, ssp2_fderiv_f]
    have e2 : stopIntegrand (ssp2_Phi k) (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) s ζ j =
        ssp2_h s * ssp2_sig k j := by
      have : ((s : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := by exact_mod_cast hs.2
      simp [stopIntegrand, Set.indicator, this, ssp2_Phi, hs.1, ssp2_sig]
    rw [e1, e2]
  · have e1 : itoIntegrand T Set.univ (fun (s : ℝ) (x : ℝ) => ssp2_h s * x) X'
        (fun _ _ => ssp2_sig k) s ζ j = 0 := by
      simp [itoIntegrand, Set.indicator, hs]
    have e2 : stopIntegrand (ssp2_Phi k) (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) s ζ j = 0 := by
      by_cases h0 : 0 ≤ s
      · have : ¬ ((s : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_le_coe]; intro h; exact hs ⟨h0, h⟩
        simp [stopIntegrand, Set.indicator, this]
      · have hΦ0 : ssp2_Phi (Ω := Ω) k s ζ j = 0 := by simp [ssp2_Phi, h0]
        by_cases hsT : ((s : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ)
        · simp [stopIntegrand, Set.indicator, hsT, hΦ0]
        · simp [stopIntegrand, Set.indicator, hsT]
    rw [e1, e2]

/-- Itô's formula for `h(t) W^k_t` identifies the Itô integral of `h e_k` with `J`. -/
theorem ssp2_ito_fixed (hW : IsBrownianFiltration P ℱ W') (k : ι) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ζ ∂P, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      itoIntegral P ℱ W' (ssp2_Phi k) t ζ = ssp2_J (fun s => W' s ζ k) t := by
  classical
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ≥0 → Ω → ℝ, X = fun t ζ => W' t ζ k := ⟨_, rfl⟩
  have hXmeas : ∀ t, Measurable (X t) := fun t =>
    by rw [hXdef]; exact (measurable_pi_apply k).comp ((hW.adapted t).mono (ℱ.le _) le_rfl)
  have hX0 : X 0 = fun _ => 0 := funext fun ζ => by simp [hXdef, hW.zero]
  have hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0) := fun t => by rw [hX0]; exact measurable_const
  have hb : IsProgressive ℱ (ofNNRealTime (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ))) :=
    isProgressive_const ℱ 0
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn
      (fun s : ℝ => (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (Real.toNNReal s) ζ) (Set.Icc 0 T) :=
    ae_of_all _ fun _ => integrableOn_zero
  have hX : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ζ = X 0 ζ + (∫ s in Set.Icc (0 : ℝ) t,
        (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) (Real.toNNReal s) ζ) +
        ∑ j, (W' t ζ j - W' 0 ζ j) • ssp2_sig k j := by
    refine ae_of_all _ fun ζ t _ => ?_
    simp [hXdef, hW.zero, ssp2_sig, mul_ite]
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hW hT.le
    (fun (s : ℝ) (x : ℝ) => ssp2_h s * x) (ssp2_isC12On hT) (ssp2_sig k) X hXmeas hX₀
    (fun _ _ => (0 : ℝ)) hb hbint hX
  have hΦ := ssp2_isProgressiveL2_Phi P ℱ k
  have hτ : IsStoppingTime ℱ (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) := isStoppingTime_const_real T
  have hΨ := hΦ.stopIntegrand hτ
  have hΨeq := ssp2_itoIntegrand_eq (Ω := Ω) (T := T) k (ofNNRealTime X)
  rw [← hΨeq] at hΨ
  filter_upwards [hito, localItoIntegral_eq_itoIntegral hW hΨ,
    itoIntegral_stopIntegrand hW hΦ hτ] with ζ h1 h2 h3 t ht0 htT
  obtain ⟨_, h1⟩ := h1
  have hle : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal _ ht0]; exact htT
  have h4 := h1 (Real.toNNReal t) hle
  rw [Real.coe_toNNReal _ ht0] at h4
  rw [hX0] at h4
  have hb0 : ofNNRealTime (fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) = fun _ _ => (0 : ℝ) := rfl
  rw [hb0] at h4
  have hI : itoIntegral P ℱ W' (ssp2_Phi k) t ζ =
      localItoIntegral P ℱ W' (itoIntegrand T Set.univ (fun (s : ℝ) (x : ℝ) => ssp2_h s * x)
        (ofNNRealTime X) (fun _ _ => ssp2_sig k)) t ζ := by
    rw [h2 t, hΨeq, h3 t]
    exact (stoppedProcess_eq_of_le (by exact_mod_cast htT)).symm
  rw [hI]
  have hdr : ∫ s in Set.Icc (0 : ℝ) t, itoDrift T (fun (s : ℝ) (x : ℝ) => ssp2_h s * x)
      (ofNNRealTime X) (fun _ _ => (0 : ℝ)) (fun _ _ => ssp2_sig k) s ζ =
      ∫ s in Set.Icc (0 : ℝ) t, ssp2_h' s • W' (Real.toNNReal s) ζ k := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have := ssp2_itoDrift_eq hT k s ⟨hs.1, hs.2.trans htT⟩ (ofNNRealTime X) ζ
    simpa [ofNNRealTime, hXdef] using this
  rw [hdr] at h4
  simp only [ssp2_J, smul_eq_mul]
  simp only [hXdef, zero_add, mul_zero] at h4
  simp only [smul_eq_mul] at h4
  have e : ofNNRealTime (fun t ζ => W' t ζ k) = ofNNRealTime X := by rw [hXdef]
  rw [e] at h4
  linarith [h4]

theorem ssp2_ito_ident (hW : IsBrownianFiltration P ℱ W') (k : ι) :
    ∀ᵐ ζ ∂P, ∀ t : ℝ, 0 ≤ t →
      itoIntegral P ℱ W' (ssp2_Phi k) t ζ = ssp2_J (fun s => W' s ζ k) t := by
  have h := fun n : ℕ => ssp2_ito_fixed hW k (T := (n : ℝ) + 1) (by positivity)
  filter_upwards [ae_all_iff.2 h] with ζ hζ t ht0
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hζ n t ht0 (by linarith)

end Ito

/-- The time-changed filtration `ℱ̄_τ = ℱ_{e^τ - 1}`. -/
def ssp2_fil (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq τ := ℱ (Real.exp τ - 1)
  mono' := fun a b hab => ℱ.mono (by linarith [Real.exp_le_exp.2 hab])
  le' := fun τ => ℱ.le _

/-- The time-changed Brownian motion `W̄_τ = ∫_0^{e^τ-1} (1+u)^{-1/2} dW_u`, in its pathwise form. -/
def ssp2_Wb (W' : ℝ≥0 → Ω → ι → ℝ) (τ : ℝ≥0) (ζ : Ω) (k : ι) : ℝ :=
  ssp2_J (fun s => W' s ζ k) (Real.exp τ - 1)

theorem ssp2_measurable_h' : Measurable ssp2_h' :=
  measurable_const.mul ((measurable_const.add measurable_id).pow_const _)

theorem ssp2_continuousOn_J {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℝ≥0 → E} (hw : Continuous w) : ContinuousOn (ssp2_J w) (Set.Ici 0) := by
  have hwc : Continuous fun s : ℝ => w (Real.toNNReal s) := hw.comp continuous_real_toNNReal
  have hF : Continuous fun s : ℝ => ssp2_h' (max s 0) • w (Real.toNNReal s) := by
    have h1 : Continuous fun s : ℝ => ssp2_h' (max s 0) :=
      ssp2_continuousOn_h'.comp_continuous (continuous_id.max continuous_const)
        (fun s => Set.mem_Ici.2 (le_max_right _ _))
    exact h1.smul hwc
  have hprim : Continuous fun t : ℝ => ∫ x in (0 : ℝ)..t, ssp2_h' (max x 0) • w (Real.toNNReal x) :=
    intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 0
  have h1 : ContinuousOn (fun t : ℝ => ssp2_h t • w (Real.toNNReal t)) (Set.Ici 0) :=
    ssp2_continuousOn_h.smul hwc.continuousOn
  refine (h1.sub hprim.continuousOn).congr fun t ht => ?_
  have ht' : 0 ≤ t := ht
  simp only [ssp2_J]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht']
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le ht'] at hx
  simp only [max_eq_left hx.1]

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → ι → ℝ}

theorem ssp2_Wb_zero (hW : IsBrownianFiltration P ℱ W') (ζ : Ω) : ssp2_Wb W' 0 ζ = 0 := by
  funext k
  simp [ssp2_Wb, ssp2_J_zero, hW.zero]

theorem ssp2_continuous_Wb (hW : IsBrownianFiltration P ℱ W') (ζ : Ω) :
    Continuous fun τ : ℝ≥0 => ssp2_Wb W' τ ζ := by
  refine continuous_pi fun k => ?_
  have hw : Continuous fun s : ℝ≥0 => W' s ζ k := (continuous_apply k).comp (hW.cont ζ)
  exact (ssp2_continuousOn_J hw).comp_continuous
    ((Real.continuous_exp.comp NNReal.continuous_coe).sub continuous_const)
    (fun τ => Set.mem_Ici.2 (by
      have := Real.add_one_le_exp (τ : ℝ)
      have h0 := τ.2
      linarith))

theorem ssp2_measurable_Wb (hW : IsBrownianFiltration P ℱ W') (τ : ℝ≥0) (k : ι) :
    Measurable fun ζ => ssp2_Wb W' τ ζ k := by
  have hm : ∀ t : ℝ≥0, Measurable fun ζ => W' t ζ k := fun t =>
    (measurable_pi_apply k).comp ((hW.adapted t).mono (ℱ.le _) le_rfl)
  have hu : Measurable (Function.uncurry fun (s : ℝ) (ζ : Ω) => W' (Real.toNNReal s) ζ k) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ζ => (continuous_apply k).comp ((hW.cont ζ).comp continuous_real_toNNReal))
      (fun s => hm _)
  have hH : Measurable fun p : ℝ × Ω => ssp2_h' p.1 * W' (Real.toNNReal p.1) p.2 k :=
    (ssp2_measurable_h'.comp measurable_fst).mul hu
  have hI := measurable_setIntegral_Icc _ hH 0 (Real.exp τ - 1)
  simp only [ssp2_Wb, ssp2_J, smul_eq_mul]
  exact (measurable_const.mul (hm _)).sub hI

theorem ssp2_h_sq {s : ℝ} (hs : 0 ≤ s) : ssp2_h s ^ 2 = (1 + s)⁻¹ := by
  simp only [ssp2_h]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_neg_one]
  norm_num

theorem ssp2_integral_inv {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, (1 + s)⁻¹ = Real.log (1 + t) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 + x)⁻¹ x := by
    intro x hx
    rw [Set.uIcc_of_le ht] at hx
    have := ((hasDerivAt_id x).const_add 1).log (by simp; linarith [hx.1])
    simpa using this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · refine ContinuousOn.intervalIntegrable ?_
    intro x hx
    rw [Set.uIcc_of_le ht] at hx
    exact ((continuousAt_const.add continuousAt_id).inv₀ (by simp; linarith [hx.1])).continuousWithinAt

theorem ssp2_cov_Phi (k l : ι) {t : ℝ} (ht : 0 ≤ t) (ζ : Ω) :
    covProcess (ssp2_Phi (Ω := Ω) k) (ssp2_Phi l) t ζ = if k = l then Real.log (1 + t) else 0 := by
  unfold covProcess
  by_cases hkl : k = l
  · subst hkl
    simp only [if_true]
    rw [← ssp2_integral_inv ht]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [ssp2_Phi, Set.indicator_of_mem (Set.mem_Ici.2 hs.1)]
    rw [Finset.sum_eq_single k]
    · simp only [if_true, mul_one]; rw [← sq, ssp2_h_sq hs.1]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ k) h
  · simp only [hkl, if_false]
    have : ∀ s ∈ Set.Icc (0 : ℝ) t, ∑ j, ssp2_Phi (Ω := Ω) k s ζ j * ssp2_Phi l s ζ j = 0 := by
      intro s hs
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = k
      · subst hj; simp [ssp2_Phi, hkl, Ne.symm hkl]
      · simp [ssp2_Phi, hj]
    rw [setIntegral_congr_fun measurableSet_Icc this]
    simp

theorem ssp2_Wb_ae (hW : IsBrownianFiltration P ℱ W') (k : ι) (τ : ℝ) :
    (fun ζ => ofNNRealTime (ssp2_Wb W') τ ζ k) =ᵐ[P]
      itoIntegral P ℱ W' (ssp2_Phi k) (Real.exp τ - 1) := by
  by_cases hτ : 0 ≤ τ
  · filter_upwards [ssp2_ito_ident hW k] with ζ h
    have h1 := h (Real.exp τ - 1) (by linarith [Real.add_one_le_exp τ])
    rw [h1]
    simp only [ofNNRealTime_apply, ssp2_Wb, Real.coe_toNNReal _ hτ]
  · refine Filter.Eventually.of_forall fun ζ => ?_
    have h1 : Real.exp τ - 1 ≤ 0 := by
      have := Real.exp_lt_one_iff.2 (not_le.1 hτ); linarith
    rw [itoIntegral_of_nonpos P ℱ W' _ h1]
    show ssp2_Wb W' (Real.toNNReal τ) ζ k = 0
    rw [Real.toNNReal_of_nonpos (not_le.1 hτ).le, ssp2_Wb_zero hW ζ]
    rfl

theorem ssp2_martingale_timechange {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ P) :
    Martingale (fun τ => f (Real.exp τ - 1)) (ssp2_fil ℱ) P :=
  ⟨fun τ => hf.1 (Real.exp τ - 1), fun i j hij =>
    hf.2 (Real.exp i - 1) (Real.exp j - 1) (by linarith [Real.exp_le_exp.2 hij])⟩

theorem ssp2_measurable_Wb_fil (hW : IsBrownianFiltration P ℱ W') (k : ι) (τ : ℝ) :
    Measurable[ssp2_fil ℱ τ] (fun ζ => ofNNRealTime (ssp2_Wb W') τ ζ k) := by
  have h1 : Measurable[ℱ (Real.exp τ - 1)] (itoIntegral P ℱ W' (ssp2_Phi k) (Real.exp τ - 1)) :=
    adapted_itoIntegral P ℱ W' (ssp2_Phi k) (Real.exp τ - 1)
  have h2 : Measurable fun ζ => ofNNRealTime (ssp2_Wb W') τ ζ k :=
    ssp2_measurable_Wb hW _ k
  exact hW.complete.measurable_of_ae_eq (Real.exp τ - 1) h1 h2 (ssp2_Wb_ae hW k τ).symm

theorem ssp2_brownian (hW : IsBrownianFiltration P ℱ W') :
    IsBrownianFiltration P (ssp2_fil ℱ) (ssp2_Wb W') := by
  refine levy_characterization P (ssp2_fil ℱ) (fun τ s hs h0 => hW.complete (Real.exp τ - 1) s hs h0)
    (ssp2_Wb W') ?_ (ssp2_Wb_zero hW) (ssp2_continuous_Wb hW) ?_ ?_
  · intro t
    refine (@measurable_pi_iff Ω ι (fun _ => ℝ) (ssp2_fil ℱ (t : ℝ)) _ _).2 fun k => ?_
    have := ssp2_measurable_Wb_fil hW k (t : ℝ)
    simpa [ofNNRealTime_apply] using this
  · intro k
    refine martingale_congr_ae (ssp2_martingale_timechange
      (martingale_itoIntegral hW (ssp2_isProgressiveL2_Phi P ℱ k)))
      (fun τ => (ssp2_measurable_Wb_fil hW k τ).stronglyMeasurable) fun τ => ssp2_Wb_ae hW k τ
  · intro k l
    have hM := martingale_itoIntegral_mul_sub hW (ssp2_isProgressiveL2_Phi P ℱ k)
      (ssp2_isProgressiveL2_Phi P ℱ l)
    refine martingale_congr_ae (ssp2_martingale_timechange hM)
      (fun τ => (((ssp2_measurable_Wb_fil hW k τ).mul (ssp2_measurable_Wb_fil hW l τ)).sub
        measurable_const).stronglyMeasurable) fun τ => ?_
    filter_upwards [ssp2_Wb_ae hW k τ, ssp2_Wb_ae hW l τ] with ζ h1 h2
    rw [h1, h2]
    by_cases hτ : 0 ≤ τ
    · rw [ssp2_cov_Phi k l (by linarith [Real.add_one_le_exp τ]) ζ, max_eq_left hτ]
      have : (1 + (Real.exp τ - 1)) = Real.exp τ := by ring
      rw [this, Real.log_exp]
    · have h1 : Real.exp τ - 1 ≤ 0 := by
        have := Real.exp_lt_one_iff.2 (not_le.1 hτ); linarith
      have hcov : covProcess (ssp2_Phi (Ω := Ω) k) (ssp2_Phi l) (Real.exp τ - 1) ζ = 0 := by
        unfold covProcess
        rcases h1.lt_or_eq with h | h
        · rw [Set.Icc_eq_empty (by linarith)]; simp
        · rw [h]; simp
      rw [hcov, max_eq_right (not_le.1 hτ).le]
      split_ifs <;> simp

end Brownian

/-! ### Assembly: pieces -/

section Assembly

variable {Ω : Type*} {N : ℕ}

theorem ssp2_ssPath_apply {X : ℝ≥0 → Ω → EucConfig d N} {r : ℝ} (hr : 0 ≤ r) (ζ : Ω) :
    ssPath X (Real.toNNReal r) ζ = fun i => Real.exp (-r / 2) • X (Real.toNNReal (Real.exp r - 1)) ζ i := by
  funext i
  simp only [ssPath, selfSimProcess, Real.coe_toNNReal _ hr]

theorem ssp2_ssPath_zero {X : ℝ≥0 → Ω → EucConfig d N} (ζ : Ω) : ssPath X 0 ζ = X 0 ζ := by
  funext i
  simp [ssPath, selfSimProcess]

theorem ssp2_exp_sub_one_le {T r : ℝ} (hr : r ≤ Real.log (1 + T)) (hT : 0 < T) :
    Real.exp r - 1 ≤ T := by
  have := (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < 1 + T)).1 hr
  linarith

theorem ssp2_collision_smul {c : ℝ} (hc : c ≠ 0) (x : EucConfig d N) :
    (fun i => c • x i) ∈ eucCollisionSet d N ↔ x ∈ eucCollisionSet d N := by
  simp only [eucCollisionSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact ⟨i, j, hij, smul_right_injective _ hc h⟩
  · rintro ⟨i, j, hij, h⟩
    exact ⟨i, j, hij, by simp only [h]⟩

theorem ssp2_continuous_ssPath {X : ℝ≥0 → Ω → EucConfig d N} (hXc : ∀ ζ, Continuous fun t => X t ζ)
    (ζ : Ω) : Continuous fun τ : ℝ≥0 => ssPath X τ ζ := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous fun τ : ℝ≥0 => Real.exp (-(τ : ℝ) / 2) :=
    Real.continuous_exp.comp ((NNReal.continuous_coe.neg).div_const 2)
  have h2 : Continuous fun τ : ℝ≥0 => X (Real.toNNReal (Real.exp (τ : ℝ) - 1)) ζ i :=
    (continuous_apply i).comp ((hXc ζ).comp (continuous_real_toNNReal.comp
      ((Real.continuous_exp.comp NNReal.continuous_coe).sub continuous_const)))
  exact h1.smul h2

theorem ssp2_noCollision {X : ℝ≥0 → Ω → EucConfig d N} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T : ℝ}
    (hT : 0 < T) (h : SSNoCollision P T X) :
    SSNoCollision P (Real.log (1 + T)) (ssPath X) := by
  filter_upwards [h] with ζ hζ t ht
  have hle : ((Real.toNNReal (Real.exp (t : ℝ) - 1) : ℝ≥0) : ℝ) ≤ T := by
    rw [Real.coe_toNNReal _ (by linarith [Real.add_one_le_exp (t : ℝ)])]
    exact ssp2_exp_sub_one_le ht hT
  have h1 := hζ _ hle
  have : ssPath X t ζ = fun i => Real.exp (-(t : ℝ) / 2) • X (Real.toNNReal (Real.exp (t : ℝ) - 1)) ζ i := by
    have := ssp2_ssPath_apply (X := X) (r := (t : ℝ)) t.2 ζ
    simpa using this
  rw [this, ssp2_collision_smul (Real.exp_pos _).ne']
  exact h1

theorem ssp2_ordered {X : ℝ≥0 → Ω → EucConfig d N} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T : ℝ}
    (hT : 0 < T) (h : SSOrdered P T X) :
    SSOrdered P (Real.log (1 + T)) (ssPath X) := by
  obtain ⟨π, hπ, hord⟩ := h
  refine ⟨π, hπ, ?_⟩
  filter_upwards [hord] with ζ hζ t ht j k k' hkk'
  have hle : ((Real.toNNReal (Real.exp (t : ℝ) - 1) : ℝ≥0) : ℝ) ≤ T := by
    rw [Real.coe_toNNReal _ (by linarith [Real.add_one_le_exp (t : ℝ)])]
    exact ssp2_exp_sub_one_le ht hT
  have h1 := hζ _ hle j k k' hkk'
  have : ssPath X t ζ = fun i => Real.exp (-(t : ℝ) / 2) • X (Real.toNNReal (Real.exp (t : ℝ) - 1)) ζ i := by
    have := ssp2_ssPath_apply (X := X) (r := (t : ℝ)) t.2 ζ
    simpa using this
  rw [this]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

theorem ssp2_occupation {X : ℝ≥0 → Ω → EucConfig d N} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {T : ℝ}
    (hT : 0 < T) (h : ∀ᵐ ζ ∂P, volume {r : ℝ | r ∈ Set.Icc 0 T ∧ X (Real.toNNReal r) ζ ∈ eucCollisionSet d N} = 0) :
    ∀ᵐ ζ ∂P, volume {r : ℝ | r ∈ Set.Icc 0 (Real.log (1 + T)) ∧
      ssPath X (Real.toNNReal r) ζ ∈ eucCollisionSet d N} = 0 := by
  filter_upwards [h] with ζ hζ
  set A : Set ℝ := {r : ℝ | r ∈ Set.Icc 0 T ∧ X (Real.toNNReal r) ζ ∈ eucCollisionSet d N} with hA
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => Real.log (1 + t)) A := by
    intro t ht
    have : (1 + t) ≠ 0 := by linarith [ht.1.1]
    exact (((differentiableAt_const (1 : ℝ)).add differentiableAt_id).log this).differentiableWithinAt
  have himg := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume : Measure ℝ) hdiff hζ
  refine measure_mono_null ?_ himg
  intro r hr
  obtain ⟨⟨hr0, hr1⟩, hcol⟩ := hr
  refine ⟨Real.exp r - 1, ⟨⟨by linarith [Real.add_one_le_exp r], ?_⟩, ?_⟩, ?_⟩
  · exact ssp2_exp_sub_one_le hr1 hT
  · rw [ssp2_ssPath_apply hr0, ssp2_collision_smul (Real.exp_pos _).ne'] at hcol
    exact hcol
  · simp only
    rw [show 1 + (Real.exp r - 1) = Real.exp r by ring, Real.log_exp]

theorem ssp2_adapted_ssPath {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {X : ℝ≥0 → Ω → EucConfig d N}
    (hXp : IsProgressive ℱ (ofNNRealTime X)) (r : ℝ) :
    Measurable[ssp2_fil ℱ r] (ofNNRealTime (ssPath X) r) := by
  have hm : Measurable[ℱ (Real.exp r - 1)] (ofNNRealTime X (Real.exp r - 1)) :=
    hXp.adapted (Real.exp r - 1)
  by_cases hr : 0 ≤ r
  · have : ofNNRealTime (ssPath X) r =
        fun ζ => Real.exp (-r / 2) • ofNNRealTime X (Real.exp r - 1) ζ := by
      funext ζ
      simp only [ofNNRealTime_apply]
      rw [ssp2_ssPath_apply hr]
      rfl
    rw [this]
    exact hm.const_smul (Real.exp (-r / 2))
  · have h1 : Real.exp r - 1 < 0 := by
      have := Real.exp_lt_one_iff.2 (not_le.1 hr); linarith
    have : ofNNRealTime (ssPath X) r = ofNNRealTime X (Real.exp r - 1) := by
      funext ζ
      simp only [ofNNRealTime_apply]
      rw [Real.toNNReal_of_nonpos (not_le.1 hr).le, Real.toNNReal_of_nonpos h1.le]
      exact ssp2_ssPath_zero ζ
    rw [this]
    exact hm

theorem ssp2_progressive_ssPath {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → EucConfig d N} (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hXc : ∀ ζ, Continuous fun t => X t ζ) :
    IsProgressive (ssp2_fil ℱ) (ofNNRealTime (ssPath X)) := by
  have hA : Adapted (ssp2_fil ℱ) (ofNNRealTime (ssPath X)) := ssp2_adapted_ssPath hXp
  have hc : ∀ ζ, Continuous fun r : ℝ => ofNNRealTime (ssPath X) r ζ := fun ζ =>
    (ssp2_continuous_ssPath hXc ζ).comp continuous_real_toNNReal
  exact (hA.stronglyAdapted.isStronglyProgressive_of_continuous hc).isProgressive

theorem ssp2_J_toLp {f : ℝ≥0 → Fin d → ℝ} (hf : ∀ j, Continuous fun u => f u j) {t : ℝ} (ht : 0 ≤ t) :
    ssp2_J (fun u => (WithLp.toLp 2 (f u) : Euc d)) t =
      WithLp.toLp 2 (fun j => ssp2_J (fun u => f u j) t) := by
  ext j
  have hcont : ContinuousOn (fun s : ℝ => ssp2_h' s • (WithLp.toLp 2 (f (Real.toNNReal s)) : Euc d))
      (Set.Icc 0 t) := by
    refine (ssp2_continuousOn_h'.mono Set.Icc_subset_Ici_self).smul ?_
    refine Continuous.continuousOn ?_
    refine (PiLp.continuous_toLp 2 _).comp ?_
    exact continuous_pi fun j => (hf j).comp continuous_real_toNNReal
  have hint := hcont.integrableOn_Icc (μ := (volume : Measure ℝ))
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) j) hint
  simp only [ssp2_J, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  congr 1
  simpa using this.symm

/-- The vector form of the time-changed noise. -/
def ssp2_WbV (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) : ℝ≥0 → Ω → Fin N → Euc d :=
  fun t ζ i => WithLp.toLp 2 (fun j => ssp2_Wb W' t ζ (i, j))

theorem ssp2_eqn_pointwise (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (invβ : ℝ) {T : ℝ} (hT : 0 < T)
    (X : ℝ≥0 → Ω → EucConfig d N) (W : ℝ≥0 → Ω → Fin N → Euc d)
    (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (ζ : Ω)
    (hXc : Continuous fun t => X t ζ) (hWc : Continuous fun t => W' t ζ)
    (hW0 : W' 0 ζ = 0) (hcoords : ∀ t i j, W' t ζ (i, j) = W t ζ i j)
    (heqn : ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (∀ i, IntegrableOn (fun r : ℝ =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) (X (Real.toNNReal r) ζ) i)
        (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, X t ζ i = X 0 ζ i +
        (∫ r in Set.Icc (0 : ℝ) t,
          particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) (X (Real.toNNReal r) ζ) i) +
        Real.sqrt (2 * invβ) • (W t ζ i - W 0 ζ i))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ Real.log (1 + T)) :
    (∀ i, IntegrableOn (fun r : ℝ => ssDrift d s N r (ssPath X (Real.toNNReal r) ζ) i)
      (Set.Icc 0 (t : ℝ))) ∧
    ∀ i, ssPath X t ζ i = ssPath X 0 ζ i +
      (∫ r in Set.Icc (0 : ℝ) t, ssDrift d s N r (ssPath X (Real.toNNReal r) ζ) i) +
      Real.sqrt (2 * invβ) • (ssp2_WbV W' t ζ i - ssp2_WbV W' 0 ζ i) := by
  have hτ0 : (0 : ℝ) ≤ t := t.2
  have hτT : Real.exp (t : ℝ) - 1 ≤ T := ssp2_exp_sub_one_le ht hT
  have hexp0 : 0 ≤ Real.exp (t : ℝ) - 1 := by linarith [Real.add_one_le_exp (t : ℝ)]
  -- the data for each particle
  have key : ∀ i : Fin N,
      IntegrableOn (fun r : ℝ => ssDrift d s N r (ssPath X (Real.toNNReal r) ζ) i)
        (Set.Icc 0 (t : ℝ)) ∧
      ssPath X t ζ i = ssPath X 0 ζ i +
        (∫ r in Set.Icc (0 : ℝ) t, ssDrift d s N r (ssPath X (Real.toNNReal r) ζ) i) +
        Real.sqrt (2 * invβ) • (ssp2_WbV W' t ζ i - ssp2_WbV W' 0 ζ i) := by
    intro i
    set x : ℝ≥0 → Euc d := fun u => X u ζ i with hxdef
    set wv : ℝ≥0 → Euc d := fun u => WithLp.toLp 2 (fun j => W' u ζ (i, j)) with hwvdef
    set β : ℝ → Euc d := fun r =>
      particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) (X (Real.toNNReal r) ζ) i with hβdef
    have hxc : Continuous x := (continuous_apply i).comp hXc
    have hwc : Continuous wv :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => (continuous_apply (i, j)).comp hWc)
    have hWw : ∀ u : ℝ≥0, W u ζ i = wv u := fun u => by
      ext j; simp [hwvdef, hcoords]
    have hβT : IntegrableOn β (Set.Icc 0 T) := by
      have := (heqn (Real.toNNReal T) (by rw [Real.coe_toNNReal _ hT.le])).1 i
      rwa [Real.coe_toNNReal _ hT.le] at this
    have hx : ∀ u : ℝ≥0, (u : ℝ) ≤ T →
        x u = x 0 + (∫ r in Set.Icc (0 : ℝ) u, β r) + Real.sqrt (2 * invβ) • (wv u - wv 0) := by
      intro u hu
      have := (heqn u hu).2 i
      rw [hWw u, hWw 0] at this
      exact this
    have hA := ssp2_pathwise x wv hxc hwc β (Real.sqrt (2 * invβ)) hβT hx hexp0 hτT
    obtain ⟨hcovI, hcovE⟩ := ssp2_cov x (β := β) hτ0 hτT hβT
    rw [hcovE, ssp2_h_exp] at hA
    -- identification of the integrands
    have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, ssDrift d s N r (ssPath X (Real.toNNReal r) ζ) i =
        Real.exp (r / 2) • β (Real.exp r - 1) -
          (1 / 2 : ℝ) • (Real.exp (-r / 2) • x (Real.toNNReal (Real.exp r - 1))) := by
      intro r hr
      rw [ssp2_ssPath_apply hr.1]
      exact ssp2_drift_identity hd s hs0 N invβ r (X (Real.toNNReal (Real.exp r - 1)) ζ) i
    have hxcont : Continuous fun r : ℝ =>
        (1 / 2 : ℝ) • (Real.exp (-r / 2) • x (Real.toNNReal (Real.exp r - 1))) := by
      have h1 : Continuous fun r : ℝ => Real.exp (-r / 2) :=
        Real.continuous_exp.comp (continuous_neg.div_const 2)
      have h2 : Continuous fun r : ℝ => x (Real.toNNReal (Real.exp r - 1)) :=
        hxc.comp (continuous_real_toNNReal.comp (Real.continuous_exp.sub continuous_const))
      exact (continuous_const : Continuous fun _ : ℝ => (1 / 2 : ℝ)).smul (h1.smul h2)
    have hint : IntegrableOn (fun r : ℝ => ssDrift d s N r (ssPath X (Real.toNNReal r) ζ) i)
        (Set.Icc 0 (t : ℝ)) :=
      (hcovI.sub (hxcont.continuousOn.integrableOn_Icc (μ := (volume : Measure ℝ)))).congr_fun
        (fun r hr => (hpt r hr).symm) measurableSet_Icc
    refine ⟨hint, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Icc hpt]
    have e1 : ssPath X t ζ i = Real.exp (-(t : ℝ) / 2) • x (Real.toNNReal (Real.exp (t : ℝ) - 1)) := by
      have := ssp2_ssPath_apply (X := X) (r := (t : ℝ)) t.2 ζ
      simp only [Real.toNNReal_coe] at this
      rw [this]
    have hJ : ssp2_J wv (Real.exp (t : ℝ) - 1) = ssp2_WbV W' t ζ i := by
      have := ssp2_J_toLp (d := d) (f := fun u j => W' u ζ (i, j))
        (fun j => (continuous_apply (i, j)).comp hWc |>.comp continuous_id) hexp0
      exact this
    have hW0' : wv 0 = 0 := by ext j; simp [hwvdef, hW0]
    have hWb0 : ssp2_WbV W' 0 ζ i = 0 := by
      ext j; simp [ssp2_WbV, ssp2_Wb, ssp2_J_zero, hW0]
    rw [hJ, ssp2_J_zero, hW0', sub_zero] at hA
    rw [hWb0, sub_zero, e1, ssp2_ssPath_zero]
    exact hA
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

end Assembly

/-- **P2** (time change): the proof of `HRS.MP.SelfSim.ss_P2_time_change`. -/
theorem ss_P2_time_change_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : SSAddSol P invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i)
      T ℱ W' W X) :
    ∃ (ℱb : Filtration ℝ mΩ) (Wb' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Wb : ℝ≥0 → Ω → (Fin N → Euc d)),
      SSAddSol P invβ (ssDrift d s N) (Real.log (1 + T)) ℱb Wb' Wb (ssPath X) ∧
      (SSNoCollision P T X → SSNoCollision P (Real.log (1 + T)) (ssPath X)) ∧
      (SSOrdered P T X → SSOrdered P (Real.log (1 + T)) (ssPath X)) := by
  refine ⟨ssp2_fil ℱ, ssp2_Wb W', ssp2_WbV W', ⟨?_, ?_, ?_, ?_, ?_⟩,
    fun h => ssp2_noCollision hT h, fun h => ssp2_ordered hT h⟩
  · refine ⟨ssp2_brownian hX.filtered.brownian, ae_of_all _ fun ζ t i j => rfl, fun t => ?_, ?_⟩
    · have e : ofNNRealTime (ssPath X) (t : ℝ) = ssPath X t := by
        funext ζ; simp [ofNNRealTime]
      rw [← e]
      exact ssp2_adapted_ssPath hX.filtered.progressive (t : ℝ)
    · exact ssp2_progressive_ssPath hX.filtered.progressive hX.cont
  · exact fun ζ => ssp2_continuous_ssPath hX.cont ζ
  · filter_upwards [hX.init_distinct] with ζ h
    rw [ssp2_ssPath_zero]; exact h
  · filter_upwards [hX.eqn, hX.filtered.coords] with ζ heqn hcoords t ht
    exact ssp2_eqn_pointwise hd s hs0 invβ hT X W W' ζ (hX.cont ζ) (hX.filtered.brownian.cont ζ)
      (hX.filtered.brownian.zero ζ) hcoords heqn t ht
  · exact ssp2_occupation hT hX.occupation

example := (@ss_P2_time_change_proof : type_of% @HRS.MP.SelfSim.ss_P2_time_change)

end HRS.MP.SelfSimP2

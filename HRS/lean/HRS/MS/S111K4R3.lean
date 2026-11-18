import HRS.MS.S111K4R2

/-!
# S11.1 / V02 (S11K4), Pro `R26-T6C.V07` (part): continuity in `r` of the individual cubic-formula integrands
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X1 (KData kA kG_measurable prod_integrable_kernel kA_nonneg)

variable {d : ℕ}

theorem k4_comm_meas (s : ℝ) {w : Euc d → Euc d} (hw : Measurable w) :
    Measurable fun p : Euc d × Euc d => commutatorKernel d s w p.1 p.2 := by
  unfold commutatorKernel
  exact Measurable.inner ((hw.comp measurable_fst).sub (hw.comp measurable_snd))
    ((kG_measurable s).comp (measurable_fst.sub measurable_snd))

theorem k4_nu_integrable_kernel {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M)
    (hρ : HRS.Whole.IsProbDensity ρ) :
    Integrable (fun p : Euc d × Euc d => ‖rieszKernelGrad d s (p.1 - p.2)‖)
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  rw [k4_integrable_prod_nu hρ]
  exact (prod_integrable_kernel K).congr (Filter.Eventually.of_forall fun p => by simp only; ring)

theorem k4_comm_abs {s : ℝ} {w : Euc d → Euc d} {B1 : ℝ} (hB1 : ∀ x, ‖w x‖ ≤ B1) (p : Euc d × Euc d) :
    |commutatorKernel d s w p.1 p.2| ≤ 2 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖ := by
  unfold commutatorKernel
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  calc ‖w p.1 - w p.2‖ ≤ ‖w p.1‖ + ‖w p.2‖ := norm_sub_le _ _
    _ ≤ 2 * B1 := by linarith [hB1 p.1, hB1 p.2]

theorem k4_comm_integrable_one {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M)
    (hρ : HRS.Whole.IsProbDensity ρ) {w : Euc d → Euc d} (hwm : Measurable w) {B1 : ℝ}
    (hB1 : ∀ x, ‖w x‖ ≤ B1) :
    Integrable (fun p : Euc d × Euc d => commutatorKernel d s w p.1 p.2)
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  have := k4_comm_integrable K hρ hwm hB1 (u := fun _ => (1 : ℝ)) measurable_const (Bu := 1)
    (fun _ => by simp) (v := fun _ => (1 : ℝ)) measurable_const (Bv := 1) (fun _ => by simp)
  exact this.congr (Filter.Eventually.of_forall fun p => by simp)

/-- Continuity within `S` of `r ↦ ∬ κ_{w r} a_r b_r d(ν⊗ν)`. -/
theorem k4_comm_cont {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) (hρ : HRS.Whole.IsProbDensity ρ)
    {S : Set ℝ} (w : ℝ → Euc d → Euc d) (hwm : ∀ r ∈ S, Measurable (w r)) {B1 : ℝ}
    (hB1 : ∀ r ∈ S, ∀ x, ‖w r x‖ ≤ B1) (hwc : ∀ x, ContinuousOn (fun r => w r x) S)
    (a b : ℝ → Euc d → ℝ) (ham : ∀ r ∈ S, Measurable (a r)) (hbm : ∀ r ∈ S, Measurable (b r)) {Bh : ℝ}
    (hBa : ∀ r ∈ S, ∀ x, |a r x| ≤ Bh) (hBb : ∀ r ∈ S, ∀ x, |b r x| ≤ Bh)
    (hal : ∀ r ∈ S, MemLp (a r) 2 (HRS.Whole.withDensityReal ρ))
    (hbl : ∀ r ∈ S, MemLp (b r) 2 (HRS.Whole.withDensityReal ρ))
    (hac : ∀ r ∈ S, ContinuousWithinAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (a q)) S r)
    (hbc : ∀ r ∈ S, ContinuousWithinAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (b q)) S r) :
    ContinuousOn (fun r => ∫ p, commutatorKernel d s (w r) p.1 p.2 * a r p.1 * b r p.2
      ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) S := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  intro r0 hr0
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 r0 hr0 0)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hBa r0 hr0 0)
  have hA0 := kA_nonneg K
  set CC : ℝ := 2 * B1 * Bh * kA d s M ρ with hCC
  have hCC0 : 0 ≤ CC := by positivity
  have hC : ∀ q ∈ S, ∀ {u v : Euc d → ℝ}, Measurable u → Measurable v → ∀ {Bu Bv : ℝ},
      (∀ x, |u x| ≤ Bu) → (∀ x, |v x| ≤ Bv) →
      Integrable (fun p : Euc d × Euc d => commutatorKernel d s (w q) p.1 p.2 * u p.1 * v p.2) (ν.prod ν) :=
    fun q hq u v hu hv Bu Bv hBu hBv => k4_comm_integrable K hρ (hwm q hq) (hB1 q hq) hu hBu hv hBv
  set E1 : ℝ → ℝ := fun q => ∫ p, |commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2|
    ∂(ν.prod ν) with hE1
  set E2 : ℝ → ℝ := fun q => ‖k4_toL ν (a q) - k4_toL ν (a r0)‖ with hE2
  set E3 : ℝ → ℝ := fun q => ‖k4_toL ν (b q) - k4_toL ν (b r0)‖ with hE3
  have hmain : ∀ q ∈ S, |(∫ p, commutatorKernel d s (w q) p.1 p.2 * a q p.1 * b q p.2 ∂(ν.prod ν)) -
      ∫ p, commutatorKernel d s (w r0) p.1 p.2 * a r0 p.1 * b r0 p.2 ∂(ν.prod ν)| ≤
      Bh ^ 2 * E1 q + CC * E2 q + CC * E3 q := by
    intro q hq
    have hΔa : Measurable fun x => a q x - a r0 x := (ham q hq).sub (ham r0 hr0)
    have hΔb : Measurable fun x => b q x - b r0 x := (hbm q hq).sub (hbm r0 hr0)
    have hbΔa : ∀ x, |a q x - a r0 x| ≤ 2 * Bh := fun x => by
      have := abs_sub (a q x) (a r0 x); linarith [hBa q hq x, hBa r0 hr0 x]
    have hbΔb : ∀ x, |b q x - b r0 x| ≤ 2 * Bh := fun x => by
      have := abs_sub (b q x) (b r0 x); linarith [hBb q hq x, hBb r0 hr0 x]
    have e1 : Integrable (fun p : Euc d × Euc d => (commutatorKernel d s (w q) p.1 p.2 -
        commutatorKernel d s (w r0) p.1 p.2) * a q p.1 * b q p.2) (ν.prod ν) := by
      have := (hC q hq (ham q hq) (hbm q hq) (hBa q hq) (hBb q hq)).sub (hC r0 hr0 (ham q hq) (hbm q hq) (hBa q hq) (hBb q hq))
      exact this.congr (Filter.Eventually.of_forall fun p => by simp only [Pi.sub_apply]; ring)
    have e2 : Integrable (fun p : Euc d × Euc d => commutatorKernel d s (w r0) p.1 p.2 *
        (a q p.1 - a r0 p.1) * b q p.2) (ν.prod ν) :=
      hC r0 hr0 hΔa (hbm q hq) hbΔa (hBb q hq)
    have e3 : Integrable (fun p : Euc d × Euc d => commutatorKernel d s (w r0) p.1 p.2 *
        a r0 p.1 * (b q p.2 - b r0 p.2)) (ν.prod ν) :=
      hC r0 hr0 (ham r0 hr0) hΔb (hBa r0 hr0) hbΔb
    have hsplit : (∫ p, commutatorKernel d s (w q) p.1 p.2 * a q p.1 * b q p.2 ∂(ν.prod ν)) -
        ∫ p, commutatorKernel d s (w r0) p.1 p.2 * a r0 p.1 * b r0 p.2 ∂(ν.prod ν) =
        (∫ p, (commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2) * a q p.1 * b q p.2
          ∂(ν.prod ν)) +
        (∫ p, commutatorKernel d s (w r0) p.1 p.2 * (a q p.1 - a r0 p.1) * b q p.2 ∂(ν.prod ν)) +
        ∫ p, commutatorKernel d s (w r0) p.1 p.2 * a r0 p.1 * (b q p.2 - b r0 p.2) ∂(ν.prod ν) := by
      have e12 : Integrable (fun p : Euc d × Euc d => (commutatorKernel d s (w q) p.1 p.2 -
          commutatorKernel d s (w r0) p.1 p.2) * a q p.1 * b q p.2 +
          commutatorKernel d s (w r0) p.1 p.2 * (a q p.1 - a r0 p.1) * b q p.2) (ν.prod ν) := e1.add e2
      rw [← integral_sub (hC q hq (ham q hq) (hbm q hq) (hBa q hq) (hBb q hq))
        (hC r0 hr0 (ham r0 hr0) (hbm r0 hr0) (hBa r0 hr0) (hBb r0 hr0)), ← integral_add e1 e2,
        ← integral_add e12 e3]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      beta_reduce
      ring
    -- first term
    have hkd : Integrable (fun p : Euc d × Euc d => |commutatorKernel d s (w q) p.1 p.2 -
        commutatorKernel d s (w r0) p.1 p.2|) (ν.prod ν) :=
      ((k4_comm_integrable_one K hρ (hwm q hq) (hB1 q hq)).sub
        (k4_comm_integrable_one K hρ (hwm r0 hr0) (hB1 r0 hr0))).abs
    have b1 : |∫ p, (commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2) * a q p.1 * b q p.2
        ∂(ν.prod ν)| ≤ Bh ^ 2 * E1 q := by
      refine (abs_integral_le_integral_abs).trans ?_
      rw [hE1]
      simp only
      rw [← integral_const_mul]
      refine integral_mono e1.abs (hkd.const_mul _) fun p => ?_
      simp only [abs_mul]
      have h1 := hBa q hq p.1
      have h2 := hBb q hq p.2
      have h0 := abs_nonneg (commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2)
      calc |commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2| * |a q p.1| * |b q p.2|
          ≤ |commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2| * Bh * Bh := by gcongr
        _ = _ := by ring
    -- second term
    have hL1 : ∀ {f g : Euc d → ℝ}, MemLp f 2 ν → MemLp g 2 ν →
        ∫ x, |f x - g x| ∂ν ≤ ‖k4_toL ν f - k4_toL ν g‖ := fun {f g} hf hg => by
      rw [← k4_toL_sub hf hg]
      exact k4_l1_le_l2 (hf.sub hg)
    have b2 : |∫ p, commutatorKernel d s (w r0) p.1 p.2 * (a q p.1 - a r0 p.1) * b q p.2 ∂(ν.prod ν)| ≤
        CC * E2 q := by
      refine (k4_comm_TB K hρ (hwm r0 hr0) (hB1 r0 hr0) hΔa hbΔa (hbm q hq) (hBb q hq)).trans ?_
      have := hL1 (hal q hq) (hal r0 hr0)
      rw [hCC, hE2]
      simp only
      calc 2 * B1 * Bh * kA d s M ρ * ∫ x, |a q x - a r0 x| ∂ν
          ≤ 2 * B1 * Bh * kA d s M ρ * ‖k4_toL ν (a q) - k4_toL ν (a r0)‖ := by gcongr
        _ = _ := by ring
    have b3 : |∫ p, commutatorKernel d s (w r0) p.1 p.2 * a r0 p.1 * (b q p.2 - b r0 p.2) ∂(ν.prod ν)| ≤
        CC * E3 q := by
      have hsw : ∫ p, commutatorKernel d s (w r0) p.1 p.2 * a r0 p.1 * (b q p.2 - b r0 p.2) ∂(ν.prod ν) =
          ∫ p, commutatorKernel d s (w r0) p.1 p.2 * (b q p.1 - b r0 p.1) * a r0 p.2 ∂(ν.prod ν) := by
        rw [← integral_prod_swap (μ := ν) (ν := ν)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [k4_comm_even]
        ring
      rw [hsw]
      refine (k4_comm_TB K hρ (hwm r0 hr0) (hB1 r0 hr0) hΔb hbΔb (ham r0 hr0) (hBa r0 hr0)).trans ?_
      have := hL1 (hbl q hq) (hbl r0 hr0)
      rw [hCC, hE3]
      simp only
      calc 2 * B1 * Bh * kA d s M ρ * ∫ x, |b q x - b r0 x| ∂ν
          ≤ 2 * B1 * Bh * kA d s M ρ * ‖k4_toL ν (b q) - k4_toL ν (b r0)‖ := by gcongr
        _ = _ := by ring
    rw [hsplit]
    refine (abs_add_three _ _ _).trans ?_
    linarith
  -- the limits
  have hE1t : Tendsto E1 (𝓝[S] r0) (𝓝 0) := by
    have hdom : Integrable (fun p : Euc d × Euc d => 4 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖) (ν.prod ν) :=
      (k4_nu_integrable_kernel K hρ).const_mul _
    have := tendsto_integral_filter_of_dominated_convergence (μ := ν.prod ν) (l := 𝓝[S] r0)
      (F := fun q p => |commutatorKernel d s (w q) p.1 p.2 - commutatorKernel d s (w r0) p.1 p.2|)
      (f := fun _ => (0 : ℝ)) (fun p => 4 * B1 * ‖rieszKernelGrad d s (p.1 - p.2)‖)
      (by
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (((k4_comm_meas s (hwm q hq)).sub (k4_comm_meas s (hwm r0 hr0))).abs).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_nhdsWithin] with q hq
        refine Filter.Eventually.of_forall fun p => ?_
        rw [Real.norm_eq_abs, abs_abs]
        refine (abs_sub _ _).trans ?_
        have h1 := k4_comm_abs (s := s) (hB1 q hq) p
        have h2 := k4_comm_abs (s := s) (hB1 r0 hr0) p
        linarith)
      hdom
      (Filter.Eventually.of_forall fun p => by
        have hw1 : Tendsto (fun q => w q p.1) (𝓝[S] r0) (𝓝 (w r0 p.1)) := hwc p.1 r0 hr0
        have hw2 : Tendsto (fun q => w q p.2) (𝓝[S] r0) (𝓝 (w r0 p.2)) := hwc p.2 r0 hr0
        have h3 : Tendsto (fun q => commutatorKernel d s (w q) p.1 p.2) (𝓝[S] r0)
            (𝓝 (commutatorKernel d s (w r0) p.1 p.2)) := by
          unfold commutatorKernel
          exact (hw1.sub hw2).inner tendsto_const_nhds
        have h4 := (h3.sub_const (commutatorKernel d s (w r0) p.1 p.2)).abs
        simpa using h4)
    simpa using this
  have hE2t : Tendsto E2 (𝓝[S] r0) (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 (hac r0 hr0)
    exact this
  have hE3t : Tendsto E3 (𝓝[S] r0) (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 (hbc r0 hr0)
    exact this
  have hz : Tendsto (fun q => Bh ^ 2 * E1 q + CC * E2 q + CC * E3 q) (𝓝[S] r0) (𝓝 0) := by
    have := ((hE1t.const_mul (Bh ^ 2)).add (hE2t.const_mul CC)).add (hE3t.const_mul CC)
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun q => dist_nonneg) ?_ hz
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Real.dist_eq]
  exact hmain q hq

/-- Continuity within `S` of `r ↦ ∫ ⟨w₁ r x, w₂ r x⟩ b_r(x) dν`. -/
theorem k4_dir_cont {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {S : Set ℝ} (w1 w2 : ℝ → Euc d → Euc d) (hm1 : ∀ r ∈ S, Measurable (w1 r)) (hm2 : ∀ r ∈ S, Measurable (w2 r))
    {B1 : ℝ} (hb1 : ∀ r ∈ S, ∀ x, ‖w1 r x‖ ≤ B1) (hb2 : ∀ r ∈ S, ∀ x, ‖w2 r x‖ ≤ B1)
    (hc1 : ∀ x, ContinuousOn (fun r => w1 r x) S) (hc2 : ∀ x, ContinuousOn (fun r => w2 r x) S)
    (b : ℝ → Euc d → ℝ) (hbm : ∀ r ∈ S, Measurable (b r)) {Bh : ℝ} (hBb : ∀ r ∈ S, ∀ x, |b r x| ≤ Bh)
    (hbl : ∀ r ∈ S, MemLp (b r) 2 (HRS.Whole.withDensityReal ρ))
    (hbc : ∀ r ∈ S, ContinuousWithinAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (b q)) S r) :
    ContinuousOn (fun r => ∫ x, inner ℝ (w1 r x) (w2 r x) * b r x ∂(HRS.Whole.withDensityReal ρ)) S := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  intro r0 hr0
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hb1 r0 hr0 0)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hBb r0 hr0 0)
  have hGm : ∀ q ∈ S, Measurable fun x => inner ℝ (w1 q x) (w2 q x) := fun q hq => (hm1 q hq).inner (hm2 q hq)
  have hGb : ∀ q ∈ S, ∀ x, |inner ℝ (w1 q x) (w2 q x)| ≤ B1 * B1 := fun q hq x =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hb1 q hq x) (hb2 q hq x) (norm_nonneg _) hB10)
  have hGi : ∀ q ∈ S, ∀ {v : Euc d → ℝ}, Measurable v → ∀ {Bv : ℝ}, (∀ x, |v x| ≤ Bv) →
      Integrable (fun x => inner ℝ (w1 q x) (w2 q x) * v x) ν := by
    intro q hq v hv Bv hBv
    refine (integrable_const (B1 * B1 * Bv)).mono' ((hGm q hq).mul hv).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGb q hq x) (hBv x) (abs_nonneg _) (by positivity)
  set E1 : ℝ → ℝ := fun q => ∫ x, |inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)| ∂ν with hE1
  set E3 : ℝ → ℝ := fun q => ‖k4_toL ν (b q) - k4_toL ν (b r0)‖ with hE3
  have hmain : ∀ q ∈ S, |(∫ x, inner ℝ (w1 q x) (w2 q x) * b q x ∂ν) -
      ∫ x, inner ℝ (w1 r0 x) (w2 r0 x) * b r0 x ∂ν| ≤ Bh * E1 q + B1 * B1 * E3 q := by
    intro q hq
    have hΔb : Measurable fun x => b q x - b r0 x := (hbm q hq).sub (hbm r0 hr0)
    have hbΔb : ∀ x, |b q x - b r0 x| ≤ 2 * Bh := fun x => by
      have := abs_sub (b q x) (b r0 x); linarith [hBb q hq x, hBb r0 hr0 x]
    have hGd : Integrable (fun x => |inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)|) ν := by
      refine (integrable_const (B1 * B1 + B1 * B1)).mono' (((hGm q hq).sub (hGm r0 hr0)).abs).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      exact (abs_sub _ _).trans (by linarith [hGb q hq x, hGb r0 hr0 x])
    have e1 : Integrable (fun x => (inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)) * b q x) ν := by
      have := (hGi q hq (hbm q hq) (hBb q hq)).sub (hGi r0 hr0 (hbm q hq) (hBb q hq))
      exact this.congr (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    have e2 : Integrable (fun x => inner ℝ (w1 r0 x) (w2 r0 x) * (b q x - b r0 x)) ν :=
      hGi r0 hr0 hΔb hbΔb
    have hsplit : (∫ x, inner ℝ (w1 q x) (w2 q x) * b q x ∂ν) -
        ∫ x, inner ℝ (w1 r0 x) (w2 r0 x) * b r0 x ∂ν =
        (∫ x, (inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)) * b q x ∂ν) +
        ∫ x, inner ℝ (w1 r0 x) (w2 r0 x) * (b q x - b r0 x) ∂ν := by
      rw [← integral_sub (hGi q hq (hbm q hq) (hBb q hq)) (hGi r0 hr0 (hbm r0 hr0) (hBb r0 hr0)),
        ← integral_add e1 e2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      ring
    have b1 : |∫ x, (inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)) * b q x ∂ν| ≤ Bh * E1 q := by
      refine (abs_integral_le_integral_abs).trans ?_
      rw [hE1]
      simp only
      rw [← integral_const_mul]
      refine integral_mono e1.abs (hGd.const_mul _) fun x => ?_
      simp only [abs_mul]
      have := hBb q hq x
      have h0 := abs_nonneg (inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x))
      calc |inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)| * |b q x|
          ≤ |inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)| * Bh := by gcongr
        _ = _ := by ring
    have b2 : |∫ x, inner ℝ (w1 r0 x) (w2 r0 x) * (b q x - b r0 x) ∂ν| ≤ B1 * B1 * E3 q := by
      refine (abs_integral_le_integral_abs).trans ?_
      have hL1 : ∫ x, |b q x - b r0 x| ∂ν ≤ ‖k4_toL ν (b q) - k4_toL ν (b r0)‖ := by
        rw [← k4_toL_sub (hbl q hq) (hbl r0 hr0)]
        exact k4_l1_le_l2 ((hbl q hq).sub (hbl r0 hr0))
      have hi : Integrable (fun x => |b q x - b r0 x|) ν := (((hbl q hq).sub (hbl r0 hr0)).integrable (by norm_num)).abs
      calc ∫ x, |inner ℝ (w1 r0 x) (w2 r0 x) * (b q x - b r0 x)| ∂ν
          ≤ ∫ x, B1 * B1 * |b q x - b r0 x| ∂ν := by
            refine integral_mono e2.abs (hi.const_mul _) fun x => ?_
            simp only [abs_mul]
            exact mul_le_mul_of_nonneg_right (hGb r0 hr0 x) (abs_nonneg _)
        _ = B1 * B1 * ∫ x, |b q x - b r0 x| ∂ν := by rw [integral_const_mul]
        _ ≤ B1 * B1 * ‖k4_toL ν (b q) - k4_toL ν (b r0)‖ := by gcongr
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    linarith
  have hE1t : Tendsto E1 (𝓝[S] r0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := 𝓝[S] r0)
      (F := fun q x => |inner ℝ (w1 q x) (w2 q x) - inner ℝ (w1 r0 x) (w2 r0 x)|)
      (f := fun _ => (0 : ℝ)) (fun _ => B1 * B1 + B1 * B1)
      (by
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (((hGm q hq).sub (hGm r0 hr0)).abs).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_nhdsWithin] with q hq
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hGb q hq x, hGb r0 hr0 x]))
      (integrable_const _)
      (Filter.Eventually.of_forall fun x => by
        have h3 : Tendsto (fun q => inner ℝ (w1 q x) (w2 q x)) (𝓝[S] r0) (𝓝 (inner ℝ (w1 r0 x) (w2 r0 x))) :=
          (hc1 x r0 hr0).inner (hc2 x r0 hr0)
        have h4 := (h3.sub_const (inner ℝ (w1 r0 x) (w2 r0 x))).abs
        simpa using h4)
    simpa using this
  have hE3t : Tendsto E3 (𝓝[S] r0) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hbc r0 hr0)
  have hz : Tendsto (fun q => Bh * E1 q + B1 * B1 * E3 q) (𝓝[S] r0) (𝓝 0) := by
    have := (hE1t.const_mul Bh).add (hE3t.const_mul (B1 * B1))
    simpa using this
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun q => dist_nonneg) ?_ hz
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Real.dist_eq]
  exact hmain q hq

end HRS.MS.S111K4

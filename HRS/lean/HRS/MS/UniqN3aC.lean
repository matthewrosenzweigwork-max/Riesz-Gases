import HRS.MS.UniqN0b

/-!
# N3a, part C: the physical-space function `w = g * D_q² v`

For `v ∈ C²_c`, `0 ≤ s < d`, `d - 2 ≤ s`: `w = convFun g (D_q D_q v)` is continuous, decays like
`(1+|y|)^{-(s+2)}`, hence lies in `L²`.  Also a uniform linear-growth bound for `g * h`, `h` supported
in a fixed ball, in terms of `sup |h|`.
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff Convolution

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0

variable {d : ℕ}

/-- `g * h` is linearly bounded, uniformly for `h` supported in `closedBall 0 R0`, `|h| ≤ M`. -/
theorem conv_bound_unif {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (R0 : ℝ) (hR : 0 ≤ R0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : Euc d → ℝ) (M : ℝ), Continuous h →
      (∀ t, h t ≠ 0 → t ∈ closedBall (0 : Euc d) R0) → (∀ t, |h t| ≤ M) → ∀ r,
      Integrable (fun t => rieszKernel d s (r - t) * h t) ∧
      |HRS.Whole.convFun (rieszKernel d s) h r| ≤ M * K * (1 + ‖r‖) := by
  set g := rieszKernel d s with hg
  obtain ⟨G0, hG0i, hG0n, hgG⟩ := g_dom (d := d) hs0 hsd
  set Vcb : ℝ := (volume (closedBall (0 : Euc d) R0)).toReal with hVcb
  have hcbi : Integrable ((closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have hI0 : 0 ≤ ∫ z, G0 z := integral_nonneg hG0n
  have hV0 : 0 ≤ Vcb := ENNReal.toReal_nonneg
  refine ⟨(∫ z, G0 z) + Vcb * (1 + R0), by positivity, fun h M hc hsupp hM r => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set bd : Euc d → ℝ := fun t => M * G0 (r - t) + M * (‖r‖ + R0) *
    (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) t with hbd
  have hbdi : Integrable bd := ((hG0i.comp_sub_left r).const_mul M).add (hcbi.const_mul _)
  have hle : ∀ t, ‖g (r - t) * h t‖ ≤ bd t := by
    intro t
    by_cases ht : h t = 0
    · rw [ht, mul_zero, norm_zero]
      have : 0 ≤ M * (‖r‖ + R0) * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) t := by
        exact mul_nonneg (mul_nonneg hM0 (add_nonneg (norm_nonneg _) hR))
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      exact add_nonneg (mul_nonneg hM0 (hG0n _)) this
    · have htc : t ∈ closedBall (0 : Euc d) R0 := hsupp t ht
      have htn : ‖t‖ ≤ R0 := by simpa using htc
      have h1 : ‖r - t‖ ≤ ‖r‖ + R0 := (norm_sub_le _ _).trans (by linarith)
      rw [norm_mul, Real.norm_eq_abs, hbd]
      simp only [Set.indicator_of_mem htc, mul_one]
      calc |g (r - t)| * ‖h t‖ ≤ (G0 (r - t) + (‖r‖ + R0)) * M :=
            mul_le_mul ((hgG _).trans (by linarith)) (by simpa using hM t) (norm_nonneg _)
              (by linarith [hG0n (r - t), norm_nonneg r, norm_nonneg t])
        _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun t => g (r - t) * h t) volume :=
    (((g_meas s).comp (measurable_const.sub measurable_id)).mul hc.measurable).aestronglyMeasurable
  refine ⟨hbdi.mono' hmeas (Eventually.of_forall hle), ?_⟩
  have h1 := norm_integral_le_of_norm_le hbdi (Eventually.of_forall hle)
  have h2 : ∫ t, bd t = M * (∫ z, G0 z) + M * (‖r‖ + R0) * Vcb := by
    rw [hbd, integral_add ((hG0i.comp_sub_left r).const_mul M) (hcbi.const_mul _),
      integral_const_mul, integral_const_mul, integral_sub_left_eq_self G0 volume r,
      integral_indicator measurableSet_closedBall]
    simp [hVcb, Measure.real]
  rw [Real.norm_eq_abs] at h1
  calc _ = |∫ t, g (r - t) * h t| := rfl
    _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := by
      nlinarith [mul_nonneg hM0 hI0, mul_nonneg hM0 hV0, norm_nonneg r,
        mul_nonneg (mul_nonneg hM0 hV0) (norm_nonneg r), mul_nonneg (mul_nonneg hM0 hV0) hR]

/-- Continuity of `g * h` for `h` continuous with compact support. -/
theorem convFun_continuous {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    Continuous (HRS.Whole.convFun (rieszKernel d s) h) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have := hhc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hh hl
  convert this using 1
  funext y
  simp only [HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
  congr 1; funext t; ring

/-- The second directional derivative `D_q D_q v`. -/
def qq (q : Euc d) (v : Euc d → ℝ) (y : Euc d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ v z q) y q

theorem qq_eq {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (q y : Euc d) :
    qq q v y = ∑ i, ∑ j, q i * q j * D1 j (D1 i v) y := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have e1 : ∀ w : Euc d, fderiv ℝ (fun z => fderiv ℝ v z w) y = (fderiv ℝ (fderiv ℝ v) y).flip w := by
    intro w
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    ext z; simp
  have hq : ∀ (T : Euc d →L[ℝ] ℝ), T q = ∑ i, q i * T (EuclideanSpace.single i 1) := by
    intro T
    conv_lhs => rw [show q = ∑ i, q i • (EuclideanSpace.single i (1 : ℝ) : Euc d) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, smul_eq_mul]
  unfold qq
  rw [e1 q, hq]
  simp only [ContinuousLinearMap.flip_apply]
  have : ∀ x : Euc d, (fderiv ℝ (fderiv ℝ v) y x) q = ∑ i, q i * (fderiv ℝ (fderiv ℝ v) y x)
      (EuclideanSpace.single i 1) := fun x => hq _
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := e1 (EuclideanSpace.single i 1)
  have hD : D1 i v = fun z => fderiv ℝ v z (EuclideanSpace.single i 1) := rfl
  show _ = q i * q j * fderiv ℝ (D1 i v) y (EuclideanSpace.single j 1)
  rw [hD, this]
  simp only [ContinuousLinearMap.flip_apply]
  ring


/-! ### Directional derivatives as functions -/

/-- `D_a ψ = fun y => fderiv ψ y a`. -/
def Da (a : Euc d) (ψ : Euc d → ℝ) : Euc d → ℝ := fun y => fderiv ℝ ψ y a

theorem Da_contDiff {k : ℕ} {a : Euc d} {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) ψ) :
    ContDiff ℝ (k : WithTop ℕ∞) (Da a ψ) :=
  (hψ.fderiv_right (m := k) (by norm_cast)).clm_apply contDiff_const

theorem Da_hasCompactSupport {a : Euc d} {ψ : Euc d → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (Da a ψ) :=
  (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L a) (by simp)

theorem Da_support_sub (a : Euc d) (ψ : Euc d → ℝ) :
    Function.support (Da a ψ) ⊆ tsupport ψ := fun x hx => by
  have : fderiv ℝ ψ x ≠ 0 := fun h0 => hx (by simp [Da, h0])
  exact (support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 this)

theorem qq_eq_Da (q : Euc d) (v : Euc d → ℝ) : qq q v = Da q (Da q v) := rfl

theorem qq_contDiff {q : Euc d} {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) : Continuous (qq q v) := by
  have h1 : ContDiff ℝ 1 (Da q v) := Da_contDiff (k := 1) (by simpa using hv)
  have := (Da_contDiff (k := 0) (a := q) (ψ := Da q v) (by simpa using h1)).continuous
  exact this

theorem qq_hasCompactSupport {q : Euc d} {v : Euc d → ℝ} (hvc : HasCompactSupport v) :
    HasCompactSupport (qq q v) := Da_hasCompactSupport (Da_hasCompactSupport hvc)

theorem qq_support_sub (q : Euc d) (v : Euc d → ℝ) :
    Function.support (qq q v) ⊆ tsupport v := fun x hx =>
  (closure_minimal (Da_support_sub q v) isClosed_closure : tsupport (Da q v) ⊆ tsupport v)
    (Da_support_sub q (Da q v) hx)

/-! ### Decay of `w = g * D_q² v` -/

theorem w_decomp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (q y : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (qq q v) y =
      ∑ i, ∑ j, q i * q j *
        fderiv ℝ (kernelConvDeriv d s i v) y (EuclideanSpace.single j (1 : ℝ)) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hterm : ∀ i j, Integrable (fun t => rieszKernel d s (y - t) * D1 j (D1 i v) t) := by
    intro i j
    have hc : Continuous (D1 j (D1 i v)) :=
      ((D1_contDiff hv i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (D1 j (D1 i v)) := D1_supp (D1_supp hvc i) j
    obtain ⟨R1, hR1⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : Euc d)
    obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
    obtain ⟨K, -, hK⟩ := conv_bound_unif hs0 hsd (max R1 0) (le_max_right _ _)
    exact (hK _ M hc (fun t ht => closedBall_subset_closedBall (le_max_left _ _)
      (hR1 (subset_tsupport _ ht))) (fun t => by simpa [Real.norm_eq_abs] using hM t) y).1
  have hsum : qq q v = fun t => ∑ i, ∑ j, q i * q j * D1 j (D1 i v) t :=
    funext fun t => qq_eq hv q t
  unfold HRS.Whole.convFun
  rw [hsum]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hterm i j).const_mul (q i * q j) |>.congr (Eventually.of_forall fun t => by ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hterm i j).const_mul (q i * q j) |>.congr
    (Eventually.of_forall fun t => by ring)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hD := convFun_D1 hl (D1_contDiff hv i) (D1_supp hvc i) j y
  have hD' : fderiv ℝ (kernelConvDeriv d s i v) y (EuclideanSpace.single j (1 : ℝ)) =
      HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i v)) y := hD
  rw [hD']
  unfold HRS.Whole.convFun
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only; ring

theorem w_far {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (q : Euc d) {R : ℝ} (hR : 1 ≤ R)
    (hsupp : Function.support v ⊆ closedBall (0 : Euc d) R) :
    ∃ B : ℝ, ∀ y : Euc d, 2 * R ≤ ‖y‖ →
      |HRS.Whole.convFun (rieszKernel d s) (qq q v) y| ≤ B * ‖y‖ ^ (-s - 2) := by
  refine ⟨(∑ i, ∑ j, |q i| * |q j|) *
    ((max 1 s * (s + 3) * 2 ^ (s + 2)) * (∫ x, |v x|)), fun y hy => ?_⟩
  rw [w_decomp hs0 hsd hv hvc q y]
  have hb : ∀ i j, |q i * q j * fderiv ℝ (kernelConvDeriv d s i v) y (EuclideanSpace.single j (1 : ℝ))| ≤
      |q i| * |q j| * (((max 1 s * (s + 3) * 2 ^ (s + 2)) * (∫ x, |v x|)) * ‖y‖ ^ (-s - 2)) := by
    intro i j
    rw [abs_mul, abs_mul]
    have := n0_far_grad_bound hs0 hsd i j hv hvc (c := 0) hR hsupp (y := y) (by simpa using hy)
    simp only [sub_zero] at this
    gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => hb i j)).trans (le_of_eq ?_)
  simp_rw [← Finset.sum_mul]
  ring_nf

theorem w_decay {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (q : Euc d) :
    ∃ C : ℝ, ∀ y : Euc d,
      |HRS.Whole.convFun (rieszKernel d s) (qq q v) y| ≤ C * (1 + ‖y‖) ^ (-(s + 2)) := by
  obtain ⟨R1, hR1⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R1 1 with hRdef
  have hR : 1 ≤ R := le_max_right _ _
  have hsupp : Function.support v ⊆ closedBall (0 : Euc d) R := fun x hx =>
    closedBall_subset_closedBall (le_max_left _ _) (hR1 (subset_tsupport _ hx))
  obtain ⟨B, hB⟩ := w_far hs0 hsd hv hvc q hR hsupp
  have hcont := convFun_continuous hs0 hsd (qq_contDiff hv (q := q)) (qq_hasCompactSupport hvc)
  obtain ⟨B0, hB0⟩ := (isCompact_closedBall (0 : Euc d) (2 * R)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0 (by simp; linarith))
  refine ⟨max (B0 * (1 + 2 * R) ^ (s + 2)) (B * 2 ^ (s + 2)), fun y => ?_⟩
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hrp : 0 < (1 + ‖y‖) ^ (-(s + 2)) := Real.rpow_pos_of_pos hpos _
  by_cases hy : ‖y‖ ≤ 2 * R
  · have h1 : |HRS.Whole.convFun (rieszKernel d s) (qq q v) y| ≤ B0 := by
      simpa [Real.norm_eq_abs] using hB0 y (by simpa using hy)
    have h2 : (1 + 2 * R) ^ (-(s + 2)) ≤ (1 + ‖y‖) ^ (-(s + 2)) :=
      Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
    have h3 : (1 + 2 * R) ^ (s + 2) * (1 + 2 * R) ^ (-(s + 2)) = 1 := by
      rw [← Real.rpow_add (by linarith)]; simp
    calc _ ≤ B0 := h1
      _ = B0 * (1 + 2 * R) ^ (s + 2) * (1 + 2 * R) ^ (-(s + 2)) := by
          rw [mul_assoc, h3, mul_one]
      _ ≤ B0 * (1 + 2 * R) ^ (s + 2) * (1 + ‖y‖) ^ (-(s + 2)) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at hy
    have h1 := hB y hy.le
    have hy1 : 1 ≤ ‖y‖ := by linarith
    have h2 := n0_rpow_half (a := 1 + ‖y‖) (r := ‖y‖) (e := -s - 2) hpos (by linarith) (by linarith)
    have hBn : 0 ≤ B ∨ B < 0 := le_or_gt 0 B |>.imp id id
    have h4 : (-(-s - 2)) = s + 2 := by ring
    rw [h4] at h2
    have h5 : -s - 2 = -(s + 2) := by ring
    rw [h5] at h1 h2
    rcases hBn with hB0'' | hBneg
    · calc _ ≤ B * ‖y‖ ^ (-(s + 2)) := h1
        _ ≤ B * (2 ^ (s + 2) * (1 + ‖y‖) ^ (-(s + 2))) := by gcongr
        _ = B * 2 ^ (s + 2) * (1 + ‖y‖) ^ (-(s + 2)) := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _
    · have : B * ‖y‖ ^ (-(s + 2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hBneg.le
        (Real.rpow_nonneg (norm_nonneg _) _)
      have hmax0 : 0 ≤ max (B0 * (1 + 2 * R) ^ (s + 2)) (B * 2 ^ (s + 2)) :=
        le_trans (mul_nonneg hB0' (Real.rpow_nonneg (by positivity) _)) (le_max_left _ _)
      exact h1.trans (this.trans (mul_nonneg hmax0 hrp.le))

theorem w_memLp {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d)
    {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (q : Euc d) :
    MemLp (HRS.Whole.convFun (rieszKernel d s) (qq q v)) 2 volume := by
  obtain ⟨C, hC⟩ := w_decay hs0 hsd hv hvc q
  have hcont := convFun_continuous hs0 hsd (qq_contDiff hv (q := q)) (qq_hasCompactSupport hvc)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-(2 * (s + 2)))) volume := by
    refine integrable_one_add_norm ?_
    rw [finrank_euclideanSpace_fin]; linarith
  refine (hint.const_mul (C ^ 2)).mono' (hcont.aestronglyMeasurable.pow 2)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have h1 := hC y
  have h0 := abs_nonneg (HRS.Whole.convFun (rieszKernel d s) (qq q v) y)
  have hrp : 0 ≤ (1 + ‖y‖) ^ (-(s + 2)) := Real.rpow_nonneg (by positivity) _
  calc _ ≤ (C * (1 + ‖y‖) ^ (-(s + 2))) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = C ^ 2 * (1 + ‖y‖) ^ (-(2 * (s + 2))) := by
        rw [mul_pow, ← Real.rpow_natCast ((1 + ‖y‖) ^ (-(s + 2))) 2, ← Real.rpow_mul (by positivity)]
        congr 2; push_cast; ring

end HRS.MS.UniqN3a

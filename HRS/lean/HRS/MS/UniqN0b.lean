import HRS.MS.UniqN0a

/-!
# N0 of `UniqPlan.md`, part (b): far-field identities and pointwise bounds for `H_i = g * ∂_iψ`

Let `ψ ∈ C¹_c(ℝ^d)`, `0 ≤ s < d`, `H_i := kernelConvDeriv d s i ψ`.

* `n0_ibp`: integration by parts of a `C¹` compactly supported `F` against a function `k` which is `C¹`
  near `tsupport F` (no regularity of `k` elsewhere).
* `n0_kcd_eq_gradConv`: for `y ∉ tsupport ψ`,
  `H_i(y) = ∫ ∂_i g(y - x) ψ(x) dx` (`= gradGConvPlain d s ψ y i`, the plain convolution `∂_ig * ψ`).
* `n0_far_bound`: if `supp ψ ⊆ B̄(c,R)`, `R ≥ 1`, `‖y - c‖ ≥ 2R` then
  `|H_i(y)| ≤ max(1,s) 2^{s+1} ‖ψ‖₁ ‖y - c‖^{-s-1}`.
* `n0_far_grad_bound` (`ψ ∈ C²_c`): same hypotheses, `|∂_j H_i(y)| ≤ max(1,s)(s+3) 2^{s+2} ‖ψ‖₁ ‖y - c‖^{-s-2}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN0

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3

variable {d : ℕ}

/-- Integration by parts: `F ∈ C¹_c`, `k` of class `C¹` at each point of `tsupport F`. -/
theorem n0_ibp {F k : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hk : ∀ t ∈ tsupport F, ContDiffAt ℝ 1 k t) (v : Euc d) :
    ∫ t, k t * fderiv ℝ F t v = -∫ t, fderiv ℝ k t v * F t := by
  have hS : IsCompact (tsupport F) := hFc
  have hkd : ∀ t ∈ tsupport F, DifferentiableAt ℝ k t :=
    fun t ht => (hk t ht).differentiableAt one_ne_zero
  have hfd0 : ∀ t, t ∉ tsupport F → fderiv ℝ F t = 0 := by
    intro t ht
    by_contra h
    exact ht ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h))
  have hF0 : ∀ t, t ∉ tsupport F → F t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  have hFd : Continuous (fun t => fderiv ℝ F t v) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hkc : ContinuousOn k (tsupport F) := fun t ht => (hk t ht).continuousAt.continuousWithinAt
  have hkd' : ContinuousOn (fun t => fderiv ℝ k t v) (tsupport F) := fun t ht =>
    (((hk t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have i1 : Integrable (fun t => fderiv ℝ k t v * F t) volume :=
    q09_integrable_of_zero_outside hS (hkd'.mul hF.continuous.continuousOn)
      (by intro t ht; simp [hF0 t ht])
  have i2 : Integrable (fun t => k t * fderiv ℝ F t v) volume :=
    q09_integrable_of_zero_outside hS (hkc.mul hFd.continuousOn)
      (by intro t ht; simp [hfd0 t ht])
  have i3 : Integrable (fun t => k t * F t) volume :=
    q09_integrable_of_zero_outside hS (hkc.mul hF.continuous.continuousOn)
      (by intro t ht; simp [hF0 t ht])
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := k) (g := F) (v := v)
    i1 i2 i3 (fun t ht => hkd t ht) (fun t _ => (hF.differentiable one_ne_zero) t)

/-! ### The kernel `∂_i g` and its derivative -/

theorem n0_gradRK (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s z i = q09_H s i z := by
  unfold rieszKernelGrad
  rw [q09_gradient_apply, q09_H_eq_fderiv s i hz]

theorem n0_qc_abs {s : ℝ} (hs0 : 0 ≤ s) : |q09_c s| ≤ max 1 s := by
  unfold q09_c
  split_ifs with h
  · simp
  · rw [abs_neg, abs_of_nonneg hs0]; exact le_max_right _ _

theorem n0_coord_le (z : Euc d) (i : Fin d) : |z i| ≤ ‖z‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i

theorem n0_qH_bound {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    |q09_H s i z| ≤ max 1 s * ‖z‖ ^ (-s - 1) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold q09_H
  have h1 : ‖z‖ ^ (-s - 2) * ‖z‖ = ‖z‖ ^ (-s - 1) := by
    rw [← Real.rpow_add_one hn.ne']; congr 1; ring
  have h2 : 0 ≤ ‖z‖ ^ (-s - 2) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg h2]
  calc |q09_c s| * (‖z‖ ^ (-s - 2) * |z i|) ≤ max 1 s * (‖z‖ ^ (-s - 2) * ‖z‖) :=
        mul_le_mul (n0_qc_abs hs0) (mul_le_mul_of_nonneg_left (n0_coord_le z i) h2)
          (by positivity) (le_trans zero_le_one (le_max_left _ _))
    _ = _ := by rw [h1]

theorem n0_qH_contDiffAt (s : ℝ) (j : Fin d) {z : Euc d} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (q09_H s j) z := by
  have hn : ContDiffAt ℝ ∞ (fun x : Euc d => ‖x‖) z := contDiffAt_norm ℝ hz
  have hr : ContDiffAt ℝ ∞ (fun x : Euc d => ‖x‖ ^ (-s - 2)) z :=
    hn.rpow_const_of_ne (norm_ne_zero_iff.2 hz)
  have hp : ContDiffAt ℝ ∞ (fun x : Euc d => x j) z :=
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.contDiffAt
  show ContDiffAt ℝ ∞ (fun z : Euc d => q09_c s * (‖z‖ ^ (-s - 2) * z j)) z
  exact contDiffAt_const.mul (hr.mul hp)

theorem n0_qDH_apply (s : ℝ) (i j : Fin d) (z : Euc d) :
    q09_DH s i z (EuclideanSpace.single j (1 : ℝ)) =
      q09_c s * (‖z‖ ^ (-s - 2) * (if i = j then 1 else 0) +
        (z i * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2))) * z j) := by
  unfold q09_DH
  simp [EuclideanSpace.inner_single_right, innerSL_apply_apply]
  split_ifs <;> ring

theorem n0_qDH_bound {s : ℝ} (hs0 : 0 ≤ s) (i j : Fin d) {z : Euc d} (hz : z ≠ 0) :
    |q09_DH s i z (EuclideanSpace.single j (1 : ℝ))| ≤ max 1 s * (s + 3) * ‖z‖ ^ (-s - 2) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [n0_qDH_apply, abs_mul]
  have h2 : 0 ≤ ‖z‖ ^ (-s - 2) := by positivity
  have h4 : ‖z‖ ^ (-s - 2 - 2) * ‖z‖ ^ 2 = ‖z‖ ^ (-s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]; congr 1; push_cast; ring
  have hb1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have hb2 : |z i * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2)) * z j| ≤ (s + 2) * ‖z‖ ^ (-s - 2) := by
    have h5 : 0 ≤ ‖z‖ ^ (-s - 2 - 2) := by positivity
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h5,
      abs_of_nonpos (by linarith : -s - 2 ≤ 0)]
    calc |z i| * ((-(-s - 2)) * ‖z‖ ^ (-s - 2 - 2)) * |z j|
        ≤ ‖z‖ * ((-(-s - 2)) * ‖z‖ ^ (-s - 2 - 2)) * ‖z‖ := by
          have hcr : 0 ≤ (-(-s - 2)) * ‖z‖ ^ (-s - 2 - 2) := mul_nonneg (by linarith) h5
          exact mul_le_mul (mul_le_mul_of_nonneg_right (n0_coord_le z i) hcr) (n0_coord_le z j)
            (abs_nonneg _) (mul_nonneg hn.le hcr)
      _ = (s + 2) * (‖z‖ ^ (-s - 2 - 2) * ‖z‖ ^ 2) := by ring
      _ = _ := by rw [h4]
  have hsum : |‖z‖ ^ (-s - 2) * (if i = j then (1 : ℝ) else 0) +
      z i * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2)) * z j| ≤ (s + 3) * ‖z‖ ^ (-s - 2) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg h2]
    nlinarith [mul_le_mul_of_nonneg_left hb1 h2]
  calc |q09_c s| * |‖z‖ ^ (-s - 2) * (if i = j then (1 : ℝ) else 0) +
        z i * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2)) * z j|
      ≤ max 1 s * ((s + 3) * ‖z‖ ^ (-s - 2)) :=
        mul_le_mul (n0_qc_abs hs0) hsum (abs_nonneg _) (le_trans zero_le_one (le_max_left _ _))
    _ = _ := by ring

/-! ### Far-field identity -/

theorem n0_g_contDiffAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ 1 (rieszKernel d s) z :=
  ((rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt
    (isOpen_ne.mem_nhds hz)).of_le (by exact_mod_cast le_top)

theorem n0_kcd_eq_gradConv {s : ℝ} (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {y : Euc d} (hy : y ∉ tsupport ψ) :
    kernelConvDeriv d s i ψ y = ∫ x, rieszKernelGrad d s (y - x) i * ψ x := by
  have hne : ∀ t ∈ tsupport ψ, y - t ≠ 0 := fun t ht h0 => hy (by
    rw [sub_eq_zero] at h0; rwa [h0])
  have hk : ∀ t ∈ tsupport ψ, ContDiffAt ℝ 1 (fun t => rieszKernel d s (y - t)) t := fun t ht =>
    (n0_g_contDiffAt s (hne t ht)).comp t ((contDiffAt_const.sub contDiffAt_id))
  have h := n0_ibp hψ hψc hk (EuclideanSpace.single i (1 : ℝ))
  unfold kernelConvDeriv
  rw [h, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  by_cases ht : t ∈ tsupport ψ
  · have hd : HasFDerivAt (fun t => rieszKernel d s (y - t))
        ((fderiv ℝ (rieszKernel d s) (y - t)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) t :=
      ((n0_g_contDiffAt s (hne t ht)).differentiableAt one_ne_zero).hasFDerivAt.comp t
        ((hasFDerivAt_const y t).sub (hasFDerivAt_id t))
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, zero_sub, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
    unfold rieszKernelGrad
    rw [q09_gradient_apply]
    ring
  · rw [image_eq_zero_of_notMem_tsupport ht]; simp

/-! ### Pointwise bounds -/

theorem n0_tsupport_sub {ψ : Euc d → ℝ} {c : Euc d} {R : ℝ}
    (hsupp : Function.support ψ ⊆ closedBall c R) : tsupport ψ ⊆ closedBall c R :=
  closure_minimal hsupp isClosed_closedBall

theorem n0_far_geom {ψ : Euc d → ℝ} {c : Euc d} {R : ℝ} (hR : 1 ≤ R)
    (hsupp : Function.support ψ ⊆ closedBall c R) {y : Euc d} (hy : 2 * R ≤ ‖y - c‖) :
    y ∉ tsupport ψ ∧ ∀ x ∈ tsupport ψ, ‖y - c‖ / 2 ≤ ‖y - x‖ := by
  have hs := n0_tsupport_sub hsupp
  have hx : ∀ x ∈ tsupport ψ, ‖y - c‖ / 2 ≤ ‖y - x‖ := by
    intro x hx
    have h1 : ‖x - c‖ ≤ R := by simpa [dist_eq_norm] using hs hx
    have h2 : ‖y - c‖ ≤ ‖y - x‖ + ‖x - c‖ := by
      have := norm_add_le (y - x) (x - c)
      simpa using this
    linarith
  refine ⟨fun hmem => ?_, hx⟩
  have := hx y hmem
  have h0 : ‖y - y‖ = 0 := by simp
  rw [h0] at this
  have : 0 < ‖y - c‖ := by linarith
  linarith

theorem n0_rpow_half {a r e : ℝ} (ha : 0 < a) (he : e ≤ 0) (h : a / 2 ≤ r) :
    r ^ e ≤ 2 ^ (-e) * a ^ e := by
  have h1 : r ^ e ≤ (a / 2) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) h he
  calc r ^ e ≤ (a / 2) ^ e := h1
    _ = a ^ e / 2 ^ e := Real.div_rpow ha.le (by norm_num) e
    _ = _ := by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; ring

theorem n0_far_bound {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {c : Euc d} {R : ℝ} (hR : 1 ≤ R)
    (hsupp : Function.support ψ ⊆ closedBall c R) {y : Euc d} (hy : 2 * R ≤ ‖y - c‖) :
    |kernelConvDeriv d s i ψ y| ≤
      (max 1 s * 2 ^ (s + 1)) * (∫ x, |ψ x|) * ‖y - c‖ ^ (-s - 1) := by
  obtain ⟨hyn, hgeo⟩ := n0_far_geom hR hsupp hy
  rw [n0_kcd_eq_gradConv i hψ hψc hyn]
  have hyc : 0 < ‖y - c‖ := by linarith
  have hint : Integrable (fun x => |ψ x|) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hψc).abs
  have hK : ∀ x, ψ x ≠ 0 → |rieszKernelGrad d s (y - x) i| ≤
      max 1 s * 2 ^ (s + 1) * ‖y - c‖ ^ (-s - 1) := by
    intro x hx
    have hxt : x ∈ tsupport ψ := subset_tsupport ψ hx
    have hge := hgeo x hxt
    have hpos : 0 < ‖y - x‖ := lt_of_lt_of_le (by positivity) hge
    have hne : y - x ≠ 0 := norm_pos_iff.1 hpos
    rw [n0_gradRK s i hne]
    refine (n0_qH_bound hs0 i hne).trans ?_
    have h1 := n0_rpow_half hyc (by linarith : -s - 1 ≤ 0) hge
    rw [show -(-s - 1) = s + 1 by ring] at h1
    calc max 1 s * ‖y - x‖ ^ (-s - 1) ≤ max 1 s * (2 ^ (s + 1) * ‖y - c‖ ^ (-s - 1)) := by
          gcongr
      _ = _ := by ring
  have hbd : ∀ x, ‖rieszKernelGrad d s (y - x) i * ψ x‖ ≤
      (max 1 s * 2 ^ (s + 1) * ‖y - c‖ ^ (-s - 1)) * |ψ x| := by
    intro x
    by_cases hx : ψ x = 0
    · simp [hx]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hK x hx) (abs_nonneg _)
  have := norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbd)
  rw [integral_const_mul] at this
  calc _ ≤ _ := by simpa [Real.norm_eq_abs] using this
    _ = _ := by ring

theorem n0_far_grad_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) {c : Euc d} {R : ℝ} (hR : 1 ≤ R)
    (hsupp : Function.support ψ ⊆ closedBall c R) {y : Euc d} (hy : 2 * R ≤ ‖y - c‖) :
    |fderiv ℝ (kernelConvDeriv d s i ψ) y (EuclideanSpace.single j (1 : ℝ))| ≤
      (max 1 s * (s + 3) * 2 ^ (s + 2)) * (∫ x, |ψ x|) * ‖y - c‖ ^ (-s - 2) := by
  obtain ⟨hyn, hgeo⟩ := n0_far_geom hR hsupp hy
  have hyc : 0 < ‖y - c‖ := by linarith
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hF1 : ContDiff ℝ 1 (D1 i ψ) := D1_contDiff hψ i
  have hF1c : HasCompactSupport (D1 i ψ) := D1_supp hψc i
  have hsupp1 : Function.support (D1 i ψ) ⊆ tsupport ψ := fun x hx => by
    have : fderiv ℝ ψ x ≠ 0 := fun h0 => hx (by simp [D1, h0])
    exact (support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 this)
  have hy1 : y ∉ tsupport (D1 i ψ) := fun hmem =>
    hyn ((closure_minimal hsupp1 isClosed_closure : tsupport (D1 i ψ) ⊆ tsupport ψ) hmem)
  have hD : fderiv ℝ (kernelConvDeriv d s i ψ) y (EuclideanSpace.single j (1 : ℝ)) =
      kernelConvDeriv d s j (D1 i ψ) y := by
    have := convFun_D1 hl hF1 hF1c j y
    exact this
  rw [hD, n0_kcd_eq_gradConv j hF1 hF1c hy1]
  -- the kernel `x ↦ ∂_j g (y - x)`
  have hne : ∀ x ∈ tsupport ψ, y - x ≠ 0 := fun x hx h0 => hyn (by
    rw [sub_eq_zero] at h0; rwa [h0])
  have hk : ∀ x ∈ tsupport ψ, ContDiffAt ℝ 1 (fun x => q09_H s j (y - x)) x := fun x hx =>
    ((n0_qH_contDiffAt s j (hne x hx)).of_le (by exact_mod_cast le_top)).comp x
      (contDiffAt_const.sub contDiffAt_id)
  have hpt : ∀ x, rieszKernelGrad d s (y - x) j * D1 i ψ x = q09_H s j (y - x) * D1 i ψ x := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · rw [n0_gradRK s j (hne x hx)]
    · have : D1 i ψ x = 0 := by
        have h0 : fderiv ℝ ψ x = 0 := by
          by_contra h
          exact hx ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h))
        simp [D1, h0]
      simp [this]
  simp_rw [hpt]
  have hibp := n0_ibp (hψ.of_le (by norm_num)) hψc hk (EuclideanSpace.single i (1 : ℝ))
  have hIBP : ∫ x, q09_H s j (y - x) * D1 i ψ x = -∫ x, fderiv ℝ (fun x => q09_H s j (y - x)) x
      (EuclideanSpace.single i (1 : ℝ)) * ψ x := hibp
  rw [hIBP]
  have hint : Integrable (fun x => |ψ x|) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hψc).abs
  have hder : ∀ x ∈ tsupport ψ, fderiv ℝ (fun x => q09_H s j (y - x)) x
      (EuclideanSpace.single i (1 : ℝ)) = -(q09_DH s j (y - x) (EuclideanSpace.single i (1 : ℝ))) := by
    intro x hx
    have hd : HasFDerivAt (fun x => q09_H s j (y - x))
        ((q09_DH s j (y - x)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) x :=
      (q09_H_hasFDerivAt s j (hne x hx)).comp x ((hasFDerivAt_const y x).sub (hasFDerivAt_id x))
    rw [hd.fderiv]
    simp
  have hbd : ∀ x, ‖fderiv ℝ (fun x => q09_H s j (y - x)) x (EuclideanSpace.single i (1 : ℝ)) * ψ x‖ ≤
      (max 1 s * (s + 3) * 2 ^ (s + 2) * ‖y - c‖ ^ (-s - 2)) * |ψ x| := by
    intro x
    by_cases hx : ψ x = 0
    · simp [hx]
    · have hxt : x ∈ tsupport ψ := subset_tsupport ψ hx
      have hge := hgeo x hxt
      have hpos : 0 < ‖y - x‖ := lt_of_lt_of_le (by positivity) hge
      rw [hder x hxt, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (n0_qDH_bound hs0 j i (hne x hxt)).trans ?_
      have h1 := n0_rpow_half hyc (by linarith : -s - 2 ≤ 0) hge
      rw [show -(-s - 2) = s + 2 by ring] at h1
      have hc : 0 ≤ max 1 s * (s + 3) := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by linarith)
      calc max 1 s * (s + 3) * ‖y - x‖ ^ (-s - 2)
          ≤ max 1 s * (s + 3) * (2 ^ (s + 2) * ‖y - c‖ ^ (-s - 2)) := by gcongr
        _ = _ := by ring
  have := norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbd)
  rw [integral_const_mul] at this
  rw [abs_neg]
  calc _ ≤ _ := by simpa [Real.norm_eq_abs] using this
    _ = _ := by ring

end HRS.MS.UniqN0

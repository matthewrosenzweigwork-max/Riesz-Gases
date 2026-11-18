import HRS.MS.S113X2A2h

/-!
# S11.3 X2 part A2i: `movPartial` and `movFP` through directional derivatives
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_update_eq (X : EucConfig d N) (i : Fin N) (k : Fin d) (τ : ℝ) :
    Function.update X i (X i + τ • (EuclideanSpace.single k 1 : Euc d)) =
      X + τ • HRS.configBasis d N (i, k) := by
  funext j
  by_cases h : j = i
  · subst h; simp [HRS.configBasis]
  · simp [Function.update_of_ne h, HRS.configBasis, Pi.single_apply, h]

theorem s113a_movPartial_eq {g : EucConfig d N → ℝ} {X : EucConfig d N} (hg : DifferentiableAt ℝ g X)
    (i : Fin N) (k : Fin d) :
    movPartial g i k X = fderiv ℝ g X (HRS.configBasis d N (i, k)) := by
  unfold movPartial
  have hc : HasDerivAt (fun τ : ℝ => X + τ • HRS.configBasis d N (i, k)) (HRS.configBasis d N (i, k)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (HRS.configBasis d N (i, k))).const_add X
  have hg' : HasFDerivAt g (fderiv ℝ g X) ((fun τ : ℝ => X + τ • HRS.configBasis d N (i, k)) 0) := by
    simpa using hg.hasFDerivAt
  simp_rw [s113a_update_eq]
  exact (hg'.comp_hasDerivAt (0 : ℝ) hc).deriv

theorem s113a_movPartial_congr {g1 g2 : EucConfig d N → ℝ} {X : EucConfig d N} (h : g1 =ᶠ[𝓝 X] g2)
    (i : Fin N) (k : Fin d) : movPartial g1 i k X = movPartial g2 i k X := by
  unfold movPartial
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : Continuous fun τ : ℝ => Function.update X i (X i + τ • (EuclideanSpace.single k 1 : Euc d)) := by
    simp_rw [s113a_update_eq]
    fun_prop
  have h0 : Function.update X i (X i + (0 : ℝ) • (EuclideanSpace.single k 1 : Euc d)) = X := by simp
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this.eventually h

theorem s113a_fderiv_clm_const_E {g : EucConfig d N → ℝ} {X : EucConfig d N}
    (hD : DifferentiableAt ℝ (fderiv ℝ g) X) (v w : EucConfig d N) :
    fderiv ℝ (fun Y => fderiv ℝ g Y v) X w = fderiv ℝ (fderiv ℝ g) X w v := by
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

theorem s113a_movPartial2 {g : EucConfig d N → ℝ} {X : EucConfig d N} (hg : ContDiffAt ℝ 2 g X)
    (i : Fin N) (k : Fin d) :
    movPartial (movPartial g i k) i k X =
      fderiv ℝ (fderiv ℝ g) X (HRS.configBasis d N (i, k)) (HRS.configBasis d N (i, k)) := by
  have hev : movPartial g i k =ᶠ[𝓝 X] fun Y => fderiv ℝ g Y (HRS.configBasis d N (i, k)) := by
    filter_upwards [hg.eventually (by norm_num)] with Y hY
    exact s113a_movPartial_eq (hY.differentiableAt (by simp)) i k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) X := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd : DifferentiableAt ℝ (fun Y => fderiv ℝ g Y (HRS.configBasis d N (i, k))) X :=
    hD.clm_apply (differentiableAt_const _)
  rw [s113a_movPartial_congr hev, s113a_movPartial_eq hd, s113a_fderiv_clm_const_E hD]

theorem s113a_slice_hasFDerivAt_local {G : ℝ × EucConfig d N → ℝ} {t : ℝ} {z : EucConfig d N}
    (hG : DifferentiableAt ℝ G (t, z)) :
    HasFDerivAt (fun y : EucConfig d N => G (t, y))
      ((fderiv ℝ G (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ (EucConfig d N))) z := by
  have h1 : HasFDerivAt (fun y : EucConfig d N => ((t, y) : ℝ × EucConfig d N))
      (ContinuousLinearMap.inr ℝ ℝ (EucConfig d N)) z :=
    (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z) |>.congr_fderiv (by ext <;> simp)
  exact hG.hasFDerivAt.comp z h1

theorem s113a_slice_fderiv_local {G : ℝ × EucConfig d N → ℝ} {t : ℝ} {z : EucConfig d N}
    (hG : DifferentiableAt ℝ G (t, z)) (v : EucConfig d N) :
    fderiv ℝ (fun y : EucConfig d N => G (t, y)) z v = fderiv ℝ G (t, z) (0, v) := by
  rw [(s113a_slice_hasFDerivAt_local hG).fderiv]
  rfl

theorem s113a_slice_fderiv2_local {O : Set (ℝ × EucConfig d N)} (hO : IsOpen O) {F : ℝ × EucConfig d N → ℝ}
    (hF : ContDiffOn ℝ ∞ F O) {t : ℝ} {z : EucConfig d N} (hz : (t, z) ∈ O) (v w : EucConfig d N) :
    fderiv ℝ (fderiv ℝ (fun y : EucConfig d N => F (t, y))) z v w =
      fderiv ℝ (fderiv ℝ F) (t, z) (0, v) (0, w) := by
  set L := ContinuousLinearMap.inr ℝ ℝ (EucConfig d N) with hL
  have hFd : ∀ p ∈ O, DifferentiableAt ℝ F p := fun p hp =>
    (hF.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
  have h2F : ContDiffOn ℝ ∞ (fderiv ℝ F) O := hF.fderiv_of_isOpen hO (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ F) (t, z) :=
    (h2F.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hev : fderiv ℝ (fun y : EucConfig d N => F (t, y)) =ᶠ[𝓝 z] fun y =>
      (ContinuousLinearMap.compL ℝ (EucConfig d N) (ℝ × EucConfig d N) ℝ).flip L (fderiv ℝ F (t, y)) := by
    have hmem : ∀ᶠ y in 𝓝 z, (t, y) ∈ O :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually_mem (hO.mem_nhds hz)
    filter_upwards [hmem] with y hy
    exact (s113a_slice_hasFDerivAt_local (hFd _ hy)).fderiv
  have hg : HasFDerivAt (fun y : EucConfig d N => ((t, y) : ℝ × EucConfig d N)) L z :=
    (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z) |>.congr_fderiv (by ext <;> simp [hL])
  have h3 : HasFDerivAt (fun y : EucConfig d N => fderiv ℝ F (t, y))
      ((fderiv ℝ (fderiv ℝ F) (t, z)).comp L) z := hDd.hasFDerivAt.comp z hg
  have h4 := ((ContinuousLinearMap.compL ℝ (EucConfig d N) (ℝ × EucConfig d N) ℝ).flip L).hasFDerivAt.comp z h3
  rw [hev.fderiv_eq]
  exact congrArg (fun M => M v w) h4.fderiv

theorem s113a_weight_eq (s q β : ℝ) (Y : EucConfig d N) (i : Fin N) (k : Fin d) :
    q * (Y i) k + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k =
      -(particleDriftW (quadraticGradientDyn d s q β) Y i) k := by
  have hM : ∀ v : Euc d, Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
    intro v
    simp [Torus.matVec]
  have hg := movtr_gradient_confinement (d := d) q (Y i)
  simp only [particleDriftW, quadraticGradientDyn]
  rw [hg]
  simp only [hM, Finset.sum_neg_distrib, smul_neg, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply,
    smul_eq_mul]
  have : (∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j)) k =
      ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k := by
    simp [WithLp.ofLp_sum]
  rw [this]
  ring

/-- `movFP` of a time slice of a smooth space-time function, through the directional derivatives of the space-time function. -/
theorem s113a_movFP_eq (s q β : ℝ) {O : Set (ℝ × EucConfig d N)} (hO : IsOpen O) {F : ℝ × EucConfig d N → ℝ}
    (hF : ContDiffOn ℝ ∞ F O)
    (hG : ∀ k : Fin N × Fin d, ContDiffOn ℝ ∞ (fun p => F p * s113a_drift d s q β N p k.1 k.2) O)
    {t : ℝ} {z : EucConfig d N} (hz : (t, z) ∈ O) :
    movFP d s q β N (fun Y => F (t, Y)) z =
      β⁻¹ * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) (t, z) (0, HRS.configBasis d N k) (0, HRS.configBasis d N k) -
        ∑ k : Fin N × Fin d, fderiv ℝ (fun p => F p * s113a_drift d s q β N p k.1 k.2) (t, z)
          (0, HRS.configBasis d N k) := by
  have hFa : ContDiffAt ℝ 2 F (t, z) := (hF.contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  have hslice : ContDiffAt ℝ 2 (fun Y : EucConfig d N => F (t, Y)) z :=
    hFa.comp z ((contDiffAt_const.prodMk contDiffAt_id) :
      ContDiffAt ℝ 2 (fun Y : EucConfig d N => ((t, Y) : ℝ × EucConfig d N)) z)
  have hdiff : ∀ k : Fin N × Fin d, DifferentiableAt ℝ (fun p => F p * s113a_drift d s q β N p k.1 k.2) (t, z) :=
    fun k => ((hG k).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hA : ∀ k : Fin N × Fin d, movPartial (movPartial (fun Y => F (t, Y)) k.1 k.2) k.1 k.2 z =
      fderiv ℝ (fderiv ℝ F) (t, z) (0, HRS.configBasis d N k) (0, HRS.configBasis d N k) := by
    intro k
    rw [s113a_movPartial2 hslice k.1 k.2, s113a_slice_fderiv2_local hO hF hz]
  have hB : ∀ k : Fin N × Fin d,
      movPartial (fun Y => F (t, Y) * (q * (Y k.1) k.2 + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase k.1, rieszKernelGrad d s (Y k.1 - Y j) k.2)) k.1 k.2 z =
      -fderiv ℝ (fun p => F p * s113a_drift d s q β N p k.1 k.2) (t, z) (0, HRS.configBasis d N k) := by
    intro k
    have hfun : (fun Y : EucConfig d N => F (t, Y) * (q * (Y k.1) k.2 + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase k.1, rieszKernelGrad d s (Y k.1 - Y j) k.2)) =
        fun Y => -((fun p => F p * s113a_drift d s q β N p k.1 k.2) (t, Y)) := by
      funext Y
      rw [s113a_weight_eq s q β Y k.1 k.2]
      simp only [s113a_drift]
      ring
    rw [hfun, s113a_movPartial_eq, fderiv_fun_neg, ContinuousLinearMap.neg_apply, s113a_slice_fderiv_local (hdiff k)]
    exact ((hdiff k).hasFDerivAt.comp z
      ((hasFDerivAt_const t z).prodMk (hasFDerivAt_id z))).differentiableAt.neg
  unfold movFP
  rw [← Fintype.sum_prod_type' (f := fun i k => β⁻¹ * movPartial (movPartial (fun Y => F (t, Y)) i k) i k z +
      movPartial (fun Y => F (t, Y) * (q * (Y i) k + (1 / (N : ℝ)) *
        ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k)) i k z)]
  simp only [hA, hB]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  ring

end HRS.MS.S113X2

end

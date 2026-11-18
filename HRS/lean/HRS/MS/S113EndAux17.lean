import HRS.MS.S113EndAux16
import HRS.MH.PairingRdP5

/-!
# S11.3 endpoint (worker S11X), part 17: the one-body identity `⟨u(x), F(x)⟩ - (g * D)(x) = ∫ h_u(x,y) dμ(y)`

For a fixed time: `f` a positive `C¹` density with Gaussian-bounded `f, Df`, `u` a `C¹` field with `u, Du` bounded, `F = movForce f`,
`D = div(f u)`, `h_u(x,y) = ⟨u(x) - u(y), ∇g(x-y)⟩` (`commutatorKernel`).

* `S113XSlice`: the hypotheses.
* `s113x_pair_antisym`: `∑_{i≠j} ⟨∇g(X_i - X_j), u(X_i)⟩ = ½ ∑_{i≠j} h_u(X_i, X_j)` off collisions.
* `s113x_onebody`: `∫ h_u(x,y) f(y) dy = ⟨u(x), F(x)⟩ - ∑_k (F^{(k)} of f u_k)_k(x) = ⟨u(x), F(x)⟩ - (g * D)(x)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d N : ℕ}

/-- The fixed-time data. -/
structure S113XSlice (f : Euc d → ℝ) (u : Euc d → Euc d) (c B M : ℝ) : Prop where
  hc : 0 < c
  hB : 0 ≤ B
  hM : 0 ≤ M
  pos : ∀ x, 0 < f x
  cd : ContDiff ℝ 1 f
  g0 : ∀ x, |f x| ≤ B * Real.exp (-c * ‖x‖ ^ 2)
  g1 : ∀ x, ‖fderiv ℝ f x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2)
  ucd : ContDiff ℝ 1 u
  ub : ∀ x, ‖u x‖ ≤ M
  Dub : ∀ x, ‖fderiv ℝ u x‖ ≤ M

/-- The component flux `f u_k`. -/
def s113x_Yk (f : Euc d → ℝ) (u : Euc d → Euc d) (k : Fin d) (y : Euc d) : ℝ := f y * (u y) k

section Yk

variable {f : Euc d → ℝ} {u : Euc d → Euc d} {c B M : ℝ}

theorem s113x_coord_norm_le (v : Euc d) (k : Fin d) : |v k| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v k
  simpa [Real.norm_eq_abs] using this

theorem S113XSlice.Yk_cd (S : S113XSlice f u c B M) (k : Fin d) : ContDiff ℝ 1 (s113x_Yk f u k) := by
  unfold s113x_Yk
  have hu : ContDiff ℝ 1 (fun y => (u y) k) :=
    ((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff).comp S.ucd
  exact S.cd.mul hu

theorem S113XSlice.Yk_fderiv (S : S113XSlice f u c B M) (k : Fin d) (y v : Euc d) :
    fderiv ℝ (s113x_Yk f u k) y v = fderiv ℝ f y v * (u y) k + f y * (fderiv ℝ u y v) k := by
  have hf : HasFDerivAt f (fderiv ℝ f y) y := (S.cd.differentiable (by norm_num) y).hasFDerivAt
  have hu : HasFDerivAt u (fderiv ℝ u y) y := (S.ucd.differentiable (by norm_num) y).hasFDerivAt
  have hk := (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y hu
  have h2 : HasFDerivAt (fun y => f y * (u y) k) (f y • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).comp (fderiv ℝ u y) +
      (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ) (u y) • fderiv ℝ f y) y := hf.mul hk
  unfold s113x_Yk
  rw [h2.fderiv]
  simp [add_comm, mul_comm]

theorem S113XSlice.Yk_g0 (S : S113XSlice f u c B M) (k : Fin d) (y : Euc d) :
    |s113x_Yk f u k y| ≤ (B * M) * Real.exp (-c * ‖y‖ ^ 2) := by
  unfold s113x_Yk
  rw [abs_mul]
  calc |f y| * |(u y) k| ≤ (B * Real.exp (-c * ‖y‖ ^ 2)) * M :=
        mul_le_mul (S.g0 y) ((s113x_coord_norm_le _ k).trans (S.ub y)) (abs_nonneg _) (by have := S.hB; positivity)
    _ = (B * M) * Real.exp (-c * ‖y‖ ^ 2) := by ring

theorem S113XSlice.Yk_g1 (S : S113XSlice f u c B M) (k : Fin d) (y : Euc d) :
    ‖fderiv ℝ (s113x_Yk f u k) y‖ ≤ (2 * (B * M)) * Real.exp (-c * ‖y‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := S.hB; have := S.hM; positivity) fun v => ?_
  rw [S.Yk_fderiv k y v, Real.norm_eq_abs]
  have h1 : |fderiv ℝ f y v| ≤ B * Real.exp (-c * ‖y‖ ^ 2) * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (S.g1 y) (norm_nonneg _))
  have h2 : |(fderiv ℝ u y v) k| ≤ M * ‖v‖ :=
    (s113x_coord_norm_le _ k).trans ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (S.Dub y) (norm_nonneg _)))
  have hM := S.hM
  have hB := S.hB
  have hu : |(u y) k| ≤ M := (s113x_coord_norm_le _ k).trans (S.ub y)
  have hE := Real.exp_pos (-c * ‖y‖ ^ 2)
  calc |fderiv ℝ f y v * (u y) k + f y * (fderiv ℝ u y v) k|
      ≤ |fderiv ℝ f y v| * |(u y) k| + |f y| * |(fderiv ℝ u y v) k| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ (B * Real.exp (-c * ‖y‖ ^ 2) * ‖v‖) * M + (B * Real.exp (-c * ‖y‖ ^ 2)) * (M * ‖v‖) := by
        gcongr
        · exact S.g0 y
    _ = (2 * (B * M)) * Real.exp (-c * ‖y‖ ^ 2) * ‖v‖ := by ring

end Yk

theorem s113x_pair_antisym (s : ℝ) (u : Euc d → Euc d) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X i)) =
      (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commutatorKernel d s u (X i) (X j) := by
  set φ : Fin N → Fin N → ℝ := fun i j => inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X i)) with hφ
  have hswap : ∑ i, ∑ j ∈ Finset.univ.erase i, φ i j = ∑ i, ∑ j ∈ Finset.univ.erase i, φ j i := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.univ.erase i)
      (s' := fun j => Finset.univ.erase j) (t' := Finset.univ) (f := fun i j => φ i j)]
    intro x y
    simp [Finset.mem_erase, eq_comm]
  have hodd : ∑ i, ∑ j ∈ Finset.univ.erase i, φ j i =
      -∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (rieszKernelGrad d s (X i - X j)) (u (X j)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : X i - X j ≠ 0 := fun h => hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, sub_eq_zero.1 h⟩
    simp only [hφ]
    rw [show X j - X i = -(X i - X j) by abel, s113x_G_neg s hne, inner_neg_left]
  have h2 : (∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) + (∑ i, ∑ j ∈ Finset.univ.erase i, φ i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, commutatorKernel d s u (X i) (X j) := by
    nth_rewrite 2 [hswap]
    rw [hodd, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hφ, commutatorKernel]
    rw [inner_sub_left, real_inner_comm, real_inner_comm (u (X j))]
  linarith


section Integrable

variable {s : ℝ}

theorem s113x_gauss_integrable (hd : 1 ≤ d) {c B' : ℝ} (hc : 0 < c) {h : Euc d → ℝ} (hm : AEStronglyMeasurable h volume)
    (h0 : ∀ y, |h y| ≤ B' * Real.exp (-c * ‖y‖ ^ 2)) : Integrable h := by
  have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hg := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c) (by linarith) hc
  simp only [Real.rpow_zero, one_mul] at hg
  refine (hg.const_mul B').mono' hm (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact h0 y

theorem s113x_lip_bound {h : Euc d → ℝ} {Λ : ℝ} (hh : Differentiable ℝ h) (hΛ : ∀ y, ‖fderiv ℝ h y‖ ≤ Λ)
    (x z : Euc d) : |h (x - z) - h x| ≤ Λ * ‖z‖ := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hL : LipschitzWith Λ.toNNReal h := by
    refine lipschitzWith_of_nnnorm_fderiv_le hh fun y => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hΛ0]
    exact hΛ y
  have := hL.dist_le_mul (x - z) x
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hΛ0] at this
  simpa using this

theorem s113x_ci_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ} {Λ c B' : ℝ} (hc : 0 < c)
    (hh : ContDiff ℝ 1 h) (h0 : ∀ y, |h y| ≤ B' * Real.exp (-c * ‖y‖ ^ 2)) (hΛ : ∀ y, ‖fderiv ℝ h y‖ ≤ Λ) (x : Euc d) :
    Integrable (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) h x) volume := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  refine (HRS.MH.PairingRdP.integrable_conv_rd hd hs0 hsd (h := h) (Λ := Λ) (β := 1) hh.continuous.measurable
    (s113x_gauss_integrable hd hc hh.continuous.aestronglyMeasurable h0) hΛ0 (by linarith) ?_).1 x
  intro x' z _
  rw [Real.rpow_one]
  exact s113x_lip_bound (hh.differentiable (by norm_num)) hΛ x' z

theorem s113x_force_comp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ} {Λ c B' : ℝ} (hc : 0 < c)
    (hh : ContDiff ℝ 1 h) (h0 : ∀ y, |h y| ≤ B' * Real.exp (-c * ‖y‖ ^ 2)) (hΛ : ∀ y, ‖fderiv ℝ h y‖ ≤ Λ)
    (x : Euc d) (k : Fin d) :
    (movForce d s h x) k = ∫ y, (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) h x y) k := by
  have hint := s113x_ci_integrable hd hs0 hsd hc hh h0 hΛ x
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ) hint
  have e : (∫ y, HRS.MH.PairingRd.convInt (rieszKernelGrad d s) h x y) = movForce d s h x := rfl
  rw [e] at this
  simpa using this.symm

theorem s113x_ci_pointwise {s : ℝ} (f : Euc d → ℝ) (u : Euc d → Euc d) (x y : Euc d) (k : Fin d) :
    f y * ((u x k - u y k) * (rieszKernelGrad d s (x - y)) k) =
      u x k * (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) f x y) k -
        (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) (s113x_Yk f u k) x y) k := by
  unfold HRS.MH.PairingRd.convInt s113x_Yk
  by_cases h : ‖x - y‖ ≤ 1 / 4
  · simp only [h, ite_true, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [h, ite_false, PiLp.smul_apply, smul_eq_mul]
    ring

theorem S113XSlice.movDiv_flux {f : Euc d → ℝ} {u : Euc d → Euc d} {c B M : ℝ} (S : S113XSlice f u c B M) (y : Euc d) :
    movDiv (fun y => f y • u y) y =
      ∑ k, fderiv ℝ (s113x_Yk f u k) y (EuclideanSpace.single k (1 : ℝ)) := by
  have hf : HasFDerivAt f (fderiv ℝ f y) y := (S.cd.differentiable (by norm_num) y).hasFDerivAt
  have hu : HasFDerivAt u (fderiv ℝ u y) y := (S.ucd.differentiable (by norm_num) y).hasFDerivAt
  have h := hf.smul hu
  unfold movDiv
  rw [show fderiv ℝ (fun y => f y • u y) y = f y • fderiv ℝ u y + (fderiv ℝ f y).smulRight (u y) from h.fderiv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [S.Yk_fderiv k y]
  simp [mul_comm, add_comm]

theorem s113x_onebody (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} {u : Euc d → Euc d} {c B M : ℝ}
    (S : S113XSlice f u c B M) (x : Euc d) :
    ∫ y, commutatorKernel d s u x y ∂(HRS.Whole.withDensityReal f) =
      inner ℝ (u x) (movForce d s f x) -
        ∫ z, rieszKernel d s z * movDiv (fun y => f y • u y) (x - z) := by
  have hB := S.hB
  have hM := S.hM
  have hc := S.hc
  have hfm : Measurable f := S.cd.continuous.measurable
  have hf0 : ∀ y, 0 ≤ f y := fun y => (S.pos y).le
  rw [HRS.MP.RdRem.mrr_integral_withDensityReal f hfm hf0]
  have hΛf : ∀ y, ‖fderiv ℝ f y‖ ≤ B := fun y =>
    (S.g1 y).trans (mul_le_of_le_one_right hB (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])))
  have hΛY : ∀ k y, ‖fderiv ℝ (s113x_Yk f u k) y‖ ≤ 2 * (B * M) := fun k y =>
    (S.Yk_g1 k y).trans (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])))
  have hfint := s113x_ci_integrable hd hs0 hsd hc S.cd S.g0 hΛf x
  have hYint : ∀ k, Integrable (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) (s113x_Yk f u k) x) volume := fun k =>
    s113x_ci_integrable hd hs0 hsd hc (S.Yk_cd k) (S.Yk_g0 k) (hΛY k) x
  have hfcomp : ∀ k, Integrable (fun y => (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) f x y) k) volume := fun k =>
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).integrable_comp hfint
  have hYcomp : ∀ k, Integrable (fun y => (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) (s113x_Yk f u k) x y) k) volume :=
    fun k => (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).integrable_comp (hYint k)
  -- the integrand as a sum over coordinates
  have hsum : ∀ y, f y * commutatorKernel d s u x y = ∑ k, (u x k * (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) f x y) k -
      (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) (s113x_Yk f u k) x y) k) := by
    intro y
    simp only [← s113x_ci_pointwise]
    unfold commutatorKernel
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  simp only [hsum]
  have hI : ∀ k : Fin d, Integrable (fun y => u x k * (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) f x y) k -
      (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) (s113x_Yk f u k) x y) k) volume := fun k =>
    ((hfcomp k).const_mul (u x k)).sub (hYcomp k)
  rw [integral_finsetSum _ (fun k _ => hI k)]
  have hk : ∀ k, ∫ y, (u x k * (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) f x y) k -
      (HRS.MH.PairingRd.convInt (rieszKernelGrad d s) (s113x_Yk f u k) x y) k) =
      u x k * (movForce d s f x) k - (movForce d s (s113x_Yk f u k) x) k := by
    intro k
    rw [integral_sub ((hfcomp k).const_mul (u x k)) (hYcomp k), integral_const_mul,
      ← s113x_force_comp hd hs0 hsd hc S.cd S.g0 hΛf x k,
      ← s113x_force_comp hd hs0 hsd hc (S.Yk_cd k) (S.Yk_g0 k) (hΛY k) x k]
  simp only [hk]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  · set C : ℝ := 2 * (B * M) with hC
    have hC0 : 0 ≤ C := by positivity
    have hY0 : ∀ k y, |s113x_Yk f u k y| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := fun k y =>
      (S.Yk_g0 k y).trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hB hM]) (Real.exp_pos _).le)
    have hk' : ∀ k, (movForce d s (s113x_Yk f u k) x) k =
        ∫ z, rieszKernel d s z * (fderiv ℝ (s113x_Yk f u k) (x - z) (EuclideanSpace.single k (1 : ℝ))) := by
      intro k
      have := HRS.MS.MovForce.mv1_force_eq_conv_grad hd hs0 hsd hc hC0 (S.Yk_cd k) (hY0 k) (S.Yk_g1 k) x k
      rw [this, HRS.MS.MovForce.mv1_convFun_eq]
    obtain ⟨A0, A1, hA0, hA1, hbd⟩ := s113x_conv_bound hd hs0 hsd (s := s) hc
    have hφint : ∀ k, Integrable (fun z => rieszKernel d s z *
        (fderiv ℝ (s113x_Yk f u k) (x - z) (EuclideanSpace.single k (1 : ℝ)))) volume := by
      intro k
      refine (hbd C (fun y => fderiv ℝ (s113x_Yk f u k) y (EuclideanSpace.single k (1 : ℝ))) hC0 ?_ ?_ x).1
      · exact ((S.Yk_cd k).continuous_fderiv (by norm_num)).clm_apply continuous_const
      · intro y
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have : ‖(EuclideanSpace.single k (1 : ℝ) : Euc d)‖ = 1 := by simp
        rw [this, mul_one]
        exact S.Yk_g1 k y
    simp only [hk']
    rw [← integral_finsetSum _ (fun k _ => hφint k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [S.movDiv_flux, Finset.mul_sum]

end Integrable

end HRS.MS.S113BD

end

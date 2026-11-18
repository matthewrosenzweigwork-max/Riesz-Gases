import HRS.Whole.HeadlineStatement
import HRS.MS.Comm
import HRS.MS.WrRowAux2
import HRS.MS.FcauTie

/-!
# S5.3 (`field_remainder`), part 1: the commutator functional `D_μ(h_f)` on `C_b²`

`s53_Dk s ρ f X = D_μ(h_f)(X)`, `μ = ρ dx`, `h_f = (∇f(x)-∇f(y))·∇g(x-y)`; this is exactly the integrand of
`commForcing` (`commForcing C s m μ X α t r ζ = s53_Dk s ρ (propagatorW C r t (oscTestFun m α)) (X r ζ)` for
`μ = withDensityReal ρ`).

* the kernel bound `|h_f(x,y)| ≤ (s+1)Λ(1 + W_s(x-y))` for every pair `(x,y)` (also `x = y`, where `h_f = 0`), for
  `Λ` a Lipschitz constant of `∇f` (`s53_grad_lip`: `Λ = sup‖D²f‖`);
* the background integrals are bounded uniformly in the base point by the row bound `wr3_lintegral_W_row`
  (`s53_rowConst`), so that `D` is linear on `C_b²` for **every** configuration `X` and
  `|D f (X)| ≤ (s+1) sup‖D²f‖ cX(X)` with the finite real `cX(X)` (`s53_D_bound`);
* no collision-free hypothesis is used anywhere (the bound holds on the diagonal too);
* joint measurability (`s53_D_measurable`) and the differentiability of `τ ↦ D(G τ)(X)` from the `C_b²`
  difference-quotient property (`s53_D_hasDerivWithinAt`).

Helper names carry the prefix `s53_`, namespace `HRS.MS.S53`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d N : ℕ}

/-- `D_μ(h_f)(X)` for `μ = ρ dx`. -/
def s53_Dk (s : ℝ) (ρ : Euc d → ℝ) (f : Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  centeredPairFunctional (commutatorKernel d s (fun x => gradient f x)) X (HRS.Whole.withDensityReal ρ)

/-! ### Lipschitz constant of the gradient -/

lemma s53_cbSup_nonneg (f : Euc d → ℝ) : 0 ≤ ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

lemma s53_grad_lip {f : Euc d → ℝ} (hf : MemCb 2 f) :
    LipschitzWith (Real.toNNReal (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖)) (fun x => gradient f x) := by
  have hbdd := hf.2 2 le_rfl
  have hc2 : ContDiff ℝ 2 f := hf.1
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : LipschitzWith (Real.toNNReal (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖)) (fderiv ℝ f) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdf fun z => ?_
    have h2 : ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [← NNReal.coe_le_coe, coe_nnnorm, h2, Real.coe_toNNReal _ (s53_cbSup_nonneg f)]
    exact le_ciSup hbdd z
  have h3 : LipschitzWith 1 (fun p : Euc d →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ (Euc d)).symm p) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.isometry.lipschitzWith
  have h4 := h3.comp h1
  simp only [one_mul] at h4
  exact h4

/-! ### The kernel bound -/

lemma s53_comm_bound {s : ℝ} (hs0 : 0 ≤ s) {Λ : ℝ≥0} {v : Euc d → Euc d} (hv : LipschitzWith Λ v)
    (x y : Euc d) :
    |commutatorKernel d s v x y| ≤ (s + 1) * (Λ : ℝ) * (1 + rieszWeight s (x - y)) := by
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  have hW : 0 ≤ rieszWeight s (x - y) := HRS.MS.Wr.wr3_rieszWeight_nonneg s _
  have hR : 0 ≤ (s + 1) * (Λ : ℝ) * (1 + rieszWeight s (x - y)) := by positivity
  by_cases hxy : x = y
  · subst hxy
    simp only [commutatorKernel, sub_self, inner_zero_left, abs_zero]
    simpa using hR
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
    have hG : ‖rieszKernelGrad d 0 (x - y)‖ = ‖x - y‖⁻¹ := by
      rw [movtr_rieszKernelGrad_norm 0 le_rfl hz]
      norm_num [movtr_sigma, Real.rpow_neg_one]
    have key : |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) := by
      unfold commutatorKernel
      calc |inner ℝ (v x - v y) (rieszKernelGrad d 0 (x - y))|
          ≤ ‖v x - v y‖ * ‖rieszKernelGrad d 0 (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ ((Λ : ℝ) * ‖x - y‖) * ‖x - y‖⁻¹ :=
            mul_le_mul (HRS.MS.Comm.comm_lip hv x y) hG.le (norm_nonneg _) (by positivity)
        _ = (Λ : ℝ) := by rw [mul_assoc, mul_inv_cancel₀ hzpos.ne', mul_one]
    calc |commutatorKernel d 0 v x y| ≤ (Λ : ℝ) := key
      _ ≤ (0 + 1) * (Λ : ℝ) * (1 + rieszWeight 0 (x - y)) := by nlinarith
  · have := HRS.MS.Comm.comm_bound_pos hpos Λ v hv x y hxy
    refine this.trans ?_
    have h1 : s * (Λ : ℝ) * (1 + rieszWeight s (x - y)) ≤
        (s + 1) * (Λ : ℝ) * (1 + rieszWeight s (x - y)) := by
      have : 0 ≤ (Λ : ℝ) * (1 + rieszWeight s (x - y)) := by positivity
      nlinarith
    exact h1

/-! ### Uniform row bound -/

lemma s53_rowConst (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    ∃ Mρ : ℝ, 0 ≤ Mρ ∧ ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal Mρ := by
  refine ⟨max 0 (1 + (1 + 4 / (d : ℝ)) *
    (M * HRS.sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) + 1)), le_max_left _ _,
    fun x => ?_⟩
  exact (HRS.MS.Wr.wr3_lintegral_W_row hd hs0 hsd hρ hM x).trans
    (ENNReal.ofReal_le_ofReal (le_max_right _ _))


/-! ### Integrability of the kernel rows and linearity -/

section Kernel

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ}

lemma s53_ker_row (hs0 : 0 ≤ s) {Λ : ℝ≥0} {v : Euc d → Euc d} (hv : LipschitzWith Λ v)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (x : Euc d) :
    Integrable (fun y => commutatorKernel d s v x y) (HRS.Whole.withDensityReal ρ) ∧
      ∫⁻ y, ‖commutatorKernel d s v x y‖ₑ ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal ((s + 1) * (Λ : ℝ) * Mρ) := by
  have hm0 : Measurable fun p : Euc d × Euc d => commutatorKernel d s v p.1 p.2 :=
    HRS.MS.Comm.comm_meas (s := s) v hv.continuous.measurable
  have hmeas : Measurable fun y => commutatorKernel d s v x y :=
    Measurable.of_uncurry_left (f := fun x y => commutatorKernel d s v x y) hm0
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  have hc : 0 ≤ (s + 1) * (Λ : ℝ) := by positivity
  have hb : ∫⁻ y, ‖commutatorKernel d s v x y‖ₑ ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal ((s + 1) * (Λ : ℝ) * Mρ) := by
    calc ∫⁻ y, ‖commutatorKernel d s v x y‖ₑ ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal ((s + 1) * (Λ : ℝ)) *
            ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_mul hc, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (s53_comm_bound hs0 hv x y)
      _ = ENNReal.ofReal ((s + 1) * (Λ : ℝ)) *
            ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((s + 1) * (Λ : ℝ)) * ENNReal.ofReal Mρ := by gcongr; exact hrow x
      _ = ENNReal.ofReal ((s + 1) * (Λ : ℝ) * Mρ) := by rw [ENNReal.ofReal_mul hc]
  exact ⟨⟨hmeas.aestronglyMeasurable, lt_of_le_of_lt hb ENNReal.ofReal_lt_top⟩, hb⟩

lemma s53_ker_row_norm (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) {Λ : ℝ≥0} {v : Euc d → Euc d}
    (hv : LipschitzWith Λ v)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (x : Euc d) :
    ‖∫ y, commutatorKernel d s v x y ∂(HRS.Whole.withDensityReal ρ)‖ ≤ (s + 1) * (Λ : ℝ) * Mρ := by
  obtain ⟨hi, hb⟩ := s53_ker_row hs0 hv hrow x
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := NNReal.coe_nonneg Λ
  have hc : 0 ≤ (s + 1) * (Λ : ℝ) * Mρ := by positivity
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hc hb

lemma s53_ker_outer (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ) {Λ : ℝ≥0}
    {v : Euc d → Euc d} (hv : LipschitzWith Λ v)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) :
    Integrable (fun x => ∫ y, commutatorKernel d s v x y ∂(HRS.Whole.withDensityReal ρ))
        (HRS.Whole.withDensityReal ρ) ∧
      ‖∫ x, ∫ y, commutatorKernel d s v x y ∂(HRS.Whole.withDensityReal ρ)
          ∂(HRS.Whole.withDensityReal ρ)‖ ≤ (s + 1) * (Λ : ℝ) * Mρ := by
  have := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hmeas : Measurable fun p : Euc d × Euc d => commutatorKernel d s v p.1 p.2 :=
    HRS.MS.Comm.comm_meas (s := s) v hv.continuous.measurable
  have hsm : StronglyMeasurable fun x : Euc d =>
      ∫ y, commutatorKernel d s v x y ∂(HRS.Whole.withDensityReal ρ) :=
    hmeas.stronglyMeasurable.integral_prod_right' (ν := HRS.Whole.withDensityReal ρ)
  have hbd : ∀ x, ‖∫ y, commutatorKernel d s v x y ∂(HRS.Whole.withDensityReal ρ)‖ ≤
      (s + 1) * (Λ : ℝ) * Mρ := s53_ker_row_norm hs0 hM0 hv hrow
  refine ⟨Integrable.of_bound hsm.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd), ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := HRS.Whole.withDensityReal ρ)
    (f := fun x => ∫ y, commutatorKernel d s v x y ∂(HRS.Whole.withDensityReal ρ))
    (C := (s + 1) * (Λ : ℝ) * Mρ) (Filter.Eventually.of_forall hbd)
  simpa using this

lemma s53_cPF_sub {h1 h2 : Euc d → Euc d → ℝ} (X : EucConfig d N) {ν : Measure (Euc d)}
    (hi1 : ∀ x, Integrable (fun y => h1 x y) ν) (hi2 : ∀ x, Integrable (fun y => h2 x y) ν)
    (ho1 : Integrable (fun x => ∫ y, h1 x y ∂ν) ν) (ho2 : Integrable (fun x => ∫ y, h2 x y ∂ν) ν) :
    centeredPairFunctional (fun x y => h1 x y - h2 x y) X ν =
      centeredPairFunctional h1 X ν - centeredPairFunctional h2 X ν := by
  unfold centeredPairFunctional
  have e1 : ∀ x, ∫ y, (h1 x y - h2 x y) ∂ν = ∫ y, h1 x y ∂ν - ∫ y, h2 x y ∂ν :=
    fun x => integral_sub (hi1 x) (hi2 x)
  simp only [e1, integral_sub ho1 ho2, Finset.sum_sub_distrib, mul_sub]
  ring

lemma s53_cPF_const_mul (c : ℝ) {h : Euc d → Euc d → ℝ} (X : EucConfig d N) (ν : Measure (Euc d)) :
    centeredPairFunctional (fun x y => c * h x y) X ν = c * centeredPairFunctional h X ν := by
  unfold centeredPairFunctional
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

end Kernel


/-! ### `D` on `C_b²` -/

section Dk

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ}

lemma s53_gradient_const_mul (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (x : Euc d) :
    gradient (fun x => c * f x) x = c • gradient f x := by
  ext i
  rw [q09_gradient_apply, PiLp.smul_apply, q09_gradient_apply,
    fderiv_const_mul (hf.differentiable one_ne_zero x) c]
  simp

lemma s53_memCb_const_mul (c : ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) : MemCb 2 (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hf.2 j hj
  refine ⟨|c| * B, ?_⟩
  rintro _ ⟨x, rfl⟩
  have e : iteratedFDeriv ℝ j (fun x => c * f x) x = c • iteratedFDeriv ℝ j f x := by
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (a := c) (f := f) (x := x)
      (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
    have e2 : (fun x => c * f x) = c • f := by funext x; simp
    rw [e2]
    exact this
  show ‖iteratedFDeriv ℝ j (fun x => c * f x) x‖ ≤ |c| * B
  rw [e, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB ⟨x, rfl⟩) (abs_nonneg c)

lemma s53_kernel_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x y : Euc d) :
    commutatorKernel d s (fun x => gradient (fun x => f x - g x) x) x y =
      commutatorKernel d s (fun x => gradient f x) x y -
        commutatorKernel d s (fun x => gradient g x) x y := by
  unfold commutatorKernel
  beta_reduce
  rw [HRS.MS.Fcau.fcau_gradient_sub hf hg x, HRS.MS.Fcau.fcau_gradient_sub hf hg y,
    ← inner_sub_left]
  congr 1
  abel

lemma s53_kernel_const_mul (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (x y : Euc d) :
    commutatorKernel d s (fun x => gradient (fun x => c * f x) x) x y =
      c * commutatorKernel d s (fun x => gradient f x) x y := by
  unfold commutatorKernel
  beta_reduce
  rw [s53_gradient_const_mul c hf x, s53_gradient_const_mul c hf y, ← smul_sub, real_inner_smul_left]

lemma s53_Dk_const_mul (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (X : EucConfig d N) :
    s53_Dk s ρ (fun x => c * f x) X = c * s53_Dk s ρ f X := by
  unfold s53_Dk
  have : commutatorKernel d s (fun x => gradient (fun x => c * f x) x) =
      fun x y => c * commutatorKernel d s (fun x => gradient f x) x y := by
    funext x y; exact s53_kernel_const_mul c hf x y
  rw [this]
  exact s53_cPF_const_mul c X _

lemma s53_Dk_sub (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g) (X : EucConfig d N) :
    s53_Dk s ρ (fun x => f x - g x) X = s53_Dk s ρ f X - s53_Dk s ρ g X := by
  unfold s53_Dk
  have : commutatorKernel d s (fun x => gradient (fun x => f x - g x) x) =
      fun x y => commutatorKernel d s (fun x => gradient f x) x y -
        commutatorKernel d s (fun x => gradient g x) x y := by
    funext x y; exact s53_kernel_sub (hf.1.of_le (by norm_num)) (hg.1.of_le (by norm_num)) x y
  rw [this]
  exact s53_cPF_sub X (fun x => (s53_ker_row hs0 (s53_grad_lip hf) hrow x).1)
    (fun x => (s53_ker_row hs0 (s53_grad_lip hg) hrow x).1)
    (s53_ker_outer hs0 hM0 hρ (s53_grad_lip hf) hrow).1
    (s53_ker_outer hs0 hM0 hρ (s53_grad_lip hg) hrow).1


/-- The finite, configuration-dependent constant in the bound of `D`. -/
def s53_cX (s Mρ : ℝ) (X : EucConfig d N) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, (1 + rieszWeight s (X i - X j)) + 3 * Mρ

lemma s53_cX_nonneg (hM0 : 0 ≤ Mρ) (X : EucConfig d N) : 0 ≤ s53_cX s Mρ X := by
  unfold s53_cX
  have h : ∀ i j : Fin N, 0 ≤ 1 + rieszWeight s (X i - X j) := fun i j => by
    have := HRS.MS.Wr.wr3_rieszWeight_nonneg s (X i - X j); linarith
  have h2 : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (1 + rieszWeight s (X i - X j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => h i j
  positivity

lemma s53_Dk_bound (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (hN : 0 < N) {f : Euc d → ℝ} (hf : MemCb 2 f) (X : EucConfig d N) :
    |s53_Dk s ρ f X| ≤ (s + 1) * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) * s53_cX s Mρ X := by
  set Λ : ℝ≥0 := Real.toNNReal (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) with hΛdef
  have hΛ : (Λ : ℝ) = ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖ := Real.coe_toNNReal _ (s53_cbSup_nonneg f)
  have hv := s53_grad_lip hf
  rw [← hΛ]
  have hΛ0 : (0 : ℝ) ≤ Λ := NNReal.coe_nonneg Λ
  have hc0 : 0 ≤ (s + 1) * (Λ : ℝ) := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set k := commutatorKernel d s (fun x => gradient f x) with hk
  have hk1 : ∀ x y, |k x y| ≤ (s + 1) * (Λ : ℝ) * (1 + rieszWeight s (x - y)) :=
    fun x y => s53_comm_bound hs0 hv x y
  have hT1 : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤
      (s + 1) * (Λ : ℝ) * ((1 / (N : ℝ) ^ 2) *
        ∑ i, ∑ j ∈ Finset.univ.erase i, (1 + rieszWeight s (X i - X j))) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2)]
    have h1 : |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤
        ∑ i, ∑ j ∈ Finset.univ.erase i, (s + 1) * (Λ : ℝ) * (1 + rieszWeight s (X i - X j)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hk1 _ _)
    calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)|
        ≤ 1 / (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, (s + 1) * (Λ : ℝ) *
            (1 + rieszWeight s (X i - X j)) := by gcongr
      _ = _ := by simp only [← Finset.mul_sum]; ring
  have hB : ∀ x, |∫ y, k x y ∂(HRS.Whole.withDensityReal ρ)| ≤ (s + 1) * (Λ : ℝ) * Mρ := fun x => by
    have := s53_ker_row_norm hs0 hM0 hv hrow x
    rwa [Real.norm_eq_abs] at this
  have hT2 : |(1 / (N : ℝ)) * ∑ i, ∫ y, k (X i) y ∂(HRS.Whole.withDensityReal ρ)| ≤
      (s + 1) * (Λ : ℝ) * Mρ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    have h1 : |∑ i, ∫ y, k (X i) y ∂(HRS.Whole.withDensityReal ρ)| ≤
        ∑ _i : Fin N, (s + 1) * (Λ : ℝ) * Mρ :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hB (X i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    calc 1 / (N : ℝ) * |∑ i, ∫ y, k (X i) y ∂(HRS.Whole.withDensityReal ρ)|
        ≤ 1 / (N : ℝ) * ((N : ℝ) * ((s + 1) * (Λ : ℝ) * Mρ)) := by gcongr
      _ = _ := by field_simp
  have hT3 : |∫ x, ∫ y, k x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ)| ≤
      (s + 1) * (Λ : ℝ) * Mρ := by
    have := (s53_ker_outer hs0 hM0 hρ hv hrow).2
    rwa [Real.norm_eq_abs] at this
  unfold s53_Dk centeredPairFunctional s53_cX
  rw [← hk]
  have h1 := abs_le.1 hT1
  have h2 := abs_le.1 hT2
  have h3 := abs_le.1 hT3
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

lemma s53_Dk_lip (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (hN : 0 < N) {f g : Euc d → ℝ} (hf : MemCb 2 f) (hg : MemCb 2 g)
    (X : EucConfig d N) :
    |s53_Dk s ρ f X - s53_Dk s ρ g X| ≤
      (s + 1) * (⨆ x, ‖iteratedFDeriv ℝ 2 (fun x => f x - g x) x‖) * s53_cX s Mρ X := by
  rw [← s53_Dk_sub hs0 hM0 hρ hrow hf hg X]
  exact s53_Dk_bound hs0 hM0 hρ hrow hN (HRS.MS.Fcau.fcau_memCb_sub hf hg) X


end Dk

/-! ### Joint measurability -/

section Meas

variable {s : ℝ} {ρ : Euc d → ℝ}

def s53_H (s : ℝ) (F : ℝ → Euc d → ℝ) (τ : ℝ) (x y : Euc d) : ℝ :=
  inner ℝ (gradient (F τ) x - gradient (F τ) y) (rieszKernelGrad d s (x - y))

lemma s53_H_meas {α : Type*} [MeasurableSpace α] {F : ℝ → Euc d → ℝ}
    (hF : Measurable fun p : ℝ × Euc d => gradient (F p.1) p.2) {t : α → ℝ} {x y : α → Euc d}
    (ht : Measurable t) (hx : Measurable x) (hy : Measurable y) :
    Measurable fun a => s53_H s F (t a) (x a) (y a) := by
  have h1 : Measurable fun a => gradient (F (t a)) (x a) := hF.comp (ht.prodMk hx)
  have h2 : Measurable fun a => gradient (F (t a)) (y a) := hF.comp (ht.prodMk hy)
  have h3 : Measurable fun a => rieszKernelGrad d s (x a - y a) :=
    (movtr_rieszKernelGrad_measurable (d := d) s).comp (hx.sub hy)
  exact (h1.sub h2).inner h3

lemma s53_Dk_measurable (hρ : HRS.Whole.IsProbDensity ρ) {F : ℝ → Euc d → ℝ}
    (hF : Measurable fun p : ℝ × Euc d => gradient (F p.1) p.2) :
    Measurable fun p : ℝ × EucConfig d N => s53_Dk s ρ (F p.1) p.2 := by
  have := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hHq : Measurable fun q : (ℝ × Euc d) × Euc d => s53_H s F q.1.1 q.1.2 q.2 :=
    s53_H_meas hF (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
  have hm2 : Measurable fun q : ℝ × Euc d => ∫ y, s53_H s F q.1 q.2 y ∂(HRS.Whole.withDensityReal ρ) :=
    (hHq.stronglyMeasurable.integral_prod_right' (ν := HRS.Whole.withDensityReal ρ)).measurable
  have hm3 : Measurable fun τ : ℝ => ∫ x, ∫ y, s53_H s F τ x y ∂(HRS.Whole.withDensityReal ρ)
      ∂(HRS.Whole.withDensityReal ρ) :=
    (hm2.stronglyMeasurable.integral_prod_right' (ν := HRS.Whole.withDensityReal ρ)).measurable
  have e : (fun p : ℝ × EucConfig d N => s53_Dk s ρ (F p.1) p.2) = fun p =>
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, s53_H s F p.1 (p.2 i) (p.2 j)
        - 2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, s53_H s F p.1 (p.2 i) y ∂(HRS.Whole.withDensityReal ρ))
        + ∫ x, ∫ y, s53_H s F p.1 x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) := by
    funext p
    simp only [s53_Dk, centeredPairFunctional, commutatorKernel, s53_H]
  rw [e]
  have hp : ∀ i : Fin N, Measurable fun p : ℝ × EucConfig d N => (p.1, p.2 i) :=
    fun i => measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hT1 : Measurable fun p : ℝ × EucConfig d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, s53_H s F p.1 (p.2 i) (p.2 j) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact s53_H_meas (t := fun p : ℝ × EucConfig d N => p.1) (x := fun p => p.2 i) (y := fun p => p.2 j) hF
      measurable_fst ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_snd)
  have hT2 : Measurable fun p : ℝ × EucConfig d N =>
      ∑ i, ∫ y, s53_H s F p.1 (p.2 i) y ∂(HRS.Whole.withDensityReal ρ) :=
    Finset.measurable_sum _ fun i _ => by
      have := hm2.comp (hp i)
      exact this
  have hT3 : Measurable fun p : ℝ × EucConfig d N =>
      ∫ x, ∫ y, s53_H s F p.1 x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) :=
    hm3.comp measurable_fst
  exact ((hT1.const_mul _).sub ((hT2.const_mul _).const_mul _)).add hT3
end Meas

/-! ### Differentiability in the time parameter -/

section Deriv

variable {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ}

lemma s53_Dk_hasDerivWithinAt (hs0 : 0 ≤ s) (hM0 : 0 ≤ Mρ) (hρ : HRS.Whole.IsProbDensity ρ)
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal Mρ) (hN : 0 < N) {T : ℝ} {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hdiff : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → |h| < δ →
      τ + h ∈ Set.Icc (0 : ℝ) T → ∀ j ≤ 2, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (G (τ + h) y - G τ y) - G' τ y) x‖ ≤ ε)
    (X : EucConfig d N) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun τ => s53_Dk s ρ (G τ) X) (s53_Dk s ρ (G' τ) X) (Set.Icc 0 T) τ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set c : ℝ := (s + 1) * s53_cX s Mρ X + 1 with hc
  have hc0 : 0 < c := by
    have := s53_cX_nonneg (s := s) hM0 X
    have : 0 ≤ (s + 1) * s53_cX s Mρ X := by positivity
    linarith
  obtain ⟨δ, hδ, hD⟩ := hdiff τ hτ (ε / (2 * c)) (by positivity)
  refine ⟨δ, hδ, fun {y} hy hyd => ?_⟩
  obtain ⟨hyI, hyne⟩ := hy
  have hne : y - τ ≠ 0 := sub_ne_zero.2 hyne
  set h := y - τ with hh
  have hyτ : τ + h = y := by rw [hh]; ring
  have hhd : |h| < δ := by rwa [Real.dist_eq] at hyd
  have hq := hD h hne hhd (by rw [hyτ]; exact hyI)
  rw [hyτ] at hq
  set q : Euc d → ℝ := fun z => h⁻¹ * (G y z - G τ z) - G' τ z with hqdef
  have hGy := hG y hyI
  have hGτ := hG τ hτ
  have hG'τ := hG' τ hτ
  have hA : MemCb 2 (fun z => G y z - G τ z) := HRS.MS.Fcau.fcau_memCb_sub hGy hGτ
  have hB : MemCb 2 (fun z => h⁻¹ * (G y z - G τ z)) := s53_memCb_const_mul _ hA
  have hlin : s53_Dk s ρ q X = h⁻¹ * (s53_Dk s ρ (G y) X - s53_Dk s ρ (G τ) X) - s53_Dk s ρ (G' τ) X := by
    have e1 := s53_Dk_sub hs0 hM0 hρ hrow hB hG'τ X
    have e2 := s53_Dk_const_mul (s := s) (ρ := ρ) h⁻¹ (hA.1.of_le (by norm_num)) X
    have e3 := s53_Dk_sub hs0 hM0 hρ hrow hGy hGτ X
    rw [hqdef]
    rw [e1, e2, e3]
  have hbd := s53_Dk_bound hs0 hM0 hρ hrow hN (f := q) (by
    refine HRS.MS.Fcau.fcau_memCb_sub hB hG'τ) X
  have hsup : (⨆ x, ‖iteratedFDeriv ℝ 2 q x‖) ≤ ε / (2 * c) :=
    ciSup_le fun x => hq 2 le_rfl x
  have hcX := s53_cX_nonneg (s := s) hM0 X
  have h1 : |s53_Dk s ρ q X| ≤ ε / 2 := by
    refine hbd.trans ?_
    have hs1 : 0 ≤ s + 1 := by linarith
    calc (s + 1) * (⨆ x, ‖iteratedFDeriv ℝ 2 q x‖) * s53_cX s Mρ X
        ≤ (s + 1) * (ε / (2 * c)) * s53_cX s Mρ X := by gcongr
      _ = ε / 2 * (((s + 1) * s53_cX s Mρ X) / c) := by field_simp
      _ ≤ ε / 2 * 1 := by
          gcongr
          rw [div_le_one hc0]; linarith
      _ = ε / 2 := by ring
  rw [Real.dist_eq, slope_def_field]
  have : (s53_Dk s ρ (G y) X - s53_Dk s ρ (G τ) X) / (y - τ) - s53_Dk s ρ (G' τ) X =
      s53_Dk s ρ q X := by
    rw [hlin, ← hh]; field_simp
  rw [this]
  linarith

end Deriv

end HRS.MS.S53

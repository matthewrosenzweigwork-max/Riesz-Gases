import HRS.PDE.TorusFPSpec
import HRS.PDE.TorusCalculus
import HRS.PDE.Fourier

/-!
# D1 comparison, helper 1: the Gibbs weight is invariant for the generator

For `G = exp(-U/κ)` and smooth `φ`, `∫ (d1_gen κ (-∇U) φ) G dx = 0` on `𝕋^n`.
Proof by coordinatewise integration by parts (`PDE.integral_partialDeriv_mul`) using
`∂_j G = -κ⁻¹ ∂_j U · G`, and `Δφ = ∑_j ∂_j∂_j φ`, `⟨∇U, ∇φ⟩ = ∑_j ∂_j U ∂_j φ`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem d1c_isCk1_partialDeriv {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) (j : Fin n) :
    Torus.IsCk 1 (Torus.partialDeriv j φ) := by
  have hφ2 : ContDiff ℝ 2 (Torus.lift φ) := hφ
  have hφ1 : Torus.IsCk 1 φ := hφ2.of_le (by norm_num)
  have h1 : Torus.lift (Torus.partialDeriv j φ) =
      fun x => fderiv ℝ (Torus.lift φ) x (EuclideanSpace.single j 1) := by
    funext x
    exact PDE.partialDeriv_mk j φ hφ1 x
  unfold Torus.IsCk
  rw [h1]
  exact (hφ2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem d1c_gibbs_isCk1 {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsCk 1 U) :
    Torus.IsCk 1 (fun x => d1_gibbsWeight κ U x) := by
  have hU' : ContDiff ℝ 1 (Torus.lift U) := hU
  have h : Torus.lift (fun x => d1_gibbsWeight κ U x) =
      fun z => Real.exp (-(κ⁻¹ * Torus.lift U z)) := rfl
  unfold Torus.IsCk
  rw [h]
  exact Real.contDiff_exp.comp ((contDiff_const.mul hU').neg)

theorem d1c_partialDeriv_gibbs {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsCk 1 U) (j : Fin n)
    (x : Torus n) :
    Torus.partialDeriv j (fun y => d1_gibbsWeight κ U y) x =
      -(κ⁻¹ * Torus.partialDeriv j U x) * d1_gibbsWeight κ U x := by
  have hU' : ContDiff ℝ 1 (Torus.lift U) := hU
  have h1 : HasFDerivAt (Torus.lift U) (fderiv ℝ (Torus.lift U) (Torus.rep x)) (Torus.rep x) :=
    ((hU'.differentiable (by norm_num)) (Torus.rep x)).hasFDerivAt
  have hU0 : Torus.lift U (Torus.rep x) = U x := by simp [Torus.lift, Torus.mk_rep]
  have h2 : HasFDerivAt (fun z => Real.exp (-(κ⁻¹ * Torus.lift U z)))
      (Real.exp (-(κ⁻¹ * Torus.lift U (Torus.rep x))) •
        (-(κ⁻¹ • fderiv ℝ (Torus.lift U) (Torus.rep x)))) (Torus.rep x) :=
    (Real.hasDerivAt_exp _).comp_hasFDerivAt (Torus.rep x) ((h1.const_mul κ⁻¹).neg)
  show fderiv ℝ (fun z => Real.exp (-(κ⁻¹ * Torus.lift U z))) (Torus.rep x)
      (EuclideanSpace.single j 1) = _
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    smul_eq_mul, Torus.partialDeriv, hU0, d1_gibbsWeight]
  ring

theorem d1c_grad_component {φ : Torus n → ℝ} (x : Torus n) (j : Fin n) :
    (Torus.grad φ x).ofLp j = Torus.partialDeriv j φ x := by
  have key := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := fderiv ℝ (Torus.lift φ) (Torus.rep x))
  unfold Torus.grad gradient Torus.partialDeriv
  rw [← key, EuclideanSpace.inner_single_right]
  simp

theorem d1c_inner_grad {U φ : Torus n → ℝ} (x : Torus n) :
    inner ℝ (Torus.grad U x) (Torus.grad φ x) =
      ∑ j, Torus.partialDeriv j U x * Torus.partialDeriv j φ x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← d1c_grad_component x j, ← d1c_grad_component x j]
  simp [mul_comm]

theorem d1c_gen_gradDrift (κ : ℝ) (U : Torus n → ℝ) {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ)
    (x : Torus n) :
    d1_gen κ (d1_gradDrift U) φ x =
      κ * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x -
        ∑ j, Torus.partialDeriv j U x * Torus.partialDeriv j φ x := by
  simp only [d1_gen, d1_gradDrift, PDE.laplacian_eq_sum φ hφ x, inner_neg_left, d1c_inner_grad]
  ring

/-- **Invariance of the Gibbs weight (IBP).** For smooth `U`, `κ > 0` and `φ ∈ C²(𝕋^n)`:
`∫ (d1_gen κ (-∇U) φ) G dx = 0`, `G = exp(-U/κ)`. -/
theorem d1c_ibp {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) :
    ∫ x, d1_gen κ (d1_gradDrift U) φ x * d1_gibbsWeight κ U x = 0 := by
  have hU1 : Torus.IsCk 1 U := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift U) := hU
    exact h.of_le (by norm_num)
  have hφ1 : Torus.IsCk 1 φ := (show ContDiff ℝ 2 (Torus.lift φ) from hφ).of_le (by norm_num)
  have hG1 := d1c_gibbs_isCk1 (κ := κ) hU1
  have hGc : Continuous (fun x => d1_gibbsWeight κ U x) :=
    Torus.continuous_of_continuous_lift
      (show ContDiff ℝ 1 (Torus.lift (fun x => d1_gibbsWeight κ U x)) from hG1).continuous
  have hcont : ∀ j : Fin n, Continuous (Torus.partialDeriv j U) := fun j =>
    PDE.continuous_partialDeriv j U hU1
  have hcontφ : ∀ j : Fin n, Continuous (Torus.partialDeriv j φ) := fun j =>
    PDE.continuous_partialDeriv j φ hφ1
  have hcont2 : ∀ j : Fin n, Continuous (Torus.partialDeriv j (Torus.partialDeriv j φ)) :=
    fun j => PDE.continuous_partialDeriv j _ (d1c_isCk1_partialDeriv hφ j)
  have hint : ∀ g : Torus n → ℝ, Continuous g → Integrable g := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- per-coordinate identity: κ ∫ ∂_j∂_jφ G = ∫ ∂_jU ∂_jφ G
  have hj : ∀ j : Fin n, κ * (∫ x, Torus.partialDeriv j (Torus.partialDeriv j φ) x *
      d1_gibbsWeight κ U x) = ∫ x, Torus.partialDeriv j U x * Torus.partialDeriv j φ x *
      d1_gibbsWeight κ U x := by
    intro j
    have h := PDE.integral_partialDeriv_mul j (Torus.partialDeriv j φ)
      (fun y => d1_gibbsWeight κ U y) (d1c_isCk1_partialDeriv hφ j) hG1
    have hpt : ∀ x, Torus.partialDeriv j φ x * Torus.partialDeriv j
        (fun y => d1_gibbsWeight κ U y) x =
        -κ⁻¹ * (Torus.partialDeriv j U x * Torus.partialDeriv j φ x * d1_gibbsWeight κ U x) :=
      fun x => by rw [d1c_partialDeriv_gibbs hU1 j x]; ring
    have h3 : (∫ x, Torus.partialDeriv j φ x * Torus.partialDeriv j
        (fun y => d1_gibbsWeight κ U y) x) = -κ⁻¹ * (∫ x, Torus.partialDeriv j U x *
        Torus.partialDeriv j φ x * d1_gibbsWeight κ U x) := by
      simp_rw [hpt]
      rw [integral_const_mul]
    rw [h, h3]
    field_simp
  have hpt : ∀ x, d1_gen κ (d1_gradDrift U) φ x * d1_gibbsWeight κ U x =
      ∑ j, (κ * (Torus.partialDeriv j (Torus.partialDeriv j φ) x * d1_gibbsWeight κ U x) -
        Torus.partialDeriv j U x * Torus.partialDeriv j φ x * d1_gibbsWeight κ U x) := by
    intro x
    rw [d1c_gen_gradDrift κ U hφ x]
    simp only [sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, mul_assoc]
  have hsplit : (∫ x, d1_gen κ (d1_gradDrift U) φ x * d1_gibbsWeight κ U x) =
      ∑ j, (κ * (∫ x, Torus.partialDeriv j (Torus.partialDeriv j φ) x *
        d1_gibbsWeight κ U x) - ∫ x, Torus.partialDeriv j U x * Torus.partialDeriv j φ x *
        d1_gibbsWeight κ U x) := by
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_sub, integral_const_mul]
      · exact ((hint _ ((hcont2 j).mul hGc)).const_mul κ)
      · exact hint _ (((hcont j).mul (hcontφ j)).mul hGc)
    · intro j _
      exact ((hint _ ((hcont2 j).mul hGc)).const_mul κ).sub
        (hint _ (((hcont j).mul (hcontφ j)).mul hGc))
  rw [hsplit]
  exact Finset.sum_eq_zero fun j _ => by rw [hj j, sub_self]

end HRS

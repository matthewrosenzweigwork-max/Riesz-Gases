import HRS.MS.PoisKolmAux2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# S8.2 NormalForm, A02 stationarity lemma, part 1: cutoff integration by parts

For a density `ρ` with `ν ∇ρ = ρ b`, and `φ` of class `C²` off the point `y`, the cutoff identity
`∫ χ ρ (ν Δφ + b·∇φ) = -ν ∫ Σ_i ∂_i χ ρ ∂_i φ` for a `C¹` cutoff `χ` vanishing near `y`.
(Part 2, `CritForceNF3`: removal of the cutoff against the diagonal envelope.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MS.S82P

open HRS HRS.Whole

variable {d : ℕ}

/-- The coordinate derivative `∂_i φ`. -/
lemma s82p_u_contDiffAt {y : Euc d} {φ : Euc d → ℝ} (hφ : ContDiffOn ℝ 2 φ {x | x ≠ y})
    (v : Euc d) {x : Euc d} (hx : x ≠ y) :
    ContDiffAt ℝ 1 (fun z => fderiv ℝ φ z v) x := by
  have h1 : ContDiffAt ℝ 2 φ x := hφ.contDiffAt (isOpen_ne.mem_nhds hx)
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := h1.fderiv_right (by norm_num)
  exact h2.clm_apply contDiffAt_const

lemma s82p_laplacian_eq (φ : Euc d → ℝ) (x : Euc d) :
    Laplacian.laplacian φ x =
      ∑ i, fderiv ℝ (fderiv ℝ φ) x ((stdOrthonormalBasis ℝ (Euc d)) i)
        ((stdOrthonormalBasis ℝ (Euc d)) i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_two_apply]

/-- The cutoff identity. -/
theorem s82p_ibp_cut {ν : ℝ} (hν : 0 < ν) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ)
    {b : Euc d → Euc d} (hbρ : ∀ x, ν • gradient ρ x = ρ x • b x) (y : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiffOn ℝ 2 φ {x | x ≠ y}) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hχz : ∀ x, ‖x - y‖ < ε → χ x = 0) {Kχ : ℝ} (hKχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ Kχ)
    {Ψ : Euc d → ℝ} (hΨ : Integrable Ψ) (hΨ0 : ∀ x, 0 ≤ Ψ x)
    (hbd1 : ∀ x, x ≠ y → ρ x * ‖gradient φ x‖ ≤ Ψ x)
    (hbd2 : ∀ x, x ≠ y → ρ x * ‖b x‖ * ‖gradient φ x‖ ≤ Ψ x)
    (hbd3 : ∀ x, x ≠ y → ρ x * ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ Ψ x)
    (hρ0 : ∀ x, 0 ≤ ρ x) :
    Integrable (fun x => χ x * ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x))) ∧
    ∫ x, χ x * ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x)) =
      -ν * ∫ x, ∑ i, fderiv ℝ χ x ((stdOrthonormalBasis ℝ (Euc d)) i) *
        (ρ x * fderiv ℝ φ x ((stdOrthonormalBasis ℝ (Euc d)) i)) := by
  set bs := stdOrthonormalBasis ℝ (Euc d) with hbs
  have hKχ0 : 0 ≤ Kχ := (norm_nonneg _).trans (hKχ 0)
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  -- coordinate norms
  have hcoord : ∀ (f : Euc d → ℝ) (x : Euc d) (i : Fin (Module.finrank ℝ (Euc d))), |fderiv ℝ f x (bs i)| ≤ ‖gradient f x‖ := by
    intro f x i
    rw [← HRS.MS.PoisKolm.kl_inner_gradient]
    have := abs_real_inner_le_norm (bs i) (gradient f x)
    rwa [bs.norm_eq_one i, one_mul] at this
  have hcoordH : ∀ (x : Euc d) (i : Fin (Module.finrank ℝ (Euc d))),
      |fderiv ℝ (fderiv ℝ φ) x (bs i) (bs i)| ≤ ‖fderiv ℝ (fderiv ℝ φ) x‖ := by
    intro x i
    have h3 := (fderiv ℝ (fderiv ℝ φ) x).le_opNorm₂ (bs i) (bs i)
    rw [bs.norm_eq_one i, mul_one, mul_one] at h3
    rwa [← Real.norm_eq_abs]
  have hcoordχ : ∀ (x : Euc d) (i : Fin (Module.finrank ℝ (Euc d))), |fderiv ℝ χ x (bs i)| ≤ Kχ := by
    intro x i
    have h3 := (fderiv ℝ χ x).le_opNorm (bs i)
    rw [bs.norm_eq_one i, mul_one] at h3
    rw [← Real.norm_eq_abs]; exact h3.trans (hKχ x)
  have hcoordρ : ∀ (x : Euc d) (i : Fin (Module.finrank ℝ (Euc d))), |fderiv ℝ ρ x (bs i)| ≤ ‖gradient ρ x‖ :=
    fun x i => hcoord ρ x i
  -- the vector fields
  let F : Fin (Module.finrank ℝ (Euc d)) → Euc d → ℝ := fun i x => χ x * (ρ x * fderiv ℝ φ x (bs i))
  have hFz : ∀ i, ∀ x, ‖x - y‖ < ε → F i x = 0 := fun i x hx => by
    show χ x * _ = 0; rw [hχz x hx, zero_mul]
  have hFev : ∀ i, ∀ x, ‖x - y‖ < ε → F i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun i x hx => by
    have : {z : Euc d | ‖z - y‖ < ε} ∈ 𝓝 x :=
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds hx
    filter_upwards [this] with z hz using hFz i z hz
  have hFcd : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x - y‖ < ε
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hFev i x hx)
    · have hxy : x ≠ y := by
        intro h; apply hx; rw [h, sub_self, norm_zero]; exact hε
      exact hχ.contDiffAt.mul (hρ.contDiffAt.mul (s82p_u_contDiffAt hφ (bs i) hxy))
  -- derivative formula
  have hdF : ∀ i, ∀ x, fderiv ℝ (F i) x (bs i) =
      fderiv ℝ χ x (bs i) * (ρ x * fderiv ℝ φ x (bs i)) +
        χ x * (fderiv ℝ ρ x (bs i) * fderiv ℝ φ x (bs i) +
          ρ x * fderiv ℝ (fderiv ℝ φ) x (bs i) (bs i)) := by
    intro i x
    by_cases hx : ‖x - y‖ < ε
    · have h1 : fderiv ℝ (F i) x = 0 := by
        rw [(hFev i x hx).fderiv_eq]; simp
      have hev : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        have : {z : Euc d | ‖z - y‖ < ε} ∈ 𝓝 x :=
          (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
            continuous_const).mem_nhds hx
        filter_upwards [this] with z hz using hχz z hz
      have h2 : fderiv ℝ χ x = 0 := by rw [hev.fderiv_eq]; simp
      simp [h1, h2, hχz x hx]
    · have hxy : x ≠ y := by
        intro h; apply hx; rw [h, sub_self, norm_zero]; exact hε
      have hu := (s82p_u_contDiffAt hφ (bs i) hxy).differentiableAt (by norm_num)
      have hu2 : HasFDerivAt (fun z => fderiv ℝ φ z (bs i))
          ((fderiv ℝ (fderiv ℝ φ) x).flip (bs i)) x := by
        have h1 : ContDiffAt ℝ 2 φ x := hφ.contDiffAt (isOpen_ne.mem_nhds hxy)
        have h2 : DifferentiableAt ℝ (fderiv ℝ φ) x :=
          (h1.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
        have := h2.hasFDerivAt.clm_apply (hasFDerivAt_const (bs i) x)
        convert this using 1
        ext v; simp
      have hmul := (hχd x).hasFDerivAt.mul ((hρd x).hasFDerivAt.mul hu2)
      have hF : fderiv ℝ (F i) x = _ := hmul.fderiv
      rw [hF]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.flip_apply, Pi.mul_apply]
      ring
  -- bounds
  have hxy_of : ∀ x : Euc d, ¬ ‖x - y‖ < ε → x ≠ y := by
    intro x hx h; apply hx; rw [h, sub_self, norm_zero]; exact hε
  have hb1 : ∀ i, ∀ x, |F i x| ≤ Ψ x := by
    intro i x
    by_cases hx : ‖x - y‖ < ε
    · rw [hFz i x hx, abs_zero]; exact hΨ0 x
    · have hxy := hxy_of x hx
      show |χ x * (ρ x * fderiv ℝ φ x (bs i))| ≤ _
      rw [abs_mul, abs_mul, abs_of_nonneg (hχ0 x), abs_of_nonneg (hρ0 x)]
      calc χ x * (ρ x * |fderiv ℝ φ x (bs i)|) ≤ 1 * (ρ x * ‖gradient φ x‖) := by
            apply mul_le_mul (hχ1 x) _ (by have := hρ0 x; positivity) zero_le_one
            exact mul_le_mul_of_nonneg_left (hcoord φ x i) (hρ0 x)
        _ ≤ Ψ x := by rw [one_mul]; exact hbd1 x hxy
  have hgradρ : ∀ x, ‖gradient ρ x‖ = ρ x * ‖b x‖ / ν := by
    intro x
    have h := congrArg norm (hbρ x)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hν.le, Real.norm_of_nonneg (hρ0 x)] at h
    field_simp; linarith
  have hb2 : ∀ i, ∀ x, |fderiv ℝ (F i) x (bs i)| ≤ (Kχ + ν⁻¹ + 1) * Ψ x := by
    intro i x
    by_cases hx : ‖x - y‖ < ε
    · have h0 : fderiv ℝ (F i) x = 0 := by rw [(hFev i x hx).fderiv_eq]; simp
      rw [h0]; simp only [ContinuousLinearMap.zero_apply, abs_zero]
      exact mul_nonneg (by positivity) (hΨ0 x)
    · have hxy := hxy_of x hx
      rw [hdF]
      have e1 : |fderiv ℝ χ x (bs i) * (ρ x * fderiv ℝ φ x (bs i))| ≤ Kχ * Ψ x := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hρ0 x)]
        calc |fderiv ℝ χ x (bs i)| * (ρ x * |fderiv ℝ φ x (bs i)|) ≤ Kχ * (ρ x * ‖gradient φ x‖) := by
              apply mul_le_mul (hcoordχ x i) _ (by have := hρ0 x; positivity) hKχ0
              exact mul_le_mul_of_nonneg_left (hcoord φ x i) (hρ0 x)
          _ ≤ Kχ * Ψ x := mul_le_mul_of_nonneg_left (hbd1 x hxy) hKχ0
      have e2 : |χ x * (fderiv ℝ ρ x (bs i) * fderiv ℝ φ x (bs i))| ≤ ν⁻¹ * Ψ x := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hχ0 x)]
        calc χ x * (|fderiv ℝ ρ x (bs i)| * |fderiv ℝ φ x (bs i)|)
            ≤ 1 * (‖gradient ρ x‖ * ‖gradient φ x‖) := by
              apply mul_le_mul (hχ1 x) _ (by positivity) zero_le_one
              exact mul_le_mul (hcoordρ x i) (hcoord φ x i) (abs_nonneg _) (norm_nonneg _)
          _ = ν⁻¹ * (ρ x * ‖b x‖ * ‖gradient φ x‖) := by rw [one_mul, hgradρ]; field_simp
          _ ≤ ν⁻¹ * Ψ x := mul_le_mul_of_nonneg_left (hbd2 x hxy) (by positivity)
      have e3 : |χ x * (ρ x * fderiv ℝ (fderiv ℝ φ) x (bs i) (bs i))| ≤ Ψ x := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hχ0 x), abs_of_nonneg (hρ0 x)]
        calc χ x * (ρ x * |fderiv ℝ (fderiv ℝ φ) x (bs i) (bs i)|)
            ≤ 1 * (ρ x * ‖fderiv ℝ (fderiv ℝ φ) x‖) := by
              apply mul_le_mul (hχ1 x) _ (by have := hρ0 x; positivity) zero_le_one
              exact mul_le_mul_of_nonneg_left (hcoordH x i) (hρ0 x)
          _ ≤ Ψ x := by rw [one_mul]; exact hbd3 x hxy
      have : fderiv ℝ χ x (bs i) * (ρ x * fderiv ℝ φ x (bs i)) +
          χ x * (fderiv ℝ ρ x (bs i) * fderiv ℝ φ x (bs i) +
            ρ x * fderiv ℝ (fderiv ℝ φ) x (bs i) (bs i)) =
          fderiv ℝ χ x (bs i) * (ρ x * fderiv ℝ φ x (bs i)) +
            χ x * (fderiv ℝ ρ x (bs i) * fderiv ℝ φ x (bs i)) +
            χ x * (ρ x * fderiv ℝ (fderiv ℝ φ) x (bs i) (bs i)) := by ring
      rw [this]
      refine (abs_add_three _ _ _).trans ?_
      nlinarith [hΨ0 x]
  -- integrability and vanishing of the integral of each coordinate divergence
  have hum : ∀ i, Measurable (fun x => fderiv ℝ φ x (bs i)) := fun i =>
    (measurable_fderiv ℝ φ).apply_continuousLinearMap (bs i)
  have hFint : ∀ i, Integrable (F i) := fun i =>
    hΨ.mono' (hFcd i).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb1 i x)
  have hdFint : ∀ i, Integrable (fun x => fderiv ℝ (F i) x (bs i)) := fun i =>
    (hΨ.const_mul (Kχ + ν⁻¹ + 1)).mono'
      (((hFcd i).continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb2 i x)
  have hdFzero : ∀ i, ∫ x, fderiv ℝ (F i) x (bs i) = 0 := by
    intro i
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := F i) (g := fun _ => (1 : ℝ)) (v := bs i)
      (by simpa using hdFint i) (by simp) (by simpa using hFint i)
      (fun x _ => ((hFcd i).differentiable (by norm_num)) x) (fun x _ => differentiableAt_const _)
    simp at this
    linarith
  -- the pointwise identity
  let S1 : Euc d → ℝ := fun x => ∑ i, fderiv ℝ χ x (bs i) * (ρ x * fderiv ℝ φ x (bs i))
  have hsum_id : ∀ x, χ x * ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x)) =
      ν * ∑ i, fderiv ℝ (F i) x (bs i) - ν * S1 x := by
    intro x
    have hs2 : ∑ i, fderiv ℝ ρ x (bs i) * fderiv ℝ φ x (bs i) =
        inner ℝ (gradient ρ x) (gradient φ x) := by
      have e1 : ∀ i, fderiv ℝ φ x (bs i) = inner ℝ (bs i) (gradient φ x) := fun i => by
        rw [HRS.MS.PoisKolm.kl_inner_gradient]
      have e2 : ∀ i, fderiv ℝ ρ x (bs i) = inner ℝ (bs i) (gradient ρ x) := fun i => by
        rw [HRS.MS.PoisKolm.kl_inner_gradient]
      simp_rw [e1, e2]
      rw [← bs.sum_inner_mul_inner (gradient ρ x) (gradient φ x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (gradient ρ x) (bs i)]
    have hnu : ν * inner ℝ (gradient ρ x) (gradient φ x) = ρ x * inner ℝ (b x) (gradient φ x) := by
      have := congrArg (fun v => inner ℝ v (gradient φ x)) (hbρ x)
      simpa [inner_smul_left] using this
    have hL := s82p_laplacian_eq φ x
    have hsplit : ∑ i, fderiv ℝ (F i) x (bs i) = S1 x + χ x * (inner ℝ (gradient ρ x) (gradient φ x) +
        ρ x * Laplacian.laplacian φ x) := by
      simp_rw [hdF]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hs2, hL]
    rw [hsplit]
    linear_combination (-(χ x)) * hnu
  have hS1m : Measurable S1 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 : Measurable (fun x => fderiv ℝ χ x (bs i)) :=
      ((hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable
    exact h1.mul (hρ.continuous.measurable.mul (hum i))
  have hdχz : ∀ x, ‖x - y‖ < ε → fderiv ℝ χ x = 0 := by
    intro x hx
    have hev : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have : {z : Euc d | ‖z - y‖ < ε} ∈ 𝓝 x :=
        (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
          continuous_const).mem_nhds hx
      filter_upwards [this] with z hz using hχz z hz
    rw [hev.fderiv_eq]; simp
  have hS1b : ∀ x, |S1 x| ≤ ((d : ℝ) * Kχ) * Ψ x := by
    intro x
    by_cases hx : ‖x - y‖ < ε
    · have : S1 x = 0 := by simp [S1, hdχz x hx]
      rw [this, abs_zero]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKχ0) (hΨ0 x)
    · have hxy := hxy_of x hx
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (Kχ * Ψ x) fun i _ => ?_).trans ?_
      · rw [abs_mul, abs_mul, abs_of_nonneg (hρ0 x)]
        calc |fderiv ℝ χ x (bs i)| * (ρ x * |fderiv ℝ φ x (bs i)|) ≤ Kχ * (ρ x * ‖gradient φ x‖) := by
              apply mul_le_mul (hcoordχ x i) _ (by have := hρ0 x; positivity) hKχ0
              exact mul_le_mul_of_nonneg_left (hcoord φ x i) (hρ0 x)
          _ ≤ Kχ * Ψ x := mul_le_mul_of_nonneg_left (hbd1 x hxy) hKχ0
      · simp [nsmul_eq_mul]; ring_nf; exact le_refl _
  have hS1int : Integrable S1 :=
    (hΨ.const_mul ((d : ℝ) * Kχ)).mono' hS1m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hS1b x)
  have hmain : (fun x => χ x * ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x))) =
      fun x => ν * ∑ i, fderiv ℝ (F i) x (bs i) - ν * S1 x := funext hsum_id
  have hI : Integrable (fun x => ν * ∑ i, fderiv ℝ (F i) x (bs i) - ν * S1 x) :=
    ((integrable_finsetSum _ fun i _ => hdFint i).const_mul ν).sub (hS1int.const_mul ν)
  refine ⟨by rw [hmain]; exact hI, ?_⟩
  rw [hmain, integral_sub ((integrable_finsetSum _ fun i _ => hdFint i).const_mul ν)
    (hS1int.const_mul ν), integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun i _ => hdFint i]
  rw [Finset.sum_eq_zero fun i _ => hdFzero i]
  show ν * 0 - ν * ∫ x, S1 x = -ν * ∫ x, S1 x
  ring

end HRS.MS.S82P

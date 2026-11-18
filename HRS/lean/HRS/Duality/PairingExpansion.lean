import HRS.Dynamics.Setup
import HRS.Kernel.GradD1
import HRS.PDE.EnergyR2Fn

/-!
# HRS.Duality.PairingExpansion — package DUAL-01: Lemma 3.1 (torus case)

Lemma 3.1 `B:lem:pairing-expansion` (main paper, source lines 1518-1524), with the bilinear
form `B_f` of `B:eq:B-def` / `B:eq:B-symmetrized` (lines 1488-1501) and the cancellation
convention `B:eq:nabla-g-convolution` (lines 10091-10101; `HRS.convGradConv`).

Representation decisions (recorded in `docs/ISSUES.md` §H):
* Domain: the torus `𝕋^d` (the source's `𝔻 ∈ {𝕋^d, ℝ^d}`); the `ℝ^d` case is a separate statement
  of the whole-space package.
* `B_f(α, λ)` is taken in the symmetrized form with the diagonal removed,
  `pairB f M s α λ = ∬_{x ≠ y} ½ (∇f(x) - ∇f(y)) · M ∇g(x - y) dα(x) dλ(y)`;
  for equal arguments this is the source's definition `B:eq:B-symmetrized`, and for a
  pairwise-distinct empirical measure it is the label sum over `i ≠ j` (line 1501).
* `B_f(ρ_N, ρ_N)` for the signed measure `ρ_N = μ_N - μ` is expanded bilinearly into four
  absolutely convergent pieces (`pairBSigned`); their absolute convergence is part of the
  conclusion ("all four quantities below are finite").
* `μ = ρ dx` with `ρ` a probability density that is `α`-Hölder, `α > max(0, s + 1 - d)`.
* `Div g * (μ M^* ∇f) := (∇g) * (μ M^* ∇f)` contracted: the sum over coordinates `a` of the
  `a`-th component of the convention convolution of the scalar function `ρ (M^* ∇f)_a`.
-/

open MeasureTheory

noncomputable section

namespace HRS

namespace Duality

variable {d N : ℕ}

/-- The symmetrized kernel `½ (∇f(x) - ∇f(y)) · M ∇g(x - y)` of `B:eq:B-symmetrized`, set to `0`
on the diagonal. -/
def pairKernelB (f : Torus d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (x y : Torus d) : ℝ :=
  if x = y then 0 else
    (1 / 2 : ℝ) * inner ℝ (Torus.grad f x - Torus.grad f y)
      (Torus.matVec M (periodicRieszGrad d s (x - y)))

/-- `B_f(α, λ)` in symmetrized, off-diagonal form. -/
def pairB (f : Torus d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (α ν : Measure (Torus d)) : ℝ :=
  ∫ p, pairKernelB f M s p.1 p.2 ∂(α.prod ν)

/-- `B_f(μ_N - μ, μ_N - μ)`, expanded bilinearly. -/
def pairBSigned (f : Torus d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (ν μ : Measure (Torus d)) : ℝ :=
  pairB f M s ν ν - pairB f M s ν μ - pairB f M s μ ν + pairB f M s μ μ

/-- The pairing `⟨φ, μ_N - μ⟩ = N⁻¹ ∑ φ(x_i) - ∫ φ dμ`. -/
def pairEmp (φ : Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, φ (X i) - ∫ x, φ x ∂μ

/-- The contracted convolution `(∇g) * (ρ M^* ∇f)` with the cancellation convention. -/
def divConvB (f : Torus d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (ρ : Torus d → ℝ)
    (x : Torus d) : ℝ :=
  ∑ a : Fin d, convGradConv (periodicRieszGrad d s)
    (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x a

section Helpers

/-- Coordinates of the matrix action. -/
theorem matVec_apply (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) (j : Fin d) :
    Torus.matVec M v j = ∑ i, M j i * v i := by
  unfold Torus.matVec
  show (WithLp.toLp 2 (M.mulVec v.ofLp) : Euc d) j = _
  simp [Matrix.mulVec, dotProduct]

/-- Adjoint identity for the matrix action: `⟪u, M v⟫ = ⟪Mᵀ u, v⟫`. -/
theorem inner_matVec_transpose (M : Matrix (Fin d) (Fin d) ℝ) (u v : Euc d) :
    inner ℝ u (Torus.matVec M v) = inner ℝ (Torus.matVec M.transpose u) v := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matVec_apply,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Components of the torus gradient are partial derivatives. -/
theorem grad_apply_eq_partialDeriv (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad f x j = Torus.partialDeriv j f x := by
  unfold Torus.grad Torus.partialDeriv
  have h1 := EuclideanSpace.inner_single_right j (1 : ℝ) (gradient (Torus.lift f) (Torus.rep x))
  have h2 := InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift f) (Torus.rep x))
  simp only [one_mul, RCLike.conj_to_real] at h1
  rw [← h1]
  exact h2

/-- The `ℓ¹`-to-Euclidean norm comparison used for vectors in `ℝ^d`. -/
theorem norm_euc_le_sum (v : Euc d) : ‖v‖ ≤ ∑ j, |v j| := by
  have := HRS.KernelAux.norm_toLp_le_sum (d := d) (fun j => v j)
  simpa using this

theorem tdist_le_norm_mul (x y : Torus d) : KernelGrad.tdist x y ≤ d * ‖x - y‖ := by
  rw [KernelGrad.tdist_eq_sub_zero]; exact KernelGrad.tdist_le_mul_norm (x - y)

/-- The gradient of a `C²` function on the torus is Lipschitz for the torus distance. -/
theorem grad_lipschitz {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖Torus.grad f x - Torus.grad f y‖ ≤ L * KernelGrad.tdist x y := by
  refine ⟨|Torus.cbNorm 2 f| * d, by positivity, fun x y => ?_⟩
  have hc : ∀ j, |Torus.partialDeriv j f x - Torus.partialDeriv j f y|
      ≤ |Torus.cbNorm 2 f| * KernelGrad.tdist x y := fun j => by
    have h := PDE.R2Aux.isLipschitz_partialDeriv hf j x y
    have h0 : Torus.cbNorm 2 f ≤ |Torus.cbNorm 2 f| := le_abs_self _
    have ht : 0 ≤ KernelGrad.tdist x y := norm_nonneg _
    calc _ ≤ Torus.cbNorm 2 f * Torus.tdist x y := h
      _ ≤ |Torus.cbNorm 2 f| * KernelGrad.tdist x y := mul_le_mul h0 le_rfl ht (abs_nonneg _)
  have hv := norm_euc_le_sum (Torus.grad f x - Torus.grad f y)
  calc ‖Torus.grad f x - Torus.grad f y‖ ≤ ∑ j, |(Torus.grad f x - Torus.grad f y) j| := hv
    _ ≤ ∑ _j : Fin d, |Torus.cbNorm 2 f| * KernelGrad.tdist x y := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [PiLp.sub_apply, grad_apply_eq_partialDeriv, grad_apply_eq_partialDeriv]
        exact hc j
    _ = |Torus.cbNorm 2 f| * d * KernelGrad.tdist x y := by simp; ring

end Helpers

/-- Real form of the Hölder condition. -/
theorem holder_abs_le {ρ : Torus d → ℝ} {C α : NNReal} (hH : HolderWith C α ρ) (x y : Torus d) :
    |ρ x - ρ y| ≤ (C : ℝ) * ‖x - y‖ ^ (α : ℝ) := by
  have h := hH x y
  rw [edist_dist, edist_dist, Real.dist_eq, dist_eq_norm x y] at h
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) (NNReal.coe_nonneg α),
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  exact h2

/-- A Lipschitz map into a normed space is continuous. -/
theorem continuous_of_lip {E : Type*} [NormedAddCommGroup E] (g : Torus d → E) {L : ℝ}
    (hL0 : 0 ≤ L) (h : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) : Continuous g := by
  have : LipschitzWith (Real.toNNReal L) g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
    exact h x y
  exact this.continuous

theorem matVec_sub (M : Matrix (Fin d) (Fin d) ℝ) (v w : Euc d) :
    Torus.matVec M (v - w) = Torus.matVec M v - Torus.matVec M w := by
  unfold Torus.matVec
  exact map_sub _ _ _

/-- The linear map `v ↦ M v` is bounded on `ℝ^d`. -/
theorem exists_matVec_bound (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ v : Euc d, ‖Torus.matVec M v‖ ≤ CM * ‖v‖ := by
  let T : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
  refine ⟨‖T‖, norm_nonneg _, fun v => ?_⟩
  exact T.le_opNorm v

/-- The gradient of a `C²` function is Lipschitz for the Euclidean norm of `ℝ^d`. -/
theorem grad_lip_norm {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖Torus.grad f x - Torus.grad f y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL0, hL⟩ := grad_lipschitz hf
  refine ⟨L * d, by positivity, fun x y => ?_⟩
  refine (hL x y).trans ?_
  have := tdist_le_norm_mul x y
  calc L * KernelGrad.tdist x y ≤ L * (d * ‖x - y‖) := by gcongr
    _ = L * d * ‖x - y‖ := by ring

theorem grad_continuous {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    Continuous (Torus.grad f) := by
  obtain ⟨L, hL0, hL⟩ := grad_lip_norm hf
  exact continuous_of_lip _ hL0 hL

/-- The `a`-th component of `Mᵀ ∇f` is Lipschitz. -/
theorem vcomp_lip (M : Matrix (Fin d) (Fin d) ℝ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f)
    (a : Fin d) : ∃ Lv : ℝ, 0 ≤ Lv ∧ ∀ x y,
      |Torus.matVec M.transpose (Torus.grad f x) a - Torus.matVec M.transpose (Torus.grad f y) a|
        ≤ Lv * ‖x - y‖ := by
  obtain ⟨CM, hCM0, hCM⟩ := exists_matVec_bound M.transpose
  obtain ⟨L, hL0, hL⟩ := grad_lip_norm hf
  refine ⟨CM * L, by positivity, fun x y => ?_⟩
  have h1 : Torus.matVec M.transpose (Torus.grad f x) a - Torus.matVec M.transpose (Torus.grad f y) a
      = (Torus.matVec M.transpose (Torus.grad f x - Torus.grad f y)) a := by
    rw [matVec_sub]; rfl
  rw [h1]
  calc |(Torus.matVec M.transpose (Torus.grad f x - Torus.grad f y)) a|
      = ‖(Torus.matVec M.transpose (Torus.grad f x - Torus.grad f y)) a‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖Torus.matVec M.transpose (Torus.grad f x - Torus.grad f y)‖ :=
        PiLp.norm_apply_le _ a
    _ ≤ CM * ‖Torus.grad f x - Torus.grad f y‖ := hCM _
    _ ≤ CM * (L * ‖x - y‖) := by gcongr; exact hL x y
    _ = CM * L * ‖x - y‖ := by ring

/-- Bounded continuous functions on the torus. -/
theorem bounded_of_continuous {g : Torus d → ℝ} (hg : Continuous g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun x => by
    have := hB x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

variable {s : ℝ}

/-- The symmetrized kernel is dominated by `|x - y|^{-s}`. -/
theorem pairKernelB_bound {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (M : Matrix (Fin d) (Fin d) ℝ)
    {C : ℝ} (hG : KernelGrad.GoodKernel d s C (periodicRieszGrad d s)) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ x y, |pairKernelB f M s x y| ≤ KM * (‖x - y‖ ^ (-s) + d) := by
  obtain ⟨L, hL0, hL⟩ := grad_lipschitz hf
  obtain ⟨CM, hCM0, hCM⟩ := exists_matVec_bound M
  have hC0 := hG.hC0
  have hKM0 : 0 ≤ (1 / 2 : ℝ) * CM * L * C :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCM0) hL0) hC0
  refine ⟨(1 / 2 : ℝ) * CM * L * C, hKM0, fun x y => ?_⟩
  unfold pairKernelB
  split_ifs with hxy
  · rw [abs_zero]
    exact mul_nonneg hKM0 (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hG' := hG.norm_mul_tdist_le (x - y) hz
    rw [← KernelGrad.tdist_eq_sub_zero] at hG'
    have e1 : ‖Torus.grad f x - Torus.grad f y‖ * ‖Torus.matVec M (periodicRieszGrad d s (x - y))‖
        ≤ (L * KernelGrad.tdist x y) * (CM * ‖periodicRieszGrad d s (x - y)‖) :=
      mul_le_mul (hL x y) (hCM _) (norm_nonneg _)
        (mul_nonneg hL0 (KernelGrad.tdist_nonneg x y))
    calc |(1 / 2 : ℝ) * inner ℝ (Torus.grad f x - Torus.grad f y)
          (Torus.matVec M (periodicRieszGrad d s (x - y)))|
        = (1 / 2 : ℝ) * |inner ℝ (Torus.grad f x - Torus.grad f y)
          (Torus.matVec M (periodicRieszGrad d s (x - y)))| := by
          rw [abs_mul]; norm_num
      _ ≤ (1 / 2 : ℝ) * (‖Torus.grad f x - Torus.grad f y‖ *
          ‖Torus.matVec M (periodicRieszGrad d s (x - y))‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * ((L * KernelGrad.tdist x y) * (CM * ‖periodicRieszGrad d s (x - y)‖)) :=
          mul_le_mul_of_nonneg_left e1 (by norm_num)
      _ = (1 / 2 : ℝ) * CM * L * (KernelGrad.tdist x y * ‖periodicRieszGrad d s (x - y)‖) := by ring
      _ ≤ (1 / 2 : ℝ) * CM * L * (C * (‖x - y‖ ^ (-s) + d)) :=
          mul_le_mul_of_nonneg_left hG' (mul_nonneg (mul_nonneg (by norm_num) hCM0) hL0)
      _ = _ := by ring

/-- Pointwise bound for the cancellation integrand with a Hölder integrand. -/
theorem kern_norm_holder {C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {h : Torus d → ℝ} {B Λ β : ℝ} (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d)
    {z : Torus d} (hz : z ≠ 0) :
    ‖KernelGrad.kern G h x z‖ ≤
      Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β) + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hC0 := hG.hC0
  have hGb := hG.bound_norm z hz
  have hs0 := hG.hs0
  have hpow : ‖z‖ ^ (β - s - 1) = ‖z‖ ^ β * ‖z‖ ^ (-s - 1) := by
    rw [← Real.rpow_add hz0]; congr 1; ring
  have hR1 : 0 ≤ Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β) := by
    have := Real.rpow_nonneg (norm_nonneg z) (β - s - 1)
    have := Real.rpow_nonneg (norm_nonneg z) β
    positivity
  have hR2 : 0 ≤ B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (-s - 1)
    positivity
  unfold KernelGrad.kern
  split_ifs with hc
  · rw [norm_smul, Real.norm_eq_abs]
    have hβ := Real.rpow_nonneg (norm_nonneg z) β
    calc |h (x - z) - h x| * ‖G z‖ ≤ (Λ * ‖z‖ ^ β) * (C * (‖z‖ ^ (-s - 1) + 1)) :=
          mul_le_mul (hH x z hc) hGb (norm_nonneg _) (mul_nonneg hΛ hβ)
      _ = Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β) := by rw [hpow]; ring
      _ ≤ _ := by linarith
  · push_neg at hc
    rw [norm_smul, Real.norm_eq_abs]
    have hle : ‖z‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hc.le (by linarith)
    calc |h (x - z)| * ‖G z‖ ≤ B * (C * (‖z‖ ^ (-s - 1) + 1)) :=
          mul_le_mul (hB _) hGb (norm_nonneg _) hB0
      _ ≤ B * (C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) := by
          gcongr
      _ = B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by ring
      _ ≤ _ := by linarith

/-- Integrability of the dominating function of `kern_norm_holder`. -/
theorem integrable_dom_holder {C : ℝ} {G : Torus d → Euc d}
    (hG : KernelGrad.GoodKernel d s C G) {Λ B β : ℝ} (hβ0 : 0 < β) (hβ : s + 1 - d < β) :
    Integrable (fun z : Torus d => Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β)
      + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) := by
  have h1 : Integrable (fun z : Torus d => ‖z‖ ^ (β - s - 1)) := by
    have e : (fun z : Torus d => ‖z‖ ^ (β - s - 1)) = fun z => ‖z‖ ^ (-(s + 1 - β)) := by
      funext z; congr 1; ring
    rw [e]
    exact KernelGrad.integrable_norm_rpow_neg hG.pos (by linarith)
  have h2 : Integrable (fun z : Torus d => ‖z‖ ^ β) := by
    have e : (fun z : Torus d => ‖z‖ ^ β) = fun z => ‖z‖ ^ (-(-β)) := by
      funext z; rw [neg_neg]
    rw [e]
    exact KernelGrad.integrable_norm_rpow_neg hG.pos (by linarith)
  exact ((h1.add h2).const_mul (Λ * C)).add (integrable_const _)

/-- The cancellation integrand with a Hölder integrand is integrable. -/
theorem integrable_kern_holder {C : ℝ} {G : Torus d → Euc d}
    (hG : KernelGrad.GoodKernel d s C G) {h : Torus d → ℝ} {B Λ β : ℝ}
    (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d) :
    Integrable (KernelGrad.kern G h x) :=
  (integrable_dom_holder hG (Λ := Λ) (B := B) hβ0 hβ).mono'
    (KernelGrad.measurable_kern hG hh x).aestronglyMeasurable
    (by
      filter_upwards [KernelGrad.torus_ae_ne' hG.pos] with z hz
      exact kern_norm_holder hG hB hB0 hΛ hH x hz)

/-- The convention integrand of `B:eq:nabla-g-convolution` in the form used by the statement. -/
theorem integrable_conv_form {C : ℝ} {G : Torus d → Euc d}
    (hG : KernelGrad.GoodKernel d s C G) {h : Torus d → ℝ} {B Λ β : ℝ}
    (hh : Measurable h) (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d) :
    Integrable (fun y : Torus d => if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • G (x - y)
      else h y • G (x - y)) := by
  refine ((integrable_kern_holder hG hh hB hB0 hΛ hβ0 hβ hH x).comp_sub_left x).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [KernelGrad.kern, sub_sub_cancel]

/-- The Hölder bound of a product `ρ · v` with `v` bounded Lipschitz. -/
theorem holder_mul_kern {ρ v : Torus d → ℝ} {Cρ β Lv Bρ Bv : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hCρ : 0 ≤ Cρ) (hLv : 0 ≤ Lv)
    (hBρ : ∀ x, |ρ x| ≤ Bρ) (hBv : ∀ x, |v x| ≤ Bv)
    (hρH : ∀ x z, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ Cρ * ‖z‖ ^ β)
    (hvL : ∀ x y, |v x - v y| ≤ Lv * ‖x - y‖) (x : Torus d) {z : Torus d} (hz : ‖z‖ ≤ 1 / 4) :
    |ρ (x - z) * v (x - z) - ρ x * v x| ≤ (Cρ * Bv + Bρ * Lv) * ‖z‖ ^ β := by
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hz1 : ‖z‖ ≤ ‖z‖ ^ β := by
    have h1 : ‖z‖ ≤ 1 := by linarith
    calc ‖z‖ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ‖z‖ ^ β := Real.rpow_le_rpow_of_exponent_ge' h0 h1 hβ0 hβ1
  have hv' : |v (x - z) - v x| ≤ Lv * ‖z‖ := by
    have := hvL (x - z) x
    rwa [sub_sub_cancel_left, norm_neg] at this
  have hβn : 0 ≤ ‖z‖ ^ β := Real.rpow_nonneg h0 _
  have e : ρ (x - z) * v (x - z) - ρ x * v x
      = (ρ (x - z) - ρ x) * v (x - z) + ρ x * (v (x - z) - v x) := by ring
  rw [e]
  calc |(ρ (x - z) - ρ x) * v (x - z) + ρ x * (v (x - z) - v x)|
      ≤ |(ρ (x - z) - ρ x) * v (x - z)| + |ρ x * (v (x - z) - v x)| := abs_add_le _ _
    _ = |ρ (x - z) - ρ x| * |v (x - z)| + |ρ x| * |v (x - z) - v x| := by
        rw [abs_mul, abs_mul]
    _ ≤ (Cρ * ‖z‖ ^ β) * Bv + Bρ * (Lv * ‖z‖ ^ β) := by
        refine add_le_add (mul_le_mul (hρH x z hz) (hBv _) (abs_nonneg _)
          (mul_nonneg hCρ hβn)) (mul_le_mul (hBρ x) ?_ (abs_nonneg _)
          ((abs_nonneg _).trans (hBρ x)))
        exact hv'.trans (mul_le_mul_of_nonneg_left hz1 hLv)
    _ = (Cρ * Bv + Bρ * Lv) * ‖z‖ ^ β := by ring


/-- A bounded density is dominated by a multiple of the Haar measure. -/
theorem withDensityReal_le_smul {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) :
    withDensityReal ρ ≤ ENNReal.ofReal B • (volume : Measure (Torus d)) := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold withDensityReal
  rw [withDensity_apply' , Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ a in A, ENNReal.ofReal (ρ a) ≤ ∫⁻ _ in A, ENNReal.ofReal B :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hB a)
    _ = ENNReal.ofReal B * volume A := setLIntegral_const _ _ 

/-- A probability density gives a finite measure. -/
theorem isFiniteMeasure_withDensityReal {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) :
    IsFiniteMeasure (withDensityReal ρ) := by
  refine ⟨?_⟩
  have h := Measure.le_iff'.1 (withDensityReal_le_smul hB) Set.univ
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))

/-- Integrability with respect to the density measure from integrability with respect to Haar. -/
theorem integrable_withDensityReal_of {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B)
    {g : Torus d → ℝ} (hg : Integrable g volume) :
    Integrable g (withDensityReal ρ) :=
  (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure (withDensityReal_le_smul hB)

/-- The integral against the density measure is controlled by the Haar integral. -/
theorem integral_withDensityReal_le {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B)
    {g : Torus d → ℝ} (hg0 : ∀ y, 0 ≤ g y) (hg : Integrable g volume) :
    ∫ y, g y ∂(withDensityReal ρ) ≤ B * ∫ y, g y := by
  have h1 := integral_mono_measure (withDensityReal_le_smul hB) (Filter.Eventually.of_forall hg0)
    (hg.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hB0, smul_eq_mul] at h1
  exact h1

/-- Measurability of the symmetrized kernel. -/
theorem measurable_pairKernelB {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (M : Matrix (Fin d) (Fin d) ℝ)
    (hsd : s < d) :
    Measurable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) := by
  have hgrad : Continuous (Torus.grad f) := grad_continuous hf
  have hmat : Continuous (fun v : Euc d => Torus.matVec M v) := by
    have e : (fun v : Euc d => Torus.matVec M v)
        = ⇑(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) := rfl
    rw [e]
    exact ContinuousLinearMap.continuous _
  have hG : Measurable (periodicRieszGrad d s) := KernelGrad.measurable_periodicRieszGrad hsd
  unfold pairKernelB
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.const_mul ?_ _
  refine Measurable.inner ?_ ?_
  · exact ((hgrad.measurable.comp measurable_fst).sub (hgrad.measurable.comp measurable_snd))
  · exact hmat.measurable.comp (hG.comp (measurable_fst.sub measurable_snd))


/-- Integrability on `ν ⊗ μ` from a fibrewise integrability and a uniform fibrewise bound. -/
theorem integrable_prod_of_bound {ν μ : Measure (Torus d)} [IsFiniteMeasure ν] [SFinite μ]
    {F : Torus d × Torus d → ℝ} (hF : Measurable F)
    (hx : ∀ x, Integrable (fun y => F (x, y)) μ) {M : ℝ}
    (hM : ∀ x, ∫ y, ‖F (x, y)‖ ∂μ ≤ M) : Integrable F (ν.prod μ) := by
  rw [integrable_prod_iff hF.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => hx x, ?_⟩
  refine Integrable.of_bound ?_ M (Filter.Eventually.of_forall fun x => ?_)
  · exact (hF.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hM x

/-- The symmetrized kernel is symmetric. -/
theorem pairKernelB_symm {f : Torus d → ℝ} (M : Matrix (Fin d) (Fin d) ℝ) (hsd : s < d) (x y : Torus d) :
    pairKernelB f M s y x = pairKernelB f M s x y := by
  by_cases hxy : x = y
  · subst hxy; rfl
  · have hyx : y ≠ x := fun h => hxy h.symm
    unfold pairKernelB
    rw [if_neg hxy, if_neg hyx]
    have e1 : y - x = -(x - y) := (neg_sub x y).symm
    have e2 : Torus.grad f y - Torus.grad f x = -(Torus.grad f x - Torus.grad f y) :=
      (neg_sub _ _).symm
    have hneg : ∀ v : Euc d, Torus.matVec M (-v) = -Torus.matVec M v := fun v => by
      unfold Torus.matVec; exact map_neg _ _
    rw [e1, e2, KernelGrad.periodicRieszGrad_neg_of_lt hsd, hneg, inner_neg_left, inner_neg_right,
      neg_neg]

/-- Integrability of the symmetrized kernel on `ν' ⊗ μ` for a finite `ν'` and the density
measure `μ = ρ dx` with `ρ ≤ B`. -/
theorem pairKernelB_integrable_prod {f : Torus d → ℝ} (hf : Torus.IsCk 2 f)
    (M : Matrix (Fin d) (Fin d) ℝ) {C : ℝ}
    (hG : KernelGrad.GoodKernel d s C (periodicRieszGrad d s))
    {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B)
    {ν' : Measure (Torus d)} [IsFiniteMeasure ν'] :
    Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2)
      (ν'.prod (withDensityReal ρ)) := by
  haveI := isFiniteMeasure_withDensityReal hB
  obtain ⟨KM, hKM0, hKM⟩ := pairKernelB_bound hf M hG
  have hmeas := measurable_pairKernelB (s := s) hf M hG.hsd
  have hgi : Integrable (fun z : Torus d => KM * (‖z‖ ^ (-s) + d)) volume :=
    ((KernelGrad.integrable_norm_rpow_neg hG.pos hG.hsd).add (integrable_const _)).const_mul KM
  have hg0 : ∀ z : Torus d, 0 ≤ KM * (‖z‖ ^ (-s) + d) := fun z =>
    mul_nonneg hKM0 (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))
  have hx : ∀ x, Integrable (fun y => pairKernelB f M s x y) (withDensityReal ρ) := by
    intro x
    have hgx : Integrable (fun y : Torus d => KM * (‖x - y‖ ^ (-s) + d)) volume :=
      hgi.comp_sub_left x
    refine Integrable.mono' (integrable_withDensityReal_of hB hgx)
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    show ‖pairKernelB f M s x y‖ ≤ KM * (‖x - y‖ ^ (-s) + d)
    rw [Real.norm_eq_abs]
    exact hKM x y
  have hM : ∀ x, ∫ y, ‖pairKernelB f M s x y‖ ∂(withDensityReal ρ)
      ≤ B * ∫ z : Torus d, KM * (‖z‖ ^ (-s) + d) := by
    intro x
    have hgx : Integrable (fun y : Torus d => KM * (‖x - y‖ ^ (-s) + d)) volume :=
      hgi.comp_sub_left x
    have h1 : ∫ y, ‖pairKernelB f M s x y‖ ∂(withDensityReal ρ)
        ≤ ∫ y, KM * (‖x - y‖ ^ (-s) + d) ∂(withDensityReal ρ) := by
      refine integral_mono (hx x).norm (integrable_withDensityReal_of hB hgx) fun y => ?_
      show ‖pairKernelB f M s x y‖ ≤ KM * (‖x - y‖ ^ (-s) + d)
      rw [Real.norm_eq_abs]
      exact hKM x y
    refine h1.trans ?_
    refine (integral_withDensityReal_le hB hB0 (fun y => hg0 (x - y)) hgx).trans ?_
    rw [integral_sub_left_eq_self (fun z : Torus d => KM * (‖z‖ ^ (-s) + d)) volume x]
  exact integrable_prod_of_bound hmeas hx hM

/-- Joint measurability of the cancellation integrand. -/
theorem measurable_kern_joint {C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {h : Torus d → ℝ} (hh : Measurable h) :
    Measurable (fun p : Torus d × Torus d => KernelGrad.kern G h p.1 p.2) := by
  unfold KernelGrad.kern
  refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const) ?_ ?_
  · exact (((hh.comp (measurable_fst.sub measurable_snd)).sub (hh.comp measurable_fst)).smul
      (hG.meas.comp measurable_snd))
  · exact (hh.comp (measurable_fst.sub measurable_snd)).smul (hG.meas.comp measurable_snd)

/-- The cancellation convolution of a measurable function is measurable. -/
theorem measurable_conv {C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {h : Torus d → ℝ} (hh : Measurable h) : Measurable (fun x => convGradConv G h x) := by
  have e : (fun x => convGradConv G h x) = fun x => ∫ z, KernelGrad.kern G h x z :=
    funext fun x => KernelGrad.convGradConv_eq_integral_kern G h x
  rw [e]
  exact (measurable_kern_joint hG hh).stronglyMeasurable.integral_prod_right'.measurable

/-- A uniform bound for the cancellation convolution of a Hölder function. -/
theorem conv_norm_le {C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {h : Torus d → ℝ} {B Λ β : ℝ} (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d) :
    ‖convGradConv G h x‖ ≤ ∫ z : Torus d, (Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β)
      + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) := by
  rw [KernelGrad.convGradConv_eq_integral_kern]
  exact norm_integral_le_of_norm_le (integrable_dom_holder hG hβ0 hβ)
    (by
      filter_upwards [KernelGrad.torus_ae_ne' hG.pos] with z hz
      exact kern_norm_holder hG hB hB0 hΛ hH x hz)

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_bdd_meas {μ : Measure (Torus d)} [IsFiniteMeasure μ] {φ : Torus d → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : ∀ x, |φ x| ≤ K) : Integrable φ μ :=
  Integrable.of_bound hm.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x)

/-- Coordinates of a Euclidean vector: the inner product with `v` is the coordinate sum. -/
theorem inner_euc_eq (u v : Euc d) : inner ℝ u v = ∑ a, u a * v a := by
  simp [PiLp.inner_apply, mul_comm]


theorem sum_split {n : ℕ} (c₁ c₂ : ℝ) (v w G : Fin n → ℝ) :
    ∑ a, (c₁ * v a - c₂ * w a) * G a = c₁ * ∑ a, v a * G a - c₂ * ∑ a, w a * G a := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem sum_scale {n : ℕ} (c : ℝ) (v G : Fin n → ℝ) :
    ∑ a, c * v a * G a = c * ∑ a, v a * G a := by
  simp only [Finset.mul_sum, mul_assoc]

/-- The pointwise algebraic identity behind `∫ K(x,y) dμ(y) = ½(φ₁ - φ₂)(x)`. -/
theorem pointwise_identity (f : Torus d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Torus d → ℝ)
    (x z : Torus d) :
    ρ (x - z) * pairKernelB f M s x (x - z) =
      (1 / 2 : ℝ) * (inner ℝ (Torus.matVec M.transpose (Torus.grad f x))
          (KernelGrad.kern (periodicRieszGrad d s) ρ x z)
        - ∑ a, (KernelGrad.kern (periodicRieszGrad d s)
            (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x z) a) := by
  by_cases hz : z = 0
  · subst hz
    simp [pairKernelB, KernelGrad.kern]
  · have hxz : x ≠ x - z := fun h => hz (sub_eq_self.mp h.symm)
    unfold pairKernelB KernelGrad.kern
    rw [if_neg hxz, sub_sub_cancel]
    by_cases hc : ‖z‖ ≤ 1 / 4
    · simp only [hc, ↓reduceIte, inner_smul_right, PiLp.smul_apply, smul_eq_mul, inner_sub_left,
        inner_matVec_transpose]
      simp only [inner_euc_eq]
      rw [sum_split]
      ring
    · simp only [hc, ↓reduceIte, inner_smul_right, PiLp.smul_apply, smul_eq_mul, inner_sub_left,
        inner_matVec_transpose]
      simp only [inner_euc_eq]
      rw [sum_scale]
      ring

/-- `∫ K(x,y) dμ(y) = ½ (φ₁(x) - φ₂(x))` for every `x`. -/
theorem integral_pairKernel_eq {f : Torus d → ℝ} (M : Matrix (Fin d) (Fin d) ℝ)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (x : Torus d)
    (hKρ : Integrable (KernelGrad.kern (periodicRieszGrad d s) ρ x))
    (hKψ : ∀ a : Fin d, Integrable (KernelGrad.kern (periodicRieszGrad d s)
      (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x)) :
    ∫ y, pairKernelB f M s x y ∂(withDensityReal ρ) =
      (1 / 2 : ℝ) * (inner ℝ (Torus.grad f x)
        (Torus.matVec M (convGradConv (periodicRieszGrad d s) ρ x)) - divConvB f M s ρ x) := by
  have step1 : ∫ y, pairKernelB f M s x y ∂(withDensityReal ρ)
      = ∫ y, ρ y * pairKernelB f M s x y := by
    unfold withDensityReal
    rw [integral_withDensity_eq_integral_toReal_smul (hρ.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [ENNReal.toReal_ofReal (hρ.nonneg y), smul_eq_mul]
  have step2 : ∫ y, ρ y * pairKernelB f M s x y = ∫ z, ρ (x - z) * pairKernelB f M s x (x - z) :=
    (integral_sub_left_eq_self (fun y => ρ y * pairKernelB f M s x y) volume x).symm
  have step3 : ∫ z, ρ (x - z) * pairKernelB f M s x (x - z) = ∫ z, (1 / 2 : ℝ) *
      (inner ℝ (Torus.matVec M.transpose (Torus.grad f x)) (KernelGrad.kern (periodicRieszGrad d s) ρ x z)
        - ∑ a, (KernelGrad.kern (periodicRieszGrad d s)
            (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x z) a) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => pointwise_identity f M ρ x z)
  have hI1 : Integrable (fun z => inner ℝ (Torus.matVec M.transpose (Torus.grad f x))
      (KernelGrad.kern (periodicRieszGrad d s) ρ x z)) :=
    ContinuousLinearMap.integrable_comp (innerSL ℝ (Torus.matVec M.transpose (Torus.grad f x))) hKρ
  have hI2 : ∀ a : Fin d, Integrable (fun z => (KernelGrad.kern (periodicRieszGrad d s)
      (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x z) a) := fun a =>
    ContinuousLinearMap.integrable_comp (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ) (hKψ a)
  have hI3 : Integrable (fun z => ∑ a, (KernelGrad.kern (periodicRieszGrad d s)
      (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x z) a) :=
    integrable_finsetSum _ fun a _ => hI2 a
  have hA : ∫ z, inner ℝ (Torus.matVec M.transpose (Torus.grad f x))
      (KernelGrad.kern (periodicRieszGrad d s) ρ x z)
      = inner ℝ (Torus.matVec M.transpose (Torus.grad f x))
        (∫ z, KernelGrad.kern (periodicRieszGrad d s) ρ x z) :=
    integral_inner hKρ _
  have hB : ∫ z, ∑ a, (KernelGrad.kern (periodicRieszGrad d s)
      (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x z) a
      = ∑ a, (∫ z, KernelGrad.kern (periodicRieszGrad d s)
        (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x z) a := by
    rw [integral_finsetSum _ fun a _ => hI2 a]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ) (hKψ a))
  rw [step1, step2, step3, integral_const_mul, integral_sub hI1 hI3, hA, hB]
  simp only [← KernelGrad.convGradConv_eq_integral_kern]
  rw [inner_matVec_transpose]
  unfold divConvB
  ring


/-- Lemma 3.1 `B:lem:pairing-expansion` (source lines 1518-1524), torus case: for
`f ∈ C²`, a Hölder probability density `ρ` of exponent `α > max(0, s+1-d)` and pairwise-distinct
particles, the four quantities are finite (absolute convergence of the integrals defining
them) and `B_f(μ_N,μ_N) - B_f(μ,μ) = ⟨∇f·M(∇g*μ), ρ_N⟩ - ⟨Div g*(μ M^*∇f), ρ_N⟩ + B_f(ρ_N,ρ_N)`. -/
theorem pairing_expansion (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (C α : NNReal) (hα0 : 0 < (α : ℝ))
    (hα : s + 1 - d < α) (hHol : HolderWith C α ρ)
    (hN : 1 ≤ N) (X : Config d N) (hX : Pairwise fun i j => X i ≠ X j) :
    let μ := withDensityReal ρ
    let μN := empirical X
    let φ₁ : Torus d → ℝ := fun x =>
      inner ℝ (Torus.grad f x) (Torus.matVec M (convGradConv (periodicRieszGrad d s) ρ x))
    let φ₂ : Torus d → ℝ := divConvB f M s ρ
    (Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) (μ.prod μ) ∧
      Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) (μN.prod μ) ∧
      Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) (μ.prod μN) ∧
      (∀ x, Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • periodicRieszGrad d s (x - y)
        else ρ y • periodicRieszGrad d s (x - y))) ∧
      (∀ (a : Fin d) x, let ψ : Torus d → ℝ := fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a
        Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (ψ y - ψ x) • periodicRieszGrad d s (x - y)
          else ψ y • periodicRieszGrad d s (x - y))) ∧
      Integrable φ₁ μ ∧ Integrable φ₂ μ) ∧
    pairB f M s μN μN - pairB f M s μ μ =
      pairEmp φ₁ X μ - pairEmp φ₂ X μ + pairBSigned f M s μN μ := by
  intro μ μN φ₁ φ₂
  have hd0 : 0 < d := by omega
  obtain ⟨CG, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  have hC0 : (0 : ℝ) ≤ C := NNReal.coe_nonneg C
  have hN' : 0 < N := by omega
  set β : ℝ := min (α : ℝ) 1 with hβdef
  have hβ0 : 0 < β := lt_min hα0 one_pos
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hβα : β ≤ (α : ℝ) := min_le_left _ _
  have hβ : s + 1 - d < β := lt_min hα (by linarith)
  -- density facts
  have hρc : Continuous ρ := hHol.continuous (NNReal.coe_pos.mp hα0)
  obtain ⟨Bρ, hBρ0, hBρ⟩ := bounded_of_continuous hρc
  have hρle : ∀ x, ρ x ≤ Bρ := fun x => (le_abs_self _).trans (hBρ x)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_withDensityReal hρle
  haveI : IsProbabilityMeasure μN := empirical_isProbabilityMeasure hN' X
  have hρH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ (C : ℝ) * ‖z‖ ^ β := by
    intro x z hz
    have h1 := holder_abs_le hHol (x - z) x
    rw [sub_sub_cancel_left, norm_neg] at h1
    have h2 : ‖z‖ ^ (α : ℝ) ≤ ‖z‖ ^ β :=
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) (by linarith) hβ0.le hβα
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
  have hKρ : ∀ x, Integrable (KernelGrad.kern (periodicRieszGrad d s) ρ x) := fun x =>
    integrable_kern_holder hG hρ.measurable hBρ hBρ0 hC0 hβ0 hβ hρH x
  have hclaim4 : ∀ x, Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • periodicRieszGrad d s (x - y)
      else ρ y • periodicRieszGrad d s (x - y)) := fun x =>
    integrable_conv_form hG hρ.measurable hBρ hBρ0 hC0 hβ0 hβ hρH x
  -- the vector-field facts
  have hvcont : ∀ a : Fin d, Continuous (fun y => Torus.matVec M.transpose (Torus.grad f y) a) := by
    intro a
    obtain ⟨Lv, hLv0, hLv⟩ := vcomp_lip M hf a
    exact continuous_of_lip _ hLv0 (fun x y => by rw [Real.norm_eq_abs]; exact hLv x y)
  have hψfacts : ∀ a : Fin d, ∃ Bψ Λψ : ℝ, 0 ≤ Bψ ∧ 0 ≤ Λψ ∧
      (∀ x, |ρ x * Torus.matVec M.transpose (Torus.grad f x) a| ≤ Bψ) ∧
      (∀ x z, ‖z‖ ≤ 1 / 4 → |ρ (x - z) * Torus.matVec M.transpose (Torus.grad f (x - z)) a
          - ρ x * Torus.matVec M.transpose (Torus.grad f x) a| ≤ Λψ * ‖z‖ ^ β) := by
    intro a
    obtain ⟨Lv, hLv0, hLv⟩ := vcomp_lip M hf a
    obtain ⟨Bv, hBv0, hBv⟩ := bounded_of_continuous (hvcont a)
    refine ⟨Bρ * Bv, C * Bv + Bρ * Lv, mul_nonneg hBρ0 hBv0,
      add_nonneg (mul_nonneg hC0 hBv0) (mul_nonneg hBρ0 hLv0), fun x => ?_, fun x z hz => ?_⟩
    · rw [abs_mul]
      exact mul_le_mul (hBρ x) (hBv x) (abs_nonneg _) hBρ0
    · exact holder_mul_kern hβ0.le hβ1 hC0 hLv0 hBρ hBv hρH hLv x hz
  have hψmeas : ∀ a : Fin d, Measurable (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) :=
    fun a => hρ.measurable.mul (hvcont a).measurable
  have hψint : ∀ a : Fin d, ∀ x, Integrable (KernelGrad.kern (periodicRieszGrad d s)
      (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x) := by
    intro a x
    obtain ⟨Bψ, Λψ, hBψ0, hΛψ0, hBψ, hΛψ⟩ := hψfacts a
    exact integrable_kern_holder hG (hψmeas a) hBψ hBψ0 hΛψ0 hβ0 hβ hΛψ x
  have hclaim5 : ∀ (a : Fin d) x, Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then
      ((fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) y
        - (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x) • periodicRieszGrad d s (x - y)
      else (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) y • periodicRieszGrad d s (x - y)) := by
    intro a x
    obtain ⟨Bψ, Λψ, hBψ0, hΛψ0, hBψ, hΛψ⟩ := hψfacts a
    exact integrable_conv_form hG (hψmeas a) hBψ hBψ0 hΛψ0 hβ0 hβ hΛψ x
  -- uniform bounds for the convention convolutions
  obtain ⟨Kρ, hKρb⟩ : ∃ K, ∀ x, ‖convGradConv (periodicRieszGrad d s) ρ x‖ ≤ K :=
    ⟨_, fun x => conv_norm_le hG hBρ hBρ0 hC0 hβ0 hβ hρH x⟩
  have hconvψ : ∀ a : Fin d, ∃ K, ∀ x, ‖convGradConv (periodicRieszGrad d s)
      (fun y => ρ y * Torus.matVec M.transpose (Torus.grad f y) a) x‖ ≤ K := by
    intro a
    obtain ⟨Bψ, Λψ, hBψ0, hΛψ0, hBψ, hΛψ⟩ := hψfacts a
    exact ⟨_, fun x => conv_norm_le hG hBψ hBψ0 hΛψ0 hβ0 hβ hΛψ x⟩
  choose Kψ hKψb using hconvψ
  obtain ⟨CM, hCM0, hCM⟩ := exists_matVec_bound M
  obtain ⟨Gb, hGb0, hGb⟩ := bounded_of_continuous (grad_continuous hf).norm
  have hGb' : ∀ x, ‖Torus.grad f x‖ ≤ Gb := fun x => by
    have := hGb x
    rwa [abs_norm] at this
  have hmatC : Continuous (fun v : Euc d => Torus.matVec M v) := by
    have e : (fun v : Euc d => Torus.matVec M v)
        = ⇑(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) := rfl
    rw [e]
    exact ContinuousLinearMap.continuous _
  -- the functions φ₁, φ₂: bounds and measurability
  have hφ1b : ∀ x, |φ₁ x| ≤ Gb * (CM * Kρ) := by
    intro x
    show |inner ℝ (Torus.grad f x) (Torus.matVec M (convGradConv (periodicRieszGrad d s) ρ x))| ≤ _
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul (hGb' x) ((hCM _).trans (mul_le_mul_of_nonneg_left (hKρb x) hCM0))
      (norm_nonneg _) hGb0
  have hφ1m : Measurable φ₁ := by
    show Measurable (fun x => inner ℝ (Torus.grad f x)
      (Torus.matVec M (convGradConv (periodicRieszGrad d s) ρ x)))
    exact (grad_continuous hf).measurable.inner
      (hmatC.measurable.comp (measurable_conv hG hρ.measurable))
  have hφ2b : ∀ x, |φ₂ x| ≤ ∑ a, Kψ a := by
    intro x
    show |divConvB f M s ρ x| ≤ _
    unfold divConvB
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    calc |convGradConv (periodicRieszGrad d s) (fun y => ρ y * Torus.matVec M.transpose
            (Torus.grad f y) a) x a|
        = ‖convGradConv (periodicRieszGrad d s) (fun y => ρ y * Torus.matVec M.transpose
            (Torus.grad f y) a) x a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖convGradConv (periodicRieszGrad d s) (fun y => ρ y * Torus.matVec M.transpose
            (Torus.grad f y) a) x‖ := PiLp.norm_apply_le _ a
      _ ≤ Kψ a := hKψb a x
  have hφ2m : Measurable φ₂ := by
    show Measurable (fun x => divConvB f M s ρ x)
    unfold divConvB
    exact Finset.measurable_sum _ fun a _ =>
      ((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.measurable).comp
        (measurable_conv hG (hψmeas a))
  have hφ1i : Integrable φ₁ μ := integrable_of_bdd_meas hφ1m hφ1b
  have hφ2i : Integrable φ₂ μ := integrable_of_bdd_meas hφ2m hφ2b
  -- the four integrability claims on the kernel
  have K1 : Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) (μ.prod μ) :=
    pairKernelB_integrable_prod hf M hG hρle hBρ0
  have K2 : Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) (μN.prod μ) :=
    pairKernelB_integrable_prod hf M hG hρle hBρ0
  have K3 : Integrable (fun p : Torus d × Torus d => pairKernelB f M s p.1 p.2) (μ.prod μN) := by
    refine (K2.swap).congr (Filter.Eventually.of_forall fun p => ?_)
    exact pairKernelB_symm M hsd p.1 p.2
  -- the inner integrals
  have hint : ∀ x, ∫ y, pairKernelB f M s x y ∂μ = (1 / 2 : ℝ) * (φ₁ x - φ₂ x) := fun x =>
    integral_pairKernel_eq M hρ x (hKρ x) (fun a => hψint a x)
  have hBmm : pairB f M s μ μ = (1 / 2 : ℝ) * (∫ x, φ₁ x ∂μ - ∫ x, φ₂ x ∂μ) := by
    calc pairB f M s μ μ = ∫ x, ∫ y, pairKernelB f M s x y ∂μ ∂μ := integral_prod _ K1
      _ = ∫ x, (1 / 2 : ℝ) * (φ₁ x - φ₂ x) ∂μ := integral_congr_ae (Filter.Eventually.of_forall hint)
      _ = _ := by rw [integral_const_mul, integral_sub hφ1i hφ2i]
  have hBNm : pairB f M s μN μ = (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, φ₁ (X i)
      - (N : ℝ)⁻¹ * ∑ i, φ₂ (X i)) := by
    have hφ1N : Integrable φ₁ μN := integrable_of_bdd_meas hφ1m hφ1b
    have hφ2N : Integrable φ₂ μN := integrable_of_bdd_meas hφ2m hφ2b
    calc pairB f M s μN μ = ∫ x, ∫ y, pairKernelB f M s x y ∂μ ∂μN := integral_prod _ K2
      _ = ∫ x, (1 / 2 : ℝ) * (φ₁ x - φ₂ x) ∂μN := integral_congr_ae (Filter.Eventually.of_forall hint)
      _ = _ := by
        have e1 : ∫ x, φ₁ x ∂μN = (N : ℝ)⁻¹ * ∑ i, φ₁ (X i) := pair_empirical hN' X φ₁
        have e2 : ∫ x, φ₂ x ∂μN = (N : ℝ)⁻¹ * ∑ i, φ₂ (X i) := pair_empirical hN' X φ₂
        rw [integral_const_mul, integral_sub hφ1N hφ2N, e1, e2]
  have hBmN : pairB f M s μ μN = pairB f M s μN μ := by
    unfold pairB
    rw [← integral_prod_swap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact pairKernelB_symm M hsd p.1 p.2
  refine ⟨⟨K1, K2, K3, hclaim4, fun a x => hclaim5 a x, hφ1i, hφ2i⟩, ?_⟩
  unfold pairBSigned pairEmp
  linarith [hBmm, hBNm, hBmN]

end Duality

end HRS

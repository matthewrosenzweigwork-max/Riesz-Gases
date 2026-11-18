import HRS.Prob.CLT

/-!
# Discrete Lindeberg/Taylor route to Lemma A.21 (package CLT-01)

Lemma A.21 `M:B:lem:lindeberg` (source lines 10545-10551; statements
`HRS.multivariate_martingale_clt`, `HRS.multivariate_martingale_clt_dc2` in
`HRS/Prob/CLT.lean`) is proved in the source (lines 10553-10598) with the backward heat
function `u(σ, x) = E h(x + G_{σ,t})`, `G_{σ,t} ∼ N(0, ∫_σ^t sb)`, and Itô's formula.  Mathlib has
no stochastic calculus, so the formalisation follows a **discrete** route along the uniform
partitions `τ_k = k t / n` and never uses Itô's formula:

1. `gaussSmooth h Q x = ∫ h(x + y) dN(0, Q)(y)` (the source's `u(σ, ·)` with
   `Q = ∫_σ^t sb`); it keeps the Hessian bound and the Hessian Lipschitz constant, satisfies the
   semigroup identity, and `gaussSmooth h 0 = h`.
2. Telescoping `E h(M_t) - E h(G) = ∑_k E[u_{k+1}(M_{τ_{k+1}}) - u_k(M_{τ_k})]`, with
   `u_k(x) = ∫ u_{k+1}(x + y) dN(0, Q_k)`, `Q_k = ∫_{τ_k}^{τ_{k+1}} sb`.
3. Second-order Taylor expansion of `u_{k+1}` at `M_{τ_k}` in the increment `ΔM_k` and in the
   Gaussian variable `y`: first-order terms vanish (martingale property; mean zero), the
   second-order terms give `½ E⟨∇²u_{k+1}(M_{τ_k}), ∫_{τ_k}^{τ_{k+1}} (Σ - sb)⟩` (covariation
   martingale), bounded by trace duality by `½ H E∫_{τ_k}^{τ_{k+1}} ‖Σ - sb‖_{S_1}`.
4. Remainders `min(H|v|², L|v|³)`; their sums tend to zero along the uniform partitions
   (discrete Lindeberg condition, from path continuity and uniform integrability of the
   discrete quadratic variations after localisation).
5. A Gaussian smoothing of `h` (step 1 with `Q = ε² I`) reduces general `h ∈ C²` with bounded
   Hessian to `h` with a Lipschitz Hessian, at uniform cost `½ H ε² p`.

All statements below are proof infrastructure for Lemma A.21; none is a new source claim.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

section Lindeberg

variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The Gaussian smoothing `x ↦ ∫ h(x + y) dN(0, Q)(y)`; with `Q = ∫_σ^t sb` it is the backward
heat function `u(σ, x) = E h(x + G_{σ,t})` of the proof of Lemma A.21 (source lines 10556-10560). -/
def gaussSmooth (h : (ℝ^p) → ℝ) (Q : Matrix (Fin p) (Fin p) ℝ) (x : ℝ^p) : ℝ :=
  ∫ y, h (x + y) ∂(multivariateGaussian 0 Q)

/-- The covariance block `∫_a^b sb(σ) dσ`. -/
def covBlock (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => ∫ σ in Set.Icc a b, sb σ i j

/-- The uniform partition point `τ_k = k t / n`. -/
def unifPart (t : ℝ) (n k : ℕ) : ℝ := k * t / n

/-- The Taylor remainder envelope `min(H|v|², L|v|³)`. -/
def taylorRem (H L : ℝ) (v : ℝ^p) : ℝ := min (H * ‖v‖ ^ 2) (L * ‖v‖ ^ 3)

/-- Step 1: `gaussSmooth h 0 = h` (terminal condition `u(t, ·) = h`). -/
theorem gaussSmooth_zero (h : (ℝ^p) → ℝ) : gaussSmooth h 0 = h := by
  funext x
  have : multivariateGaussian (0 : ℝ^p) (0 : Matrix (Fin p) (Fin p) ℝ) = Measure.dirac 0 := by
    simp [multivariateGaussian]
  simp [gaussSmooth, this]


namespace LindebergAux

lemma hasFDerivAt_gaussInt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (γ : Measure (ℝ^p)) [IsProbabilityMeasure γ] [IsGaussian γ]
    (g : (ℝ^p) → V) (hg : ContDiff ℝ 1 g) (a b : ℝ) (hb : 0 ≤ b)
    (hgd : ∀ z, ‖fderiv ℝ g z‖ ≤ a + b * ‖z‖)
    (hgi : ∀ x, Integrable (fun z => g (x + z)) γ) (x : ℝ^p) :
    HasFDerivAt (fun x => ∫ z, g (x + z) ∂γ) (∫ z, fderiv ℝ g (x + z) ∂γ) x := by
  have hm2 : MemLp id 2 γ := IsGaussian.memLp_two_id
  have h1 : Integrable (fun y : ℝ^p => ‖y‖) γ := (hm2.integrable (by norm_num)).norm
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x z => g (x + z))
    (F' := fun x z => fderiv ℝ g (x + z)) (bound := fun z => a + b * (‖x‖ + 1) + b * ‖z‖)
    (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos) ?_ (hgi x) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y => (hgi y).aestronglyMeasurable
  · exact (hcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · refine ae_of_all _ fun z y hy => ?_
    have : ‖y‖ ≤ ‖x‖ + 1 := by
      have := Metric.mem_ball.1 hy
      rw [dist_eq_norm] at this
      calc ‖y‖ = ‖(y - x) + x‖ := by simp
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc ‖fderiv ℝ g (y + z)‖ ≤ a + b * ‖y + z‖ := hgd _
      _ ≤ a + b * (‖x‖ + 1 + ‖z‖) := by
          gcongr
          exact (norm_add_le _ _).trans (by linarith)
      _ = _ := by ring
  · exact (integrable_const _).add (h1.const_mul _)
  · refine ae_of_all _ fun z y _ => ?_
    exact (hasFDerivAt_comp_add_right z).2 (hdiff (y + z)).hasFDerivAt

lemma norm_fderiv_le_lin {h : (ℝ^p) → ℝ} (hh : ContDiff ℝ 2 h) {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) (z : ℝ^p) :
    ‖fderiv ℝ h z‖ ≤ ‖fderiv ℝ h 0‖ + H * ‖z‖ := by
  have := norm_fderiv_sub_le hh hH 0 z
  rw [sub_zero] at this
  calc ‖fderiv ℝ h z‖ = ‖(fderiv ℝ h z - fderiv ℝ h 0) + fderiv ℝ h 0‖ := by simp
    _ ≤ ‖fderiv ℝ h z - fderiv ℝ h 0‖ + ‖fderiv ℝ h 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

lemma norm_hess_le {h : (ℝ^p) → ℝ} {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) (z : ℝ^p) :
    ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ H := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := h) (x := z) (n := 1)
  rw [norm_iteratedFDeriv_one] at this
  rw [this]; exact hH z

lemma gaussSmooth_derivs (Q : Matrix (Fin p) (Fin p) ℝ)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H : ℝ) (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) :
    (∀ x, HasFDerivAt (gaussSmooth h Q) (∫ z, fderiv ℝ h (x + z) ∂(multivariateGaussian 0 Q)) x) ∧
    (∀ x, HasFDerivAt (fun x => ∫ z, fderiv ℝ h (x + z) ∂(multivariateGaussian 0 Q))
      (∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂(multivariateGaussian 0 Q)) x) ∧
    Continuous (fun x => ∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂(multivariateGaussian 0 Q)) := by
  set γ := multivariateGaussian (0 : ℝ^p) Q with hγ
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hd1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
  have hm2 : MemLp id 2 γ := IsGaussian.memLp_two_id
  have h1 : Integrable (fun y : ℝ^p => ‖y‖) γ := (hm2.integrable (by norm_num)).norm
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · exact hasFDerivAt_gaussInt γ h (hh.of_le (by norm_num)) ‖fderiv ℝ h 0‖ H hH0
      (norm_fderiv_le_lin hh hH) (fun x => integrable_shift_gaussian hh hH γ x) x
  · refine hasFDerivAt_gaussInt γ (fderiv ℝ h) hd1 H 0 le_rfl
      (fun z => by simpa using norm_hess_le hH z) (fun x => ?_) x
    have hg : Integrable (fun y : ℝ^p => ‖fderiv ℝ h 0‖ + H * ‖x‖ + H * ‖y‖) γ :=
      (integrable_const _).add (h1.const_mul _)
    refine Integrable.mono' hg
      ((hd1.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    calc ‖fderiv ℝ h (x + y)‖ ≤ ‖fderiv ℝ h 0‖ + H * ‖x + y‖ := norm_fderiv_le_lin hh hH _
      _ ≤ _ := by
          have := norm_add_le x y
          nlinarith
  · have hc : Continuous (fderiv ℝ (fderiv ℝ h)) := (hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    refine continuous_of_dominated (bound := fun _ => H) (fun x => ?_) (fun x => ae_of_all _ fun z => ?_)
      (integrable_const _) (ae_of_all _ fun z => ?_)
    · exact (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · exact norm_hess_le hH _
    · exact hc.comp (continuous_id.add continuous_const)

lemma integrable_shift_of_bdd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (γ : Measure (ℝ^p)) [IsProbabilityMeasure γ] (g : (ℝ^p) → V) (hg : Continuous g) (C : ℝ)
    (hC : ∀ z, ‖g z‖ ≤ C) (x : ℝ^p) : Integrable (fun z => g (x + z)) γ :=
  Integrable.mono' (integrable_const C)
    ((hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (ae_of_all _ fun _ => hC _)

lemma norm_iter2 {f : (ℝ^p) → ℝ} (x : ℝ^p) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 1)
  rw [norm_iteratedFDeriv_one] at this
  rw [← this]

/-- the evaluation of a bilinear-valued CLM at a pair of vectors -/
noncomputable def evalBil (a b : ℝ^p) : ((ℝ^p) →L[ℝ] (ℝ^p) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.apply ℝ ((ℝ^p) →L[ℝ] ℝ) a)

lemma evalBil_apply (a b : ℝ^p) (T : (ℝ^p) →L[ℝ] (ℝ^p) →L[ℝ] ℝ) : evalBil a b T = T a b := rfl

end LindebergAux
open LindebergAux

/-- Step 1: the Gaussian smoothing of an `h ∈ C²` with `‖∇²h‖ ≤ H` is `C²` with `‖∇²u‖ ≤ H`,
and an `L`-Lipschitz Hessian stays `L`-Lipschitz (differentiation under the integral sign;
`h` has at most quadratic growth, so all integrals converge). -/
theorem gaussSmooth_hessian (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.PosSemidef)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H : ℝ) (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) :
    ContDiff ℝ 2 (gaussSmooth h Q) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 (gaussSmooth h Q) x‖ ≤ H) ∧
      ∀ L : ℝ, (∀ x y, ‖iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y‖ ≤ L * ‖x - y‖) →
        ∀ x y, ‖iteratedFDeriv ℝ 2 (gaussSmooth h Q) x -
          iteratedFDeriv ℝ 2 (gaussSmooth h Q) y‖ ≤ L * ‖x - y‖ := by
  set γ := multivariateGaussian (0 : ℝ^p) Q with hγ
  obtain ⟨h1, h2, h3⟩ := gaussSmooth_derivs Q h hh H hH
  have hfd : fderiv ℝ (gaussSmooth h Q) = fun x => ∫ z, fderiv ℝ h (x + z) ∂γ :=
    funext fun x => (h1 x).fderiv
  have hfd2 : ∀ x, fderiv ℝ (fderiv ℝ (gaussSmooth h Q)) x =
      ∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂γ := by
    intro x; rw [hfd]; exact (h2 x).fderiv
  have hc : Continuous (fderiv ℝ (fderiv ℝ h)) :=
    (hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hG := fun x : ℝ^p => integrable_shift_of_bdd (V := (ℝ^p) →L[ℝ] (ℝ^p) →L[ℝ] ℝ) γ (fderiv ℝ (fderiv ℝ h)) hc H (norm_hess_le hH) x
  refine ⟨?_, ?_, ?_⟩
  · refine (contDiff_succ_iff_fderiv (n := 1)).2 ⟨fun x => (h1 x).differentiableAt, by simp, ?_⟩
    rw [hfd]
    refine contDiff_one_iff_fderiv.2 ⟨fun x => (h2 x).differentiableAt, ?_⟩
    have : fderiv ℝ (fun x => ∫ z, fderiv ℝ h (x + z) ∂γ) =
        fun x => ∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂γ := funext fun x => (h2 x).fderiv
    rw [this]; exact h3
  · intro x
    rw [norm_iter2, hfd2]
    have := norm_integral_le_of_norm_le_const (μ := γ) (C := H)
      (f := fun z => fderiv ℝ (fderiv ℝ h) (x + z)) (ae_of_all _ fun z => norm_hess_le hH _)
    simpa using this
  · intro L hL x y
    refine ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg _).trans (hL x y)) fun m => ?_
    have hψ : ∀ x a : ℝ^p, Integrable (fun z => fderiv ℝ (fderiv ℝ h) (x + z) a) γ := by
      intro x a
      refine integrable_shift_of_bdd (V := (ℝ^p) →L[ℝ] ℝ) γ (fun w => fderiv ℝ (fderiv ℝ h) w a)
        (by fun_prop) (H * ‖a‖) (fun w => ?_) x
      exact ((fderiv ℝ (fderiv ℝ h) w).le_opNorm a).trans (by gcongr; exact norm_hess_le hH w)
    have e2 : ∀ x : ℝ^p, ∀ a b : ℝ^p, (∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂γ) a b =
        ∫ z, fderiv ℝ (fderiv ℝ h) (x + z) a b ∂γ := by
      intro x a b
      rw [ContinuousLinearMap.integral_apply (hG x) a, ContinuousLinearMap.integral_apply (hψ x a) b]
    have e3 : ∀ x : ℝ^p, ∀ a b : ℝ^p, Integrable (fun z => fderiv ℝ (fderiv ℝ h) (x + z) a b) γ := by
      intro x a b
      refine integrable_shift_of_bdd (V := ℝ) γ (fun w => fderiv ℝ (fderiv ℝ h) w a b)
        (by fun_prop) (H * ‖a‖ * ‖b‖) (fun w => ?_) x
      rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
      calc ‖fderiv ℝ (fderiv ℝ h) w a b‖ ≤ ‖fderiv ℝ (fderiv ℝ h) w a‖ * ‖b‖ :=
            (fderiv ℝ (fderiv ℝ h) w a).le_opNorm b
        _ ≤ (‖fderiv ℝ (fderiv ℝ h) w‖ * ‖a‖) * ‖b‖ := by
            gcongr; exact (fderiv ℝ (fderiv ℝ h) w).le_opNorm a
        _ ≤ _ := by gcongr; exact norm_hess_le hH w
    have e1 : (iteratedFDeriv ℝ 2 (gaussSmooth h Q) x - iteratedFDeriv ℝ 2 (gaussSmooth h Q) y) m =
        ∫ z, ((iteratedFDeriv ℝ 2 h (x + z) - iteratedFDeriv ℝ 2 h (y + z)) m) ∂γ := by
      simp only [sub_apply, iteratedFDeriv_two_apply, hfd2, e2]
      rw [← integral_sub (e3 x _ _) (e3 y _ _)]
    rw [e1]
    have hb := norm_integral_le_of_norm_le_const (μ := γ) (C := L * ‖x - y‖ * ∏ i, ‖m i‖)
      (f := fun z => (iteratedFDeriv ℝ 2 h (x + z) - iteratedFDeriv ℝ 2 h (y + z)) m)
      (ae_of_all _ fun z => by
        refine (ContinuousMultilinearMap.le_opNorm _ m).trans ?_
        have := hL (x + z) (y + z)
        rw [add_sub_add_right_eq_sub] at this
        gcongr)
    simpa using hb


/-- Step 1: semigroup identity `u(σ, x) = ∫ u(σ', x + y) dN(0, ∫_σ^{σ'} sb)(y)`, i.e.
`N(0, Q₁) * N(0, Q₂) = N(0, Q₁ + Q₂)` tested against the quadratically growing `h`. -/
theorem gaussSmooth_add (Q₁ Q₂ : Matrix (Fin p) (Fin p) ℝ) (hQ₁ : Q₁.PosSemidef)
    (hQ₂ : Q₂.PosSemidef) (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H : ℝ)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) (x : ℝ^p) :
    gaussSmooth h (Q₁ + Q₂) x = ∫ y, gaussSmooth h Q₂ (x + y) ∂(multivariateGaussian 0 Q₁) := by
  unfold gaussSmooth
  rw [← mvGaussian_conv hQ₁ hQ₂]
  have hint : Integrable (fun z => h (x + z)) (multivariateGaussian (0 : ℝ^p) Q₁ ∗ multivariateGaussian (0 : ℝ^p) Q₂) := by
    rw [mvGaussian_conv hQ₁ hQ₂]
    exact integrable_shift_gaussian hh hH _ x
  rw [integral_conv hint]
  simp_rw [add_assoc]


namespace LindebergAux

lemma gaussSmooth_sub_le (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.PosSemidef)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H : ℝ) (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H)
    (x : ℝ^p) : |gaussSmooth h Q x - h x| ≤ (1 / 2) * H * Matrix.trace Q := by
  set ν := multivariateGaussian (0 : ℝ^p) Q with hν
  have hmem : MemLp id 2 ν := IsGaussian.memLp_two_id
  have hy : Integrable (fun y : ℝ^p => y) ν := hmem.integrable (by norm_num)
  have hsq : Integrable (fun y : ℝ^p => ‖y‖ ^ 2) ν := hmem.norm.integrable_sq
  have hlin : ∫ y, fderiv ℝ h x y ∂ν = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm hy (fderiv ℝ h x)]
    simp [hν]
  have hi1 := integrable_shift_gaussian hh hH ν x
  have hi2 : Integrable (fun y => fderiv ℝ h x y) ν := (fderiv ℝ h x).integrable_comp hy
  have : gaussSmooth h Q x - h x = ∫ y, (h (x + y) - h x - fderiv ℝ h x y) ∂ν := by
    rw [integral_sub (f := fun y => h (x + y) - h x) (g := fun y => fderiv ℝ h x y)
      (hi1.sub (integrable_const _)) hi2, integral_sub (f := fun y => h (x + y))
      (g := fun _ => h x) hi1 (integrable_const _), hlin]
    simp [gaussSmooth, hν]
  rw [this, ← Real.norm_eq_abs]
  calc _ ≤ ∫ y, H / 2 * ‖y‖ ^ 2 ∂ν := by
        refine norm_integral_le_of_norm_le (hsq.const_mul _) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs]; exact taylor_two_bound hh hH x y
    _ = (1 / 2) * H * Matrix.trace Q := by
        rw [integral_const_mul, hν, integral_norm_sq_mvGaussian hQ]; ring



lemma exists_sub_psd (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (Q - c • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef := by
  classical
  have key : ∀ c : ℝ, (∀ x : Fin p → ℝ, c * dotProduct x x ≤ dotProduct x (Q.mulVec x)) →
      (Q - c • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef := by
    intro c hc
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · have h1 : (c • (1 : Matrix (Fin p) (Fin p) ℝ)).IsHermitian := by
        unfold Matrix.IsHermitian
        simp
      exact hQ.isHermitian.sub h1
    · have := hc x
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul]
      linarith
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · refine ⟨1, one_pos, key 1 fun x => ?_⟩
    simp [dotProduct]
  · have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    have hq : Continuous (fun x : ℝ^p => dotProduct x.ofLp (Q.mulVec x.ofLp)) := by
      unfold dotProduct Matrix.mulVec
      fun_prop
    obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : ℝ^p) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) hq.continuousOn
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hx0ne : x0.ofLp ≠ 0 := by
      intro h
      have : x0 = 0 := by ext i; simpa using congrFun h i
      rw [this] at hx0n; simp at hx0n
    have hm : 0 < dotProduct x0.ofLp (Q.mulVec x0.ofLp) := by
      simpa using hQ.dotProduct_mulVec_pos hx0ne
    refine ⟨_, hm, key _ fun x => ?_⟩
    set y : ℝ^p := WithLp.toLp 2 x with hy
    have hyn : dotProduct x x = ‖y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [dotProduct, sq, hy]
    have hyq : dotProduct x (Q.mulVec x) = dotProduct y.ofLp (Q.mulVec y.ofLp) := rfl
    rw [hyn, hyq]
    by_cases hy0 : y = 0
    · have : x = 0 := by
        ext i; have := congrArg (fun z : ℝ^p => z i) hy0; simpa [hy] using this
      subst this
      simp [hy]
    · have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hsph : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : ℝ^p) 1 := by
        simp [norm_smul, hyp.ne']
      have h1 := hmin hsph
      simp only [Set.mem_ofPred_eq] at h1
      have e : dotProduct (‖y‖⁻¹ • y).ofLp (Q.mulVec (‖y‖⁻¹ • y).ofLp) =
          (‖y‖⁻¹) ^ 2 * dotProduct y.ofLp (Q.mulVec y.ofLp) := by
        simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        ring
      rw [e] at h1
      have h2 : ‖y‖ ^ 2 * (‖y‖⁻¹) ^ 2 = 1 := by field_simp
      calc _ = ‖y‖ ^ 2 * (dotProduct x0.ofLp (Q.mulVec x0.ofLp)) := by ring
        _ ≤ ‖y‖ ^ 2 * ((‖y‖⁻¹) ^ 2 * dotProduct y.ofLp (Q.mulVec y.ofLp)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by rw [← mul_assoc, h2, one_mul]


lemma gsmooth_lip {ε : ℝ} (hε : 0 < ε) {f : (ℝ^p) → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (x y : ℝ^p) :
    |gsmooth ε f x - gsmooth ε f y| ≤ R * (Real.sqrt p / ε) * ‖x - y‖ := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  have hbd : ∀ z : ℝ^p, ‖∫ w, f w • fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) (z - w)‖ ≤
      R * (Real.sqrt p / ε) := by
    intro z
    refine (norm_conv_le hf hR
      ((contDiff_gaussKernel (p := p) _).continuous_fderiv (by simp))
      (integrable_fderiv_gaussKernel (p := p) hb) z).trans ?_
    exact mul_le_mul_of_nonneg_left (integral_norm_fderiv_gaussKernel_le hε)
      ((abs_nonneg _).trans (hR 0))
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := gsmooth ε f) (f' := fun z => ∫ w, f w • fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) (z - w))
    (s := Set.univ) (fun z _ => (gsmooth_hasFDerivAt hε hf hR z).hasFDerivWithinAt)
    (fun z _ => hbd z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rwa [Real.norm_eq_abs] at this


lemma gaussKernel_neg (b : ℝ) (z : ℝ^p) : gaussKernel p b (-z) = gaussKernel p b z := by
  simp [gaussKernel, norm_neg]

lemma hess_entry_eq_gsmooth {ε : ℝ} (hε : 0 < ε) (g : (ℝ^p) → ℝ) (hg : ContDiff ℝ 2 g) (H : ℝ)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ H) (x a b : ℝ^p) :
    fderiv ℝ (fderiv ℝ (gaussSmooth g (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) x a b =
      gsmooth ε (fun w => fderiv ℝ (fderiv ℝ g) w a b) x := by
  set γ := multivariateGaussian (0 : ℝ^p) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) with hγ
  obtain ⟨h1, h2, -⟩ := gaussSmooth_derivs (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) g hg H hH
  have hfd : fderiv ℝ (gaussSmooth g (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))) =
      fun x => ∫ z, fderiv ℝ g (x + z) ∂γ := funext fun x => (h1 x).fderiv
  have hfd2 : fderiv ℝ (fderiv ℝ (gaussSmooth g (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) x =
      ∫ z, fderiv ℝ (fderiv ℝ g) (x + z) ∂γ := by
    rw [hfd]; exact (h2 x).fderiv
  have hc : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hG := integrable_shift_of_bdd (V := (ℝ^p) →L[ℝ] (ℝ^p) →L[ℝ] ℝ) γ (fderiv ℝ (fderiv ℝ g)) hc
    H (norm_hess_le hH) x
  have hψ : Integrable (fun z => fderiv ℝ (fderiv ℝ g) (x + z) a) γ := by
    refine integrable_shift_of_bdd (V := (ℝ^p) →L[ℝ] ℝ) γ (fun w => fderiv ℝ (fderiv ℝ g) w a)
      (by fun_prop) (H * ‖a‖) (fun w => ?_) x
    exact ((fderiv ℝ (fderiv ℝ g) w).le_opNorm a).trans (by gcongr; exact norm_hess_le hH w)
  have e2 : (∫ z, fderiv ℝ (fderiv ℝ g) (x + z) ∂γ) a b =
      ∫ z, fderiv ℝ (fderiv ℝ g) (x + z) a b ∂γ := by
    rw [ContinuousLinearMap.integral_apply hG a, ContinuousLinearMap.integral_apply hψ b]
  rw [hfd2, e2]
  have h3 := integral_kernel_eq_mvG (p := p) hε (fun z => fderiv ℝ (fderiv ℝ g) (x + z) a b)
  rw [← hγ] at h3
  rw [← h3]
  unfold gsmooth
  rw [← integral_add_left_eq_self (μ := volume) (fun y => (fderiv ℝ (fderiv ℝ g) y a b) •
    gaussKernel p (1 / (2 * ε ^ 2)) (x - y)) x]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul, sub_add_cancel_left, gaussKernel_neg]
  ring

end LindebergAux
open LindebergAux

/-- Step 5 (mollification): `|gaussSmooth h Q x - h x| ≤ ½ H tr Q` (the first-order term
integrates to zero), and for positive definite `Q` the smoothed function has a Lipschitz
Hessian. -/
theorem gaussSmooth_approx (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.PosDef)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H : ℝ) (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) :
    (∀ x, |gaussSmooth h Q x - h x| ≤ (1 / 2) * H * Q.trace) ∧
      ∃ L : ℝ, ∀ x y, ‖iteratedFDeriv ℝ 2 (gaussSmooth h Q) x -
        iteratedFDeriv ℝ 2 (gaussSmooth h Q) y‖ ≤ L * ‖x - y‖ := by
  refine ⟨fun x => gaussSmooth_sub_le Q hQ.posSemidef h hh H hH x, ?_⟩
  obtain ⟨c, hc, hQ₂⟩ := exists_sub_psd Q hQ
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.sqrt c := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact Real.sqrt_pos.2 hc
  have hε2 : ε ^ 2 = c := by rw [hεdef]; exact Real.sq_sqrt hc.le
  set g := gaussSmooth h (Q - c • (1 : Matrix (Fin p) (Fin p) ℝ)) with hgdef
  obtain ⟨hg, hgH, -⟩ := gaussSmooth_hessian (Q - c • (1 : Matrix (Fin p) (Fin p) ℝ)) hQ₂ h hh H hH
  have hpsd1 : (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by positivity)
  have hu : gaussSmooth h Q = gaussSmooth g (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) := by
    funext x
    have := gaussSmooth_add (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))
      (Q - c • (1 : Matrix (Fin p) (Fin p) ℝ)) hpsd1 hQ₂ h hh H hH x
    have e : ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) + (Q - c • (1 : Matrix (Fin p) (Fin p) ℝ)) = Q := by
      rw [hε2]; abel
    rw [e] at this
    exact this
  refine ⟨H * (Real.sqrt p / ε), fun x y => ?_⟩
  rw [hu]
  have hL0 : 0 ≤ H * (Real.sqrt p / ε) := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hL0 (norm_nonneg _)) fun m => ?_
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hf : Continuous (fun w => fderiv ℝ (fderiv ℝ g) w (m 0) (m 1)) := by fun_prop
  have hbd : ∀ w, |fderiv ℝ (fderiv ℝ g) w (m 0) (m 1)| ≤ H * ‖m 0‖ * ‖m 1‖ := by
    intro w
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ g) w (m 0) (m 1)‖ ≤ ‖fderiv ℝ (fderiv ℝ g) w (m 0)‖ * ‖m 1‖ :=
          (fderiv ℝ (fderiv ℝ g) w (m 0)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ g) w‖ * ‖m 0‖) * ‖m 1‖ := by
          gcongr; exact (fderiv ℝ (fderiv ℝ g) w).le_opNorm _
      _ ≤ _ := by gcongr; exact norm_hess_le hgH w
  have key := gsmooth_lip hε hf hbd x y
  simp only [sub_apply, iteratedFDeriv_two_apply,
    hess_entry_eq_gsmooth hε g hg H hgH, Fin.prod_univ_two]
  rw [← Real.norm_eq_abs] at key
  calc _ ≤ H * ‖m 0‖ * ‖m 1‖ * (Real.sqrt p / ε) * ‖x - y‖ := by simpa using key
    _ = _ := by ring


namespace LindebergAux

lemma abs_iter2_le {f : (ℝ^p) → ℝ} {H : ℝ} (hH : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ H) (x v : ℝ^p) :
    |iteratedFDeriv ℝ 2 f x ![v, v]| ≤ H * ‖v‖ ^ 2 := by
  have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![v, v]
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : 0 ≤ ‖v‖ * ‖v‖ := by positivity
  nlinarith [hH x]

lemma taylor_L_bound {f : (ℝ^p) → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ}
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖)
    (x v : ℝ^p) :
    |f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v]| ≤
      L * ‖v‖ ^ 3 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set B : ℝ := iteratedFDeriv ℝ 2 f x ![v, v] with hB
  have hBx : B = fderiv ℝ (fderiv ℝ f) x v v := by
    simp [hB, iteratedFDeriv_two_apply]
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := by
    intro s; simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + s • v) v) s := fun s =>
    (hd1 (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hφ' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x + s • v) v v) s := by
    intro s
    have h1 := (hd2 (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt s h1
    exact h2
  set k : ℝ → ℝ := fun s => fderiv ℝ f (x + s • v) v - s * B with hk
  have hkd : ∀ s, HasDerivAt k (fderiv ℝ (fderiv ℝ f) (x + s • v) v v - B) s := by
    intro s
    have := (hφ' s).sub ((hasDerivAt_id s).mul_const B)
    simp only [one_mul, id] at this
    exact this
  set g : ℝ → ℝ := fun s => f (x + s • v) - s * fderiv ℝ f x v - (1 / 2) * s ^ 2 * B with hg
  have hgd : ∀ s, HasDerivAt g (k s - fderiv ℝ f x v) s := by
    intro s
    have h1 := (hφ s).sub ((hasDerivAt_id s).mul_const (fderiv ℝ f x v))
    have h2 := (((hasDerivAt_id s).pow 2).const_mul (1 / 2 : ℝ)).mul_const B
    have := h1.sub h2
    convert this using 1
    · funext y; simp [hg]
    · simp [hk]; ring
  by_cases hv : v = 0
  · subst hv
    have hB0 : B = 0 := (iteratedFDeriv ℝ 2 f x).map_coord_zero 0 (by simp)
    simp [hB0]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hL0 : 0 ≤ L := by
    have := (norm_nonneg _).trans (hL x (x + v))
    rw [sub_add_cancel_left, norm_neg] at this
    exact nonneg_of_mul_nonneg_left this hvpos
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g (fun s => k s - fderiv ℝ f x v) zero_lt_one
    (fun s _ => (hgd s).continuousAt.continuousWithinAt) (fun s _ => hgd s)
  obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope k
    (fun s => fderiv ℝ (fderiv ℝ f) (x + s • v) v v - B) hξ.1
    (fun s _ => (hkd s).continuousAt.continuousWithinAt) (fun s _ => hkd s)
  have e1 : g 1 - g 0 = f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * B := by
    simp [hg]; ring
  have e2 : k ξ - k 0 = ξ * (fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B) := by
    rw [sub_zero] at hηe
    have : ξ ≠ 0 := hξ.1.ne'
    field_simp at hηe
    simp only [hk] at hηe ⊢
    simp at hηe ⊢
    linarith
  have e3 : |fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B| ≤ L * ‖v‖ ^ 3 := by
    have : fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B =
        (iteratedFDeriv ℝ 2 f (x + η • v) - iteratedFDeriv ℝ 2 f x) ![v, v] := by
      simp [iteratedFDeriv_two_apply, hBx]
    rw [this, ← Real.norm_eq_abs]
    refine ((ContinuousMultilinearMap.le_opNorm _ _)).trans ?_
    have h5 := hL (x + η • v) x
    have h6 : ‖(x + η • v) - x‖ ≤ ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hη.1]
      nlinarith [norm_nonneg v, hη.2, hξ.2]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc ‖iteratedFDeriv ℝ 2 f (x + η • v) - iteratedFDeriv ℝ 2 f x‖ * (‖v‖ * ‖v‖)
        ≤ (L * ‖v‖) * (‖v‖ * ‖v‖) := by gcongr; exact h5.trans (by gcongr)
      _ = L * ‖v‖ ^ 3 := by ring
  have hgabs : g 1 - g 0 = k ξ - fderiv ℝ f x v := by
    have := hξe
    simp only [sub_zero, div_one] at this
    linarith
  have e4 : g 1 - g 0 = (k ξ - k 0) := by
    rw [hgabs]; simp [hk]
  rw [← e1, e4, e2, abs_mul, abs_of_pos hξ.1]
  calc ξ * |fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B| ≤ 1 * (L * ‖v‖ ^ 3) := by
        gcongr
        · exact hξ.2.le
      _ = _ := one_mul _

end LindebergAux
open LindebergAux

/-- Step 3: second-order Taylor bound with remainder envelope `min(H|v|², L|v|³)`, for
`f ∈ C²` with `‖∇²f‖ ≤ H` and `L`-Lipschitz Hessian. -/
theorem taylor_two_remainder (f : (ℝ^p) → ℝ) (hf : ContDiff ℝ 2 f) (H L : ℝ)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ H)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖)
    (x v : ℝ^p) :
    |f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v]| ≤
      taylorRem H L v := by
  refine le_min ?_ (taylor_L_bound hf hL x v)
  have h1 := taylor_two_bound hf hH x v
  have h2 := abs_iter2_le hH x v
  calc _ ≤ |f (x + v) - f x - fderiv ℝ f x v| + |(1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v]| := by
        have := abs_sub (f (x + v) - f x - fderiv ℝ f x v) ((1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v])
        simpa [sub_sub] using this
    _ ≤ H / 2 * ‖v‖ ^ 2 + (1 / 2) * (H * ‖v‖ ^ 2) := by
        rw [abs_mul]; norm_num; linarith
    _ = H * ‖v‖ ^ 2 := by ring


section
open scoped MatrixOrder
namespace LindebergAux

/-- trace-duality for an invertible matrix (polar decomposition route) -/
lemma trace_dual_of_isUnit (H Q : Matrix (Fin p) (Fin p) ℝ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ u v : Fin p → ℝ, |u ⬝ᵥ (H.mulVec v)| ≤ β * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v))
    (hQ : IsUnit Q.det) :
    |∑ a, ∑ b, H a b * Q a b| ≤ β * traceNormMatrix Q := by
  classical
  set R : Matrix (Fin p) (Fin p) ℝ := CFC.sqrt (Q.transpose * Q) with hR
  have hQQ : (Q.transpose * Q).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self Q
  have hRnn : 0 ≤ R := CFC.sqrt_nonneg _
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.1 hRnn
  have hRR : R * R = Q.transpose * Q := CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.2 hQQ)
  have hRT : R.transpose = R := by
    have := hRpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hRunit : IsUnit R.det := by
    have h1 : (R * R).det = (Q.transpose * Q).det := by rw [hRR]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    have : IsUnit (R.det * R.det) := by rw [h1]; exact hQ.mul hQ
    exact (IsUnit.mul_iff.1 this).1
  set U : Matrix (Fin p) (Fin p) ℝ := Q * R⁻¹ with hU
  have hRiT : (R⁻¹).transpose = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRT]
  have hUU : U.transpose * U = 1 := by
    rw [hU, Matrix.transpose_mul, hRiT]
    calc R⁻¹ * Q.transpose * (Q * R⁻¹) = R⁻¹ * (Q.transpose * Q) * R⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = R⁻¹ * (R * R) * R⁻¹ := by rw [hRR]
      _ = (R⁻¹ * R) * (R * R⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hRunit, Matrix.mul_nonsing_inv _ hRunit, Matrix.mul_one]
  have hUo : U ∈ Matrix.orthogonalGroup (Fin p) ℝ := (Matrix.mem_orthogonalGroup_iff' _ _).2 hUU
  have hQUR : Q = U * R := by
    rw [hU, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRunit, Matrix.mul_one]
  -- the fourth root
  set S : Matrix (Fin p) (Fin p) ℝ := CFC.sqrt R with hS
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)
  have hSS : S * S = R := CFC.sqrt_mul_sqrt_self _ hRnn
  have hST : S.transpose = S := by
    have := hSpsd.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hSsymm : ∀ i j, S i j = S j i := fun i j => by
    have := congrFun (congrFun hST i) j
    simpa using this.symm
  have hQT : Q.transpose = R * U.transpose := by
    calc Q.transpose = (U * R).transpose := by rw [← hQUR]
      _ = R.transpose * U.transpose := Matrix.transpose_mul _ _
      _ = _ := by rw [hRT]
  -- N(Q) ≥ tr R
  have hN : Matrix.trace R ≤ traceNormMatrix Q := by
    have := le_traceNormMatrix Q ⟨U, hUo⟩
    have e : Q.transpose * U = R := by
      rw [hQT, Matrix.mul_assoc, hUU, Matrix.mul_one]
    simpa [e] using this
  have hRtr : Matrix.trace R = ∑ j, ∑ c, S c j * S c j := by
    rw [← hSS]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hSsymm j c]
  -- the sum
  have hsum : ∑ a, ∑ b, H a b * Q a b =
      ∑ j, (U.mulVec (fun c => S c j)) ⬝ᵥ (H.mulVec (fun b => S b j)) := by
    have hQ' : ∀ a b, Q a b = ∑ c, ∑ j, U a c * (S c j * S j b) := by
      intro a b
      rw [hQUR, ← hSS, Matrix.mul_apply]
      simp only [Matrix.mul_apply, Finset.mul_sum]
    simp_rw [hQ', dotProduct, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    -- LHS: ∑ a b c j, H a b * (U a c * (S c j * S j b));  RHS: ∑ j a c b, (U a c * S c j) * (H a b * S b j)
    have e1 : ∀ a b c j, H a b * (U a c * (S c j * S j b)) = (U a c * S c j) * (H a b * S b j) := by
      intro a b c j; rw [hSsymm j b]; ring
    simp_rw [e1]
    -- reorder sums
    calc ∑ a, ∑ b, ∑ c, ∑ j, (U a c * S c j) * (H a b * S b j)
        = ∑ a, ∑ c, ∑ b, ∑ j, (U a c * S c j) * (H a b * S b j) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ c, ∑ j, ∑ b, (U a c * S c j) * (H a b * S b j) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ a, ∑ j, ∑ c, ∑ b, (U a c * S c j) * (H a b * S b j) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ j, ∑ a, ∑ c, ∑ b, (U a c * S c j) * (H a b * S b j) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
  have hterm : ∀ j, |(U.mulVec (fun c => S c j)) ⬝ᵥ (H.mulVec (fun b => S b j))| ≤
      β * ∑ c, S c j * S c j := by
    intro j
    have hUv : (U.mulVec (fun c => S c j)) ⬝ᵥ (U.mulVec (fun c => S c j)) =
        (fun c => S c j) ⬝ᵥ (fun c => S c j) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    have hnn : 0 ≤ (fun c => S c j) ⬝ᵥ (fun c => S c j) := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun c _ => mul_self_nonneg _
    have h1 := hβ (U.mulVec (fun c => S c j)) (fun b => S b j)
    have hq := Real.mul_self_sqrt hnn
    rw [hUv, mul_assoc, hq] at h1
    simpa [dotProduct] using h1
  rw [hsum]
  calc |∑ j, (U.mulVec (fun c => S c j)) ⬝ᵥ (H.mulVec (fun b => S b j))|
      ≤ ∑ j, |(U.mulVec (fun c => S c j)) ⬝ᵥ (H.mulVec (fun b => S b j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, β * ∑ c, S c j * S c j := Finset.sum_le_sum fun j _ => hterm j
    _ = β * Matrix.trace R := by rw [← Finset.mul_sum, hRtr]
    _ ≤ β * traceNormMatrix Q := mul_le_mul_of_nonneg_left hN hβ0

lemma traceNormMatrix_add_le (A B : Matrix (Fin p) (Fin p) ℝ) :
    traceNormMatrix (A + B) ≤ traceNormMatrix A + traceNormMatrix B := by
  unfold traceNormMatrix
  refine ciSup_le fun U => ?_
  have h1 := le_traceNormMatrix A U
  have h2 := le_traceNormMatrix B U
  unfold traceNormMatrix at h1 h2
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]
  exact add_le_add h1 h2

lemma traceNormMatrix_smul_one_le (ε : ℝ) (hε : 0 ≤ ε) :
    traceNormMatrix (ε • (1 : Matrix (Fin p) (Fin p) ℝ)) ≤ ε * p := by
  unfold traceNormMatrix
  refine ciSup_le fun U => ?_
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul]
  have hU : ∀ i, (U : Matrix (Fin p) (Fin p) ℝ) i i ≤ 1 := by
    intro i
    have := entry_norm_bound_of_unitary U.2 i i
    exact (le_abs_self _).trans (by simpa using this)
  have : Matrix.trace (U : Matrix (Fin p) (Fin p) ℝ) ≤ p := by
    simp only [Matrix.trace, Matrix.diag]
    calc ∑ i, (U : Matrix (Fin p) (Fin p) ℝ) i i ≤ ∑ _i : Fin p, (1 : ℝ) := Finset.sum_le_sum fun i _ => hU i
      _ = p := by simp
  exact mul_le_mul_of_nonneg_left this hε

lemma trace_dual (H Q : Matrix (Fin p) (Fin p) ℝ) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ u v : Fin p → ℝ, |u ⬝ᵥ (H.mulVec v)| ≤ β * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v)) :
    |∑ a, ∑ b, H a b * Q a b| ≤ β * traceNormMatrix Q := by
  classical
  have hdiag : ∀ a, |H a a| ≤ β := by
    intro a
    have := hβ (Pi.single a 1) (Pi.single a 1)
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using this
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- choose ε small with Q + ε • 1 invertible
  have hne : Q.charpoly ≠ 0 := (Matrix.charpoly_monic Q).ne_zero
  have hfin : Set.Finite {ε : ℝ | Q.charpoly.IsRoot (-ε)} :=
    (Polynomial.finite_setOfPred_isRoot hne).preimage (neg_injective.injOn)
  set ε0 : ℝ := δ / (2 * (β * p + 1) + 1) with hε0
  have hε0pos : 0 < ε0 := by positivity
  obtain ⟨ε, hε, hεbad⟩ : ∃ ε ∈ Set.Ioo 0 ε0, ε ∉ {ε : ℝ | Q.charpoly.IsRoot (-ε)} := by
    by_contra hcon
    push Not at hcon
    exact (Set.Ioo_infinite hε0pos).not_finite (hfin.subset fun ε hε => hcon ε hε)
  have hdet : IsUnit (Q + ε • (1 : Matrix (Fin p) (Fin p) ℝ)).det := by
    have h1 : Q.charpoly.eval (-ε) ≠ 0 := hεbad
    rw [Matrix.eval_charpoly] at h1
    have h2 : (Matrix.scalar (Fin p) (-ε) - Q) = -(Q + ε • (1 : Matrix (Fin p) (Fin p) ℝ)) := by
      ext i j
      by_cases hij : i = j
      · simp [Matrix.scalar_apply, hij]; ring
      · simp [Matrix.scalar_apply, hij]
    rw [h2, Matrix.det_neg] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => h1 ?_
    rw [h0]; simp
  have key := trace_dual_of_isUnit H (Q + ε • 1) β hβ0 hβ hdet
  have hε1 : 0 ≤ ε := hε.1.le
  have e1 : ∑ a, ∑ b, H a b * (Q + ε • (1 : Matrix (Fin p) (Fin p) ℝ)) a b =
      ∑ a, ∑ b, H a b * Q a b + ε * ∑ a, H a a := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]
  have e2 : |∑ a, H a a| ≤ β * p := by
    calc |∑ a, H a a| ≤ ∑ a, |H a a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin p, β := Finset.sum_le_sum fun a _ => hdiag a
      _ = β * p := by simp [mul_comm]
  have e3 := traceNormMatrix_add_le Q (ε • (1 : Matrix (Fin p) (Fin p) ℝ))
  have e4 := traceNormMatrix_smul_one_le (p := p) ε hε1
  rw [e1] at key
  have e5 : |∑ a, ∑ b, H a b * Q a b| ≤ |∑ a, ∑ b, H a b * Q a b + ε * ∑ a, H a a| + ε * (β * p) := by
    have := abs_sub (∑ a, ∑ b, H a b * Q a b + ε * ∑ a, H a a) (ε * ∑ a, H a a)
    rw [add_sub_cancel_right] at this
    calc _ ≤ _ := this
      _ ≤ _ := by
        gcongr
        rw [abs_mul, abs_of_nonneg hε1]
        exact mul_le_mul_of_nonneg_left e2 hε1
  have hεle : ε ≤ ε0 := hε.2.le
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have e6 : β * (traceNormMatrix Q + ε * p) + ε * (β * p) ≤ β * traceNormMatrix Q + δ := by
    have : ε * (2 * (β * p)) ≤ ε0 * (2 * (β * p + 1) + 1) := by
      have h0 : 0 ≤ 2 * (β * p) := by positivity
      nlinarith [mul_nonneg hβ0 hp]
    have h3 : ε0 * (2 * (β * p + 1) + 1) = δ := by
      rw [hε0]; field_simp
    nlinarith [mul_nonneg hβ0 hp]
  calc _ ≤ _ := e5
    _ ≤ β * traceNormMatrix (Q + ε • 1) + ε * (β * p) := by gcongr
    _ ≤ β * (traceNormMatrix Q + ε * p) + ε * (β * p) := by
        gcongr
        exact e3.trans (add_le_add le_rfl e4)
    _ ≤ _ := e6

lemma cmm_expand (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ^p) ℝ) (x y : ℝ^p) :
    B ![x, y] = ∑ a, ∑ b, x a * y b * B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1] := by
  classical
  have hx : ∀ z : ℝ^p, z = ∑ a, z a • (EuclideanSpace.single a (1 : ℝ) : ℝ^p) := by
    intro z
    have := (EuclideanSpace.basisFun (Fin p) ℝ).sum_repr z
    simpa [EuclideanSpace.basisFun_apply] using this.symm
  have h1 : (![x, y] : Fin 2 → ℝ^p) = fun i => ∑ k, ((![x, y] i) k) • (EuclideanSpace.single k (1 : ℝ) : ℝ^p) := by
    funext i; exact hx _
  rw [h1]
  have := B.toMultilinearMap.map_sum (fun i k => ((![x, y] i) k) • (EuclideanSpace.single k (1 : ℝ) : ℝ^p))
  rw [show ⇑B.toMultilinearMap = ⇑B from rfl] at this
  rw [this]
  simp_rw [ContinuousMultilinearMap.map_smul_univ]
  rw [← Fintype.sum_prod_type' (f := fun a b => x a * y b * B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1])]
  refine Fintype.sum_equiv (finTwoArrowEquiv (Fin p)) _ _ fun r => ?_
  have e : (fun i : Fin 2 => (EuclideanSpace.single (r i) (1 : ℝ) : ℝ^p)) =
      ![EuclideanSpace.single (r 0) 1, EuclideanSpace.single (r 1) 1] := by
    funext i; fin_cases i <;> rfl
  simp [Fin.prod_univ_two, e, finTwoArrowEquiv]


end LindebergAux
end
open LindebergAux

/-- Step 3: trace duality
`|∑_{a,b} ∇²f(x)(e_a, e_b) Q_{ab}| ≤ ‖∇²f(x)‖ ‖Q‖_{S_1}`. -/
theorem hessian_trace_duality (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ^p) ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) :
    |∑ a, ∑ b, B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1] * Q a b| ≤
      ‖B‖ * traceNormMatrix Q := by
  classical
  refine trace_dual (Matrix.of fun a b => B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1])
    Q ‖B‖ (norm_nonneg _) fun u v => ?_
  have hexp := cmm_expand B (WithLp.toLp 2 u) (WithLp.toLp 2 v)
  have hdot : u ⬝ᵥ (Matrix.of fun a b => B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1]).mulVec v =
      B ![WithLp.toLp 2 u, WithLp.toLp 2 v] := by
    rw [hexp]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hdot]
  have hn : ∀ w : Fin p → ℝ, ‖(WithLp.toLp 2 w : ℝ^p)‖ = Real.sqrt (w ⬝ᵥ w) := by
    intro w
    rw [EuclideanSpace.norm_eq]
    simp [dotProduct, sq]
  have := B.le_opNorm ![WithLp.toLp 2 u, WithLp.toLp 2 v]
  rw [Real.norm_eq_abs, Fin.prod_univ_two] at this
  simpa [hn, mul_assoc] using this


/-- Step 3: `‖∫_a^b Q(σ) dσ‖_{S_1} ≤ ∫_a^b ‖Q(σ)‖_{S_1} dσ` (convexity of the trace norm). -/
theorem traceNorm_covBlock_le (Q : ℝ → Matrix (Fin p) (Fin p) ℝ) (a b : ℝ)
    (hQ : ∀ i j, IntegrableOn (fun σ => Q σ i j) (Set.Icc a b))
    (hQn : IntegrableOn (fun σ => traceNormMatrix (Q σ)) (Set.Icc a b)) :
    traceNormMatrix (covBlock Q a b) ≤ ∫ σ in Set.Icc a b, traceNormMatrix (Q σ) := by
  unfold traceNormMatrix
  refine ciSup_le fun U => ?_
  have hU : ∀ M : Matrix (Fin p) (Fin p) ℝ, Matrix.trace (M.transpose * (U : Matrix (Fin p) (Fin p) ℝ)) =
      ∑ i, ∑ j, M j i * (U : Matrix (Fin p) (Fin p) ℝ) j i := by
    intro M
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have h1 : Matrix.trace ((covBlock Q a b).transpose * (U : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ σ in Set.Icc a b, Matrix.trace ((Q σ).transpose * (U : Matrix (Fin p) (Fin p) ℝ)) := by
    simp_rw [hU]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hQ j i).mul_const _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hQ j i).mul_const _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    rfl
  rw [h1]
  refine setIntegral_mono_on ?_ hQn measurableSet_Icc fun σ _ => ?_
  · simp_rw [hU]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hQ j i).mul_const _
  · exact le_traceNormMatrix (Q σ) U


namespace LindebergAux

lemma integral_mul_martingale (ℱ : Filtration ℝ mΩ) {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ P)
    {τ τ' : ℝ} (hττ' : τ ≤ τ') {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ τ] Z)
    (hZ2 : MemLp Z 2 P) (hf2 : MemLp (f τ') 2 P) :
    ∫ ω, Z ω * f τ' ω ∂P = ∫ ω, Z ω * f τ ω ∂P := by
  have hint : Integrable (Z * f τ') P := hZ2.integrable_mul hf2
  calc ∫ ω, Z ω * f τ' ω ∂P = ∫ ω, (P[Z * f τ' | ℱ τ]) ω ∂P :=
        (integral_condExp (ℱ.le τ)).symm
    _ = ∫ ω, (Z * P[f τ' | ℱ τ]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hZ hint (hf.integrable τ'))
    _ = ∫ ω, Z ω * f τ ω ∂P := by
        refine integral_congr_ae ((hf.condExp_ae_eq hττ').mono fun ω h => ?_)
        simp [h]

omit [IsProbabilityMeasure P] in
lemma memLp_coord {X : Ω → ℝ^p} (hX : MemLp X 2 P) (a : Fin p) : MemLp (fun ω => X ω a) 2 P :=
  (EuclideanSpace.proj a : (ℝ^p) →L[ℝ] ℝ).comp_memLp' hX

lemma stronglyMeasurable_coord {m : MeasurableSpace Ω} {X : Ω → ℝ^p} (hX : StronglyMeasurable[m] X)
    (a : Fin p) : StronglyMeasurable[m] (fun ω => X ω a) :=
  (EuclideanSpace.proj a : (ℝ^p) →L[ℝ] ℝ).continuous.comp_stronglyMeasurable hX

end LindebergAux
open LindebergAux

/-- Step 3: orthogonality of martingale increments to square-integrable `ℱ_τ`-measurable
vectors, `E⟨Z, M_{τ'} - M_τ⟩ = 0` for `0 ≤ τ ≤ τ' ≤ t`. -/
theorem martingale_increment_inner (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg) (τ τ' : ℝ) (hτ : 0 ≤ τ)
    (hττ' : τ ≤ τ') (hτ' : τ' ≤ t) (Z : Ω → ℝ^p) (hZ : StronglyMeasurable[ℱ τ] Z)
    (hZ2 : MemLp Z 2 P) :
    ∫ ω, inner ℝ (Z ω) (M τ' ω - M τ ω) ∂P = 0 := by
  have hm1 : MemLp (M τ') 2 P := hM.sq_int τ' ⟨hτ.trans hττ', hτ'⟩
  have hm0 : MemLp (M τ) 2 P := hM.sq_int τ ⟨hτ, hττ'.trans hτ'⟩
  have key : ∀ a : Fin p, ∫ ω, Z ω a * (M τ' ω a - M τ ω a) ∂P = 0 := by
    intro a
    have hZa := memLp_coord P hZ2 a
    have h1 := memLp_coord P hm1 a
    have h0 := memLp_coord P hm0 a
    have e := integral_mul_martingale P ℱ (hM.martingale a) hττ'
      (stronglyMeasurable_coord hZ a) hZa h1
    have i1 : Integrable (fun ω => Z ω a * M τ' ω a) P := hZa.integrable_mul h1
    have i0 : Integrable (fun ω => Z ω a * M τ ω a) P := hZa.integrable_mul h0
    simp_rw [mul_sub]
    rw [integral_sub i1 i0, e, sub_self]
  have hin : ∀ ω, inner ℝ (Z ω) (M τ' ω - M τ ω) = ∑ a, Z ω a * (M τ' ω a - M τ ω a) := by
    intro ω
    simp [PiLp.inner_apply, mul_comm]
  simp_rw [hin]
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun a _ => key a
  · intro a _
    have hZa := memLp_coord P hZ2 a
    have h1 := memLp_coord P hm1 a
    have h0 := memLp_coord P hm0 a
    have i1 : Integrable (fun ω => Z ω a * M τ' ω a) P := hZa.integrable_mul h1
    have i0 : Integrable (fun ω => Z ω a * M τ ω a) P := hZa.integrable_mul h0
    simp_rw [mul_sub]
    exact i1.sub i0


namespace LindebergAux

lemma setInt_Icc_diff {f : ℝ → ℝ} {t τ τ' : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ τ') (h2 : τ' ≤ t)
    (hf : IntegrableOn f (Set.Icc 0 t)) :
    (∫ σ in Set.Icc 0 τ', f σ) - ∫ σ in Set.Icc 0 τ, f σ = ∫ σ in Set.Icc τ τ', f σ := by
  have i1 : IntervalIntegrable f volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h0]
    exact hf.mono_set (Set.Icc_subset_Icc le_rfl (h1.trans h2))
  have i2 : IntervalIntegrable f volume τ τ' := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h1]
    exact hf.mono_set (Set.Icc_subset_Icc h0 h2)
  have i3 : IntervalIntegrable f volume 0 τ' := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (h0.trans h1)]
    exact hf.mono_set (Set.Icc_subset_Icc le_rfl h2)
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0,
    ← intervalIntegral.integral_of_le h1, ← intervalIntegral.integral_of_le (h0.trans h1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  ring

end LindebergAux

namespace LindebergAux

omit [IsProbabilityMeasure P] in
lemma integrable_bdd_mul {z g : Ω → ℝ} (hz : AEStronglyMeasurable z P) {K : ℝ}
    (hK : ∀ ω, |z ω| ≤ K) (hg : Integrable g P) : Integrable (fun ω => z ω * g ω) P := by
  refine (hg.norm.const_mul K).mono' (hz.mul hg.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hK ω) (norm_nonneg _)

lemma integral_bdd_mul_martingale (ℱ : Filtration ℝ mΩ) {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ P)
    {τ τ' : ℝ} (hττ' : τ ≤ τ') {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ τ] Z) {K : ℝ}
    (hK : ∀ ω, |Z ω| ≤ K) :
    ∫ ω, Z ω * f τ' ω ∂P = ∫ ω, Z ω * f τ ω ∂P := by
  have hZ' : StronglyMeasurable Z := hZ.mono (ℱ.le τ)
  have hint : Integrable (Z * f τ') P := integrable_bdd_mul P hZ'.aestronglyMeasurable hK (hf.integrable τ')
  calc ∫ ω, Z ω * f τ' ω ∂P = ∫ ω, (P[Z * f τ' | ℱ τ]) ω ∂P :=
        (integral_condExp (ℱ.le τ)).symm
    _ = ∫ ω, (Z * P[f τ' | ℱ τ]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hZ hint (hf.integrable τ'))
    _ = ∫ ω, Z ω * f τ ω ∂P := by
        refine integral_congr_ae ((hf.condExp_ae_eq hττ').mono fun ω h => ?_)
        simp [h]

lemma cov_pair (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg) (τ τ' : ℝ) (hτ : 0 ≤ τ)
    (hττ' : τ ≤ τ') (hτ' : τ' ≤ t) (z : Ω → ℝ) (hz : StronglyMeasurable[ℱ τ] z) (K : ℝ)
    (hzK : ∀ ω, |z ω| ≤ K) (a b : Fin p) :
    Integrable (fun ω => z ω * ((M τ' ω - M τ ω) a * (M τ' ω - M τ ω) b)) P ∧
    Integrable (fun ω => z ω * (∫ σ in Set.Icc τ τ', Sg σ ω a b)) P ∧
    ∫ ω, z ω * ((M τ' ω - M τ ω) a * (M τ' ω - M τ ω) b) ∂P =
      ∫ ω, z ω * (∫ σ in Set.Icc τ τ', Sg σ ω a b) ∂P := by
  have hm1 : MemLp (M τ') 2 P := hM.sq_int τ' ⟨hτ.trans hττ', hτ'⟩
  have hm0 : MemLp (M τ) 2 P := hM.sq_int τ ⟨hτ, hττ'.trans hτ'⟩
  have hz' : StronglyMeasurable z := hz.mono (ℱ.le τ)
  have hzm : AEStronglyMeasurable z P := hz'.aestronglyMeasurable
  have c1 := memLp_coord P hm1
  have c0 := memLp_coord P hm0
  set A : ℝ → Ω → ℝ := fun s ω => ∫ σ in Set.Icc 0 s, Sg σ ω a b with hA
  set N : ℝ → Ω → ℝ := fun s ω => M s ω a * M s ω b - A s ω with hN
  have iN : ∀ s, Integrable (N s) P := fun s => (hM.covariation a b).integrable s
  have iA : ∀ s, MemLp (M s) 2 P → Integrable (A s) P := by
    intro s hs
    have hprod : Integrable (fun ω => M s ω a * M s ω b) P := (memLp_coord P hs a).integrable_mul (memLp_coord P hs b)
    have : A s = fun ω => (M s ω a * M s ω b) - N s ω := by funext ω; simp [hN]
    rw [this]; exact hprod.sub (iN s)
  have iA1 := iA τ' hm1
  have iA0 := iA τ hm0
  -- the pathwise increment
  have hD : (fun ω => ∫ σ in Set.Icc τ τ', Sg σ ω a b) =ᵐ[P] fun ω => A τ' ω - A τ ω := by
    filter_upwards [hM.sigma_entry_int] with ω hω
    exact (setInt_Icc_diff hτ hττ' hτ' (hω a b)).symm
  -- pieces
  set T1 : Ω → ℝ := fun ω => z ω * (N τ' ω - N τ ω) with hT1
  set T2 : Ω → ℝ := fun ω => z ω * (A τ' ω - A τ ω) with hT2
  set T3 : Ω → ℝ := fun ω => (z ω * M τ ω a) * (M τ' ω b - M τ ω b) with hT3
  set T4 : Ω → ℝ := fun ω => (z ω * M τ ω b) * (M τ' ω a - M τ ω a) with hT4
  have iT1 : Integrable T1 P := integrable_bdd_mul P hzm hzK ((iN τ').sub (iN τ))
  have iT2 : Integrable T2 P := integrable_bdd_mul P hzm hzK (iA1.sub iA0)
  have hW : ∀ c : Fin p, MemLp (fun ω => z ω * M τ ω c) 2 P := by
    intro c
    refine MemLp.of_le_mul (c := K) (c0 c) (hzm.mul (c0 c).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hzK ω) (norm_nonneg _)
  have iT3 : Integrable T3 P := (hW a).integrable_mul ((c1 b).sub (c0 b))
  have iT4 : Integrable T4 P := (hW b).integrable_mul ((c1 a).sub (c0 a))
  have e1 : ∫ ω, T1 ω ∂P = 0 := by
    have := integral_bdd_mul_martingale P ℱ (hM.covariation a b) hττ' hz hzK
    simp only [hT1, mul_sub]
    rw [integral_sub (integrable_bdd_mul P hzm hzK (iN τ')) (integrable_bdd_mul P hzm hzK (iN τ))]
    simp only [hN] at this ⊢
    rw [this, sub_self]
  have wm : ∀ c : Fin p, StronglyMeasurable[ℱ τ] (fun ω => z ω * M τ ω c) := fun c =>
    hz.mul ((hM.martingale c).1 τ)
  have e3 : ∫ ω, T3 ω ∂P = 0 := by
    have := integral_mul_martingale P ℱ (hM.martingale b) hττ' (wm a) (hW a) (c1 b)
    have i1 : Integrable (fun ω => (z ω * M τ ω a) * M τ' ω b) P := (hW a).integrable_mul (c1 b)
    have i0 : Integrable (fun ω => (z ω * M τ ω a) * M τ ω b) P := (hW a).integrable_mul (c0 b)
    simp only [hT3, mul_sub]
    rw [integral_sub i1 i0, this, sub_self]
  have e4 : ∫ ω, T4 ω ∂P = 0 := by
    have := integral_mul_martingale P ℱ (hM.martingale a) hττ' (wm b) (hW b) (c1 a)
    have i1 : Integrable (fun ω => (z ω * M τ ω b) * M τ' ω a) P := (hW b).integrable_mul (c1 a)
    have i0 : Integrable (fun ω => (z ω * M τ ω b) * M τ ω a) P := (hW b).integrable_mul (c0 a)
    simp only [hT4, mul_sub]
    rw [integral_sub i1 i0, this, sub_self]
  have hF : (fun ω => z ω * ((M τ' ω - M τ ω) a * (M τ' ω - M τ ω) b)) =
      fun ω => T1 ω + T2 ω - T3 ω - T4 ω := by
    funext ω
    simp only [hT1, hT2, hT3, hT4, hN, PiLp.sub_apply]
    ring
  have hG : (fun ω => z ω * (∫ σ in Set.Icc τ τ', Sg σ ω a b)) =ᵐ[P] T2 :=
    hD.mono fun ω h => by simp only [hT2, h]
  refine ⟨?_, iT2.congr hG.symm, ?_⟩
  · rw [hF]; exact ((iT1.add iT2).sub iT3).sub iT4
  · have j1 : Integrable (fun ω => T1 ω + T2 ω) P := iT1.add iT2
    have j2 : Integrable (fun ω => T1 ω + T2 ω - T3 ω) P := j1.sub iT3
    rw [hF, integral_sub j2 iT4, integral_sub j1 iT3, integral_add iT1 iT2, e1, e3, e4,
      integral_congr_ae hG]
    ring

end LindebergAux

/-- Step 3: the covariation identity for increments: for bounded `ℱ_τ`-measurable matrices
`Z`, `E ∑_{a,b} Z_{ab} ΔM^a ΔM^b = E ∑_{a,b} Z_{ab} ∫_τ^{τ'} Σ^{ab}`. -/
theorem martingale_increment_covariation (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg) (τ τ' : ℝ) (hτ : 0 ≤ τ)
    (hττ' : τ ≤ τ') (hτ' : τ' ≤ t) (Z : Ω → Matrix (Fin p) (Fin p) ℝ)
    (hZ : ∀ a b, StronglyMeasurable[ℱ τ] fun ω => Z ω a b) (K : ℝ)
    (hZK : ∀ ω a b, |Z ω a b| ≤ K) :
    ∫ ω, ∑ a, ∑ b, Z ω a b * ((M τ' ω - M τ ω) a * (M τ' ω - M τ ω) b) ∂P =
      ∫ ω, ∑ a, ∑ b, Z ω a b * (∫ σ in Set.Icc τ τ', Sg σ ω a b) ∂P := by
  have hp := fun a b => cov_pair P ℱ t M Sg hM τ τ' hτ hττ' hτ' (fun ω => Z ω a b) (hZ a b) K
    (fun ω => hZK ω a b) a b
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hp a b).1),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hp a b).2.1)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (hp a b).1), integral_finsetSum _ (fun b _ => (hp a b).2.1)]
  exact Finset.sum_congr rfl fun b _ => (hp a b).2.2


section LindebergDiscrete
set_option linter.unusedSectionVars false
namespace LindebergAux

/-- Discrete-time square-integrable vector martingale data on indices `0..n`: adapted to the
increasing σ-algebras `G`, square integrable, with orthogonal increments. -/
structure DM (n : ℕ) (G : ℕ → MeasurableSpace Ω) (M : ℕ → Ω → ℝ^p) : Prop where
  mono : Monotone G
  le : ∀ k, G k ≤ mΩ
  meas : ∀ k ≤ n, StronglyMeasurable[G k] (M k)
  memLp : ∀ k ≤ n, MemLp (M k) 2 P
  orth : ∀ k < n, ∀ Z : Ω → ℝ^p, StronglyMeasurable[G k] Z → MemLp Z 2 P →
    ∫ ω, inner ℝ (Z ω) (M (k + 1) ω - M k ω) ∂P = 0

omit [IsProbabilityMeasure P] in
lemma integrable_inner_of_memLp {f g : Ω → ℝ^p} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => inner ℝ (f ω) (g ω)) P := by
  have h := hf.norm.integrable_mul hg.norm
  refine Integrable.mono' h (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  simpa using norm_inner_le_norm (𝕜 := ℝ) (f ω) (g ω)

variable {n : ℕ} {G : ℕ → MeasurableSpace Ω} {M : ℕ → Ω → ℝ^p}

omit [IsProbabilityMeasure P] in
lemma DM.integrable_sq (hM : DM P n G M) {k : ℕ} (hk : k ≤ n) :
    Integrable (fun ω => ‖M k ω‖ ^ 2) P :=
  (hM.memLp k hk).integrable_norm_pow (by norm_num)

omit [IsProbabilityMeasure P] in
lemma DM.integrable_incr_sq (hM : DM P n G M) {k : ℕ} (hk : k < n) :
    Integrable (fun ω => ‖M (k + 1) ω - M k ω‖ ^ 2) P :=
  ((hM.memLp (k + 1) hk).sub (hM.memLp k hk.le)).integrable_norm_pow (by norm_num)

omit [IsProbabilityMeasure P] in
/-- bounded `G k`-measurable weights. -/
lemma DM.integral_weight_incr (hM : DM P n G M) {k : ℕ} (hk : k < n) {w : Ω → ℝ}
    (hw : StronglyMeasurable[G k] w) {B : ℝ} (hwB : ∀ ω, |w ω| ≤ B) :
    ∫ ω, w ω * ‖M (k + 1) ω - M k ω‖ ^ 2 ∂P =
      ∫ ω, w ω * (‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2) ∂P := by
  have hw' : StronglyMeasurable w := hw.mono (hM.le k)
  have hwm : AEStronglyMeasurable w P := hw'.aestronglyMeasurable
  have hZ : StronglyMeasurable[G k] (fun ω => w ω • M k ω) := hw.smul (hM.meas k hk.le)
  have hZ2 : MemLp (fun ω => w ω • M k ω) 2 P := by
    refine MemLp.of_le_mul (c := B) ((hM.memLp k hk.le)) (hZ.mono (hM.le k)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hwB ω) (norm_nonneg _)
  have h0 := hM.orth k hk _ hZ hZ2
  have i1 : Integrable (fun ω => w ω * ‖M (k + 1) ω‖ ^ 2) P :=
    (hM.integrable_sq P (by omega)).bdd_mul hwm (ae_of_all _ fun ω => by simpa using hwB ω)
  have i0 : Integrable (fun ω => w ω * ‖M k ω‖ ^ 2) P :=
    (hM.integrable_sq P hk.le).bdd_mul hwm (ae_of_all _ fun ω => by simpa using hwB ω)
  have i2 : Integrable (fun ω => w ω * ‖M (k + 1) ω - M k ω‖ ^ 2) P :=
    (hM.integrable_incr_sq P hk).bdd_mul hwm (ae_of_all _ fun ω => by simpa using hwB ω)
  have i3 : Integrable (fun ω => inner ℝ (w ω • M k ω) (M (k + 1) ω - M k ω)) P := by
    exact integrable_inner_of_memLp P hZ2 ((hM.memLp (k + 1) hk).sub (hM.memLp k hk.le))
  have key : ∀ ω, w ω * ‖M (k + 1) ω - M k ω‖ ^ 2 =
      w ω * (‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2) -
        2 * inner ℝ (w ω • M k ω) (M (k + 1) ω - M k ω) := by
    intro ω
    have h1 : M (k + 1) ω = M k ω + (M (k + 1) ω - M k ω) := by abel
    have h2 : ‖M (k + 1) ω‖ ^ 2 = ‖M k ω‖ ^ 2 + 2 * inner ℝ (M k ω) (M (k + 1) ω - M k ω) +
        ‖M (k + 1) ω - M k ω‖ ^ 2 := by
      conv_lhs => rw [h1]
      exact norm_add_sq_real _ _
    rw [real_inner_smul_left, h2]; ring
  simp_rw [key]
  rw [integral_sub (i1.sub i0 |>.congr (ae_of_all _ fun ω => by simp [mul_sub])) (i3.const_mul 2),
    integral_const_mul, h0]
  simp

omit [IsProbabilityMeasure P] in
lemma DM.integrable_weight_sq (hM : DM P n G M) {k : ℕ} (hk : k ≤ n) {w : Ω → ℝ}
    (hw : StronglyMeasurable w) {B : ℝ} (hwB : ∀ ω, |w ω| ≤ B) :
    Integrable (fun ω => w ω * ‖M k ω‖ ^ 2) P :=
  (hM.integrable_sq P hk).bdd_mul hw.aestronglyMeasurable (ae_of_all _ fun ω => by simpa using hwB ω)

omit [IsProbabilityMeasure P] in
lemma DM.integral_weight_mono (hM : DM P n G M) {j : ℕ} (hj : j ≤ n) {w : Ω → ℝ}
    (hw : StronglyMeasurable[G j] w) (hw0 : ∀ ω, 0 ≤ w ω) {B : ℝ} (hwB : ∀ ω, w ω ≤ B) :
    ∫ ω, w ω * ‖M j ω‖ ^ 2 ∂P ≤ ∫ ω, w ω * ‖M n ω‖ ^ 2 ∂P := by
  have hwB' : ∀ ω, |w ω| ≤ B := fun ω => by rw [abs_of_nonneg (hw0 ω)]; exact hwB ω
  have hw' : StronglyMeasurable w := hw.mono (hM.le j)
  have : ∀ k, j ≤ k → k ≤ n → ∫ ω, w ω * ‖M j ω‖ ^ 2 ∂P ≤ ∫ ω, w ω * ‖M k ω‖ ^ 2 ∂P := by
    intro k hjk
    induction k, hjk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hjk ih =>
      intro hk1
      have hk : k < n := hk1
      refine (ih hk.le).trans ?_
      have hwk : StronglyMeasurable[G k] w := hw.mono (hM.mono hjk)
      have e := hM.integral_weight_incr P hk hwk hwB'
      have hnn : 0 ≤ ∫ ω, w ω * ‖M (k + 1) ω - M k ω‖ ^ 2 ∂P :=
        integral_nonneg fun ω => mul_nonneg (hw0 ω) (by positivity)
      rw [e] at hnn
      have i1 := hM.integrable_weight_sq P hk1 hw' hwB'
      have i0 := hM.integrable_weight_sq P hk.le hw' hwB'
      have : ∫ ω, w ω * (‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2) ∂P =
          ∫ ω, w ω * ‖M (k + 1) ω‖ ^ 2 ∂P - ∫ ω, w ω * ‖M k ω‖ ^ 2 ∂P := by
        rw [← integral_sub i1 i0]; congr 1; ext ω; ring
      linarith
  exact this n hj le_rfl


open scoped Classical in
/-- The first grid index (capped at `n`) at which `‖M i‖ ≥ R`. -/
noncomputable def stopIdx (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (ω : Ω) : ℕ :=
  Nat.find (⟨n, Or.inl le_rfl⟩ : ∃ i, n ≤ i ∨ R ≤ ‖M i ω‖)

lemma stopIdx_le (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (ω : Ω) : stopIdx n R M ω ≤ n := by
  classical
  unfold stopIdx
  convert Nat.find_min' (⟨n, Or.inl le_rfl⟩ : ∃ i, n ≤ i ∨ R ≤ ‖M i ω‖) (Or.inl le_rfl)

lemma lt_stopIdx_iff (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (ω : Ω) (k : ℕ) :
    k < stopIdx n R M ω ↔ ∀ i ≤ k, i < n ∧ ‖M i ω‖ < R := by
  classical
  unfold stopIdx
  rw [Nat.lt_find_iff]
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  simp [not_or]

lemma le_norm_stopIdx (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (ω : Ω) (h : stopIdx n R M ω < n) :
    R ≤ ‖M (stopIdx n R M ω) ω‖ := by
  classical
  have := Nat.find_spec (⟨n, Or.inl le_rfl⟩ : ∃ i, n ≤ i ∨ R ≤ ‖M i ω‖)
  unfold stopIdx at h ⊢
  rcases this with h1 | h1
  · exact absurd h (not_lt.2 (by convert h1))
  · convert h1


omit [IsProbabilityMeasure P] in
lemma DM.measurableSet_lt_stopIdx (hM : DM P n G M) (R : ℝ) (j : ℕ) :
    MeasurableSet[G j] {ω | j < stopIdx n R M ω} := by
  by_cases hj : j < n
  · have : {ω | j < stopIdx n R M ω} = ⋂ i ∈ Finset.range (j + 1), {ω | ‖M i ω‖ < R} := by
      ext ω
      simp only [Set.mem_ofPred_eq, lt_stopIdx_iff, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
      exact ⟨fun h i hi => (h i hi).2, fun h i hi => ⟨by omega, h i hi⟩⟩
    rw [this]
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 : StronglyMeasurable[G j] (M i) := (hM.meas i (by omega)).mono (hM.mono hij)
    exact h1.norm.measurable measurableSet_Iio
  · have : {ω | j < stopIdx n R M ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (stopIdx_le n R M ω).trans (not_lt.1 hj)
    rw [this]; exact @MeasurableSet.empty Ω (G j)

omit [IsProbabilityMeasure P] in
lemma DM.measurableSet_eq_stopIdx (hM : DM P n G M) (R : ℝ) (j : ℕ) :
    MeasurableSet[G j] {ω | stopIdx n R M ω = j} := by
  cases j with
  | zero =>
    have : {ω | stopIdx n R M ω = 0} = {ω | 0 < stopIdx n R M ω}ᶜ := by
      ext ω; simp [Nat.pos_iff_ne_zero]
    rw [this]; exact (hM.measurableSet_lt_stopIdx P R 0).compl
  | succ i =>
    have : {ω | stopIdx n R M ω = i + 1} =
        {ω | i < stopIdx n R M ω} \ {ω | i + 1 < stopIdx n R M ω} := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_sdiff]; omega
    rw [this]
    exact ((hM.mono (Nat.le_succ i)) _ (hM.measurableSet_lt_stopIdx P R i)).diff
      (hM.measurableSet_lt_stopIdx P R (i + 1))


omit [IsProbabilityMeasure P] in
/-- the weight `1_{m = j} W(‖M_j‖²)`. -/
lemma DM.stronglyMeasurable_stopWeight (hM : DM P n G M) (R : ℝ) {W : ℝ → ℝ} (hW : Measurable W)
    (j : ℕ) (hj : j ≤ n) :
    StronglyMeasurable[G j] ({ω | stopIdx n R M ω = j}.indicator (fun ω => W (‖M j ω‖ ^ 2))) := by
  refine StronglyMeasurable.indicator ?_ (hM.measurableSet_eq_stopIdx P R j)
  have h1 : StronglyMeasurable[G j] (fun ω => ‖M j ω‖ ^ 2) := (hM.meas j hj).norm.pow 2
  exact (hW.comp h1.measurable).stronglyMeasurable

lemma DM.stopped_ineq (hM : DM P n G M) (R : ℝ) {W : ℝ → ℝ} (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (hW1 : ∀ x, W x ≤ 1) :
    Integrable (fun ω => W (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M (stopIdx n R M ω) ω‖ ^ 2) P ∧
    Integrable (fun ω => W (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2) P ∧
    ∫ ω, W (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M (stopIdx n R M ω) ω‖ ^ 2 ∂P ≤
      ∫ ω, W (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 ∂P := by
  set w : ℕ → Ω → ℝ := fun j => {ω | stopIdx n R M ω = j}.indicator (fun ω => W (‖M j ω‖ ^ 2))
    with hw
  have hwm : ∀ j ≤ n, StronglyMeasurable[G j] (w j) := fun j hj =>
    hM.stronglyMeasurable_stopWeight P R hW j hj
  have hw0 : ∀ j ω, 0 ≤ w j ω := fun j ω => by
    simp only [hw]; exact Set.indicator_nonneg (fun _ _ => hW0 _) ω
  have hw1 : ∀ j ω, w j ω ≤ 1 := fun j ω => by
    simp only [hw]
    by_cases h : ω ∈ {ω | stopIdx n R M ω = j}
    · rw [Set.indicator_of_mem h]; exact hW1 _
    · rw [Set.indicator_of_notMem h]; exact zero_le_one
  have hid1 : ∀ ω, W (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M (stopIdx n R M ω) ω‖ ^ 2 =
      ∑ j ∈ Finset.range (n + 1), w j ω * ‖M j ω‖ ^ 2 := by
    intro ω
    rw [Finset.sum_eq_single (stopIdx n R M ω)]
    · simp [hw]
    · intro j _ hne
      simp [hw, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (stopIdx_le n R M ω))) h
  have hid2 : ∀ ω, W (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 =
      ∑ j ∈ Finset.range (n + 1), w j ω * ‖M n ω‖ ^ 2 := by
    intro ω
    rw [Finset.sum_eq_single (stopIdx n R M ω)]
    · simp [hw]
    · intro j _ hne
      simp [hw, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (stopIdx_le n R M ω))) h
  simp_rw [hid1, hid2]
  have hB : ∀ j ω, |w j ω| ≤ 1 := fun j ω => by rw [abs_of_nonneg (hw0 j ω)]; exact hw1 j ω
  refine ⟨integrable_finsetSum _ (fun j hj => hM.integrable_weight_sq P (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      ((hwm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).mono (hM.le j)) (hB j)),
    integrable_finsetSum _ (fun j hj => hM.integrable_weight_sq P le_rfl
      ((hwm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).mono (hM.le j)) (hB j)), ?_⟩
  rw [integral_finsetSum _ (fun j hj => hM.integrable_weight_sq P (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      ((hwm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).mono (hM.le j)) (hB j)),
    integral_finsetSum _ (fun j hj => hM.integrable_weight_sq P le_rfl
      ((hwm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).mono (hM.le j)) (hB j))]
  exact Finset.sum_le_sum fun j hj =>
    hM.integral_weight_mono P (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (hwm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (hw0 j) (hw1 j)


lemma sum_ite_lt_eq (f : ℕ → ℝ) {m n : ℕ} (hm : m ≤ n) :
    ∑ k ∈ Finset.range n, (if k < m then f k else 0) = ∑ k ∈ Finset.range m, f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum_ite_lt_telescope (b : ℕ → ℝ) {m n : ℕ} (hm : m ≤ n) :
    ∑ k ∈ Finset.range n, (if k < m then b (k + 1) - b k else 0) = b m - b 0 := by
  rw [sum_ite_lt_eq _ hm, Finset.sum_range_sub (fun k => b k)]

lemma sum_ite_ge_telescope (b : ℕ → ℝ) {m n : ℕ} (hm : m ≤ n) :
    ∑ k ∈ Finset.range n, (if m ≤ k then b (k + 1) - b k else 0) = b n - b m := by
  have h1 := Finset.sum_range_sub (fun k => b k) n
  have h2 := sum_ite_lt_telescope b hm
  have h3 : ∀ k, (if m ≤ k then b (k + 1) - b k else (0:ℝ)) =
      (b (k + 1) - b k) - (if k < m then b (k + 1) - b k else 0) := by
    intro k; split_ifs <;> first | omega | simp
  simp_rw [h3]
  rw [Finset.sum_sub_distrib, h1, h2]; ring


omit [IsProbabilityMeasure P] in
lemma integrable_ite_of_meas {f : Ω → ℝ} (hf : Integrable f P) {q : Ω → Prop} [DecidablePred q]
    (hS : MeasurableSet {ω | q ω}) : Integrable (fun ω => if q ω then f ω else 0) P := by
  convert hf.indicator hS using 1
  ext ω
  by_cases h : q ω <;> simp [Set.indicator, h]

omit [IsProbabilityMeasure P] in
lemma DM.integral_ite_incr (hM : DM P n G M) {k : ℕ} (hk : k < n) {q : Ω → Prop}
    [DecidablePred q] (hS : MeasurableSet[G k] {ω | q ω}) :
    ∫ ω, (if q ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) ∂P =
      ∫ ω, (if q ω then ‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2 else 0) ∂P := by
  have hw : StronglyMeasurable[G k] ({ω | q ω}.indicator (fun _ => (1 : ℝ))) :=
    (@stronglyMeasurable_const _ _ (G k) _ _).indicator hS
  have hB : ∀ ω, |{ω | q ω}.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
    by_cases h : q ω <;> simp [Set.indicator, h]
  have := hM.integral_weight_incr P hk hw hB
  convert this using 2 <;> (ext ω; by_cases h : q ω <;> simp [Set.indicator, h])

lemma DM.energy_pre (hM : DM P n G M) (R : ℝ) :
    ∑ k ∈ Finset.range n, ∫ ω, (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) ∂P =
      ∫ ω, (‖M (stopIdx n R M ω) ω‖ ^ 2 - ‖M 0 ω‖ ^ 2) ∂P := by
  have hS : ∀ k, MeasurableSet {ω | k < stopIdx n R M ω} := fun k =>
    hM.le k _ (hM.measurableSet_lt_stopIdx P R k)
  have h1 : ∀ k ∈ Finset.range n, ∫ ω, (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) ∂P =
      ∫ ω, (if k < stopIdx n R M ω then ‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2 else 0) ∂P := by
    intro k hk
    exact hM.integral_ite_incr P (Finset.mem_range.1 hk) (hM.measurableSet_lt_stopIdx P R k)
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum]
  · congr 1
    ext ω
    exact sum_ite_lt_telescope (fun k => ‖M k ω‖ ^ 2) (stopIdx_le n R M ω)
  · intro k hk
    exact integrable_ite_of_meas P ((hM.integrable_sq P (Nat.succ_le_of_lt (Finset.mem_range.1 hk))).sub
      (hM.integrable_sq P (Finset.mem_range.1 hk).le)) (hS k)

lemma DM.energy_post (hM : DM P n G M) (R : ℝ) :
    ∑ k ∈ Finset.range n, ∫ ω, (if stopIdx n R M ω ≤ k then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) ∂P =
      ∫ ω, (‖M n ω‖ ^ 2 - ‖M (stopIdx n R M ω) ω‖ ^ 2) ∂P := by
  have hS : ∀ k, MeasurableSet[G k] {ω | stopIdx n R M ω ≤ k} := fun k => by
    have := (hM.measurableSet_lt_stopIdx P R k).compl
    convert this using 1
    ext ω; simp
  have hS' : ∀ k, MeasurableSet {ω | stopIdx n R M ω ≤ k} := fun k => hM.le k _ (hS k)
  have h1 : ∀ k ∈ Finset.range n, ∫ ω, (if stopIdx n R M ω ≤ k then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) ∂P =
      ∫ ω, (if stopIdx n R M ω ≤ k then ‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2 else 0) ∂P := by
    intro k hk
    exact hM.integral_ite_incr P (Finset.mem_range.1 hk) (hS k)
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum]
  · congr 1
    ext ω
    exact sum_ite_ge_telescope (fun k => ‖M k ω‖ ^ 2) (stopIdx_le n R M ω)
  · intro k hk
    exact integrable_ite_of_meas P ((hM.integrable_sq P (Nat.succ_le_of_lt (Finset.mem_range.1 hk))).sub
      (hM.integrable_sq P (Finset.mem_range.1 hk).le)) (hS' k)


/-- the stopped increments `1_{k < m} ⟨M_k, ΔM_k⟩`. -/
noncomputable def stopInner (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (k : ℕ) (ω : Ω) : ℝ :=
  if k < stopIdx n R M ω then inner ℝ (M k ω) (M (k + 1) ω - M k ω) else 0

/-- the stopped martingale transform `∑_{k<j} 1_{k < m} ⟨M_k, ΔM_k⟩`. -/
noncomputable def stopJ (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (j : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range j, stopInner n R M k ω

lemma stopInner_bound {R : ℝ} (hR : 0 ≤ R) (k : ℕ) (ω : Ω) :
    |stopInner n R M k ω| ≤ R * ‖M (k + 1) ω - M k ω‖ := by
  unfold stopInner
  split_ifs with h
  · have h1 : ‖M k ω‖ < R := ((lt_stopIdx_iff n R M ω k).1 h k le_rfl).2
    calc |inner ℝ (M k ω) (M (k + 1) ω - M k ω)| ≤ ‖M k ω‖ * ‖M (k + 1) ω - M k ω‖ := by
          simpa using abs_real_inner_le_norm (M k ω) (M (k + 1) ω - M k ω)
      _ ≤ R * ‖M (k + 1) ω - M k ω‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
  · simpa using mul_nonneg hR (norm_nonneg _)

lemma stopInner_sq_le {R : ℝ} (k : ℕ) (ω : Ω) :
    stopInner n R M k ω ^ 2 ≤
      R ^ 2 * (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) := by
  unfold stopInner
  split_ifs with h
  · have h1 : ‖M k ω‖ < R := ((lt_stopIdx_iff n R M ω k).1 h k le_rfl).2
    have : |inner ℝ (M k ω) (M (k + 1) ω - M k ω)| ≤ R * ‖M (k + 1) ω - M k ω‖ := by
      calc |inner ℝ (M k ω) (M (k + 1) ω - M k ω)| ≤ ‖M k ω‖ * ‖M (k + 1) ω - M k ω‖ := by
            simpa using abs_real_inner_le_norm (M k ω) (M (k + 1) ω - M k ω)
        _ ≤ R * ‖M (k + 1) ω - M k ω‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
    calc inner ℝ (M k ω) (M (k + 1) ω - M k ω) ^ 2 = |inner ℝ (M k ω) (M (k + 1) ω - M k ω)| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (R * ‖M (k + 1) ω - M k ω‖) ^ 2 := by gcongr
      _ = _ := by ring
  · simp


omit [IsProbabilityMeasure P] in
lemma DM.stopJ_facts (hM : DM P n G M) {R : ℝ} (hR : 0 ≤ R) :
    ∀ j, j ≤ n → StronglyMeasurable[G j] (stopJ n R M j) ∧ MemLp (stopJ n R M j) 2 P ∧
      ∫ ω, stopJ n R M j ω ^ 2 ∂P ≤ R ^ 2 * ∑ k ∈ Finset.range j,
        ∫ ω, (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) ∂P := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : stopJ n R M 0 = fun _ => 0 := by funext ω; simp [stopJ]
    rw [h0]
    refine ⟨@stronglyMeasurable_const _ _ (G 0) _ _, MemLp.zero, by simp⟩
  | succ j ih =>
    intro hj
    have hjn : j < n := hj
    obtain ⟨hJm, hJL, hJint⟩ := ih hjn.le
    have hS : MeasurableSet[G j] {ω | j < stopIdx n R M ω} := hM.measurableSet_lt_stopIdx P R j
    have hMj1 : StronglyMeasurable[G (j + 1)] (M j) :=
      (hM.meas j hjn.le).mono (hM.mono (Nat.le_succ j))
    have hXm : StronglyMeasurable[G (j + 1)] (stopInner n R M j) := by
      have e : stopInner n R M j = {ω | j < stopIdx n R M ω}.indicator
          (fun ω => inner ℝ (M j ω) (M (j + 1) ω - M j ω)) := by
        funext ω; by_cases h : j < stopIdx n R M ω <;> simp [stopInner, Set.indicator, h]
      rw [e]
      exact StronglyMeasurable.indicator (hMj1.inner ((hM.meas (j + 1) hj).sub hMj1))
        (hM.mono (Nat.le_succ j) _ hS)
    have hd : MemLp (fun ω => M (j + 1) ω - M j ω) 2 P :=
      (hM.memLp (j + 1) hj).sub (hM.memLp j hjn.le)
    have hXL : MemLp (stopInner n R M j) 2 P :=
      MemLp.of_le_mul (c := R) hd (hXm.mono (hM.le _)).aestronglyMeasurable
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using stopInner_bound hR j ω)
    have hsplit : stopJ n R M (j + 1) = fun ω => stopJ n R M j ω + stopInner n R M j ω := by
      funext ω; simp [stopJ, Finset.sum_range_succ]
    -- the orthogonality
    set Z : Ω → ℝ^p := fun ω =>
      (stopJ n R M j ω * {ω | j < stopIdx n R M ω}.indicator (fun _ => (1 : ℝ)) ω) • M j ω with hZ
    have hZm : StronglyMeasurable[G j] Z :=
      (hJm.mul ((@stronglyMeasurable_const _ _ (G j) _ _).indicator hS)).smul (hM.meas j hjn.le)
    have hZL : MemLp Z 2 P := by
      refine MemLp.of_le_mul (c := R) hJL (hZm.mono (hM.le j)).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      by_cases h : j < stopIdx n R M ω
      · have h1 : ‖M j ω‖ < R := ((lt_stopIdx_iff n R M ω j).1 h j le_rfl).2
        simp only [hZ, Set.indicator, Set.mem_ofPred_eq, h, ite_true, mul_one, norm_smul,
          Real.norm_eq_abs]
        calc |stopJ n R M j ω| * ‖M j ω‖ ≤ |stopJ n R M j ω| * R :=
              mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
          _ = R * ‖stopJ n R M j ω‖ := by rw [mul_comm, Real.norm_eq_abs]
      · simp only [hZ, Set.indicator, Set.mem_ofPred_eq, h, ite_false, mul_zero, zero_smul, norm_zero]
        positivity
    have hZX : ∀ ω, stopJ n R M j ω * stopInner n R M j ω =
        inner ℝ (Z ω) (M (j + 1) ω - M j ω) := by
      intro ω
      by_cases h : j < stopIdx n R M ω
      · simp [hZ, stopInner, Set.indicator, h, real_inner_smul_left]
      · simp [hZ, stopInner, Set.indicator, h]
    have hcross : ∫ ω, stopJ n R M j ω * stopInner n R M j ω ∂P = 0 := by
      simp_rw [hZX]
      exact hM.orth j hjn Z hZm hZL
    have iJ := hJL.integrable_sq
    have iX := hXL.integrable_sq
    have iJX : Integrable (fun ω => stopJ n R M j ω * stopInner n R M j ω) P := hJL.integrable_mul hXL
    have i1 : Integrable (fun ω => stopJ n R M j ω ^ 2 + 2 * (stopJ n R M j ω * stopInner n R M j ω)) P := iJ.add (iJX.const_mul 2)
    have hX2 : ∫ ω, stopInner n R M j ω ^ 2 ∂P ≤
        R ^ 2 * ∫ ω, (if j < stopIdx n R M ω then ‖M (j + 1) ω - M j ω‖ ^ 2 else 0) ∂P := by
      rw [← integral_const_mul]
      refine integral_mono iX ((integrable_ite_of_meas P (hM.integrable_incr_sq P hjn)
        (hM.le j _ hS)).const_mul _) fun ω => stopInner_sq_le j ω
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit]
      exact (hJm.mono (hM.mono (Nat.le_succ j))).add hXm
    · rw [hsplit]; exact hJL.add hXL
    · rw [hsplit, Finset.sum_range_succ, mul_add]
      have e : ∀ ω, (stopJ n R M j ω + stopInner n R M j ω) ^ 2 =
          stopJ n R M j ω ^ 2 + 2 * (stopJ n R M j ω * stopInner n R M j ω) +
            stopInner n R M j ω ^ 2 := fun ω => by ring
      simp_rw [e]
      rw [integral_add i1 iX, integral_add iJ (iJX.const_mul 2),
        integral_const_mul, hcross]
      linarith


lemma stopEnergy_identity (n : ℕ) (R : ℝ) (M : ℕ → Ω → ℝ^p) (ω : Ω) :
    ∑ k ∈ Finset.range n, (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) =
      ‖M (stopIdx n R M ω) ω‖ ^ 2 - ‖M 0 ω‖ ^ 2 - 2 * stopJ n R M n ω := by
  have h1 : ∀ k, (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) =
      (if k < stopIdx n R M ω then ‖M (k + 1) ω‖ ^ 2 - ‖M k ω‖ ^ 2 else 0) -
        2 * stopInner n R M k ω := by
    intro k
    unfold stopInner
    split_ifs
    · have h0 : M (k + 1) ω = M k ω + (M (k + 1) ω - M k ω) := by abel
      have h2 : ‖M (k + 1) ω‖ ^ 2 = ‖M k ω‖ ^ 2 +
          2 * inner ℝ (M k ω) (M (k + 1) ω - M k ω) + ‖M (k + 1) ω - M k ω‖ ^ 2 := by
        conv_lhs => rw [h0]
        exact norm_add_sq_real _ _
      linarith
    · simp
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, sum_ite_lt_telescope (fun k => ‖M k ω‖ ^ 2) (stopIdx_le n R M ω),
    ← Finset.mul_sum]
  rfl

/-- the indicator weight `1_{x ≥ s}`. -/
noncomputable def tailW (s : ℝ) : ℝ → ℝ := Set.indicator (Set.Ici s) (fun _ => 1)

lemma tailW_measurable (s : ℝ) : Measurable (tailW s) :=
  measurable_const.indicator measurableSet_Ici

lemma tailW_nonneg (s x : ℝ) : 0 ≤ tailW s x := by
  unfold tailW; by_cases h : x ∈ Set.Ici s <;> simp [Set.indicator, h]

lemma tailW_le_one (s x : ℝ) : tailW s x ≤ 1 := by
  unfold tailW; by_cases h : x ∈ Set.Ici s <;> simp [Set.indicator, h]

lemma tailW_mul_le (s : ℝ) {x : ℝ} (hx : 0 ≤ x) : s * tailW s x ≤ x := by
  unfold tailW
  by_cases h : x ∈ Set.Ici s
  · simp only [Set.indicator, h, ite_true]; simpa using h
  · simp [Set.indicator, h, hx]

lemma tailW_of_lt {s x : ℝ} (h : x < s) : tailW s x = 0 := by
  unfold tailW; simp [Set.indicator, not_le.2 h]

lemma tailW_of_le {s x : ℝ} (h : s ≤ x) : tailW s x = 1 := by
  unfold tailW; simp [Set.indicator, h]


lemma DM.stop_mean (hM : DM P n G M) (R : ℝ) :
    Integrable (fun ω => ‖M (stopIdx n R M ω) ω‖ ^ 2) P ∧
      ∫ ω, ‖M (stopIdx n R M ω) ω‖ ^ 2 ∂P ≤ ∫ ω, ‖M n ω‖ ^ 2 ∂P := by
  obtain ⟨h1, -, h3⟩ := hM.stopped_ineq P R (W := fun _ => 1) measurable_const (fun _ => zero_le_one)
    (fun _ => le_rfl)
  simp only [one_mul] at h1 h3
  exact ⟨h1, h3⟩

lemma DM.tail_stop (hM : DM P n G M) (R : ℝ) {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    ∫ ω, tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 ∂P ≤
      ∫ ω, (if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) ∂P +
        c / s * ∫ ω, ‖M n ω‖ ^ 2 ∂P := by
  obtain ⟨hI, hmean⟩ := hM.stop_mean P R
  obtain ⟨-, hI2, -⟩ := hM.stopped_ineq P R (tailW_measurable s) (tailW_nonneg s) (tailW_le_one s)
  have hmeasn : Measurable (fun ω => ‖M n ω‖ ^ 2) :=
    ((hM.meas n le_rfl).mono (hM.le n)).norm.measurable.pow_const 2
  have hIte : Integrable (fun ω => if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) P :=
    integrable_ite_of_meas P (hM.integrable_sq P le_rfl)
      (measurableSet_lt measurable_const hmeasn)
  have hpt : ∀ ω, tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 ≤
      (if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) + c / s * ‖M (stopIdx n R M ω) ω‖ ^ 2 := by
    intro ω
    have hW0 := tailW_nonneg s (‖M (stopIdx n R M ω) ω‖ ^ 2)
    have hW1 := tailW_le_one s (‖M (stopIdx n R M ω) ω‖ ^ 2)
    have hWm := tailW_mul_le s (x := ‖M (stopIdx n R M ω) ω‖ ^ 2) (by positivity)
    have han : 0 ≤ ‖M n ω‖ ^ 2 := by positivity
    have ham : 0 ≤ ‖M (stopIdx n R M ω) ω‖ ^ 2 := by positivity
    have hcs : 0 ≤ c / s := div_nonneg hc hs.le
    split_ifs with h
    · have : tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 ≤ ‖M n ω‖ ^ 2 :=
        mul_le_of_le_one_left han hW1
      nlinarith [mul_nonneg hcs ham]
    · have h := not_lt.1 h
      calc tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2
          ≤ tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2) * c := mul_le_mul_of_nonneg_left h hW0
        _ = c / s * (s * tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2)) := by field_simp
        _ ≤ c / s * ‖M (stopIdx n R M ω) ω‖ ^ 2 := mul_le_mul_of_nonneg_left hWm hcs
        _ = 0 + c / s * ‖M (stopIdx n R M ω) ω‖ ^ 2 := by ring
  calc ∫ ω, tailW s (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 ∂P
      ≤ ∫ ω, ((if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) +
          c / s * ‖M (stopIdx n R M ω) ω‖ ^ 2) ∂P := integral_mono hI2 (hIte.add (hI.const_mul _)) hpt
    _ ≤ _ := by
        rw [integral_add hIte (hI.const_mul _), integral_const_mul]
        have := mul_le_mul_of_nonneg_left hmean (div_nonneg hc hs.le)
        linarith


lemma DM.post_le (hM : DM P n G M) {R : ℝ} (hR : 0 ≤ R) :
    ∫ ω, (‖M n ω‖ ^ 2 - ‖M (stopIdx n R M ω) ω‖ ^ 2) ∂P ≤
      ∫ ω, tailW (R ^ 2) (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M n ω‖ ^ 2 ∂P := by
  obtain ⟨hI, -⟩ := hM.stop_mean P R
  obtain ⟨-, hI2, -⟩ := hM.stopped_ineq P R (tailW_measurable (R ^ 2)) (tailW_nonneg _)
    (tailW_le_one _)
  refine integral_mono ((hM.integrable_sq P le_rfl).sub hI) hI2 fun ω => ?_
  by_cases h : R ^ 2 ≤ ‖M (stopIdx n R M ω) ω‖ ^ 2
  · rw [tailW_of_le h, one_mul]
    have : 0 ≤ ‖M (stopIdx n R M ω) ω‖ ^ 2 := by positivity
    linarith
  · have h' := not_le.1 h
    have hmn : stopIdx n R M ω = n := by
      by_contra hne
      have hlt : stopIdx n R M ω < n := lt_of_le_of_ne (stopIdx_le n R M ω) hne
      have := le_norm_stopIdx n R M ω hlt
      exact h (by nlinarith [norm_nonneg (M (stopIdx n R M ω) ω)])
    rw [tailW_of_lt h', hmn]
    simp


lemma continuous_taylorRem (H L : ℝ) : Continuous (taylorRem H L : (ℝ^p) → ℝ) := by
  unfold taylorRem; fun_prop

lemma taylorRem_nonneg {H L : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (v : ℝ^p) : 0 ≤ taylorRem H L v := by
  unfold taylorRem
  exact le_min (by positivity) (by positivity)

lemma taylorRem_le_left (H L : ℝ) (v : ℝ^p) : taylorRem H L v ≤ H * ‖v‖ ^ 2 := min_le_left _ _

lemma two_mul_le_aux {ψ J η : ℝ} (hη : 0 < η) : 2 * ψ * |J| ≤ η * J ^ 2 + ψ ^ 2 / η := by
  have h := sq_nonneg (η * |J| - ψ)
  have e : η * J ^ 2 + ψ ^ 2 / η - 2 * ψ * |J| = (η * |J| - ψ) ^ 2 / η := by
    have : J ^ 2 = |J| ^ 2 := (sq_abs J).symm
    rw [this]; field_simp; ring
  have : 0 ≤ (η * |J| - ψ) ^ 2 / η := div_nonneg h hη.le
  linarith


lemma DM.lindeberg_discrete (hM : DM P n G M) {R : ℝ} (hR : 0 < R) {H L : ℝ} (hH : 0 ≤ H)
    (hL : 0 ≤ L) {ψ : Ω → ℝ} (hψm : Measurable ψ) (hψ0 : ∀ ω, 0 ≤ ψ ω) (hψH : ∀ ω, ψ ω ≤ H)
    (hψ : ∀ ω, ∀ k < n, taylorRem H L (M (k + 1) ω - M k ω) ≤
      ψ ω * ‖M (k + 1) ω - M k ω‖ ^ 2)
    {K c η : ℝ} (hK : 0 < K) (hc : 0 ≤ c) (hη : 0 < η) :
    ∑ k ∈ Finset.range n, ∫ ω, taylorRem H L (M (k + 1) ω - M k ω) ∂P ≤
      K * ∫ ω, ψ ω ∂P + H * (∫ ω, (if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) ∂P +
        c / K * ∫ ω, ‖M n ω‖ ^ 2 ∂P)
      + η * R ^ 2 * ∫ ω, ‖M n ω‖ ^ 2 ∂P + H * (∫ ω, ψ ω ∂P) / η
      + H * (∫ ω, (if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) ∂P +
        c / R ^ 2 * ∫ ω, ‖M n ω‖ ^ 2 ∂P) := by
  classical
  have hsq : ∀ k < n, Integrable (fun ω => ‖M (k + 1) ω - M k ω‖ ^ 2) P :=
    fun k hk => hM.integrable_incr_sq P hk
  have hmeasS : ∀ k, MeasurableSet {ω | k < stopIdx n R M ω} := fun k =>
    hM.le k _ (hM.measurableSet_lt_stopIdx P R k)
  have hmeasS' : ∀ k, MeasurableSet {ω | stopIdx n R M ω ≤ k} := fun k => by
    have := (hmeasS k).compl
    convert this using 1
    ext ω; simp
  have hψint : Integrable ψ P := Integrable.of_bound hψm.aestronglyMeasurable H
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 ω)]; exact hψH ω)
  have hψsq : Integrable (fun ω => ψ ω ^ 2) P :=
    Integrable.of_bound (hψm.pow_const 2).aestronglyMeasurable (H ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (hψ0 ω) (hψH ω) 2)
  have hψbdd : ∀ ω, ‖ψ ω‖ ≤ H := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 ω)]; exact hψH ω
  -- the stopped and post-stopping energies
  set ξs : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n,
    (if k < stopIdx n R M ω then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) with hξs
  set ξp : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n,
    (if stopIdx n R M ω ≤ k then ‖M (k + 1) ω - M k ω‖ ^ 2 else 0) with hξp
  have hξsI : Integrable ξs P := integrable_finsetSum _ fun k hk =>
    integrable_ite_of_meas P (hsq k (Finset.mem_range.1 hk)) (hmeasS k)
  have hξpI : Integrable ξp P := integrable_finsetSum _ fun k hk =>
    integrable_ite_of_meas P (hsq k (Finset.mem_range.1 hk)) (hmeasS' k)
  have hTint : ∀ k ∈ Finset.range n, Integrable (fun ω => taylorRem H L (M (k + 1) ω - M k ω)) P := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hd : MemLp (fun ω => M (k + 1) ω - M k ω) 2 P :=
      (hM.memLp (k + 1) hk').sub (hM.memLp k hk'.le)
    refine Integrable.mono' ((hsq k hk').const_mul H)
      ((continuous_taylorRem H L).comp_aestronglyMeasurable hd.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (taylorRem_nonneg hH hL _)]
    exact taylorRem_le_left H L _
  -- pointwise comparison
  have hpt1 : ∀ ω, ∑ k ∈ Finset.range n, taylorRem H L (M (k + 1) ω - M k ω) ≤
      ψ ω * ξs ω + H * ξp ω := by
    intro ω
    simp only [hξs, hξp, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    by_cases h : k < stopIdx n R M ω
    · have : ¬ stopIdx n R M ω ≤ k := not_le.2 h
      simp only [h, this, ite_true, ite_false, mul_zero, add_zero]
      exact hψ ω k hk'
    · have h' : stopIdx n R M ω ≤ k := not_lt.1 h
      simp only [h, h', ite_true, ite_false, mul_zero, zero_add]
      exact taylorRem_le_left H L _
  have hA : ∑ k ∈ Finset.range n, ∫ ω, taylorRem H L (M (k + 1) ω - M k ω) ∂P =
      ∫ ω, ∑ k ∈ Finset.range n, taylorRem H L (M (k + 1) ω - M k ω) ∂P :=
    (integral_finsetSum _ hTint).symm
  have hψξI : Integrable (fun ω => ψ ω * ξs ω) P := hξsI.bdd_mul hψm.aestronglyMeasurable (ae_of_all _ hψbdd)
  have hB : ∫ ω, ∑ k ∈ Finset.range n, taylorRem H L (M (k + 1) ω - M k ω) ∂P ≤
      ∫ ω, ψ ω * ξs ω ∂P + H * ∫ ω, ξp ω ∂P := by
    rw [← integral_const_mul, ← integral_add hψξI (hξpI.const_mul H)]
    exact integral_mono (integrable_finsetSum _ hTint) (hψξI.add (hξpI.const_mul H)) hpt1
  have hξpint : ∫ ω, ξp ω ∂P = ∫ ω, (‖M n ω‖ ^ 2 - ‖M (stopIdx n R M ω) ω‖ ^ 2) ∂P := by
    rw [← hM.energy_post P R, ← integral_finsetSum]
    exact fun k hk => integrable_ite_of_meas P (hsq k (Finset.mem_range.1 hk)) (hmeasS' k)
  -- stopped quantities
  obtain ⟨hamI, hamean⟩ := hM.stop_mean P R
  obtain ⟨hJm, hJL, hJint⟩ := hM.stopJ_facts P hR.le n le_rfl
  have hJint2 : ∫ ω, stopJ n R M n ω ^ 2 ∂P ≤ R ^ 2 * ∫ ω, ‖M n ω‖ ^ 2 ∂P := by
    rw [hM.energy_pre P R] at hJint
    have h0 : 0 ≤ ∫ ω, ‖M 0 ω‖ ^ 2 ∂P := integral_nonneg fun ω => by positivity
    have : ∫ ω, (‖M (stopIdx n R M ω) ω‖ ^ 2 - ‖M 0 ω‖ ^ 2) ∂P =
        ∫ ω, ‖M (stopIdx n R M ω) ω‖ ^ 2 ∂P - ∫ ω, ‖M 0 ω‖ ^ 2 ∂P :=
      integral_sub hamI (hM.integrable_sq P (Nat.zero_le n))
    rw [this] at hJint
    have h2 : 0 ≤ R ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hamean h2]
  -- weights for the overshoot
  obtain ⟨hWKI, -, hWK⟩ := hM.stopped_ineq P R (tailW_measurable K) (tailW_nonneg K) (tailW_le_one K)
  have hKt := hM.tail_stop P R hK hc (c := c)
  have hRt := hM.tail_stop P R (s := R ^ 2) (by positivity) hc (c := c)
  have hpost := hM.post_le P hR.le
  -- the pointwise bound on `ψ ξs`
  have hJsqI := hJL.integrable_sq
  have hpt2 : ∀ ω, ψ ω * ξs ω ≤ K * ψ ω + H * (tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) *
      ‖M (stopIdx n R M ω) ω‖ ^ 2) + (η * stopJ n R M n ω ^ 2 + ψ ω ^ 2 / η) := by
    intro ω
    have hid := stopEnergy_identity n R M ω
    have h0 : 0 ≤ ‖M 0 ω‖ ^ 2 := by positivity
    have hJ : -(2 * stopJ n R M n ω) ≤ 2 * |stopJ n R M n ω| := by
      have := neg_abs_le (stopJ n R M n ω); linarith [abs_nonneg (stopJ n R M n ω)]
    have hξle : ξs ω ≤ ‖M (stopIdx n R M ω) ω‖ ^ 2 + 2 * |stopJ n R M n ω| := by
      have : ξs ω = ‖M (stopIdx n R M ω) ω‖ ^ 2 - ‖M 0 ω‖ ^ 2 - 2 * stopJ n R M n ω := hid
      rw [this]
      have := le_abs_self (stopJ n R M n ω)
      have := neg_abs_le (stopJ n R M n ω)
      linarith
    have hψ0' := hψ0 ω
    have hψH' := hψH ω
    have ham : 0 ≤ ‖M (stopIdx n R M ω) ω‖ ^ 2 := by positivity
    have h1 : ψ ω * ‖M (stopIdx n R M ω) ω‖ ^ 2 ≤ K * ψ ω + H * (tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) *
        ‖M (stopIdx n R M ω) ω‖ ^ 2) := by
      by_cases h : K ≤ ‖M (stopIdx n R M ω) ω‖ ^ 2
      · rw [tailW_of_le h, one_mul]
        nlinarith [mul_nonneg hψ0' hK.le, mul_le_mul_of_nonneg_right hψH' ham]
      · have h' := not_le.1 h
        rw [tailW_of_lt h', zero_mul, mul_zero, add_zero]
        nlinarith
    have h2 := two_mul_le_aux (ψ := ψ ω) (J := stopJ n R M n ω) hη
    calc ψ ω * ξs ω ≤ ψ ω * (‖M (stopIdx n R M ω) ω‖ ^ 2 + 2 * |stopJ n R M n ω|) :=
          mul_le_mul_of_nonneg_left hξle hψ0'
      _ = ψ ω * ‖M (stopIdx n R M ω) ω‖ ^ 2 + 2 * ψ ω * |stopJ n R M n ω| := by ring
      _ ≤ _ := by linarith
  have hUI : Integrable (fun ω => K * ψ ω + H * (tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) *
      ‖M (stopIdx n R M ω) ω‖ ^ 2) + (η * stopJ n R M n ω ^ 2 + ψ ω ^ 2 / η)) P :=
    (hψint.const_mul K |>.add (hWKI.const_mul H)).add ((hJsqI.const_mul η).add (hψsq.div_const η))
  have hC : ∫ ω, ψ ω * ξs ω ∂P ≤ K * ∫ ω, ψ ω ∂P + H * ∫ ω, tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) *
      ‖M (stopIdx n R M ω) ω‖ ^ 2 ∂P + (η * ∫ ω, stopJ n R M n ω ^ 2 ∂P + (∫ ω, ψ ω ^ 2 ∂P) / η) := by
    refine (integral_mono hψξI hUI hpt2).trans (le_of_eq ?_)
    have i1 : Integrable (fun ω => K * ψ ω) P := hψint.const_mul K
    have i2 : Integrable (fun ω => H * (tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) *
        ‖M (stopIdx n R M ω) ω‖ ^ 2)) P := hWKI.const_mul H
    have i3 : Integrable (fun ω => η * stopJ n R M n ω ^ 2) P := hJsqI.const_mul η
    have i4 : Integrable (fun ω => ψ ω ^ 2 / η) P := hψsq.div_const η
    have i12 : Integrable (fun ω => K * ψ ω + H * (tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) *
        ‖M (stopIdx n R M ω) ω‖ ^ 2)) P := i1.add i2
    have i34 : Integrable (fun ω => η * stopJ n R M n ω ^ 2 + ψ ω ^ 2 / η) P := i3.add i4
    rw [integral_add i12 i34, integral_add i1 i2, integral_add i3 i4, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_div]
  -- ψ² ≤ H ψ
  have hψ2 : ∫ ω, ψ ω ^ 2 ∂P ≤ H * ∫ ω, ψ ω ∂P := by
    rw [← integral_const_mul]
    exact integral_mono hψsq (hψint.const_mul H) fun ω => by
      have := hψ0 ω; have := hψH ω; nlinarith
  have hdiv : (∫ ω, ψ ω ^ 2 ∂P) / η ≤ H * (∫ ω, ψ ω ∂P) / η := by
    exact div_le_div_of_nonneg_right hψ2 hη.le
  rw [hA]
  refine hB.trans ?_
  rw [hξpint]
  have hpost' : H * ∫ ω, (‖M n ω‖ ^ 2 - ‖M (stopIdx n R M ω) ω‖ ^ 2) ∂P ≤
      H * (∫ ω, (if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) ∂P +
        c / R ^ 2 * ∫ ω, ‖M n ω‖ ^ 2 ∂P) :=
    mul_le_mul_of_nonneg_left (hpost.trans hRt) hH
  have hWK' : H * ∫ ω, tailW K (‖M (stopIdx n R M ω) ω‖ ^ 2) * ‖M (stopIdx n R M ω) ω‖ ^ 2 ∂P ≤
      H * (∫ ω, (if c < ‖M n ω‖ ^ 2 then ‖M n ω‖ ^ 2 else 0) ∂P +
        c / K * ∫ ω, ‖M n ω‖ ^ 2 ∂P) :=
    mul_le_mul_of_nonneg_left (hWK.trans hKt) hH
  have hJ' : η * ∫ ω, stopJ n R M n ω ^ 2 ∂P ≤ η * (R ^ 2 * ∫ ω, ‖M n ω‖ ^ 2 ∂P) :=
    mul_le_mul_of_nonneg_left hJint2 hη.le
  nlinarith


lemma stronglyMeasurable_of_coord {m : MeasurableSpace Ω} {X : Ω → ℝ^p}
    (h : ∀ a, StronglyMeasurable[m] (fun ω => X ω a)) : StronglyMeasurable[m] X := by
  have : X = fun ω => ∑ a, X ω a • EuclideanSpace.single a (1 : ℝ) := by
    ext ω b
    simp [Pi.single_apply]
  rw [this]
  exact Finset.stronglyMeasurable_fun_sum _ fun a _ => (h a).smul_const _

lemma unifPart_mono {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : Monotone (unifPart t n) := by
  intro j k hjk
  unfold unifPart
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) ht)
    (Nat.cast_nonneg n)

lemma unifPart_nonneg {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) : 0 ≤ unifPart t n k := by
  unfold unifPart; positivity

lemma unifPart_le {t : ℝ} (ht : 0 ≤ t) {n k : ℕ} (hk : k ≤ n) : unifPart t n k ≤ t := by
  unfold unifPart
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using ht
  · rw [div_le_iff₀ (by exact_mod_cast hn)]
    nlinarith [mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ n by exact_mod_cast hk) ht]

lemma unifPart_self (t : ℝ) {n : ℕ} (hn : 1 ≤ n) : unifPart t n n = t := by
  unfold unifPart
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma unifPart_succ_sub (t : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    unifPart t n (k + 1) - unifPart t n k = t / n := by
  unfold unifPart
  have : (n : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- the discrete martingale along the uniform partition. -/
lemma dm_unif (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg) (n : ℕ) :
    DM P n (fun k => ℱ (unifPart t n k)) (fun k => M (unifPart t n k)) where
  mono := fun j k hjk => ℱ.mono (unifPart_mono ht n hjk)
  le := fun k => ℱ.le _
  meas := fun k _ => stronglyMeasurable_of_coord fun a => (hM.martingale a).1 _
  memLp := fun k hk => hM.sq_int _ ⟨unifPart_nonneg ht n k, unifPart_le ht hk⟩
  orth := fun k hk Z hZ hZ2 => by
    refine martingale_increment_inner P ℱ t M Sg hM _ _ (unifPart_nonneg ht n k)
      (unifPart_mono ht n (Nat.le_succ k)) (unifPart_le ht hk) Z hZ hZ2


/-- the modulus envelope `ψ_n = min(H, L max_k |ΔM_k|)`. -/
noncomputable def lipPsi (H L t : ℝ) (M : ℝ → Ω → (ℝ^p)) (n : ℕ) (ω : Ω) : ℝ :=
  min H (L * ((Finset.range n).sup
    (fun k => ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖₊) : ℝ≥0))

lemma lipPsi_nonneg {H L : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (t : ℝ) (M : ℝ → Ω → (ℝ^p)) (n : ℕ)
    (ω : Ω) : 0 ≤ lipPsi H L t M n ω :=
  le_min hH (mul_nonneg hL (NNReal.coe_nonneg _))

lemma lipPsi_le (H L t : ℝ) (M : ℝ → Ω → (ℝ^p)) (n : ℕ) (ω : Ω) : lipPsi H L t M n ω ≤ H :=
  min_le_left _ _

lemma measurable_finset_sup_nnreal {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ≥0}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => s.sup fun i => f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    simp only [Finset.sup_insert]
    exact (hf a).sup ih

lemma lipPsi_measurable (H L t : ℝ) (M : ℝ → Ω → (ℝ^p)) (hMm : ∀ τ, Measurable (M τ)) (n : ℕ) :
    Measurable (lipPsi H L t M n) := by
  unfold lipPsi
  refine measurable_const.min (Measurable.const_mul ?_ _)
  refine measurable_coe_nnreal_real.comp ?_
  exact measurable_finset_sup_nnreal _ fun k => ((hMm _).sub (hMm _)).nnnorm

lemma taylorRem_le_lipPsi {H L : ℝ} (hL : 0 ≤ L) (t : ℝ) (M : ℝ → Ω → (ℝ^p)) {n k : ℕ}
    (hk : k < n) (ω : Ω) :
    taylorRem H L (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω) ≤
      lipPsi H L t M n ω * ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖ ^ 2 := by
  set v := M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω with hv
  have hle : ‖v‖ ≤ (((Finset.range n).sup
      (fun k => ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖₊) : ℝ≥0) : ℝ) := by
    have := Finset.le_sup (f := fun k => ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖₊)
      (Finset.mem_range.2 hk)
    exact_mod_cast this
  unfold lipPsi taylorRem
  set s : ℝ := (((Finset.range n).sup
      (fun k => ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖₊) : ℝ≥0) : ℝ)
  calc min (H * ‖v‖ ^ 2) (L * ‖v‖ ^ 3) ≤ min (H * ‖v‖ ^ 2) (L * s * ‖v‖ ^ 2) := by
        refine min_le_min le_rfl ?_
        have : L * ‖v‖ ^ 3 = L * ‖v‖ * ‖v‖ ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hL) (by positivity)
    _ = min H (L * s) * ‖v‖ ^ 2 := by
        rw [min_mul_of_nonneg _ _ (by positivity)]


lemma lipPsi_tendsto {H L : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (ω : Ω) (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t)) :
    Tendsto (fun n => lipPsi H L t M n ω) atTop (𝓝 0) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (L + 1) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / (L + 1)) hε'
  refine ⟨⌈t / δ⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have htn : t / n < δ := by
    rw [div_lt_iff₀ hnpos]
    have h1 : t / δ < n := by
      have := Nat.le_ceil (t / δ)
      have h2 : (⌈t / δ⌉₊ + 1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hsup : ((Finset.range n).sup
      (fun k => ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖₊) : ℝ≥0) ≤
        Real.toNNReal (ε / (L + 1)) := by
    refine Finset.sup_le fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have := hδ' (unifPart t n (k + 1)) ⟨unifPart_nonneg ht n _, unifPart_le ht hk'⟩
      (unifPart t n k) ⟨unifPart_nonneg ht n _, unifPart_le ht hk'.le⟩ (by
        rw [Real.dist_eq, unifPart_succ_sub t hn1, abs_of_nonneg (by positivity)]; exact htn)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hε'.le]
    simpa [dist_eq_norm] using this.le
  have hψ0 := lipPsi_nonneg hH hL t M n ω
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hψ0]
  calc lipPsi H L t M n ω ≤ L * ((Finset.range n).sup
        (fun k => ‖M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω‖₊) : ℝ≥0) := min_le_right _ _
    _ ≤ L * (ε / (L + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hL
        have := NNReal.coe_le_coe.2 hsup
        rwa [Real.coe_toNNReal _ hε'.le] at this
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith


omit [IsProbabilityMeasure P] in
lemma tail_tendsto {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω) :
    Tendsto (fun c : ℝ => ∫ ω, (if c < f ω then f ω else 0) ∂P) atTop (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := atTop)
    (F := fun (c : ℝ) ω => if c < f ω then f ω else 0) (f := fun _ => (0 : ℝ)) f
    (Eventually.of_forall fun c => (Measurable.ite (measurableSet_lt measurable_const hfm) hfm
      measurable_const).aestronglyMeasurable)
    (Eventually.of_forall fun c => ae_of_all _ fun ω => by
      by_cases h : c < f ω
      · simp [h, abs_of_nonneg (hf0 ω)]
      · simp [h, hf0 ω])
    hf
    (ae_of_all _ fun ω => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (f ω)] with c hc
      simp [not_lt.2 hc])
  simpa using this

lemma limit_aux {S e : ℕ → ℝ} {H μ : ℝ} (hH : 0 ≤ H) (hμ : 0 ≤ μ) {τ : ℝ → ℝ}
    (hτ : Tendsto τ atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) (hS0 : ∀ n, 0 ≤ S n)
    (hb : ∀ᶠ n in atTop, ∀ R K c η : ℝ, 0 < R → 0 < K → 0 ≤ c → 0 < η →
      S n ≤ K * e n + H * (τ c + c / K * μ) + η * R ^ 2 * μ + H * e n / η +
        H * (τ c + c / R ^ 2 * μ)) :
    Tendsto S atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hτ' : ∀ᶠ c in atTop, |τ c| < ε / (8 * (H + 1)) := by
    have := (Metric.tendsto_nhds.1 hτ) (ε / (8 * (H + 1))) (by positivity)
    simpa [Real.dist_eq] using this
  obtain ⟨c, hcτ, hc0⟩ := (hτ'.and (eventually_ge_atTop (0 : ℝ))).exists
  have hHτ : H * τ c ≤ ε / 8 := by
    calc H * τ c ≤ H * |τ c| := mul_le_mul_of_nonneg_left (le_abs_self _) hH
      _ ≤ H * (ε / (8 * (H + 1))) := mul_le_mul_of_nonneg_left hcτ.le hH
      _ ≤ ε / 8 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  obtain ⟨A, hA⟩ : ∃ A, A = H * c * μ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 8 * A / ε + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; positivity
  have hAK : H * (c / K * μ) ≤ ε / 8 := by
    have h1 : H * (c / K * μ) = A / K := by rw [hA]; field_simp
    rw [h1, div_le_iff₀ hK]
    have h2 : 8 * A / ε * (ε / 8) = A := by field_simp
    rw [hKdef]
    nlinarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.sqrt K := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; exact Real.sqrt_pos.2 hK
  have hR2 : R ^ 2 = K := by rw [hRdef]; exact Real.sq_sqrt hK.le
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (8 * (K * μ + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηK : η * R ^ 2 * μ ≤ ε / 8 := by
    rw [hR2, hηdef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hε.le (mul_nonneg hK.le hμ)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = K + H / η := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have he' : ∀ᶠ n in atTop, |e n| < ε / (8 * (C + 1)) := by
    have := (Metric.tendsto_nhds.1 he) (ε / (8 * (C + 1))) (by positivity)
    simpa [Real.dist_eq] using this
  have key : ∀ᶠ n in atTop, dist (S n) 0 < ε := by
    filter_upwards [hb, he'] with n hbn hen
    have hbn := hbn R K c η hR hK hc0 hη
    have hCe : K * e n + H * e n / η ≤ ε / 8 := by
      have : K * e n + H * e n / η = C * e n := by rw [hC]; ring
      rw [this]
      calc C * e n ≤ C * |e n| := mul_le_mul_of_nonneg_left (le_abs_self _) hC0
        _ ≤ C * (ε / (8 * (C + 1))) := mul_le_mul_of_nonneg_left hen.le hC0
        _ ≤ ε / 8 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    have hexp : H * (τ c + c / K * μ) = H * τ c + H * (c / K * μ) := mul_add _ _ _
    have hexp2 : H * (τ c + c / R ^ 2 * μ) = H * τ c + H * (c / K * μ) := by
      rw [hR2, mul_add]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hS0 n)]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 key
  exact ⟨N, hN⟩

end LindebergAux
end LindebergDiscrete
open LindebergAux

/-- Step 4: the discrete Lindeberg condition for the martingale along uniform partitions,
`∑_k E min(H|ΔM_k|², L|ΔM_k|³) → 0` (path continuity, `E∑_k|ΔM_k|² = E|M_t|²`, and uniform
integrability of the discrete quadratic variations after localisation at
`T_R = inf{τ : |M_τ| ≥ R or ∫_0^τ ‖Σ‖_{S_1} ≥ R}`). -/
theorem martingale_lindeberg_tendsto (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg) (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        ∫ ω, taylorRem H L (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω) ∂P)
      atTop (𝓝 0) := by
  classical
  have hMm : ∀ τ, Measurable (M τ) := fun τ =>
    ((stronglyMeasurable_of_coord fun a => (hM.martingale a).1 τ).mono (ℱ.le τ)).measurable
  have hMt : MemLp (M t) 2 P := hM.sq_int t ⟨ht, le_rfl⟩
  have hsqI : Integrable (fun ω => ‖M t ω‖ ^ 2) P := hMt.integrable_norm_pow (by norm_num)
  have hτ : Tendsto (fun c : ℝ => ∫ ω, (if c < ‖M t ω‖ ^ 2 then ‖M t ω‖ ^ 2 else 0) ∂P) atTop (𝓝 0) :=
    tail_tendsto P ((hMm t).norm.pow_const 2) hsqI (fun ω => by positivity)
  have he : Tendsto (fun n : ℕ => ∫ ω, lipPsi H L t M n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => H)
      (F := fun (n : ℕ) ω => lipPsi H L t M n ω) (f := fun _ => (0 : ℝ))
      (fun n => (lipPsi_measurable H L t M hMm n).aestronglyMeasurable) (integrable_const H)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (lipPsi_nonneg hH hL t M n ω)]
        exact lipPsi_le H L t M n ω)
      (by
        filter_upwards [hM.cont] with ω hω
        exact lipPsi_tendsto hH hL ht M ω hω)
    simpa using this
  refine limit_aux (S := fun n : ℕ => ∑ k ∈ Finset.range n,
      ∫ ω, taylorRem H L (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω) ∂P)
    (e := fun n : ℕ => ∫ ω, lipPsi H L t M n ω ∂P) (μ := ∫ ω, ‖M t ω‖ ^ 2 ∂P) hH
    (integral_nonneg fun ω => by positivity) hτ he
    (fun n => Finset.sum_nonneg fun k _ => integral_nonneg fun ω => taylorRem_nonneg hH hL _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn R K c η hR hK hc hη
  have hDM := dm_unif P ℱ t ht M Sg hM n
  have := hDM.lindeberg_discrete P hR hH hL (lipPsi_measurable H L t M hMm n)
    (lipPsi_nonneg hH hL t M n) (lipPsi_le H L t M n)
    (fun ω k hk => taylorRem_le_lipPsi hL t M hk ω) hK hc hη
  have e1 : unifPart t n n = t := unifPart_self t hn
  simp only [e1] at this
  exact this


namespace LindebergAux


lemma integral_pow4_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = (v : ℝ) ^ 2 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  have h : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · rw [← NNReal.coe_inj]
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [h, integral_map (by fun_prop) (by fun_prop)]
  have : ∀ x : ℝ, (Real.sqrt v * x) ^ 4 = (v : ℝ) ^ 2 * x ^ 4 := fun x => by
    rw [mul_pow]
    congr 1
    have := Real.sq_sqrt v.coe_nonneg
    calc Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]
  simp_rw [this]
  rw [integral_const_mul]


lemma integral_coord_pow4_mvGaussian {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) (i : Fin p) :
    ∫ y, (y i) ^ 4 ∂(multivariateGaussian (0 : ℝ^p) Q) =
      (Q i i) ^ 2 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : ℝ^p)) hQ (i := i)
  have hmeq : Measure.map (fun x : ℝ^p => x i) (multivariateGaussian (0 : ℝ^p) Q) =
      gaussianReal 0 (Q i i).toNNReal := hmp.map_eq
  have h1 : ∫ x, x ^ 4 ∂(gaussianReal 0 (Q i i).toNNReal) =
      ∫ y, (y i) ^ 4 ∂(multivariateGaussian (0 : ℝ^p) Q) := by
    rw [← hmeq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
  rw [← h1, integral_pow4_gaussianReal, Real.coe_toNNReal _ hQ.diag_nonneg]

lemma integral_norm_pow4_mvGaussian {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) :
    ∫ y, ‖y‖ ^ 4 ∂(multivariateGaussian (0 : ℝ^p) Q) ≤
      p * (∫ x, x ^ 4 ∂(gaussianReal 0 1)) * (Matrix.trace Q) ^ 2 := by
  set γ := multivariateGaussian (0 : ℝ^p) Q with hγ
  have hmem : MemLp id 4 γ := IsGaussian.memLp_id γ 4 (by simp)
  have hint4 : Integrable (fun y : ℝ^p => ‖y‖ ^ 4) γ := by
    have := hmem.integrable_norm_pow (p := 4) (by norm_num)
    simpa using this
  have hinti : ∀ i : Fin p, Integrable (fun y : ℝ^p => (y i) ^ 4) γ := by
    intro i
    have h1 : MemLp (fun y : ℝ^p => y i) 4 γ :=
      (EuclideanSpace.proj i : (ℝ^p) →L[ℝ] ℝ).comp_memLp' hmem
    have := h1.integrable_norm_pow (p := 4) (by norm_num)
    simpa [Even.pow_abs (by norm_num : Even 4)] using this
  have hpt : ∀ y : ℝ^p, ‖y‖ ^ 4 ≤ p * ∑ i, (y i) ^ 4 := by
    intro y
    have h1 : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin p => (y i) ^ 2)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    calc ‖y‖ ^ 4 = (‖y‖ ^ 2) ^ 2 := by ring
      _ = (∑ i, (y i) ^ 2) ^ 2 := by rw [h1]
      _ ≤ p * ∑ i, ((y i) ^ 2) ^ 2 := h2
      _ = _ := by simp_rw [← pow_mul]
  have hc4 : 0 ≤ ∫ x, x ^ 4 ∂(gaussianReal 0 1) := integral_nonneg fun x => by positivity
  calc ∫ y, ‖y‖ ^ 4 ∂γ ≤ ∫ y, (p : ℝ) * ∑ i, (y i) ^ 4 ∂γ :=
        integral_mono hint4 ((integrable_finsetSum _ fun i _ => hinti i).const_mul _) hpt
    _ = p * ∑ i, (Q i i) ^ 2 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hinti i]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_coord_pow4_mvGaussian hQ i
    _ = p * (∫ x, x ^ 4 ∂(gaussianReal 0 1)) * ∑ i, (Q i i) ^ 2 := by
        rw [← Finset.sum_mul]; ring
    _ ≤ p * (∫ x, x ^ 4 ∂(gaussianReal 0 1)) * (Matrix.trace Q) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hQ.diag_nonneg


lemma taylorRem_le_fourth {H L δ : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hδ : 0 < δ) (v : ℝ^p) :
    taylorRem H L v ≤ L * δ * ‖v‖ ^ 2 + H / δ ^ 2 * ‖v‖ ^ 4 := by
  have hv := norm_nonneg v
  have h4 : 0 ≤ H / δ ^ 2 * ‖v‖ ^ 4 := by positivity
  by_cases h : ‖v‖ ≤ δ
  · calc taylorRem H L v ≤ L * ‖v‖ ^ 3 := min_le_right _ _
      _ = L * ‖v‖ * ‖v‖ ^ 2 := by ring
      _ ≤ L * δ * ‖v‖ ^ 2 := by gcongr
      _ ≤ _ := by linarith
  · have h' := not_le.1 h
    have hL0 : 0 ≤ L * δ * ‖v‖ ^ 2 := by positivity
    calc taylorRem H L v ≤ H * ‖v‖ ^ 2 := min_le_left _ _
      _ ≤ H / δ ^ 2 * ‖v‖ ^ 4 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : δ ^ 2 ≤ ‖v‖ ^ 2 := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hH (sq_nonneg ‖v‖))]
      _ ≤ _ := by linarith

lemma integral_taylorRem_mvGaussian_le {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef)
    {H L δ : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p) Q) ≤
      L * δ * Matrix.trace Q +
        H / δ ^ 2 * (p * (∫ x, x ^ 4 ∂(gaussianReal 0 1)) * (Matrix.trace Q) ^ 2) := by
  set γ := multivariateGaussian (0 : ℝ^p) Q with hγ
  have hmem2 : MemLp id 2 γ := IsGaussian.memLp_id γ 2 (by simp)
  have hmem4 : MemLp id 4 γ := IsGaussian.memLp_id γ 4 (by simp)
  have hint2 : Integrable (fun y : ℝ^p => ‖y‖ ^ 2) γ := by
    simpa using hmem2.integrable_norm_pow (p := 2) (by norm_num)
  have hint4 : Integrable (fun y : ℝ^p => ‖y‖ ^ 4) γ := by
    simpa using hmem4.integrable_norm_pow (p := 4) (by norm_num)
  have hT : Integrable (fun y : ℝ^p => taylorRem H L y) γ := by
    refine Integrable.mono' (hint2.const_mul H) (continuous_taylorRem H L).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (taylorRem_nonneg hH hL _)]
    exact taylorRem_le_left H L _
  calc ∫ y, taylorRem H L y ∂γ ≤ ∫ y, (L * δ * ‖y‖ ^ 2 + H / δ ^ 2 * ‖y‖ ^ 4) ∂γ :=
        integral_mono hT ((hint2.const_mul _).add (hint4.const_mul _))
          fun y => taylorRem_le_fourth hH hL hδ y
    _ = L * δ * ∫ y, ‖y‖ ^ 2 ∂γ + H / δ ^ 2 * ∫ y, ‖y‖ ^ 4 ∂γ := by
        rw [integral_add (hint2.const_mul _) (hint4.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        rw [hγ, integral_norm_sq_mvGaussian hQ]
        have := integral_norm_pow4_mvGaussian hQ
        have h0 : 0 ≤ H / δ ^ 2 := by positivity
        linarith [mul_le_mul_of_nonneg_left this h0]


lemma intervalIntegrable_unif {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : IntegrableOn f (Set.Icc 0 t))
    (n k : ℕ) (hk : k < n) :
    IntervalIntegrable f volume (unifPart t n k) (unifPart t n (k + 1)) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (unifPart_mono ht n (Nat.le_succ k))]
  refine hf.mono_set (Set.Icc_subset_Icc (unifPart_nonneg ht n k) (unifPart_le ht hk))

lemma sum_blocks {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : IntegrableOn f (Set.Icc 0 t)) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, ∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x = ∫ x in (0:ℝ)..t, f x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := unifPart t n) (n := n) (fun k hk => intervalIntegrable_unif ht hf n k hk)
  rw [h]
  have h0 : unifPart t n 0 = 0 := by simp [unifPart]
  rw [h0, unifPart_self t hn]

lemma block_small {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : IntegrableOn f (Set.Icc 0 t)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k < n, ∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x < ε := by
  have hcont : ContinuousOn (fun x => ∫ s in (0:ℝ)..x, f s) (Set.Icc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t) (μ := volume)
      (f := f) (by rwa [Set.uIcc_of_le ht])
    rwa [Set.uIcc_of_le ht] at this
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  refine ⟨⌈t / δ⌉₊ + 1, fun n hn k hk => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have htn : t / n < δ := by
    rw [div_lt_iff₀ hnpos]
    have h1 : t / δ < n := by
      have := Nat.le_ceil (t / δ)
      have h2 : (⌈t / δ⌉₊ + 1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hI := intervalIntegrable_unif ht hf n k hk
  have hI0 : IntervalIntegrable f volume 0 (unifPart t n k) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (unifPart_nonneg ht n k)]
    exact hf.mono_set (Set.Icc_subset_Icc le_rfl (unifPart_le ht hk.le))
  have hI1 : IntervalIntegrable f volume 0 (unifPart t n (k + 1)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (unifPart_nonneg ht n _)]
    exact hf.mono_set (Set.Icc_subset_Icc le_rfl (unifPart_le ht hk))
  have e := intervalIntegral.integral_interval_sub_left hI1 hI0
  rw [← e]
  have := hδ' (unifPart t n (k + 1)) ⟨unifPart_nonneg ht n _, unifPart_le ht hk⟩
    (unifPart t n k) ⟨unifPart_nonneg ht n _, unifPart_le ht hk.le⟩ (by
      rw [Real.dist_eq, unifPart_succ_sub t hn1, abs_of_nonneg (by positivity)]; exact htn)
  rw [Real.dist_eq] at this
  exact lt_of_le_of_lt (le_abs_self _) this


lemma trace_le_s1Norm (A : Matrix (Fin p) (Fin p) ℝ) : Matrix.trace A ≤ s1Norm A := by
  have := le_traceNormMatrix A 1
  simpa using this

lemma sb_diag_integrableOn {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb) {t : ℝ}
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef) (i : Fin p) :
    IntegrableOn (fun σ => sb σ i i) (Set.Icc 0 t) := by
  refine Integrable.mono' hsbint ?_ ?_
  · exact ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp hsbmeas)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun σ hσ => ?_)
    have hd : 0 ≤ sb σ i i := (hsbpsd σ hσ).diag_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hd]
    refine le_trans ?_ (trace_le_s1Norm (sb σ))
    exact Finset.single_le_sum (f := fun j => sb σ j j) (fun j _ => (hsbpsd σ hσ).diag_nonneg)
      (Finset.mem_univ i)
end LindebergAux
open LindebergAux

/-- Step 4, Gaussian side: `∑_k ∫ min(H|y|², L|y|³) dN(0, Q_k) → 0`, since
`E|Y_k|³ ≤ C_p (tr Q_k)^{3/2}` and `τ ↦ ∫_0^τ tr sb` is uniformly continuous. -/
theorem gaussian_lindeberg_tendsto (t : ℝ) (ht : 0 ≤ t)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef) (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        ∫ y, taylorRem H L y ∂(multivariateGaussian 0
          (covBlock sb (unifPart t n k) (unifPart t n (k + 1))))) atTop (𝓝 0) := by
  classical
  have hdiag := sb_diag_integrableOn hsbmeas hsbint hsbpsd
  set f : ℝ → ℝ := fun σ => Matrix.trace (sb σ) with hf
  have hfint : IntegrableOn f (Set.Icc 0 t) := by
    simp only [hf, Matrix.trace, Matrix.diag]
    exact integrable_finsetSum _ fun i _ => hdiag i
  have hf0 : ∀ σ ∈ Set.Icc 0 t, 0 ≤ f σ := fun σ hσ => (hsbpsd σ hσ).trace_nonneg
  have htr : ∀ a b : ℝ, 0 ≤ a → b ≤ t →
      Matrix.trace (covBlock sb a b) = ∫ σ in Set.Icc a b, f σ := by
    intro a b ha hb
    have hsub : Set.Icc a b ⊆ Set.Icc 0 t := Set.Icc_subset_Icc ha hb
    simp only [hf, Matrix.trace, Matrix.diag, covBlock, Matrix.of_apply]
    rw [integral_finsetSum _ fun i _ => (hdiag i).mono_set hsub]
  set c4 : ℝ := ∫ x, x ^ 4 ∂(gaussianReal 0 1) with hc4def
  have hc4 : 0 ≤ c4 := integral_nonneg fun x => by positivity
  -- block bound
  have hblock : ∀ n k : ℕ, k < n → ∀ δ : ℝ, 0 < δ →
      ∫ y, taylorRem H L y ∂(multivariateGaussian 0
          (covBlock sb (unifPart t n k) (unifPart t n (k + 1)))) ≤
        L * δ * (∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x) +
          H / δ ^ 2 * (p * c4) * (∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x) ^ 2 := by
    intro n k hk δ hδ
    have hab : unifPart t n k ≤ unifPart t n (k + 1) := unifPart_mono ht n (Nat.le_succ k)
    have hq : ∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x =
        ∫ σ in Set.Icc (unifPart t n k) (unifPart t n (k + 1)), f σ := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    have hq0 : 0 ≤ ∫ σ in Set.Icc (unifPart t n k) (unifPart t n (k + 1)), f σ :=
      setIntegral_nonneg measurableSet_Icc fun σ hσ =>
        hf0 σ ⟨(unifPart_nonneg ht n k).trans hσ.1, hσ.2.trans (unifPart_le ht hk)⟩
    rw [hq]
    set Q := covBlock sb (unifPart t n k) (unifPart t n (k + 1)) with hQ
    by_cases hQpsd : Q.PosSemidef
    · have := integral_taylorRem_mvGaussian_le hQpsd hH hL hδ
      rw [hQ, htr _ _ (unifPart_nonneg ht n k) (unifPart_le ht hk)] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [multivariateGaussian_of_not_posSemidef _ hQpsd, integral_dirac]
      have : taylorRem H L (0 : ℝ^p) = 0 := by simp [taylorRem]
      rw [this]
      positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set T : ℝ := ∫ x in (0:ℝ)..t, f x with hT
  have hT0 : 0 ≤ T := by
    rw [hT, intervalIntegral.integral_of_le ht]
    exact setIntegral_nonneg measurableSet_Ioc fun σ hσ => hf0 σ ⟨hσ.1.le, hσ.2⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (2 * (L * T + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hLδT : L * δ * T ≤ ε / 2 := by
    have h1 : δ * (2 * (L * T + 1)) = ε := by rw [hδdef]; field_simp
    nlinarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = H / δ ^ 2 * (p * c4) := ⟨_, rfl⟩
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = ε / (4 * (C * T + 1)) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  have hCε : C * ε₁ * T ≤ ε / 4 := by
    have h1 : ε₁ * (4 * (C * T + 1)) = ε := by rw [hε₁def]; field_simp
    nlinarith
  obtain ⟨N, hN⟩ := block_small ht hfint hε₁
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hq0 : ∀ k < n, 0 ≤ ∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x := by
    intro k hk
    rw [intervalIntegral.integral_of_le (unifPart_mono ht n (Nat.le_succ k))]
    exact setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
      hf0 σ ⟨(unifPart_nonneg ht n k).trans hσ.1.le, hσ.2.trans (unifPart_le ht hk)⟩
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range n, ∫ y, taylorRem H L y ∂(multivariateGaussian 0
      (covBlock sb (unifPart t n k) (unifPart t n (k + 1)))) :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun y => taylorRem_nonneg hH hL y
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  calc _ ≤ ∑ k ∈ Finset.range n, (L * δ + C * ε₁) *
        (∫ x in (unifPart t n k)..(unifPart t n (k + 1)), f x) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        refine (hblock n k hk' δ hδ).trans ?_
        have hqk := hq0 k hk'
        have hqe := hN n hnN k hk'
        rw [← hCdef]
        nlinarith [mul_le_mul_of_nonneg_right hqe.le hqk, mul_nonneg hC hqk]
    _ = (L * δ + C * ε₁) * T := by rw [← Finset.mul_sum, sum_blocks ht hfint hn1]
    _ < ε := by nlinarith


namespace LindebergAux

lemma psd_entry_le {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) (i j : Fin p) :
    |Q i j| ≤ (Q i i + Q j j) / 2 := by
  classical
  have hs : Q j i = Q i j := by
    have := hQ.1.apply i j
    simpa using this
  have key : ∀ c : ℝ, 0 ≤ Q i i + c * Q i j + c * Q j i + c * c * Q j j := by
    intro c
    have := hQ.dotProduct_mulVec_nonneg (Pi.single i 1 + c • Pi.single j 1)
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct] at this
    nlinarith [this]
  have h1 := key 1
  have h2 := key (-1)
  rw [hs] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

lemma sb_entry_integrableOn {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb) {t : ℝ}
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef) (i j : Fin p) :
    IntegrableOn (fun σ => sb σ i j) (Set.Icc 0 t) := by
  have hi := sb_diag_integrableOn hsbmeas hsbint hsbpsd i
  have hj := sb_diag_integrableOn hsbmeas hsbint hsbpsd j
  refine Integrable.mono' ((hi.add hj).div_const 2) ?_ ?_
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hsbmeas)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun σ hσ => ?_)
    rw [Real.norm_eq_abs]
    exact psd_entry_le (hsbpsd σ hσ) i j

lemma setInt_Icc_add {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntegrableOn f (Set.Icc a c)) :
    (∫ σ in Set.Icc a b, f σ) + (∫ σ in Set.Icc b c, f σ) = ∫ σ in Set.Icc a c, f σ := by
  have i1 : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf.mono_set (Set.Icc_subset_Icc le_rfl hbc)
  have i2 : IntervalIntegrable f volume b c := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbc]
    exact hf.mono_set (Set.Icc_subset_Icc hab le_rfl)
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hbc, ← intervalIntegral.integral_of_le (hab.trans hbc)]
  exact intervalIntegral.integral_add_adjacent_intervals i1 i2

lemma covBlock_add {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ i j, IntegrableOn (fun σ => sb σ i j) (Set.Icc a c)) :
    covBlock sb a c = covBlock sb a b + covBlock sb b c := by
  ext i j
  simp only [covBlock, Matrix.of_apply, Matrix.add_apply]
  rw [setInt_Icc_add hab hbc (hf i j)]

lemma covBlock_self (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (a : ℝ) : covBlock sb a a = 0 := by
  ext i j
  simp [covBlock]

lemma covBlock_psd {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} {t : ℝ}
    (hpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    (hent : ∀ i j, IntegrableOn (fun σ => sb σ i j) (Set.Icc 0 t)) {a b : ℝ} (ha : 0 ≤ a)
    (hbt : b ≤ t) : (covBlock sb a b).PosSemidef := by
  have hsub : Set.Icc a b ⊆ Set.Icc 0 t := Set.Icc_subset_Icc ha hbt
  have hent' : ∀ i j, IntegrableOn (fun σ => sb σ i j) (Set.Icc a b) := fun i j =>
    (hent i j).mono_set hsub
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [covBlock, Matrix.of_apply, star_trivial]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have := (hpsd σ (hsub hσ)).1.apply i j
    simpa using this
  · intro x
    have e : star x ⬝ᵥ Matrix.mulVec (covBlock sb a b) x =
        ∫ σ in Set.Icc a b, star x ⬝ᵥ Matrix.mulVec (sb σ) x := by
      simp only [dotProduct, Matrix.mulVec, covBlock, Matrix.of_apply, star_trivial, Pi.star_apply]
      symm
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_finsetSum]
        · simp_rw [integral_mul_const]
        · intro j _
          exact (hent' i j).mul_const _
      · intro i _
        exact (integrable_finsetSum _ fun j _ => (hent' i j).mul_const _).const_mul _
    rw [e]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ => (hpsd σ (hsub hσ)).dotProduct_mulVec_nonneg x

lemma s1Norm_le_sum (Q : Matrix (Fin p) (Fin p) ℝ) : s1Norm Q ≤ ∑ i, ∑ j, |Q j i| := by
  unfold s1Norm traceNormMatrix
  refine ciSup_le fun U => ?_
  have hU : ∀ i j, |(U : Matrix (Fin p) (Fin p) ℝ) i j| ≤ 1 := by
    intro i j
    have := entry_norm_bound_of_unitary U.2 i j
    simpa using this
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  calc Q j i * (U : Matrix (Fin p) (Fin p) ℝ) j i ≤ |Q j i * (U : Matrix (Fin p) (Fin p) ℝ) j i| := le_abs_self _
    _ = |Q j i| * |(U : Matrix (Fin p) (Fin p) ℝ) j i| := abs_mul _ _
    _ ≤ |Q j i| * 1 := by gcongr; exact hU j i
    _ = |Q j i| := mul_one _

lemma s1Norm_sub_le (A B : Matrix (Fin p) (Fin p) ℝ) :
    s1Norm A ≤ s1Norm B + ∑ i, ∑ j, |A j i - B j i| := by
  have h1 := traceNormMatrix_add_le (A - B) B
  rw [sub_add_cancel] at h1
  have h2 := s1Norm_le_sum (A - B)
  simp only [Matrix.sub_apply] at h2
  change traceNormMatrix A ≤ _ at *
  linarith

lemma continuous_s1Norm : Continuous (fun Q : Matrix (Fin p) (Fin p) ℝ => s1Norm Q) := by
  rw [continuous_iff_continuousAt]
  intro B
  have hg : Continuous (fun A : Matrix (Fin p) (Fin p) ℝ => ∑ i, ∑ j, |A j i - B j i|) := by
    fun_prop
  have hg0 : Tendsto (fun A : Matrix (Fin p) (Fin p) ℝ => ∑ i, ∑ j, |A j i - B j i|) (𝓝 B) (𝓝 0) := by
    simpa using hg.tendsto B
  have hl : Tendsto (fun A : Matrix (Fin p) (Fin p) ℝ => s1Norm B - ∑ i, ∑ j, |A j i - B j i|) (𝓝 B)
      (𝓝 (s1Norm B)) := by simpa using tendsto_const_nhds.sub hg0
  have hu : Tendsto (fun A : Matrix (Fin p) (Fin p) ℝ => s1Norm B + ∑ i, ∑ j, |A j i - B j i|) (𝓝 B)
      (𝓝 (s1Norm B)) := by simpa using tendsto_const_nhds.add hg0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun A => ?_) (fun A => ?_)
  · have := s1Norm_sub_le B A
    have e : ∑ i, ∑ j, |B j i - A j i| = ∑ i, ∑ j, |A j i - B j i| :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => abs_sub_comm _ _
    simp only [e] at this
    linarith
  · exact s1Norm_sub_le A B

end LindebergAux

namespace LindebergAux

lemma mvG_second {G : Matrix (Fin p) (Fin p) ℝ} (hG : G.PosSemidef) (a b : Fin p) :
    ∫ y, y a * y b ∂(multivariateGaussian (0 : ℝ^p) G) = G a b := by
  set γ := multivariateGaussian (0 : ℝ^p) G with hγ
  have hmem : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hc : ∀ i : Fin p, MemLp (fun y : ℝ^p => y i) 2 γ := fun i =>
    (EuclideanSpace.proj i : (ℝ^p) →L[ℝ] ℝ).comp_memLp' hmem
  have hmean : ∀ i, ∫ y : ℝ^p, y i ∂γ = 0 := by
    intro i
    have h1 := ContinuousLinearMap.integral_comp_id_comm (μ := γ)
      (IsGaussian.integrable_id (μ := γ)) (EuclideanSpace.proj i : (ℝ^p) →L[ℝ] ℝ)
    simpa [hγ] using h1
  have := covariance_eval_multivariateGaussian (μ := (0 : ℝ^p)) hG a b
  rw [covariance_eq_sub (hc a) (hc b)] at this
  simpa [hmean, Pi.mul_apply] using this

lemma clm_expand (f : (ℝ^p) →L[ℝ] ℝ) (v : ℝ^p) :
    f v = ∑ i, v i * f (EuclideanSpace.single i 1) := by
  classical
  have hx : v = ∑ a, v a • (EuclideanSpace.single a (1 : ℝ) : ℝ^p) := by
    have := (EuclideanSpace.basisFun (Fin p) ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply] using this.symm
  conv_lhs => rw [hx]
  rw [map_sum]
  simp [map_smul]

lemma integrable_comp_memLp {f : (ℝ^p) → ℝ} (hf : ContDiff ℝ 2 f) {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ H) {X : Ω → ℝ^p} (hX : MemLp X 2 P) :
    Integrable (fun ω => f (X ω)) P := by
  have hn : Integrable (fun ω => ‖X ω‖) P := hX.norm.integrable one_le_two
  have hn2 : Integrable (fun ω => ‖X ω‖ ^ 2) P := hX.norm.integrable_sq
  have hg : Integrable (fun ω => |f 0| + ‖fderiv ℝ f 0‖ * ‖X ω‖ + H / 2 * ‖X ω‖ ^ 2) P := by
    exact ((integrable_const _).add (hn.const_mul _)).add (hn2.const_mul _)
  refine Integrable.mono' hg (hf.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  have h1 := taylor_two_bound hf hH 0 (X ω)
  rw [zero_add] at h1
  have h2 : |fderiv ℝ f 0 (X ω)| ≤ ‖fderiv ℝ f 0‖ * ‖X ω‖ := by
    have := (fderiv ℝ f 0).le_opNorm (X ω)
    rwa [← Real.norm_eq_abs]
  rw [Real.norm_eq_abs]
  have h3 := abs_sub_abs_le_abs_sub (f (X ω)) (f 0 + fderiv ℝ f 0 (X ω))
  have h4 := abs_add_le (f 0) (fderiv ℝ f 0 (X ω))
  have h5 : |f (X ω) - (f 0 + fderiv ℝ f 0 (X ω))| = |f (X ω) - f 0 - fderiv ℝ f 0 (X ω)| := by
    congr 1; ring
  linarith

lemma gauss_taylor_step {u : (ℝ^p) → ℝ} (hu : ContDiff ℝ 2 u) {H L : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ H)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤ L * ‖x - y‖)
    {G : Matrix (Fin p) (Fin p) ℝ} (hG : G.PosSemidef) (x : ℝ^p) :
    Integrable (taylorRem H L) (multivariateGaussian (0 : ℝ^p) G) ∧
    |gaussSmooth u G x - u x - (1 / 2) * ∑ a, ∑ b,
        iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single a 1, EuclideanSpace.single b 1] * G a b| ≤
      ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p) G) := by
  set γ := multivariateGaussian (0 : ℝ^p) G with hγ
  have hmem : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hy : Integrable (fun y : ℝ^p => y) γ := hmem.integrable (by norm_num)
  have hc : ∀ i : Fin p, MemLp (fun y : ℝ^p => y i) 2 γ := fun i =>
    (EuclideanSpace.proj i : (ℝ^p) →L[ℝ] ℝ).comp_memLp' hmem
  set B := iteratedFDeriv ℝ 2 u x with hB
  have pt : ∀ y, |u (x + y) - u x - fderiv ℝ u x y - (1 / 2) * B ![y, y]| ≤ taylorRem H L y :=
    fun y => taylor_two_remainder u hu H L hH hL x y
  have hint : Integrable (taylorRem H L) γ := by
    refine Integrable.mono' ((hmem.norm.integrable_sq).const_mul H)
      (continuous_taylorRem H L).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    have h0 : 0 ≤ taylorRem H L y := (abs_nonneg _).trans (pt y)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact taylorRem_le_left H L y
  refine ⟨hint, ?_⟩
  have i1 : Integrable (fun y => u (x + y)) γ := integrable_shift_gaussian hu hH γ x
  have i2 : Integrable (fun y => fderiv ℝ u x y) γ := (fderiv ℝ u x).integrable_comp hy
  have hq : ∀ y : ℝ^p, B ![y, y] = ∑ a, ∑ b, y a * y b * B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1] :=
    fun y => cmm_expand B y y
  have iq : ∀ a b : Fin p, Integrable (fun y : ℝ^p => y a * y b *
      B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1]) γ := fun a b =>
    ((hc a).integrable_mul (hc b)).mul_const _
  have i3 : Integrable (fun y => B ![y, y]) γ := by
    simp_rw [hq]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => iq a b
  have hlin : ∫ y, fderiv ℝ u x y ∂γ = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm hy (fderiv ℝ u x)]
    simp [hγ]
  have hquad : ∫ y, B ![y, y] ∂γ = ∑ a, ∑ b, B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1] * G a b := by
    simp_rw [hq]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => iq a b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => iq a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_mul_const, mvG_second hG a b]
    ring
  have hR : ∫ y, (u (x + y) - u x - fderiv ℝ u x y - (1 / 2) * B ![y, y]) ∂γ =
      gaussSmooth u G x - u x - (1 / 2) * ∑ a, ∑ b, B ![EuclideanSpace.single a 1, EuclideanSpace.single b 1] * G a b := by
    have hA : Integrable (fun y => u (x + y) - u x - fderiv ℝ u x y) γ :=
      (i1.sub (integrable_const _)).sub i2
    have hA' : Integrable (fun y => u (x + y) - u x) γ := i1.sub (integrable_const _)
    rw [integral_sub (f := fun y => u (x + y) - u x - fderiv ℝ u x y)
        (g := fun y => (1 / 2) * B ![y, y]) hA (i3.const_mul _),
      integral_sub (f := fun y => u (x + y) - u x) (g := fun y => fderiv ℝ u x y) hA' i2,
      integral_sub (f := fun y => u (x + y)) (g := fun _ => u x) i1 (integrable_const _),
      integral_const_mul, hquad, hlin]
    simp [gaussSmooth, hγ]
  rw [← hR, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hint (ae_of_all _ fun y => by simpa using pt y)

end LindebergAux

namespace LindebergAux

lemma s1Norm_neg_le (B : Matrix (Fin p) (Fin p) ℝ) : s1Norm (-B) ≤ s1Norm B := by
  unfold s1Norm traceNormMatrix
  refine ciSup_le fun U => ?_
  have hm : (-1 : Matrix (Fin p) (Fin p) ℝ) ∈ Matrix.orthogonalGroup (Fin p) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  have h := le_traceNormMatrix B (⟨-1, hm⟩ * U)
  have e : Matrix.trace ((-B).transpose * (U : Matrix (Fin p) (Fin p) ℝ)) =
      Matrix.trace (B.transpose * ((⟨-1, hm⟩ * U : Matrix.orthogonalGroup (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ)) := by
    simp
  rw [e]
  exact h

lemma s1Norm_sub_le_add (A B : Matrix (Fin p) (Fin p) ℝ) : s1Norm (A - B) ≤ s1Norm A + s1Norm B := by
  rw [sub_eq_add_neg]
  exact (traceNormMatrix_add_le A (-B)).trans (add_le_add_right (s1Norm_neg_le B) _)

lemma measurable_mat_sub {α : Type*} [MeasurableSpace α] {f g : α → Matrix (Fin p) (Fin p) ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x - g x) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hg))

lemma measurable_s1_sub {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hmeas : Measurable (Function.uncurry Sg)) {sb : ℝ → Matrix (Fin p) (Fin p) ℝ}
    (hsb : Measurable sb) :
    Measurable (fun q : Ω × ℝ => s1Norm (Sg q.2 q.1 - sb q.2)) := by
  have h1 : Measurable (fun q : Ω × ℝ => Sg q.2 q.1) := hmeas.comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℝ => sb q.2) := hsb.comp measurable_snd
  exact continuous_s1Norm.measurable.comp (measurable_mat_sub h1 h2)

omit [IsProbabilityMeasure P] in
lemma s1_sub_intOn (ℱ : Filtration ℝ mΩ) {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t)) :
    ∀ᵐ ω ∂P, IntegrableOn (fun σ => s1Norm (Sg σ ω - sb σ)) (Set.Icc 0 t) := by
  filter_upwards [hM.sigma_pathint] with ω hω
  refine Integrable.mono' (hω.add hsbint) ?_ (ae_of_all _ fun σ => ?_)
  · have h1 : Measurable (fun σ => Sg σ ω) :=
      hM.sigma_meas.comp (measurable_id.prodMk measurable_const)
    exact (continuous_s1Norm.measurable.comp (measurable_mat_sub h1 hsbmeas)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (traceNormMatrix_nonneg _)]
    exact s1Norm_sub_le_add _ _

lemma Iblk_integrable (ℱ : Filtration ℝ mΩ) {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t)) {c d : ℝ} (hc : 0 ≤ c)
    (hd : d ≤ t) :
    Integrable (fun ω => ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ)) P := by
  have hJ : Integrable (fun ω => (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω)) +
      ∫ σ in Set.Icc 0 t, s1Norm (sb σ)) P := hM.sigma_int.add (integrable_const _)
  refine Integrable.mono' hJ ?_ ?_
  · have hF := measurable_s1_sub hM.sigma_meas hsbmeas
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc c d))
      ).aestronglyMeasurable
  · filter_upwards [s1_sub_intOn P ℱ hM hsbmeas hsbint, hM.sigma_pathint] with ω h1 h2
    have hsub : Set.Icc c d ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hc hd
    have e0 : 0 ≤ ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ) :=
      setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg e0]
    calc ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ)
        ≤ ∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ) :=
          setIntegral_mono_set h1 (ae_of_all _ fun σ => traceNormMatrix_nonneg _)
            (Filter.Eventually.of_forall hsub)
      _ ≤ ∫ σ in Set.Icc 0 t, (s1Norm (Sg σ ω) + s1Norm (sb σ)) :=
          integral_mono h1 (h2.add hsbint) fun σ => s1Norm_sub_le_add _ _
      _ = _ := integral_add h2 hsbint

omit [IsProbabilityMeasure P] in
lemma pathwise_bound (ℱ : Filtration ℝ mΩ) {t : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef) {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ t) :
    ∀ᵐ ω ∂P, ∀ B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ^p) ℝ, ∀ H : ℝ, ‖B‖ ≤ H →
      |∑ i, ∑ j, B ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
          ((∫ σ in Set.Icc c d, Sg σ ω i j) - covBlock sb c d i j)| ≤
        H * ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ) := by
  filter_upwards [hM.sigma_entry_int, s1_sub_intOn P ℱ hM hsbmeas hsbint] with ω he hs B H hB
  have hsub : Set.Icc c d ⊆ Set.Icc 0 t := Set.Icc_subset_Icc hc hd
  have hsbe := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  have hQent : ∀ i j, IntegrableOn (fun σ => (Sg σ ω - sb σ) i j) (Set.Icc c d) := fun i j =>
    ((he i j).sub (hsbe i j)).mono_set hsub
  have hQn : IntegrableOn (fun σ => traceNormMatrix (Sg σ ω - sb σ)) (Set.Icc c d) :=
    hs.mono_set hsub
  have hcov : ∀ i j, covBlock (fun σ => Sg σ ω - sb σ) c d i j =
      (∫ σ in Set.Icc c d, Sg σ ω i j) - covBlock sb c d i j := by
    intro i j
    simp only [covBlock, Matrix.of_apply, Matrix.sub_apply]
    exact integral_sub ((he i j).mono_set hsub) ((hsbe i j).mono_set hsub)
  have h1 := hessian_trace_duality B (covBlock (fun σ => Sg σ ω - sb σ) c d)
  simp only [hcov] at h1
  refine h1.trans ?_
  have h2 := traceNorm_covBlock_le (fun σ => Sg σ ω - sb σ) c d hQent hQn
  have h3 : 0 ≤ ∫ σ in Set.Icc c d, traceNormMatrix (Sg σ ω - sb σ) :=
    setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  calc ‖B‖ * traceNormMatrix (covBlock (fun σ => Sg σ ω - sb σ) c d)
      ≤ ‖B‖ * ∫ σ in Set.Icc c d, traceNormMatrix (Sg σ ω - sb σ) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ H * ∫ σ in Set.Icc c d, s1Norm (Sg σ ω - sb σ) := mul_le_mul_of_nonneg_right hB h3

lemma sum_blocks_Icc {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : IntegrableOn f (Set.Icc 0 t)) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, (∫ σ in Set.Icc (unifPart t n k) (unifPart t n (k + 1)), f σ) =
      ∫ σ in Set.Icc 0 t, f σ := by
  have h := sum_blocks ht hf hn
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (unifPart_mono ht n (Nat.le_succ k))]

end LindebergAux

namespace LindebergAux

lemma partition_step (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t)
    (u : (ℝ^p) → ℝ) (hu : ContDiff ℝ 2 u) (H L : ℝ)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ H)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤ L * ‖x - y‖) :
    Integrable (fun ω => u (M b ω) - gaussSmooth u (covBlock sb a b) (M a ω)) P ∧
    |∫ ω, (u (M b ω) - gaussSmooth u (covBlock sb a b) (M a ω)) ∂P| ≤
      (1 / 2) * H * (∫ ω, (∫ σ in Set.Icc a b, s1Norm (Sg σ ω - sb σ)) ∂P) +
      ∫ ω, taylorRem H L (M b ω - M a ω) ∂P +
      ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p) (covBlock sb a b)) := by
  classical
  set G := covBlock sb a b with hG
  set γ := multivariateGaussian (0 : ℝ^p) G with hγ
  have hent := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  have hGpsd : G.PosSemidef := covBlock_psd hsbpsd hent ha hbt
  set v := gaussSmooth u G with hv
  obtain ⟨hv2, hvH, -⟩ := gaussSmooth_hessian G hGpsd u hu H hH
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hma : MemLp (M a) 2 P := hM.sq_int a ⟨ha, hab.trans hbt⟩
  have hmb : MemLp (M b) 2 P := hM.sq_int b ⟨ha.trans hab, hbt⟩
  have hca := memLp_coord P hma
  have hcb := memLp_coord P hmb
  set e : Fin p → ℝ^p := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- the pieces
  set Z : Fin p → Fin p → Ω → ℝ := fun i j ω => iteratedFDeriv ℝ 2 u (M a ω) ![e i, e j] with hZ
  set w : Fin p → Ω → ℝ := fun i ω => fderiv ℝ u (M a ω) (e i) with hw
  set y : Ω → ℝ^p := fun ω => M b ω - M a ω with hy
  set T1 : Ω → ℝ := fun ω => ∑ i, w i ω * y ω i with hT1
  set T2 : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω * (y ω i * y ω j) with hT2
  set T3 : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω * G i j with hT3
  set T4 : Ω → ℝ := fun ω => v (M a ω) - u (M a ω) - (1 / 2) * T3 ω with hT4
  have hmeasA : StronglyMeasurable[ℱ a] (M a) :=
    stronglyMeasurable_of_coord fun i => (hM.martingale i).1 a
  have hZmeas : ∀ i j, StronglyMeasurable[ℱ a] (Z i j) := by
    intro i j
    have hc : Continuous (fun x : ℝ^p => iteratedFDeriv ℝ 2 u x ![e i, e j]) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ^p) ℝ ![e i, e j]).continuous.comp
        (hu.continuous_iteratedFDeriv le_rfl)
    exact hc.comp_stronglyMeasurable hmeasA
  have hZK : ∀ i j ω, |Z i j ω| ≤ H := by
    intro i j ω
    have h1 := (iteratedFDeriv ℝ 2 u (M a ω)).le_opNorm ![e i, e j]
    simp only [Fin.prod_univ_two, he, PiLp.norm_single, Matrix.cons_val_zero,
      Matrix.cons_val_one, norm_one, mul_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hH _)
  have hwmeas : ∀ i, StronglyMeasurable[ℱ a] (w i) := by
    intro i
    have hc : Continuous (fun x : ℝ^p => fderiv ℝ u x (e i)) :=
      (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hc.comp_stronglyMeasurable hmeasA
  have hwL2 : ∀ i, MemLp (w i) 2 P := by
    intro i
    refine MemLp.mono' ((memLp_const (‖fderiv ℝ u 0‖)).add (hma.norm.const_mul H))
      ((hwmeas i).mono (ℱ.le a)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have h1 := (fderiv ℝ u (M a ω)).le_opNorm (e i)
    simp only [he, PiLp.norm_single, norm_one, mul_one] at h1
    have h2 := norm_fderiv_le_lin hu hH (M a ω)
    simp only [hw, Pi.add_apply]
    exact h1.trans h2
  have hyL2 : ∀ i, MemLp (fun ω => y ω i) 2 P := fun i => (hcb i).sub (hca i)
  have hcp := fun i j => cov_pair P ℱ t M Sg hM a b ha hab hbt (Z i j) (hZmeas i j) H (hZK i j) i j
  have iT1 : Integrable T1 P := integrable_finsetSum _ fun i _ => (hwL2 i).integrable_mul (hyL2 i)
  have iT2 : Integrable T2 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).1
  have iT3 : Integrable T3 P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_bdd_mul P ((hZmeas i j).mono (ℱ.le a)).aestronglyMeasurable (hZK i j)
        (integrable_const (G i j))
  have iub : Integrable (fun ω => u (M b ω)) P := integrable_comp_memLp P hu hH hmb
  have iua : Integrable (fun ω => u (M a ω)) P := integrable_comp_memLp P hu hH hma
  have iva : Integrable (fun ω => v (M a ω)) P := integrable_comp_memLp P hv2 hvH hma
  have iT4 : Integrable T4 P := (iva.sub iua).sub (iT3.const_mul _)
  set c := ∫ y, taylorRem H L y ∂γ with hc
  have hT4b : ∀ ω, |T4 ω| ≤ c := fun ω => (gauss_taylor_step hu hH hL hGpsd (M a ω)).2
  have hint_c : Integrable (taylorRem H L) γ := (gauss_taylor_step hu hH hL hGpsd 0).1
  set R1 : Ω → ℝ := fun ω => u (M b ω) - u (M a ω) - T1 ω - (1 / 2) * T2 ω with hR1
  have iR1 : Integrable R1 P := ((iub.sub iua).sub iT1).sub (iT2.const_mul _)
  have hR1b : ∀ ω, |R1 ω| ≤ taylorRem H L (y ω) := by
    intro ω
    have h := taylor_two_remainder u hu H L hH hL (M a ω) (y ω)
    have e1 : M a ω + y ω = M b ω := by simp [hy]
    have e2 : fderiv ℝ u (M a ω) (y ω) = T1 ω := by
      rw [clm_expand (fderiv ℝ u (M a ω)) (y ω)]
      simp only [hT1, hw, he]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have e3 : iteratedFDeriv ℝ 2 u (M a ω) ![y ω, y ω] = T2 ω := by
      rw [cmm_expand (iteratedFDeriv ℝ 2 u (M a ω)) (y ω) (y ω)]
      simp only [hT2, hZ, he]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, e2, e3] at h
    exact h
  have hD : (fun ω => u (M b ω) - v (M a ω)) =
      fun ω => R1 ω + T1 ω + (1 / 2) * T2 ω - (1 / 2) * T3 ω - T4 ω := by
    funext ω
    simp only [hR1, hT4]
    ring
  refine ⟨iub.sub iva, ?_⟩
  have e1 : ∫ ω, T1 ω ∂P = 0 := by
    have hi : ∀ i, ∫ ω, w i ω * y ω i ∂P = 0 := by
      intro i
      have h := integral_mul_martingale P ℱ (hM.martingale i) hab (hwmeas i) (hwL2 i) (hcb i)
      have i1 : Integrable (fun ω => w i ω * M b ω i) P := (hwL2 i).integrable_mul (hcb i)
      have i0 : Integrable (fun ω => w i ω * M a ω i) P := (hwL2 i).integrable_mul (hca i)
      have hfe : (fun ω => w i ω * y ω i) = fun ω => w i ω * M b ω i - w i ω * M a ω i := by
        funext ω; simp [hy, mul_sub]
      rw [hfe, integral_sub i1 i0, h, sub_self]
    simp only [hT1]
    rw [integral_finsetSum (f := fun i ω => w i ω * y ω i) _
      (fun i _ => (hwL2 i).integrable_mul (hyL2 i))]
    exact Finset.sum_eq_zero fun i _ => hi i
  set TA : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω * (∫ σ in Set.Icc a b, Sg σ ω i j) with hTA
  have iTA : Integrable TA P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).2.1
  have e2 : ∫ ω, T2 ω ∂P = ∫ ω, TA ω ∂P := by
    simp only [hT2, hTA]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).1),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hcp i j).2.1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hcp i j).1),
      integral_finsetSum _ (fun j _ => (hcp i j).2.1)]
    exact Finset.sum_congr rfl fun j _ => (hcp i j).2.2
  set T : Ω → ℝ := fun ω => ∑ i, ∑ j, Z i j ω *
    ((∫ σ in Set.Icc a b, Sg σ ω i j) - G i j) with hT
  have hTe : T = fun ω => TA ω - T3 ω := by
    funext ω
    simp only [hT, hTA, hT3, mul_sub, Finset.sum_sub_distrib]
  have hTint : ∫ ω, T ω ∂P = (∫ ω, TA ω ∂P) - ∫ ω, T3 ω ∂P := by
    rw [hTe]; exact integral_sub iTA iT3
  have hTb : |∫ ω, T ω ∂P| ≤ H * ∫ ω, (∫ σ in Set.Icc a b, s1Norm (Sg σ ω - sb σ)) ∂P := by
    have iI := Iblk_integrable P ℱ hM hsbmeas hsbint ha hbt (c := a) (d := b)
    have hpw := pathwise_bound P ℱ hM hsbmeas hsbint hsbpsd (c := a) (d := b) ha hbt
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (iI.const_mul H) ?_
    filter_upwards [hpw] with ω hω
    rw [Real.norm_eq_abs]
    exact hω (iteratedFDeriv ℝ 2 u (M a ω)) H (hH _)
  have hintD : ∫ ω, (u (M b ω) - v (M a ω)) ∂P =
      ∫ ω, R1 ω ∂P + 0 + (1 / 2) * (∫ ω, T ω ∂P) - ∫ ω, T4 ω ∂P := by
    rw [hD]
    have j1 : Integrable (fun ω => R1 ω + T1 ω) P := iR1.add iT1
    have j2 : Integrable (fun ω => R1 ω + T1 ω + (1 / 2) * T2 ω) P := j1.add (iT2.const_mul _)
    have j3 : Integrable (fun ω => R1 ω + T1 ω + (1 / 2) * T2 ω - (1 / 2) * T3 ω) P :=
      j2.sub (iT3.const_mul _)
    rw [integral_sub j3 iT4, integral_sub j2 (iT3.const_mul _), integral_add j1 (iT2.const_mul _),
      integral_add iR1 iT1, integral_const_mul, integral_const_mul, e1, e2, hTint]
    ring
  have itr : Integrable (fun ω => taylorRem H L (y ω)) P := by
    refine Integrable.mono' ((((hmb.sub hma).norm.integrable_sq)).const_mul H)
      ((continuous_taylorRem H L).comp_aestronglyMeasurable
        (hmb.sub hma).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ taylorRem H L (y ω) := (abs_nonneg _).trans (hR1b ω)
    simp only [Real.norm_eq_abs, abs_of_nonneg h0]
    exact taylorRem_le_left H L _
  have b1 : |∫ ω, R1 ω ∂P| ≤ ∫ ω, taylorRem H L (y ω) ∂P := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le itr (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hR1b ω)
  have b4 : |∫ ω, T4 ω ∂P| ≤ c := by
    rw [← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le (μ := P) (integrable_const c) (f := T4)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hT4b ω)
    simpa using this
  rw [hintD]
  have b1' := abs_le.1 b1
  have b4' := abs_le.1 b4
  have bT := abs_le.1 hTb
  show _ ≤ _ + ∫ ω, taylorRem H L (y ω) ∂P + c
  rw [abs_le]
  constructor <;> nlinarith [b1'.1, b1'.2, b4'.1, b4'.2, bT.1, bT.2]

end LindebergAux

/-- Steps 2-3 assembled: for `h ∈ C²` with `‖∇²h‖ ≤ H` and `L`-Lipschitz Hessian, and every
`n ≥ 1`, along `τ_k = k t / n`,
`|E h(M_t) - E h(G)| ≤ ½ H E ∫_0^t ‖Σ - sb‖_{S_1}
  + ∑_k (E min(H|ΔM_k|², L|ΔM_k|³) + ∫ min(H|y|², L|y|³) dN(0, ∫_{τ_k}^{τ_{k+1}} sb))`. -/
theorem lindeberg_partition_bound (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h) (H L : ℝ)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H)
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y‖ ≤ L * ‖x - y‖)
    (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, h (M t ω) ∂P - ∫ x, h x ∂(multivariateGaussian 0 (covBlock sb 0 t))| ≤
      (1 / 2) * H * ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P +
        ∑ k ∈ Finset.range n,
          (∫ ω, taylorRem H L (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω) ∂P +
            ∫ y, taylorRem H L y ∂(multivariateGaussian 0
              (covBlock sb (unifPart t n k) (unifPart t n (k + 1))))) := by
  classical
  have hent := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  set τ : ℕ → ℝ := unifPart t n with hτ
  have hτ0 : ∀ k, 0 ≤ τ k := unifPart_nonneg ht n
  have hτt : ∀ k, k ≤ n → τ k ≤ t := fun k hk => unifPart_le ht hk
  have hτm : ∀ k, τ k ≤ τ (k + 1) := fun k => unifPart_mono ht n (Nat.le_succ k)
  have hτn : τ n = t := unifPart_self t hn
  have hτz : τ 0 = 0 := by simp [hτ, unifPart]
  set Q : ℕ → Matrix (Fin p) (Fin p) ℝ := fun k => covBlock sb (τ k) t with hQ
  set u : ℕ → (ℝ^p) → ℝ := fun k => gaussSmooth h (Q k) with hu
  have hQpsd : ∀ k, (Q k).PosSemidef := fun k => covBlock_psd hsbpsd hent (hτ0 k) le_rfl
  have hQadd : ∀ k, k < n → Q k = covBlock sb (τ k) (τ (k + 1)) + Q (k + 1) := by
    intro k hk
    exact covBlock_add (hτm k) (hτt (k + 1) hk) (fun i j =>
      (hent i j).mono_set (Set.Icc_subset_Icc (hτ0 k) le_rfl))
  have hGpsd : ∀ k, k < n → (covBlock sb (τ k) (τ (k + 1))).PosSemidef := fun k hk =>
    covBlock_psd hsbpsd hent (hτ0 k) (hτt (k + 1) hk)
  have huprops := fun k => gaussSmooth_hessian (Q k) (hQpsd k) h hh H hH
  have hustep : ∀ k, k < n → ∀ x, u k x = gaussSmooth (u (k + 1))
      (covBlock sb (τ k) (τ (k + 1))) x := by
    intro k hk x
    have e := gaussSmooth_add (covBlock sb (τ k) (τ (k + 1))) (Q (k + 1)) (hGpsd k hk)
      (hQpsd (k + 1)) h hh H hH x
    rw [← hQadd k hk] at e
    exact e
  set D : ℕ → Ω → ℝ := fun k ω => u (k + 1) (M (τ (k + 1)) ω) - u k (M (τ k) ω) with hD
  have hstep : ∀ k, k < n → Integrable (D k) P ∧ |∫ ω, D k ω ∂P| ≤
      (1 / 2) * H * (∫ ω, (∫ σ in Set.Icc (τ k) (τ (k + 1)), s1Norm (Sg σ ω - sb σ)) ∂P) +
      ∫ ω, taylorRem H L (M (τ (k + 1)) ω - M (τ k) ω) ∂P +
      ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p) (covBlock sb (τ k) (τ (k + 1)))) := by
    intro k hk
    have := partition_step P ℱ t M Sg hM sb hsbmeas hsbint hsbpsd (τ k) (τ (k + 1)) (hτ0 k)
      (hτm k) (hτt (k + 1) hk) (u (k + 1)) (huprops (k + 1)).1 H L (huprops (k + 1)).2.1
      ((huprops (k + 1)).2.2 L hL)
    have hfe : (fun ω => u (k + 1) (M (τ (k + 1)) ω) -
        gaussSmooth (u (k + 1)) (covBlock sb (τ k) (τ (k + 1))) (M (τ k) ω)) = D k := by
      funext ω
      simp only [hD, hustep k hk]
    rw [hfe] at this
    exact this
  have iD : ∀ k ∈ Finset.range n, Integrable (D k) P := fun k hk =>
    (hstep k (Finset.mem_range.1 hk)).1
  have hun : u n = h := by
    have : Q n = 0 := by simp only [hQ, hτn, covBlock_self]
    simp only [hu, this, gaussSmooth_zero]
  have hu00 : u 0 0 = ∫ x, h x ∂(multivariateGaussian (0 : ℝ^p) (covBlock sb 0 t)) := by
    simp [hu, hQ, hτz, gaussSmooth]
  have hsum : (fun ω => h (M t ω) - u 0 0) =ᵐ[P] fun ω => ∑ k ∈ Finset.range n, D k ω := by
    filter_upwards [hM.zero] with ω h0
    have := Finset.sum_range_sub (fun k => u k (M (τ k) ω)) n
    simp only [hD]
    rw [this, hun, hτn, hτz]
    have h00 : M 0 ω = 0 := h0
    rw [h00]
  have ih : Integrable (fun ω => h (M t ω)) P :=
    integrable_comp_memLp P hh hH (hM.sq_int t ⟨ht, le_rfl⟩)
  have key : ∫ ω, h (M t ω) ∂P - ∫ x, h x ∂(multivariateGaussian (0 : ℝ^p) (covBlock sb 0 t)) =
      ∑ k ∈ Finset.range n, ∫ ω, D k ω ∂P := by
    rw [← hu00]
    have e1 : ∫ ω, (h (M t ω) - u 0 0) ∂P = ∫ ω, h (M t ω) ∂P - u 0 0 := by
      rw [integral_sub ih (integrable_const _)]; simp
    rw [← e1, integral_congr_ae hsum, integral_finsetSum _ iD]
  -- blockwise integrals of the s1 norm
  have hI : ∀ k ∈ Finset.range n, Integrable
      (fun ω => ∫ σ in Set.Icc (τ k) (τ (k + 1)), s1Norm (Sg σ ω - sb σ)) P := fun k hk =>
    Iblk_integrable P ℱ hM hsbmeas hsbint (hτ0 k) (hτt (k + 1) (Finset.mem_range.1 hk))
  have hIsum : ∑ k ∈ Finset.range n, (∫ ω, (∫ σ in Set.Icc (τ k) (τ (k + 1)),
      s1Norm (Sg σ ω - sb σ)) ∂P) = ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P := by
    rw [← integral_finsetSum _ hI]
    refine integral_congr_ae ?_
    filter_upwards [s1_sub_intOn P ℱ hM hsbmeas hsbint] with ω hω
    exact sum_blocks_Icc ht hω hn
  rw [key]
  calc |∑ k ∈ Finset.range n, ∫ ω, D k ω ∂P|
      ≤ ∑ k ∈ Finset.range n, |∫ ω, D k ω ∂P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, ((1 / 2) * H * (∫ ω, (∫ σ in Set.Icc (τ k) (τ (k + 1)),
          s1Norm (Sg σ ω - sb σ)) ∂P) +
          (∫ ω, taylorRem H L (M (τ (k + 1)) ω - M (τ k) ω) ∂P +
          ∫ y, taylorRem H L y ∂(multivariateGaussian (0 : ℝ^p)
            (covBlock sb (τ k) (τ (k + 1)))))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have := (hstep k (Finset.mem_range.1 hk)).2
        linarith
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hIsum]


end Lindeberg

end HRS

end

import HRS.MS.QsfFeat2

/-!
# S4.5 packet B5 (assembly), part 1: calculus of the finite-dimensional feature map

`s45_Yi N ψ c X = √N (μ_N(ψ) - c)` and `s45_Yv n N φ c X = ∑_{i<n} s45_Yi N (φ i) (c i) X • e_i ∈ ℝⁿ`
(the first `n` feature coordinates).  For `f ∈ C¹(ℝⁿ)`, `F = f ∘ s45_Yv` has
`dF(X) w = ∑_i (s45_L N (φ i) X w) ∂_i f(Y(X))` with `s45_L N ψ X w = (√N/N) ∑_k Dψ(X_k) w_k`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- `√N (μ_N(ψ) - c)`. -/
def s45_Yi (N : ℕ) (ψ : Euc d → ℝ) (c : ℝ) (X : EucConfig d N) : ℝ :=
  Real.sqrt N * (pair (empirical X) ψ - c)

/-- The derivative of `s45_Yi` in the configuration. -/
def s45_L (N : ℕ) (ψ : Euc d → ℝ) (X : EucConfig d N) : EucConfig d N →L[ℝ] ℝ :=
  ∑ k : Fin N, ((Real.sqrt N / N) • ((fderiv ℝ ψ (X k)).comp (ContinuousLinearMap.proj k)))

theorem s45_L_apply (ψ : Euc d → ℝ) (X w : EucConfig d N) :
    s45_L N ψ X w = (Real.sqrt N / N) * ∑ k, fderiv ℝ ψ (X k) (w k) := by
  simp [s45_L, Finset.mul_sum]

theorem s45_Yi_eq (hN : 1 ≤ N) (ψ : Euc d → ℝ) (c : ℝ) :
    s45_Yi N ψ c = fun X : EucConfig d N => (∑ k : Fin N, (Real.sqrt N / N) * ψ (X k)) -
      Real.sqrt N * c := by
  funext X
  have hN' : 0 < N := hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  unfold s45_Yi
  rw [pair_empirical hN', ← Finset.mul_sum]
  field_simp

theorem s45_Yi_hasFDerivAt (hN : 1 ≤ N) {ψ : Euc d → ℝ} (hψ : Differentiable ℝ ψ) (c : ℝ)
    (X : EucConfig d N) : HasFDerivAt (s45_Yi N ψ c) (s45_L N ψ X) X := by
  rw [s45_Yi_eq hN]
  have h : ∀ k : Fin N, HasFDerivAt (fun X : EucConfig d N => (Real.sqrt N / N) * ψ (X k))
      ((Real.sqrt N / N) • ((fderiv ℝ ψ (X k)).comp (ContinuousLinearMap.proj k))) X := by
    intro k
    have h1 : HasFDerivAt (fun X : EucConfig d N => ψ (X k))
        ((fderiv ℝ ψ (X k)).comp (ContinuousLinearMap.proj k)) X :=
      (hψ (X k)).hasFDerivAt.comp X (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) k).hasFDerivAt
    exact h1.const_mul _
  exact (HasFDerivAt.fun_sum (fun k _ => h k)).sub_const _

theorem s45_Yi_contDiff (hN : 1 ≤ N) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (c : ℝ) :
    ContDiff ℝ 1 (s45_Yi N ψ c : EucConfig d N → ℝ) := by
  rw [s45_Yi_eq hN]
  refine ContDiff.sub (ContDiff.sum fun k _ => contDiff_const.mul ?_) contDiff_const
  exact hψ.comp (contDiff_apply ℝ (Euc d) k)

theorem s45_L_bound {ψ : Euc d → ℝ} {D : ℝ} (hD : ∀ x, ‖fderiv ℝ ψ x‖ ≤ D) (hN : 1 ≤ N)
    (X w : EucConfig d N) : |s45_L N ψ X w| ≤ Real.sqrt N * D * ‖w‖ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [s45_L_apply, abs_mul, abs_of_nonneg (by positivity)]
  have h1 : |∑ k, fderiv ℝ ψ (X k) (w k)| ≤ N * (D * ‖w‖) := by
    calc _ ≤ ∑ k, |fderiv ℝ ψ (X k) (w k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, D * ‖w‖ := Finset.sum_le_sum fun k _ => by
          rw [← Real.norm_eq_abs]
          exact ((fderiv ℝ ψ (X k)).le_opNorm _).trans
            (mul_le_mul (hD _) (norm_le_pi_norm w k) (norm_nonneg _) ((norm_nonneg _).trans (hD (X k))))
      _ = _ := by simp
  calc Real.sqrt N / N * |∑ k, fderiv ℝ ψ (X k) (w k)| ≤ Real.sqrt N / N * (N * (D * ‖w‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

/-- The first `n` feature coordinates as a vector of `ℝⁿ`. -/
def s45_Yv (n N : ℕ) (φ : ℕ → Euc d → ℝ) (c : ℕ → ℝ) (X : EucConfig d N) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n, s45_Yi N (φ i) (c i) X • EuclideanSpace.single i (1 : ℝ)

theorem s45_Yv_apply (n N : ℕ) (φ : ℕ → Euc d → ℝ) (c : ℕ → ℝ) (X : EucConfig d N) (j : Fin n) :
    s45_Yv n N φ c X j = s45_Yi N (φ j) (c j) X := by
  simp [s45_Yv, Pi.single_apply]

theorem s45_Yv_hasFDerivAt (hN : 1 ≤ N) {n : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, Differentiable ℝ (φ i))
    (c : ℕ → ℝ) (X : EucConfig d N) :
    HasFDerivAt (s45_Yv n N φ c)
      (∑ i : Fin n, (s45_L N (φ i) X).smulRight (EuclideanSpace.single i (1 : ℝ))) X := by
  unfold s45_Yv
  exact HasFDerivAt.fun_sum fun i _ => (s45_Yi_hasFDerivAt hN (hφ i) (c i) X).smul_const _

theorem s45_Yv_contDiff (hN : 1 ≤ N) {n : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (c : ℕ → ℝ) : ContDiff ℝ 1 (s45_Yv n N φ c : EucConfig d N → EuclideanSpace ℝ (Fin n)) := by
  unfold s45_Yv
  exact ContDiff.sum fun i _ => (s45_Yi_contDiff hN (hφ i) (c i)).smul contDiff_const

theorem s45_F_fderiv (hN : 1 ≤ N) {n : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, Differentiable ℝ (φ i))
    (c : ℕ → ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Differentiable ℝ f) (X w : EucConfig d N) :
    fderiv ℝ (fun X => f (s45_Yv n N φ c X)) X w =
      ∑ i : Fin n, s45_L N (φ i) X w * fderiv ℝ f (s45_Yv n N φ c X) (EuclideanSpace.single i 1) := by
  have h := (hf (s45_Yv n N φ c X)).hasFDerivAt.comp X (s45_Yv_hasFDerivAt hN hφ c X)
  change fderiv ℝ (f ∘ s45_Yv n N φ c) X w = _
  rw [h.fderiv]
  simp [map_sum, map_smul]

theorem s45_F_contDiff (hN : 1 ≤ N) {n : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (c : ℕ → ℝ) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (fun X : EucConfig d N => f (s45_Yv n N φ c X)) :=
  (hf.of_le (by exact_mod_cast le_top)).comp (s45_Yv_contDiff hN hφ c)

theorem s45_F_fderiv_bound (hN : 1 ≤ N) {n : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, Differentiable ℝ (φ i))
    (c : ℕ → ℝ) {D : ℕ → ℝ} (hD : ∀ i x, ‖fderiv ℝ (φ i) x‖ ≤ D i)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Differentiable ℝ f) {Cf : ℝ}
    (hCf : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf) (X : EucConfig d N) :
    ‖fderiv ℝ (fun X => f (s45_Yv n N φ c X)) X‖ ≤ ∑ i : Fin n, Real.sqrt N * D i * Cf := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => ?_) fun w => ?_
  · have : 0 ≤ D i := (norm_nonneg _).trans (hD i 0)
    have : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
    positivity
  rw [s45_F_fderiv hN hφ c hf, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans' (le_of_eq (Real.norm_eq_abs _)) |>.trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have h1 := s45_L_bound (hD i) hN X w
  have h2 : |fderiv ℝ f (s45_Yv n N φ c X) (EuclideanSpace.single i 1)| ≤ Cf := by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ f _).le_opNorm _).trans ?_
    simpa using mul_le_mul_of_nonneg_right (hCf (s45_Yv n N φ c X)) (by simp : (0 : ℝ) ≤ ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖)
  calc |s45_L N (φ i) X w| * |fderiv ℝ f (s45_Yv n N φ c X) (EuclideanSpace.single i 1)|
      ≤ (Real.sqrt N * D i * ‖w‖) * Cf := mul_le_mul h1 h2 (abs_nonneg _)
        (by have := (norm_nonneg w); have : 0 ≤ D i := (norm_nonneg _).trans (hD i 0); positivity)
    _ = _ := by ring

end S45

end

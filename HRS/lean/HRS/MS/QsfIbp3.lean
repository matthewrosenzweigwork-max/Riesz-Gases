import HRS.MS.QsfIbp2

/-!
# S4.5 packet B2, part 3: summing the integration by parts over the coordinate directions (fixed `ε`)

For a vector field `v` on `ℝ^d` (differentiable, bounded, bounded derivative) and a functional `F` on `(ℝ^d)^N`
(differentiable, bounded, bounded derivative) the identity at fixed `ε ∈ (0,1]` is
`∫ w_ε [ (∑_k div v(x_k)) F + dF(v(X)) - β F dH_ε(v(X)) ] = 0` (`s45_sum_eps`), where
`dH_ε(v(X)) = ∑_i a⟨x_i, v(x_i)⟩ + N⁻¹ ∑_{i<j} ⟨∇g_ε(x_i-x_j), v(x_i) - v(x_j)⟩`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- The unit vector `e_{k,a}` of `(ℝ^d)^N`. -/
def s45_e (k : Fin N) (a : Fin d) : EucConfig d N := Pi.single k (EuclideanSpace.single a (1 : ℝ))

/-- The divergence `∑_a (∂_a v)_a`. -/
def s45_div (v : Euc d → Euc d) (x : Euc d) : ℝ :=
  ∑ a : Fin d, (fderiv ℝ v x (EuclideanSpace.single a (1 : ℝ))) a

theorem s45_e_apply_same (k : Fin N) (a : Fin d) : s45_e k a k = EuclideanSpace.single a (1 : ℝ) := by
  simp [s45_e]

theorem s45_norm_e_le (k : Fin N) (a : Fin d) : ‖(s45_e k a : EucConfig d N)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  by_cases h : i = k
  · subst h; simp [s45_e]
  · simp [s45_e, Pi.single_eq_of_ne h]

theorem s45_expand_vec (W : EucConfig d N) : W = ∑ k, ∑ a, W k a • s45_e k a := by
  ext k b
  simp [s45_e, Finset.sum_apply, Pi.single_apply, EuclideanSpace.single_apply]

theorem s45_clm_expand (ℓ : EucConfig d N →L[ℝ] ℝ) (W : EucConfig d N) :
    ℓ W = ∑ k, ∑ a, ℓ (s45_e k a) * W k a := by
  conv_lhs => rw [s45_expand_vec W]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem s45_hasFDerivAt_vk {v : Euc d → Euc d} (hv : Differentiable ℝ v) (k : Fin N) (a' : Fin d)
    (X : EucConfig d N) :
    HasFDerivAt (fun Y : EucConfig d N => v (Y k) a')
      ((EuclideanSpace.proj a' : Euc d →L[ℝ] ℝ).comp
        ((fderiv ℝ v (X k)).comp (ContinuousLinearMap.proj k : EucConfig d N →L[ℝ] Euc d))) X := by
  have h1 : HasFDerivAt (fun Y : EucConfig d N => Y k)
      (ContinuousLinearMap.proj k : EucConfig d N →L[ℝ] Euc d) X :=
    (ContinuousLinearMap.proj k : EucConfig d N →L[ℝ] Euc d).hasFDerivAt
  have h2 := (hv (X k)).hasFDerivAt.comp X h1
  exact (EuclideanSpace.proj a' : Euc d →L[ℝ] ℝ).hasFDerivAt.comp X h2

theorem s45_fderiv_G {v : Euc d → Euc d} (hv : Differentiable ℝ v) {F : EucConfig d N → ℝ}
    (hF : Differentiable ℝ F) (k : Fin N) (a' : Fin d) (X e : EucConfig d N) :
    fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X e =
      F X * (fderiv ℝ v (X k) (e k)) a' + v (X k) a' * fderiv ℝ F X e := by
  have h : HasFDerivAt (fun Y : EucConfig d N => F Y * v (Y k) a')
      (F X • (EuclideanSpace.proj a' : Euc d →L[ℝ] ℝ).comp
        ((fderiv ℝ v (X k)).comp (ContinuousLinearMap.proj k : EucConfig d N →L[ℝ] Euc d)) +
        (v (X k) a') • fderiv ℝ F X) X :=
    (hF X).hasFDerivAt.mul (s45_hasFDerivAt_vk hv k a' X)
  rw [h.fderiv]
  simp

theorem s45_differentiable_G {v : Euc d → Euc d} (hv : Differentiable ℝ v) {F : EucConfig d N → ℝ}
    (hF : Differentiable ℝ F) (k : Fin N) (a' : Fin d) :
    Differentiable ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') :=
  fun X => ((hF X).hasFDerivAt.mul (s45_hasFDerivAt_vk hv k a' X)).differentiableAt

theorem s45_abs_coord_le (y : Euc d) (a : Fin d) : |y a| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y a
  simpa [Real.norm_eq_abs] using this

/-- **The identity at fixed `ε ∈ (0,1]`.** -/
theorem s45_sum_eps {s a β : ℝ} (hs0 : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {v : Euc d → Euc d} (hv : Differentiable ℝ v) {Bv Dv : ℝ}
    (hBv : ∀ x, ‖v x‖ ≤ Bv) (hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ Dv) {F : EucConfig d N → ℝ}
    (hF : Differentiable ℝ F) {BF DF : ℝ} (hBF : ∀ X, |F X| ≤ BF)
    (hDF : ∀ X, ‖fderiv ℝ F X‖ ≤ DF) :
    ∫ X, s45_w s a β ε X * (((∑ k, s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) -
      β * (F X * (∑ i, a * ⟪X i, v (X i)⟫ + (1 / (N : ℝ)) *
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫))) = 0 := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hDv0 : 0 ≤ Dv := (norm_nonneg _).trans (hDv 0)
  have hBF0 : 0 ≤ BF := (abs_nonneg _).trans (hBF 0)
  have hDF0 : 0 ≤ DF := (norm_nonneg _).trans (hDF 0)
  have key : ∀ (k : Fin N) (a' : Fin d),
      Integrable (fun X => s45_w s a β ε X *
        fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a')) ∧
      Integrable (fun X => s45_w s a β ε X * (s45_dH s a ε X (s45_e k a') *
        (F X * v (X k) a'))) ∧
      ∫ X, s45_w s a β ε X * fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a') =
        β * ∫ X, s45_w s a β ε X * (s45_dH s a ε X (s45_e k a') * (F X * v (X k) a')) := by
    intro k a'
    refine s45_ibp_eps hs0 ha hβ hN hε hε1 (s45_differentiable_G hv hF k a') (s45_e k a')
      (K1 := BF * Bv) (K2 := BF * Dv + Bv * DF) (fun X => ?_) (fun X => ?_)
    · rw [abs_mul]
      exact mul_le_mul (hBF X) ((s45_abs_coord_le _ _).trans (hBv _)) (abs_nonneg _) hBF0
    · rw [s45_fderiv_G hv hF k a' X, s45_e_apply_same]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        refine mul_le_mul (hBF X) ?_ (abs_nonneg _) hBF0
        refine (s45_abs_coord_le _ _).trans ?_
        calc ‖fderiv ℝ v (X k) (EuclideanSpace.single a' (1 : ℝ))‖
            ≤ ‖fderiv ℝ v (X k)‖ * ‖EuclideanSpace.single a' (1 : ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ Dv * 1 := by
              rw [EuclideanSpace.norm_single]
              simp only [norm_one, mul_one]
              exact hDv _
          _ = Dv := mul_one _
      · rw [abs_mul]
        refine mul_le_mul ((s45_abs_coord_le _ _).trans (hBv _)) ?_ (abs_nonneg _) hBv0
        calc |fderiv ℝ F X (s45_e k a')| ≤ ‖fderiv ℝ F X (s45_e k a')‖ := by
              rw [← Real.norm_eq_abs]
          _ ≤ ‖fderiv ℝ F X‖ * ‖(s45_e k a' : EucConfig d N)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ DF * 1 := mul_le_mul (hDF X) (s45_norm_e_le k a') (norm_nonneg _) hDF0
          _ = DF := mul_one _
  -- pointwise algebra
  have hpt : ∀ X : EucConfig d N,
      s45_w s a β ε X * (((∑ k, s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k))) -
        β * (F X * (∑ i, a * ⟪X i, v (X i)⟫ + (1 / (N : ℝ)) *
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫))) =
      (∑ k, ∑ a', s45_w s a β ε X *
          fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a')) -
        β * ∑ k, ∑ a', s45_w s a β ε X * (s45_dH s a ε X (s45_e k a') * (F X * v (X k) a')) := by
    intro X
    have e1 : ∑ k : Fin N, ∑ a' : Fin d,
        fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a') =
        (∑ k, s45_div v (X k)) * F X + fderiv ℝ F X (fun k => v (X k)) := by
      simp_rw [s45_fderiv_G hv hF, s45_e_apply_same, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        unfold s45_div
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        ring
      · rw [s45_clm_expand (fderiv ℝ F X) (fun k => v (X k))]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a' _ => ?_
        ring
    have e2 : ∑ k : Fin N, ∑ a' : Fin d, s45_dH s a ε X (s45_e k a') * (F X * v (X k) a') =
        F X * (∑ i, a * ⟪X i, v (X i)⟫ + (1 / (N : ℝ)) *
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ⟪s45_F s ε (X i - X j), v (X i) - v (X j)⟫) := by
      rw [← s45_dH_apply s a ε X (fun k => v (X k)), s45_clm_expand (s45_dH s a ε X) (fun k => v (X k)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      ring
    have s1 : ∑ k : Fin N, ∑ a' : Fin d, s45_w s a β ε X *
        fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a') =
        s45_w s a β ε X * ∑ k : Fin N, ∑ a' : Fin d,
          fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a') := by
      simp only [← Finset.mul_sum]
    have s2 : ∑ k : Fin N, ∑ a' : Fin d, s45_w s a β ε X *
        (s45_dH s a ε X (s45_e k a') * (F X * v (X k) a')) =
        s45_w s a β ε X * ∑ k : Fin N, ∑ a' : Fin d,
          s45_dH s a ε X (s45_e k a') * (F X * v (X k) a') := by
      simp only [← Finset.mul_sum]
    rw [s1, s2, e1, e2]
    ring
  simp_rw [hpt]
  rw [integral_sub, integral_const_mul]
  · have h1 : ∫ X, ∑ k : Fin N, ∑ a' : Fin d, s45_w s a β ε X *
        fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a') =
        ∑ k : Fin N, ∑ a' : Fin d, ∫ X, s45_w s a β ε X *
          fderiv ℝ (fun Y : EucConfig d N => F Y * v (Y k) a') X (s45_e k a') := by
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun a' _ => (key k a').1)]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact integral_finsetSum _ fun a' _ => (key k a').1
    have h2 : ∫ X, ∑ k : Fin N, ∑ a' : Fin d, s45_w s a β ε X *
        (s45_dH s a ε X (s45_e k a') * (F X * v (X k) a')) =
        ∑ k : Fin N, ∑ a' : Fin d, ∫ X, s45_w s a β ε X *
          (s45_dH s a ε X (s45_e k a') * (F X * v (X k) a')) := by
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun a' _ => (key k a').2.1)]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact integral_finsetSum _ fun a' _ => (key k a').2.1
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [(key k a').2.2, sub_self]
  · exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun a' _ => (key k a').1
  · exact (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun a' _ => (key k a').2.1).const_mul β

end S45

end

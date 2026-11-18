import HRS.MS.FinNoiseAux27

/-!
# S8.6 `finite_noise`: the Araki-Yamagami inequality (S86)

`s86_araki_yamagami`: for Hilbert-Schmidt `X, Y : K →L F` and symmetric nonnegative `S, S'` with `S*S = X*X`,
`S'*S' = Y*Y` (as forms), `∑_j ‖(S - S') e_j‖² ≤ 2 ∑_j ‖(X - Y) e_j‖²`.  (The classical `‖|X| - |Y|‖₂ ≤ √2 ‖X - Y‖₂`.)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {ι : Type*} (e : HilbertBasis ι ℝ K)

theorem s86_araki_yamagami [Countable ι] (X Y : K →L[ℝ] F) (S S' : K →L[ℝ] K)
    (hS : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y)) (hS0 : ∀ x, 0 ≤ inner ℝ (S x) x)
    (hS' : ∀ x y, inner ℝ (S' x) y = inner ℝ x (S' y)) (hS'0 : ∀ x, 0 ≤ inner ℝ (S' x) x)
    (hSX : ∀ x y, inner ℝ (S x) (S y) = inner ℝ (X x) (X y))
    (hS'Y : ∀ x y, inner ℝ (S' x) (S' y) = inner ℝ (Y x) (Y y))
    (hX : Summable fun j => ‖X (e j)‖ ^ 2) (hY : Summable fun j => ‖Y (e j)‖ ^ 2) :
    Summable (fun j => ‖(S - S') (e j)‖ ^ 2) ∧ Summable (fun j => ‖(X - Y) (e j)‖ ^ 2) ∧
    ∑' j, ‖(S - S') (e j)‖ ^ 2 ≤ 2 * ∑' j, ‖(X - Y) (e j)‖ ^ 2 := by
  classical
  have hnX : ∀ x, ‖X x‖ = ‖S x‖ := fun x => by
    have h := hSX x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h).symm
  have hnY : ∀ x, ‖Y x‖ = ‖S' x‖ := fun x => by
    have h := hS'Y x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h).symm
  have hSs : Summable fun j => ‖S (e j)‖ ^ 2 := hX.congr fun j => by rw [hnX]
  have hS's : Summable fun j => ‖S' (e j)‖ ^ 2 := hY.congr fun j => by rw [hnY]
  obtain ⟨U, hU, hUS⟩ := s86_polar_map S X hnX
  obtain ⟨V, hV, hVS⟩ := s86_polar_map S' Y hnY
  set W : K →L[ℝ] K := (ContinuousLinearMap.adjoint U).comp V with hW
  have hWn : ‖W‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    nlinarith [norm_nonneg U, norm_nonneg V]
  have hkey := s86_key_ineq e hS hS0 hS' hS'0 hSs hS's hWn
  have hxeq : ∀ j, inner ℝ (X (e j)) (Y (e j)) = inner ℝ (S (e j)) ((W.comp S') (e j)) := fun j => by
    rw [← hUS (e j), ← hVS (e j)]
    simp only [hW, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hp := (s86_hsPair_formula e hSs hS's).1
  have hpXY : Summable fun j => inner ℝ (X (e j)) (Y (e j)) := by
    refine Summable.of_norm_bounded ((hX.add hY).mul_left (1 / 2 : ℝ)) (fun j => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [abs_real_inner_le_norm (X (e j)) (Y (e j)), norm_nonneg (X (e j)), norm_nonneg (Y (e j)),
      sq_nonneg (‖X (e j)‖ - ‖Y (e j)‖), abs_nonneg (inner ℝ (X (e j)) (Y (e j)))]
  have hdiffSX : Summable fun j => ‖(X - Y) (e j)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_) ((hX.add hY).mul_left 2)
    simp only [sub_apply]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (X (e j)) (Y (e j))) 2,
      sq_nonneg (‖X (e j)‖ - ‖Y (e j)‖)]
  have hdiffS : Summable fun j => ‖(S - S') (e j)‖ ^ 2 := s86_hs_sub_summable e hSs hS's
  refine ⟨hdiffS, hdiffSX, ?_⟩
  have e1 : ∑' j, ‖(S - S') (e j)‖ ^ 2 =
      (∑' j, ‖S (e j)‖ ^ 2) + (∑' j, ‖S' (e j)‖ ^ 2) - 2 * hsPair e S S' := by
    unfold hsPair
    rw [← tsum_mul_left, ← hSs.tsum_add hS's, ← (hSs.add hS's).tsum_sub (hp.mul_left 2)]
    refine tsum_congr fun j => ?_
    simp only [sub_apply]
    rw [norm_sub_sq_real]
    ring
  have e2 : ∑' j, ‖(X - Y) (e j)‖ ^ 2 =
      (∑' j, ‖S (e j)‖ ^ 2) + (∑' j, ‖S' (e j)‖ ^ 2) - 2 * hsPair e S (W.comp S') := by
    have hp2 := (s86_hsPair_formula e hSs (s86_hsS_comp_left e hS's W)).1
    unfold hsPair
    rw [← tsum_mul_left, ← hSs.tsum_add hS's, ← (hSs.add hS's).tsum_sub (hp2.mul_left 2)]
    refine tsum_congr fun j => ?_
    simp only [sub_apply]
    rw [norm_sub_sq_real, hxeq j, hnX, hnY]
    ring
  rw [e1, e2]
  linarith

end HRS.MS.FinNoise

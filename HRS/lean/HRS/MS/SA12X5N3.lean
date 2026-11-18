import HRS.MS.SA12X5N2
import HRS.MS.SA12X2R36J
import HRS.MS.ToriCoefAAux1

/-!
# S.A.12 X5 N3: pointwise Leibniz bound for the jets of `a' * ∂_j F` by the jets of `F` of order `N+1`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x5_norm_D1_le {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (j : Fin d) (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (D1 j F) x‖ ≤ ‖iteratedFDeriv ℝ (k + 1) F x‖ := by
  set L : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ)) with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    have := f.le_opNorm (EuclideanSpace.single j (1 : ℝ))
    simpa [hL] using this
  have hfd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have e : D1 j F = L ∘ fderiv ℝ F := rfl
  have h1 := L.norm_iteratedFDeriv_comp_left (f := fderiv ℝ F) (x := x) (N := (k : ℕ∞ω))
    (hfd.of_le (by exact_mod_cast le_top)).contDiffAt (n := k) le_rfl
  rw [e]
  refine h1.trans ?_
  rw [← norm_iteratedFDeriv_fderiv]
  calc ‖L‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ F) x‖ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ F) x‖ :=
        mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
    _ = _ := one_mul _

theorem sa12x5_sum_abs_sq (n : ℕ) (u : (Fin n → Fin d) → ℝ) :
    (∑ ι, |u ι|) ^ 2 ≤ (d : ℝ) ^ n * ∑ ι, u ι ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → Fin d))) (f := fun ι => |u ι|)
  simp only [sq_abs, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  exact_mod_cast h

theorem sa12x5_pd_prod_le (hd : 1 ≤ d) {N : ℕ} {a' F : Euc d → ℝ} (ha' : ContDiff ℝ N a') {Ba : ℝ}
    (hBa : 0 ≤ Ba) (hB : ∀ r ≤ N, ∀ x, ‖iteratedFDeriv ℝ r a' x‖ ≤ Ba) (hF : ContDiff ℝ ∞ F)
    (j : Fin d) (γ : Fin N → Fin d) (x : Euc d) :
    partialDeriv γ (fun y => a' y * D1 j F y) x ^ 2 ≤
      (4 ^ N * (d : ℝ) ^ (N + 1)) * Ba ^ 2 * sa12z3_Y (N + 1) F x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hDF : ContDiff ℝ N (D1 j F) :=
    ((hF.fderiv_right (m := ∞) (by simp)).of_le (by exact_mod_cast le_top)).clm_apply contDiff_const
  set Y : ℝ := sa12z3_Y (N + 1) F x with hY
  have hY0 : 0 ≤ Y := sa12z3_Y_nonneg (N + 1) F x
  set Z : ℝ := Real.sqrt ((d : ℝ) ^ (N + 1) * Y) with hZ
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hZ2 : Z ^ 2 = (d : ℝ) ^ (N + 1) * Y := Real.sq_sqrt (by positivity)
  have h1 : |partialDeriv γ (fun y => a' y * D1 j F y) x| ≤
      ‖iteratedFDeriv ℝ N (fun y => a' y * D1 j F y) x‖ := by
    unfold partialDeriv
    have := (iteratedFDeriv ℝ N (fun y => a' y * D1 j F y) x).le_opNorm
      (fun l => (EuclideanSpace.single (γ l) (1 : ℝ) : Euc d))
    simpa [PiLp.norm_single] using this
  have h2 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) ha' hDF x (n := N) le_rfl
  have hT : ∀ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ (N - i) (D1 j F) x‖ ≤ Z := by
    intro i hi
    have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    refine (sa12x5_norm_D1_le hF j (N - i) x).trans ?_
    refine (HRS.MS.ToriCoefA.tca_norm_iteratedFDeriv_le_sum (N - i + 1) F x).trans ?_
    refine Real.le_sqrt_of_sq_le ?_
    refine (sa12x5_sum_abs_sq (N - i + 1) (fun ι => partialDeriv ι F x)).trans ?_
    have hr : ∑ ι : Fin (N - i + 1) → Fin d, partialDeriv ι F x ^ 2 ≤ Y := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ γ : Fin r → Fin d, partialDeriv γ F x ^ 2)
        (fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _) (Finset.mem_range.2 (by omega : N - i + 1 < N + 1 + 1)))
      exact le_rfl
    have hp : (d : ℝ) ^ (N - i + 1) ≤ (d : ℝ) ^ (N + 1) := pow_le_pow_right₀ hd1 (by omega)
    exact mul_le_mul hp hr (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  have h3 : ‖iteratedFDeriv ℝ N (fun y => a' y * D1 j F y) x‖ ≤ 2 ^ N * Ba * Z := by
    refine h2.trans ?_
    calc ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * ‖iteratedFDeriv ℝ i a' x‖ *
          ‖iteratedFDeriv ℝ (N - i) (D1 j F) x‖
        ≤ ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * (Ba * Z) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul (hB i hi' x) (hT i hi) (norm_nonneg _) hBa
      _ = 2 ^ N * (Ba * Z) := by
          rw [← Finset.sum_mul]
          have : ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) = 2 ^ N := by
            exact_mod_cast Nat.sum_range_choose N
          rw [this]
      _ = _ := by ring
  have h4 : |partialDeriv γ (fun y => a' y * D1 j F y) x| ≤ 2 ^ N * Ba * Z := h1.trans h3
  have h5 : partialDeriv γ (fun y => a' y * D1 j F y) x ^ 2 ≤ (2 ^ N * Ba * Z) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h4 2
  have e4 : ((2 : ℝ) ^ N) ^ 2 = 4 ^ N := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h6 : (2 ^ N * Ba * Z) ^ 2 = (4 ^ N * (d : ℝ) ^ (N + 1)) * Ba ^ 2 * Y := by
    have e5 : (2 ^ N * Ba * Z) ^ 2 = ((2 : ℝ) ^ N) ^ 2 * Ba ^ 2 * Z ^ 2 := by ring
    rw [e5, e4, hZ2]; ring
  linarith

end HRS.MH.AdjointRd.Phase2SA12X5

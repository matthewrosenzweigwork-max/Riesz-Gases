import HRS.MS.CovMeasAux5
import HRS.MS.S111K4ATC

/-!
# S11.1 / all-tests boundary (S111K4AT), piece F: jets of the gradient pairing `x ↦ ⟨∇f, ∇h⟩`

`k4Gf f h x = ∑_k ∂_k f(x) ∂_k h(x)` equals `⟨∇f, ∇h⟩`; for `f,h ∈ C^{r+1}` with bounded jets (order `≤ r+1`) it is `C^r` with
jets of order `≤ r` bounded by `d 2^r b_f b_h`.  The difference `k4Gf f1 h1 - k4Gf f2 h2` is bounded by the jets of
`f1-f2` and `h1-h2` (Leibniz).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

/-- `∑_k ∂_k f ∂_k h`. -/
def k4Gf (f h : Euc d → ℝ) (x : Euc d) : ℝ := ∑ k : Fin d, s101Gk f k x * s101Gk h k x

theorem k4_inner_grad_eq (f h : Euc d → ℝ) (x : Euc d) :
    inner ℝ (gradient f x) (gradient h x) = k4Gf f h x := by
  have hc : ∀ g : Euc d → ℝ, ∀ k : Fin d, gradient g x k = s101Gk g k x := by
    intro g k
    have h1 : inner ℝ (gradient g x) (EuclideanSpace.single k (1 : ℝ)) = fderiv ℝ g x (EuclideanSpace.single k 1) := by
      unfold gradient
      rw [InnerProductSpace.toDual_symm_apply]
    have h2 : inner ℝ (gradient g x) (EuclideanSpace.single k (1 : ℝ)) = gradient g x k := by
      rw [EuclideanSpace.inner_single_right]
      simp
    unfold s101Gk
    exact h2.symm.trans h1
  simp only [PiLp.inner_apply, k4Gf, hc]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_comm]

theorem k4Gf_contDiff {f h : Euc d → ℝ} {r : ℕ} (hf : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) f)
    (hh : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) h) : ContDiff ℝ (r : WithTop ℕ∞) (k4Gf f h) := by
  unfold k4Gf
  exact ContDiff.sum fun k _ => (s101_Gk_contDiff hf k).mul (s101_Gk_contDiff hh k)

theorem k4Gf_bound {f h : Euc d → ℝ} {r : ℕ} (hf : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) f)
    (hh : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) h) {bf bh : ℝ}
    (hbf : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ bf)
    (hbh : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j h x‖ ≤ bh) :
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (k4Gf f h) x‖ ≤ (d : ℝ) * (2 ^ r * (bf * bh)) := by
  intro j hj x
  have hbf0 : 0 ≤ bf := (norm_nonneg _).trans (hbf 0 (Nat.zero_le _) x)
  have hbh0 : 0 ≤ bh := (norm_nonneg _).trans (hbh 0 (Nat.zero_le _) x)
  have hterm : ∀ k : Fin d, ‖iteratedFDeriv ℝ j (fun y => s101Gk f k y * s101Gk h k y) x‖ ≤
      2 ^ r * (bf * bh) := by
    intro k
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (s101_Gk_contDiff hf k) (s101_Gk_contDiff hh k) x
      (n := j) (by exact_mod_cast hj)
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => s101Gk f k y) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => s101Gk h k y) x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (bf * bh) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := by simpa [Nat.lt_succ_iff] using hi
          have a1 := s101_Gk_bound hf k hbf i (hi'.trans hj) x
          have a2 := s101_Gk_bound hh k hbh (j - i) ((Nat.sub_le _ _).trans hj) x
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 (norm_nonneg _) hbf0) (Nat.cast_nonneg _)
      _ = 2 ^ j * (bf * bh) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ r * (bf * bh) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hbf0 hbh0)
  have hsum : iteratedFDeriv ℝ j (k4Gf f h) x =
      ∑ k : Fin d, iteratedFDeriv ℝ j (fun y => s101Gk f k y * s101Gk h k y) x := by
    unfold k4Gf
    refine iteratedFDeriv_fun_sum_apply fun k _ => ?_
    exact ((s101_Gk_contDiff hf k).mul (s101_Gk_contDiff hh k)).contDiffAt.of_le (by exact_mod_cast hj)
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k : Fin d, ‖iteratedFDeriv ℝ j (fun y => s101Gk f k y * s101Gk h k y) x‖
      ≤ ∑ _k : Fin d, 2 ^ r * (bf * bh) := Finset.sum_le_sum fun k _ => hterm k
    _ = (d : ℝ) * (2 ^ r * (bf * bh)) := by simp

/-- Leibniz splitting of the difference of two gradient pairings. -/
theorem k4Gf_sub_eq {f1 f2 h1 h2 : Euc d → ℝ} (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2)
    (hh1 : Differentiable ℝ h1) (hh2 : Differentiable ℝ h2) :
    (fun x => k4Gf f1 h1 x - k4Gf f2 h2 x) =
      fun x => k4Gf (fun y => f1 y - f2 y) h1 x + k4Gf f2 (fun y => h1 y - h2 y) x := by
  funext x
  simp only [k4Gf, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : s101Gk (fun y => f1 y - f2 y) k x = s101Gk f1 k x - s101Gk f2 k x := by
    unfold s101Gk
    rw [fderiv_fun_sub (hf1 x) (hf2 x)]; rfl
  have e2 : s101Gk (fun y => h1 y - h2 y) k x = s101Gk h1 k x - s101Gk h2 k x := by
    unfold s101Gk
    rw [fderiv_fun_sub (hh1 x) (hh2 x)]; rfl
  rw [e1, e2]; ring

/-- Jets of a perturbation: `‖∂^j h1‖ ≤ ‖∂^j h2‖ + ‖∂^j (h1 - h2)‖`. -/
theorem k4_iter_le_add {f g : Euc d → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) {i : ℕ}
    (hi : i ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ ‖iteratedFDeriv ℝ i g x‖ + ‖iteratedFDeriv ℝ i (fun y => f y - g y) x‖ := by
  have e : f = g + fun y => f y - g y := by funext y; simp
  have h1 : ContDiffAt ℝ i g x := (hg.of_le (by exact_mod_cast hi)).contDiffAt
  have h2 : ContDiffAt ℝ i (fun y => f y - g y) x := ((hf.sub hg).of_le (by exact_mod_cast hi)).contDiffAt
  have h3 := iteratedFDeriv_add_apply h1 h2
  calc ‖iteratedFDeriv ℝ i f x‖ = ‖iteratedFDeriv ℝ i (g + fun y => f y - g y) x‖ := by rw [← e]
    _ = ‖iteratedFDeriv ℝ i g x + iteratedFDeriv ℝ i (fun y => f y - g y) x‖ := by rw [h3]
    _ ≤ _ := norm_add_le _ _

end HRS.MS.S111K4AT

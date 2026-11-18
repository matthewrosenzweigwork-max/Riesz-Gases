import HRS.Whole.Round2
import HRS.Whole.Dynamics

/-!
# S2.1(iii) packet 31a: growth and local Lipschitz bounds for the finite-rank quadratic polynomial

For finite-rank data `c u` (`IsR2FiniteRankData c u`) and the oscillator path space
`OscPath d (wholeSpaceIndex d) H`, with evaluation `ev x t f = OscDual.eval (OscPath.at' x t) f`,
the polynomial `fp81s21_quadPoly c u x t = (1/2) * ∑ i, ∑ j, c i j * ev x t (u i) * ev x t (u j)`
satisfies bounds with the constant `fp81s21_quadK c u`, which depends only on `c` and `u`
(not on `x`, `t`, `H`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS.Whole

variable {d : ℕ}

/-- Each finite-rank test function is an oscillator test (smooth and compactly supported). -/
theorem fp81s21_isOscTest_of_r2 {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) (i : Fin m) :
    IsOscTest ((wholeSpaceIndex d : ℕ) : ℝ) (u i) :=
  ⟨hu.smooth i, memOsc_schwartz _ ((hu.compactSupport i).toSchwartzMap (hu.smooth i))⟩

theorem fp81s21_oscNorm_nonneg (m : ℝ) (f : Euc d → ℝ) : 0 ≤ oscNorm m f := by
  unfold oscNorm
  exact Real.sqrt_nonneg _

/-- Evaluation at time `t` is bounded by the sup norm of the path. -/
theorem fp81s21_norm_at_le {m H : ℝ} (x : OscPath d m H) (t : Set.Icc (0 : ℝ) H) :
    ‖OscPath.at' x t‖ ≤ ‖x‖ :=
  ContinuousMap.norm_coe_le_norm x t

/-- `|ev x t f| ≤ ‖x‖ · ‖f‖_{Σ^m}` for an oscillator test `f`. -/
theorem fp81s21_abs_eval_le {m H : ℝ} (x : OscPath d m H) (t : Set.Icc (0 : ℝ) H)
    (f : Euc d → ℝ) (hf : MemOsc m f) :
    |OscDual.eval (OscPath.at' x t) f| ≤ ‖x‖ * oscNorm m f :=
  (OscDual.abs_eval_le (OscPath.at' x t) f hf).trans
    (mul_le_mul_of_nonneg_right (fp81s21_norm_at_le x t) (fp81s21_oscNorm_nonneg m f))

/-- The pairing is linear in the dual element (on `Σ^m` test functions). -/
theorem fp81s21_eval_sub {m : ℝ} (u v : OscDual d m) (f : Euc d → ℝ) (hf : MemOsc m f) :
    OscDual.eval (u - v) f = OscDual.eval u f - OscDual.eval v f := by
  rw [← OscDual.toDual_ofFun (u - v) f hf, ← OscDual.toDual_ofFun u f hf,
    ← OscDual.toDual_ofFun v f hf]
  first
  | exact congrArg (fun L : StrongDual ℝ (OscSpace d m) => L (OscSpace.ofFun m f))
      (map_sub OscDual.toDual u v)
  | simp [map_sub]

/-- Difference bound: `|ev x t f - ev y t f| ≤ ‖x - y‖ · ‖f‖_{Σ^m}`. -/
theorem fp81s21_abs_eval_sub_le {m H : ℝ} (x y : OscPath d m H) (t : Set.Icc (0 : ℝ) H)
    (f : Euc d → ℝ) (hf : MemOsc m f) :
    |OscDual.eval (OscPath.at' x t) f - OscDual.eval (OscPath.at' y t) f|
      ≤ ‖x - y‖ * oscNorm m f := by
  rw [← fp81s21_eval_sub (OscPath.at' x t) (OscPath.at' y t) f hf]
  have hsub : OscPath.at' (x - y) t = OscPath.at' x t - OscPath.at' y t := by
    first
    | rfl
    | exact ContinuousMap.sub_apply x y t
  calc |OscDual.eval (OscPath.at' x t - OscPath.at' y t) f|
      = |OscDual.eval (OscPath.at' (x - y) t) f| := by rw [hsub]
    _ ≤ ‖OscPath.at' (x - y) t‖ * oscNorm m f := OscDual.abs_eval_le (OscPath.at' (x - y) t) f hf
    _ ≤ ‖x - y‖ * oscNorm m f :=
        mul_le_mul_of_nonneg_right (fp81s21_norm_at_le (x - y) t) (fp81s21_oscNorm_nonneg m f)

/-- The H-independent constant `K = (1/2) ∑_i ∑_j |c i j| C_i C_j`, where
`C_i = oscNorm (wholeSpaceIndex d) (u i)` is the Σ^m-norm of the test function `u i`. -/
def fp81s21_quadK {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, |c i j| * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u i)
    * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u j)

/-- The quadratic polynomial `(1/2) ∑_i ∑_j c i j * ev x t (u i) * ev x t (u j)`,
with `ev x t f = OscDual.eval (OscPath.at' x t) f`. -/
def fp81s21_quadPoly {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ) {H : ℝ}
    (x : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) H) (t : Set.Icc (0 : ℝ) H) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * OscDual.eval (OscPath.at' x t) (u i)
    * OscDual.eval (OscPath.at' x t) (u j)

/-- Bilinear sum estimate: `|∑_i ∑_j c i j α_i β_j| ≤ ∑_i ∑_j |c i j| A_i B_j`. -/
theorem fp81s21_bil_abs_le {m : ℕ} (c : Fin m → Fin m → ℝ) (α β A B : Fin m → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hα : ∀ i, |α i| ≤ A i) (hβ : ∀ j, |β j| ≤ B j) :
    |∑ i, ∑ j, c i j * α i * β j| ≤ ∑ i, ∑ j, |c i j| * (A i * B j) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_mul]
  calc |c i j| * |α i| * |β j| = |c i j| * (|α i| * |β j|) := by ring
    _ ≤ |c i j| * (A i * B j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hα i) (hβ j) (abs_nonneg _) (hA i)) (abs_nonneg _)

theorem fp81s21_quadK_nonneg {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ) :
    0 ≤ fp81s21_quadK c u := by
  unfold fp81s21_quadK
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (fp81s21_oscNorm_nonneg _ _))
    (fp81s21_oscNorm_nonneg _ _)

/-- Growth bound (1): `|fp81s21_quadPoly c u x t| ≤ K ‖x‖²`, with `K` independent of `x`, `t`, `H`. -/
theorem fp81s21_quadPoly_bound {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) {H : ℝ} (x : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) H)
    (t : Set.Icc (0 : ℝ) H) :
    |fp81s21_quadPoly c u x t| ≤ fp81s21_quadK c u * ‖x‖ ^ 2 := by
  have hG := fp81s21_bil_abs_le c (fun i => OscDual.eval (OscPath.at' x t) (u i))
    (fun i => OscDual.eval (OscPath.at' x t) (u i))
    (fun i => ‖x‖ * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u i))
    (fun i => ‖x‖ * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u i))
    (fun i => mul_nonneg (norm_nonneg _) (fp81s21_oscNorm_nonneg _ _))
    (fun i => fp81s21_abs_eval_le x t (u i) (fp81s21_isOscTest_of_r2 hu i).2)
    (fun i => fp81s21_abs_eval_le x t (u i) (fp81s21_isOscTest_of_r2 hu i).2)
  have hid : ∑ i, ∑ j, |c i j| * (‖x‖ * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u i)
      * (‖x‖ * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u j)))
      = (∑ i, ∑ j, |c i j| * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u i)
          * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u j)) * ‖x‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold fp81s21_quadPoly fp81s21_quadK
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine le_trans (mul_le_mul_of_nonneg_left (hG.trans (le_of_eq hid))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)) (le_of_eq ?_)
  ring

/-- Time-sup form of the growth bound: `⨆ t, |fp81s21_quadPoly c u x t| ≤ K ‖x‖²`. -/
theorem fp81s21_quadPoly_sup_bound {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) {H : ℝ} (x : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) H) :
    (⨆ t : Set.Icc (0 : ℝ) H, |fp81s21_quadPoly c u x t|) ≤ fp81s21_quadK c u * ‖x‖ ^ 2 :=
  Real.iSup_le (fun t => fp81s21_quadPoly_bound hu x t)
    (mul_nonneg (fp81s21_quadK_nonneg c u) (sq_nonneg _))

/-- Generic difference estimate: with `|a i| ≤ X C_i`, `|a' i| ≤ Y C_i`, `|a i - a' i| ≤ D C_i`,
`|∑∑ c a_i a_j - ∑∑ c a'_i a'_j| ≤ (∑∑ |c| C_i C_j) ((X+Y) D)`. -/
theorem fp81s21_quad_lip_generic {m : ℕ} (c : Fin m → Fin m → ℝ) (a a' Cu : Fin m → ℝ)
    (X Y D : ℝ) (hCu : ∀ i, 0 ≤ Cu i) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (ha : ∀ i, |a i| ≤ X * Cu i) (ha' : ∀ i, |a' i| ≤ Y * Cu i)
    (hd : ∀ i, |a i - a' i| ≤ D * Cu i) :
    |∑ i, ∑ j, c i j * a i * a j - ∑ i, ∑ j, c i j * a' i * a' j|
      ≤ (∑ i, ∑ j, |c i j| * Cu i * Cu j) * ((X + Y) * D) := by
  have hsplit : ∑ i, ∑ j, c i j * a i * a j - ∑ i, ∑ j, c i j * a' i * a' j
      = ∑ i, ∑ j, c i j * (a i - a' i) * a j + ∑ i, ∑ j, c i j * a' i * (a j - a' j) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h1 := fp81s21_bil_abs_le c (fun i => a i - a' i) a (fun i => D * Cu i) (fun j => X * Cu j)
    (fun i => mul_nonneg hD (hCu i)) hd ha
  have h2 := fp81s21_bil_abs_le c a' (fun j => a j - a' j) (fun i => Y * Cu i)
    (fun j => D * Cu j) (fun i => mul_nonneg hY (hCu i)) ha' hd
  have hid : ∑ i, ∑ j, |c i j| * (D * Cu i * (X * Cu j))
      + ∑ i, ∑ j, |c i j| * (Y * Cu i * (D * Cu j))
      = (∑ i, ∑ j, |c i j| * Cu i * Cu j) * ((X + Y) * D) := by
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  calc |∑ i, ∑ j, c i j * (a i - a' i) * a j + ∑ i, ∑ j, c i j * a' i * (a j - a' j)|
      ≤ |∑ i, ∑ j, c i j * (a i - a' i) * a j| + |∑ i, ∑ j, c i j * a' i * (a j - a' j)| :=
        abs_add_le _ _
    _ ≤ (∑ i, ∑ j, |c i j| * (D * Cu i * (X * Cu j)))
          + ∑ i, ∑ j, |c i j| * (Y * Cu i * (D * Cu j)) := add_le_add h1 h2
    _ = (∑ i, ∑ j, |c i j| * Cu i * Cu j) * ((X + Y) * D) := hid

/-- Local Lipschitz bound (2): `|fp81s21_quadPoly c u x t - fp81s21_quadPoly c u y t|
≤ K (‖x‖ + ‖y‖) ‖x - y‖`, with the same `K` as in the growth bound. -/
theorem fp81s21_quadPoly_lip {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) {H : ℝ} (x y : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) H)
    (t : Set.Icc (0 : ℝ) H) :
    |fp81s21_quadPoly c u x t - fp81s21_quadPoly c u y t|
      ≤ fp81s21_quadK c u * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hL := fp81s21_quad_lip_generic c (fun i => OscDual.eval (OscPath.at' x t) (u i))
    (fun i => OscDual.eval (OscPath.at' y t) (u i))
    (fun i => oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (u i)) ‖x‖ ‖y‖ ‖x - y‖
    (fun i => fp81s21_oscNorm_nonneg _ _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (fun i => fp81s21_abs_eval_le x t (u i) (fp81s21_isOscTest_of_r2 hu i).2)
    (fun i => fp81s21_abs_eval_le y t (u i) (fp81s21_isOscTest_of_r2 hu i).2)
    (fun i => fp81s21_abs_eval_sub_le x y t (u i) (fp81s21_isOscTest_of_r2 hu i).2)
  have hdiff : fp81s21_quadPoly c u x t - fp81s21_quadPoly c u y t
      = (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * OscDual.eval (OscPath.at' x t) (u i)
          * OscDual.eval (OscPath.at' x t) (u j)
        - ∑ i, ∑ j, c i j * OscDual.eval (OscPath.at' y t) (u i)
          * OscDual.eval (OscPath.at' y t) (u j)) := by
    unfold fp81s21_quadPoly
    ring
  rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine le_trans (mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 1 / 2)) (le_of_eq ?_)
  unfold fp81s21_quadK
  ring

/-- Time-sup form of the local Lipschitz bound:
`⨆ t, |fp81s21_quadPoly c u x t - fp81s21_quadPoly c u y t| ≤ K (‖x‖ + ‖y‖) ‖x - y‖`. -/
theorem fp81s21_quadPoly_sup_lip {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}
    (hu : IsR2FiniteRankData c u) {H : ℝ} (x y : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) H) :
    (⨆ t : Set.Icc (0 : ℝ) H, |fp81s21_quadPoly c u x t - fp81s21_quadPoly c u y t|)
      ≤ fp81s21_quadK c u * (‖x‖ + ‖y‖) * ‖x - y‖ :=
  Real.iSup_le (fun t => fp81s21_quadPoly_lip hu x y t)
    (mul_nonneg (mul_nonneg (fp81s21_quadK_nonneg c u)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_quadPoly_bound
#print axioms HRS.Fp81.S21.fp81s21_quadPoly_sup_bound
#print axioms HRS.Fp81.S21.fp81s21_quadPoly_lip
#print axioms HRS.Fp81.S21.fp81s21_quadPoly_sup_lip

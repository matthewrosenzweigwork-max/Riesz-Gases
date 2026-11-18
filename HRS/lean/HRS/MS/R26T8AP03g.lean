import HRS.MS.R26T8AP03f

/-!
# S8.2 local Newton layer, packet T8A.P03 (part g): scale-invariant bound of the Newton kernel jets
For `y/lam <= |u| <= lam y`: `|D^q K(u)| <= C lam^(d+k) (1+log lam) y^(2-d-q) (1+|log y| if d=2, q=0)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_abs_log_le {x y lam : ℝ} (hx : 0 < x) (hy : 0 < y) (hl : 1 ≤ lam) (h1 : y / lam ≤ x)
    (h2 : x ≤ lam * y) : |Real.log x| ≤ |Real.log y| + Real.log lam := by
  have hl0 : 0 < lam := by linarith
  have hll : 0 ≤ Real.log lam := Real.log_nonneg hl
  have a1 : Real.log x ≤ Real.log lam + Real.log y := by
    rw [← Real.log_mul hl0.ne' hy.ne']; exact Real.log_le_log hx h2
  have a2 : Real.log y - Real.log lam ≤ Real.log x := by
    rw [← Real.log_div hy.ne' hl0.ne']; exact Real.log_le_log (by positivity) h1
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log y)]
  · linarith [le_abs_self (Real.log y)]

theorem r26t8a_kernel_scale (d : ℕ) (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → ∀ lam : ℝ, 1 ≤ lam → ∀ q : ℕ, q ≤ k → ∀ u : Euc d,
      y / lam ≤ ‖u‖ → ‖u‖ ≤ lam * y →
      ‖iteratedFDeriv ℝ q (newtonKernel d nu) u‖ ≤
        C * lam ^ ((d : ℝ) + k) * (1 + Real.log lam) * y ^ (2 - (d : ℝ) - q) *
          (if d = 2 ∧ q = 0 then 1 + |Real.log y| else 1) := by
  obtain ⟨C2, hC20, -, hC2⟩ := r26t8a_newton_kernel_jets d hd nu hnu k
  refine ⟨C2, hC20, fun y hy lam hl q hq u h1 h2 => ?_⟩
  have hl0 : 0 < lam := by linarith
  have hll : 0 ≤ Real.log lam := Real.log_nonneg hl
  have hyl : 0 < y / lam := by positivity
  have hu : 0 < ‖u‖ := lt_of_lt_of_le hyl h1
  have hu0 : u ≠ 0 := norm_pos_iff.1 hu
  have hb := hC2 q hq u hu0
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 2 - (d : ℝ) - q ≤ 0 := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg _; linarith
  have hqk : (q : ℝ) ≤ k := by exact_mod_cast hq
  -- radial factor
  have hrad : ‖u‖ ^ (2 - (d : ℝ) - q) ≤ lam ^ ((d : ℝ) + k) * y ^ (2 - (d : ℝ) - q) := by
    refine (Real.rpow_le_rpow_of_nonpos hyl h1 he).trans ?_
    rw [Real.div_rpow hy.le hl0.le, div_eq_mul_inv, ← Real.rpow_neg hl0.le, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy.le _)
    exact Real.rpow_le_rpow_of_exponent_le hl (by linarith)
  have hLnn : 0 ≤ (if d = 2 ∧ q = 0 then 1 + |Real.log y| else (1 : ℝ)) := by
    split_ifs
    · positivity
    · exact zero_le_one
  have hlog : (if d = 2 ∧ q = 0 then 1 + |Real.log ‖u‖| else (1 : ℝ)) ≤
      (1 + Real.log lam) * (if d = 2 ∧ q = 0 then 1 + |Real.log y| else 1) := by
    split_ifs
    · have := r26t8a_abs_log_le hu hy hl h1 h2
      nlinarith [abs_nonneg (Real.log y)]
    · linarith
  have hrn : 0 ≤ ‖u‖ ^ (2 - (d : ℝ) - q) := Real.rpow_nonneg hu.le _
  calc _ ≤ C2 * ‖u‖ ^ (2 - (d : ℝ) - q) * (if d = 2 ∧ q = 0 then 1 + |Real.log ‖u‖| else 1) := hb
    _ ≤ C2 * (lam ^ ((d : ℝ) + k) * y ^ (2 - (d : ℝ) - q)) *
          ((1 + Real.log lam) * (if d = 2 ∧ q = 0 then 1 + |Real.log y| else 1)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hrad hC20) hlog ?_ (by positivity)
        split_ifs
        · positivity
        · exact zero_le_one
    _ = _ := by ring

end HRS.MS.R26T8A

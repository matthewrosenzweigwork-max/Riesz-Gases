import HRS.MS.R26T8AP07p
import HRS.MS.R26T8AP06b

/-!
# S8.2 local Newton layer, packet T8A.P07 (part q): smoothness of the dyadic series
`r26t8a_p07_N_contDiffOn` (`0 <= sigma < d`): `(Y,w) |-> sum_n annularNewton (1/2)^n F Y w` is `C^k` on `{0 < |w| < 3}`
(joint jets of the pieces are controlled by the nested ones, `r26t8a_joint_le_nest`, and `r26t8a_p07_contDiffOn_tsum` is applied on small balls).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_N_contDiffOn (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {A : ℝ} (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ}
    (hF : ConormalP k b M σ A F) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d =>
      ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2)
      {Yw : Euc d × Euc d | 0 < ‖Yw.2‖ ∧ ‖Yw.2‖ < 3} := by
  have hV : ∀ n : ℕ, ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d =>
      r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) := fun n =>
    r26t8a_p07_T_contDiff hd nu hchi (by positivity) hF.1
  have hopen : IsOpen {Yw : Euc d × Euc d | 0 < ‖Yw.2‖ ∧ ‖Yw.2‖ < 3} :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  obtain ⟨hx0, hx3⟩ := hx
  obtain ⟨r, hr0, -, -, Φ, hΦ0, hΦ, hΦb⟩ :=
    r26t8a_p07_majorant hd k b nu M σ hnu hM hσd hchi A hA F hF x.1 x.2 hx0 hx3.le
  refine ⟨ball x r, isOpen_ball, mem_ball_self hr0, (r26t8a_p07_contDiffOn_tsum x r k _ hV ?_).mono
    Set.inter_subset_right⟩
  intro i hi
  refine ⟨fun n => 2 ^ i * Φ n, hΦ.mul_left _, fun n y hy => ?_⟩
  have hd2 : dist y.1 x.1 < r ∧ dist y.2 x.2 < r := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hy; exact hy
  have hY : ‖y.1 - x.1‖ < r := by simpa [dist_eq_norm] using hd2.1
  have hW : ‖y.2 - x.2‖ < r := by simpa [dist_eq_norm] using hd2.2
  have hjn := r26t8a_joint_le_nest i (fun Yw : Euc d × Euc d =>
    r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) y.1 y.2
    ((hV n).of_le (by exact_mod_cast hi))
  rw [Prod.mk.eta] at hjn
  refine hjn.trans ?_
  calc _ ≤ ∑ q ∈ Finset.range (i + 1), (i.choose q : ℝ) * Φ n :=
        Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
          (hΦb n (i - q) q (by have := Finset.mem_range.1 hq; omega) y.1 hY y.2 hW) (Nat.cast_nonneg _)
    _ = 2 ^ i * Φ n := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i

end HRS.MS.R26T8A

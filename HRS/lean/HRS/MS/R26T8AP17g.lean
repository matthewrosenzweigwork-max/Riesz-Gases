import HRS.MS.R26T8ARow6
import HRS.MS.R26T8AN0

/-!
# S8.2 local Newton layer, packet T8A.P17 (part g): smooth pieces of the centred source
`r26t8a_p17_conormal_fx`: a `C^k` function `g` with bounded jets gives `Conormal k b 0 σ B` for `(x,y) |-> g x` and `(x,y) |-> g y`.
`r26t8a_p17_testBound_smul`, `r26t8a_p17_hSource_smul`: scaling of the test function.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p17_conormal_fx (k b : ℕ) (σ B : ℝ) {g : Euc d → ℝ} (hg : ContDiff ℝ (k : WithTop ℕ∞) g)
    (hB : ∀ i ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    Conormal k b 0 σ B (fun x _ => g x) ∧ Conormal k b 0 σ B (fun _ y => g y) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hpw : ∀ x y : Euc d, pairWeight 0 x y = 1 := fun x y => by simp [pairWeight]
  have hfin : ∀ (q : ℕ) (z : Euc d), 0 ≤ B * 1 * (1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) := by
    intro q z
    have : 0 ≤ (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    positivity
  have hfin2 : ∀ (q : ℕ) (z : Euc d), B ≤ B * 1 * (1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) := by
    intro q z
    have : 0 ≤ (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by
      have : 0 ≤ (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
      positivity
    nlinarith
  constructor
  · refine And.intro ((hg.comp contDiff_fst).contDiffOn) fun p q hpq X z hz => ?_
    rw [hpw]
    have h := r26t8a_p17_nest_affine (1 / 2 : ℝ) q p g X z (hg.of_le (by exact_mod_cast hpq))
    refine (le_trans ?_ (hfin2 q z))
    show ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => g (Yw.1 + (1 / 2 : ℝ) • Yw.2)) X z‖ ≤ B
    refine h.trans ?_
    have hq : |(1 / 2 : ℝ)| ^ q ≤ 1 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; exact pow_le_one₀ (by norm_num) (by norm_num)
    calc |(1 / 2 : ℝ)| ^ q * ‖iteratedFDeriv ℝ (p + q) g (X + (1 / 2 : ℝ) • z)‖ ≤ 1 * B :=
          mul_le_mul hq (hB _ hpq _) (norm_nonneg _) zero_le_one
      _ = B := one_mul _
  · refine And.intro ((hg.comp contDiff_snd).contDiffOn) fun p q hpq X z hz => ?_
    rw [hpw]
    have h := r26t8a_p17_nest_affine (-(1 / 2 : ℝ)) q p g X z (hg.of_le (by exact_mod_cast hpq))
    refine (le_trans ?_ (hfin2 q z))
    have e : (fun Yw : Euc d × Euc d => midPair (fun _ y => g y) Yw.1 Yw.2) =
        fun Yw : Euc d × Euc d => g (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2) := by
      funext Yw; unfold midPair
      have : Yw.1 - (1 / 2 : ℝ) • Yw.2 = Yw.1 + (-(1 / 2 : ℝ)) • Yw.2 := by module
      rw [this]
    show ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (fun _ y => g y) Yw.1 Yw.2) X z‖ ≤ B
    rw [e]
    refine h.trans ?_
    have hq : |(-(1 / 2 : ℝ))| ^ q ≤ 1 := by
      rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; exact pow_le_one₀ (by norm_num) (by norm_num)
    calc |(-(1 / 2 : ℝ))| ^ q * ‖iteratedFDeriv ℝ (p + q) g (X + (-(1 / 2 : ℝ)) • z)‖ ≤ 1 * B :=
          mul_le_mul hq (hB _ hpq _) (norm_nonneg _) zero_le_one
      _ = B := one_mul _

theorem r26t8a_p17_jets_const_mul {k : ℕ} {a : Euc d → ℝ} (ha : ContDiff ℝ (k : WithTop ℕ∞) a) (c : ℝ) {i : ℕ} (hi : i ≤ k)
    (x : Euc d) : ‖iteratedFDeriv ℝ i (fun y => c * a y) x‖ = |c| * ‖iteratedFDeriv ℝ i a x‖ := by
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := c) (f := a) (x := x) (i := i)
    ((ha.of_le (by exact_mod_cast hi : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞))).contDiffAt)
  have e : (fun y => c * a y) = c • a := by funext y; simp
  rw [e, h, norm_smul, Real.norm_eq_abs]

theorem r26t8a_p17_testBound_smul {k : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : TestBound k A f) (c : ℝ) :
    TestBound k (|c| * A) (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj hjk x => ?_⟩
  rw [r26t8a_p17_jets_const_mul (k := j) (contDiff_infty.1 hf.1 j) c le_rfl]
  exact mul_le_mul_of_nonneg_left (hf.2 j hj hjk x) (abs_nonneg c)

theorem r26t8a_p17_hSource_smul {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    hSource (fun x => c * f x) = fun x y => c * hSource f x y := by
  funext x y
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hg : ∀ z, gradient (fun x => c * f x) z = c • gradient f z := fun z => by
    simp only [gradient]
    rw [fderiv_const_mul (hd z) c, map_smul]
  unfold hSource commutatorKernel
  rw [hg x, hg y, ← smul_sub, inner_smul_left]
  simp

end HRS.MS.R26T8A

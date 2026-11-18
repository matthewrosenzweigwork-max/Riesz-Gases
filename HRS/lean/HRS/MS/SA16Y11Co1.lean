import HRS.MS.SA16Y11Nl1
import HRS.MS.SA16Y11Dr1
import HRS.MS.SA16QFin2

/-!
# S.A.16 (SA16Y11) Co1: unpacking `coeffNormE` into the weight predicates used by the iso/hilbert difference lemmas

* `sa16y11_Dec_of_wsup`: `weightedSupE k (d+3) f ≤ ofReal W` gives `sa16y5_Dec k (d^k 2^{d+3} W) f` (pointwise `(1+‖x‖)^{-(d+3)}` bounds of `‖D^κ f‖`).
* `sa16y11_Dec_w`: `Dec k W f` gives the `sa16p_w` form `‖D^j f y‖ ≤ W * sa16p_w d y`.
* `sa16y11_comp_iter`: the component of a vector function has no larger iterated derivative norm.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Co1
variable {d : ℕ}

lemma sa16y11_Dec_of_wsup (hd : 1 ≤ d) (k : ℕ) {f : Euc d → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (h : weightedSupE k ((d : ℝ) + 3) f ≤ ENNReal.ofReal W) :
    sa16y5_Dec k ((d : ℝ) ^ k * (2 ^ (d + 3) * W)) f := by
  have hw : ∀ κ ≤ k, ∀ r : Fin κ → Fin d, ∀ x, |partialDeriv r f x| * (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * W := by
    intro κ hκ r x
    have h1 : ENNReal.ofReal (jbracket x ^ ((d : ℝ) + 3) * |partialDeriv r f x|) ≤
        weightedSupE k ((d : ℝ) + 3) f := by
      unfold weightedSupE derivSupE
      exact le_iSup_of_le ⟨κ, by omega⟩ (le_iSup_of_le r (le_iSup_of_le x le_rfl))
    have h2 : jbracket x ^ ((d : ℝ) + 3) * |partialDeriv r f x| ≤ W :=
      (ENNReal.ofReal_le_ofReal_iff hW).1 (h1.trans h)
    have h3 : jbracket x ^ ((d : ℝ) + 3) = jbracket x ^ (d + 3) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [h3] at h2
    have h4 : (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * jbracket x ^ (d + 3) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (sa16q_jb_le x) _
    calc |partialDeriv r f x| * (1 + ‖x‖) ^ (d + 3)
        ≤ |partialDeriv r f x| * (2 ^ (d + 3) * jbracket x ^ (d + 3)) := by gcongr
      _ = 2 ^ (d + 3) * (jbracket x ^ (d + 3) * |partialDeriv r f x|) := by ring
      _ ≤ 2 ^ (d + 3) * W := by gcongr
  intro κ hκ x
  have h := sa16q_weight_conv (a := f) (κ := κ) (Λ2 := 2 ^ (d + 3) * W) (hw κ hκ) x
  refine h.trans ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hω : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hc : 0 ≤ 2 ^ (d + 3) * W := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hκ) hc) hω

lemma sa16y11_Dec_w {k : ℕ} {W : ℝ} {f : Euc d → ℝ} (h : sa16y5_Dec k W f) :
    ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ W * Phase2SA16P.sa16p_w d y := by
  intro j hj y
  refine (h j hj y).trans (le_of_eq ?_)
  unfold Phase2SA16P.sa16p_w
  congr 2
  push_cast; ring

lemma sa16y11_comp_iter {k : ℕ} {v : Euc d → Euc d} (hv : ContDiff ℝ (k : WithTop ℕ∞) v) (j : Fin d)
    (x : Euc d) : ‖iteratedFDeriv ℝ k (fun y => v y j) x‖ ≤ ‖iteratedFDeriv ℝ k v x‖ := by
  let L : Euc d →L[ℝ] ℝ := EuclideanSpace.proj j
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    rw [one_mul]
    exact PiLp.norm_apply_le v j)
  have h := L.norm_iteratedFDeriv_comp_left (f := v) (x := x) hv.contDiffAt (by exact_mod_cast le_refl k)
  have e : (fun y => v y j) = L ∘ v := rfl
  rw [e]
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hL)

end Co1

end HRS.Whole.AppendixA.Phase2SA16R

end

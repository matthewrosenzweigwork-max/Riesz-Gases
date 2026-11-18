import HRS.MS.SA12X3C7C17
import HRS.MS.SA12X3C7B5

/-!
# S.A.12 C7 (SA12X3), part D1 (7D): splitting `jetPair` along a decomposition valid on `{w ≠ 0}`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x3_pd_add {n : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y + g y) x = partialDeriv idx f x + partialDeriv idx g x := by
  unfold partialDeriv
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  simp

theorem sa12x3_jetPair_split {m : ℕ} {w F G N S Fs : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ ∞ F) (hN : ContDiff ℝ m N) (hS : ContDiff ℝ m S) (hFs : ContDiff ℝ m Fs)
    (hG : ∀ x, w x ≠ 0 → G x = N x + S x + Fs x) :
    jetPair m w F G = jetPair m w F N + jetPair m w F S + jetPair m w F Fs := by
  unfold jetPair
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  have hpc : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
  have hcN : ∀ {H : Euc d → ℝ}, ContDiff ℝ m H → Continuous (partialDeriv idx H) := fun {H} hH =>
    (sa12x2_pd_cd (k := 0) (by simpa using hH.of_le (by exact_mod_cast hjm)) idx).continuous
  have hint : ∀ {H : Euc d → ℝ}, ContDiff ℝ m H →
      Integrable (fun x => w x ^ 2 * (partialDeriv idx F x * partialDeriv idx H x)) := fun {H} hH =>
    Continuous.integrable_of_hasCompactSupport ((hw.pow 2).mul (hpc.mul (hcN hH)))
      ((hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right)
  have hopen : IsOpen {x : Euc d | w x ≠ 0} := isOpen_ne_fun hw continuous_const
  have hpt : ∀ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x) =
      w x ^ 2 * (partialDeriv idx F x * partialDeriv idx N x) +
      w x ^ 2 * (partialDeriv idx F x * partialDeriv idx S x) +
      w x ^ 2 * (partialDeriv idx F x * partialDeriv idx Fs x) := by
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have hEq : EqOn G (fun y => N y + S y + Fs y) {x : Euc d | w x ≠ 0} := fun y hy => hG y hy
      rw [sa12x3_pd_congr_open hopen hEq idx hx,
        sa12x3_pd_add (hN.add hS |>.of_le le_rfl |> fun h => by simpa using (hN.add hS).of_le (by exact_mod_cast hjm))
          (hFs.of_le (by exact_mod_cast hjm)) idx x,
        sa12x3_pd_add (hN.of_le (by exact_mod_cast hjm)) (hS.of_le (by exact_mod_cast hjm)) idx x]
      ring
  simp_rw [hpt]
  have h12 : Integrable (fun x => w x ^ 2 * (partialDeriv idx F x * partialDeriv idx N x) +
      w x ^ 2 * (partialDeriv idx F x * partialDeriv idx S x)) := (hint hN).add (hint hS)
  rw [integral_add h12 (hint hFs), integral_add (hint hN) (hint hS)]

end HRS.MH.AdjointRd.Phase2SA12Near

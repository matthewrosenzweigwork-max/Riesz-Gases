import HRS.MS.S82P2Mar3

/-!
# S8.2 (S82P2): second moment of a centered sum under the pinned weak reference law
Resampling (one-site) gives the variance of `S = sum_j psi (X_j)` of order `n * int psi^2`, and the
mean of `S` is of order `n * int |psi| * (delta_N + min 1 ((1 + sum q)/N))` by `PinComparison`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_sum_update {d n : ℕ} (ψ : Euc d → ℝ) (X : EucConfig d n) (i : Fin n) (y : Euc d) :
    ∑ j, ψ (Function.update X i y j) = ∑ j, ψ (X j) + (ψ y - ψ (X i)) := by
  have h1 : ∀ j, ψ (Function.update X i y j) = Function.update (fun j => ψ (X j)) i (ψ y) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp only [h1]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase Finset.univ (fun j => ψ (X j)) (Finset.mem_univ i)
  linarith

lemma s82p2_resample_le {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2) (hnp : n + p ≤ N) (pins : Fin p → Euc d)
    (i : Fin n) (X : EucConfig d n) :
    resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X ≤
      ENNReal.ofReal C0 • HRS.Whole.withDensityReal rho := by
  refine (hW.conditional N hN p n (by omega) hnp pins i X).trans ?_
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, Measure.smul_apply, withDensity_apply _ hs]
  gcongr
  calc ∫⁻ y in s, ENNReal.ofReal (Real.exp (-(beta / N) *
        ((∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j))))
        ∂HRS.Whole.withDensityReal rho
      ≤ ∫⁻ y in s, 1 ∂HRS.Whole.withDensityReal rho := by
        refine lintegral_mono fun y => ?_
        refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
        have hq := hW.short.nonneg
        have : 0 ≤ (beta / N) * ((∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j)) :=
          mul_nonneg (div_nonneg hbeta.le (Nat.cast_nonneg _))
            (add_nonneg (Finset.sum_nonneg fun j _ => hq _) (Finset.sum_nonneg fun j _ => hq _))
        linarith
    _ = HRS.Whole.withDensityReal rho s := by simp

end HRS.MS.S82P2

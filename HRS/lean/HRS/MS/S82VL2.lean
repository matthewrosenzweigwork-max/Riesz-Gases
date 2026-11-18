import HRS.MS.S82VL1

/-!
# S8.2 A02 (S82V), part 1b: the Laplacian of the pair statistic at one site
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The Laplacian of `y ↦ pairStatistic Q (update X i y)` at `X i`. -/
lemma s82v_laplacian_pair {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {m : ℕ}
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (hX : ∀ j, j ≠ i → X j ≠ X i) :
    Laplacian.laplacian (fun y => pairStatistic (N := m + 1) Q (Function.update X i y)) (X i) =
      (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
        ∑ j ∈ Finset.univ.erase i, Laplacian.laplacian (fun y => Q y (X j)) (X i) := by
  have hsym := hQ.symmetric
  set cN : ℝ := ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) with hcN
  set c0 : ℝ := pairStatistic (N := m + 1) Q
    (i.insertNth (X i) (fun k => X (i.succAbove k)) : EucConfig d (m + 1)) with hc0
  have hform : (fun y => pairStatistic (N := m + 1) Q (Function.update X i y)) =
      fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))) := by
    funext y
    exact HRS.MS.S82P2.s82p2_phi_formula hsym i X y
  have hk : ∀ k : Fin m, ContDiffAt ℝ 2 (fun y => Q y (X (i.succAbove k))) (X i) := fun k =>
    s82v_Q_contDiffAt hQ (X i) _ (fun h => hX _ (Fin.succAbove_ne i k) h.symm)
  have hsub : ∀ k : Fin m, ContDiffAt ℝ 2
      (fun y => Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))) (X i) := fun k =>
    (hk k).sub contDiffAt_const
  have hsum : ContDiffAt ℝ 2 (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
      Q (X i) (X (i.succAbove k)))) (X i) := ContDiffAt.sum fun k _ => hsub k
  rw [hform]
  have e : (fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k)))) =
      (fun _ => c0) + (2 * cN) • fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))) := by
    funext y; simp [smul_eq_mul]
  have hadd := ContDiffAt.laplacian_add (f₁ := fun _ : Euc d => c0)
    (f₂ := (2 * cN) • fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))))
    (x := X i) contDiffAt_const (hsum.const_smul (2 * cN))
  rw [e, hadd, InnerProductSpace.laplacian_const, InnerProductSpace.laplacian_smul _ hsum,
    s82v_laplacian_sum _ _ _ (fun k _ => hsub k)]
  have hlap : ∀ k : Fin m, Laplacian.laplacian
      (fun y => Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))) (X i) =
      Laplacian.laplacian (fun y => Q y (X (i.succAbove k))) (X i) := fun k => by
    have e2 : (fun y => Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))) =
        (fun y => Q y (X (i.succAbove k))) - fun _ => Q (X i) (X (i.succAbove k)) := rfl
    rw [e2, ContDiffAt.laplacian_sub (hk k) contDiffAt_const, InnerProductSpace.laplacian_const]
    simp
  simp only [hlap]
  rw [s82v_sum_succAbove (fun j => Laplacian.laplacian (fun y => Q y (X j)) (X i)) i]
  simp [smul_eq_mul]

end HRS.MS.S82V

end

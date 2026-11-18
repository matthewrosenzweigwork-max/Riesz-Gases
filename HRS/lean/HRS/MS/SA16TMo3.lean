import HRS.MS.SA16TMo2

/-!
# S.A.16 (SA16T) Mo3: regularity of the mollified density at order `m+4` (non-uniform in `n`) and `sa16so_G` as `SA16SubOp`
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P

section Mo3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the `n`-dependent regularity constant at order `k` -/
def sa16t_LamN (d n k : ℕ) (A0 : ℝ) : ℝ := ((k : ℝ) + 2) * (sa16t_Crho d n k * (2 ^ ((d : ℝ) + 3) * A0))

lemma sa16t_reg_hi {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hd : 1 ≤ d) (hμ : CoeffHypRd s m Λ T μ) (n k : ℕ)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    IsRegularDensityW k (sa16t_LamN d n k (sa16t_A0 d m Λ)) (sa16t_mu d n μ r) := by
  obtain ⟨hc, hb⟩ := sa16t_mu_decay hd hμ hr
  have hcont : Continuous (μ r) := hc.continuous
  have h0 : ∀ y, |μ r y| ≤ sa16t_A0 d m Λ * sa16p_w d y := fun y => by
    simpa [Real.norm_eq_abs] using hb 0 (Nat.zero_le _) y
  exact sa16t_regular_of_decay (contDiff_infty.1 (sa16y_mollify_smooth n hcont) k)
    (fun j hj y => by
      refine (sa16t_conv_decay_n hcont h0 n k hj y).trans (le_of_eq ?_)
      ring)

theorem sa16t_G_subop (k : ℕ) (hd : 1 ≤ d) (s MB Λ : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
    (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ ν : Euc d → ℝ,
      IsRegularDensityW (k + 3) Λ ν →
      SA16SubOp d k p s M ν (sa16so_G d k p s M ν) ∧ ‖sa16so_G d k p s M ν‖ ≤ C := by
  obtain ⟨C, hC, hex⟩ := sa16so_G_exists d k hd s p MB Λ hs0 hs2 hfar
  refine ⟨C, hC, fun M hM ν hν => ?_⟩
  obtain ⟨T, hTn, hT⟩ := hex M hM ν hν
  have : sa16so_G d k p s M ν = T := sa16so_G_eq hT
  rw [this]
  exact ⟨hT, hTn⟩

end Mo3

end HRS.Whole.AppendixA.Phase2SA16R

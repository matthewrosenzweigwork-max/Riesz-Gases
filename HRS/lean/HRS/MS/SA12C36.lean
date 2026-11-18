import HRS.MS.SA12C35
import HRS.MS.SA12X3C15E

/-! E7.06 for an arbitrary prescribed uniformly local cutoff: choose its larger cutoff companion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction
variable {d : ℕ}

theorem sa12c_periodic_box_energy_uloc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hs1 : (d : ℝ) < 2 * (s + 1)) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C Lmin : ℝ, 0 < C ∧ 0 < Lmin ∧
      ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
        (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), Lmin ≤ L →
        PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
        RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
          IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
            boxEnergy m L (F τ) ≤
              Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * boxEnergy m L (F 0) := by
  obtain ⟨χh, hpair⟩ := sa12x3_cutoffPair hχ
  obtain ⟨C, Lmin, hC, hLmin, hbound⟩ := sa12c_periodic_box_energy hd s hs0 hsd hs1 m hm Rg
    MB Λ ΛV νbar Cb T hpair
  refine ⟨C, Lmin, hC, by linarith, ?_⟩
  intro ν₀ L γ M ν μ V b hL hPD hR t ht F hsol τ hτ
  exact hbound L hL γ M ν ν₀ μ V b hPD hR t ht F hsol τ hτ

end HRS.MH.AdjointRd.Phase2SA12C

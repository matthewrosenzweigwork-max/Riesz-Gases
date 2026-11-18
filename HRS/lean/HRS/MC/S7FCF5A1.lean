import HRS.MC.S7FCW7F3
import HRS.PDE.MeanFieldAprioriClassicalOn

/-!
# Block A1 of packet `fcf5`: joint continuity of the mean-field density `(t,x) ↦ ρ^t(x)` on `[0,∞) × 𝕋^d`

Proof of `fcf5_A1_rho_cont` (`S7FCF5Plan.lean`).  Route: `s7fcw7_sol` gives the coefficient solution `ρc` with
`R.ρ t = mfPath ρc t` for `t ≥ 0`; for every horizon `n` the `MFSolRealOn` structure and
`MFApriori.continuousOn_mfPath_prod_on` give joint continuity on `[0,n] × 𝕋^d`; these are glued over `n`.
Also `S7FCF5A_rho_cont_x`: continuity of `x ↦ ρ^u(x)` for `u ≥ 0`.
Namespace `HRS.MC.Sec7.S7FCF5A`, prefix `S7FCF5A_` for helpers, `_proof` for the theorems.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5A

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW7

variable {d : ℕ}

/-- The mean-field density is jointly continuous on `[0,∞) × 𝕋^d` (proof of `fcf5_A1_rho_cont`). -/
theorem fcf5_A1_rho_cont_proof (R : Regime d) :
    ContinuousOn (fun p : ℝ × Torus d => R.ρ p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  obtain ⟨K, hK, ρc, hρc, hρ⟩ := s7fcw7_sol R
  have hK2 : (d : ℝ) / 2 + 2 < (K : ℝ) := by linarith
  have hreal : ∀ t : ℝ, 0 ≤ t → PDE.IsRealCoeff (ρc t) :=
    HRS.PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK (by have := R.hd; omega) R.D.s R.β R.β K R.D.V R.ρ₀
      (R.finiteRegHyp K hK) R.β ⟨le_rfl, le_rfl⟩ ρc hρc
  have H : ∀ n : ℕ, ContinuousOn (fun p : ℝ × Torus d => PDE.mfPath ρc p.1 p.2)
      (Set.Icc (0 : ℝ) (n : ℝ) ×ˢ (Set.univ : Set (Torus d))) := by
    intro n
    have hS : HRS.PDE.MFApriori.MFSolRealOn d R.D.s R.D.V R.β⁻¹ K R.ρ₀ ρc (n : ℝ) :=
      ⟨HRS.PDE.MFApriori.IsMFSolutionHK.toSolOn hρc (n : ℝ), fun t ht => hreal t ht.1⟩
    exact (HRS.PDE.MFApriori.continuousOn_mfPath_prod_on (by have := R.hd; omega) R.D.s R.D.hs0 R.D.hsd K
      hK2 R.D.V R.ρ₀ (R.finiteRegHyp K hK).hV R.β⁻¹ ρc hS).1
  have hcont : ContinuousOn (fun p : ℝ × Torus d => PDE.mfPath ρc p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    obtain ⟨n, hn⟩ := exists_nat_gt p.1
    have hpn : p ∈ Set.Icc (0 : ℝ) (n : ℝ) ×ˢ (Set.univ : Set (Torus d)) :=
      ⟨⟨Set.mem_Ici.1 hp.1, hn.le⟩, Set.mem_univ _⟩
    have hnhd : Set.Iio (n : ℝ) ×ˢ (Set.univ : Set (Torus d)) ∈ 𝓝 p :=
      (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hn, Set.mem_univ _⟩
    have hsub : Set.Icc (0 : ℝ) (n : ℝ) ×ˢ (Set.univ : Set (Torus d)) ∈
        𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p := by
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici (0 : ℝ) ×ˢ Set.univ) hnhd) ?_
      rintro q ⟨hq1, hq2⟩
      exact ⟨⟨Set.mem_Ici.1 hq1.1, (Set.mem_Iio.1 hq2.1).le⟩, Set.mem_univ _⟩
    exact (H n p hpn).mono_of_mem_nhdsWithin hsub
  refine hcont.congr ?_
  intro q hq
  exact congrFun (hρ q.1 (Set.mem_Ici.1 hq.1)) q.2

/-- Continuity of `x ↦ ρ^u(x)` for `u ≥ 0` (restriction of the joint continuity). -/
theorem S7FCF5A_rho_cont_x (R : Regime d) {u : ℝ} (hu : 0 ≤ u) : Continuous (R.ρ u) := by
  have h := (fcf5_A1_rho_cont_proof R).comp_continuous
    (continuous_const.prodMk continuous_id : Continuous fun x : Torus d => (u, x))
    (fun x => ⟨Set.mem_Ici.2 hu, Set.mem_univ _⟩)
  exact h

end HRS.MC.Sec7.S7FCF5A

end

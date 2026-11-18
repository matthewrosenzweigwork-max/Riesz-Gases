import HRS.MS.PROS13SeparatedA

/-!
# S13: a common sequence of smooth symmetric separated finite-rank kernels

This holds for every Borel probability measure on Euclidean space, including
finite atomic measures. No density or envelope assumptions are imposed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ}

theorem pro_s13_generic_separated_sequence
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun p : Euc d × Euc d => h p.1 p.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ hj : ℕ → Euc d → Euc d → ℝ,
      (∀ j, ∃ (m : ℕ) (c : Fin m → Fin m → ℝ)
        (u : Fin m → Euc d → ℝ),
        IsR2FiniteRankData c u ∧ hj j = r2FiniteRankKernel c u) ∧
      Tendsto (fun j => eLpNorm
        (fun p : Euc d × Euc d => hj j p.1 p.2 - h p.1 p.2)
        2 (μ.prod μ)) atTop (𝓝 0) := by
  classical
  have hε : ∀ j : ℕ, 0 < (1 : ℝ) / ((j : ℝ) + 1) := by
    intro j
    positivity
  have hchoose : ∀ j : ℕ, ∃ (m : ℕ) (c : Fin m → Fin m → ℝ)
      (u : Fin m → Euc d → ℝ), IsR2FiniteRankData c u ∧
      eLpNorm
        (fun p : Euc d × Euc d =>
          r2FiniteRankKernel c u p.1 p.2 - h p.1 p.2)
        2 (μ.prod μ) ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
    fun j => pro_s13_generic_separated_approx μ h hh hs _ (hε j)
  choose m c u hd herr using hchoose
  let hj : ℕ → Euc d → Euc d → ℝ :=
    fun j => r2FiniteRankKernel (c j) (u j)
  refine ⟨hj, (fun j => ⟨m j, c j, u j, hd j, rfl⟩), ?_⟩
  have hright : Tendsto
      (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1)))
      atTop (𝓝 0) := by
    have hr : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa only [one_div] using
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using ENNReal.tendsto_ofReal hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hright (fun j => bot_le) (fun j => herr j)

end HRS.MS.R26T3

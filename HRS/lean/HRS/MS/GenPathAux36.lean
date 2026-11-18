import HRS.MS.GenPathAux35

/-!
# S5.6 packet P4e: a.e. measurability of the particle path `Ξ_N`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_wpo_eq_windowPath {m T : ℝ} {Ω : Type*} (Y : ℝ → Ω → OscDual d m) :
    (fun ζ => windowPathOf m T 0 (fun t => Y t ζ)) = HRS.Uniform.windowPath 0 T Y := by
  funext ζ
  unfold windowPathOf HRS.Uniform.windowPath
  rfl

theorem s56_fluc_aemeas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) :
    AEMeasurable (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)) P := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have h := HRS.GF.gfb4_aemeasurable_windowPath P hT (s56Xi S X)
    (fun t ht => s56_xi_meas b hbv S (by omega) X hX.adapted t ht)
    (by
      filter_upwards [hX.cont] with ζ hζ
      exact s56_xi_cont b hbv S (by omega) X ζ hζ)
  rw [← s56_wpo_eq_windowPath] at h
  exact h

end HRS.MS.GenPath

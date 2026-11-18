import HRS.MS.CritForceMom13
import HRS.MS.S82P2Mom

/-!
# S8.2 local Newton layer, packet T8A.R00c: smooth-kernel export of merged `s82n_E5`
`ShortRangePole` and `S82nShortRangePole` have the same six fields (`criticalS d` and `s82n_critS d` are both `d/2`), so the merged theorem applies after repackaging.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

theorem r26t8a_s82n_E5 {d : ℕ} (hd : 2 ≤ d) (β M G c : ℝ) (hβ : 0 < β) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * HRS.MS.S82N.s82n_pole x y ^ 2 *
          (HRS.MS.S82N.s82n_logN N + 1 + |Real.log (HRS.MS.S82N.s82n_smallRadius x y)|) ^ 2 *
          Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * jbracket x ^ M * HRS.MS.S82N.s82n_logN N ^ 3) := by
  exact HRS.MS.S82N.s82n_E5 hd β M G c hβ hM hG hc q
    ⟨hq.measurable, hq.smooth, hq.even, hq.nonneg, hq.near, hq.far⟩

end HRS.MS.R26T8A

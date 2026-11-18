import HRS.MS.CritForceMom16
import HRS.MS.S82P2Mom

/-!
# S8.2 R03 / R04 in the frozen `Phase2S82` vocabulary
Bridges from the `s82n_`/`s82p_` theorems (`CritForceMom14`, `CritForceMom16`) to the frozen statements
`S82.R03` (`weighted_radial_rows`) and `S82.R04` (`weighted_pin_product`) of the Pro skeleton.
`ShortRangePole` is the frozen structure of `S82P2Mom`; the fields are identical up to the unfolding
`criticalS = s82n_critS` (both `d / 2`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

lemma s82q_pole_bridge {d : ℕ} {q : Euc d → ℝ} (hq : ShortRangePole d q) :
    HRS.MS.S82N.S82nShortRangePole d q :=
  ⟨hq.measurable, hq.smooth, hq.even, hq.nonneg, hq.near, hq.far⟩

/-- Weighted radial rows (frozen statement `S82.R03`). -/
theorem weighted_radial_rows (d : ℕ) (hd : 2 ≤ d)
    (beta M G c : ℝ) (hbeta : 0 < beta) (hM : 0 ≤ M) (hG : 0 < G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      let mu := HRS.Whole.withDensityReal rho
      let cutoff := fun y => Real.exp (-(beta / N) * q (x - y))
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M *
        (1 + smallRadius x y ^ (1 - criticalS d)) ^ 2) ∂mu) ≤
        ENNReal.ofReal (C * jbracket x ^ M) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M *
        (1 + smallRadius x y ^ (1 - criticalS d)) * pole x y) ∂mu) ≤
        ENNReal.ofReal (C * jbracket x ^ M) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M * pole x y ^ 2 * cutoff y) ∂mu) ≤
        ENNReal.ofReal (C * jbracket x ^ M * logN N) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M * pole x y ^ 4 * cutoff y) ∂mu) ≤
        ENNReal.ofReal (C * jbracket x ^ M * (N : ℝ) ^ 2) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M * pole x y ^ 2 *
        (logN N + 1 + |Real.log (smallRadius x y)|) ^ 2 * cutoff y) ∂mu) ≤
        ENNReal.ofReal (C * jbracket x ^ M * logN N ^ 3) := by
  obtain ⟨C, hC, h⟩ := HRS.MS.S82N.s82n_weighted_radial_rows hd beta M G c hbeta hM hG hc q
    (s82q_pole_bridge hq)
  exact ⟨C, hC, fun rho hρ hρG N hN x => h rho hρ hρG N hN x⟩

/-- Weighted pin product (frozen statement `S82.R04`). -/
theorem weighted_pin_product (d : ℕ) (hd : 2 ≤ d)
    (M G c : ℝ) (hM : 0 ≤ M) (hG : 0 < G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C M' : ℝ, 0 ≤ C ∧ M ≤ M' ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ N : ℕ, 2 ≤ N → ∀ x y : Euc d, x ≠ y →
        (∫⁻ z, ENNReal.ofReal (jbracket z ^ M * triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂HRS.Whole.withDensityReal rho) ≤
          ENNReal.ofReal (C * pairWeight M' x y * pole x y *
            (logN N + 1 + |Real.log (smallRadius x y)|) / N) := by
  obtain ⟨C, M', hC, hM', h⟩ := HRS.MS.S82P.s82p_weighted_pin_product hd M G c hM hG hc q
    (s82q_pole_bridge hq)
  exact ⟨C, M', hC, hM', fun rho hρ hρG N hN x y hxy => h rho hρ hρG N hN x y hxy⟩

end HRS.MS.Phase2S82

import HRS.MS.S88BDA05
import HRS.MS.S88BDG01
import HRS.MS.S88BDM03

/-!
# S8.8.F02: Gaussian rational-window assembly

`s88_gaussian_decay`: G01 turns the deterministic envelope of A05 into the base and increment inputs of M03, with the
common constant `K = max Cin 1 ≥ 1`; the supremum is over the rational-time subtype exactly as in the frozen statement.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

theorem s88_gaussian_decay {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (m : ℝ) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ)
    (c : ℝ) (b : MultiIndex d → ℝ) (hb : ∀ α, 0 ≤ b α) (hsum : Summable b)
    (hreg : S88OrbitRegular (critCoeff d a β ρ) m)
    (henv : S88OrbitEnvelope (critCoeff d a β ρ) (HRS.Whole.withDensityReal ρ) m c b)
    (T Cin u : ℝ) (hT : 0 < T) (hu : 1 ≤ u)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Ω → (Euc d → ℝ) → ℝ)
    (hη : IsGaussianFunctionalW P η
      (HRS.Whole.susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρ) β)) :
    ((∫⁻ z, (⨆ t : S88RatTime T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
      η z (s88Orbit (critCoeff d a β ρ) m (u + t.1) α))) ^ 2 ∂P) ^
        (1 / 2 : ℝ)) ≤ ENNReal.ofReal (s88Constant T Cin b * Real.exp (-c * u)) := by
  haveI : Countable (S88RatTime T) := s88_ratTime_countable T
  have hK0 : (0 : ℝ) ≤ max Cin 1 := le_trans zero_le_one (le_max_right _ _)
  have hK1 : (1 : ℝ) ≤ max Cin 1 := le_max_right _ _
  have hE0 : 0 < Real.exp (-2 * c * u) := Real.exp_pos _
  have hu0 : 0 ≤ u := by linarith
  have hIcc : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ u + t := fun t ht => by linarith [ht.1]
  have hmem : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      MemLp (fun z => η z (s88Orbit (critCoeff d a β ρ) m (u + t) α)) 2 P := by
    intro α t ht
    exact (s88_gaussian_second_moments hd a β ha hβ ρ hρ P η hη _ _
      (hreg.memCb α _ (hIcc t ht)) (hreg.memCb α _ (hIcc t ht))).1
  have hbase : ∀ α : MultiIndex d,
      (∫⁻ z, ENNReal.ofReal ((η z (s88Orbit (critCoeff d a β ρ) m (u + 0) α)) ^ 2) ∂P) ≤
        ENNReal.ofReal (max Cin 1 * b α * Real.exp (-2 * c * u)) := by
    intro α
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hmc := hreg.memCb α _ (hIcc 0 h0)
    refine (s88_gaussian_second_moments hd a β ha hβ ρ hρ P η hη _ _ hmc hmc).2.2.1.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := (henv.base α u hu).2
    rw [add_zero]
    have hb0 := mul_nonneg (hb α) hE0.le
    nlinarith
  have hinc : ∀ (α : MultiIndex d) (s : ℝ), s ∈ Set.Icc (0 : ℝ) T →
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
        (∫⁻ z, ENNReal.ofReal ((η z (s88Orbit (critCoeff d a β ρ) m (u + s) α) -
            η z (s88Orbit (critCoeff d a β ρ) m (u + t) α)) ^ 2) ∂P) ≤
          ENNReal.ofReal (max Cin 1 * b α * Real.exp (-2 * c * u) * (s - t) ^ 2) := by
    intro α s hs t ht
    refine (s88_gaussian_second_moments hd a β ha hβ ρ hρ P η hη _ _
      (hreg.memCb α _ (hIcc s hs)) (hreg.memCb α _ (hIcc t ht))).2.2.2.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := (henv.increment α u s t hu hs.1 ht.1).2
    have hb0 := mul_nonneg (mul_nonneg (hb α) hE0.le) (sq_nonneg (s - t))
    nlinarith
  have := s88_l2_maximal_decay P T (max Cin 1) c u hT hK0 b hb hsum
    (fun t z α => η z (s88Orbit (critCoeff d a β ρ) m (u + t) α)) hmem hbase hinc
    (fun t : S88RatTime T => t.1) (fun t => t.2.1)
  exact this

end HRS.MS.S88Breakdown

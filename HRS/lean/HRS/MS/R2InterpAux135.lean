import HRS.MS.R2InterpAux134

/-!
# S10.2 (worker S10S), part 135 (packet C3): the corner `γ = 0 = s`

For the logarithmic gas with the Gibbs-free preparation `μ^{⊗N} = Q_{N,0}(μ)`, the time marginals of the particle dynamics have an `L^p(Q_{N,β})` density.  The density of `μ^{⊗N}` against
`Q_{N,β}` is `K_{N,β} e^{βN F_N}`; its `p`-th moment is `K_{N,β}^p K_{N,β}^{-1} K_{N,-(p-1)β}`, finite for small `p - 1` by the log-gas normalizer at small negative
inverse temperature (`s113x_X4_generic`, worker S11X).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.Wr HRS.MS.PrepStat HRS.MS.R2Mt

variable {d N : ℕ}

set_option maxHeartbeats 1600000 in
theorem s102_time_density_log (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d 0 a β ρ) (hN : 2 ≤ N)
    (hinv : GibbsInvariant d 0 a β N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d 0 a β P X₀ W X) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hlaw : P.map X₀ = HRS.Whole.modulatedGibbs (rieszKernel d 0) N 0 (HRS.Whole.withDensityReal ρ)) (T : ℝ) :
    ∃ p K : ℝ, 1 < p ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      HasR2ActualDensity 0 β p K (HRS.Whole.withDensityReal ρ) (P.map (X t)) := by
  classical
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  obtain ⟨M, L, c, hRD, hGU⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hβ hρ
  haveI hμp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hRD.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  -- the normalizer at `β` and at small negative temperatures
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L (β / 2) (β + 1) (by positivity) (by linarith)
  obtain ⟨hWb, hlb⟩ := hnorm ρ hRD N hN β ⟨by linarith, by linarith⟩
  obtain ⟨astar, B, hastar, hB0, hX4⟩ := HRS.MS.S113BD.s113x_X4_generic (d := d) (by omega) M c hGU.1
  -- the exponent
  set η : ℝ := min 1 (astar / β) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hastar hβ)
  have hηβ : η * β ≤ astar := by
    have : η ≤ astar / β := min_le_right _ _
    rwa [le_div_iff₀ hβ] at this
  set p : ℝ := 1 + η with hp
  have hp1 : 1 < p := by linarith
  have hb' : β + p * (0 - β) = -(η * β) := by rw [hp]; ring
  have hmem : -(η * β) ∈ Set.Icc (-astar) (0 : ℝ) := ⟨by linarith, by nlinarith⟩
  obtain ⟨hpos, hlog⟩ := hX4 ρ hRD.prob.measurable (fun x => ⟨hRD.prob.nonneg x, hGU.2 x⟩) hRD.prob.integral_one N hN
    (-(η * β)) hmem
  -- well-definedness at `b₀ = 0` and `b' = -(ηβ)`
  have hW0 : GibbsWellDefined (fun x y => rieszKernel d 0 (x - y)) N 0 μ := by
    refine ⟨hWb.conv_integrable, hWb.pair_integrable, ?_, ?_⟩
    · simp only [neg_zero, zero_mul, Real.exp_zero]
      exact integrable_const _
    · simp [pairNormalizer]
  have hW' : GibbsWellDefined (fun x y => rieszKernel d 0 (x - y)) N (β + p * (0 - β)) μ := by
    rw [hb']
    refine ⟨hWb.conv_integrable, hWb.pair_integrable, ?_, hpos⟩
    refine Integrable.of_integral_ne_zero ?_
    exact hpos.ne'
  have hK0 : pairNormalizer (fun x y => rieszKernel d 0 (x - y)) N 0 μ = 1 := by simp [pairNormalizer]
  have hl0 : |Real.log (pairNormalizer (fun x y => rieszKernel d 0 (x - y)) N 0 μ)| ≤ max C0 B := by
    rw [hK0, Real.log_one, abs_zero]
    exact le_max_of_le_left hC0
  have hlb' : |Real.log (pairNormalizer (fun x y => rieszKernel d 0 (x - y)) N β μ)| ≤ max C0 B := hlb.trans (le_max_left _ _)
  have hl' : |Real.log (pairNormalizer (fun x y => rieszKernel d 0 (x - y)) N (β + p * (0 - β)) μ)| ≤ max C0 B := by
    rw [hb']
    exact hlog.trans (le_max_right _ _)
  exact s102_time_density_gen hd le_rfl hs ha hβ hρ hN hinv P X₀ W X hreal ℱ W' hF hlaw T hW0
    ⟨p, Real.exp (2 * max C0 B), hp1, fun κ hκ hQκ => s102_quench_gen hp1 hWb hW0 hW' hlb' hl0 hl' κ hκ hQκ⟩

end HRS.MS.R2Interp

end

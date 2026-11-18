import HRS.MS.R2InterpAux130

/-!
# S10.2 (worker S10S), part 131 (packet M3): almost sure continuity of `u ↦ Y_u` in `𝒳` for the thermal quadratic dynamics

Countably many orbit coordinates (rational times `q` and `T`, all `α`) are a.s. continuous (Aux128); with the uniform bound (Aux127), the slice continuity
(Aux129), the Lipschitz bound in `t` and the gluing with the path `ζ_N` (Aux130) this gives continuity of the predicted path.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.CovMeas

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s102_M3 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X) {M L p K : ℝ}
    (hp : 1 < p) (hρR : IsRound2Density d s M L ρ)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    {m : ℝ} (hm : (d : ℝ) < m) {r : ℕ} {c : MultiIndex d → ℝ}
    (hS : S102Std ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T r c)
    (hlin : S102Lin ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T) {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r)
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    {Cm : ℝ} (hCm : ∀ u ∈ Icc (0 : ℝ) T,
      ∫ x, jbracket x ^ Pw ∂(HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) ≤ Cm) :
    ∀ᵐ ζ ∂P, ContinuousOn
      (s102_Y ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) m T P X ζ) (Icc 0 T) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  have hXm : ∀ t, Measurable (X t) := hX.adapted
  have hcont : ∀ᵐ ζ ∂P, ∀ k, Continuous fun t : ℝ≥0 => X t ζ k := hX.cont
  have hzc := s102_zeta_cont hm hN0 P X hXm hcont
  have hsl : ∀ᵐ ζ ∂P, ∀ q ∈ s102_Qset T, ∀ α : MultiIndex d,
      ContinuousOn (fun u => s102_zf P X ζ u (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) u q
        (oscTestFun m α))) (Icc 0 q) := by
    rw [ae_ball_iff (s102_Qset_countable T)]
    intro q hq
    rw [ae_all_iff]
    intro α
    exact s102_orbit_cont hd hs0 hs ha hβ hρ hT.le hN P X₀ W X hX ℱ W' hF hp hρR hdens (s102_Qset_sub hT.le hq) m α
      (hS.hcls α q (s102_Qset_sub hT.le hq))
  filter_upwards [hcont, hzc, hsl] with ζ hc hz hs'
  obtain ⟨M', hM'⟩ := s102_zf_unif hd1 hP0 r hr hN0 P X hmom hCm ζ hc
  exact s102_Y_continuousOn hS hP hlin hT hd1 hP0 hr hm hN0 P X hXm hmom ζ hz hM' hs'

end HRS.MS.R2Interp

end

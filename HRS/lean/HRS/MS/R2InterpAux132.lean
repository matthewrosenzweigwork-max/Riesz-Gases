import HRS.MS.R2InterpAux131
import HRS.MS.R2InterpAux125
import HRS.MS.R2InterpAux112

/-!
# S10.2 (worker S10S), part 132: `S102Rest` (M1 and the continuity of the predicted path) from the `L^p` density of the time marginals
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.CovMeas

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
theorem s102_rest_proof {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalEquilibrium d s a β ρ)
    (horb : HRS.Whole.R2OrbitSummable ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8))
    (N : ℕ) (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d s a β P X₀ W X)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hdenP : ∃ p K : ℝ, 1 < p ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X t))) :
    S102Rest ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8) ((d : ℝ) + 2) s (HRS.Whole.withDensityReal ρ) hT P X := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hN0 : 0 < N := by omega
  obtain ⟨c, hDc⟩ := s101_data_of_horb hd1 horb
  have hstd := s102_std_thermal hd hs0 hs ha hβ hρ ((14 * d + 114 : ℕ) : ℝ) T hT.le hDc
  have hlin := s102_lin_thermal hd hs0 hs ha hβ hρ ((14 * d + 114 : ℕ) : ℝ) T hT.le
  obtain ⟨M, L, c₁, hRD, hGU⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hβ hρ
  haveI hμp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hRD.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set m : ℝ := ((14 * d + 114 : ℕ) : ℝ) with hmdef
  have hm : (d : ℝ) < m := by rw [hmdef]; push_cast; linarith
  have hr : (d : ℝ) / 2 < ((2 * d + 8 : ℕ) : ℝ) := by push_cast; linarith
  have hr2 : (d : ℝ) / 2 + 2 < ((2 * d + 8 : ℕ) : ℝ) := by push_cast; linarith
  have hP : (d : ℝ) < 2 * ((d : ℝ) + 2) := by linarith
  have hP0 : (0 : ℝ) ≤ (d : ℝ) + 2 := by positivity
  have hXm : ∀ t, Measurable (X t) := (hreal.solution T).adapted
  obtain ⟨p, K, hp, hdensN⟩ := hdenP
  have hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K μ (P.map (X r.toNNReal)) := fun r hr' =>
    hdensN r.toNNReal (by rw [Real.coe_toNNReal _ hr'.1]; exact hr'.2)
  have hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ ((d : ℝ) + 2))
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) := fun u hu =>
    s102_marginal_moment hd hs0 hs M L M c₁ β p K hGU.1 hβ hp hP0 hRD hGU.2 hN (hdens u hu)
  obtain ⟨Cm, hCm⟩ := s102_marginal_moment_bound hd hs0 hs M L M c₁ β p K hGU.1 hβ hp hP0
  refine ⟨?_, ?_⟩
  · exact s102_M1 hd hs0 hs hstd hT hr2 hP0 hGU.1 hβ hp hRD hGU.2 hN P X hXm
      (fun t _ => measurable_progressive_min_gen (u := ofNNRealTime X) hF.progressive t) hdens
  · exact s102_M3 hd hs0 hs ha hβ hρ hT hN P X₀ W X (hreal.solution T) ℱ W' hF hp hRD hdens hm hstd hlin hP hP0 hr hmom
      (fun u hu => hCm hRD hGU.2 hN (hdens u hu))

end HRS.MS.R2Interp

end

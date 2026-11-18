import HRS.MS.R2InterpAux132
import HRS.MS.R2InterpAux135

/-!
# S10.2 (worker S10S), part 136: `S102Part` from `S102Rest` and the `L^p` density of the time marginals (no preparation hypotheses)
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.CovMeas

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1600000 in
theorem s102_part_of_rest_gen {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalEquilibrium d s a β ρ)
    (horb : HRS.Whole.R2OrbitSummable ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8))
    (hγex : ∃ γu : ℝ → Measure (OscPath d ((14 * d + 114 : ℕ) : ℝ) T), ∀ u ∈ Set.Icc (0 : ℝ) T,
      IsR2FutureGaussian ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T u (γu u))
    (N : ℕ) (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsR2Realization d s a β P X₀ W X)
    (hdenP : ∃ p K : ℝ, 1 < p ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X t)))
    (hrest : S102Rest ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T
      (2 * d + 8) ((d : ℝ) + 2) s (HRS.Whole.withDensityReal ρ) hT P X)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hneg : ∀ t : ℝ, t ≤ 0 → ℱ t = ℱ 0) :
    S102Part ((HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((14 * d + 114 : ℕ) : ℝ) T (2 * d + 8)
      ((d : ℝ) + 2) s (HRS.Whole.withDensityReal ρ) hT P X ℱ W' := by
  classical
  obtain ⟨hMb, hYc⟩ := hrest
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hN0 : 0 < N := by omega
  obtain ⟨c, hDc⟩ := s101_data_of_horb hd1 horb
  have hstd := s102_std_thermal hd hs0 hs ha hβ hρ ((14 * d + 114 : ℕ) : ℝ) T hT.le hDc
  have hlin := s102_lin_thermal hd hs0 hs ha hβ hρ ((14 * d + 114 : ℕ) : ℝ) T hT.le
  obtain ⟨M, L, c₁, hRD, hGU⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hβ hρ
  haveI hμp : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hRD.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  set m : ℝ := ((14 * d + 114 : ℕ) : ℝ) with hmdef
  have hm : (d : ℝ) < m := by rw [hmdef]; push_cast; linarith
  have hr : (d : ℝ) / 2 < ((2 * d + 8 : ℕ) : ℝ) := by push_cast; linarith
  have hP : (d : ℝ) < 2 * ((d : ℝ) + 2) := by linarith
  have hP0 : (0 : ℝ) ≤ (d : ℝ) + 2 := by positivity
  have hXm : ∀ t, Measurable (X t) := (hreal.solution T).adapted
  have hcont : ∀ᵐ ζ ∂P, ∀ k, Continuous fun t : ℝ≥0 => X t ζ k := (hreal.solution T).cont
  have hXprog : IsProgressive ℱ (ofNNRealTime X) := hF.progressive
  have hXjm : Measurable fun q : ℝ × Ω => X (min q.1 T).toNNReal q.2 :=
    measurable_progressive_min_gen (u := ofNNRealTime X) hXprog T
  -- the time marginals have an `L^p` density
  obtain ⟨p, K, hp, hdensN⟩ := hdenP
  have hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K μ (P.map (X r.toNNReal)) := fun r hr' =>
    hdensN r.toNNReal (by rw [Real.coe_toNNReal _ hr'.1]; exact hr'.2)
  -- moments
  have hPd : (d : ℝ) / 2 < (d : ℝ) + 2 := by linarith
  have hμint : Integrable (fun x : Euc d => jbracket x ^ ((d : ℝ) + 2)) μ := by
    obtain ⟨C1, hC1⟩ := HRS.MS.R2Chaos.s94_moment_rpow hRD.prob hGU hP0
    have hjm : Measurable fun z : Euc d => jbracket z ^ ((d : ℝ) + 2) :=
      ((by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
        (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')).measurable
    refine ⟨hjm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Real.rpow_nonneg (by unfold jbracket; positivity) _)]
    exact lt_of_le_of_lt hC1 ENNReal.ofReal_lt_top
  have hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ ((d : ℝ) + 2))
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) := fun u hu =>
    s102_marginal_moment hd hs0 hs M L M c₁ β p K hGU.1 hβ hp hP0 hRD hGU.2 hN (hdens u hu)
  obtain ⟨Cm, hCm⟩ := s102_marginal_moment_bound hd hs0 hs M L M c₁ β p K hGU.1 hβ hp hP0
  have hmoz : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun ζ => (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ ((d : ℝ) + 2)) P ∧
      ∫ ζ, (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ ((d : ℝ) + 2) ∂P ≤ Cm := by
    intro u hu
    have hjm : Measurable fun z : Euc d => jbracket z ^ ((d : ℝ) + 2) :=
      ((by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
        (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')).measurable
    obtain ⟨h1, h2⟩ := s102_empMoment hN0 P (X u.toNNReal) (hXm _) hjm
      (fun x => Real.rpow_nonneg (by unfold jbracket; positivity) _) (hmom u hu)
    exact ⟨h1, by rw [h2]; exact hCm hRD hGU.2 hN (hdens u hu)⟩
  -- the covariance measure
  obtain ⟨Vf, hVf, hJc⟩ := s102_M2 hd hstd hlin hT horb hPd hP0 hr hN0 P μ hμint X hcont hXjm Cm hmoz
  obtain ⟨Mb, hdr, hMint⟩ := hMb
  obtain ⟨γu, hγG⟩ := hγex
  have hμ' : ∀ u ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ,
      HRS.Whole.pair μ g = ∫ x, g x * C.ρ u x := by
    intro u _ g
    rw [HRS.Whole.Q09A.pair_withDensityReal hρ.2.1 g]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [C, WholeDyn.coeff]
    ring
  refine ⟨hF.brownian, Mb, Vf, hdr, hMint, hYc, hVf, hJc, ?_, ?_, ?_, fun L Φ hΦ => ?_, fun L => ?_⟩
  · exact s102_zetaPath_aemeas hm hN0 P X hXm hcont
  · exact (s102_y0_meas hstd hP hlin hT hd1 hP0 (by linarith) hN0 P X hXm
      (by simpa using hmom 0 ⟨le_rfl, hT.le⟩)).aemeasurable
  · intro L
    filter_upwards [hcont] with ζ hζ
    exact fun i j => s102_hh2_integrable hstd hT L hN0 μ hμ' X ζ hζ i j
  · exact ⟨s102_cylA_meas hd hs0 hs hstd hlin hP hP0 hr hm hT L hβ hp hRD hN P X hXprog hXm hcont hdens hmom γu hγG hΦ,
      s102_cylJ_meas hd hs0 hs hstd hlin hP hP0 hr hm hT L hβ hp hRD hN P X hXprog hXm hcont hdens hmom hμ' γu hγG hΦ⟩
  · exact s102_itoRep hd hs0 hs ha hβ hρ hT hN P X₀ W X (hreal.solution T) ℱ W' hF hneg hp hRD hdens hm hstd hlin hP hP0
      (by linarith) hmom L

end HRS.MS.R2Interp

end

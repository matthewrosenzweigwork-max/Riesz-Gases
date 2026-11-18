import HRS.MS.ShiftFldAux7

/-!
# S79: `critical_path_limit` conditional on S2.1(i)

`critical_path_limit_of_S21 (h21 : type_of% @HRS.Whole.whole_space_stationary) : type_of% @HRS.Whole.critical_path_limit`.
The hypothesis `h21` is the frozen statement of S2.1(i) (`Headline.lean:334`, still `stated`); once `whole_space_stationary` is proved,
`critical_path_limit_of_S21 whole_space_stationary_proof` is the proof of the frozen S7.9 limit (this file makes no use of any
unproved declaration other than through `h21`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.Whole.S79

open HRS (Euc)

theorem critical_path_limit_of_S21 (h21 : HRS.Whole.WholeSpaceStationaryStatement) :
    type_of% @HRS.Whole.critical_path_limit := by
  intro d s hd hs a β ha hβ T hT ρβ hρβ Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs2 : (d : ℝ) / 2 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hp : biasP d s = 3 / 2 := s79_biasP_critical hd hs
  have hmd : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex
    push_cast
    linarith
  obtain ⟨C₀, C, -, hmain⟩ := h21 hd s hs0 hsd a β ha hβ T hT
  obtain ⟨K, hK0, hK⟩ := s79_core hd hs2 hsd ha hβ hmd (s := s)
  -- the S2.1(i) conclusion for each N
  have hS : ∀ N : ℕ, 2 ≤ N →
      AEMeasurable (zetaPathW (wholeSpaceIndex d) T 0 (P N) (X N)) (P N) ∧
      AEMeasurable (processWindow (wholeSpaceIndex d) T 0 Z) P' ∧
      smoothDist 2 (law (P N) (zetaPathW (wholeSpaceIndex d) T 0 (P N) (X N)))
          (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
        C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ∧
      wassersteinE 1 (law (P N) (zetaPathW (wholeSpaceIndex d) T 0 (P N) (X N)))
          (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
        ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
          Real.sqrt (localizationRate d s C₀ N))) := by
    intro N hN
    have hRN := hR N hN
    exact hmain ρβ hρβ N hN hRN.invariant (P N) (X₀ N) (W N) (X N) hRN.brownian hRN.indep hRN.init
      (hRN.solution T) P' Z (hZ T)
  -- the core at each N
  have hC : ∀ N : ℕ, 2 ≤ N →
      AEMeasurable (flucPathW (wholeSpaceIndex d) T 0 (Real.sqrt N) (X N) (fun _ => ρβ)) (P N) ∧
      AEMeasurable (fun ζ' => processWindow (wholeSpaceIndex d) T 0 Z ζ' +
        constPath (wholeSpaceIndex d) T (biasField (wholeSpaceIndex d) d s β ρβ)) P' ∧
      wassersteinE 1 (law (P N) (flucPathW (wholeSpaceIndex d) T 0 (Real.sqrt N) (X N)
          (fun _ => ρβ)))
        (law P' (fun ζ' => processWindow (wholeSpaceIndex d) T 0 Z ζ' +
          constPath (wholeSpaceIndex d) T (biasField (wholeSpaceIndex d) d s β ρβ))) ≤
        ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
          Real.sqrt (localizationRate d s C₀ N))) +
          ENNReal.ofReal (K * (N : ℝ) ^ (-biasTheta d s)) := by
    intro N hN
    obtain ⟨hz1, hz2, -, hz4⟩ := hS N hN
    obtain ⟨c1, c2, -, c4⟩ := hK T 0 ρβ hρβ N hN (P N) (X₀ N) (W N) (X N) (hR N hN) P' Z hz1 hz2
    simp only [hp, sub_self, Real.rpow_zero, one_smul, zero_sub] at c1 c2 c4
    exact ⟨c1, c2, c4.trans (add_le_add hz4 le_rfl)⟩
  refine ⟨fun N hN => (hC N hN).1, (hC 2 le_rfl).2.1, ?_⟩
  intro F
  set ν : Measure (OscPath d (wholeSpaceIndex d) T) := law P' (fun ζ' => processWindow (wholeSpaceIndex d) T 0 Z ζ' +
          constPath (wholeSpaceIndex d) T (biasField (wholeSpaceIndex d) d s β ρβ)) with hν
  have hW : Tendsto (fun N : ℕ => wassersteinE 1 (law (P N) (flucPathW (wholeSpaceIndex d) T 0
      (Real.sqrt N) (X N) (fun _ => ρβ))) ν) atTop (𝓝 0) := by
    obtain ⟨hrA, hrB⟩ := s79_rates_tendsto hd hs C₀ C K
    have hrate' : Tendsto (fun N : ℕ => ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
        Real.sqrt (localizationRate d s C₀ N))) +
        ENNReal.ofReal (K * (N : ℝ) ^ (-biasTheta d s))) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal hrA).add (ENNReal.tendsto_ofReal hrB)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate'
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (hC N hN).2.2
  have hconv := HRS.Main.therm_convergesInLaw_of_W1
    (fun N : ℕ => law (P N) (flucPathW (wholeSpaceIndex d) T 0 (Real.sqrt N) (X N) (fun _ => ρβ)))
    ν (Eventually.of_forall fun N => inferInstance) hW F
  have hνint : ∫ x, F x ∂ν = ∫ ζ', F (processWindow (wholeSpaceIndex d) T 0 Z ζ' +
      constPath (wholeSpaceIndex d) T (biasField (wholeSpaceIndex d) d s β ρβ)) ∂P' :=
    integral_map (hC 2 le_rfl).2.1 F.continuous.aestronglyMeasurable
  rw [hνint] at hconv
  refine hconv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact integral_map (hC N hN).1 F.continuous.aestronglyMeasurable

end HRS.Whole.S79

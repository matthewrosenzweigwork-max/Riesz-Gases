import HRS.Prob.Metrics

/-!
# S7FCHA2: the abstract triangle-inequality argument of the FC-H assembly

Let `U_N` (particle) and `U'` (limit) be random elements of a separable Banach space `B`, and `V_N^j`, `V'^j`
(`j` in an index set) approximants.  If for every `δ > 0` there is an index `j` such that
`E‖U_N - V_N^j‖^q ≤ δ` (all `N ≥ 2`), `E‖U' - V'^j‖^q ≤ δ`, and `W_q(Law V_N^j, Law V'^j) → 0`, then
`W_q(Law U_N, Law U') → 0`.  (Triangle inequality `wassersteinE_triangle`, identity couplings
`wassersteinE_le_of_coupling`, and `(e/4) + (e/2) + (e/4) = e`.)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH

open HRS

/-- The abstract assembly: `W_q` of the pair laws tends to `0`. -/
theorem S7FCHA_Wq_abstract {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] {J : Type*} (U : ∀ N, Ω N → B) (U' : Ω' → B)
    (V : J → ∀ N, Ω N → B) (V' : J → Ω' → B) (q : ℝ) (hq : 1 ≤ q)
    (hU : ∀ N, 2 ≤ N → AEMeasurable (U N) (P N)) (hU' : AEMeasurable U' P')
    (hV : ∀ j N, 2 ≤ N → AEMeasurable (V j N) (P N)) (hV' : ∀ j, AEMeasurable (V' j) P')
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ j : J,
      (∀ N, 2 ≤ N → ∫⁻ ω, ENNReal.ofReal (‖U N ω - V j N ω‖ ^ q) ∂(P N) ≤ ENNReal.ofReal δ) ∧
      ∫⁻ ω, ENNReal.ofReal (‖U' ω - V' j ω‖ ^ q) ∂P' ≤ ENNReal.ofReal δ ∧
      Tendsto (fun N => wassersteinE q (law (P N) (V j N)) (law P' (V' j))) atTop (𝓝 0)) :
    Tendsto (fun N => wassersteinE q (law (P N) (U N)) (law P' U')) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => hεt ▸ le_top
  obtain ⟨e, he0, rfl⟩ : ∃ e : ℝ, 0 < e ∧ ε = ENNReal.ofReal e :=
    ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεt, (ENNReal.ofReal_toReal hεt).symm⟩
  have hq0 : 0 < q := by linarith
  have he4 : 0 < e / 4 := by positivity
  set δ : ℝ := (e / 4) ^ q with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos he4 q
  obtain ⟨j, h1, h3, h2⟩ := hmain δ hδ
  have hroot : (ENNReal.ofReal δ) ^ (1 / q) = ENNReal.ofReal (e / 4) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hδ.le (by positivity)]
    congr 1
    rw [hδdef, ← Real.rpow_mul he4.le, mul_one_div_cancel hq0.ne', Real.rpow_one]
  have hmid := ENNReal.tendsto_nhds_zero.1 h2 (ENNReal.ofReal (e / 2)) (ENNReal.ofReal_pos.2 (by positivity))
  haveI : IsProbabilityMeasure (law P' (V' j)) :=
    (Measure.isProbabilityMeasure_map_iff (hV' j)).2 inferInstance
  haveI : IsProbabilityMeasure (law P' U') := (Measure.isProbabilityMeasure_map_iff hU').2 inferInstance
  filter_upwards [hmid, eventually_ge_atTop 2] with N hN hN2
  haveI : IsProbabilityMeasure (law (P N) (U N)) :=
    (Measure.isProbabilityMeasure_map_iff (hU N hN2)).2 inferInstance
  haveI : IsProbabilityMeasure (law (P N) (V j N)) :=
    (Measure.isProbabilityMeasure_map_iff (hV j N hN2)).2 inferInstance
  have t1 : wassersteinE q (law (P N) (U N)) (law (P N) (V j N)) ≤ ENNReal.ofReal (e / 4) := by
    refine (wassersteinE_le_of_coupling (P N) q hq (U N) (V j N) (hU N hN2) (hV j N hN2)).trans ?_
    rw [← hroot]
    exact ENNReal.rpow_le_rpow (h1 N hN2) (by positivity)
  have t3 : wassersteinE q (law P' (V' j)) (law P' U') ≤ ENNReal.ofReal (e / 4) := by
    refine (wassersteinE_le_of_coupling P' q hq (V' j) U' (hV' j) hU').trans ?_
    rw [← hroot]
    refine ENNReal.rpow_le_rpow (le_of_eq_of_le ?_ h3) (by positivity)
    refine lintegral_congr fun ω => ?_
    rw [norm_sub_rev]
  calc wassersteinE q (law (P N) (U N)) (law P' U')
      ≤ wassersteinE q (law (P N) (U N)) (law (P N) (V j N)) +
        wassersteinE q (law (P N) (V j N)) (law P' U') := wassersteinE_triangle q hq _ _ _
    _ ≤ wassersteinE q (law (P N) (U N)) (law (P N) (V j N)) +
        (wassersteinE q (law (P N) (V j N)) (law P' (V' j)) +
          wassersteinE q (law P' (V' j)) (law P' U')) :=
        add_le_add le_rfl (wassersteinE_triangle q hq _ _ _)
    _ ≤ ENNReal.ofReal (e / 4) + (ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 4)) :=
        add_le_add t1 (add_le_add hN t3)
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HRS.MC.Sec7.S7FCH

end

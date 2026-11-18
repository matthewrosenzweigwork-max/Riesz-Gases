import HRS.Prob.Metrics

/-!
# S7UCAWq: the abstract triangle argument with a supremum over a parameter (UC-ABS)

`s7_UC_Wq_abstract_proof`: `S7FCHA_Wq_abstract` (`S7FCHA2.lean`) for families indexed by `a : A` with approximants
indexed by `j : J` (chosen independently of `a`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCA

open HRS

theorem s7_UC_Wq_abstract_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] {A : Type*} {J : Type*} (U : A → ∀ N, Ω N → B) (U' : A → Ω' → B)
    (V : J → A → ∀ N, Ω N → B) (V' : J → A → Ω' → B) (q : ℝ) (hq : 1 ≤ q)
    (hU : ∀ a N, 2 ≤ N → AEMeasurable (U a N) (P N)) (hU' : ∀ a, AEMeasurable (U' a) P')
    (hV : ∀ j a N, 2 ≤ N → AEMeasurable (V j a N) (P N)) (hV' : ∀ j a, AEMeasurable (V' j a) P')
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ j : J,
      (∀ a N, 2 ≤ N → ∫⁻ ω, ENNReal.ofReal (‖U a N ω - V j a N ω‖ ^ q) ∂(P N) ≤ ENNReal.ofReal δ) ∧
      (∀ a, ∫⁻ ω, ENNReal.ofReal (‖U' a ω - V' j a ω‖ ^ q) ∂P' ≤ ENNReal.ofReal δ) ∧
      Tendsto (fun N => ⨆ a, wassersteinE q (law (P N) (V j a N)) (law P' (V' j a))) atTop (𝓝 0)) :
    Tendsto (fun N => ⨆ a, wassersteinE q (law (P N) (U a N)) (law P' (U' a))) atTop (𝓝 0) := by
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
  filter_upwards [hmid, eventually_ge_atTop 2] with N hN hN2
  refine iSup_le fun a => ?_
  haveI : IsProbabilityMeasure (law P' (V' j a)) :=
    (Measure.isProbabilityMeasure_map_iff (hV' j a)).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (U' a)) := (Measure.isProbabilityMeasure_map_iff (hU' a)).2 inferInstance
  haveI : IsProbabilityMeasure (law (P N) (U a N)) :=
    (Measure.isProbabilityMeasure_map_iff (hU a N hN2)).2 inferInstance
  haveI : IsProbabilityMeasure (law (P N) (V j a N)) :=
    (Measure.isProbabilityMeasure_map_iff (hV j a N hN2)).2 inferInstance
  have t1 : wassersteinE q (law (P N) (U a N)) (law (P N) (V j a N)) ≤ ENNReal.ofReal (e / 4) := by
    refine (wassersteinE_le_of_coupling (P N) q hq (U a N) (V j a N) (hU a N hN2) (hV j a N hN2)).trans ?_
    rw [← hroot]
    exact ENNReal.rpow_le_rpow (h1 a N hN2) (by positivity)
  have t3 : wassersteinE q (law P' (V' j a)) (law P' (U' a)) ≤ ENNReal.ofReal (e / 4) := by
    refine (wassersteinE_le_of_coupling P' q hq (V' j a) (U' a) (hV' j a) (hU' a)).trans ?_
    rw [← hroot]
    refine ENNReal.rpow_le_rpow (le_of_eq_of_le ?_ (h3 a)) (by positivity)
    refine lintegral_congr fun ω => ?_
    rw [norm_sub_rev]
  have t2 : wassersteinE q (law (P N) (V j a N)) (law P' (V' j a)) ≤ ENNReal.ofReal (e / 2) :=
    (le_iSup (fun a => wassersteinE q (law (P N) (V j a N)) (law P' (V' j a))) a).trans hN
  calc wassersteinE q (law (P N) (U a N)) (law P' (U' a))
      ≤ wassersteinE q (law (P N) (U a N)) (law (P N) (V j a N)) +
        wassersteinE q (law (P N) (V j a N)) (law P' (U' a)) := wassersteinE_triangle q hq _ _ _
    _ ≤ wassersteinE q (law (P N) (U a N)) (law (P N) (V j a N)) +
        (wassersteinE q (law (P N) (V j a N)) (law P' (V' j a)) +
          wassersteinE q (law P' (V' j a)) (law P' (U' a))) :=
        add_le_add le_rfl (wassersteinE_triangle q hq _ _ _)
    _ ≤ ENNReal.ofReal (e / 4) + (ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 4)) :=
        add_le_add t1 (add_le_add t2 t3)
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HRS.MC.Sec7.S7UCA

end

import HRS.Main.ThermAux13

/-!
# THERM helper 14: `thermalization_recentered` for `m > d/2`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem therm_recentered_hm (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (T : ℝ) (hT : 0 < T)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (a : ℝ) (ha : 0 ≤ a)
    (N : ℕ) (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hflow : SelectedFlow P S.dyn (a + T) X₀ W X)
    (Q : Measure (PathSpace d m T)) [IsProbabilityMeasure Q] :
    let shift : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt N) *
      ⨆ t : Set.Icc (0 : ℝ) T, ‖NegSobolev.ofMeasureDiff m (withDensityReal (S.ρ (a + t)))
        (withDensityReal ρβ)‖ₑ
    let recentered := law P (windowFluc m T a (Real.sqrt N) X (fun _ => ρβ))
    ENNReal.ofReal (smoothDist 2 recentered Q) ≤
      ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) Q) + shift ∧
    wassersteinE 1 recentered Q ≤ wassersteinE 1 (S.etaLaw m T a P X) Q + shift ∧
    wassersteinE 2 recentered Q ≤ wassersteinE 2 (S.etaLaw m T a P X) Q + shift := by
  intro shift recentered
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hρd : IsProbDensity ρβ := hρβ.1
  set σ : ℝ := Real.sqrt N with hσ
  set η : Ω → PathSpace d m T := windowFluc m T a σ X S.ρ with hη
  set R : Ω → PathSpace d m T := windowFluc m T a σ X (fun _ => ρβ) with hR
  set Dp : PathSpace d m T := (⟨therm_Dfun S T a m σ ρβ, therm_Dfun_cont S T a hm2 ha σ hρd⟩ :
    C(Set.Icc (0 : ℝ) T, NegSobolev d m)) with hDp
  have hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i := by
    rcases hflow.flow with h | h
    · exact h.1.cont
    · exact absurd h.1 (by have := S.hd; omega)
  have hae : R =ᵐ[P] fun ω => η ω + Dp := by
    filter_upwards [hcont] with ω hω
    exact therm_window_eq S T a hm2 (by omega) ha σ hρd X ω hω
  -- the shift bounds the norm of `Dp`
  have hDnorm : ENNReal.ofReal ‖Dp‖ ≤ shift := by
    by_cases htop : shift = ⊤
    · rw [htop]; exact le_top
    · set r : ℝ := shift.toReal with hr
      have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
      have hle : ‖Dp‖ ≤ r := by
        refine (ContinuousMap.norm_le (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from Dp) hr0).2
          fun t => ?_
        have h1 : ‖therm_Dfun S T a m σ ρβ t‖ₑ ≤ shift := by
          unfold therm_Dfun
          rw [enorm_smul, Real.enorm_of_nonneg (Real.sqrt_nonneg _)]
          refine mul_le_mul' le_rfl ?_
          exact le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖NegSobolev.ofMeasureDiff m
            (withDensityReal (S.ρ (a + t))) (withDensityReal ρβ)‖ₑ) t
        have := ENNReal.toReal_mono htop h1
        rw [toReal_enorm] at this
        exact this
      calc ENNReal.ofReal ‖Dp‖ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hle
        _ = shift := ENNReal.ofReal_toReal htop
  have hP0 : P ≠ 0 := IsProbabilityMeasure.ne_zero P
  show ENNReal.ofReal (smoothDist 2 (law P R) Q) ≤
      ENNReal.ofReal (smoothDist 2 (law P η) Q) + shift ∧
    wassersteinE 1 (law P R) Q ≤ wassersteinE 1 (law P η) Q + shift ∧
    wassersteinE 2 (law P R) Q ≤ wassersteinE 2 (law P η) Q + shift
  by_cases hηm : AEMeasurable η P
  · have hlaw : law P R = (law P η).map (fun x => x + Dp) := by
      have h1 : Measure.map R P = Measure.map (fun ω => η ω + Dp) P := Measure.map_congr hae
      have h2 := AEMeasurable.map_map_of_aemeasurable (μ := P)
        (measurable_add_const Dp).aemeasurable hηm
      exact h1.trans h2.symm
    rw [hlaw]
    refine ⟨?_, ?_, ?_⟩
    · calc ENNReal.ofReal (smoothDist 2 ((law P η).map (fun x => x + Dp)) Q)
          ≤ ENNReal.ofReal (smoothDist 2 (law P η) Q + ‖Dp‖) :=
            ENNReal.ofReal_le_ofReal (therm_smoothDist_translate_le _ _ Dp)
        _ = ENNReal.ofReal (smoothDist 2 (law P η) Q) + ENNReal.ofReal ‖Dp‖ :=
            ENNReal.ofReal_add (smoothDist_nonneg _ _ _) (norm_nonneg _)
        _ ≤ _ := add_le_add le_rfl hDnorm
    · exact (therm_wE_translate_le _ _ Dp 1 le_rfl).trans (add_le_add le_rfl hDnorm)
    · exact (therm_wE_translate_le _ _ Dp 2 (by norm_num)).trans (add_le_add le_rfl hDnorm)
  · have hRm : ¬ AEMeasurable R P := fun hRm => hηm (by
      have : AEMeasurable (fun ω => R ω - Dp) P := hRm.sub_const Dp
      refine this.congr ?_
      filter_upwards [hae] with ω hω
      rw [hω]; abel)
    have hlaw : law P R = law P η := by
      unfold law
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hRm hP0,
        Measure.map_of_not_aemeasurable_of_ne_zero hηm hP0]
    rw [hlaw]
    exact ⟨le_self_add, le_self_add, le_self_add⟩

end Main

end HRS

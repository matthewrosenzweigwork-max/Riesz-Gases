import HRS.Main.ThermLinFinal
import HRS.Main.ThermLin2As3
import HRS.Main.T25PFinal
import HRS.Main.ThermAux12

/-!
# THERMLIN (conditional): `thermalization_proof`, `thermalization_W2_proof`

(Formerly conditional; now unconditional: the rows below are the `_proof` versions.)  Was conditional on (i) the frozen Theorem 2.5 rows `prepared_fluctuations`, `prepared_fluctuations_W2` and
(ii) the new lemma `thermlin_gaussian_comparison` (`ThermLinAux5`, the Gaussian comparison `Y` vs `Z_β`).  The
existence of the prepared linear process is `preparedLinear_exists_proof` (`ThermLinFinal`, unconditional).  The
statements are derived from these as lemmas, so `#print axioms` shows `sorryAx` until (i), (ii) are replaced by
proofs.  Route (TeX `M:proof:L6969`): apply 2.5 with `ν = law(η_N^0)` (so `a_{N,p} = 0`), then the triangle inequality for
`d_2`, `W_1`, `W_2` and the Gaussian comparison.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem thermlin_wassersteinE_self {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (p : ℝ) (hp : 1 ≤ p) (μ : Measure B) [IsProbabilityMeasure μ] :
    wassersteinE p μ μ = 0 := by
  have hp0 : 0 < p := by linarith
  have h := wassersteinE_le_of_coupling μ p hp id id measurable_id.aemeasurable measurable_id.aemeasurable
  simp only [law, Measure.map_id, sub_self, norm_zero] at h
  rw [Real.zero_rpow hp0.ne'] at h
  refine le_antisymm (h.trans ?_) zero_le
  simp [ENNReal.zero_rpow_of_pos (inv_pos.2 hp0)]

instance thermlin_pathSpace_complete {m T : ℝ} : CompleteSpace (PathSpace d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))

theorem thermlin_ofReal_mul_le {C₁ C : ℝ} (hC₁ : 0 ≤ C₁) (h : C₁ ≤ C) (x : ℝ) :
    ENNReal.ofReal (C₁ * x) ≤ ENNReal.ofReal (C * x) := by
  rcases le_total 0 x with hx | hx
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h hx)
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hC₁ hx)]
    exact zero_le

theorem thermlin_eta_measurable (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) {N : ℕ} (hN : 2 ≤ N) :
    Measurable (fun X : Config d N => etaE m X S.μ0) := by
  haveI : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have := measurable_ofMeasureDiff_empirical (N := N) hm2 S.μ0 (by omega)
  unfold etaE flucE
  exact this.const_smul (Real.sqrt N)

theorem thermalization_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m), IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z))) ≤
          ENNReal.ofReal (C * (S.B N (law P X₀) / Real.sqrt N +
              Real.sqrt (S.B N (law P X₀) / N))) +
            ENNReal.ofReal (C * Real.exp (-c * a)) *
              (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) ∧
        wassersteinE 1 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (S.B N (law P X₀) / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) +
            ENNReal.ofReal (C * Real.exp (-c * a)) *
              (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) := by
  classical
  obtain ⟨C1, c1, hC1, hc1, hpf⟩ := prepared_fluctuations_proof S m hm T hT
  obtain ⟨C2, c2, hC2, hc2, hgc⟩ := thermlin_gaussian_comparison_proof S m hm T hT ρβ hρβ
  refine ⟨max C1 C2, min c1 c2, lt_max_of_lt_left hC1, lt_min hc1 hc2, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hflow hfilt hent Ω'' _ P'' _ Z hZ
  have hηm := thermlin_eta_measurable S m hm hN
  have hη0 : Measurable (fun ω => etaE m (X₀ ω) S.μ0) := hηm.comp (hflow.init_meas)
  set ν : Measure (NegSobolev d m) := law P (fun ω => etaE m (X₀ ω) S.μ0) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; unfold law; infer_instance
  obtain ⟨Ω', mΩ', P', hP', Y₀, Y, hY⟩ := preparedLinear_exists_proof S m hm (a + T) (by linarith) ν
  have h1 := hpf a ha N hN P X₀ W X hflow hfilt hent ν P' Y₀ Y hY
  have hinit : S.initW m 1 P X₀ ν = 0 := by
    unfold PreparedData.initW
    exact thermlin_wassersteinE_self 1 le_rfl ν
  obtain ⟨h1s, h1w⟩ := h1.1 (by rw [hinit]; exact ENNReal.zero_ne_top)
  rw [hinit, ENNReal.toReal_zero, mul_zero, zero_add] at h1s h1w
  obtain ⟨g1, -⟩ := hgc a ha ν P' Y₀ Y hY P'' Z hZ
  haveI : IsProbabilityMeasure (S.etaLaw m T a P X) := by unfold PreparedData.etaLaw; infer_instance
  have hmom : ∫⁻ y, ‖y‖ₑ ∂ν = ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P := by
    rw [hν, law, lintegral_map (f := fun y : NegSobolev d m => ‖y‖ₑ) (by fun_prop) hη0]
  have hexp : ENNReal.ofReal (C2 * Real.exp (-c2 * a)) ≤ ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_right _ _) ?_ (Real.exp_pos _).le
      (le_trans hC1.le (le_max_left _ _)))
    refine Real.exp_le_exp.2 ?_
    nlinarith [min_le_right c1 c2]
  have hrhs : ENNReal.ofReal (C2 * Real.exp (-c2 * a)) * (1 + ∫⁻ y, ‖y‖ₑ ∂ν) ≤
      ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) *
        (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) := by
    rw [hmom]
    gcongr
  constructor
  · calc ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z)))
        ≤ ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) +
            smoothDist 2 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z))) :=
          ENNReal.ofReal_le_ofReal (smoothDist_triangle 2 _ _ _)
      _ = ENNReal.ofReal (smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y))) +
            ENNReal.ofReal (smoothDist 2 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z))) :=
          ENNReal.ofReal_add (smoothDist_nonneg _ _ _) (smoothDist_nonneg _ _ _)
      _ ≤ ENNReal.ofReal (max C1 C2 * (S.B N (law P X₀) / Real.sqrt N +
              Real.sqrt (S.B N (law P X₀) / N))) +
            ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) *
              (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) := by
          refine add_le_add ?_ (le_trans ?_ hrhs)
          · exact (ENNReal.ofReal_le_ofReal h1s).trans
              (thermlin_ofReal_mul_le hC1.le (le_max_left _ _) _)
          · exact (ENNReal.ofReal_le_ofReal (smoothDist_succ_le 1 _ _)).trans
              ((smoothDist_one_le_wasserstein _ _).trans g1)
  · calc wassersteinE 1 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z))
        ≤ wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) +
            wassersteinE 1 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z)) :=
          wassersteinE_triangle 1 le_rfl _ _ _
      _ ≤ ENNReal.ofReal (max C1 C2 * (S.B N (law P X₀) / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) +
            ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) *
              (1 + ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ∂P) := by
          refine add_le_add ?_ (le_trans g1 hrhs)
          exact h1w.trans (thermlin_ofReal_mul_le hC1.le (le_max_left _ _) _)

example := (@thermalization_proof : type_of% @HRS.Main.thermalization)

theorem thermalization_W2_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        MemLp (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
          (S.refMeasure N 0) →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m), IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE 2 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (S.J N (law P X₀) p₀ / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) +
            ENNReal.ofReal (C * Real.exp (-c * a)) *
              (1 + (∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2)) := by
  classical
  obtain ⟨C1, c1, hC1, hc1, hpf⟩ := prepared_fluctuations_W2_proof S m hm T hT p₀ hp₀
  obtain ⟨C2, c2, hC2, hc2, hgc⟩ := thermlin_gaussian_comparison_proof S m hm T hT ρβ hρβ
  refine ⟨max C1 C2, min c1 c2, lt_max_of_lt_left hC1, lt_min hc1 hc2, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hflow hfilt hent hMem Ω'' _ P'' _ Z hZ
  have hηm := thermlin_eta_measurable S m hm hN
  have hη0 : Measurable (fun ω => etaE m (X₀ ω) S.μ0) := hηm.comp (hflow.init_meas)
  set ν : Measure (NegSobolev d m) := law P (fun ω => etaE m (X₀ ω) S.μ0) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; unfold law; infer_instance
  obtain ⟨Ω', mΩ', P', hP', Y₀, Y, hY⟩ := preparedLinear_exists_proof S m hm (a + T) (by linarith) ν
  have hinit : S.initW m 2 P X₀ ν = 0 := by
    unfold PreparedData.initW
    exact thermlin_wassersteinE_self 2 (by norm_num) ν
  have h1 := hpf a ha N hN P X₀ W X hflow hfilt hent hMem ν P' Y₀ Y hY (by rw [hinit]; exact ENNReal.zero_ne_top)
  rw [hinit, ENNReal.toReal_zero, mul_zero, zero_add] at h1
  obtain ⟨-, g2⟩ := hgc a ha ν P' Y₀ Y hY P'' Z hZ
  haveI : IsProbabilityMeasure (S.etaLaw m T a P X) := by unfold PreparedData.etaLaw; infer_instance
  have hmom : ∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂ν = ∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ^ (2 : ℝ) ∂P := by
    rw [hν, law, lintegral_map (f := fun y : NegSobolev d m => ‖y‖ₑ ^ (2 : ℝ)) (by fun_prop) hη0]
  have hexp : ENNReal.ofReal (C2 * Real.exp (-c2 * a)) ≤ ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_right _ _) ?_ (Real.exp_pos _).le
      (le_trans hC1.le (le_max_left _ _)))
    refine Real.exp_le_exp.2 ?_
    nlinarith [min_le_right c1 c2]
  have hrhs : ENNReal.ofReal (C2 * Real.exp (-c2 * a)) *
      (1 + (∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) ≤
      ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) *
        (1 + (∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2)) := by
    rw [hmom]
    gcongr
  calc wassersteinE 2 (S.etaLaw m T a P X) (law P'' (windowPath m T 0 Z))
      ≤ wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) +
          wassersteinE 2 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z)) :=
        wassersteinE_triangle 2 (by norm_num) _ _ _
    _ ≤ ENNReal.ofReal (max C1 C2 * (S.J N (law P X₀) p₀ / Real.sqrt N +
            (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) +
          ENNReal.ofReal (max C1 C2 * Real.exp (-min c1 c2 * a)) *
            (1 + (∫⁻ ω, ‖etaE m (X₀ ω) S.μ0‖ₑ ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2)) := by
        refine add_le_add ?_ (le_trans g2 hrhs)
        exact h1.trans (thermlin_ofReal_mul_le hC1.le (le_max_left _ _) _)

example := (@thermalization_W2_proof : type_of% @HRS.Main.thermalization_W2)

end Main

end HRS

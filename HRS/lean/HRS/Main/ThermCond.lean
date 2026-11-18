import HRS.Main.ThermAux10
import HRS.Main.ThermLinCond
import HRS.Main.T25Final

/-!
# THERM (conditional): `thermalization_limit_proof`

(Now unconditional: the frozen rows are replaced by their `_proof` versions.)  Was conditional on the frozen rows `thermalization`, `thermalization_W2` (Corollary 2.7, blocked on Theorem 2.5
and the Gaussian comparison) and `prepared_scales` (proved elsewhere as `prepared_scales_proof`): the
statement is derived from them as lemmas, so `#print axioms` shows `sorryAx` until those rows are
replaced by their `_proof` versions at the final assembly.  Everything else used is proved here
(`standard_preparation_norms_proof`, `ThermFinal`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem therm_ratio_bounds {B Cb δ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hδ : 0 < δ) (hB1 : 0 < B)
    (hB : B ≤ Cb * (N * δ)) :
    B / Real.sqrt N ≤ Cb * (Real.sqrt N * δ) ∧ B / N ≤ Cb * δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
  constructor
  · rw [div_le_iff₀ hs0]
    calc B ≤ Cb * (N * δ) := hB
      _ = Cb * (Real.sqrt N * δ) * Real.sqrt N := by linear_combination (Cb * δ) * hsq
  · rw [div_le_iff₀ hN0]
    calc B ≤ Cb * (N * δ) := hB
      _ = Cb * δ * N := by ring

theorem therm_delta_tendsto (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) :
    Tendsto (fun N : ℕ => deltaN d S.s N) atTop (𝓝 0) := by
  have h := (deltaN_errors_tendsto (by have := S.hd; omega) S.hs0 hs).1
  have h2 : Tendsto (fun N : ℕ => (1 / Real.sqrt N)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
    simpa [Function.comp_def] using this
  have h3 := h2.mul h
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  field_simp

theorem thermalization_limit_proof (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (a : ℕ → ℝ) (ha0 : ∀ N, 0 ≤ a N) (ha : Tendsto a atTop atTop)
    (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)]
    (X₀ : ∀ N, Ω N → Config d N) (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d))
    (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hflow : ∀ N : ℕ, 2 ≤ N → SelectedFlow (P N) S.dyn (a N + T) (X₀ N) (W N) (X N))
    (hfilt : ∀ N : ℕ, 2 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω N)))
      (W' : ℝ≥0 → Ω N → (Fin N × Fin d) → ℝ), IsFilteredSolution (P N) ℱ W' (W N) (X N))
    (hinit : ∀ N : ℕ, 2 ≤ N →
      law (P N) (X₀ N) = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Z : ℝ → Ω'' → NegSobolev d m) (hZ : IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z) :
    Tendsto (fun N : ℕ => smoothDist 2 (S.etaLaw m T (a N) (P N) (X N))
        (law P'' (windowPath m T 0 Z))) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => wassersteinE 1 (S.etaLaw m T (a N) (P N) (X N))
        (law P'' (windowPath m T 0 Z))) atTop (𝓝 0) ∧
      ((0 < β₀ ∨ S.s = 0) →
        Tendsto (fun N : ℕ => wassersteinE 2 (S.etaLaw m T (a N) (P N) (X N))
          (law P'' (windowPath m T 0 Z))) atTop (𝓝 0)) := by
  classical
  have hd1 : 1 ≤ d := by have := S.hd; omega
  obtain ⟨C, c, hC, hc, hth⟩ := thermalization_proof S m hm T hT ρβ hρβ
  obtain ⟨C₀, h0⟩ := standard_preparation_norms_proof S hs m hm β₀ hβ₀
  obtain ⟨⟨Cb, hCb⟩, hJ⟩ := prepared_scales_proof S β₀ hβ₀
  have hs_t := (deltaN_errors_tendsto hd1 S.hs0 hs).1
  have hq_t := (deltaN_errors_tendsto hd1 S.hs0 hs).2
  have hδ_t := therm_delta_tendsto S hs
  have hη : ∀ N, 1 ≤ N → Measurable (fun X : Config d N => etaE m X S.μ0) := fun N hN => by
    haveI : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
    have hm2 : (d : ℝ) < 2 * m := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have := measurable_ofMeasureDiff_empirical (N := N) hm2 S.μ0 hN
    unfold etaE flucE
    exact this.const_smul (Real.sqrt N)
  -- the initial moments, in terms of `P N`
  have hmom1 : ∀ N, 2 ≤ N → ∫⁻ ω, ‖etaE m (X₀ N ω) S.μ0‖ₑ ∂(P N) ≤ ENNReal.ofReal C₀ := fun N hN => by
    have := (h0 N hN).1
    rw [← hinit N hN, law, lintegral_map (hη N (by omega)).enorm (hflow N hN).init_meas] at this
    exact this
  have hB : ∀ N, 2 ≤ N → relEntropy (law (P N) (X₀ N)) (S.refMeasure N 0) < ⊤ ∧
      S.B N (law (P N) (X₀ N)) ≤ Cb * ((N : ℝ) * deltaN d S.s N) := fun N hN => by
    rw [hinit N hN]; exact hCb N hN
  have hB1 : ∀ N, 2 ≤ N → 0 < S.B N (law (P N) (X₀ N)) := fun N hN => by
    have h1 := (deltaN_basic hd1 S.hs0 S.hsd N (by omega)).1
    unfold PreparedData.B
    have := ENNReal.toReal_nonneg (a := relEntropy (law (P N) (X₀ N)) (S.refMeasure N 0))
    linarith
  have hδpos : ∀ N, 2 ≤ N → 0 < deltaN d S.s N := fun N hN =>
    therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  -- the limits of the right-hand sides
  have hu1 : Tendsto (fun N : ℕ => C * (Cb * (Real.sqrt N * deltaN d S.s N) +
      Real.sqrt (Cb * deltaN d S.s N))) atTop (𝓝 0) := by
    have h1 := hs_t.const_mul Cb
    have h2 : Tendsto (fun N : ℕ => Real.sqrt (Cb * deltaN d S.s N)) atTop (𝓝 0) := by
      have := (hδ_t.const_mul Cb).sqrt
      simpa using this
    have := (h1.add h2).const_mul C
    simpa using this
  have hu2 : Tendsto (fun N : ℕ => C * (Cb * (Real.sqrt N * deltaN d S.s N) +
      (Cb * deltaN d S.s N) ^ ((1 : ℝ) / 4))) atTop (𝓝 0) := by
    have h1 := hs_t.const_mul Cb
    have h2 : Tendsto (fun N : ℕ => (Cb * deltaN d S.s N) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
      have := (hδ_t.const_mul Cb).rpow_const (p := (1 : ℝ) / 4) (Or.inr (by norm_num))
      simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using this
    have := (h1.add h2).const_mul C
    simpa using this
  have hK1 : ENNReal.ofReal C₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hR1 := therm_tendsto_rhs _ hu1 C c hc a ha (ENNReal.ofReal C₀) hK1
  have hR2 := therm_tendsto_rhs _ hu2 C c hc a ha (ENNReal.ofReal C₀) hK1
  -- the two estimates of `thermalization`
  have hEst : ∀ N, 2 ≤ N →
      ENNReal.ofReal (smoothDist 2 (S.etaLaw m T (a N) (P N) (X N)) (law P'' (windowPath m T 0 Z))) ≤
        ENNReal.ofReal (C * (Cb * (Real.sqrt N * deltaN d S.s N) + Real.sqrt (Cb * deltaN d S.s N))) +
          ENNReal.ofReal (C * Real.exp (-c * a N)) * (1 + ENNReal.ofReal C₀) ∧
      wassersteinE 1 (S.etaLaw m T (a N) (P N) (X N)) (law P'' (windowPath m T 0 Z)) ≤
        ENNReal.ofReal (C * (Cb * (Real.sqrt N * deltaN d S.s N) + (Cb * deltaN d S.s N) ^ ((1 : ℝ) / 4))) +
          ENNReal.ofReal (C * Real.exp (-c * a N)) * (1 + ENNReal.ofReal C₀) := fun N hN => by
    obtain ⟨h1, h2⟩ := hth (a N) (ha0 N) N hN (P N) (X₀ N) (W N) (X N) (hflow N hN) (hfilt N hN)
      (hB N hN).1 P'' Z hZ
    have hr := therm_ratio_bounds (by omega) (hδpos N hN) (hB1 N hN) (hB N hN).2
    have hmono : ENNReal.ofReal (C * Real.exp (-c * a N)) * (1 + ∫⁻ ω, ‖etaE m (X₀ N ω) S.μ0‖ₑ ∂(P N)) ≤
        ENNReal.ofReal (C * Real.exp (-c * a N)) * (1 + ENNReal.ofReal C₀) := by
      gcongr
      exact hmom1 N hN
    constructor
    · refine h1.trans (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le))
        hmono)
      have := Real.sqrt_le_sqrt hr.2
      linarith [hr.1]
    · refine h2.trans (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le))
        hmono)
      have := Real.rpow_le_rpow (div_nonneg (hB1 N hN).le (Nat.cast_nonneg N)) hr.2
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      linarith [hr.1]
  refine ⟨?_, ?_, ?_⟩
  · -- smooth distance
    have h3 : Tendsto (fun N : ℕ => ENNReal.ofReal (smoothDist 2 (S.etaLaw m T (a N) (P N) (X N))
        (law P'' (windowPath m T 0 Z)))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR1
        (Eventually.of_forall fun _ => zero_le)
        (by filter_upwards [eventually_ge_atTop 2] with N hN using (hEst N hN).1)
    have := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp h3
    simpa [Function.comp_def, ENNReal.toReal_ofReal (smoothDist_nonneg _ _ _)] using this
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR2
      (Eventually.of_forall fun _ => zero_le)
      (by filter_upwards [eventually_ge_atTop 2] with N hN using (hEst N hN).2)
  · intro hcond
    obtain ⟨p₀, hp₀, Cj, hCj⟩ := hJ hcond
    obtain ⟨C', c', hC', hc', hth2⟩ := thermalization_W2_proof S m hm T hT ρβ hρβ p₀ hp₀
    have hmom2 : ∀ N, 2 ≤ N → ∫⁻ ω, ‖etaE m (X₀ N ω) S.μ0‖ₑ ^ (2 : ℝ) ∂(P N) ≤ ENNReal.ofReal C₀ :=
      fun N hN => by
      have := (h0 N hN).2 hcond
      rw [← hinit N hN, law, lintegral_map ((hη N (by omega)).enorm.pow_const _)
        (hflow N hN).init_meas] at this
      exact this
    set K2 : ℝ≥0∞ := (ENNReal.ofReal C₀) ^ ((1 : ℝ) / 2) with hK2
    have hK2top : K2 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have hu3 : Tendsto (fun N : ℕ => C' * (Cj * (Real.sqrt N * deltaN d S.s N) +
        (Cb * deltaN d S.s N) ^ ((1 : ℝ) / 4))) atTop (𝓝 0) := by
      have h1 := hs_t.const_mul Cj
      have h2 : Tendsto (fun N : ℕ => (Cb * deltaN d S.s N) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
        have := (hδ_t.const_mul Cb).rpow_const (p := (1 : ℝ) / 4) (Or.inr (by norm_num))
        simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using this
      have := (h1.add h2).const_mul C'
      simpa using this
    have hR3 := therm_tendsto_rhs _ hu3 C' c' hc' a ha K2 hK2top
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR3
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hcj := hCj N hN
    rw [← hinit N hN] at hcj
    have h2 := hth2 (a N) (ha0 N) N hN (P N) (X₀ N) (W N) (X N) (hflow N hN) (hfilt N hN)
      (hB N hN).1 hcj.1 P'' Z hZ
    have hr := therm_ratio_bounds (by omega) (hδpos N hN) (hB1 N hN) (hB N hN).2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
    have hJr : S.J N (law (P N) (X₀ N)) p₀ / Real.sqrt N ≤ Cj * (Real.sqrt N * deltaN d S.s N) := by
      rw [div_le_iff₀ hs0]
      calc S.J N (law (P N) (X₀ N)) p₀ ≤ Cj * ((N : ℝ) * deltaN d S.s N) := hcj.2
        _ = Cj * (Real.sqrt N * deltaN d S.s N) * Real.sqrt N := by
          linear_combination (Cj * deltaN d S.s N) * hsq
    have hmono : ENNReal.ofReal (C' * Real.exp (-c' * a N)) *
        (1 + (∫⁻ ω, ‖etaE m (X₀ N ω) S.μ0‖ₑ ^ (2 : ℝ) ∂(P N)) ^ ((1 : ℝ) / 2)) ≤
        ENNReal.ofReal (C' * Real.exp (-c' * a N)) * (1 + K2) := by
      gcongr
      exact ENNReal.rpow_le_rpow (hmom2 N hN) (by norm_num)
    refine h2.trans (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC'.le))
      hmono)
    have := Real.rpow_le_rpow (div_nonneg (hB1 N hN).le (Nat.cast_nonneg N)) hr.2
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith

example := (@thermalization_limit_proof : type_of% @HRS.Main.thermalization_limit)

end Main

end HRS

import HRS.Main.ThermAux9
import HRS.Main.ThermAux14

/-!
# THERM: relocated proofs of the frozen statements of Example 2.6 / Corollary 2.7

RELOCATION PATTERN: the frozen statements of `HRS/Main/Headline.lean` are not edited; each proved one is restated
VERBATIM here as `<name>_proof` and tied by `example := (@<name>_proof : type_of% @HRS.Main.<name>)`.

* `mixture_limit_proof` (Example 2.6, TeX M L836-847): part 1 from `ThermAux1`
  (`therm_mixture_marginal`); part 2 from the proved Prop. 5.9 (`HRS.iid_field_mixture_proof`, W_1 clause)
  and `W_1 → 0 ⇒` weak convergence (`ThermAux2`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem mixture_limit_proof (S : PreparedData d) (b : Torus d → ℝ) (hb : Torus.IsSmooth b)
    (hb0 : pair S.μ0 b = 0) (a₀ : ℝ) (m : ℝ) (hm : (d : ℝ) / 2 < m)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussianWithCov m γ (iidCov S.μ0)) :
    (∀ N : ℕ, 1 ≤ N → (∀ x, |a₀ * b x| < Real.sqrt N) →
      IsProbabilityMeasure (mixturePrep S.μ0 b a₀ N) ∧
        firstMarginal (mixturePrep S.μ0 b a₀ N) = S.μ0) ∧
    ConvergesInLaw
      (fun N : ℕ => law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0))
      ((1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
        (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) := by
  refine ⟨fun N hN hpos => therm_mixture_marginal S hb hb0 a₀ N hN hpos, ?_⟩
  have hbc : Continuous b := therm_continuous_of_smooth hb
  have hbm : Measurable b := hbc.measurable
  have hρc : Continuous S.ρ0 := therm_continuous_of_smooth S.hρ0.smooth
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- bounds
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn hbc.continuousOn
  set B : ℝ := |B₀| with hBdef
  have hB : ∀ x, |b x| ≤ B := fun x => by
    have := hB₀ x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hB0 : 0 ≤ B := abs_nonneg _
  obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρc.continuousOn
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρc.continuousOn
  have hc : 0 < S.ρ0 xmin := S.hρ0.pos xmin
  have hbL : MemLp b ⊤ (volume : Measure (Torus d)) :=
    MemLp.of_bound hbc.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hnorm : (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ≤ B := by
    have h1 : eLpNorm b ⊤ (volume : Measure (Torus d)) ≤ ENNReal.ofReal B := by
      rw [eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
      all_goals first | exact hbc.aestronglyMeasurable | skip
    exact ENNReal.toReal_le_of_le_ofReal hB0 h1
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.iid_field_mixture_proof S.hd m hm (S.ρ0 xmin) (S.ρ0 xmax) hc a₀ b
    hbm hbL
  -- threshold
  set N0 : ℕ := ⌈4 * a₀ ^ 2 * B ^ 2⌉₊ + 2 with hN0
  have hNge : ∀ N : ℕ, N0 ≤ N → 2 ≤ N ∧ 4 * a₀ ^ 2 * B ^ 2 + 2 ≤ (N : ℝ) := fun N hN => by
    refine ⟨by omega, ?_⟩
    have h1 : (4 * a₀ ^ 2 * B ^ 2 : ℝ) ≤ ⌈4 * a₀ ^ 2 * B ^ 2⌉₊ := Nat.le_ceil _
    have h2 : ((N0 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    have h3 : ((N0 : ℕ) : ℝ) = ⌈4 * a₀ ^ 2 * B ^ 2⌉₊ + 2 := by rw [hN0]; push_cast; ring
    linarith
  have hposN : ∀ N : ℕ, N0 ≤ N → ∀ x, |a₀ * b x| < Real.sqrt N := fun N hN x => by
    obtain ⟨-, h⟩ := hNge N hN
    rw [abs_mul]
    have h1 : |a₀| * |b x| ≤ |a₀| * B := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
    have h2 : (|a₀| * B) ^ 2 < N := by
      have : (|a₀| * B) ^ 2 = a₀ ^ 2 * B ^ 2 := by rw [mul_pow, sq_abs]
      have h0 : 0 ≤ a₀ ^ 2 * B ^ 2 := by positivity
      linarith
    exact h1.trans_lt (Real.lt_sqrt (by positivity) |>.2 h2)
  -- the limit measure
  haveI hμ0 : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  haveI hγp : IsProbabilityMeasure γ := hγ.1.1.toIsProbabilityMeasure
  set ν : Measure (NegSobolev d m) :=
    (1 / 2 : ℝ≥0∞) • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
        (1 / 2 : ℝ≥0∞) • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) with hν
  haveI hνp : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have e1 : (γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) Set.univ = 1 := by
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp
    have e2 : (γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x))) Set.univ = 1 := by
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp
    simp only [hν, Measure.add_apply, Measure.smul_apply, smul_eq_mul, e1, e2, mul_one]
    rw [one_div, ENNReal.inv_two_add_inv_two]
  have hmeas : ∀ N : ℕ, 1 ≤ N → Measurable (fun X : Config d N => etaE m X S.μ0) := fun N hN => by
    have := measurable_ofMeasureDiff_empirical (N := N) hm2 S.μ0 hN
    unfold etaE flucE
    exact this.const_smul (Real.sqrt N)
  have hprob : ∀ᶠ N : ℕ in atTop,
      IsProbabilityMeasure (law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0)) := by
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hN1 : 1 ≤ N := by have := (hNge N hN).1; omega
    have hP := (therm_mixture_marginal S hb hb0 a₀ N hN1 (hposN N hN)).1
    haveI := hP
    infer_instance
  have hbd : ∀ᶠ N : ℕ in atTop,
      wassersteinE 1 (law (mixturePrep S.μ0 b a₀ N) (fun X => etaE m X S.μ0)) ν ≤
        ENNReal.ofReal (Cm * iidRateW d m N) := by
    filter_upwards [eventually_ge_atTop N0] with N hN
    obtain ⟨hN2, hN4⟩ := hNge N hN
    have h4 : 4 * a₀ ^ 2 * (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤ N := by
      have h1 : (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg hnorm 2
      have h2 : 4 * a₀ ^ 2 * (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤
          4 * a₀ ^ 2 * B ^ 2 := by gcongr
      linarith
    have := (hCm S.ρ0 S.hρ0.density (fun x => by simpa using hxmin (Set.mem_univ x))
      (fun x => by simpa using hxmax (Set.mem_univ x)) hb0 γ hγ N hN2 h4).2.1
    rw [← therm_mixturePrep_eq S b hbm a₀ N] at this
    simp only [therm_ofFun_smul] at this
    have e : ν = (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) +
        (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - a₀ • NegSobolev.ofFun m (fun x => b x * S.ρ0 x)) := by
      simp [hν, one_div]
    rw [e]
    exact this
  have hW : Tendsto (fun N : ℕ => wassersteinE 1 (law (mixturePrep S.μ0 b a₀ N)
      (fun X => etaE m X S.μ0)) ν) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => ENNReal.ofReal (Cm * iidRateW d m N)) atTop (𝓝 0) := by
      have := (therm_iidRateW_tendsto hm).const_mul Cm
      rw [mul_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => zero_le) hbd
  exact therm_convergesInLaw_of_W1 _ ν hprob hW

example := (@mixture_limit_proof : type_of% @HRS.Main.mixture_limit)

/-- The standard preparations are probability measures (`N ≥ 1`). -/
theorem therm_prep_prob (S : PreparedData d) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) := by
  haveI hμ0 : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  rcases hβ₀.eq_or_lt with h | h
  · subst h
    rw [modulatedGibbs_zero]
    infer_instance
  · have hρc : Continuous S.ρ0 := therm_continuous_of_smooth S.hρ0.smooth
    obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρc.continuousOn
    exact HRS.Q32c.q32c_Q_isProb S.hd S.hs0 S.hsd h (le_max_left 1 (S.ρ0 xmax)) S.hρ0.density
      (fun x => (hxmax (Set.mem_univ x)).trans (le_max_right _ _)) (by omega)

/-- Uniform second moment of `η_N^0` for every standard preparation. -/
theorem therm_prep_sq_bound (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X, ‖etaE m X S.μ0‖ₑ ^ (2 : ℝ) ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) ≤
        ENNReal.ofReal C := by
  haveI hμ0 : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N → ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (therm_eta S.μ0 k X ^ 2) ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) ≤
        ENNReal.ofReal A := by
    rcases hβ₀.eq_or_lt with h | h
    · subst h
      refine ⟨4, by norm_num, fun N hN k => ?_⟩
      rw [modulatedGibbs_zero]
      exact therm_mode_bound_iid S.μ0 (by omega) k
    · exact therm_mode_bound_gibbs S hs h
  refine ⟨A * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)), ?_, fun N hN => ?_⟩
  · exact mul_nonneg hA0 (tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  · exact therm_lintegral_sq_etaE hm2 S.μ0 (by omega) _ hA0 (hA N hN)

theorem standard_preparation_norms_proof (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∫⁻ X, ‖etaE m X S.μ0‖ₑ ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) ≤
        ENNReal.ofReal C ∧
      ((0 < β₀ ∨ S.s = 0) →
        (∫⁻ X, ‖etaE m X S.μ0‖ₑ ^ (2 : ℝ) ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)) ≤
          ENNReal.ofReal C) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := therm_prep_sq_bound S hs m hm hβ₀
  refine ⟨C₂ + 1, fun N hN => ⟨?_, fun _ => (hC₂ N hN).trans (ENNReal.ofReal_le_ofReal (by linarith))⟩⟩
  haveI := therm_prep_prob S hβ₀ (N := N) (by omega)
  have h1 := HRS.lintegral_rpow_mono (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
    (fun X : Config d N => ‖etaE m X S.μ0‖ₑ) (p := 1) (q := 2) (by norm_num) (by norm_num)
  simp only [ENNReal.rpow_one, div_one, one_div] at h1
  refine h1.trans ?_
  have h2 := ENNReal.rpow_le_rpow (hC₂ N hN) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  refine h2.trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg hC₂0 (by norm_num), show C₂ ^ (2⁻¹ : ℝ) = Real.sqrt C₂ by
    rw [Real.sqrt_eq_rpow, one_div]]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [Real.sq_sqrt hC₂0, sq_nonneg (Real.sqrt C₂ - 1), Real.sqrt_nonneg C₂]

example := (@standard_preparation_norms_proof : type_of% @HRS.Main.standard_preparation_norms)

/-- `thermalization_recentered` with the repair `d/2 < m` (see `ThermPlan.lean`: for `m ≤ d/2` the objects are
`ofSeq` junk).  The frozen statement without `hm` is NOT claimed. -/
theorem thermalization_recentered_hm_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) / 2 < m)
    (T : ℝ) (hT : 0 < T)
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
    wassersteinE 2 recentered Q ≤ wassersteinE 2 (S.etaLaw m T a P X) Q + shift :=
  therm_recentered_hm S m hm T hT ρβ hρβ a ha N hN P X₀ W X hflow Q

end Main

end HRS

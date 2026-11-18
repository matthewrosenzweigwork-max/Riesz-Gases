import HRS.MP.SelfSimP5Spec

/-!
# MPP5A (5): regularised strong solutions `ss5_regularised_sol`

`HRS.MP.SelfSimP5Impl.ss5_regularised_sol_proof` has the statement of `HRS.MP.SelfSimP5.ss5_regularised_sol`.
Route as `HRS.MC.CepE3.cep_E3_regularised_sde_proof`: solve on the filtration `ℱ' t = ℱ (max t 0)` by
`exists_sde_solution_global_nonneg` and extend constantly to negative times.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP5Impl

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The filtration `ℱ' t = ℱ (max t 0)`. -/
def ss5r_shift (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' _ _ hst := ℱ.mono (max_le_max hst le_rfl)
  le' _ := ℱ.le _

theorem ss5r_shift_isBrownian [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {B : ℝ≥0 → Ω → ι → ℝ} (hB : IsBrownianFiltration P ℱ B) :
    IsBrownianFiltration P (ss5r_shift ℱ) B where
  complete _ s hs h0 := hB.complete _ s hs h0
  adapted t := by
    have : (ss5r_shift ℱ) (t : ℝ) = ℱ t := congrArg ℱ (max_eq_left t.2)
    rw [this]; exact hB.adapted t
  zero := hB.zero
  cont := hB.cont
  indep_incr s t hst := by
    have : (ss5r_shift ℱ) (s : ℝ) = ℱ s := congrArg ℱ (max_eq_left s.2)
    rw [this]; exact hB.indep_incr s t hst
  gaussian_incr := hB.gaussian_incr

theorem ss5r_cont_ext {E : Type*} [TopologicalSpace E] (f : ℝ → E)
    (hf : ∀ t : ℝ, 0 ≤ t → ContinuousOn f (Icc 0 t)) :
    Continuous fun t => f (max t 0) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set T : ℝ := max t₀ 0 + 1 with hT
  have hg : Continuous fun t : ℝ => min (max t 0) T :=
    (continuous_id.max continuous_const).min continuous_const
  have hmem : ∀ t : ℝ, min (max t 0) T ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_min (le_max_right _ _) (by rw [hT]; linarith [le_max_right t₀ 0]), min_le_right _ _⟩
  have h1 : Continuous fun t => f (min (max t 0) T) :=
    (hf T (by rw [hT]; linarith [le_max_right t₀ 0])).comp_continuous hg hmem
  refine h1.continuousAt.congr ?_
  have : ∀ᶠ t in 𝓝 t₀, t < T := eventually_lt_nhds (by rw [hT]; linarith [le_max_left t₀ 0])
  filter_upwards [this] with t ht
  have : max t 0 ≤ T := max_le ht.le (by rw [hT]; linarith [le_max_right t₀ 0])
  rw [min_eq_left this]

theorem ss5r_isLipschitzDrift {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {K : ℝ≥0}
    (hb : LipschitzWith K b) : IsLipschitzDrift (fun _ : ℝ => b) where
  cont := by
    have : Continuous (Function.uncurry fun (_ : ℝ) => b) := hb.continuous.comp continuous_snd
    exact this.continuousOn
  lip _ := ⟨K, fun _ _ => hb⟩

theorem ss5r_noise_eq (c : ℝ) (w : ι → ℝ) :
    ∑ k, w k • (c • EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ ι) =
      c • (WithLp.toLp 2 w : EuclideanSpace ℝ ι) := by
  ext k
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply]
  rw [Finset.sum_eq_single k]
  · simp; ring
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem ss5_regularised_sol_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsBrownianFiltration P ℱ B)
    {θ : ℝ} (hθ : 0 < θ) {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {K : ℝ≥0}
    (hb : LipschitzWith K b)
    {z₀ : Ω → EuclideanSpace ℝ ι} (hz₀ : Measurable[ℱ 0] z₀) :
    ∃ Z : ℝ → Ω → EuclideanSpace ℝ ι, ss5_IsSol P ℱ B θ b z₀ Z ∧ ∀ ζ, Z 0 ζ = z₀ ζ := by
  have hB' := ss5r_shift_isBrownian hB
  have hz : ∀ t : ℝ, Measurable[ss5r_shift ℱ t] z₀ := fun t =>
    hz₀.mono (ℱ.mono (le_max_right t 0)) le_rfl
  obtain ⟨Y, hY, -⟩ := exists_sde_solution_global_nonneg hB' (fun _ => b) (ss5r_isLipschitzDrift hb)
    (fun k => Real.sqrt (2 * θ) • (EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ ι)) z₀ hz
  refine ⟨fun t ω => Y (max t 0) ω, ⟨fun ω => ?_, fun t ht => ?_, ?_⟩, fun ζ => ?_⟩
  · exact ss5r_cont_ext (fun s => Y s ω) fun t ht => hY.cont ω t ht (WithTop.coe_lt_top t)
  · have heq : (ss5r_shift ℱ) t = ℱ t := congrArg ℱ (max_eq_left ht)
    have := hY.adapted t
    rw [heq] at this
    simpa [max_eq_left ht] using this
  · filter_upwards [hY.eq] with ω h t ht
    obtain ⟨-, h2⟩ := h t ht (WithTop.coe_lt_top t)
    simp only [ofNNRealTime_apply] at h2
    rw [ss5r_noise_eq] at h2
    have hint : ∫ s in (0 : ℝ)..t, b (Y (max s 0) ω) = ∫ s in Icc 0 t, b (Y s ω) := by
      rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      simp only [max_eq_left hs.1]
    show Y (max t 0) ω = z₀ ω + (∫ s in (0 : ℝ)..t, b (Y (max s 0) ω)) +
      Real.sqrt (2 * θ) • WithLp.toLp 2 (B (Real.toNNReal t) ω)
    rw [hint, max_eq_left ht, h2]
  · simpa using hY.init ζ

example := (@ss5_regularised_sol_proof : type_of% @HRS.MP.SelfSimP5.ss5_regularised_sol)

end HRS.MP.SelfSimP5Impl

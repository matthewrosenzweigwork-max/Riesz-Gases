import HRS.Stochastic.SDE
import HRS.Stochastic.Brownian
import HRS.Stochastic.Filtration

/-!
# Packet CEPE3: global strong solutions of the regularised chamber SDE (`cep_E3_regularised_sde`)

`HRS.MC.CepE3.cep_E3_regularised_sde_proof` has the statement of `HRS.MC.Cepa.cep_E3_regularised_sde`.
Route: for each permutation `σ₀` the SDE with deterministic noise vectors `σ' e_{σ₀⁻¹ i}` is solved by
`exists_sde_solution_global_nonneg` (on the filtration `ℱ' t = ℱ (max t 0)`, which makes `z₀` adapted at all
real times and is still a Brownian filtration); the solutions are glued along the `ℱ 0`-measurable partition
`{π = σ₀}` and extended constantly to negative times (so the path is continuous on `ℝ`).
The vocabulary (`Ch`, `cep_noise`, `cep_IsChamberSolution`) is duplicated from the spec file with identical bodies.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE3

open HRS

/-- Chamber coordinates (copy of `HRS.MC.Cepa.Ch`). -/
abbrev Ch (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The chamber-coordinate noise `k ↦ W'_{π k, 0}` (copy of `HRS.MC.Cepa.cep_noise`). -/
def cep_noise {Ω : Type*} {N : ℕ} (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ)
    (t : ℝ) (ω : Ω) : Ch N :=
  WithLp.toLp 2 fun k => W' (Real.toNNReal t) ω (π ω k, 0)

/-- Copy of `HRS.MC.Cepa.cep_IsChamberSolution`. -/
def cep_IsChamberSolution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (π : Ω → Equiv.Perm (Fin N)) (σ' : ℝ) (B : Ch N → Ch N)
    (z₀ : Ω → Ch N) (Z : ℝ → Ω → Ch N) : Prop :=
  (∀ ω, Continuous fun t => Z t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Z t)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Z t ω = z₀ ω + (∫ s in (0 : ℝ)..t, B (Z s ω)) + σ' • cep_noise π W' t ω

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The filtration `ℱ' t = ℱ (max t 0)`. -/
def cepe3_shift (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' s t hst := ℱ.mono (max_le_max hst le_rfl)
  le' t := ℱ.le _

theorem cepe3_shift_isBrownian [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W') :
    IsBrownianFiltration P (cepe3_shift ℱ) W' where
  complete t s hs h0 := hW'.complete _ s hs h0
  adapted t := by
    have : (cepe3_shift ℱ) (t : ℝ) = ℱ t := by
      exact congrArg ℱ (max_eq_left t.2)
    rw [this]; exact hW'.adapted t
  zero := hW'.zero
  cont := hW'.cont
  indep_incr s t hst := by
    have : (cepe3_shift ℱ) (s : ℝ) = ℱ s := by
      exact congrArg ℱ (max_eq_left s.2)
    rw [this]; exact hW'.indep_incr s t hst
  gaussian_incr := hW'.gaussian_incr

/-- Noise vectors for a fixed permutation. -/
def cepe3_sig (σ' : ℝ) (σ₀ : Equiv.Perm (Fin N)) : (Fin N × Fin 1) → Ch N :=
  fun p => σ' • EuclideanSpace.single (σ₀.symm p.1) (1 : ℝ)

theorem cepe3_noise_eq (σ' : ℝ) (σ₀ : Equiv.Perm (Fin N)) (w : (Fin N × Fin 1) → ℝ) :
    ∑ p, w p • cepe3_sig σ' σ₀ p = σ' • (WithLp.toLp 2 fun k => w (σ₀ k, 0) : Ch N) := by
  ext k
  simp only [cepe3_sig, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, EuclideanSpace.single_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
  rw [Finset.sum_eq_single (σ₀ k)]
  · simp
    ring
  · intro b _ hb
    have : ¬ (k = σ₀.symm b) := fun h => hb (by rw [h]; simp)
    simp [this]
  · simp


theorem cepe3_isLipschitzDrift {B : Ch N → Ch N} {L : ℝ≥0} (hB : LipschitzWith L B) :
    IsLipschitzDrift (fun _ : ℝ => B) where
  cont := by
    have : Continuous (Function.uncurry fun (_ : ℝ) => B) := hB.continuous.comp continuous_snd
    exact this.continuousOn
  lip _ := ⟨L, fun _ _ => hB⟩

theorem cepe3_glue {Ω' : Type*} {m : MeasurableSpace Ω'} {N : ℕ}
    (π : Ω' → Equiv.Perm (Fin N)) (F : Equiv.Perm (Fin N) → Ω' → Ch N)
    (hF : ∀ σ, Measurable[m] (F σ)) (hπ : ∀ σ, MeasurableSet[m] {ω | π ω = σ}) :
    Measurable[m] (fun ω => F (π ω) ω) := by
  refine measurable_of_isOpen fun S hS => ?_
  have : (fun ω => F (π ω) ω) ⁻¹' S = ⋃ σ, {ω | π ω = σ} ∩ F σ ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨π ω, rfl, h⟩, fun ⟨σ, h1, h2⟩ => by rw [h1]; exact h2⟩
  rw [this]
  exact MeasurableSet.iUnion fun σ => (hπ σ).inter (hF σ hS.measurableSet)

theorem cepe3_cont_ext (f : ℝ → Ch N) (hf : ∀ t : ℝ, 0 ≤ t → ContinuousOn f (Icc 0 t)) :
    Continuous fun t => f (max t 0) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  set T : ℝ := max t₀ 0 + 1 with hT
  have hg : Continuous fun t : ℝ => min (max t 0) T := (continuous_id.max continuous_const).min continuous_const
  have hmem : ∀ t : ℝ, min (max t 0) T ∈ Icc (0 : ℝ) T := fun t =>
    ⟨le_min (le_max_right _ _) (by rw [hT]; linarith [le_max_right t₀ 0]), min_le_right _ _⟩
  have h1 : Continuous fun t => f (min (max t 0) T) :=
    (hf T (by rw [hT]; linarith [le_max_right t₀ 0])).comp_continuous hg hmem
  refine h1.continuousAt.congr ?_
  have : ∀ᶠ t in 𝓝 t₀, t < T := eventually_lt_nhds (by rw [hT]; linarith [le_max_left t₀ 0])
  filter_upwards [this] with t ht
  have : max t 0 ≤ T := max_le ht.le (by rw [hT]; linarith [le_max_right t₀ 0])
  rw [min_eq_left this]

theorem cep_E3_regularised_sde_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {B : Ch N → Ch N} {L : ℝ≥0} (hB : LipschitzWith L B) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) :
    ∃ Z : ℝ → Ω → Ch N, cep_IsChamberSolution P ℱ W' π σ' B z₀ Z := by
  classical
  have hW'' := cepe3_shift_isBrownian hW'
  have hz : ∀ t : ℝ, Measurable[cepe3_shift ℱ t] z₀ := fun t =>
    hz₀.mono (ℱ.mono (le_max_right t 0)) le_rfl
  have hex : ∀ σ₀ : Equiv.Perm (Fin N), ∃ Y : ℝ → Ω → Ch N,
      IsAdditiveSDESolution P (cepe3_shift ℱ) W' (fun _ => B) (cepe3_sig σ' σ₀) z₀ (fun _ => ⊤) Y :=
    fun σ₀ => (exists_sde_solution_global_nonneg hW'' _ (cepe3_isLipschitzDrift hB) _ z₀ hz).imp
      fun Y h => h.1
  choose Y hY using hex
  refine ⟨fun t ω => Y (π ω) (max t 0) ω, fun ω => ?_, fun t ht => ?_, ?_⟩
  · exact cepe3_cont_ext (fun s => Y (π ω) s ω) fun t ht => (hY (π ω)).cont ω t ht (WithTop.coe_lt_top t)
  · have heq : (cepe3_shift ℱ) t = ℱ t := congrArg ℱ (max_eq_left ht)
    have hm : ∀ σ₀, Measurable[ℱ t] (Y σ₀ t) := fun σ₀ => by
      have := (hY σ₀).adapted t
      rw [heq] at this
      exact this
    have := cepe3_glue (m := ℱ t) π (fun σ₀ => Y σ₀ t) hm (fun σ₀ => ℱ.mono ht _ (hπ σ₀))
    simpa [max_eq_left ht] using this
  · have hall : ∀ᵐ ω ∂P, ∀ σ₀ : Equiv.Perm (Fin N), ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < ⊤ →
        IntegrableOn (fun s => B (Y σ₀ s ω)) (Icc 0 t) ∧
        Y σ₀ t ω = z₀ ω + (∫ s in Icc 0 t, B (Y σ₀ s ω)) +
          ∑ k, ofNNRealTime W' t ω k • cepe3_sig σ' σ₀ k :=
      ae_all_iff.2 fun σ₀ => (hY σ₀).eq
    filter_upwards [hall] with ω h t ht
    obtain ⟨-, h2⟩ := h (π ω) t ht (WithTop.coe_lt_top t)
    simp only [ofNNRealTime_apply] at h2
    rw [cepe3_noise_eq] at h2
    have hint : ∫ s in (0 : ℝ)..t, B (Y (π ω) (max s 0) ω) = ∫ s in Icc 0 t, B (Y (π ω) s ω) := by
      rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      simp only [max_eq_left hs.1]
    show Y (π ω) (max t 0) ω = z₀ ω + (∫ s in (0 : ℝ)..t, B (Y (π ω) (max s 0) ω)) +
      σ' • cep_noise π W' t ω
    rw [hint, max_eq_left ht, h2]
    rfl

end HRS.MC.CepE3

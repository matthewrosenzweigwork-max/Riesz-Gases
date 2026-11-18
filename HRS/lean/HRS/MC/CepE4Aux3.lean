import HRS.MC.CepE4Aux2
import HRS.Stochastic.Brownian
import HRS.Stochastic.Filtration

/-!
# Packet CEPE4, auxiliary 3: the chamber noise as a vector Brownian-like process

`E4Noise` collects the properties of `w_t = cep_noise π W' t` used by the second-moment identity: continuity,
measurability, `w_0 = 0`, `E |w_t|² = N t`, and `E ⟨β, w_t - w_s⟩ = 0` for `ℱ_s`-measurable `L²` vectors `β`
(this is where the `ℱ_0`-measurable labelling `π` is handled, by splitting over `{π = σ}`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Glueing along a finite measurable partition. -/
theorem e4_glue {Ω' : Type*} {m : MeasurableSpace Ω'} {N : ℕ}
    (π : Ω' → Equiv.Perm (Fin N)) (F : Equiv.Perm (Fin N) → Ω' → Ch N)
    (hF : ∀ σ, Measurable[m] (F σ)) (hπ : ∀ σ, MeasurableSet[m] {ω | π ω = σ}) :
    Measurable[m] (fun ω => F (π ω) ω) := by
  refine measurable_of_isOpen fun S hS => ?_
  have : (fun ω => F (π ω) ω) ⁻¹' S = ⋃ σ, {ω | π ω = σ} ∩ F σ ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨π ω, rfl, h⟩, fun ⟨σ, h1, h2⟩ => by rw [h1]; exact h2⟩
  rw [this]
  exact MeasurableSet.iUnion fun σ => (hπ σ).inter (hF σ hS.measurableSet)

/-- Properties of the noise process used in the second-moment identity. -/
structure E4Noise (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (N : ℕ) (w : ℝ → Ω → Ch N) : Prop where
  cont : ∀ ω, Continuous fun t => w t ω
  meas : ∀ t, Measurable (w t)
  zero : ∀ ω, w 0 ω = 0
  memLp : ∀ t, MemLp (fun ω => ‖w t ω‖) 2 P
  sq : ∀ t, 0 ≤ t → ∫ ω, ‖w t ω‖ ^ 2 ∂P = N * t
  incr : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ β : Ω → Ch N, Measurable[ℱ s] β →
    MemLp (fun ω => ‖β ω‖) 2 P → ∫ ω, inner ℝ (β ω) (w t ω - w s ω) ∂P = 0

theorem e4_noise_cont {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hc : ∀ ω, Continuous fun t => W' t ω)
    (π : Ω → Equiv.Perm (Fin N)) (ω : Ω) : Continuous fun t : ℝ => cep_noise π W' t ω := by
  unfold cep_noise
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  exact (continuous_apply _).comp ((hc ω).comp continuous_real_toNNReal)

theorem e4_noise_apply (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (t : ℝ) (ω : Ω)
    (k : Fin N) : (cep_noise π W' t ω) k = W' (Real.toNNReal t) ω (π ω k, 0) := rfl

theorem e4_noise_norm_sq (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (t : ℝ) (ω : Ω) :
    ‖cep_noise π W' t ω‖ ^ 2 = ∑ i : Fin N, (W' (Real.toNNReal t) ω (i, 0)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, e4_noise_apply]
  exact Equiv.sum_comp (π ω) (fun i => (W' (Real.toNNReal t) ω (i, 0)) ^ 2)

theorem e4_noise_meas [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) (t : ℝ) :
    Measurable (cep_noise π W' t) := by
  have := e4_glue (m := mΩ) π (fun σ ω => (WithLp.toLp 2 fun k => W' (Real.toNNReal t) ω (σ k, 0) : Ch N))
    (fun σ => (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp
      (measurable_pi_iff.2 fun k => hW'.measurable_coord (Real.toNNReal t) (σ k, 0)))
    (fun σ => ℱ.le 0 _ (hπ σ))
  exact this

theorem e4_noise_incr [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (β : Ω → Ch N) (hβ : Measurable[ℱ s] β) (hβ2 : MemLp (fun ω => ‖β ω‖) 2 P) :
    ∫ ω, inner ℝ (β ω) (cep_noise π W' t ω - cep_noise π W' s ω) ∂P = 0 := by
  classical
  set g : Equiv.Perm (Fin N) → Fin N → Ω → ℝ :=
    fun σ k => {ω | π ω = σ}.indicator (fun ω => β ω k) with hg
  set Δ : (Fin N × Fin 1) → Ω → ℝ :=
    fun p ω => ofNNRealTime W' t ω p - ofNNRealTime W' s ω p with hΔ
  have hpt : ∀ ω, inner ℝ (β ω) (cep_noise π W' t ω - cep_noise π W' s ω) =
      ∑ σ : Equiv.Perm (Fin N), ∑ k : Fin N, g σ k ω * Δ (σ k, 0) ω := by
    intro ω
    rw [Finset.sum_eq_single (π ω)]
    · simp only [PiLp.inner_apply, hg, hΔ, e4_noise_apply, Set.indicator_apply, ite_true, ofNNRealTime_apply, WithLp.ofLp_sub, Pi.sub_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [hg, Set.indicator_apply, Ne.symm hσ]
    · simp
  have hgm : ∀ σ k, StronglyMeasurable[ℱ s] (g σ k) := by
    intro σ k
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.indicator ?_ (ℱ.mono hs _ (hπ σ))
    exact (measurable_pi_apply k).comp ((WithLp.measurable_ofLp (p := 2) (X := Fin N → ℝ)).comp hβ)
  have hgL : ∀ σ k, MemLp (g σ k) 2 P := by
    intro σ k
    have h1 : MemLp (fun ω => β ω k) 2 P := by
      refine hβ2.mono ?_ ?_
      · exact ((measurable_pi_apply k).comp ((WithLp.measurable_ofLp (p := 2) (X := Fin N → ℝ)).comp
          (hβ.mono (ℱ.le s) le_rfl))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun ω => by
          simpa using PiLp.norm_apply_le (β ω) k
    exact h1.indicator (ℱ.le 0 _ (hπ σ))
  have hΔL : ∀ p, MemLp (Δ p) 2 P := fun p => hW'.memLp_two_incr_real hst p
  have hint : ∀ σ k, Integrable (fun ω => g σ k ω * Δ (σ k, 0) ω) P := fun σ k =>
    (hgL σ k).integrable_mul (hΔL _)
  simp_rw [hpt]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun k _ => hint σ k]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [integral_finsetSum _ fun k _ => hint σ k]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h0 := hW'.condExp_mul_incr_real hst (k := (σ k, 0)) (g := g σ k) (hgm σ k) (hint σ k)
  rw [← integral_condExp (ℱ.le s)]
  rw [integral_congr_ae h0]
  simp

theorem e4_noise_cep [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) :
    E4Noise P ℱ N (cep_noise π W') := by
  have hint : ∀ t : ℝ, Integrable (fun ω => ‖cep_noise π W' t ω‖ ^ 2) P := by
    intro t
    simp_rw [e4_noise_norm_sq]
    exact integrable_finsetSum _ fun i _ =>
      (hW'.memLp_coord (Real.toNNReal t) (i, 0) ENNReal.ofNat_ne_top).integrable_sq
  refine ⟨e4_noise_cont hW'.cont π, e4_noise_meas hW' hπ, ?_, ?_, ?_, ?_⟩
  · intro ω
    ext k
    simp [e4_noise_apply, hW'.zero]
  · intro t
    refine (memLp_two_iff_integrable_sq ?_).2 (hint t)
    exact (e4_noise_meas hW' hπ t).norm.aestronglyMeasurable
  · intro t ht
    simp_rw [e4_noise_norm_sq]
    rw [integral_finsetSum _ fun i _ =>
      (hW'.memLp_coord (Real.toNNReal t) (i, 0) ENNReal.ofNat_ne_top).integrable_sq]
    have : ∀ i : Fin N, ∫ ω, (W' (Real.toNNReal t) ω (i, 0)) ^ 2 ∂P = t := by
      intro i
      have := hW'.integral_incr_sq (s := 0) (t := Real.toNNReal t) (by simp) (i, 0)
      simp only [hW'.zero, Pi.zero_apply, sub_zero, NNReal.coe_zero] at this
      rw [this, Real.coe_toNNReal _ ht]
    simp [this]
  · intro s t hs hst β hβ hβ2
    exact e4_noise_incr hW' hπ hs hst β hβ hβ2

end HRS.MC.CepE4

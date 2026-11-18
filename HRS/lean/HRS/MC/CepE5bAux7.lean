import HRS.MC.CepE4Aux3

/-!
# Packet CEPE5B, auxiliary 7: the relabelled noise is a Brownian filtration

For an `ℱ₀`-measurable labelling `π`, `Wp t ω k = W' t ω (π ω k, 0)` is a Brownian motion on `Fin N` for the
filtration `ℱ` clamped at time `0` (`e5b_fil`), so Itô's formula applies to the chamber noise without splitting
over `{π = σ}`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- The filtration clamped at time `0` (so that `ℱ₀`-measurable data are `ℱ t`-measurable for all real `t`). -/
def e5b_fil (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' _ _ h := ℱ.mono (max_le_max h le_rfl)
  le' t := ℱ.le _

theorem e5b_fil_apply (ℱ : Filtration ℝ mΩ) (t : ℝ≥0) : (e5b_fil ℱ) (t : ℝ) = ℱ (t : ℝ) := by
  show ℱ (max (t : ℝ) 0) = ℱ (t : ℝ)
  rw [max_eq_left (NNReal.coe_nonneg t)]

theorem e5b_fil_zero (ℱ : Filtration ℝ mΩ) : (e5b_fil ℱ) 0 = ℱ 0 := by
  show ℱ (max (0 : ℝ) 0) = ℱ 0
  rw [max_self]

theorem e5b_fil_ge (ℱ : Filtration ℝ mΩ) (t : ℝ) : ℱ 0 ≤ (e5b_fil ℱ) t :=
  ℱ.mono (le_max_right t 0)

theorem e5b_fil_brownian {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}
    (h : IsBrownianFiltration P ℱ W) : IsBrownianFiltration P (e5b_fil ℱ) W where
  complete := fun t s hs h0 => h.complete (max t 0) s hs h0
  adapted := fun t => by rw [e5b_fil_apply]; exact h.adapted t
  zero := h.zero
  cont := h.cont
  indep_incr := fun s t hst => by rw [e5b_fil_apply]; exact h.indep_incr s t hst
  gaussian_incr := h.gaussian_incr

/-- Glueing along a finite measurable partition (general target). -/
theorem e5b_glue {Ω' β : Type*} {m : MeasurableSpace Ω'} [MeasurableSpace β]
    (π : Ω' → Equiv.Perm (Fin N)) (F : Equiv.Perm (Fin N) → Ω' → β)
    (hF : ∀ σ, Measurable[m] (F σ)) (hπ : ∀ σ, MeasurableSet[m] {ω | π ω = σ}) :
    Measurable[m] (fun ω => F (π ω) ω) := by
  intro S hS
  have : (fun ω => F (π ω) ω) ⁻¹' S = ⋃ σ, {ω | π ω = σ} ∩ F σ ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨π ω, rfl, h⟩, fun ⟨σ, h1, h2⟩ => by rw [h1]; exact h2⟩
  rw [this]
  exact MeasurableSet.iUnion fun σ => (hπ σ).inter (hF σ hS)

/-- The relabelled Brownian motion. -/
def e5b_Wp (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) : ℝ≥0 → Ω → Fin N → ℝ :=
  fun t ω k => W' t ω (π ω k, 0)

/-- The increment of the relabelled noise for a fixed labelling. -/
def e5b_Dtau (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (s t : ℝ≥0) (τ : Equiv.Perm (Fin N)) (ω : Ω) :
    Fin N → ℝ := fun k => W' t ω (τ k, 0) - W' s ω (τ k, 0)

theorem e5b_partition [IsProbabilityMeasure P] {π : Ω → Equiv.Perm (Fin N)}
    (hπm : ∀ σ, MeasurableSet {ω | π ω = σ}) {S : Set Ω} (hS : MeasurableSet S) :
    P S = ∑ σ : Equiv.Perm (Fin N), P (S ∩ {ω | π ω = σ}) := by
  have h1 : S = ⋃ σ : Equiv.Perm (Fin N), S ∩ {ω | π ω = σ} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨π ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  conv_lhs => rw [h1]
  rw [measure_iUnion, tsum_fintype]
  · intro σ τ hστ
    refine Set.disjoint_left.2 fun ω h1 h2 => hστ ?_
    have a := h1.2
    have b := h2.2
    simp only [mem_setOf_eq] at a b
    rw [← a, ← b]
  · exact fun σ => hS.inter (hπm σ)

theorem e5b_Dtau_law [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {s t : ℝ≥0} (hst : s ≤ t) (τ : Equiv.Perm (Fin N)) :
    HasLaw (e5b_Dtau W' s t τ) (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) P := by
  have hl := hW'.gaussian_incr s t hst
  set e' : Fin N × Fin 1 ≃ Fin N :=
    { toFun := fun p => τ.symm p.1
      invFun := fun k => (τ k, 0)
      left_inv := fun p => Prod.ext (by simp) (Subsingleton.elim _ _)
      right_inv := fun k => by simp } with he'
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e')
      (Measure.pi fun _ : Fin N × Fin 1 => gaussianReal 0 (t - s))
      (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) :=
    measurePreserving_piCongrLeft (fun _ : Fin N => gaussianReal 0 (t - s)) e'
  have h := hmp.hasLaw.comp hl
  refine h.congr (Eventually.of_forall fun ω => ?_)
  funext k
  simp [e5b_Dtau, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply, he']

theorem e5b_Dtau_measurable {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') (s t : ℝ≥0) (τ : Equiv.Perm (Fin N)) :
    Measurable (e5b_Dtau W' s t τ) := by
  refine measurable_pi_iff.2 fun k => ?_
  exact ((hW'.measurable_coord t (τ k, 0))).sub (hW'.measurable_coord s (τ k, 0))


theorem e5b_Wp_incr_eq (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (s t : ℝ≥0) (ω : Ω) :
    e5b_Wp π W' t ω - e5b_Wp π W' s ω = e5b_Dtau W' s t (π ω) ω := rfl

theorem e5b_Wp_meas {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) (t : ℝ≥0) : Measurable[ℱ t] (e5b_Wp π W' t) := by
  letI : MeasurableSpace Ω := ℱ t
  refine measurable_pi_iff.2 fun k => ?_
  have := e5b_glue (m := ℱ t) π (fun σ ω => W' t ω (σ k, 0))
    (fun σ => (measurable_pi_apply (σ k, 0)).comp (hW'.adapted t))
    (fun σ => ℱ.mono (by simp) _ (hπ σ))
  exact this

theorem e5b_Wp_incr_meas {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) (s t : ℝ≥0) :
    Measurable (fun ω => e5b_Wp π W' t ω - e5b_Wp π W' s ω) := by
  have := e5b_glue (m := mΩ) π (fun σ ω => e5b_Dtau W' s t σ ω)
    (fun σ => e5b_Dtau_measurable hW' s t σ) (fun σ => ℱ.le 0 _ (hπ σ))
  exact this

/-- The joint law of an `ℱ_s`-event and the relabelled increment. -/
theorem e5b_Wp_prob [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) {B : Set (Fin N → ℝ)} (hB : MeasurableSet B) :
    P (A ∩ (fun ω => e5b_Wp π W' t ω - e5b_Wp π W' s ω) ⁻¹' B) =
      P A * (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) B := by
  have hπm : ∀ σ, MeasurableSet {ω | π ω = σ} := fun σ => ℱ.le 0 _ (hπ σ)
  have hAm : MeasurableSet A := ℱ.le s _ hA
  have hmeasS : MeasurableSet (A ∩ (fun ω => e5b_Wp π W' t ω - e5b_Wp π W' s ω) ⁻¹' B) :=
    hAm.inter (e5b_Wp_incr_meas hW' hπ s t hB)
  rw [e5b_partition hπm hmeasS, e5b_partition hπm hAm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hset : A ∩ (fun ω => e5b_Wp π W' t ω - e5b_Wp π W' s ω) ⁻¹' B ∩ {ω | π ω = τ} =
      (e5b_Dtau W' s t τ ⁻¹' B) ∩ (A ∩ {ω | π ω = τ}) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
    have hpt : π ω = τ → e5b_Wp π W' t ω - e5b_Wp π W' s ω = e5b_Dtau W' s t τ ω := by
      intro h3; rw [← h3]; rfl
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h1, h3⟩
      rw [← hpt h3]; exact h2
    · rintro ⟨h2, h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [hpt h3]; exact h2
  rw [hset]
  have hind := hW'.indep_incr s t hst
  have hAτ : MeasurableSet[ℱ s] (A ∩ {ω | π ω = τ}) :=
    hA.inter (ℱ.mono (by simp) _ (hπ τ))
  have hB' : MeasurableSet[MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance]
      (e5b_Dtau W' s t τ ⁻¹' B) := by
    refine ⟨(fun x : (Fin N × Fin 1) → ℝ => fun k : Fin N => x (τ k, 0)) ⁻¹' B, ?_, ?_⟩
    · exact (measurable_pi_iff.2 fun k => measurable_pi_apply (τ k, 0)) hB
    · rfl
  rw [(Indep_iff _ _ _).1 hind _ _ hB' hAτ]
  have hlaw := e5b_Dtau_law hW' hst τ
  rw [← Measure.map_apply (e5b_Dtau_measurable hW' s t τ) hB, hlaw.map_eq, mul_comm]


/-- The relabelled noise is a Brownian motion for the clamped filtration. -/
theorem e5b_Wp_brownian [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) :
    IsBrownianFiltration P (e5b_fil ℱ) (e5b_Wp π W') where
  complete := (e5b_fil_brownian hW').complete
  adapted := fun t => by rw [e5b_fil_apply]; exact e5b_Wp_meas hW' hπ t
  zero := fun ω => by funext k; simp [e5b_Wp, hW'.zero]
  cont := fun ω => continuous_pi fun k => (continuous_apply _).comp (hW'.cont ω)
  indep_incr := fun s t hst => by
    rw [e5b_fil_apply]
    rw [Indep_iff]
    intro t1 t2 h1 h2
    obtain ⟨B, hB, rfl⟩ := h1
    have h3 := e5b_Wp_prob hW' hπ hst h2 hB
    have h0 := e5b_Wp_prob hW' hπ hst (A := univ) MeasurableSet.univ hB
    simp only [univ_inter, measure_univ, one_mul] at h0
    rw [inter_comm, h3, h0, mul_comm]
  gaussian_incr := fun s t hst => by
    refine ⟨(e5b_Wp_incr_meas hW' hπ s t).aemeasurable, ?_⟩
    ext B hB
    rw [Measure.map_apply (e5b_Wp_incr_meas hW' hπ s t) hB]
    have h0 := e5b_Wp_prob hW' hπ hst (A := univ) MeasurableSet.univ hB
    simpa using h0

end HRS.MC.CepE5b

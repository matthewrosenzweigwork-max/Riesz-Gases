import HRS.MC.CepH2Defs
import HRS.Stochastic.Ito

/-!
# CEPH2, S1a: the permuted chamber noise is a Brownian filtration
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- Reindexing of a coordinate vector by a permutation. -/
def h2_reidx (σ : Equiv.Perm (Fin N)) (y : (Fin N × Fin 1) → ℝ) : Fin N → ℝ := fun k => y (σ k, 0)

theorem h2_measurable_reidx (σ : Equiv.Perm (Fin N)) : Measurable (h2_reidx σ) :=
  measurable_pi_iff.2 fun k => measurable_pi_apply _

theorem h2_pi_reidx (σ : Equiv.Perm (Fin N)) (v : ℝ≥0) :
    (Measure.pi fun _ : (Fin N × Fin 1) => gaussianReal 0 v).map (h2_reidx σ) =
      Measure.pi fun _ : Fin N => gaussianReal 0 v := by
  symm
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply (h2_measurable_reidx σ) (MeasurableSet.univ_pi hS)]
  have e : h2_reidx σ ⁻¹' (Set.pi Set.univ S) =
      Set.pi Set.univ (fun p : Fin N × Fin 1 => S (σ.symm p.1)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, h2_reidx]
    constructor
    · intro h p
      have := h (σ.symm p.1)
      obtain ⟨j, i⟩ := p
      have i0 : i = 0 := Subsingleton.elim _ _
      subst i0
      simpa using this
    · intro h k
      have := h (σ k, 0)
      simpa using this
  rw [e, Measure.pi_pi]
  rw [Fintype.prod_prod_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  exact Equiv.prod_comp σ.symm (fun k => gaussianReal 0 v (S k))

/-- Gluing of measurable maps along a measurable `Perm`-valued labelling. -/
theorem h2_glue_measurable {Ω : Type*} {m : MeasurableSpace Ω} {β : Type*} [MeasurableSpace β]
    (π : Ω → Equiv.Perm (Fin N)) (F : Equiv.Perm (Fin N) → Ω → β)
    (hF : ∀ σ, Measurable[m] (F σ)) (hπ : ∀ σ, MeasurableSet[m] {ω | π ω = σ}) :
    Measurable[m] (fun ω => F (π ω) ω) := by
  intro S hS
  have : (fun ω => F (π ω) ω) ⁻¹' S = ⋃ σ, {ω | π ω = σ} ∩ F σ ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun h => ⟨π ω, rfl, h⟩, fun ⟨σ, h1, h2⟩ => by rw [h1]; exact h2⟩
  rw [this]
  exact MeasurableSet.iUnion fun σ => (hπ σ).inter (hF σ hS)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Key factorisation: `P(A ∩ {Δ̃ ∈ S}) = P(A) γ(S)` for `A ∈ ℱ s`. -/
theorem h2_noise_key [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) {S : Set (Fin N → ℝ)}
    (hS : MeasurableSet S) :
    P (A ∩ {ω | h2_reidx (π ω) (W' t ω - W' s ω) ∈ S}) =
      P A * (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) S := by
  set Δ : Ω → (Fin N × Fin 1) → ℝ := fun ω => W' t ω - W' s ω with hΔ
  have hWt : Measurable (W' t) := (hW'.adapted t).mono (ℱ.le _) le_rfl
  have hWs : Measurable (W' s) := (hW'.adapted s).mono (ℱ.le _) le_rfl
  have hΔm : Measurable Δ :=
    measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp hWt).sub ((measurable_pi_apply i).comp hWs)
  have hℱ0s : ℱ 0 ≤ ℱ (s : ℝ) := ℱ.mono s.2
  have hpart : ∀ σ : Equiv.Perm (Fin N), A ∩ {ω | π ω = σ} ∩ Δ ⁻¹' (h2_reidx σ ⁻¹' S) =
      (A ∩ {ω | h2_reidx (π ω) (W' t ω - W' s ω) ∈ S}) ∩ {ω | π ω = σ} := by
    intro σ
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, hΔ]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by rw [h2]; exact h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, by rw [h2] at h3; exact h3⟩
  have hunion : A ∩ {ω | h2_reidx (π ω) (W' t ω - W' s ω) ∈ S} =
      ⋃ σ, (A ∩ {ω | π ω = σ} ∩ Δ ⁻¹' (h2_reidx σ ⁻¹' S)) := by
    ext ω
    simp only [mem_iUnion, hpart, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h; exact ⟨π ω, h, rfl⟩
    · rintro ⟨σ, h, h2⟩; exact h
  have hmeasπ : ∀ σ, MeasurableSet {ω | π ω = σ} := fun σ => ℱ.le _ _ (hπ σ)
  have hmeasA : MeasurableSet A := ℱ.le _ _ hA
  have hmeasΔ : ∀ σ, MeasurableSet (Δ ⁻¹' (h2_reidx σ ⁻¹' S)) := fun σ =>
    hΔm ((h2_measurable_reidx σ) hS)
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin N) =>
      A ∩ {ω | π ω = σ} ∩ Δ ⁻¹' (h2_reidx σ ⁻¹' S)) := by
    intro σ τ hστ
    refine Set.disjoint_left.2 fun ω h1 h2 => hστ ?_
    exact h1.1.2.symm.trans h2.1.2
  have hlaw : ∀ σ, P (Δ ⁻¹' (h2_reidx σ ⁻¹' S)) =
      (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) S := by
    intro σ
    have h1 := (hW'.gaussian_incr s t hst).map_eq
    have e1 : P (Δ ⁻¹' (h2_reidx σ ⁻¹' S)) = (P.map Δ) (h2_reidx σ ⁻¹' S) :=
      (Measure.map_apply hΔm ((h2_measurable_reidx σ) hS)).symm
    rw [e1, h1, ← Measure.map_apply (h2_measurable_reidx σ) hS, h2_pi_reidx σ (t - s)]
  have hind : ∀ σ, P (A ∩ {ω | π ω = σ} ∩ Δ ⁻¹' (h2_reidx σ ⁻¹' S)) =
      P (A ∩ {ω | π ω = σ}) * (Measure.pi fun _ : Fin N => gaussianReal 0 (t - s)) S := by
    intro σ
    have hi := (Indep_iff _ _ _).1 (hW'.indep_incr s t hst).symm (A ∩ {ω | π ω = σ})
      (Δ ⁻¹' (h2_reidx σ ⁻¹' S)) (hA.inter (hℱ0s _ (hπ σ))) ⟨_, (h2_measurable_reidx σ) hS, rfl⟩
    rw [hi, hlaw σ]
  rw [hunion, measure_iUnion hdisj (fun σ => ((hmeasA.inter (hmeasπ σ)).inter (hmeasΔ σ))), tsum_fintype]
  simp_rw [hind]
  rw [← Finset.sum_mul]
  congr 1
  have hA' : A = ⋃ σ, A ∩ {ω | π ω = σ} := by
    ext ω; simp
  conv_rhs => rw [hA']
  rw [measure_iUnion (fun σ τ hστ => Set.disjoint_left.2 fun ω h1 h2 => hστ (h1.2.symm.trans h2.2))
    (fun σ => hmeasA.inter (hmeasπ σ)), tsum_fintype]

/-- **S1a**.  The chamber noise `k ↦ W'_{π k, 0}` is a Brownian filtration for `ℱ` when `π` is `ℱ₀`-measurable. -/
theorem cepH2_noise_brownian_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) :
    IsBrownianFiltration P ℱ (fun (t : ℝ≥0) (ω : Ω) (k : Fin N) => W' t ω (π ω k, 0)) where
  complete := hW'.complete
  adapted t := by
    have h0t : ℱ 0 ≤ ℱ (t : ℝ) := ℱ.mono t.2
    exact h2_glue_measurable π (fun σ ω => h2_reidx σ (W' t ω))
      (fun σ => (h2_measurable_reidx σ).comp (hW'.adapted t)) (fun σ => h0t _ (hπ σ))
  zero ω := by
    funext k
    simp [hW'.zero]
  cont ω := continuous_pi fun k => (continuous_apply _).comp (hW'.cont ω)
  indep_incr s t hst := by
    rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S, hS, rfl⟩ := ht1
    have e : (fun ω => (fun k => W' t ω (π ω k, 0)) - (fun k => W' s ω (π ω k, 0))) ⁻¹' S =
        {ω | h2_reidx (π ω) (W' t ω - W' s ω) ∈ S} := rfl
    rw [e]
    have k1 := h2_noise_key hW' hπ hst ht2 hS
    have k2 := h2_noise_key hW' hπ hst (A := Set.univ) MeasurableSet.univ hS
    rw [Set.univ_inter, measure_univ, one_mul] at k2
    rw [Set.inter_comm, k1, k2, mul_comm]
  gaussian_incr s t hst := by
    have hWt : ∀ u : ℝ≥0, Measurable (fun ω => (fun k => W' u ω (π ω k, 0))) := fun u => by
      have h0t : ℱ 0 ≤ ℱ (u : ℝ) := ℱ.mono u.2
      exact (h2_glue_measurable π (fun σ ω => h2_reidx σ (W' u ω))
        (fun σ => (h2_measurable_reidx σ).comp (hW'.adapted u)) (fun σ => h0t _ (hπ σ))).mono
        (ℱ.le _) le_rfl
    have hm : Measurable (fun ω => (fun k => W' t ω (π ω k, 0)) - (fun k => W' s ω (π ω k, 0))) :=
      measurable_pi_iff.2 fun k => ((measurable_pi_apply k).comp (hWt t)).sub
        ((measurable_pi_apply k).comp (hWt s))
    refine ⟨hm.aemeasurable, Measure.ext fun S hS => ?_⟩
    rw [Measure.map_apply hm hS]
    have k2 := h2_noise_key hW' hπ hst (A := Set.univ) MeasurableSet.univ hS
    rw [Set.univ_inter, measure_univ, one_mul] at k2
    exact k2

/-- The filtration `ℱ' t = ℱ (max t 0)`. -/
def h2_shift (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' s t hst := ℱ.mono (max_le_max hst le_rfl)
  le' t := ℱ.le _

theorem h2_shift_eq (ℱ : Filtration ℝ mΩ) {t : ℝ} (ht : 0 ≤ t) : h2_shift ℱ t = ℱ t :=
  congrArg ℱ (max_eq_left ht)

theorem h2_shift_isBrownian {ι : Type*} [Fintype ι] [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) :
    IsBrownianFiltration P (h2_shift ℱ) W where
  complete t s hs h0 := hW.complete _ s hs h0
  adapted t := (hW.adapted t).mono (ℱ.mono (le_max_left (t : ℝ) 0)) le_rfl
  zero := hW.zero
  cont := hW.cont
  indep_incr s t hst := by
    have e : ℱ (max (s : ℝ) 0) = ℱ s := congrArg ℱ (max_eq_left s.2)
    have := hW.indep_incr s t hst
    rw [← e] at this
    exact this
  gaussian_incr := hW.gaussian_incr

end HRS.MC.CepH2

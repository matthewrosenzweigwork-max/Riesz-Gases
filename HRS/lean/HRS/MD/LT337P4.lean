import HRS.MD.LT337Vocab
import HRS.Stochastic.Filtration

/-!
# Packet LT4 (chunk D): the localising stopping times of Prop 3.37

`lt4_stopping_proof` is the statement `HRS.MD.LT337.lt4_stopping` (M L3137), written with the sorry-free vocabulary
copy `HRS.MD.LT337Vocab`.  `IsFilteredSolution` carries a complete Brownian filtration
(`IsBrownianFiltration.complete`), so instead of the explicit lift one uses an everywhere continuous modification
`Y` of `X` on a measurable null set; `τ_ε` is the exit time of `Y` from `{∀ i ≠ j, ε < ‖z_i - z_j‖}`
(the same sup norm as in `StoppingFamily.sep`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.MD.LT337Vocab

namespace HRS.MD.LT337P4

variable {d N : ℕ}

/-- The open set `{z : ∀ i ≠ j, ε < ‖z_i - z_j‖}` of `ε`-separated configurations (sup norm on the torus). -/
def sepSet (d N : ℕ) (ε : ℝ) : Set (Config d N) := {z | ∀ i j, i ≠ j → ε < ‖z i - z j‖}

theorem isOpen_sepSet (ε : ℝ) : IsOpen (sepSet d N ε) := by
  have : sepSet d N ε = ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {z : Config d N | ε < ‖z i - z j‖} := by
    ext z; simp [sepSet]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_lt continuous_const (by fun_prop)

/-- The modification of `X` on the set `N0`: constant `0` there, `X (t⁺)` elsewhere. -/
def modX {Ω : Type*} (N0 : Set Ω) (X : ℝ≥0 → Ω → Config d N) : ℝ → Ω → Config d N :=
  fun t ω => by classical exact if ω ∈ N0 then (fun _ => 0) else X (Real.toNNReal t) ω

theorem modX_of_notMem {Ω : Type*} {N0 : Set Ω} {X : ℝ≥0 → Ω → Config d N} {ω : Ω} (hω : ω ∉ N0)
    (t : ℝ) : modX N0 X t ω = X (Real.toNNReal t) ω := by
  simp [modX, hω]

/-- Adaptedness of the modification (uses the completeness of the filtration). -/
theorem modX_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    (hℱ : IsCompleteFiltration P ℱ) {X : ℝ≥0 → Ω → Config d N}
    (hXad : ∀ t : ℝ, Measurable[ℱ t] (X (Real.toNNReal t)))
    {N0 : Set Ω} (hN0 : MeasurableSet N0) (hN0P : P N0 = 0) (t : ℝ) :
    Measurable[ℱ t] (modX N0 X t) := by
  classical
  have hN0t : MeasurableSet[ℱ t] N0 := hℱ t N0 hN0 hN0P
  have hmeas : Measurable[ℱ t] (modX N0 X t) := by
    unfold modX
    exact Measurable.ite hN0t measurable_const (hXad t)
  exact hmeas

theorem lt4_stopping_proof (hd : 2 ≤ d) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {D : DynData d} {N : ℕ} {T Λ ΛV Mb : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ τ : ℝ → Ω → WithTop ℝ, StoppingFamily P ℱ X T τ := by
  classical
  -- a measurable null set off which the paths are continuous
  set p : Ω → Prop := fun ω => ∀ i, Continuous fun t : ℝ≥0 => X t ω i with hp
  have hpae : ∀ᵐ ω ∂P, p ω := h.sol.cont
  set N0 : Set Ω := toMeasurable P {ω | ¬ p ω} with hN0
  have hN0m : MeasurableSet N0 := measurableSet_toMeasurable _ _
  have hN0P : P N0 = 0 := by rw [hN0, measure_toMeasurable]; exact ae_iff.1 hpae
  have hpN : ∀ ω, ω ∉ N0 → p ω := fun ω hω => by_contra fun hc => hω (subset_toMeasurable _ _ hc)
  have hnotN0 : ∀ᵐ ω ∂P, ω ∉ N0 := by rw [ae_iff]; simpa using hN0P
  set Y : ℝ → Ω → Config d N := modX N0 X with hY
  -- progressivity gives adaptedness of `X (t⁺)`
  have hXad : ∀ t : ℝ, Measurable[ℱ t] (X (Real.toNNReal t)) := fun t => hF.progressive.adapted t
  have hYad : Adapted ℱ Y := fun t => modX_measurable hF.brownian.complete hXad hN0m hN0P t
  have hYcont : ∀ ω, Continuous fun t => Y t ω := by
    intro ω
    by_cases hω : ω ∈ N0
    · simp [hY, modX, hω]; exact continuous_const
    · have : (fun t => Y t ω) = fun t => X (Real.toNNReal t) ω := funext fun t => modX_of_notMem hω t
      rw [this]
      exact continuous_pi fun i => (hpN ω hω i).comp continuous_real_toNNReal
  refine ⟨fun ε => exitTime Y (sepSet d N ε) 0, ?_⟩
  refine ⟨fun ε => isStoppingTime_exitTime ℱ Y hYad hYcont (isOpen_sepSet ε) 0, fun ε ω => ?_, ?_, ?_⟩
  · exact le_hittingAfter ω
  · -- separation up to the exit time
    filter_upwards [hnotN0] with ω hω
    intro ε hε s hs hsτ hτ0 i j hij
    have hf : Continuous fun u : ℝ => ‖X (Real.toNNReal u) ω i - X (Real.toNNReal u) ω j‖ :=
      (((hpN ω hω i).comp continuous_real_toNNReal).sub
        ((hpN ω hω j).comp continuous_real_toNNReal)).norm
    have hstrict : ∀ u : ℝ, 0 ≤ u → ((u : ℝ) : WithTop ℝ) < exitTime Y (sepSet d N ε) 0 ω →
        ε < ‖X (Real.toNNReal u) ω i - X (Real.toNNReal u) ω j‖ := by
      intro u hu hlt
      have := mem_of_lt_exitTime Y (sepSet d N ε) 0 ω u hu hlt
      rw [hY, modX_of_notMem hω] at this
      exact this i j hij
    rcases hsτ.lt_or_eq with hlt | heq
    · exact (hstrict s hs.1 hlt).le
    · have hs0 : 0 < s := by
        rw [← heq] at hτ0
        exact_mod_cast hτ0
      have hlim : Tendsto (fun u : ℝ => ‖X (Real.toNNReal u) ω i - X (Real.toNNReal u) ω j‖)
          (𝓝[<] s) (𝓝 ‖X (Real.toNNReal s) ω i - X (Real.toNNReal s) ω j‖) :=
        hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hs0] with u hu
      exact (hstrict u hu.1.le (by rw [← heq]; exact_mod_cast hu.2)).le
  · -- exhaustion: positive minimal separation on the compact `[0,T]`
    filter_upwards [hnotN0, h.sol.no_collision] with ω hω hnc
    have hfp : ∀ q : Fin N × Fin N, ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Set.Icc (0 : ℝ) T, q.1 ≠ q.2 →
        δ ≤ ‖X (Real.toNNReal u) ω q.1 - X (Real.toNNReal u) ω q.2‖ := by
      intro q
      by_cases hq : q.1 = q.2
      · exact ⟨1, one_pos, fun u _ hh => absurd hq hh⟩
      · have hcont : ContinuousOn
            (fun u : ℝ => ‖X (Real.toNNReal u) ω q.1 - X (Real.toNNReal u) ω q.2‖) (Set.Icc 0 T) :=
          (((hpN ω hω q.1).comp continuous_real_toNNReal).sub
            ((hpN ω hω q.2).comp continuous_real_toNNReal)).norm.continuousOn
        have hpos : ∀ u ∈ Set.Icc (0 : ℝ) T,
            (0 : ℝ) < ‖X (Real.toNNReal u) ω q.1 - X (Real.toNNReal u) ω q.2‖ := by
          intro u hu
          have hcol := hnc (Real.toNNReal u) (by rw [Real.coe_toNNReal _ hu.1]; exact hu.2)
          have : X (Real.toNNReal u) ω q.1 ≠ X (Real.toNNReal u) ω q.2 := fun hh =>
            hcol ⟨q.1, q.2, hq, hh⟩
          exact norm_pos_iff.2 (sub_ne_zero.2 this)
        obtain ⟨a', ha', hle⟩ := isCompact_Icc.exists_forall_le' hcont hpos
        exact ⟨a', ha', fun u hu _ => hle u hu⟩
    choose δ hδ0 hδ using hfp
    obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ q : Fin N × Fin N, ε₀ ≤ δ q := by
      rcases isEmpty_or_nonempty (Fin N × Fin N) with he | hne
      · exact ⟨1, one_pos, fun q => (he.false q).elim⟩
      · obtain ⟨q0, -, hq0⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
        exact ⟨δ q0, hδ0 q0, fun q => hq0 q (Finset.mem_univ q)⟩
    refine ⟨ε₀ / 2, by positivity, fun ε hε hεle => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hne : exitTime Y (sepSet d N ε) 0 ω ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
    have ha' : exitTime Y (sepSet d N ε) 0 ω = (a : WithTop ℝ) := ha.symm
    have h0a : (0 : WithTop ℝ) ≤ (a : WithTop ℝ) := ha' ▸ le_hittingAfter ω
    have h0a' : (0 : ℝ) ≤ a := by exact_mod_cast h0a
    have haT : a < T := by rw [ha'] at hlt; exact_mod_cast hlt
    have hnm := notMem_of_exitTime_eq Y (sepSet d N ε) (isOpen_sepSet ε) 0 ω (hYcont ω) a ha'
    apply hnm
    rw [hY, modX_of_notMem hω]
    intro i j hij
    have h1 := hδ (i, j) a ⟨h0a', haT.le⟩ hij
    have h2 := hε₀le (i, j)
    simp only at h1
    linarith

end HRS.MD.LT337P4

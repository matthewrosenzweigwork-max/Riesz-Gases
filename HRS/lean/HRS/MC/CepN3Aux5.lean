import Mathlib
import HRS.MC.CepN3Aux3
import HRS.MC.CepN3Aux4

/-!
# Packet CEPN3, auxiliary 5: steering from a fixed initial datum

For a fixed permutation `σ` and strictly `σ`-ordered `y₀`, there is a radius `η₀ > 0` such that every
`ℱ₀`-event `E` of positive probability on which `π = σ` and `‖Y₀ - y₀‖ < η₀` contains (up to the steering
event) a positive-probability `ℱ_{T'}`-set on which the solution reaches the target at time `T'`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN3

open HRS HRS.MC.CepN4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cepn3_fixed [IsProbabilityMeasure P] (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hV : HRS.MC.CepC0.cep_IsC11 D.V)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {π : Ω → Equiv.Perm (Fin N)}
    {T' : ℝ} (hT' : 0 < T') {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8)
    {σ : Equiv.Perm (Fin N)} {y₀ : Fin N → Euc 1} (h0 : cep_StrictlyOrdered σ y₀) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ E : Set Ω, MeasurableSet[ℱ 0] E → 0 < P E →
      (∀ ω ∈ E, π ω = σ ∧ ‖Y₀ ω - y₀‖ < η₀) →
      ∃ A : Set Ω, MeasurableSet[ℱ T'] A ∧ 0 < P A ∧
        ∀ ω ∈ A, ((T' : ℝ) : WithTop ℝ) < τ ω ∧ cep_StrictlyOrdered (π ω) (Y T' ω) ∧
          0 < Y T' ω (π ω (cep_i1 hN)) 0 - Y T' ω (π ω (cep_i0 hN)) 0 ∧
          Y T' ω (π ω (cep_i1 hN)) 0 - Y T' ω (π ω (cep_i0 hN)) 0 ≤ ε / 2 ∧
          cep_PairIsolated hN (π ω) (Y T' ω) (1 / (8 * (N : ℝ))) ∧
          (∀ k l : Fin N, k ≠ l → k ≠ π ω (cep_i0 hN) → k ≠ π ω (cep_i1 hN) →
            l ≠ π ω (cep_i0 hN) → l ≠ π ω (cep_i1 hN) → ∀ m : ℤ,
              1 / (8 * (N : ℝ)) ≤ |Y T' ω k 0 - Y T' ω l 0 - m|) := by
  classical
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set ε₁ : ℝ := min (ε / 16) (1 / (16 * (N : ℝ))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by linarith) (by positivity)
  have hε₁a : ε₁ ≤ ε / 16 := min_le_left _ _
  have hε₁b : ε₁ ≤ 1 / (16 * (N : ℝ)) := min_le_right _ _
  set ys : Fin N → Euc 1 := cepn3_ystar σ (ε / 4) with hys_def
  have hys : cep_StrictlyOrdered σ ys :=
    (cepn3_robust hN σ hε hε1 hε₁0 hε₁a hε₁b (y := ys) (fun i => by simpa [hys_def] using hε₁0)).1
  obtain ⟨c, v, hc, hv, hv0, hc0, hcT, hcfree, hceq⟩ := cepn3_det (D := D) hs hV hT' h0 hys
  obtain ⟨r, hr, hN2⟩ := HRS.MC.CepN2.cep_N2_tube_stability_proof hs hV hT' hc hv hv0
    (fun t _ => hcfree t) (fun t _ => hceq t)
  have hKc : IsCompact (c '' Set.Icc 0 T') := isCompact_Icc.image hc
  have hKU : c '' Set.Icc 0 T' ⊆ liftedFree 1 N := by
    rintro _ ⟨t, _, rfl⟩; exact hcfree t
  obtain ⟨r₀, hr₀, hr₀K⟩ := hKc.exists_cthickening_subset_open (isOpen_liftedFree 1 N) hKU
  set ε' : ℝ := min (min r (r₀ / 2)) ε₁ with hε'
  have hε'0 : 0 < ε' := lt_min (lt_min hr (by linarith)) hε₁0
  have hε'r : ε' ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hε'r₀ : ε' ≤ r₀ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε'1 : ε' ≤ ε₁ := min_le_right _ _
  obtain ⟨η₂, hη₂, hN2'⟩ := hN2 ε' hε'0 hε'r
  set σs : ℝ := Real.sqrt (2 * D.invβ) with hσs_def
  have hσs : 0 < σs := Real.sqrt_pos.2 (by linarith)
  set w : ℝ → Fin N → Euc 1 := fun t => σs⁻¹ • v t with hw_def
  have hwc : Continuous w := hv.const_smul σs⁻¹
  have hw0 : w 0 = 0 := by simp [hw_def, hv0]
  have hvw : ∀ t, v t = σs • w t := fun t => by
    simp [hw_def, smul_smul, mul_inv_cancel₀ hσs.ne']
  set δ : ℝ := η₂ / (2 * σs) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδη : σs * δ < η₂ := by
    rw [hδ_def]; field_simp; linarith
  refine ⟨η₂, hη₂, fun E hE hPE hEprop => ?_⟩
  obtain ⟨F, hFm, hFt, hPEF⟩ := cepn3_tube_inter hW' hwc hw0 hT' hδ hE hPE
  have hQ := hsol.sol.eq
  obtain ⟨N', hN'sub, hN'm, hN'0⟩ := exists_measurable_superset_of_null (ae_iff.1 hQ)
  refine ⟨(E ∩ F) \ N', ?_, ?_, ?_⟩
  · exact (((ℱ.mono hT'.le) _ hE).inter hFm).diff (hW'.complete T' N' hN'm hN'0)
  · rw [measure_diff_null hN'0]; exact hPEF
  · intro ω hω
    obtain ⟨⟨hωE, hωF⟩, hωN⟩ := hω
    have hωQ := Set.notMem_subset hN'sub hωN
    simp only [Set.mem_setOf_eq, not_not] at hωQ
    obtain ⟨hπ, hY0⟩ := hEprop ω hωE
    have hY0' : Y 0 ω = Y₀ ω := hsol.sol.init ω
    -- pathwise claim
    have hclaim := cepn3_path_claim (D := D) (T' := T') (c := c) (v := v) (w := w) (σs := σs) (ε' := ε')
      (η := η₂) (δ := δ) hσs hvw hδη hN2' (τ := τ ω) (Yω := fun s => Y s ω)
      (X := fun t => ofCoords W' t ω)
      (fun t ht htτ => hsol.sol.cont ω t ht htτ) (fun t ht htτ => hsol.mem ω t ht htτ)
      (fun t ht htτ => by
        have h := (hωQ t ht htτ).2
        have hn : ∑ k, ofNNRealTime W' t ω k • liftedNoise (N := N) D k =
            σs • ofCoords W' (Real.toNNReal t) ω := by
          have := sum_liftedNoise (N := N) D W' (Real.toNNReal t) ω
          exact this
        rw [hn] at h
        rw [hY0']
        exact h)
      (by rw [hY0', hc0]; exact hY0) (fun t ht => hFt ω hωF t ht)
    -- T' < τ ω
    have hTτ : ((T' : ℝ) : WithTop ℝ) < τ ω := by
      by_contra hcon
      have hle : τ ω ≤ ((T' : ℝ) : WithTop ℝ) := not_lt.1 hcon
      have hlt : τ ω < ⊤ := lt_of_le_of_lt hle (WithTop.coe_lt_top T')
      obtain ⟨t, ht0, htτ, hnot⟩ := hsol.exit ω hlt (Metric.cthickening r₀ (c '' Set.Icc 0 T'))
        hKc.cthickening hr₀K 0 (by simpa using hsol.pos ω)
      have htT : t ≤ T' := by
        have := htτ.le.trans hle
        exact_mod_cast this
      have h1 := hclaim t ht0.le htT htτ t ⟨ht0.le, le_rfl⟩
      apply hnot
      refine Metric.mem_cthickening_of_dist_le _ (c t) r₀ _ ⟨t, ⟨ht0.le, htT⟩, rfl⟩ ?_
      rw [dist_eq_norm]; linarith
    have h1 := hclaim T' hT'.le le_rfl hTτ T' ⟨hT'.le, le_rfl⟩
    rw [hcT] at h1
    have hcoord : ∀ i, |Y T' ω i 0 - ys i 0| < ε₁ := fun i => by
      have a : ‖(Y T' ω - ys) i‖ ≤ ‖Y T' ω - ys‖ := norm_le_pi_norm _ i
      have b : ‖(Y T' ω - ys) i 0‖ ≤ ‖(Y T' ω - ys) i‖ := PiLp.norm_apply_le _ 0
      have : |Y T' ω i 0 - ys i 0| = ‖(Y T' ω - ys) i 0‖ := by
        simp [Real.norm_eq_abs]
      rw [this]
      exact lt_of_le_of_lt (b.trans a) (lt_of_lt_of_le h1 hε'1)
    obtain ⟨hord, ⟨hg0, hg1⟩, hiso, hsep⟩ := cepn3_robust hN σ hε hε1 hε₁0 hε₁a hε₁b hcoord
    rw [hπ]
    exact ⟨hTτ, hord, hg0, hg1, hiso, hsep⟩

end HRS.MC.CepN3

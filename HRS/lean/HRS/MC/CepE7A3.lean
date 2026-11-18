import HRS.MC.CepE7A2
import HRS.MC.CepE3
import HRS.MC.CepE2
import HRS.MC.CepE6E13
import HRS.Stochastic.Bridge

/-!
# Packet CEPE7, file A3: the upstream interfaces and adaptedness to an arbitrary Brownian filtration

* `cepE7_E0 .. cepE7_E6`: the upstream `_proof` theorems at their own types (identical to the spec statements by the ties, so the proof chain imports no spec).
* `cepE7_lip_unique`: pathwise uniqueness for the Lipschitz equation `Z_t = c + ∫_0^t B(Z) + g_t` (Gronwall).
* `cepE7_transfer`: a chamber solution built on one Brownian filtration solves the equation on every other one
  (the filtration `ℱ` is complete, the Lipschitz solution of `ℱ` equals it a.s.).
* `cepE7_tim`, `cepE7_Zl_measurable`: the limit `Zl` is a limit in measure of `Z^n_t`, hence `ℱ_t`-measurable whenever the `Z^n_t` are.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE7

open HRS HRS.MC.Cepa

/-! ### Upstream interfaces -/

theorem cepE7_E0 : type_of% @HRS.MC.CepE0.cep_E0_sort_proof := @HRS.MC.CepE0.cep_E0_sort_proof

theorem cepE7_E1 : type_of% @HRS.MC.CepE1.cep_E1_chamber_drift_proof := @HRS.MC.CepE1.cep_E1_chamber_drift_proof

theorem cepE7_E2 (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ), cep_Yosida a N J ∧
      (∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) ∧
      (∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot a N z) ∧
      (∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot a N z))) := by
  obtain ⟨J, Φn, hY, h1, h2, h3⟩ := HRS.MC.CepE2.cep_E2_moreau_yosida_proof a ha N
  exact ⟨J, Φn, ⟨hY.mem, hY.force, hY.lip, hY.yosida⟩, h1, h2, h3⟩

theorem cepE7_E3 : type_of% @HRS.MC.CepE3.cep_E3_regularised_sde_proof := @HRS.MC.CepE3.cep_E3_regularised_sde_proof

theorem cepE7_E6 : type_of% @HRS.MC.CepE6E.cep_E6_limit_solution_proof := @HRS.MC.CepE6E.cep_E6_limit_solution_proof

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-! ### Pathwise uniqueness of the Lipschitz equation -/

theorem cepE7_lip_unique {B : Ch N → Ch N} {L : ℝ≥0} (hB : LipschitzWith L B) {c : Ch N} {g : ℝ → Ch N}
    {Z Z' : ℝ → Ch N} (hZ : Continuous Z) (hZ' : Continuous Z')
    (h : ∀ t, 0 ≤ t → Z t = c + (∫ s in (0 : ℝ)..t, B (Z s)) + g t)
    (h' : ∀ t, 0 ≤ t → Z' t = c + (∫ s in (0 : ℝ)..t, B (Z' s)) + g t) :
    ∀ t, 0 ≤ t → Z t = Z' t := by
  intro T hT
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun s => Z s - Z' s) (hZ.sub hZ').continuousOn
  have key := eq_zero_of_integral_bound (d := fun s => Z s - Z' s) (T := T) (L := (L : ℝ)) (M := M)
    L.2 hM (by
      intro s hs
      refine ⟨fun r => B (Z r) - B (Z' r), ?_, ?_⟩
      · have e1 := h s hs.1
        have e2 := h' s hs.1
        have i1 : IntervalIntegrable (fun r => B (Z r)) volume 0 s :=
          (hB.continuous.comp hZ).intervalIntegrable _ _
        have i2 : IntervalIntegrable (fun r => B (Z' r)) volume 0 s :=
          (hB.continuous.comp hZ').intervalIntegrable _ _
        rw [intervalIntegral.integral_sub i1 i2]
        rw [e1, e2]
        abel
      · intro r _
        have := hB.dist_le_mul (Z r) (Z' r)
        simpa [dist_eq_norm] using this)
  exact sub_eq_zero.1 (key T ⟨hT, le_rfl⟩)

/-! ### Transfer of a chamber solution to another Brownian filtration -/

theorem cepE7_transfer [IsProbabilityMeasure P] {ℱc ℱ : Filtration ℝ mΩ}
    {Wc W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hWc : IsBrownianFiltration P ℱc Wc)
    (hW' : IsBrownianFiltration P ℱ W') (hWW : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = Wc t ω (i, j))
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {B : Ch N → Ch N} {L : ℝ≥0} (hB : LipschitzWith L B) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱc Wc π σ' B z₀ Z) :
    cep_IsChamberSolution P ℱ W' π σ' B z₀ Z := by
  obtain ⟨Zf, hZfc, hZfm, hZfe⟩ := cepE7_E3 hW' hπ hB σ' hz₀
  obtain ⟨hZc, hZm, hZe⟩ := hZ
  have hnoise : ∀ᵐ ω ∂P, ∀ t : ℝ, cep_noise π W' t ω = cep_noise π Wc t ω := by
    filter_upwards [hWW] with ω h t
    ext k
    exact h _ _ _
  have hZeW : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = z₀ ω + (∫ s in (0 : ℝ)..t, B (Z s ω)) + σ' • cep_noise π W' t ω := by
    filter_upwards [hZe, hnoise] with ω h1 h2 t ht
    rw [h2 t]
    exact h1 t ht
  have hae : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Z t ω = Zf t ω := by
    filter_upwards [hZeW, hZfe] with ω h1 h2
    exact cepE7_lip_unique hB (hZc ω) (hZfc ω) h1 h2
  refine ⟨hZc, fun t ht => ?_, hZeW⟩
  have hmΩ : Measurable (Z t) := (hZm t ht).mono (ℱc.le t) le_rfl
  refine hW'.complete.measurable_of_ae_eq t (hZfm t ht) hmΩ ?_
  filter_upwards [hae] with ω h
  exact (h t ht).symm

/-! ### Limits in measure -/

theorem cepE7_tim {Z : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N}
    (hZc : ∀ n ω, Continuous fun t => Z n t ω) (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (h : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    TendstoInMeasure P (fun n => Z n t) atTop (Zl t) := by
  intro ε hε
  by_cases htop : ε = ⊤
  · subst htop
    simp [edist_ne_top]
  have hε0 : ε.toReal ≠ 0 := by
    intro h0
    rcases (ENNReal.toReal_eq_zero_iff ε).1 h0 with h1 | h1
    · exact hε.ne' h1
    · exact htop h1
  have hεr : 0 < ε.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hε0)
  have hsub : ∀ n, {ω | ε ≤ edist (Z n t ω) (Zl t ω)} ⊆
      {ω | ε.toReal / 2 < ⨆ s : Set.Icc (0 : ℝ) t, ‖Z n s ω - Zl s ω‖} := by
    intro n ω hω
    simp only [mem_setOf_eq] at hω ⊢
    have h1 : ε.toReal ≤ dist (Z n t ω) (Zl t ω) := by
      rw [edist_dist] at hω
      have := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 (by rwa [ENNReal.ofReal_toReal htop])
      exact this
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
      (f := fun s => ‖Z n s ω - Zl s ω‖) (((hZc n ω).sub (hZlc ω)).norm).continuousOn
    have hbdd : BddAbove (range fun s : Set.Icc (0 : ℝ) t => ‖Z n s ω - Zl s ω‖) :=
      ⟨M, by rintro _ ⟨s, rfl⟩; simpa using hM s s.2⟩
    have h2 : ‖Z n t ω - Zl t ω‖ ≤ ⨆ s : Set.Icc (0 : ℝ) t, ‖Z n s ω - Zl s ω‖ :=
      le_ciSup hbdd (⟨t, ⟨ht, le_rfl⟩⟩ : Set.Icc (0 : ℝ) t)
    rw [dist_eq_norm] at h1
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h t (ε.toReal / 2) (by positivity))
    (fun _ => zero_le) (fun n => measure_mono (hsub n))

theorem cepE7_Zl_measurable [IsProbabilityMeasure P] {ℱc ℱ : Filtration ℝ mΩ}
    (hℱ : IsCompleteFiltration P ℱ) {Z : ℕ → ℝ → Ω → Ch N}
    (hZc : ∀ n ω, Continuous fun t => Z n t ω) {Zl Zl' : ℝ → Ω → Ch N}
    (hZlc : ∀ ω, Continuous fun t => Zl t ω) (hZlc' : ∀ ω, Continuous fun t => Zl' t ω)
    (hZlm : ∀ t, 0 ≤ t → Measurable[ℱc t] (Zl t)) (hZlm' : ∀ t, 0 ≤ t → Measurable[ℱ t] (Zl' t))
    (h : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) atTop (𝓝 0))
    (h' : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl' t ω‖}) atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t) := by
  intro t ht
  have hu := tendstoInMeasure_ae_unique (cepE7_tim hZc hZlc h ht) (cepE7_tim hZc hZlc' h' ht)
  have hmΩ : Measurable (Zl t) := (hZlm t ht).mono (ℱc.le t) le_rfl
  exact hℱ.measurable_of_ae_eq t (hZlm' t ht) hmΩ hu.symm

end HRS.MC.CepE7

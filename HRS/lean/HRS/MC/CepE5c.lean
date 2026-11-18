import HRS.MC.CepE5cAux2

/-!
# Packet CEPE5C: the Yosida approximations are Cauchy in probability, uniformly on `[0,T]`
(`cep_E5c_cauchy_proof`)

Pathwise (E5a) `‖Z^m_t - Z^n_t‖² ≤ e^{2LT}(1/m+1/n)(h_m + h_n)`, `h_k = ∫_0^T |G_k(Z^k)|²`, and `E h_k = k X_k` with
`X_k ≤ C k^{-1/3}` (E5b with rate, `CepE5bAux18`).  For `m ≤ n ≤ 8m` this gives `E ‖Z^m - Z^n‖² ≲ m^{-1/3}`
(the pair estimate alone degenerates for `n ≫ m`: the factor `(√(n/m) + √(m/n))`), so a general pair is chained along
`m, 8m, 64m, …, n` with Cauchy–Schwarz weights `(3/4)^j` (`CepE5cAux1`); Markov finishes.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5c

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE5b

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_E5c_cauchy_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ ≤ m → n₀ ≤ n →
      P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} < ENNReal.ofReal ε := by
  intro ε hε
  rcases lt_or_ge T 0 with hT | hT
  · refine ⟨0, fun m n _ _ => ?_⟩
    have hemp : IsEmpty (Set.Icc (0 : ℝ) T) := ⟨fun x => by linarith [x.2.1, x.2.2]⟩
    have hset : {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} = ∅ := by
      ext ω
      simp only [Real.iSup_of_isEmpty, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    rw [hset, measure_empty]
    exact ENNReal.ofReal_pos.2 hε
  obtain ⟨R, hR⟩ := hz₀b
  obtain ⟨C, hC0, hCbd⟩ := e5b_rate hW' hπ ha hJ hF σ' hz₀ hz₀A hR hZ T hT
  set Ec : ℝ := Real.exp (2 * L * T) with hEc
  have hEc0 : 0 ≤ Ec := Real.exp_nonneg _
  have hladder := e5c_ladder (P := P) (τ := Set.Icc (0 : ℝ) T)
    (d := fun m n ω (t : Set.Icc (0 : ℝ) T) => ‖Z m t ω - Z n t ω‖) (h := e5c_h J Z T) (Ec := Ec) (C := C)
    hEc0 hC0
    (fun n hn => e5c_h_integrable hW' hπ hJ hF σ' hR hZ hT (by omega))
    (fun n ω => e5c_h_nonneg hT n ω)
    (fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hn0 : (0 : ℝ) < n := by linarith
      have h1 := hCbd n hn
      rw [e5c_X_eq] at h1
      have h2 : (∫ ω, e5c_h J Z T n ω ∂P) ≤ n * (C * (1 / ((n : ℝ) ^ (1 / 3 : ℝ)))) := by
        have := mul_le_mul_of_nonneg_left h1 hn0.le
        rwa [← mul_assoc, mul_one_div_cancel hn0.ne', one_mul] at this
      calc (∫ ω, e5c_h J Z T n ω ∂P) ≤ n * (C * (1 / ((n : ℝ) ^ (1 / 3 : ℝ)))) := h2
        _ = C * ((n : ℝ) / e5c_r n) := by unfold e5c_r; ring)
    (fun m n ω t => norm_nonneg _)
    (fun m ω t => by simp)
    (fun m k n ω t => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    (by
      filter_upwards [e5c_pair_ae hJ hF σ' hZ hT] with ω hω m n t hm hmn _
      exact hω m n t (by omega) (by omega) t.2.1 t.2.2)
  set K : ℝ := 120 * Ec * C / ε ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 8 (⌈K ^ 3⌉₊ + 1), ?_⟩
  have key : ∀ m n : ℕ, max 8 (⌈K ^ 3⌉₊ + 1) ≤ m → m ≤ n →
      P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} < ENNReal.ofReal ε := by
    intro m n hm hmn
    have hm8 : 8 ≤ m := le_trans (le_max_left _ _) hm
    have hmK : ⌈K ^ 3⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
    obtain ⟨V, hVi, hV0, hVd, hVint⟩ := hladder m n hm8 hmn
    have hm0 : 0 < m := by omega
    have hr := e5c_r_pos hm0
    have hKr : K < e5c_r m := by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : e5c_r m ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (e5c_r_nonneg m) hcon 3
      rw [e5c_r_cube] at h1
      have h2 : K ^ 3 ≤ (⌈K ^ 3⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈K ^ 3⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hmK
      push_cast at h3
      linarith
    have hε3 : 0 < ε ^ 3 := by positivity
    have hEV : ∫ ω, V ω ∂P < ε ^ 3 := by
      refine lt_of_le_of_lt hVint ?_
      have e : 120 * Ec * C = K * ε ^ 3 := by rw [hK]; field_simp
      rw [e, div_lt_iff₀ hr]
      nlinarith
    -- the event
    have hsub : {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} ≤ᵐ[P] {ω | ε ^ 2 ≤ V ω} := by
      filter_upwards [hVd] with ω hω hS
      by_contra hcon
      rw [not_le] at hcon
      have hle : (⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖) ≤ ε := by
        have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
        refine ciSup_le fun t => ?_
        have h1 := hω t
        by_contra h2
        rw [not_le] at h2
        have := pow_le_pow_left₀ hε.le h2.le 2
        linarith
      exact absurd (lt_of_lt_of_le hS hle) (lt_irrefl _)
    refine lt_of_le_of_lt (measure_mono_ae hsub) ?_
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := V) (Eventually.of_forall hV0) hVi (ε ^ 2)
    have hreal : P.real {ω | ε ^ 2 ≤ V ω} < ε := by
      have : ε ^ 2 * P.real {ω | ε ^ 2 ≤ V ω} < ε ^ 2 * ε := by
        calc ε ^ 2 * P.real {ω | ε ^ 2 ≤ V ω} ≤ ∫ ω, V ω ∂P := hmk
          _ < ε ^ 3 := hEV
          _ = ε ^ 2 * ε := by ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    rw [← ofReal_measureReal]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hreal
  intro m n hm hn
  rcases le_total m n with hmn | hnm
  · exact key m n hm hmn
  · have e : {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} =
        {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Z m t ω‖} := by
      ext ω
      simp only [Set.mem_ofPred_eq, norm_sub_rev (Z m _ ω)]
    rw [e]
    exact key n m hn hnm

end HRS.MC.CepE5c

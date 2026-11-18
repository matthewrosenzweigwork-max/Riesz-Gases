import HRS.MC.CepE5bAux15

/-!
# Packet CEPE5B, auxiliary 16: the explicit bound for the defect with the `n^{-1/3}` cutoff
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_alg {nn q Eg cL Kc s a Nr T Bc : ℝ} (hq : 0 < q) (hnn : nn = q ^ 3) (ha : 0 < a) :
    (1 / nn) * (2 * (Eg + cL) + Kc + s * (((nn) * (8 * Nr ^ 3 * (1 / q) / (a * Real.pi))) * Bc +
        (nn * (16 * Nr ^ 5 * (1 / q)) + 2 * a * Real.pi ^ 2 * Nr / (1 / q) ^ 2) * T)) =
      2 * ((1 / nn) * Eg) + (2 * cL + Kc) * (1 / nn) +
        (s * ((8 * Nr ^ 3 / (a * Real.pi)) * Bc + 16 * Nr ^ 5 * T + 2 * a * Real.pi ^ 2 * Nr * T)) * (1 / q) := by
  have hpi := Real.pi_pos
  subst hnn
  field_simp
  ring


/-- The explicit bound: `X_n ≤ 2 (1/n) E Φ_n(z₀) + K₁/n + K₂ n^{-1/3}` for `n ≥ 8`. -/
theorem e5b_bound [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) {R : ℝ} (hR : ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ n : ℕ, 8 ≤ n →
      ∫ ω, (∫ s in (0 : ℝ)..T, (1 / (n : ℝ)) * ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2) ∂P ≤
        2 * ((1 / (n : ℝ)) * ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P) + K₁ * (1 / (n : ℝ)) +
          K₂ * (1 / ((n : ℝ) ^ (1 / 3 : ℝ))) := by
  set cL : ℝ := (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 with hcL
  set Mc : ℝ := e5b_Mc N R ‖e4_rho N‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L) with hMc
  set Bc : ℝ := e5b_Bc N R ‖e4_rho N‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L) with hBc
  set Kc : ℝ := (2 * ‖F 0‖ ^ 2 + 4 * (L : ℝ) ^ 2 * ‖e4_rho N‖ ^ 2) * T + 8 * (L : ℝ) ^ 2 * (Mc * T) with hKc
  set CC : ℝ := σ' ^ 2 * ((8 * (N : ℝ) ^ 3 / (a * Real.pi)) * Bc + 16 * (N : ℝ) ^ 5 * T +
    2 * a * Real.pi ^ 2 * N * T) with hCC
  have hcL0 : 0 ≤ cL := by
    have : 0 ≤ HRS.MC.CepE2.cepe2_npairs N := by unfold HRS.MC.CepE2.cepe2_npairs; positivity
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hK0 : 0 ≤ Kc := by
    have hM0 : 0 ≤ Mc := by
      have h1 : 0 ≤ e5b_cF2 L := by unfold e5b_cF2; positivity
      have h2 : 0 ≤ e5b_K1 a N := by unfold e5b_K1; have := Real.pi_pos; positivity
      have h3 : 0 ≤ e5b_cF1 F := by unfold e5b_cF1; positivity
      rw [hMc]; unfold e5b_Mc; positivity
    rw [hKc]; positivity
  have hC0 : 0 ≤ CC := by
    have hB0 : 0 ≤ Bc := by
      have h1 : 0 ≤ e5b_cF2 L := by unfold e5b_cF2; positivity
      have h2 : 0 ≤ e5b_K1 a N := by unfold e5b_K1; have := Real.pi_pos; positivity
      have h3 : 0 ≤ e5b_cF1 F := by unfold e5b_cF1; positivity
      have hM0 : 0 ≤ e5b_Mc N R ‖e4_rho N‖ σ' T (e5b_K1 a N) (e5b_cF1 F) (e5b_cF2 L) := by
        unfold e5b_Mc; positivity
      rw [hBc]; unfold e5b_Bc; positivity
    have := Real.pi_pos
    rw [hCC]; positivity
  refine ⟨2 * cL + Kc, CC, by positivity, hC0, fun n hn8 => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set q : ℝ := (n : ℝ) ^ (1 / 3 : ℝ) with hqdef
  have hqpos : 0 < q := Real.rpow_pos_of_pos hnpos _
  have hq3 : (n : ℝ) = q ^ 3 := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hq2 : 2 ≤ q := by
    by_contra h
    rw [not_le] at h
    have h8 : (8 : ℝ) ≤ n := by exact_mod_cast hn8
    have : q ^ 3 < 2 ^ 3 := pow_lt_pow_left₀ h hqpos.le (by norm_num)
    linarith
  have hr : 0 < 1 / q := by positivity
  have hr2 : 1 / q ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hqpos (by norm_num)]
    linarith
  have h := e5b_perN hW' hπ ha hJ hF σ' hz₀ hR hZ T hT hn1 hr hr2
  refine h.trans (le_of_eq ?_)
  have := e5b_alg (nn := (n : ℝ)) (Eg := ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P) (cL := cL) (Kc := Kc) (s := σ' ^ 2)
    (a := a) (Nr := N) (T := T) (Bc := Bc) hqpos hq3 ha
  rw [this]

end HRS.MC.CepE5b

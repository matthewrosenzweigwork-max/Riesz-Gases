import HRS.MC.CepE5bAux16
import HRS.MC.CepE5bAux17

/-!
# Packet CEPE5B, auxiliary 18: the rate `n^{-1/3}` for the defect
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_rate [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    {R : ℝ} (hR : ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 8 ≤ n →
      ∫ ω, (∫ s in (0 : ℝ)..T, (1 / (n : ℝ)) * ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2) ∂P ≤
        C * (1 / ((n : ℝ) ^ (1 / 3 : ℝ))) := by
  obtain ⟨K₁, K₂, hK1, hK2, hbd⟩ := e5b_bound hW' hπ ha hJ hF σ' hz₀ hR hZ T hT
  have hz0m : Measurable z₀ := hz₀.mono (ℱ.le 0) le_rfl
  set A : ℝ := (a / N) * HRS.MC.CepE2.cepe2_npairs N with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ HRS.MC.CepE2.cepe2_npairs N := HRS.MC.CepE2.cepe2_npairs_nonneg
    positivity
  set c : ℝ := |Real.log (N / 4)| with hc
  set B' : ℝ := (1 / 2) * (R + ‖e4_rho N‖) ^ 2 with hB'
  have hc0 : 0 ≤ c := abs_nonneg _
  have hB0 : 0 ≤ B' := by positivity
  refine ⟨2 * A * c + 3 * A + 2 * B' + K₁ + K₂, by positivity, fun n hn8 => ?_⟩
  refine (hbd n hn8).trans ?_
  have hn8' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  set q : ℝ := (n : ℝ) ^ (1 / 3 : ℝ) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos hn0 _
  have hq1 : 1 ≤ q := Real.one_le_rpow hn1 (by norm_num)
  have hq3 : q ^ 3 = n := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hlog : Real.log n ≤ 3 * q := by
    have h1 : Real.log n = 3 * Real.log q := by
      rw [hq, Real.log_rpow hn0]; ring
    have := Real.log_le_sub_one_of_pos hqpos
    linarith
  have e1 : 1 / (n : ℝ) ≤ 1 / q := by
    apply one_div_le_one_div_of_le hqpos
    rw [← hq3]; nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.2 hq1)]
  have e3 : q / (n : ℝ) ≤ 1 / q := by
    rw [← hq3, div_le_div_iff₀ (by positivity) hqpos]
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.2 hq1)]
  have e2 : (1 / (n : ℝ)) * Real.log n ≤ 3 * (1 / q) := by
    calc (1 / (n : ℝ)) * Real.log n ≤ (1 / (n : ℝ)) * (3 * q) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 3 * (q / n) := by ring
      _ ≤ 3 * (1 / q) := by linarith
  -- the integral of `Φ_n(z₀)`
  have hint : ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P ≤ A * (c + (1 / 2) * Real.log n) + B' := by
    have hmeas : AEStronglyMeasurable (fun ω => e5b_Pn a N J n (z₀ ω)) P :=
      (((e5b_contDiff_Pn ha hJ hn0).continuous.measurable.comp hz0m)).aestronglyMeasurable
    have hbnd : Integrable (fun ω => e5b_Pn a N J n (z₀ ω)) P := by
      refine Integrable.of_bound hmeas (((a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 +
        |cep_chamberPot a N (e4_rho N)| + n * ‖e4_rho N‖ ^ 2) + n * R ^ 2) ?_
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      refine (e5b_Pn_abs_le ha hJ hn0 (z₀ ω)).trans ?_
      have : ‖z₀ ω‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hR ω) 2
      nlinarith
    calc ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P ≤ ∫ _ω, (A * (c + (1 / 2) * Real.log n) + B') ∂P := by
          refine integral_mono hbnd (integrable_const _) fun ω => ?_
          exact e5b_Pn_log_le ha hJ hn1 (hz₀A ω) (hR ω)
      _ = _ := by simp
  have hfin : 2 * ((1 / (n : ℝ)) * ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P) ≤
      (2 * A * c + 3 * A + 2 * B') * (1 / q) := by
    have h1 : (1 / (n : ℝ)) * ∫ ω, e5b_Pn a N J n (z₀ ω) ∂P ≤
        (1 / (n : ℝ)) * (A * (c + (1 / 2) * Real.log n) + B') :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    have h2 : (1 / (n : ℝ)) * (A * (c + (1 / 2) * Real.log n) + B') =
        A * c * (1 / n) + (A / 2) * ((1 / (n : ℝ)) * Real.log n) + B' * (1 / n) := by ring
    have h3 : A * c * (1 / (n : ℝ)) ≤ A * c * (1 / q) := mul_le_mul_of_nonneg_left e1 (by positivity)
    have h4 : B' * (1 / (n : ℝ)) ≤ B' * (1 / q) := mul_le_mul_of_nonneg_left e1 hB0
    have h5 : (A / 2) * ((1 / (n : ℝ)) * Real.log n) ≤ (A / 2) * (3 * (1 / q)) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have h6 : K₁ * (1 / (n : ℝ)) ≤ K₁ * (1 / q) := mul_le_mul_of_nonneg_left e1 hK1
  have : K₂ * (1 / ((n : ℝ) ^ (1 / 3 : ℝ))) = K₂ * (1 / q) := by rw [hq]
  nlinarith

end HRS.MC.CepE5b

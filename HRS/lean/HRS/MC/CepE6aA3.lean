import HRS.MC.CepE4
import HRS.MC.CepE6aA2

/-!
# Packet CEPE6A, file 3: the `L¹` bound of E4 in lintegral form, and joint measurability

`e6a_E4_lint`: `∫⁻_Ω ∫⁻_{[0,T]} ‖G_n(Z^n_s)‖₁ ≤ C` uniformly in `n ≥ 1` (E4 gives a Bochner integral bound, which is
void for a non-integrable integrand; here the integrability is re-derived from the E4 setup).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Joint measurability of a continuous adapted path (clamped to nonnegative times). -/
theorem e6a_joint {ℱ : Filtration ℝ mΩ} {Y : ℝ → Ω → Ch N} (hc : ∀ ω, Continuous fun t => Y t ω)
    (hm : ∀ t, 0 ≤ t → Measurable[ℱ t] (Y t)) :
    Measurable fun p : ℝ × Ω => Y (max p.1 0) p.2 := by
  have h1 : ∀ ω, Continuous fun t : ℝ => Y (max t 0) ω := fun ω =>
    (hc ω).comp (continuous_id.max continuous_const)
  have h2 : ∀ t : ℝ, Measurable fun ω => Y (max t 0) ω := fun t =>
    (hm (max t 0) (le_max_right _ _)).mono (ℱ.le _) le_rfl
  exact measurable_uncurry_of_continuous_of_measurable (u := fun t ω => Y (max t 0) ω) h1 h2

/-- The lintegral form of E4. -/
theorem e6a_E4_lint [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|)) ∂P
        ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := cep_E4_L1_bound_proof hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ T
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨R, hR⟩ := hz₀b
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set G : Ch N → Ch N := fun z => (n : ℝ) • (z - J n z) with hG
  have hGlip := hJ.lip n hnpos
  have hGc : Continuous G := hGlip.continuous
  have hFc : Continuous F := hF.continuous
  have hGb : ∀ z, ‖G z‖ ≤ ‖G 0‖ + ((Real.toNNReal n : ℝ≥0) : ℝ) * ‖z‖ := fun z => e4_lip_growth hGlip z
  have hFb : ∀ z, ‖F z‖ ≤ ‖F 0‖ + (L : ℝ) * ‖z‖ := fun z => e4_lip_growth hF z
  have hBc : Continuous fun z => -G z + F z := hGc.neg.add hFc
  have hBb : ∀ z, ‖-G z + F z‖ ≤ (‖G 0‖ + ‖F 0‖) + (((Real.toNNReal n : ℝ≥0) : ℝ) + L) * ‖z‖ := fun z => by
    have h1 := norm_add_le (-G z) (F z)
    rw [norm_neg] at h1
    have h2 := hGb z
    have h3 := hFb z
    nlinarith
  obtain ⟨hZc, hZF, heq⟩ := hZ n hn
  obtain ⟨A, hS⟩ := e4_setup_of_solution hW' hπ (σ' := σ') hR hBc (by positivity) (by positivity) hBb
    (Z := Z n) hZc hZF heq hT
  have hS' : E4Setup P ℱ N T σ' (cep_noise π W') (e4_clamp (Z n)) A := hS
  have hgc : Continuous fun z : Ch N => ∑ k, |(G z) k| :=
    continuous_finset_sum _ fun k _ => ((EuclideanSpace.proj k).continuous.comp hGc).abs
  have hint0 := e4_int_inner hS' hT le_rfl hgc (c0 := (N : ℝ) * ‖G 0‖ + N * ((Real.toNNReal n : ℝ≥0) : ℝ))
    (c1 := (N : ℝ) * ((Real.toNNReal n : ℝ≥0) : ℝ)) (by positivity) (by positivity) (fun z => by
      have := e4_l1_bound (G := G) (β := ‖G 0‖) (L := ((Real.toNNReal n : ℝ≥0) : ℝ)) (norm_nonneg _)
        (NNReal.coe_nonneg _) hGb z
      exact this)
  have hint : Integrable (fun ω => ∫ s in (0 : ℝ)..T, ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|) P := by
    refine hint0.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT] at hs
    simp [e4_clamp, max_eq_left hs.1, hG]
  -- pass to lintegrals
  have hpt : ∀ ω, ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..T, ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|) := by
    intro ω
    have hcont : Continuous fun s => ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k| := by
      refine continuous_finset_sum _ fun k _ => ?_
      exact ((EuclideanSpace.proj k).continuous.comp (hGc.comp (hZc ω))).abs
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
        (Filter.Eventually.of_forall fun s => Finset.sum_nonneg fun k _ => abs_nonneg _)]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => intervalIntegral.integral_nonneg hT fun s _ =>
      Finset.sum_nonneg fun k _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hC n hn)

end HRS.MC.CepE6A

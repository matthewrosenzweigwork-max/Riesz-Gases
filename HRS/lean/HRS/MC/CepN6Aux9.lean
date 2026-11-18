import HRS.MC.CepN6Aux8
import HRS.MC.CepN6Aux2

/-!
# Packet CEPN6 (aux 9): the final measure-theoretic contradiction and the union bound on the noise
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℕ}

/-- If the minimum of a positive continuous process over a compact interval has probability `≥ c0` of being
below every positive level, we get a contradiction. -/
theorem n6_core_final [IsProbabilityMeasure P] {A₁ : Set Ω} (hA₁ : MeasurableSet A₁)
    {G : ℝ → Ω → ℝ} {t₁ dur ε c0 : ℝ} (hdur : 0 ≤ dur)
    (hGc : ∀ ω, Continuous fun u => G u ω) (hGm : ∀ u ∈ Set.Icc t₁ (t₁ + dur), Measurable (G u))
    (hGpos : ∀ ω ∈ A₁, ∀ u ∈ Set.Icc t₁ (t₁ + dur), 0 < G u ω)
    (hε : 0 < ε) (hc0 : 0 < c0)
    (hlow : ∀ δ : ℝ, 0 < δ → δ < ε / 2 →
      c0 ≤ (P (A₁ ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), G u ω ≤ δ})).toReal) : False := by
  set e : ℕ → ℝ := fun m => ε / (4 * ((m : ℝ) + 1)) with he
  have he0 : ∀ m, 0 < e m := fun m => by positivity
  set S : ℕ → Set Ω := fun m => A₁ ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), G u ω < e m} with hS
  have hSm : ∀ m, MeasurableSet (S m) := fun m =>
    hA₁.inter (n6_meas_exists_lt hGc hGm (e m))
  have hanti : Antitone S := by
    intro m m' hmm' ω ⟨hωA, u, hu, hlt⟩
    refine ⟨hωA, u, hu, lt_of_lt_of_le hlt ?_⟩
    simp only [he]
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    linarith
  have hlow' : ∀ m, c0 ≤ (P (S m)).toReal := by
    intro m
    refine le_trans (hlow (e m / 2) (by linarith [he0 m]) ?_) ?_
    · have : e m ≤ ε / 4 := by
        simp only [he]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      linarith
    · refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      rintro ω ⟨hωA, u, hu, hle⟩
      exact ⟨hωA, u, hu, by linarith [he0 m]⟩
  have hempty : ⋂ m, S m = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
    have hωA : ω ∈ A₁ := (Set.mem_iInter.1 hω 0).1
    obtain ⟨u0, hu0, hmin⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.2 (by linarith : t₁ ≤ t₁ + dur)) (hGc ω).continuousOn
    have hg0 : 0 < G u0 ω := hGpos ω hωA u0 hu0
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < 4 * G u0 ω / ε by positivity)
    obtain ⟨_, u, hu, hlt⟩ := Set.mem_iInter.1 hω m
    have h1 : e m < G u0 ω := by
      simp only [he]
      have : ε / (4 * ((m : ℝ) + 1)) = ε / 4 * (1 / ((m : ℝ) + 1)) := by field_simp
      rw [this]
      calc ε / 4 * (1 / ((m : ℝ) + 1)) < ε / 4 * (4 * G u0 ω / ε) :=
            mul_lt_mul_of_pos_left hm (by positivity)
        _ = G u0 ω := by field_simp
    have h2 := hmin hu
    simp only [Set.mem_setOf_eq] at h2
    linarith
  have ht := tendsto_measure_iInter_atTop (μ := P) (fun m => (hSm m).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at ht
  have ht2 : Tendsto (fun m => (P (S m)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp ht
    exact this
  have := ge_of_tendsto' ht2 hlow'
  linarith

/-- Union bound for the Kolmogorov inequality over the coordinates. -/
theorem n6_bad_bound [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W') {t₁ dur η : ℝ}
    (ht₁ : 0 ≤ t₁) (hdur : 0 ≤ dur) (hη : 0 < η) {A : Set Ω} (hA : MeasurableSet[ℱ t₁] A) :
    P.real (A ∩ {ω | ∃ k : Fin N, ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|}) ≤
      N * dur / η ^ 2 * P.real A := by
  have hk : ∀ k : Fin N,
      P.real (A ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|}) ≤
        dur / η ^ 2 * P.real A := by
    intro k
    have h := n6_kolmogorov hW' (k, 0) ht₁ hdur hη hA
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (mul_nonneg hdur measureReal_nonneg)] at h2
    show (P _).toReal ≤ _
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hsub : A ∩ {ω | ∃ k : Fin N, ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|} =
      ⋃ k : Fin N, A ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hω, k, hk⟩
      exact ⟨k, hω, hk⟩
    · rintro ⟨k, hω, hk⟩
      exact ⟨hω, k, hk⟩
  rw [hsub]
  calc P.real (⋃ k : Fin N, A ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|})
      ≤ ∑ k : Fin N, P.real (A ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), η < |n6_D W' (k, 0) t₁ u ω|}) :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ k : Fin N, dur / η ^ 2 * P.real A := Finset.sum_le_sum fun k _ => hk k
    _ = N * dur / η ^ 2 * P.real A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end HRS.MC.CepN6

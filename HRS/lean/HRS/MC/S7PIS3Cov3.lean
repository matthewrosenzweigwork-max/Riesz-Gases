import HRS.MC.S7PIS3Cov2

/-!
# Packet piS3, part 2c: `s7_PIS_cov_struct`, clauses (c) additivity and (d) continuity of `obsCov`,
and the assembly of the repaired statement (see the note in `S7PIS3Cov2.lean`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIS3_h_intOn (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i j : Fin q) :
    IntegrableOn (S7PIS3_h R t φ i j) (Set.Icc 0 T) := by
  have hg : ContinuousOn (S7PIS3_g R t φ i j) (Set.Icc 0 (min (t i) (t j))) :=
    S7PIS3_g_cont R (ht i).1 (ht j).1 (hφ i) (hφ j)
  have hg' : IntegrableOn (S7PIS3_g R t φ i j) (Set.Icc 0 (min (t i) (t j))) := hg.integrableOn_Icc
  have : Integrable (S7PIS3_h R t φ i j) := (integrable_indicator_iff measurableSet_Icc).2 hg'
  exact this.integrableOn

theorem S7PIS3_obsRate_eq (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (i j : Fin q)
    {v : ℝ} (hv : 0 ≤ v) :
    obsRate R.D R.ρ t φ v i j = 2 * R.D.invβ * S7PIS3_h R t φ i j v := by
  unfold S7PIS3_h
  by_cases hm : v ≤ min (t i) (t j)
  · rw [Set.indicator_of_mem (show v ∈ Set.Icc 0 (min (t i) (t j)) from ⟨hv, hm⟩)]
    have hi : v ≤ t i := hm.trans (min_le_left _ _)
    have hj : v ≤ t j := hm.trans (min_le_right _ _)
    unfold obsRate obsTest
    simp only [Matrix.of_apply, if_pos hi, if_pos hj]
    rfl
  · rw [Set.indicator_of_notMem (show v ∉ Set.Icc 0 (min (t i) (t j)) from fun h => hm h.2)]
    rcases min_lt_iff.1 (not_le.1 hm) with h | h
    · have : ¬ v ≤ t i := not_le.2 h
      unfold obsRate obsTest
      simp only [Matrix.of_apply, if_neg this, S7PIS3_grad_zero, inner_zero_left, zero_mul,
        integral_zero, mul_zero]
    · have : ¬ v ≤ t j := not_le.2 h
      unfold obsRate obsTest
      simp only [Matrix.of_apply, if_neg this, S7PIS3_grad_zero, inner_zero_right, zero_mul,
        integral_zero, mul_zero]

theorem S7PIS3_obsCov_eq (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (i j : Fin q) {u : ℝ} (hu : 0 ≤ u) :
    obsCov R.D R.ρ t φ u i j = 2 * R.D.invβ * ∫ v in Set.Icc u T, S7PIS3_h R t φ i j v := by
  unfold obsCov
  simp only [Matrix.of_apply]
  congr 1
  unfold S7PIS3_h
  rw [setIntegral_indicator measurableSet_Icc]
  have hmT : min (t i) (t j) ≤ T := (min_le_left _ _).trans (ht i).2
  have : Set.Icc u T ∩ Set.Icc 0 (min (t i) (t j)) = Set.Icc u (min (t i) (t j)) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, _, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hmT⟩, hu.trans h1, h2⟩
  rw [this]
  rfl

theorem S7PIS3_cov_d (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ T → ∀ i j,
      obsCov R.D R.ρ t φ u i j = obsCov R.D R.ρ t φ u' i j +
        ∫ v in Set.Ioc u u', obsRate R.D R.ρ t φ v i j := by
  intro u u' hu huu' hu'T i j
  have hu'0 : 0 ≤ u' := hu.trans huu'
  rw [S7PIS3_obsCov_eq R t φ ht i j hu, S7PIS3_obsCov_eq R t φ ht i j hu'0]
  have hI := S7PIS3_h_intOn R t φ ht hφ i j
  have hsplit : ∫ v in Set.Icc u T, S7PIS3_h R t φ i j v =
      (∫ v in Set.Ioc u u', S7PIS3_h R t φ i j v) + ∫ v in Set.Icc u' T, S7PIS3_h R t φ i j v := by
    have hdisj : Disjoint (Set.Ico u u') (Set.Icc u' T) :=
      Set.disjoint_left.2 fun v hv hv' => absurd hv.2 (not_lt.2 hv'.1)
    have hfs : IntegrableOn (S7PIS3_h R t φ i j) (Set.Ico u u') :=
      hI.mono_set fun v hv => ⟨hu.trans hv.1, hv.2.le.trans hu'T⟩
    have hft : IntegrableOn (S7PIS3_h R t φ i j) (Set.Icc u' T) :=
      hI.mono_set fun v hv => ⟨hu'0.trans hv.1, hv.2⟩
    rw [← Set.Ico_union_Icc_eq_Icc huu' hu'T, setIntegral_union hdisj measurableSet_Icc hfs hft,
      integral_Ico_eq_integral_Ioc]
  have hrate : ∫ v in Set.Ioc u u', obsRate R.D R.ρ t φ v i j =
      2 * R.D.invβ * ∫ v in Set.Ioc u u', S7PIS3_h R t φ i j v := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun v hv => S7PIS3_obsRate_eq R t φ i j (hu.trans hv.1.le)
  rw [hrate, hsplit]
  ring

theorem S7PIS3_cov_e (R : Regime d) {T : ℝ} (hT : 0 < T) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∀ i j, ContinuousOn (fun u => obsCov R.D R.ρ t φ u i j) (Set.Icc 0 T) := by
  intro i j
  have hI := S7PIS3_h_intOn R t φ ht hφ i j
  have hprim : ContinuousOn (fun u => ∫ v in u..T, S7PIS3_h R t φ i j v) (Set.Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval_left (a := 0) (b := T)
      (f := S7PIS3_h R t φ i j) (μ := volume) (by rwa [Set.uIcc_of_le hT.le])
    rwa [Set.uIcc_of_le hT.le] at this
  refine ((continuousOn_const (c := 2 * R.D.invβ)).mul hprim).congr fun u hu => ?_
  rw [S7PIS3_obsCov_eq R t φ ht i j hu.1, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hu.2]
  rfl

/-- **`s7_PIS_cov_struct`, repaired statement** (clause (b1) restricted to `u` with `c < t_i → u ≤ t_i`). -/
theorem s7_PIS_cov_struct_proof' (R : Regime d) (T : ℝ) (hT : 0 < T) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    (∀ u ∈ Set.Icc (0 : ℝ) T, (obsRate R.D R.ρ t φ u).PosSemidef) ∧
    (∀ c, ∀ u ∈ Set.Icc (0 : ℝ) T, (∀ i, c < t i → u ≤ t i) →
      (obsRateR R.D R.ρ t φ c u).PosSemidef) ∧
    (∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → (∀ i, ¬ (c < t i ∧ t i < c')) →
      (∀ i j, ContinuousOn (fun u => obsRateR R.D R.ρ t φ c u i j) (Set.Icc c c')) ∧
      ∀ u ∈ Set.Ioc c c', obsRateR R.D R.ρ t φ c u = obsRate R.D R.ρ t φ u) ∧
    (∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ T → ∀ i j,
      obsCov R.D R.ρ t φ u i j = obsCov R.D R.ρ t φ u' i j + ∫ v in Set.Ioc u u', obsRate R.D R.ρ t φ v i j) ∧
    (∀ i j, ContinuousOn (fun u => obsCov R.D R.ρ t φ u i j) (Set.Icc 0 T)) :=
  ⟨S7PIS3_cov_a R t φ, S7PIS3_cov_b R t φ, S7PIS3_cov_c R t φ ht hφ,
    S7PIS3_cov_d R t φ ht hφ, S7PIS3_cov_e R hT t φ ht hφ⟩

end HRS.MC.Sec7.S7PIS3

end

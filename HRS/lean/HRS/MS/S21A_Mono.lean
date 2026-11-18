import HRS.MS.R2WinErrNL7
import HRS.MS.WsPrepAux10

/-!
# S21A packet 1: monotonicity of the class in `ε_*` and of `MovParticleBounds` in the completion constant

* `s21a_cls_mono`: an admissible perturbation with a resulting solution for the smallness `ε_*` is one for every `ε_*' ≥ ε_*`
  (same `ε, ψ, ρ`).  (The classes of S2.1 (ii) are nested, so a single smallest `ε_*` serves several theorems.)
* `s21a_mpb_up`: `MovParticleBounds d s q β C₀ C ρ N P X` for a probability space `P` implies the same bounds with the completion
  constant `C₀' ≥ max C₀ 1` and every constant `CB ≥ (|C|+1)(|C₀|+1)`.  (S6.6 and S10.4 each fix their own existential completion constant;
  to feed the particle bounds of S6.6 to S10.4 the constant must be raised.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21A

open HRS.Whole HRS.MS.R2WinErr

variable {d : ℕ}

theorem s21a_cls_mono (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar ε0 c₁ C₁ ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hle : εstar ≤ ε0) (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    IsAdmissiblePerturbation ρβ ε0 ε ψ ∧ IsResultingSolution d s a β ρβ ε0 ε ψ c₁ C₁ ρ := by
  have hC := s104_C1_nonneg hd hs0 hsd ha hβ hρβ hres
  refine ⟨⟨hadm.smooth, hadm.compactSupport, hadm.nonzero, hadm.meanZero, hadm.small.trans hle⟩,
    hres.cpos, hres.global, hres.init, hres.ratio, fun t ht => ?_, fun t ht => ?_, hres.cont, hres.regular⟩
  · obtain ⟨h1, h2⟩ := hres.weighted t ht
    refine ⟨h1, h2.trans ?_⟩
    have := Real.exp_pos (-c₁ * t)
    nlinarith [mul_nonneg hC this.le]
  · refine (hres.velocity t ht).trans (ENNReal.ofReal_le_ofReal ?_)
    have := Real.exp_pos (-c₁ * t)
    nlinarith [mul_nonneg hC this.le]

theorem s21a_oN_eq (d : ℕ) (s C₀ : ℝ) (N : ℕ) :
    HRS.oN d s C₀ N = C₀ * (N : ℝ) ^ (s / d - 1) + (if s = 0 then Real.log N / (2 * d * N) else 0) := rfl

theorem s21a_lam_nonneg (d : ℕ) (s : ℝ) (N : ℕ) : 0 ≤ (if s = 0 then Real.log N / (2 * d * N) else 0) := by
  split_ifs
  · rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ N := by exact_mod_cast h
      have := Real.log_nonneg this
      positivity
  · exact le_rfl

/-- Real-number estimate behind `s21a_mpb_up`. -/
theorem s21a_oN_ineq (d : ℕ) (s : ℝ) {C₀ C₀' C CB : ℝ} (hle : C₀ ≤ C₀') (h1 : 1 ≤ C₀') (N : ℕ)
    (hCB : (|C| + 1) * (|C₀| + 1) ≤ CB) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ C * HRS.oN d s C₀ N ≤ A ∧ HRS.oN d s C₀' N - HRS.oN d s C₀ N ≤ B ∧
      A + B ≤ CB * HRS.oN d s C₀' N := by
  rw [s21a_oN_eq, s21a_oN_eq]
  set κ : ℝ := (N : ℝ) ^ (s / d - 1) with hκ
  set l : ℝ := (if s = 0 then Real.log N / (2 * d * N) else 0) with hl
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hl0 : 0 ≤ l := s21a_lam_nonneg d s N
  have ho' : 0 ≤ C₀' * κ + l := by nlinarith
  have hκo : κ ≤ C₀' * κ + l := by nlinarith
  have hlo : l ≤ C₀' * κ + l := by nlinarith
  have hC₀' : 0 ≤ C₀' * κ := by nlinarith
  set o' : ℝ := C₀' * κ + l with ho'def
  have hA : |C₀ * κ + l| ≤ (|C₀| + 1) * o' := by
    calc |C₀ * κ + l| ≤ |C₀ * κ| + |l| := abs_add_le _ _
      _ = |C₀| * κ + l := by rw [abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hl0]
      _ ≤ |C₀| * o' + o' := by nlinarith [abs_nonneg C₀]
      _ = (|C₀| + 1) * o' := by ring
  have hB : C * (C₀ * κ + l) ≤ |C| * ((|C₀| + 1) * o') := by
    calc C * (C₀ * κ + l) ≤ |C * (C₀ * κ + l)| := le_abs_self _
      _ = |C| * |C₀ * κ + l| := abs_mul _ _
      _ ≤ |C| * ((|C₀| + 1) * o') := mul_le_mul_of_nonneg_left hA (abs_nonneg _)
  have hD : (C₀' * κ + l) - (C₀ * κ + l) ≤ (|C₀| + 1) * o' := by
    have : (C₀' * κ + l) - (C₀ * κ + l) = C₀' * κ - C₀ * κ := by ring
    rw [this]
    nlinarith [neg_abs_le C₀, abs_nonneg C₀, mul_nonneg (abs_nonneg C₀) hκ0]
  have hE : 0 ≤ (|C₀| + 1) * o' := by positivity
  refine ⟨|C| * ((|C₀| + 1) * o'), (|C₀| + 1) * o', by positivity, hE, hB, hD, ?_⟩
  calc |C| * ((|C₀| + 1) * o') + (|C₀| + 1) * o' = (|C| + 1) * (|C₀| + 1) * o' := by ring
    _ ≤ CB * o' := mul_le_mul_of_nonneg_right hCB ho'

theorem s21a_mpb_up {s q β C₀ C₀' C CB : ℝ} {ρ : ℝ → Euc d → ℝ} {N : ℕ} (hN : 2 ≤ N) (hs : 0 ≤ s)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → EucConfig d N}
    (hle : C₀ ≤ C₀') (h1 : 1 ≤ C₀') (hCB : (|C| + 1) * (|C₀| + 1) ≤ CB)
    (h : MovParticleBounds d s q β C₀ C ρ N P X) : MovParticleBounds d s q β C₀' CB ρ N P X := by
  have hCle : C ≤ CB := by
    have h0 : 0 ≤ |C₀| := abs_nonneg _
    nlinarith [le_abs_self C, abs_nonneg C]
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg hN0 hδ
  intro t ht
  obtain ⟨h1', h2', h3', h4', h5'⟩ := h t ht
  refine ⟨h1'.trans (ENNReal.ofReal_le_ofReal ?_), h2'.trans (ENNReal.ofReal_le_ofReal ?_),
    h3'.trans (ENNReal.ofReal_le_ofReal ?_), ?_, h5'.trans (ENNReal.ofReal_le_ofReal hCle)⟩
  · have := mul_le_mul_of_nonneg_right hCle hNδ
    simpa [mul_assoc] using this
  · exact mul_le_mul_of_nonneg_right hCle hδ
  · have := mul_le_mul_of_nonneg_right hCle hNδ
    simpa [mul_assoc] using this
  · set μ := P.map (X t.toNNReal) with hμ
    have hμ1 : μ Set.univ ≤ 1 := by
      by_cases hm : AEMeasurable (X t.toNNReal) P
      · rw [hμ, Measure.map_apply_of_aemeasurable hm MeasurableSet.univ]; simp
      · rw [hμ, Measure.map_of_not_aemeasurable_of_ne_zero hm (NeZero.ne P)]; simp
    have hpt : ∀ Z : EucConfig d N, ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) +
          HRS.oN d s C₀' N) ≤ ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) +
          HRS.oN d s C₀ N) + ENNReal.ofReal (HRS.oN d s C₀' N - HRS.oN d s C₀ N) := by
      intro Z
      have e : rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀' N =
          (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀ N) +
            (HRS.oN d s C₀' N - HRS.oN d s C₀ N) := by ring
      rw [e]; exact ENNReal.ofReal_add_le
    calc ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀' N) ∂μ
        ≤ ∫⁻ Z, (ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀ N) +
            ENNReal.ofReal (HRS.oN d s C₀' N - HRS.oN d s C₀ N)) ∂μ := lintegral_mono hpt
      _ = ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀ N) ∂μ +
            ENNReal.ofReal (HRS.oN d s C₀' N - HRS.oN d s C₀ N) * μ Set.univ := by
          rw [lintegral_add_right' _ aemeasurable_const, lintegral_const]
      _ ≤ ENNReal.ofReal (C * HRS.oN d s C₀ N) + ENNReal.ofReal (HRS.oN d s C₀' N - HRS.oN d s C₀ N) * 1 :=
          add_le_add h4' (by gcongr)
      _ ≤ ENNReal.ofReal (CB * HRS.oN d s C₀' N) := by
          rw [mul_one]
          obtain ⟨A, B, hA, hB, hCA, hDB, hAB⟩ := s21a_oN_ineq d s hle h1 N hCB
          calc ENNReal.ofReal (C * HRS.oN d s C₀ N) + ENNReal.ofReal (HRS.oN d s C₀' N - HRS.oN d s C₀ N)
              ≤ ENNReal.ofReal A + ENNReal.ofReal B :=
                add_le_add (ENNReal.ofReal_le_ofReal hCA) (ENNReal.ofReal_le_ofReal hDB)
            _ = ENNReal.ofReal (A + B) := (ENNReal.ofReal_add hA hB).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal hAB

end HRS.MS.S21A

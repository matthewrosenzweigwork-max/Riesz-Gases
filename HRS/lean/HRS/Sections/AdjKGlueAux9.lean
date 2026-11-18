import HRS.Sections.AdjKGlueAux8

/-!
# ADJK-GLUE, part 9: Kolmogorov wrapper and remainder energy identification
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_at_sub {m T : ℝ} (w w' : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (w - w').at' t = w.at' t - w'.at' t := rfl

theorem adjkg_at_add {m T : ℝ} (w w' : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (w + w').at' t = w.at' t + w'.at' t := rfl

/-- Kolmogorov equicontinuity for the family of convolution processes `Z n`. -/
theorem adjkg_kolm {m T : ℝ} (hT : 0 < T) {Cz : ℝ} (hCz : 0 ≤ Cz) {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, ℝ → Ω n → NegSobolev d m) (hZm : ∀ n t, Measurable (Z n t))
    (hZc : ∀ n ω, ContinuousOn (fun t => Z n t ω) (Set.Icc 0 T))
    (hZ4 : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ‖Z n t ω - Z n s ω‖ₑ ^ (4 : ℝ) ∂P n ≤ ENNReal.ofReal (Cz * |t - s| ^ 2)) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      P n {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧ η < ‖Z n s ω - Z n t ω‖} ≤
        ENNReal.ofReal ε := by
  have hY : ∀ n, IsKolmogorovProcess (fun (t : Set.Icc (0 : ℝ) T) (ω : Ω n) => Z n t ω) (P n) 4 2
      (Real.toNNReal Cz) := by
    intro n
    refine ⟨fun s t => ?_, fun s t => ?_, by norm_num, by norm_num⟩
    · have := (hZm n s).prodMk (hZm n t)
      rwa [← BorelSpace.measurable_eq] at *
    · have h1 := hZ4 n s s.2 t t.2
      have e1 : ∀ ω, edist (Z n s ω) (Z n t ω) = ‖Z n t ω - Z n s ω‖ₑ := by
        intro ω
        rw [edist_eq_enorm_sub, enorm_sub_rev]
      simp_rw [e1]
      refine h1.trans (le_of_eq ?_)
      have e2 : edist s t = ENNReal.ofReal |(t : ℝ) - s| := by
        rw [Subtype.edist_eq, edist_dist, Real.dist_eq, abs_sub_comm]
      rw [e2, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two,
        ENNReal.ofReal_mul hCz]
      rfl
  intro ε η hε hη
  exact adjk_kolmogorov_equicont_proof T hT 4 2 (by norm_num) (Real.toNNReal Cz) P
    (fun n t ω => Z n t ω) hY
    (fun n => Filter.Eventually.of_forall fun ω =>
      continuousOn_iff_continuous_restrict.1 (hZc n ω)) ε η hε hη

end HRS.AdjK

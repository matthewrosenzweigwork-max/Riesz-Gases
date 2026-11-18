import HRS.Uniform.Q54cAux44

/-!
# Q54c, part 45: generic measure-theoretic lemmas for the final `W₂` estimate
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS

/-- The supremum over `[0,T]` of the norm of a pathwise continuous process is measurable. -/
theorem measurable_biSup_Icc {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {T : ℝ} (hT : 0 ≤ T)
    (F : ℝ → Ω → E) (hF : ∀ t, Measurable (F t))
    (hc : ∀ ω, ContinuousOn (fun t => F t ω) (Set.Icc 0 T)) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖F t ω‖ₑ := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hs
  have hdense : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have heq : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖F t ω‖ₑ) = ⨆ n, ‖F (s n : ℝ) ω‖ₑ := by
    intro ω
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun t ht => ?_
      set g : Set.Icc (0 : ℝ) T → ℝ≥0∞ := fun x => ‖F (x : ℝ) ω‖ₑ with hg
      have hgc : Continuous g := by
        have : Continuous fun x : Set.Icc (0 : ℝ) T => F (x : ℝ) ω :=
          (hc ω).comp_continuous continuous_subtype_val fun x => x.2
        exact continuous_enorm.comp this
      have hcl : IsClosed {x : Set.Icc (0 : ℝ) T | g x ≤ ⨆ n, ‖F (s n : ℝ) ω‖ₑ} :=
        isClosed_le hgc continuous_const
      have hsub : Set.range s ⊆ {x : Set.Icc (0 : ℝ) T | g x ≤ ⨆ n, ‖F (s n : ℝ) ω‖ₑ} := by
        rintro _ ⟨n, rfl⟩
        exact le_iSup (fun n => ‖F (s n : ℝ) ω‖ₑ) n
      have hall : closure (Set.range s) ⊆ {x | g x ≤ ⨆ n, ‖F (s n : ℝ) ω‖ₑ} :=
        closure_minimal hsub hcl
      have hmem : (⟨t, ht⟩ : Set.Icc (0 : ℝ) T) ∈ closure (Set.range s) := by
        rw [hdense.closure_range]; exact Set.mem_univ _
      exact hall hmem
    · exact iSup_le fun n => le_iSup₂_of_le (s n : ℝ) (s n).2 le_rfl
  simp_rw [heq]
  exact Measurable.iSup fun n => (hF _).enorm

/-- Scaling inside the `L²` lintegral. -/
theorem lintegral_const_mul_rpow_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, (c * f ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = c * (∫⁻ ω, f ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  have h1 : ∀ ω, (c * f ω) ^ (2 : ℝ) = c ^ (2 : ℝ) * f ω ^ (2 : ℝ) := fun ω =>
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num

/-- `W₂` between the laws of two random elements of a normed space dominated pointwise by
`c₁ D + c₂ M + c₃ H` (in `ℝ≥0∞`). -/
theorem wasserstein_two_le_of_dom {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B]
    (X Y : Ω → B) (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (D M H : Ω → ℝ≥0∞)
    (hD : Measurable D) (hM : Measurable M) (hH : Measurable H) (c₁ c₂ c₃ : ℝ)
    (hdom : ∀ ω, ‖X ω - Y ω‖ₑ ≤ ENNReal.ofReal c₁ * D ω + ENNReal.ofReal c₂ * M ω +
      ENNReal.ofReal c₃ * H ω) :
    wassersteinE 2 (P.map X) (P.map Y) ≤
      ENNReal.ofReal c₁ * (∫⁻ ω, D ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) +
      ENNReal.ofReal c₂ * (∫⁻ ω, M ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) +
      ENNReal.ofReal c₃ * (∫⁻ ω, H ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
  refine (wassersteinE_le_of_coupling P 2 (by norm_num) X Y hX hY).trans ?_
  have hcost : ∀ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ (2 : ℝ)) ≤
      (ENNReal.ofReal c₁ * D ω + ENNReal.ofReal c₂ * M ω + ENNReal.ofReal c₃ * H ω) ^ (2 : ℝ) := by
    intro ω
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ofReal_norm_eq_enorm]
    exact ENNReal.rpow_le_rpow (hdom ω) (by norm_num)
  refine ENNReal.rpow_le_rpow (lintegral_mono hcost) (by norm_num) |>.trans ?_
  have hm1 : Measurable fun ω => ENNReal.ofReal c₁ * D ω := hD.const_mul _
  have hm2 : Measurable fun ω => ENNReal.ofReal c₂ * M ω := hM.const_mul _
  have hm3 : Measurable fun ω => ENNReal.ofReal c₃ * H ω := hH.const_mul _
  have k1 := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2)
    (f := fun ω => ENNReal.ofReal c₁ * D ω + ENNReal.ofReal c₂ * M ω) (g := fun ω => ENNReal.ofReal c₃ * H ω)
    (hm1.add hm2).aemeasurable hm3.aemeasurable (by norm_num)
  have k2 := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2)
    (f := fun ω => ENNReal.ofReal c₁ * D ω) (g := fun ω => ENNReal.ofReal c₂ * M ω)
    hm1.aemeasurable hm2.aemeasurable (by norm_num)
  have s1 := lintegral_const_mul_rpow_two P (ENNReal.ofReal c₁) ENNReal.ofReal_ne_top D
  have s2 := lintegral_const_mul_rpow_two P (ENNReal.ofReal c₂) ENNReal.ofReal_ne_top M
  have s3 := lintegral_const_mul_rpow_two P (ENNReal.ofReal c₃) ENNReal.ofReal_ne_top H
  simp only [Pi.add_apply] at k1 k2
  rw [s1, s2] at k2
  rw [s3] at k1
  calc _ ≤ _ := k1
    _ ≤ _ := by gcongr

end HRS.Uniform.Q54c

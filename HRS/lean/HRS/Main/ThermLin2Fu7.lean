import HRS.Main.ThermLin2Fu6

/-!
# THERMLIN2 Fu7: the variance computation for `tl2_dyson_fubini` (B4), for an abstract test family `ψ_r`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q45 Classical

section Modif

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A jointly measurable modification of a measurable family, continuous on `[0,T']` a.s. -/
theorem tl2fu_modif {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E']
    [BorelSpace E'] (Z : ℝ → Ω → E') (hZm : ∀ t, Measurable (Z t)) {T' : ℝ} (hT : 0 ≤ T')
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T')) :
    ∃ Z' : ℝ → Ω → E', Measurable (fun q : ℝ × Ω => Z' q.1 q.2) ∧
      ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) T', Z' r ω = Z r ω := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (μ := P) (s := {ω | ¬ ContinuousOn (fun t => Z t ω) (Set.Icc 0 T')}) (ae_iff.1 hZc)
  set cl : ℝ → ℝ := fun r => max 0 (min r T') with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ r, cl r ∈ Set.Icc (0 : ℝ) T' := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  refine ⟨fun r ω => if ω ∈ N then 0 else Z (cl r) ω, ?_, ?_⟩
  · refine measurable_uncurry_of_continuous_of_measurable
      (u := fun r ω => if ω ∈ N then 0 else Z (cl r) ω) (fun ω => ?_) (fun r => ?_)
    · by_cases h : ω ∈ N
      · simp only [h, ↓reduceIte]; exact continuous_const
      · simp only [h, ↓reduceIte]
        have : ContinuousOn (fun t => Z t ω) (Set.Icc 0 T') := by
          by_contra hc; exact h (hsub hc)
        exact this.comp_continuous hclc hclm
    · exact Measurable.ite hNm measurable_const (hZm _)
  · have : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hN0
    filter_upwards [this] with ω hω r hr
    have hc : cl r = r := by
      simp only [hcl, min_eq_left hr.2]; exact max_eq_right hr.1
    simp only [hω, ↓reduceIte, hc]

end Modif

section Main

variable {d : ℕ} {m T' K : ℝ} {Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {G : ℝ → Ω → NegSobolev d m} {Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ}
  {Zs Zw : ℝ → Ω → NegSobolev d m} {t : ℝ} {φ : Torus d → ℝ} {ψ : ℝ → Torus d → ℝ} {B : ℝ}

/-- Uniform second-moment bound of `F_r = ⟨Zw^r, ψ_r⟩`. -/
theorem tl2fu_FF_bound (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ∫ ω, NegSobolev.eval (Zw r ω) (ψ r) * NegSobolev.eval (Zw r ω) (ψ r) ∂P ≤
      (∫ σ in Set.Icc 0 T', traceNormForm (Cd σ)) * (K * B) ^ 2 := by
  obtain ⟨hTC, hτ, hCm⟩ := D.cov_facts
  have hrT : r ∈ Set.Icc (0 : ℝ) T' := ⟨hr.1, hr.2.trans ht.2⟩
  rw [tl2fu_cov_FF D ht E hr hr, min_self]
  have hKB : 0 ≤ K * B := mul_nonneg D.hK ((norm_nonneg _).trans (E.hψB r hr))
  have hsub : Set.Icc (0 : ℝ) r ⊆ Set.Icc 0 T' := Set.Icc_subset_Icc_right hrT.2
  have hwm : Measurable fun σ => tl2fuW Wev t ψ (r, σ) :=
    (tl2fu_W_meas D ht E).comp measurable_prodMk_left
  have hwB : ∀ σ ∈ Set.Icc (0 : ℝ) r, ‖tl2fuW Wev t ψ (r, σ)‖ ≤ K * B :=
    fun σ hσ => tl2fu_W_bound D ht E hr hσ
  have hint := tl2fu_form_int D hrT hwm hwm hwB hwB
  have hτr : IntegrableOn (fun σ => traceNormForm (Cd σ) * (K * B) ^ 2) (Set.Icc 0 r) :=
    (hτ.mono_set hsub).mul_const _
  calc ∫ σ in Set.Icc 0 r, Cd σ (tl2fuW Wev t ψ (r, σ)) (tl2fuW Wev t ψ (r, σ))
      ≤ ∫ σ in Set.Icc 0 r, traceNormForm (Cd σ) * (K * B) ^ 2 := by
        refine setIntegral_mono_on hint hτr measurableSet_Icc fun σ hσ => ?_
        refine (le_abs_self _).trans ((abs_apply_le_tn (hTC σ (hsub hσ)) _ _).trans ?_)
        have := hwB σ hσ
        have h0 := norm_nonneg (tl2fuW Wev t ψ (r, σ))
        refine mul_le_mul_of_nonneg_left ?_ (traceNormForm_nonneg _)
        nlinarith
    _ ≤ ∫ σ in Set.Icc 0 T', traceNormForm (Cd σ) * (K * B) ^ 2 := by
        refine setIntegral_mono_set (hτ.mul_const _) ?_ (Eventually.of_forall hsub)
        exact Eventually.of_forall fun σ => mul_nonneg (traceNormForm_nonneg _) (sq_nonneg _)
    _ = _ := integral_mul_const _ _

end Main

end HRS.ThermLin.Plan2

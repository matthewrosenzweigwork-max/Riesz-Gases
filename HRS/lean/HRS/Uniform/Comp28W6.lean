import HRS.Uniform.Comp28W5
import HRS.Main.GFB4Aux1

/-!
# COMP-28, Wasserstein part, W6: stopping at the horizon and an everywhere-continuous modification
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.GF

section Modify

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The truncation of a covariation density to the horizon `[0,T]`. -/
def dhat (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (T : ℝ) : ℝ → H →L[ℝ] H →L[ℝ] ℝ :=
  fun r => if r ∈ Set.Icc 0 T then d r else 0

lemma dhat_zero (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (T : ℝ) {σ : ℝ} (hσ : σ ∉ Set.Icc 0 T) : dhat d T σ = 0 := by
  simp [dhat, hσ]

lemma dhat_of_mem (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (T : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 T) : dhat d T σ = d σ := by
  simp [dhat, hσ]

lemma int_dhat_eq (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T) (x y : H) (τ : ℝ) :
    ∫ σ in Set.Icc 0 τ, dhat d T σ x y = ∫ σ in Set.Icc 0 (min τ T), d σ x y := by
  by_cases hτ : τ < 0
  · have h1 : Set.Icc (0 : ℝ) τ = ∅ := Set.Icc_eq_empty (by linarith)
    have h2 : Set.Icc (0 : ℝ) (min τ T) = ∅ := Set.Icc_eq_empty (by
      have := min_le_left τ T; linarith)
    rw [h1, h2]; simp
  · push Not at hτ
    rw [gfb4_integral_Icc_clamp (dhat d T) hT (fun σ hσ => by rw [dhat_zero d T hσ]) x y τ,
      max_eq_right (le_min hτ hT)]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    rw [dhat_of_mem d T ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩]

theorem modify_HM {T : ℝ} (hT : 0 ≤ T) {G : ℝ → Ω → H} {d : ℝ → H →L[ℝ] H →L[ℝ] ℝ}
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => d r)) :
    ∃ G' : ℝ → Ω → H, IsHilbertMartingaleWithCovariation P (gfb4_aug P ℱ) T G' (fun r _ => dhat d T r) ∧
      (∀ ω, Continuous fun s => G' s ω) ∧ (∀ ω, G' 0 ω = 0) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, G' τ =ᵐ[P] G τ := by
  -- step 1: stop `G` at `T` (for the filtration `ℱ`) and truncate the density
  have hstop : IsHilbertMartingaleWithCovariation P ℱ T (fun τ ω => G (min τ T) ω) (fun r _ => dhat d T r) := by
    have hsub : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → min τ T = τ := fun τ _ h => min_eq_left h
    obtain ⟨ω₀, hω₀tc, hω₀int, hω₀ent⟩ : ∃ ω₀ : Ω, (∀ σ ∈ Set.Icc 0 T, IsTraceClassCov (d σ)) ∧
        IntegrableOn (fun σ => traceNormForm (d σ)) (Set.Icc 0 T) ∧
        ∀ x y : H, IntegrableOn (fun σ => d σ x y) (Set.Icc 0 T) := by
      obtain ⟨ω, h1, h2, h3⟩ := (hG.sigma_traceClass.and (hG.sigma_pathint.and hG.sigma_entry_int)).exists
      exact ⟨ω, h1, h2, h3⟩
    have hmeasd : ∀ x y : H, Measurable (fun σ => d σ x y) := fun x y =>
      (hG.sigma_meas x y).comp (measurable_id.prodMk (measurable_const (a := ω₀)))
    have hmeasdh : ∀ x y : H, Measurable (fun σ => dhat d T σ x y) := by
      intro x y
      have : (fun σ => dhat d T σ x y) = fun σ => if σ ∈ Set.Icc 0 T then d σ x y else 0 := by
        funext σ; by_cases h : σ ∈ Set.Icc 0 T <;> simp [dhat, h]
      rw [this]
      exact Measurable.ite measurableSet_Icc (hmeasd x y) measurable_const
    have hdhtc : ∀ σ ∈ Set.Icc (0 : ℝ) T, IsTraceClassCov (dhat d T σ) := fun σ hσ => by
      rw [dhat_of_mem d T hσ]; exact hω₀tc σ hσ
    have hdhint : IntegrableOn (fun σ => traceNormForm (dhat d T σ)) (Set.Icc 0 T) :=
      hω₀int.congr_fun (fun σ hσ => by rw [dhat_of_mem d T hσ]) measurableSet_Icc
    have hdhent : ∀ x y : H, IntegrableOn (fun σ => dhat d T σ x y) (Set.Icc 0 T) := fun x y =>
      (hω₀ent x y).congr_fun (fun σ hσ => by rw [dhat_of_mem d T hσ]) measurableSet_Icc
    refine ⟨fun x => ?_, ?_, ?_, fun τ hτ => ?_, fun x y => ?_, fun σ x y => ?_, ?_, ?_, ?_, ?_, fun x y => ?_⟩
    · have := HRS.MRep.martingale_stop_time (hG.martingale x) T
      simpa only [min_comm] using this
    · filter_upwards [hG.zero] with ω h
      simpa [min_eq_left hT] using h
    · filter_upwards [hG.cont] with ω h
      refine h.congr fun τ hτ => ?_
      simp [min_eq_left hτ.2]
    · have := hG.sq_int τ hτ
      simpa [hsub τ hτ.1 hτ.2] using this
    · have : (Function.uncurry fun σ (_ : Ω) => dhat d T σ x y) = fun p : ℝ × Ω => dhat d T p.1 x y := by
        funext p; rfl
      rw [this]; exact (hmeasdh x y).comp measurable_fst
    · exact measurable_const
    · exact Filter.Eventually.of_forall fun ω σ hσ => hdhtc σ hσ
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun ω => hdhint
    · exact Filter.Eventually.of_forall fun ω x y => hdhent x y
    · have h := HRS.MRep.martingale_stop_time (hG.covariation x y) T
      have e : (fun (τ : ℝ) (ω : Ω) => inner ℝ (G (min τ T) ω) x * inner ℝ (G (min τ T) ω) y -
          ∫ σ in Set.Icc 0 τ, dhat d T σ x y) =
          fun τ ω => (fun τ ω => inner ℝ (G τ ω) x * inner ℝ (G τ ω) y -
            ∫ σ in Set.Icc 0 τ, d σ x y) (min T τ) ω := by
        funext τ ω
        simp only [min_comm T τ]
        rw [int_dhat_eq d hT x y τ]
      rw [e]
      exact h
  exact gfb4_modify P ℱ hT (fun τ ω => G (min τ T) ω) (dhat d T) (fun σ hσ => by rw [dhat_zero d T hσ])
    hstop |>.imp fun G' h => ⟨h.1, h.2.1, h.2.2.1, fun τ hτ => by
      refine (h.2.2.2 τ hτ).trans (Filter.EventuallyEq.of_eq ?_)
      funext ω
      simp [min_eq_left hτ.2]⟩

end Modify

end HRS.Uniform.Comp28

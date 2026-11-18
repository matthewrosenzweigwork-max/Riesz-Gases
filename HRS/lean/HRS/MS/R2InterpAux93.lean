import HRS.MS.R2InterpAux92

/-!
# S10.2 (worker S10R), part 93 (packet F5h): the Itô integral of an integrand supported in `[0,t]` is constant after `t`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ι → ℝ}

theorem s102_isItoIntegral_congr {Φ Φ' : ℝ → Ω → ι → ℝ} {M : ℝ → Ω → ℝ} (h : ∀ s ω k, s ≠ 0 → Φ s ω k = Φ' s ω k)
    (hM : IsItoIntegral P ℱ W Φ M) : IsItoIntegral P ℱ W Φ' M := by
  refine ⟨hM.cont, hM.adapted, hM.zero, fun t ht Ψ hΨ => hM.approx t ht Ψ ?_⟩
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
    simpa using (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
  have : ∀ n, sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t =
      sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ' s ω) t := by
    intro n
    unfold sqIntegralOn
    refine lintegral_congr fun ω => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with s hs
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.sub_apply, h s ω k hs]
  simpa only [this] using hΨ

theorem s102_ito_stop [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {Φ : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressiveL2 P ℱ Φ) {t : ℝ} (ht : 0 ≤ t) (hzero : ∀ s ω k, t < s → Φ s ω k = 0)
    (hneg : ∀ s ω k, s < 0 → Φ s ω k = 0) :
    ∀ᵐ ω ∂P, ∀ u, itoIntegral P ℱ W Φ u ω = itoIntegral P ℱ W Φ (min u t) ω := by
  classical
  have hM := isItoIntegral_itoIntegral hW hΦ
  have hres := hM.restrict hW hΦ (a := 0) (b := t) le_rfl ht (A := Set.univ) MeasurableSet.univ
  have hM' : IsItoIntegral P ℱ W (restrictFun Φ 0 t Set.univ)
      (fun u ω => itoIntegral P ℱ W Φ (min u t) ω) := by
    convert hres using 1
    funext u ω
    simp only [Set.mem_univ, ite_true]
    rw [itoIntegral_of_nonpos P ℱ W Φ (min_le_right u 0), sub_zero]
  have hM'' : IsItoIntegral P ℱ W Φ (fun u ω => itoIntegral P ℱ W Φ (min u t) ω) := by
    refine s102_isItoIntegral_congr (Φ := restrictFun Φ 0 t Set.univ) (fun s ω k hs => ?_) hM'
    unfold restrictFun
    by_cases h1 : s ∈ Set.Ioc (0 : ℝ) t
    · simp [h1]
    · have : Φ s ω k = 0 := by
        rcases lt_or_gt_of_ne hs with h | h
        · exact hneg s ω k h
        · exact hzero s ω k (lt_of_not_ge fun hle => h1 ⟨h, hle⟩)
      simp [h1, this]
  exact IsItoIntegral.ae_eq_forall hW hM hM'' hΦ

end HRS.MS.R2Interp

end

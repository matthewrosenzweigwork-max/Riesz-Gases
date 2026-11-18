import HRS.MS.Fp81S21GaussG53
import HRS.MS.Fp81S21VersionG

set_option autoImplicit false
noncomputable section

open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The G3-selected Gaussian coefficient representative has a continuous
version on every finite horizon, with an envelope bound uniform in the
Gaussian realization and the nonnegative time shift. -/
theorem fp81s21_gaussian_physical_continuous_version (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ H : ℝ, 0 < H →
            ∃ D : ℝ, 0 ≤ D ∧
              ∀ G : GaussianRealization R, ∃ qsG : ℝ → G.Ω → r26t6_Coeff,
                fp81s21_MomentRep Es G.P
                  (fun u ω f => OscDual.eval (G.Z u ω) f) qsG M2 ∧
                fp81s21_Six G.P qsG M6 ∧
                fp81s21_MomentRep E G.P
                  (fun u ω f => OscDual.eval (G.Z u ω) f)
                  (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) M2 ∧
                fp81s21_Six G.P
                  (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) M6 ∧
                ∀ a : ℝ, 0 ≤ a →
                  ∃ XG : G.Ω → C(Set.Icc (0 : ℝ) H, r26t6_Coeff),
                    Measurable XG ∧ MemLp XG 2 G.P ∧
                    (∀ t : Set.Icc (0 : ℝ) H,
                      (fun ω => XG ω t) =ᵐ[G.P]
                        (fun ω => fp81s21_gaussian_chartEmbed p Es E
                          (qsG (a + t) ω))) ∧
                    ∃ B : G.Ω → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧
                      Integrable (fun ω => B ω ^ 2) G.P ∧
                      (∫ ω, B ω ^ 2 ∂G.P) ≤ D ∧
                      ∀ᵐ ω ∂G.P, ∀ s t : Set.Icc (0 : ℝ) H,
                        ‖XG ω t - XG ω s‖ ≤
                          B ω * |(t : ℝ) - s| ^ (1 / 8 : ℝ) := by
  obtain ⟨δg, hδg, hδgHalf, hG3⟩ := fp81s21_gaussian_six_momentRep p
  obtain ⟨δg5, hδg5, hδg5Half, hG5⟩ :=
    fp81s21_g5_physical_increment_fourth p
  refine ⟨min δg δg5, lt_min hδg hδg5,
    (min_le_left _ _).trans hδgHalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨M2, M6, hM2, hM6, hG3For⟩ :=
    hG3 δ hδ (hδle.trans (min_le_left _ _)) R Es E
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro H hH
  obtain ⟨CG, hCG, hG5For⟩ :=
    hG5 δ hδ (hδle.trans (min_le_right _ _)) R E H hH
  obtain ⟨D, hD, hHolder⟩ :=
    fp81s21_holder_version_from_six H M6 CG hH hM6 hCG
  refine ⟨D, hD, ?_⟩
  intro G
  obtain ⟨qsG, hStrong, hSixStrong, hWeak, hSixWeak⟩ := hG3For G
  refine ⟨qsG, hStrong, hSixStrong, hWeak, hSixWeak, ?_⟩
  intro a ha
  let qG : ℝ → G.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_gaussian_chartEmbed p Es E (qsG u ω)
  have hms :
      (HRS.MS.S111K4J01.coeffMeasurable : MeasurableSpace r26t6_Coeff) =
        r26t6_coeffMeasurable := rfl
  have hqm : ∀ t,
      @Measurable G.Ω r26t6_Coeff G.mΩ r26t6_coeffMeasurable (qG t) := by
    intro t
    rw [← hms]
    have hpair : Measurable (fun ω : G.Ω => (t, ω)) :=
      measurable_const.prodMk measurable_id
    have hsection : @Measurable G.Ω r26t6_Coeff G.mΩ
        HRS.MS.S111K4J01.coeffMeasurable
        (Function.uncurry (fun u ω =>
          fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) ∘
          fun ω : G.Ω => (t, ω)) := hWeak.1.comp hpair
    have hfun :
        (Function.uncurry (fun u ω =>
          fp81s21_gaussian_chartEmbed p Es E (qsG u ω)) ∘
          fun ω : G.Ω => (t, ω)) = qG t := by
      funext ω
      rfl
    rw [hfun] at hsection
    exact hsection
  have hInc : ∀ a : ℝ, 0 ≤ a → ∀ s t : Set.Icc (0 : ℝ) H,
      MemLp (fun ω => qG (a + t) ω - qG (a + s) ω) 4 G.P ∧
      (∫ ω, ‖qG (a + t) ω - qG (a + s) ω‖ ^ 4 ∂G.P) ≤
        CG * |(t : ℝ) - s| ^ 2 := by
    intro a ha s t
    exact hG5For G qG M2 hWeak a ha s t
  exact hHolder G.P qG hqm hSixWeak hInc a ha

#print axioms HRS.Fp81.S21.fp81s21_gaussian_physical_continuous_version

end HRS.Fp81.S21

end

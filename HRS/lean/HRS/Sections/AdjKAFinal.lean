import HRS.Sections.AdjKAAux5

/-!
# ADJKA: relocated proofs of the `AdjKSpec` packets A2, B1, BCONV

Each `<name>_proof` has the statement of `HRS.AdjK.<name>` verbatim and is tied to it by an `example`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjk_evolution_increment_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Vev : ℝ → ℝ → NegSobolev d (j : ℝ) →L[ℝ] NegSobolev d (j : ℝ),
      IsDualEvolution htr.dyn ρ (j : ℝ) Vev →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ z : NegSobolev d (j : ℝ),
        ‖NegSobolev.embed ((j : ℝ) + 2) (Vev t u z - z)‖ ≤ C * (t - u) * ‖z‖ := by
  obtain ⟨C₁, hC₁, h1⟩ := adjka_inc_near hd htr j hj
  obtain ⟨Cr, cr, hCr, hcr, Vev', hdual', -, hdec', -⟩ := adjk_evolution_along_trajectory hd htr (j : ℝ)
  refine ⟨max C₁ (Cr + 1), le_max_of_le_left hC₁, fun Vev hV u t hu hut z => ?_⟩
  have hτ0 : 0 ≤ t - u := sub_nonneg.2 hut
  by_cases hnear : t - u ≤ 1
  · exact (h1 Vev hV u t hu hut hnear z).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hτ0) (norm_nonneg _))
  · push_neg at hnear
    have hVV : Vev t u = Vev' t u := by
      refine ContinuousLinearMap.ext fun z => ?_
      refine Q54.eq_of_eval_smooth fun φ hφ => ?_
      rw [hV u t hu hut z φ hφ, hdual' u t hu hut z φ hφ]
    have hop : ‖Vev t u z‖ ≤ Cr * ‖z‖ := by
      rw [hVV]
      refine (Vev' t u).le_opNorm z |>.trans ?_
      refine mul_le_mul_of_nonneg_right ((hdec' u t hu hut).trans ?_) (norm_nonneg _)
      calc Cr * Real.exp (-cr * (t - u)) ≤ Cr * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith)) hCr.le
        _ = Cr := mul_one _
    calc ‖NegSobolev.embed ((j : ℝ) + 2) (Vev t u z - z)‖ ≤ ‖Vev t u z - z‖ :=
          NegSobolev.norm_embed_le _ (by linarith) _
      _ ≤ ‖Vev t u z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (Cr + 1) * ‖z‖ := by nlinarith [norm_nonneg z]
      _ ≤ (Cr + 1) * (t - u) * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          nlinarith
      _ ≤ max C₁ (Cr + 1) * (t - u) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hτ0) (norm_nonneg _)

example := (@adjk_evolution_increment_proof : type_of% @HRS.AdjK.adjk_evolution_increment)


theorem adjk_evolution_moment_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (r p : ℝ)
    (hp : 2 ≤ p) :
    ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
      IsDualEvolution htr.dyn ρ r Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ mΩ) (a h : ℝ), 0 ≤ a → 0 < h → h ≤ T →
          ∀ (M : ℝ → Ω → NegSobolev d r)
            (Sg : ℝ → Ω → (NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ)),
            IsHilbertMartingaleWithCovariation P ℱ (a + h) M Sg →
            ∃ Z : ℝ → Ω → NegSobolev d r,
              (∀ t ∈ Set.Icc a (a + h),
                IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d r)) M a t (Z t)) ∧
              (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + h))) ∧
              (∀ t ∈ Set.Icc a (a + h), AEMeasurable (Z t) P) ∧
              ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + h), ‖Z t ω‖ₑ) ^ p ∂P ≤
                ENNReal.ofReal C * ∫⁻ ω,
                  (∫⁻ u in Set.Icc a (a + h), ENNReal.ofReal (traceNormForm (Sg u ω))) ^ (p / 2) ∂P := by
  obtain ⟨Vev, hdual, hplain, ⟨c, hc⟩, -⟩ := adjka_levelInput_traj hd htr r
  refine ⟨Vev, hdual, hplain, fun T hT => ⟨Kot.CD p (2 * c) T, Kot.CD_nonneg _ _ _, ?_⟩⟩
  intro Ω mΩ P _ ℱ a h ha hh hhT M Sg hM
  have hq : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp ((2 * c) * (t - u) / 2) := by
    intro u t hu hut
    have := hc u t hu hut
    rwa [show (2 * c) * (t - u) / 2 = c * (t - u) by ring]
  obtain ⟨Z, h1, h2, h3, h4⟩ := adjka_winmax_p hplain (K := 2 * c) hq hh.le hp Ω P ℱ a ha M Sg hM
  refine ⟨Z, h1, h3, fun t ht => (h2 t ht).aemeasurable, h4.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hp0 : 0 ≤ p := by linarith
  have hb := HilbertBDG.bdgConst_nonneg p
  unfold Kot.CD
  have he : Real.exp (|2 * c| * h / 2) ≤ Real.exp (|2 * c| * T / 2) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg (2 * c)])
  gcongr

example := (@adjk_evolution_moment_proof : type_of% @HRS.AdjK.adjk_evolution_moment)

end HRS.AdjK

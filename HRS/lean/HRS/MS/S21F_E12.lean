import HRS.MS.MfeConfAux115
import HRS.MS.S81G_Sing
import HRS.MS.S21F_E00

/-!
# S21F, packet R26-T3.E12: regularized realizations and their product pushforward laws

Global strong solutions `Ys M` of the cutoff additive SDE (kernel `sb1kM d s M`, noise `p4r_sigma d N β⁻¹`) on the shifted
filtration, measurable at every time, with `law (Ys M t) = ((law Y₀) ⊗ (law of the noise path)).map (r26t3_flow ..)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_cutoff_laws {d N : ℕ} (s a β : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (hW' : IsBrownianFiltration P ℱ W') (Y₀ : Ω → EucConfig d N) (hY₀ : Measurable[ℱ 0] Y₀) :
    ∃ Ys : ℕ → ℝ → Ω → EucConfig d N,
      (∀ M, IsAdditiveSDESolution P (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) W'
        (fun _ => HRS.MS.MfeConf.sb1DriftM (quadraticGradientDyn d s a β) (r26t3_regKernel d s M) N)
        (HRS.MP.SelfSimP4Impl.p4r_sigma d N β⁻¹) Y₀ (fun _ => ⊤) (Ys M)) ∧
      (∀ M t, Measurable (Ys M t)) ∧
      (∀ M t, 0 ≤ t → P.map (Ys M t) =
        ((P.map Y₀).prod (P.map (HRS.MD.EQLawPath.bfPath hW'))).map (r26t3_flow d N s a β M t)) := by
  have hW'' : IsBrownianFiltration P (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) W' :=
    HRS.MP.SelfSimP4Impl.p4r_shiftFil_brownian hW'
  obtain ⟨B, hB⟩ := HRS.MS.S81G.s81g_pot (d := d) a
  set D := quadraticGradientDyn d s a β with hD
  have hPot : HRS.MS.MfeConf.Sb1Pot D.V B := hB
  have hlip : ∀ M : ℕ, HRS.IsLipschitzDrift
      (fun _ : ℝ => HRS.MS.MfeConf.sb1DriftM D (r26t3_regKernel d s M) N) := fun M =>
    HRS.MS.MfeConf.sb1_driftM_isLip D (HRS.MS.MfeConf.sb1kM_isKernel (d := d) s hs M) hPot N
  have hY0 : ∀ t : ℝ, Measurable[HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ t] Y₀ := fun t =>
    hY₀.mono (ℱ.mono (le_max_right t 0)) le_rfl
  have hex : ∀ M : ℕ, ∃ Ys : ℝ → Ω → EucConfig d N,
      IsAdditiveSDESolution P (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) W'
        (fun _ => HRS.MS.MfeConf.sb1DriftM D (r26t3_regKernel d s M) N)
        (HRS.MP.SelfSimP4Impl.p4r_sigma d N β⁻¹) Y₀ (fun _ => ⊤) Ys := fun M =>
    exists_sde_solution_global_exists hW'' _ (hlip M) _ hY0
  choose Ys hYs using hex
  refine ⟨Ys, hYs, fun M τ => ((hYs M).adapted τ).mono ((HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ).le _) le_rfl,
    fun M t ht => ?_⟩
  exact HRS.MS.MfeConf.sb1_law_repr hW'' (hlip M) (hY0 0) (hYs M) ht

end HRS.MS.R26T3

import HRS.MC.Q714GWGauss
import HRS.MC.Q714GWMeas
import HRS.Sections.QuenchAux17

/-!
# Packet GW (row 7.14): `gaussian_window_proof`

The window `procWin m T a Z` of a Gaussian limit field is an a.e. measurable random element of `𝒳_{m,T}` with centred Gaussian law
(`gw_aemeasurable`, `gw_lin_gaussian`, Bernstein interpolants `bInterp`, `gw_gauss_limit`).  Tie: `HRS/MC/Q714GWTie.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Q714.GW

open HRS HRS.Sec7 HRS.Qch

variable {d : ℕ}

theorem gw_bInterp_continuous {m T : ℝ} (hT : 0 < T) (n : ℕ) :
    Continuous (bInterp (d := d) (m := m) hT n) := by
  unfold bInterp
  exact continuous_finsetSum _ fun k _ =>
    (bemb hT n k).continuous.comp (HRS.MD.EQGaussWindow.eqgw_at_continuous _)

theorem gw_functional_gaussian (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hs0 : 0 ≤ s) (hsd : s < d)
    {m : ℝ} (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (Y : Ω → NegSobolev d m) (mf : ModeField d s β β₀ m P Z Y)
    (a : ℝ) (ha : 0 ≤ a) (hmeas : AEMeasurable (procWin m T a Z) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0))
    (ℓ : StrongDual ℝ (PathSpace d m T)) :
    ∃ v : ℝ≥0, P.map (fun ω => ℓ (procWin m T a Z ω)) = gaussianReal 0 v := by
  have hVn : ∀ n : ℕ, ∃ v : ℝ≥0,
      P.map (fun ω => ℓ (bInterp hT n (procWin m T a Z ω))) = gaussianReal 0 v := by
    intro n
    refine gw_lin_gaussian hd hs0 hsd hβ mf (fun k : Fin (n + 1) => Real.toNNReal (a + (bnode hT n k : ℝ)))
      (fun k => ℓ.comp (bemb hT n k)) _ ?_ ?_
    · exact (ℓ.continuous.comp (gw_bInterp_continuous hT n)).measurable.comp_aemeasurable hmeas
    · filter_upwards [hcont] with ω hω
      have hbi : ℓ (bInterp hT n (procWin m T a Z ω)) =
          ∑ k : Fin (n + 1), ℓ (bemb hT n k ((procWin m T a Z ω).at' (bnode hT n k))) := by
        unfold bInterp
        rw [map_sum]
      rw [hbi]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [gw_procWin_at T a ha Z ω hω]
      have : ((Real.toNNReal (a + (bnode hT n k : ℝ)) : ℝ≥0) : ℝ) = a + (bnode hT n k : ℝ) :=
        Real.coe_toNNReal _ (add_nonneg ha (bnode hT n k).2.1)
      simp only [ContinuousLinearMap.comp_apply, this]
  choose v hv using hVn
  have hWm : AEMeasurable (fun ω => ℓ (procWin m T a Z ω)) P :=
    ℓ.continuous.measurable.comp_aemeasurable hmeas
  refine gw_gauss_limit P hv ?_ hWm (fun n =>
    (ℓ.continuous.comp (gw_bInterp_continuous hT n)).measurable.comp_aemeasurable hmeas)
  exact Eventually.of_forall fun ω =>
    (ℓ.continuous.tendsto _).comp (bInterp_tendsto hT (procWin m T a Z ω))

theorem gaussian_window_proof (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m)
    (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z)
    (a : ℝ) (ha : 0 ≤ a) :
    AEMeasurable (procWin m T a Z) P ∧ IsCenteredGaussian (law P (procWin m T a Z)) := by
  have hs0 : 0 ≤ s := hD.1 ▸ D.hs0
  have hsd : s < d := hD.1 ▸ D.hsd
  obtain ⟨Y, mf⟩ := modeField_of_limit hd hβ hβ₀ D hD P Z hZ
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0) := by
    filter_upwards [mf.cont] with ω hω using gw_continuousOn_Ici hω
  have hmeas : AEMeasurable (procWin m T a Z) P := gw_aemeasurable P T a ha Z mf.meas hcont
  refine ⟨hmeas, ?_⟩
  have key := gw_functional_gaussian hd hβ hs0 hsd T hT P Z Y mf a ha hmeas hcont
  have hmap : ∀ L : StrongDual ℝ (PathSpace d m T), (law P (procWin m T a Z)).map L =
      P.map (fun ω => L (procWin m T a Z ω)) := fun L =>
    AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hmeas
  refine ⟨isGaussian_of_map_eq_gaussianReal fun L => ?_, fun L => ?_⟩
  · obtain ⟨v, hv⟩ := key L
    exact ⟨0, v, (hmap L).trans hv⟩
  · obtain ⟨v, hv⟩ := key L
    have hLm : AEMeasurable (fun ω => L (procWin m T a Z ω)) P :=
      L.continuous.measurable.comp_aemeasurable hmeas
    have h1 : ∫ z, L z ∂(law P (procWin m T a Z)) = ∫ x, x ∂((law P (procWin m T a Z)).map L) := by
      rw [integral_map L.continuous.measurable.aemeasurable
        (by exact aestronglyMeasurable_id)]
    rw [h1, hmap L, hv, integral_id_gaussianReal]

end HRS.MC.Q714.GW

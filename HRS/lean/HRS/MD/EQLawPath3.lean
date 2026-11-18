import HRS.MD.EQLawPath1
import HRS.MD.EQLawPath2
import HRS.Stochastic.Bridge

/-!
# EQ-LAW (packet `eq_path_stationary`), part 3: the canonical space `Σ = Config × C(ℝ≥0, ℝ^{N×d})`

* `Sig d N`, `sigW`: the canonical space (initial configuration, continuous driving path) and its coordinate driver.
* `eqlaw_isVectorBrownian_map`: transfer of `IsVectorBrownian` to the image measure.
* `eqlawJ`: the map `ω ↦ (X_u ω, path of W_{u+·} - W_u)` of a flow, and its image measure `law(X_u) ⊗ law(path)`
  (Markov-type independence `indep_zero_path`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQLawPath

variable {d N : ℕ}

/-- The path space `C(ℝ≥0, ℝ^{N×d})`. -/
abbrev WSp (d N : ℕ) : Type := C(ℝ≥0, (Fin N × Fin d) → ℝ)

/-- The canonical space. -/
abbrev Sig (d N : ℕ) : Type := Config d N × WSp d N

/-- The coordinate driver on the canonical space. -/
def sigW (d N : ℕ) : ℝ≥0 → Sig d N → (Fin N → Euc d) :=
  fun t σ i => WithLp.toLp 2 fun j => σ.2 t (i, j)

theorem measurable_sigW (t : ℝ≥0) : Measurable (sigW d N t) := by
  refine measurable_pi_iff.2 fun i => (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_iff.2 fun j => ?_
  exact ((measurable_pi_apply (i, j)).comp (ContinuousMap.measurable_eval t)).comp measurable_snd

theorem continuous_sigW (σ : Sig d N) (i : Fin N) (j : Fin d) :
    Continuous fun t => sigW d N t σ i j := by
  have := (continuous_apply (i, j)).comp σ.2.continuous
  exact this

theorem eqlaw_isVectorBrownian_map {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {P : Measure Ω}
    [IsProbabilityMeasure P] (J : Ω → S) (hJ : Measurable J) {B : ℝ≥0 → S → (Fin N → Euc d)}
    (hBm : ∀ t, Measurable (B t)) (hBc : ∀ σ i j, Continuous fun t => B t σ i j)
    (h : IsVectorBrownian P (fun t ω => B t (J ω))) : IsVectorBrownian (P.map J) B := by
  have hcoord : ∀ i j t, Measurable fun σ => B t σ i j := fun i j t =>
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).measurable.comp
      ((measurable_pi_apply i).comp (hBm t))
  refine ⟨fun i j => ?_, ?_⟩
  · refine ⟨⟨fun I => ?_⟩, Filter.Eventually.of_forall fun σ => hBc σ i j⟩
    have hm : Measurable fun σ => I.restrict (fun t => B t σ i j) :=
      (Finset.measurable_restrict I).comp (measurable_pi_iff.2 fun t => hcoord i j t)
    refine ⟨hm.aemeasurable, ?_⟩
    rw [Measure.map_map hm hJ]
    exact ((h.1 i j).toIsPreBrownianReal.hasLaw I).map_eq
  · set g : Fin N × Fin d → S → (ℝ≥0 → ℝ) := fun ij σ t => B t σ ij.1 ij.2 with hg
    have hgm : ∀ ij, Measurable (g ij) := fun ij => measurable_pi_iff.2 fun t => hcoord ij.1 ij.2 t
    have hP := (iIndepFun_iff_map_fun_eq_pi_map (fun ij => ((hgm ij).comp hJ).aemeasurable)).1 h.2
    refine (iIndepFun_iff_map_fun_eq_pi_map (fun ij => (hgm ij).aemeasurable)).2 ?_
    have hall : Measurable fun σ ij => g ij σ := measurable_pi_iff.2 hgm
    rw [Measure.map_map hall hJ]
    refine hP.trans ?_
    congr 1
    funext ij
    rw [Measure.map_map (hgm ij) hJ]


section Flow

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ}

/-- The map `ω ↦ (Y₀ ω, path of W'_{u+·} - W'_u)` into the canonical space. -/
def eqlawJ (hW : IsBrownianFiltration P ℱ W') (u : ℝ≥0) (Y₀ : Ω → Config d N) : Ω → Sig d N :=
  fun ω => (Y₀ ω, bfPath (isBrownianFiltration_shift hW u) ω)

theorem measurable_eqlawJ (hW : IsBrownianFiltration P ℱ W') (u : ℝ≥0) {Y₀ : Ω → Config d N}
    (hY : Measurable Y₀) : Measurable (eqlawJ hW u Y₀) :=
  hY.prodMk (measurable_bfPath _)

theorem eqlawJ_map [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W') (u : ℝ≥0)
    {Y₀ : Ω → Config d N} (hY : Measurable[ℱ (u : ℝ)] Y₀) :
    P.map (eqlawJ hW u Y₀) =
      (P.map Y₀).prod (P.map (bfPath (isBrownianFiltration_shift hW u))) := by
  have hmeas : Measurable Y₀ := hY.mono (ℱ.le _) le_rfl
  have hs := isBrownianFiltration_shift hW u
  have hbf := measurable_bfPath hs
  have hind : IndepFun Y₀ (bfPath hs) P := by
    have h0 := indep_zero_path hs
    have hle : MeasurableSpace.comap (bfPath hs) inferInstance ≤
        MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => shiftProc W' u t ω) inferInstance := by
      rw [measurableSpace_continuousMap_eq, MeasurableSpace.comap_comp]
      exact le_rfl
    have hle2 : MeasurableSpace.comap Y₀ inferInstance ≤ (shiftFil ℱ u) 0 :=
      hY.comap_le.trans (ℱ.mono (by simp [shiftFil]))
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right h0 hle) hle2
  exact (indepFun_iff_map_prod_eq_prod_map_map hmeas.aemeasurable hbf.aemeasurable).1 hind

theorem eqlawJ_driver (hW : IsBrownianFiltration P ℱ W') (u : ℝ≥0) (Y₀ : Ω → Config d N) (t : ℝ≥0)
    (ω : Ω) : sigW d N t (eqlawJ hW u Y₀ ω) = ofCoords (shiftProc W' u) t ω := rfl

end Flow

end HRS.MD.EQLawPath

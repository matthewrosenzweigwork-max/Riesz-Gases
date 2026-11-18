import HRS.Sections.AdjKGlueAux14

/-!
# ADJK-GLUE, part 15: the characteristic-function comparison for one particle system

`dynamic_comparison_proof'` on the product extension `P ⊗ γ` (Gaussian `G = snd`) and `adjkg_charFun_sub_le` give, for one
particle system on `[0,T]` (filtered, finite entropy) and any times / smooth tests, a bound
`|φ_{L}(t) - φ_{A}(t) φ_γ(t)| ≤ 6 max(1,|t|²) C (B/√N + √(B/N))` between the characteristic function of
`L = (linCoord(ρ^{t_a}, φ_a, X_{t_a}))_a` and that of `A + G`, `A = (linCoord(ρ⁰, U^{0,t_a}φ_a, X₀))_a`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_cmp (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ} (hT : 0 ≤ T)
    {p : ℕ} (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ ts : Fin p → ℝ, (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
          ∀ t : EuclideanSpace ℝ (Fin p),
            ‖charFun (P.map (fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ (ts a))) (φ a) (X (ts a).toNNReal ω) :
                  EuclideanSpace ℝ (Fin p)))) t -
              charFun (P.map (fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (ts a) (φ a)) (X₀ ω) :
                  EuclideanSpace ℝ (Fin p)))) t *
              charFun (multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ ts φ)) t‖ ≤
            6 * max 1 (‖t‖ ^ 2) * (C * (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N +
                Real.sqrt (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N))) := by
  classical
  obtain ⟨C, hC0, hC⟩ := dynamic_comparison_proof'.{0} hd htr T hT p φ hφ
  refine ⟨C, hC0, fun N hN Ω mΩ P hP X₀ W X hX hF hfin ts hts t => ?_⟩
  obtain ⟨ℱ, W', hFs⟩ := hF
  have hNpos : 0 < N := by omega
  set Sg := noiseCovMatrix htr.dyn ρ β⁻¹ ts φ with hSg
  set γ : Measure (EuclideanSpace ℝ (Fin p)) := multivariateGaussian 0 Sg with hγ
  haveI : IsProbabilityMeasure γ := inferInstance
  have hXt := adjkg_enlarge_particle P γ hX
  obtain ⟨ℱ', W'', hFt⟩ := adjkg_enlarge_filtered P γ ℱ W' hFs
  have hπ : MeasurePreserving (Prod.fst : (Ω × EuclideanSpace ℝ (Fin p)) → Ω) (P.prod γ) P := measurePreserving_fst
  have hπ2 : MeasurePreserving (Prod.snd : Ω × EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (P.prod γ) γ := measurePreserving_snd
  have hX₀m : AEMeasurable X₀ P := by
    refine (hX.sol.adapted 0).aemeasurable.congr ?_
    filter_upwards [hX.sol.init] with ω hω
    exact hω
  have hmap : (P.prod γ).map (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => X₀ ωt.1) = P.map X₀ := by
    rw [show (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => X₀ ωt.1) = X₀ ∘ Prod.fst from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [hπ.map_eq]; exact hX₀m) hπ.aemeasurable,
      hπ.map_eq]
  have hent : relEntropy ((P.prod γ).map (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => X₀ ωt.1))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ := by
    rw [hmap]; exact hfin
  have hindep : IndepFun (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => X₀ ωt.1) (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => ωt.2) (P.prod γ) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro u v hu hv
    have e1 : ((fun ωt : Ω × EuclideanSpace ℝ (Fin p) => X₀ ωt.1) ⁻¹' u ∩ (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => ωt.2) ⁻¹' v) =
        (X₀ ⁻¹' u) ×ˢ v := by ext ω; simp
    have e2 : ((fun ωt : Ω × EuclideanSpace ℝ (Fin p) => X₀ ωt.1) ⁻¹' u) = Prod.fst ⁻¹' (X₀ ⁻¹' u) := rfl
    have e3 : ((fun ωt : Ω × EuclideanSpace ℝ (Fin p) => ωt.2) ⁻¹' v) = Set.univ ×ˢ v := by ext ω; simp
    rw [e1, e2, e3, adjkg_prod_preimage, Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul]
  have hcmp := hC N hN (P.prod γ) (fun ωt => X₀ ωt.1) (fun t ωt => W t ωt.1) (fun t ωt => X t ωt.1) hXt
    ⟨ℱ', W'', hFt⟩ hent ts hts (fun ωt => ωt.2) hπ2.map_eq hπ2.aemeasurable hindep
  rw [hmap] at hcmp
  -- the two random vectors
  set Lφ : Ω → EuclideanSpace ℝ (Fin p) := fun ω => (WithLp.toLp 2 fun a =>
    linCoord (withDensityReal (ρ (ts a))) (φ a) (X (ts a).toNNReal ω) : EuclideanSpace ℝ (Fin p)) with hLφ
  set Fφ : Config d N → EuclideanSpace ℝ (Fin p) := fun x => (WithLp.toLp 2 fun a =>
    linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (ts a) (φ a)) x : EuclideanSpace ℝ (Fin p)) with hFφ
  have hφc : ∀ a, Continuous (φ a) := fun a =>
    Torus.continuous_of_continuous_lift ((adjkd_isCk_of_smooth 0 (hφ a)).continuous)
  have hLm : Measurable Lφ := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    exact (adjkg_linCoord_measurable (N := N) _ (hφc a).measurable).comp (hX.sol.adapted _)
  have hFm : Measurable Fφ := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    have hck := adjkd_propagator_ck2 htr.dyn ρ (le_refl (0 : ℝ)) (hts a).1 (φ a)
    exact adjkg_linCoord_measurable (N := N) _
      (Torus.continuous_of_continuous_lift (hck.continuous)).measurable
  have e1 : law (P.prod γ) (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ (ts a))) (φ a) (X (ts a).toNNReal ωt.1) : EuclideanSpace ℝ (Fin p))) = P.map Lφ := by
    show (P.prod γ).map _ = _
    rw [show (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ (ts a))) (φ a) (X (ts a).toNNReal ωt.1) : EuclideanSpace ℝ (Fin p))) = Lφ ∘ Prod.fst from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [hπ.map_eq]; exact hLm.aemeasurable) hπ.aemeasurable,
      hπ.map_eq]
  have hAφm : AEMeasurable (fun ω => Fφ (X₀ ω)) P := hFm.comp_aemeasurable hX₀m
  have hindep' : IndepFun (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => Fφ (X₀ ωt.1)) (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => ωt.2) (P.prod γ) :=
    hindep.comp hFm measurable_id
  have e2 : (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (ts a) (φ a)) (X₀ ωt.1) + ωt.2 a : EuclideanSpace ℝ (Fin p))) =
      fun ωt => Fφ (X₀ ωt.1) + ωt.2 := by
    funext ωt
    ext a
    simp [hFφ]
  have hcf : charFun (law (P.prod γ) (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (ts a) (φ a)) (X₀ ωt.1) + ωt.2 a : EuclideanSpace ℝ (Fin p)))) t =
      charFun (P.map (fun ω => Fφ (X₀ ω))) t * charFun γ t := by
    rw [e2]
    have hA : AEMeasurable (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => Fφ (X₀ ωt.1)) (P.prod γ) :=
      hAφm.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving
    have := hindep'.charFun_map_fun_add_eq_mul hA hπ2.aemeasurable
    have e4 : (P.prod γ).map (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => Fφ (X₀ ωt.1)) = P.map (fun ω => Fφ (X₀ ω)) := by
      rw [show (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => Fφ (X₀ ωt.1)) = (fun ω => Fφ (X₀ ω)) ∘ Prod.fst from rfl,
        ← AEMeasurable.map_map_of_aemeasurable (by rw [hπ.map_eq]; exact hAφm) hπ.aemeasurable,
        hπ.map_eq]
    have e5 : (P.prod γ).map (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => ωt.2) = γ := hπ2.map_eq
    rw [e4, e5] at this
    exact congrFun this t
  -- compare
  haveI : IsProbabilityMeasure (P.map Lφ) :=
    (Measure.isProbabilityMeasure_map_iff hLm.aemeasurable).2 inferInstance
  haveI hνp : IsProbabilityMeasure (law (P.prod γ) (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (ts a) (φ a)) (X₀ ωt.1) + ωt.2 a : EuclideanSpace ℝ (Fin p)))) := by
    rw [e2]
    refine (Measure.isProbabilityMeasure_map_iff ?_).2 inferInstance
    exact (hAφm.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving).add hπ2.aemeasurable
  rw [e1] at hcmp
  have h1 := adjkg_charFun_sub_le (P.map Lφ) (law (P.prod γ) (fun ωt : Ω × EuclideanSpace ℝ (Fin p) => (WithLp.toLp 2 fun a =>
      linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (ts a) (φ a)) (X₀ ωt.1) + ωt.2 a : EuclideanSpace ℝ (Fin p)))) t
  rw [hcf] at h1
  refine h1.trans ?_
  have hc0 : 0 ≤ 6 * max 1 (‖t‖ ^ 2) := by positivity
  exact mul_le_mul_of_nonneg_left hcmp hc0

end HRS.AdjK

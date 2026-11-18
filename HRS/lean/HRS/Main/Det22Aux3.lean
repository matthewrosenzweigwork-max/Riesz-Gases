import HRS.Main.Det22Aux2

/-!
# Packet DET22, part 3: from a `W₁` bound between laws of a.e.-constant paths to a sup-norm bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Det22

variable {d : ℕ}

/-- The `W₁` distance between two Dirac masses is at least the distance of the points. -/
theorem det22_wass_dirac_ge {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (a b : B) (r : ℝ≥0∞) (h : wassersteinE 1 (Measure.dirac a) (Measure.dirac b) ≤ r) :
    ENNReal.ofReal ‖a - b‖ ≤ r := by
  refine le_trans (le_iInf fun π => ?_) h
  obtain ⟨π, h1, h2⟩ := π
  have ha : ∀ᵐ z ∂π, z.1 = a := by
    have : ∀ᵐ y ∂(π.map Prod.fst), y = a := by rw [h1, ae_dirac_eq]; exact eventually_pure.2 rfl
    exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton a)).1 this
  have hb : ∀ᵐ z ∂π, z.2 = b := by
    have : ∀ᵐ y ∂(π.map Prod.snd), y = b := by rw [h2, ae_dirac_eq]; exact eventually_pure.2 rfl
    exact (ae_map_iff measurable_snd.aemeasurable (measurableSet_singleton b)).1 this
  have hu : π Set.univ = 1 := by
    have := congrArg (fun μ => μ Set.univ) h1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
      Measure.dirac_apply_of_mem (Set.mem_univ a)] at this
    exact this
  have : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π = ENNReal.ofReal ‖a - b‖ := by
    rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal ‖a - b‖)]
    · simp [hu]
    · filter_upwards [ha, hb] with z h1 h2
      simp [h1, h2]
  simp only [this, div_one, ENNReal.rpow_one, le_refl]

/-- Sup-norm bound for a.e.-constant paths. -/
theorem det22_path_bound {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m T σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (y : ℝ → NegSobolev d m)
    (B : ℝ) (hB : 0 ≤ B)
    (hdet : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X t ω₀)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)))
    (hy : ContinuousOn y (Set.Icc 0 T))
    (hW : wassersteinE 1 (law P (flucPath m T σ X ρ)) (law P (toPath m T (fun t (_ : Ω) => y t))) ≤
      ENNReal.ofReal B) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) -
        y t‖ ≤ B := by
  obtain ⟨ω₀, h1, h2⟩ := (hdet.and hcont).exists
  have hyc : Continuous fun t : Set.Icc (0 : ℝ) T => y t := continuousOn_iff_continuous_domRestrict.1 hy
  -- the two paths
  set a : PathSpace d m T := flucPath m T σ X ρ ω₀ with ha
  set b : PathSpace d m T := toPath m T (fun t (_ : Ω) => y t) ω₀ with hb
  have hXeq : ∀ ω, (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X t ω₀) → ∀ t ∈ Set.Icc (0 : ℝ) T,
      X (Real.toNNReal t) ω = X (Real.toNNReal t) ω₀ := by
    intro ω hω t ht
    exact hω _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
  have hflucEq : ∀ ω, (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X t ω₀) →
      flucPath m T σ X ρ ω = a := by
    intro ω hω
    rw [ha]
    unfold flucPath
    refine HRS.GF.dite_continuousMap_congr _ _ ?_
    funext t
    rw [hXeq ω hω t.1 t.2]
  have hlawF : law P (flucPath m T σ X ρ) = Measure.dirac a := by
    have : flucPath m T σ X ρ =ᵐ[P] fun _ => a := by
      filter_upwards [h1] with ω hω using hflucEq ω hω
    rw [law, Measure.map_congr this, Measure.map_const]
    simp
  have hlawY : law P (toPath m T (fun t (_ : Ω) => y t)) = Measure.dirac b := by
    have : toPath m T (fun t (_ : Ω) => y t) = fun _ => b := by
      funext ω
      unfold toPath
      refine HRS.GF.dite_continuousMap_congr _ _ ?_
      rfl
    rw [law, this, Measure.map_const]
    simp
  rw [hlawF, hlawY] at hW
  have hab := det22_wass_dirac_ge a b _ hW
  rw [ENNReal.ofReal_le_ofReal_iff hB] at hab
  have hae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X t ω₀ := h1
  filter_upwards [hae] with ω hω t ht
  have e1 : σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
      (withDensityReal (ρ t)) = σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω₀))
      (withDensityReal (ρ t)) := by rw [hXeq ω hω t ht]
  rw [e1]
  let a' : C(Set.Icc (0 : ℝ) T, NegSobolev d m) :=
    ⟨fun t => σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω₀)) (withDensityReal (ρ t)), h2⟩
  let b' : C(Set.Icc (0 : ℝ) T, NegSobolev d m) := ⟨fun t => y t, hyc⟩
  have hA : a = a' := by rw [ha]; unfold flucPath; exact dif_pos h2
  have hB' : b = b' := by rw [hb]; unfold toPath; exact dif_pos hyc
  rw [hA, hB'] at hab
  have := ContinuousMap.norm_coe_le_norm (a' - b') ⟨t, ht⟩
  exact le_trans this hab

end HRS.Det22

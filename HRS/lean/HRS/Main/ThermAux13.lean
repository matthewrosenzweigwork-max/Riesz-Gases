import HRS.Main.ThermAux12

/-!
# THERM helper 13: the recentered window is the uncentred window plus a deterministic path
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d N : ℕ}

section Window

variable (S : PreparedData d) {m : ℝ} (T a : ℝ)

/-- coefficient continuity along the mean-field trajectory -/
theorem therm_coeff_cont (ha : 0 ≤ a) (k : NonzeroLattice d) :
    Continuous fun t : Set.Icc (0 : ℝ) T =>
      Torus.measureRealCoeff (withDensityReal (S.ρ (a + t))) k := by
  have hcont := therm_weak_cont S (a + T) (Torus.realMode k) (continuous_realMode' k)
  have h2 : Continuous fun t : Set.Icc (0 : ℝ) T => ∫ x, Torus.realMode k x * S.ρ (a + t) x :=
    hcont.comp_continuous (continuous_const.add continuous_subtype_val)
      (fun t => ⟨by linarith [t.2.1], by linarith [t.2.2]⟩)
  refine h2.congr fun t => ?_
  have hd := therm_density S (show 0 ≤ a + (t : ℝ) by linarith [t.2.1])
  unfold Torus.measureRealCoeff
  rw [integral_withDensityReal_eq _ hd.measurable hd.nonneg]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem therm_prob_rho (ha : 0 ≤ a) (t : Set.Icc (0 : ℝ) T) :
    IsProbabilityMeasure (withDensityReal (S.ρ (a + t))) :=
  HRS.isProb_withDensityReal (therm_density S (by linarith [t.2.1]))

/-- continuity of the empirical field against a continuous measure path -/
theorem therm_cont_emp (hm2 : (d : ℝ) < 2 * m) (hN : 1 ≤ N) (σ : ℝ)
    (Xp : Set.Icc (0 : ℝ) T → Config d N) (hX : Continuous Xp)
    (ν : Set.Icc (0 : ℝ) T → Measure (Torus d)) [∀ t, IsProbabilityMeasure (ν t)]
    (hν : ∀ k, Continuous fun t => Torus.measureRealCoeff (ν t) k) :
    Continuous fun t => σ • NegSobolev.ofMeasureDiff m (empirical (Xp t)) (ν t) := by
  haveI : ∀ t, IsProbabilityMeasure (empirical (Xp t)) := fun t => empirical_isProbabilityMeasure hN _
  have hmain : Continuous fun t => NegSobolev.ofMeasureDiff m (empirical (Xp t)) (ν t) :=
    therm_cont_ofMeasureDiff hm2 (fun t => empirical (Xp t)) ν (fun k => ?_) hν
  · exact (continuous_const (y := σ)).smul hmain
  · have : (fun t => Torus.measureRealCoeff (empirical (Xp t)) k) =
        fun t => (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (Xp t i) := by
      funext t
      exact integral_empirical (Xp t) (continuous_realMode' k)
    rw [this]
    exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (continuous_realMode' k).comp ((continuous_apply i).comp hX))

/-- The deterministic shift path `t ↦ σ (μ^{a+t} - μ_β)`. -/
def therm_Dfun (m σ : ℝ) (ρβ : Torus d → ℝ) (t : Set.Icc (0 : ℝ) T) : NegSobolev d m :=
  σ • NegSobolev.ofMeasureDiff m (withDensityReal (S.ρ (a + t))) (withDensityReal ρβ)

theorem therm_Dfun_cont (hm2 : (d : ℝ) < 2 * m) (ha : 0 ≤ a) (σ : ℝ) {ρβ : Torus d → ℝ}
    (hρβ : IsProbDensity ρβ) : Continuous (therm_Dfun S T a m σ ρβ) := by
  haveI : ∀ t : Set.Icc (0 : ℝ) T, IsProbabilityMeasure (withDensityReal (S.ρ (a + t))) :=
    therm_prob_rho S T a ha
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal hρβ
  have hmain : Continuous fun t : Set.Icc (0 : ℝ) T =>
      NegSobolev.ofMeasureDiff m (withDensityReal (S.ρ (a + t))) (withDensityReal ρβ) :=
    therm_cont_ofMeasureDiff (α := Set.Icc (0 : ℝ) T) (ν := fun _ => withDensityReal ρβ) hm2
      (fun t => withDensityReal (S.ρ (a + t))) (therm_coeff_cont S T a ha) (fun k => continuous_const)
  exact (continuous_const (y := σ)).smul hmain

theorem therm_window_eq {Ω : Type*} (hm2 : (d : ℝ) < 2 * m) (hN : 1 ≤ N) (ha : 0 ≤ a) (σ : ℝ)
    {ρβ : Torus d → ℝ} (hρβ : IsProbDensity ρβ) (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hc : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    windowFluc m T a σ X (fun _ => ρβ) ω =
      windowFluc m T a σ X S.ρ ω +
        (show PathSpace d m T from
          (⟨therm_Dfun S T a m σ ρβ, therm_Dfun_cont S T a hm2 ha σ hρβ⟩ :
            C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
  haveI : ∀ t : Set.Icc (0 : ℝ) T, IsProbabilityMeasure (withDensityReal (S.ρ (a + t))) :=
    therm_prob_rho S T a ha
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal hρβ
  have hXp : Continuous fun t : Set.Icc (0 : ℝ) T => X (Real.toNNReal a + Real.toNNReal t) ω :=
    continuous_pi fun i => (hc i).comp
      (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))
  have hE := therm_cont_emp T hm2 hN σ
    (fun t => X (Real.toNNReal a + Real.toNNReal t) ω) hXp
    (fun t => withDensityReal (S.ρ (a + t))) (therm_coeff_cont S T a ha)
  have hEβ := therm_cont_emp T hm2 hN σ
    (fun t => X (Real.toNNReal a + Real.toNNReal t) ω) hXp
    (fun _ => withDensityReal ρβ) (fun k => continuous_const)
  have e1 : windowFluc m T a σ X S.ρ ω = (show PathSpace d m T from
      (⟨fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
          (empirical (X (Real.toNNReal a + Real.toNNReal t) ω)) (withDensityReal (S.ρ (a + t))), hE⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
    unfold windowFluc flucPath
    exact dif_pos hE
  have e2 : windowFluc m T a σ X (fun _ => ρβ) ω = (show PathSpace d m T from
      (⟨fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
          (empirical (X (Real.toNNReal a + Real.toNNReal t) ω)) (withDensityReal ρβ), hEβ⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
    unfold windowFluc flucPath
    exact dif_pos hEβ
  rw [e1, e2]
  refine ContinuousMap.ext fun t => ?_
  show σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal a + Real.toNNReal t) ω))
      (withDensityReal ρβ) =
    σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal a + Real.toNNReal t) ω))
      (withDensityReal (S.ρ (a + t))) + therm_Dfun S T a m σ ρβ t
  haveI := empirical_isProbabilityMeasure (N := N) (d := d) (by omega) (X (Real.toNNReal a + Real.toNNReal t) ω)
  rw [NegSobolev.ofMeasureDiff_add hm2 (empirical (X (Real.toNNReal a + Real.toNNReal t) ω))
    (withDensityReal (S.ρ (a + t))) (withDensityReal ρβ), smul_add]
  rfl

end Window

end Main

end HRS

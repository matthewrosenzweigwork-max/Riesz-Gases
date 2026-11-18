import HRS.Main.ThermLin2Ba1

/-!
# THERMLIN2, packet Ba, part 5: D4 (`tl2_stationary_window_indep`)

A window-law helper (finite-dimensional laws against smooth tests at times `a_i + t_j` determine the window law, via
`Q54c.toPath_law_eq`) and the stationary window independence of `a`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- Helper: equality of the finite-dimensional laws against smooth tests at the times `a₁ + t_i`, `a₂ + t_i`, `t_i ∈ [0,T]`,
gives equality of the window laws (`Q54c.toPath_law_eq`; the coordinates are the pairings with `realMode`). -/
theorem tl2Ba_window_law_eq {m T a₁ a₂ : ℝ} (hT : 0 ≤ T) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] (X₁ : ℝ → Ω₁ → NegSobolev d m) (X₂ : ℝ → Ω₂ → NegSobolev d m)
    (hm₁ : ∀ t, Measurable (X₁ t)) (hm₂ : ∀ t, Measurable (X₂ t))
    (hc₁ : ∀ᵐ ω ∂P₁, ContinuousOn (fun t => X₁ t ω) (Set.Icc 0 (a₁ + T)))
    (hc₂ : ∀ᵐ ω ∂P₂, ContinuousOn (fun t => X₂ t ω) (Set.Icc 0 (a₂ + T)))
    (hfdd : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
      (∀ i, Torus.IsSmooth (φ i)) →
      P₁.map (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (X₁ (a₁ + ts i) ω) (φ i) :
        EuclideanSpace ℝ (Fin p))) =
      P₂.map (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (X₂ (a₂ + ts i) ω) (φ i) :
        EuclideanSpace ℝ (Fin p)))) :
    law P₁ (HRS.Main.windowPath m T a₁ X₁) = law P₂ (HRS.Main.windowPath m T a₂ X₂) := by
  refine HRS.Uniform.Q54c.toPath_law_eq (m := m) (T := T) hT P₁ P₂ (fun t ω => X₁ (a₁ + t) ω)
    (fun t ω => X₂ (a₂ + t) ω) (fun t => hm₁ _) (fun t => hm₂ _)
    (by filter_upwards [hc₁] with ω hω using HRS.Uniform.Comp28.contOn_shift (T := T) ha₁ (Y := X₁) hω)
    (by filter_upwards [hc₂] with ω hω using HRS.Uniform.Comp28.contOn_shift (T := T) ha₂ (Y := X₂) hω)
    ?_
  intro p ts ks hts
  set φ : Fin p → Torus d → ℝ := fun i => Torus.realMode (ks i) with hφdef
  have hφ : ∀ i, Torus.IsSmooth (φ i) := fun i => HRS.Uniform.Q48b.q48b_isSmooth_realMode (ks i)
  have hmemφ : ∀ i, MemSobolev m (φ i) := fun i => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ i) m
  have h := hfdd p ts φ hts hφ
  set Sc : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ) :=
    fun v i => Lattice.jp (ks i).1 ^ (-m) * v i with hSc
  have hScm : Measurable Sc := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (measurable_pi_apply i |>.comp (PiLp.continuous_ofLp 2 (fun _ : Fin p => ℝ)).measurable).const_mul _
  have hVm₁ : Measurable (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (X₁ (a₁ + ts i) ω) (φ i) :
      EuclideanSpace ℝ (Fin p))) :=
    HRS.Uniform.Q54c.measurable_toLp_eval fun i =>
      (HRS.Uniform.Q54c.continuous_eval_const (hmemφ i)).measurable.comp (hm₁ _)
  have hVm₂ : Measurable (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (X₂ (a₂ + ts i) ω) (φ i) :
      EuclideanSpace ℝ (Fin p))) :=
    HRS.Uniform.Q54c.measurable_toLp_eval fun i =>
      (HRS.Uniform.Q54c.continuous_eval_const (hmemφ i)).measurable.comp (hm₂ _)
  have e1 : (fun ω i => NegSobolev.coord (X₁ (a₁ + ts i) ω) (ks i)) =
      Sc ∘ (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (X₁ (a₁ + ts i) ω) (φ i) :
        EuclideanSpace ℝ (Fin p))) := by
    funext ω i
    simp only [Function.comp, hSc]
    rw [HRS.Uniform.Q54c.coord_eq_eval]
  have e2 : (fun ω i => NegSobolev.coord (X₂ (a₂ + ts i) ω) (ks i)) =
      Sc ∘ (fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (X₂ (a₂ + ts i) ω) (φ i) :
        EuclideanSpace ℝ (Fin p))) := by
    funext ω i
    simp only [Function.comp, hSc]
    rw [HRS.Uniform.Q54c.coord_eq_eval]
  show P₁.map (fun ω i => NegSobolev.coord (X₁ (a₁ + ts i) ω) (ks i)) =
    P₂.map (fun ω i => NegSobolev.coord (X₂ (a₂ + ts i) ω) (ks i))
  rw [e1, e2, ← Measure.map_map hScm hVm₁, ← Measure.map_map hScm hVm₂, h]

/-- The stationary lag covariance only depends on the order and the differences of the times. -/
theorem tl2Ba_lagCov_shift (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ} {p : ℕ} (c : ℝ) (τ : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) :
    PDE.stationaryLagCov d S.s S.β (PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ) ρβ (fun i => c + τ i) φ =
      PDE.stationaryLagCov d S.s S.β (PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ) ρβ τ φ := by
  ext i j
  simp only [PDE.stationaryLagCov, Matrix.of_apply, add_le_add_iff_left, add_sub_add_left_eq_sub]

/-- D4 proof. -/
theorem tl2_stationary_window_indep_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ} (m T : ℝ) (hT : 0 < T)
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] (Z₁ : ℝ → Ω₁ → NegSobolev d m) (Z₂ : ℝ → Ω₂ → NegSobolev d m)
    {a : ℝ} (ha : 0 ≤ a)
    (hZ₁ : Tl2StatFdd S ρβ m (a + T) P₁ Z₁) (hZ₂ : Tl2StatFdd S ρβ m T P₂ Z₂) :
    law P₁ (HRS.Main.windowPath m T a Z₁) = law P₂ (HRS.Main.windowPath m T 0 Z₂) := by
  refine tl2Ba_window_law_eq hT.le ha le_rfl P₁ P₂ Z₁ Z₂ hZ₁.meas hZ₂.meas hZ₁.cont ?_ ?_
  · simpa only [zero_add] using hZ₂.cont
  · intro p ts φ hts hφ
    have h1 := hZ₁.gaussian p (fun i => a + ts i) φ
      (fun i => ⟨by linarith [(hts i).1], by linarith [(hts i).2]⟩) hφ
    have h2 := hZ₂.gaussian p ts φ hts hφ
    unfold law at h1 h2
    simp only [zero_add]
    rw [h1, h2, tl2Ba_lagCov_shift S a ts φ]

example := (@tl2_stationary_window_indep_proof : type_of% @tl2_stationary_window_indep)

end HRS.ThermLin.Plan2

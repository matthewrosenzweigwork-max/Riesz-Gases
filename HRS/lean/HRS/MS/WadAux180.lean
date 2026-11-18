import HRS.MS.WadAux179

/-!
# S8.3, packet S8H2-6: differentiation under the integral to all orders

`s8h2_parint`: if `F_t ∈ C^j(V,W)` has jets `‖D^kF_t(z)‖ ≤ b_k(t) w(z)` with `b_k` `ν`-integrable and `w` continuous, and the evaluations
`t ↦ D^kF_t(z)(m)` are measurable, then `Ψ = ∫ F_t dν` is `C^j` and `D^kΨ(z) = ∫ D^kF_t(z) dν` for `k ≤ j`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

section ParInt

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem s8h2_iter0_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : ℝ → V → W) (ν : Measure ℝ) (z : V) :
    iteratedFDeriv ℝ 0 (fun z => ∫ t, F t z ∂ν) z = ∫ t, iteratedFDeriv ℝ 0 (F t) z ∂ν := by
  have e : ∀ g : V → W, ∀ z, iteratedFDeriv ℝ 0 g z = (continuousMultilinearCurryFin0 ℝ V W).symm (g z) := by
    intro g z
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  simp_rw [e]
  exact (ContinuousLinearEquiv.integral_comp_comm
    (continuousMultilinearCurryFin0 ℝ V W).symm.toContinuousLinearEquiv (fun t => F t z)).symm

theorem s8h2_parint (j : ℕ) : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (F : ℝ → V → W) (ν : Measure ℝ) {w : V → ℝ}, Continuous w →
    (∀ z, 0 ≤ w z) → (∀ t, ContDiff ℝ j (F t)) →
    (∀ k ≤ j, ∀ z (m : Fin k → V), Measurable (fun t => iteratedFDeriv ℝ k (F t) z m)) →
    (∀ k ≤ j, ∃ b : ℝ → ℝ, Integrable b ν ∧ (∀ t, 0 ≤ b t) ∧ ∀ t z, ‖iteratedFDeriv ℝ k (F t) z‖ ≤ b t * w z) →
    ContDiff ℝ j (fun z => ∫ t, F t z ∂ν) ∧ ∀ k ≤ j, ∀ z,
      iteratedFDeriv ℝ k (fun z => ∫ t, F t z ∂ν) z = ∫ t, iteratedFDeriv ℝ k (F t) z ∂ν := by
  induction j with
  | zero =>
    intro W _ _ _ _ _ F ν w hw hw0 hd hm hb
    obtain ⟨b, hbi, hb0, hbd⟩ := hb 0 le_rfl
    have hF0 : ∀ z, Measurable (fun t => F t z) := fun z => by
      have := hm 0 le_rfl z (fun i => i.elim0)
      simpa [iteratedFDeriv_zero_apply] using this
    have hcont : Continuous (fun z => ∫ t, F t z ∂ν) := by
      refine continuous_iff_continuousAt.2 fun z0 => ?_
      obtain ⟨W0, hW0⟩ := (isCompact_closedBall z0 1).exists_bound_of_continuousOn hw.continuousOn
      have hW0' : ∀ z ∈ Metric.closedBall z0 1, w z ≤ W0 := fun z hz =>
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (hw0 z)] using hW0 z hz)
      refine continuousAt_of_dominated (bound := fun t => b t * W0)
        (Eventually.of_forall fun z => (hF0 z).aestronglyMeasurable) ?_ (hbi.mul_const W0)
        (Eventually.of_forall fun t => ((hd t).continuous).continuousAt)
      filter_upwards [Metric.closedBall_mem_nhds z0 one_pos] with z hz
      refine Eventually.of_forall fun t => ?_
      have h1 := hbd t z
      rw [norm_iteratedFDeriv_zero] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hW0' z hz) (hb0 t))
    refine ⟨contDiff_zero.2 hcont, fun k hk z => ?_⟩
    obtain rfl : k = 0 := by omega
    exact s8h2_iter0_int F ν z
  | succ j ih =>
    intro W _ _ _ _ _ F ν w hw hw0 hd hm hb
    have hdiff : ∀ t, Differentiable ℝ (F t) := fun t => (hd t).differentiable (by exact_mod_cast Nat.succ_ne_zero j)
    have hF0 : ∀ z, Measurable (fun t => F t z) := fun z => by
      have := hm 0 (Nat.zero_le _) z (fun i => i.elim0)
      simpa [iteratedFDeriv_zero_apply] using this
    have hm1 : ∀ z, Measurable (fun t => fderiv ℝ (F t) z) := s8h2_meas_fderiv hdiff hF0
    obtain ⟨b0, hb0i, hb00, hb0d⟩ := hb 0 (Nat.zero_le _)
    obtain ⟨b1, hb1i, hb10, hb1d⟩ := hb 1 (by omega)
    have hderiv : ∀ z0, HasFDerivAt (fun z => ∫ t, F t z ∂ν) (∫ t, fderiv ℝ (F t) z0 ∂ν) z0 := by
      intro z0
      obtain ⟨W0, hW0⟩ := (isCompact_closedBall z0 1).exists_bound_of_continuousOn hw.continuousOn
      have hW0' : ∀ z ∈ Metric.closedBall z0 1, w z ≤ W0 := fun z hz =>
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (hw0 z)] using hW0 z hz)
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z t => F t z)
        (F' := fun z t => fderiv ℝ (F t) z) (bound := fun t => b1 t * W0)
        (Metric.closedBall_mem_nhds z0 one_pos) (Eventually.of_forall fun z => (hF0 z).aestronglyMeasurable)
        ?_ (hm1 z0).aestronglyMeasurable ?_ (hb1i.mul_const W0) ?_
      · refine Integrable.mono' (hb0i.mul_const (w z0)) (hF0 z0).aestronglyMeasurable
          (Eventually.of_forall fun t => ?_)
        have h1 := hb0d t z0
        rw [norm_iteratedFDeriv_zero] at h1
        exact h1
      · refine Eventually.of_forall fun t z hz => ?_
        have h1 := hb1d t z
        rw [norm_iteratedFDeriv_one] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (hW0' z hz) (hb10 t))
      · exact Eventually.of_forall fun t z _ => (hdiff t z).hasFDerivAt
    have hfd : fderiv ℝ (fun z => ∫ t, F t z ∂ν) = fun z => ∫ t, fderiv ℝ (F t) z ∂ν :=
      funext fun z => (hderiv z).fderiv
    have hd' : ∀ t, ContDiff ℝ j (fderiv ℝ (F t)) := fun t => (hd t).fderiv_right (by exact_mod_cast le_refl _)
    have hm' : ∀ k ≤ j, ∀ z (m : Fin k → V), Measurable (fun t => iteratedFDeriv ℝ k (fderiv ℝ (F t)) z m) := by
      intro k hk z m
      refine s8h2_meas_clm fun v => ?_
      have := hm (k + 1) (by omega) z (Fin.snoc (α := fun _ => V) m v)
      have e : ∀ t, iteratedFDeriv ℝ k (fderiv ℝ (F t)) z m v =
          iteratedFDeriv ℝ (k + 1) (F t) z (Fin.snoc (α := fun _ => V) m v) := fun t => by
        rw [iteratedFDeriv_succ_apply_right]
        simp
      simp only [e]
      exact this
    have hb' : ∀ k ≤ j, ∃ b : ℝ → ℝ, Integrable b ν ∧ (∀ t, 0 ≤ b t) ∧
        ∀ t z, ‖iteratedFDeriv ℝ k (fderiv ℝ (F t)) z‖ ≤ b t * w z := by
      intro k hk
      obtain ⟨b, hbi, hb0, hbd⟩ := hb (k + 1) (by omega)
      refine ⟨b, hbi, hb0, fun t z => ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      exact hbd t z
    obtain ⟨hcd, hform⟩ := ih (W := V →L[ℝ] W) (fun t => fderiv ℝ (F t)) ν hw hw0 hd' hm' hb'
    refine ⟨?_, fun k hk z => ?_⟩
    · have h1 : ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [h1, contDiff_succ_iff_fderiv]
      refine ⟨fun z => (hderiv z).differentiableAt, fun h => absurd h (by simp), ?_⟩
      rw [hfd]
      exact hcd
    · rcases k with _ | k
      · exact s8h2_iter0_int F ν z
      · have e1 : ∀ g : V → W, iteratedFDeriv ℝ (k + 1) g z =
            (continuousMultilinearCurryRightEquiv' ℝ k V W).symm (iteratedFDeriv ℝ k (fderiv ℝ g) z) :=
          fun g => by rw [iteratedFDeriv_succ_eq_comp_right]; rfl
        rw [e1, hfd, hform k (by omega) z]
        simp_rw [e1]
        exact (ContinuousLinearEquiv.integral_comp_comm
          (continuousMultilinearCurryRightEquiv' ℝ k V W).symm.toContinuousLinearEquiv
          (fun t => iteratedFDeriv ℝ k (fderiv ℝ (F t)) z)).symm

end ParInt

end HRS.MS.Wad

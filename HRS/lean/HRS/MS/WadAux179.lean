import HRS.MS.WadAux178

/-!
# S8.3, packet S8H2-5: parametric integrals of `C^j` families

`s8h2_meas_fderiv`: if `t ↦ F_t(z)` is measurable for every `z` and every `F_t` is differentiable then so is `t ↦ fderiv F_t z`
(difference quotients).  `s8h2_parint`: if `F_t ∈ C^j` with jets bounded by `b_k(t) w(z)`, `b_k` integrable, and the evaluations
`t ↦ D^kF_t(z)(m)` are measurable, then `Ψ = ∫ F_t dν` is `C^j` with `D^kΨ = ∫ D^kF_t dν`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

section Meas

variable {α : Type} [MeasurableSpace α] {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem s8h2_meas_clm {L : α → V →L[ℝ] W} (h : ∀ v, Measurable (fun t => L t v)) : Measurable L := by
  let b := Module.finBasis ℝ V
  let Φ : (Fin (Module.finrank ℝ V) → W) ≃L[ℝ] (V →L[ℝ] W) :=
    LinearEquiv.toContinuousLinearEquiv ((b.constr ℝ).trans LinearMap.toContinuousLinearMap)
  have e : L = fun t => Φ (fun i => L t (b i)) := by
    funext t
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    simp [Φ, Module.Basis.constr_basis]
  rw [e]
  exact Φ.continuous.measurable.comp (measurable_pi_iff.2 fun i => h (b i))

theorem s8h2_meas_fderiv {F : α → V → W} (hdiff : ∀ t, Differentiable ℝ (F t))
    (hm : ∀ z, Measurable (fun t => F t z)) (z : V) : Measurable (fun t => fderiv ℝ (F t) z) := by
  refine s8h2_meas_clm fun v => ?_
  have hlim : Tendsto (fun n : ℕ => fun t => (((n : ℝ) + 1)) • (F t (z + (1 / ((n : ℝ) + 1)) • v) - F t z))
      atTop (𝓝 (fun t => fderiv ℝ (F t) z v)) := by
    rw [tendsto_pi_nhds]
    intro t
    have h1 : HasDerivAt (fun s : ℝ => F t (z + s • v)) (fderiv ℝ (F t) z v) 0 := by
      have h2 : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
      have h3 := (((hdiff t) (z + (0 : ℝ) • v)).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h2
      simp only [zero_smul, add_zero] at h3
      exact h3
    have h4 := h1.tendsto_slope_zero
    have h5 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity⟩
    refine (h4.comp h5).congr fun n => ?_
    simp [Function.comp]
  refine measurable_of_tendsto_metrizable (fun n => ?_) hlim
  exact ((hm (z + (1 / ((n : ℝ) + 1)) • v)).sub (hm z)).const_smul _

end Meas

section Meas2

variable {α : Type} [MeasurableSpace α] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem s8h2_meas_iter (k : ℕ) : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (F : α → V → W), (∀ t, ContDiff ℝ k (F t)) →
    (∀ z, Measurable (fun t => F t z)) → ∀ z (m : Fin k → V),
      Measurable (fun t => iteratedFDeriv ℝ k (F t) z m) := by
  induction k with
  | zero =>
    intro W _ _ _ _ _ F hF hm z m
    simp only [iteratedFDeriv_zero_apply]
    exact hm z
  | succ k ih =>
    intro W _ _ _ _ _ F hF hm z m
    have hdiff : ∀ t, Differentiable ℝ (F t) := fun t => (hF t).differentiable (by exact_mod_cast Nat.succ_ne_zero k)
    have hF' : ∀ t, ContDiff ℝ k (fderiv ℝ (F t)) := fun t =>
      (hF t).fderiv_right (by exact_mod_cast le_refl _)
    have hm' : ∀ z, Measurable (fun t => fderiv ℝ (F t) z) := s8h2_meas_fderiv hdiff hm
    have h := ih (W := V →L[ℝ] W) (fun t => fderiv ℝ (F t)) hF' hm' z (Fin.init m)
    have e : (fun t => iteratedFDeriv ℝ (k + 1) (F t) z m) =
        fun t => iteratedFDeriv ℝ k (fderiv ℝ (F t)) z (Fin.init m) (m (Fin.last k)) := by
      funext t
      exact iteratedFDeriv_succ_apply_right m
    rw [e]
    exact (ContinuousLinearMap.measurable_apply (m (Fin.last k))).comp h

end Meas2

end HRS.MS.Wad

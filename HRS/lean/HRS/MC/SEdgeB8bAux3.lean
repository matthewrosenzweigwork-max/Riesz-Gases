import HRS.MC.SEdgeB8bAux2

/-!
# Packet B8b, helper file 3: convergence in measure of Euclidean-valued variables
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

theorem b8b_norm_euc_le_sum {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) : ‖v‖ ≤ ∑ a, |v a| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  calc ∑ j, ‖v j‖ ^ 2 = ∑ j, |v j| ^ 2 := by simp
    _ ≤ (∑ j, |v j|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem b8b_eLp_tendsto {F : ℕ → Ω → ℝ} (hm : ∀ L, AEStronglyMeasurable (F L) P)
    (h : Tendsto (fun L => ∫⁻ ω, ‖F L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun L => eLpNorm (F L) 2 P) atTop (𝓝 0) := by
  have h2 : ∀ L, eLpNorm (F L) 2 P = (∫⁻ ω, ‖F L ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    intro L
    rw [← HRS.ResponseAux.eLpNorm_two_sq (hm L), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [h2]
  have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  exact this.comp h

theorem b8b_inMeasure_euclid {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    {Y : Ω → EuclideanSpace ℝ (Fin p)}
    (h : ∀ a, TendstoInMeasure P (fun L ω => X L ω a) atTop (fun ω => Y ω a)) :
    TendstoInMeasure P X atTop Y := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set δ := ε / (p + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : ∀ L, {ω | ε ≤ ‖X L ω - Y ω‖} ⊆ ⋃ a : Fin p, {ω | δ ≤ ‖X L ω a - Y ω a‖} := by
    intro L ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hcon
    have h1 := b8b_norm_euc_le_sum (X L ω - Y ω)
    have h2 : ∑ a, |(X L ω - Y ω) a| ≤ ∑ _a : Fin p, δ := by
      refine Finset.sum_le_sum fun a _ => ?_
      have := hcon a
      simp only [PiLp.sub_apply, Real.norm_eq_abs] at this ⊢
      exact this.le
    have h3 : ∑ _a : Fin p, δ = p * δ := by simp
    have h4 : (p : ℝ) * δ < ε := by
      rw [hδ, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hs : ∀ L, P {ω | ε ≤ ‖X L ω - Y ω‖} ≤ ∑ a : Fin p, P {ω | δ ≤ ‖X L ω a - Y ω a‖} := by
    intro L
    exact (measure_mono (hsub L)).trans (measure_iUnion_fintype_le _ _)
  have hlim : Tendsto (fun L => ∑ a : Fin p, P {ω | δ ≤ ‖X L ω a - Y ω a‖}) atTop (𝓝 0) := by
    have : ∀ a : Fin p, Tendsto (fun L => P {ω | δ ≤ ‖X L ω a - Y ω a‖}) atTop (𝓝 0) := fun a =>
      (tendstoInMeasure_iff_norm.1 (h a)) δ hδ0
    simpa using tendsto_finset_sum _ fun a _ => this a
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hs

end Prob

end HRS.MC.SEdge.B8b

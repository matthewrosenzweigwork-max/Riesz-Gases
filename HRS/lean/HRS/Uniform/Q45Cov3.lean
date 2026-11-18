import HRS.Uniform.Q45Cov2
import HRS.Uniform.MaximalAux

/-!
# Q45 (Lemma 3.20): bounds and weak continuity for trace-class forms and propagated observations
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Psd

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma psd_diag_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) (v : H) :
    C v v ≤ traceNormForm C * ‖v‖ ^ 2 := by
  by_cases hv : v = 0
  · subst hv; simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set e : H := (‖v‖⁻¹) • v with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hon : Orthonormal ℝ (fun _ : Fin 1 => e) :=
    orthonormal_iff_ite.2 (fun i j => by
      have : i = j := Subsingleton.elim i j
      subst this
      simp [real_inner_self_eq_norm_sq, hen])
  let p : OrthonormalPairs H := ⟨⟨1, fun _ => e, fun _ => e⟩, hon, hon⟩
  have h1 := pairSum_le_traceNormForm (bddAbove_pairSum hC) p
  simp only [Finset.univ_unique, Finset.sum_singleton, p] at h1
  have h2 : C e e = (‖v‖⁻¹) ^ 2 * C v v := by
    rw [he]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h3 : C e e ≤ traceNormForm C := (le_abs_self _).trans h1
  rw [h2] at h3
  have h4 : 0 < (‖v‖⁻¹) ^ 2 := by positivity
  have : C v v ≤ ‖v‖ ^ 2 * traceNormForm C := by
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖v‖)
    calc C v v = ‖v‖ ^ 2 * ((‖v‖⁻¹) ^ 2 * C v v) := by field_simp
      _ ≤ _ := this
  linarith

lemma psd_apply_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) (v w : H) :
    |C v w| ≤ traceNormForm C * (‖v‖ * ‖w‖) := by
  have hcs : (C v w) ^ 2 ≤ C v v * C w w := by
    have h := fun t : ℝ => hC.nonneg (v + t • w)
    have h2 : ∀ t : ℝ, 0 ≤ C w w * t ^ 2 + (2 * C v w) * t + C v v := by
      intro t
      have := h t
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul] at this
      rw [hC.symm w v] at this
      nlinarith [this]
    have h3 : ∀ t : ℝ, 0 ≤ C w w * (t * t) + (2 * C v w) * t + C v v := fun t => by
      have := h2 t; nlinarith [this]
    have := discrim_le_zero h3
    unfold discrim at this
    nlinarith [this]
  have hv := psd_diag_le hC v
  have hw := psd_diag_le hC w
  have hv0 : 0 ≤ C v v := hC.nonneg v
  have hw0 : 0 ≤ C w w := hC.nonneg w
  have ht0 := traceNormForm_nonneg C
  rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs]
  calc (C v w) ^ 2 ≤ C v v * C w w := hcs
    _ ≤ (traceNormForm C * ‖v‖ ^ 2) * (traceNormForm C * ‖w‖ ^ 2) :=
        mul_le_mul hv hw hw0 (by positivity)
    _ = (traceNormForm C * (‖v‖ * ‖w‖)) ^ 2 := by ring

/-- Weak-times-weak continuity of a nonnegative trace-class form. -/
lemma psd_tendsto_weak {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {ι : Type*} {l : Filter ι}
    (u w : ι → H) (u₀ w₀ : H) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᶠ i in l, ‖u i‖ ≤ B)
    (hw : ∀ᶠ i in l, ‖w i‖ ≤ B)
    (hu₀ : ∀ x, Tendsto (fun i => inner ℝ (u i) x) l (𝓝 (inner ℝ u₀ x)))
    (hw₀ : ∀ x, Tendsto (fun i => inner ℝ (w i) x) l (𝓝 (inner ℝ w₀ x))) :
    Tendsto (fun i => C (u i) (w i)) l (𝓝 (C u₀ w₀)) := by
  obtain ⟨ℓ, hs, hsum⟩ := hC.exists_decomp'
  have e1 : ∀ i, C (u i) (w i) = ∑' j, inner ℝ (ℓ j) (u i) * inner ℝ (ℓ j) (w i) :=
    fun i => (hsum _ _).tsum_eq.symm
  have e2 : C u₀ w₀ = ∑' j, inner ℝ (ℓ j) u₀ * inner ℝ (ℓ j) w₀ := (hsum _ _).tsum_eq.symm
  simp_rw [e1]
  rw [e2]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => ‖ℓ j‖ ^ 2 * (B * B))
    (hs.mul_right _) (fun j => ?_) ((hu.and hw).mono fun i hi j => ?_)
  · have h1 : Tendsto (fun i => inner ℝ (ℓ j) (u i)) l (𝓝 (inner ℝ (ℓ j) u₀)) := by
      simpa [real_inner_comm] using hu₀ (ℓ j)
    have h2 : Tendsto (fun i => inner ℝ (ℓ j) (w i)) l (𝓝 (inner ℝ (ℓ j) w₀)) := by
      simpa [real_inner_comm] using hw₀ (ℓ j)
    exact h1.mul h2
  · rw [norm_mul]
    calc ‖inner ℝ (ℓ j) (u i)‖ * ‖inner ℝ (ℓ j) (w i)‖
        ≤ (‖ℓ j‖ * ‖u i‖) * (‖ℓ j‖ * ‖w i‖) :=
          mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
      _ ≤ (‖ℓ j‖ * B) * (‖ℓ j‖ * B) := by
          gcongr
          · exact hi.1
          · exact hi.2
      _ = ‖ℓ j‖ ^ 2 * (B * B) := by ring

end Psd

end HRS.Uniform.Q45

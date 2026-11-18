import HRS.Uniform.Q45Jor3

/-!
# Q45 (Lemma 3.20): measurable Jordan decomposition of a trace density
-/

noncomputable section

open MeasureTheory Filter Topology HRS.HilbertCLTAux HRS.Uniform.Q07c
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Dens

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma abs_apply_le_traceNormForm {D : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |D (p.1.2.1 i) (p.1.2.2 i)|))
    (x y : H) : |D x y| ≤ traceNormForm D * (‖x‖ * ‖y‖) := by
  by_cases hx : x = 0
  · subst hx; simp
  by_cases hy : y = 0
  · subst hy; simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  set e : H := (‖x‖⁻¹) • x with he
  set f : H := (‖y‖⁻¹) • y with hf
  have hen : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have hfn : ‖f‖ = 1 := by rw [hf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
  have hone : ∀ g : H, ‖g‖ = 1 → Orthonormal ℝ (fun _ : Fin 1 => g) := fun g hg =>
    orthonormal_iff_ite.2 (fun i j => by
      have : i = j := Subsingleton.elim i j
      subst this
      simp [real_inner_self_eq_norm_sq, hg])
  let p : OrthonormalPairs H := ⟨⟨1, fun _ => e, fun _ => f⟩, hone e hen, hone f hfn⟩
  have h1 := pairSum_le_traceNormForm hb p
  simp only [Finset.univ_unique, Finset.sum_singleton, p] at h1
  have h2 : D e f = (‖x‖⁻¹) * (‖y‖⁻¹) * D x y := by
    rw [he, hf]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [h2, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hxn), abs_of_pos (inv_pos.2 hyn)] at h1
  have := mul_le_mul_of_nonneg_left h1 (mul_pos hxn hyn).le
  calc |D x y| = ‖x‖ * ‖y‖ * (‖x‖⁻¹ * ‖y‖⁻¹ * |D x y|) := by field_simp
    _ ≤ ‖x‖ * ‖y‖ * traceNormForm D := this
    _ = _ := by ring

lemma opNorm_formOp_le {D : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |D (p.1.2.1 i) (p.1.2.2 i)|))
    (x : H) : ‖formOp D x‖ ≤ traceNormForm D * ‖x‖ := by
  by_cases h0 : formOp D x = 0
  · rw [h0]; simp only [norm_zero]; exact mul_nonneg (traceNormForm_nonneg _) (norm_nonneg _)
  have hn : 0 < ‖formOp D x‖ := norm_pos_iff.2 h0
  have := abs_apply_le_traceNormForm hb x (formOp D x)
  rw [← inner_formOp, real_inner_self_eq_norm_sq] at this
  have h2 : ‖formOp D x‖ ^ 2 = ‖formOp D x‖ * ‖formOp D x‖ := sq _
  rw [abs_of_nonneg (by positivity)] at this
  nlinarith [norm_nonneg x]

/-- A measurable square root of the square of a symmetric operator commutes with it. -/
lemma sqrtOp_comm {M X : H →L[ℝ] H} (hM : IsPSDOp M) {c : ℝ} (hc : 0 < c)
    (hMc : ∀ x, inner ℝ (M x) x ≤ c * ‖x‖ ^ 2) (hX : X * M = M * X) :
    X * sqrtOp c M = sqrtOp c M * X := by
  have hD1 := norm_one_sub_inv_smul_le hM hc hMc
  have hXD : X * ((1 : H →L[ℝ] H) - c⁻¹ • M) = ((1 : H →L[ℝ] H) - c⁻¹ • M) * X := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hX]; simp
  have := comm_sqrtLimOp hD1 hXD
  simp only [sqrtOp]
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, this]; simp

end Dens

end HRS.Uniform.Q45

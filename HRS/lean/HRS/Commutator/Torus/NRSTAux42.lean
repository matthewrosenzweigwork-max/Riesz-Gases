import HRS.Commutator.Torus.NRSTAux41

/-!
# NRS-T, part 42: evenness of `θ₀`, change of variables, and the `Ḣ^σ` norm of the lifts
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_theta0_neg (v : 𝔼) : nrstr_theta0 (d := d) (-v) = nrstr_theta0 (d := d) v := by
  rw [nrstr_theta0_apply, nrstr_theta0_apply, nrstr_bumpE_neg]

lemma nrstr_int_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : 𝔼 → E) {N : ℝ}
    (hN : 0 < N) (k : 𝔼) :
    ∫ ξ : 𝔼, G (N • (ξ - k)) = (N ^ d)⁻¹ • ∫ η : 𝔼, G η := by
  have h1 : ∫ ξ : 𝔼, G (N • (ξ - k)) = ∫ ξ : 𝔼, (fun x => G (N • x)) ξ :=
    integral_sub_right_eq_self (fun x : 𝔼 => G (N • x)) k
  rw [h1, Measure.integral_comp_smul]
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]

/-- `m₀ = ∫ |θ₀|²`. -/
def nrstr_m0 (d : ℕ) : ℝ := ∫ η : EuclideanSpace ℝ (Fin d), ‖nrstr_theta0 (d := d) η‖ ^ 2

lemma nrstr_theta0_norm (v : 𝔼) : ‖nrstr_theta0 (d := d) v‖ = nrstr_bumpE (d := d) v := by
  rw [nrstr_theta0_apply, Complex.norm_real, Real.norm_of_nonneg (nrstr_bumpE_nonneg v)]

lemma nrstr_m0_pos : 0 < nrstr_m0 d := by
  unfold nrstr_m0
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : 𝔼)) ?_ ?_
    (fun v => by positivity) ?_
  · exact ((nrstr_theta0 (d := d)).continuous.norm).pow 2
  · have : HasCompactSupport (fun v : 𝔼 => ‖nrstr_theta0 (d := d) v‖) := by
      simp_rw [nrstr_theta0_norm]; exact nrstr_bumpE_cs
    exact this.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  · rw [nrstr_theta0_norm, nrstr_bumpE_zero]; norm_num

end HRS.Commutator.TorusNote

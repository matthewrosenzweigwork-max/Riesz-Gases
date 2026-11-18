import HRS.PDE.MovAAux5

/-!
# MOVA Aux6: integration by parts for the tilted Gibbs weight (`C¹` potentials), transported to `Config d N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

/-- `d1c_ibp` for a `C¹` potential (the proof of `d1c_ibp` uses only `C¹`). -/
theorem mova_ibp {n : ℕ} {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU1 : Torus.IsCk 1 U)
    {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) :
    ∫ x, d1_gen κ (d1_gradDrift U) φ x * d1_gibbsWeight κ U x = 0 := by
  have hφ1 : Torus.IsCk 1 φ := (show ContDiff ℝ 2 (Torus.lift φ) from hφ).of_le (by norm_num)
  have hG1 := d1c_gibbs_isCk1 (κ := κ) hU1
  have hGc : Continuous (fun x => d1_gibbsWeight κ U x) :=
    Torus.continuous_of_continuous_lift
      (show ContDiff ℝ 1 (Torus.lift (fun x => d1_gibbsWeight κ U x)) from hG1).continuous
  have hcont : ∀ j : Fin n, Continuous (Torus.partialDeriv j U) := fun j =>
    PDE.continuous_partialDeriv j U hU1
  have hcontφ : ∀ j : Fin n, Continuous (Torus.partialDeriv j φ) := fun j =>
    PDE.continuous_partialDeriv j φ hφ1
  have hcont2 : ∀ j : Fin n, Continuous (Torus.partialDeriv j (Torus.partialDeriv j φ)) :=
    fun j => PDE.continuous_partialDeriv j _ (d1c_isCk1_partialDeriv hφ j)
  have hint : ∀ g : Torus n → ℝ, Continuous g → Integrable g := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- per-coordinate identity: κ ∫ ∂_j∂_jφ G = ∫ ∂_jU ∂_jφ G
  have hj : ∀ j : Fin n, κ * (∫ x, Torus.partialDeriv j (Torus.partialDeriv j φ) x *
      d1_gibbsWeight κ U x) = ∫ x, Torus.partialDeriv j U x * Torus.partialDeriv j φ x *
      d1_gibbsWeight κ U x := by
    intro j
    have h := PDE.integral_partialDeriv_mul j (Torus.partialDeriv j φ)
      (fun y => d1_gibbsWeight κ U y) (d1c_isCk1_partialDeriv hφ j) hG1
    have hpt : ∀ x, Torus.partialDeriv j φ x * Torus.partialDeriv j
        (fun y => d1_gibbsWeight κ U y) x =
        -κ⁻¹ * (Torus.partialDeriv j U x * Torus.partialDeriv j φ x * d1_gibbsWeight κ U x) :=
      fun x => by rw [d1c_partialDeriv_gibbs hU1 j x]; ring
    have h3 : (∫ x, Torus.partialDeriv j φ x * Torus.partialDeriv j
        (fun y => d1_gibbsWeight κ U y) x) = -κ⁻¹ * (∫ x, Torus.partialDeriv j U x *
        Torus.partialDeriv j φ x * d1_gibbsWeight κ U x) := by
      simp_rw [hpt]
      rw [integral_const_mul]
    rw [h, h3]
    field_simp
  have hpt : ∀ x, d1_gen κ (d1_gradDrift U) φ x * d1_gibbsWeight κ U x =
      ∑ j, (κ * (Torus.partialDeriv j (Torus.partialDeriv j φ) x * d1_gibbsWeight κ U x) -
        Torus.partialDeriv j U x * Torus.partialDeriv j φ x * d1_gibbsWeight κ U x) := by
    intro x
    rw [d1c_gen_gradDrift κ U hφ x]
    simp only [sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, mul_assoc]
  have hsplit : (∫ x, d1_gen κ (d1_gradDrift U) φ x * d1_gibbsWeight κ U x) =
      ∑ j, (κ * (∫ x, Torus.partialDeriv j (Torus.partialDeriv j φ) x *
        d1_gibbsWeight κ U x) - ∫ x, Torus.partialDeriv j U x * Torus.partialDeriv j φ x *
        d1_gibbsWeight κ U x) := by
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_sub, integral_const_mul]
      · exact ((hint _ ((hcont2 j).mul hGc)).const_mul κ)
      · exact hint _ (((hcont j).mul (hcontφ j)).mul hGc)
    · intro j _
      exact ((hint _ ((hcont2 j).mul hGc)).const_mul κ).sub
        (hint _ (((hcont j).mul (hcontφ j)).mul hGc))
  rw [hsplit]
  exact Finset.sum_eq_zero fun j _ => by rw [hj j, sub_self]


/-- The tilted potential `U - κψ`. -/
def mova_tilt {n : ℕ} (κ : ℝ) (U ψ : Torus n → ℝ) : Torus n → ℝ := fun x => U x - κ * ψ x

theorem mova_grad_tilt {n : ℕ} {κ : ℝ} {U ψ : Torus n → ℝ} (hU : Torus.IsCk 1 U)
    (hψ : Torus.IsCk 2 ψ) (x : Torus n) :
    Torus.grad (mova_tilt κ U ψ) x = Torus.grad U x - κ • Torus.grad ψ x := by
  have hψ1 := mova_isCk_one_of_two hψ
  ext j
  rw [mova_grad_apply, PiLp.sub_apply, PiLp.smul_apply, mova_grad_apply, mova_grad_apply]
  have e : mova_tilt κ U ψ = fun y => U y + (-κ) * ψ y := by
    funext y; simp [mova_tilt]; ring
  rw [e, mova_partialDeriv_add j hU (mova_isCk_const_mul _ hψ1),
    mova_partialDeriv_const_mul j hψ1]
  simp only [smul_eq_mul]
  ring

/-- Tilted invariance: `∫ (Lψ + κ‖∇ψ‖²) e^{-U/κ + ψ} = 0`. -/
theorem mova_ibp_tilt {n : ℕ} {κ : ℝ} (hκ : 0 < κ) {U ψ : Torus n → ℝ} (hU : Torus.IsCk 1 U)
    (hψ : Torus.IsCk 2 ψ) :
    ∫ x, (d1_gen κ (d1_gradDrift U) ψ x + κ * ‖Torus.grad ψ x‖ ^ 2) *
      Real.exp (-(κ⁻¹ * U x) + ψ x) = 0 := by
  have hψ1 := mova_isCk_one_of_two hψ
  have hT : Torus.IsCk 1 (mova_tilt κ U ψ) := by
    have e : mova_tilt κ U ψ = fun y => U y + (-κ) * ψ y := by
      funext y; simp [mova_tilt]; ring
    rw [e]; exact mova_isCk_add hU (mova_isCk_const_mul _ hψ1)
  have h := mova_ibp hκ hT hψ
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  · unfold d1_gen d1_gradDrift
    rw [mova_grad_tilt hU hψ x]
    simp only [inner_neg_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  · unfold d1_gibbsWeight mova_tilt
    congr 1
    field_simp
    ring

end HRS

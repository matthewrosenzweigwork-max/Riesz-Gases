import HRS.MC.D3EWAux1

/-!
# Packet D3EW, helper 2: smoothness/support of `φ = ψ * ψ`, scaling of derivatives, the representation of `w_λ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EW

open HRS HRS.MC.FDLE

variable {d : ℕ}

lemma d3ew_phi_smooth {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : ContDiff ℝ ∞ (fdlPhi ψ) := by
  unfold fdlPhi
  exact HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (fdle_psi_compact hψ) (fdle_psi_cont hψ).locallyIntegrable hψ.smooth

lemma d3ew_phi_tsupport {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    tsupport (fdlPhi ψ) ⊆ Metric.closedBall (0 : Euc d) 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Function.mem_support] at hx
  by_contra h
  apply hx
  apply fdle_phi_eq_zero hψ
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at h
  exact h.le

lemma d3ew_phi_compact {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : HasCompactSupport (fdlPhi ψ) :=
  (isCompact_closedBall (0 : Euc d) 1).of_isClosed_subset (isClosed_tsupport _)
    (d3ew_phi_tsupport hψ)

lemma d3ew_dphi_bound {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ k (fdlPhi ψ) x‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := (d3ew_phi_compact hψ).exists_bound_iteratedFDeriv (d3ew_phi_smooth hψ) k
  exact ⟨M, hM0, fun x => hM k le_rfl x⟩

lemma d3ew_dphi_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (k : ℕ) {x : Euc d} (hx : 1 < ‖x‖) :
    iteratedFDeriv ℝ k (fdlPhi ψ) x = 0 := by
  by_contra h
  have h1 : x ∈ Function.support (iteratedFDeriv ℝ k (fdlPhi ψ)) := h
  have h2 := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := fdlPhi ψ) k h1
  have h3 := d3ew_phi_tsupport hψ (subset_tsupport _ h1 |> fun _ => h2)
  simp only [Metric.mem_closedBall, dist_zero_right] at h3
  linarith

/-- Scaling of iterated derivatives. -/
lemma d3ew_scale_bound {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ)
    (z : Euc d) :
    ‖iteratedFDeriv ℝ k (fun z => c * φ (t⁻¹ • z)) z‖
      ≤ |c| * (t⁻¹) ^ k * ‖iteratedFDeriv ℝ k φ (t⁻¹ • z)‖ := by
  set g : Euc d →L[ℝ] Euc d := t⁻¹ • ContinuousLinearMap.id ℝ (Euc d) with hg
  have hgz : ∀ y, g y = t⁻¹ • y := fun y => by simp [hg]
  have hcd : ContDiff ℝ ∞ (φ ∘ g) := hφ.comp g.contDiff
  have h1 : (fun z => c * φ (t⁻¹ • z)) = fun z => c • (φ ∘ g) z := by
    funext y; simp [hgz, smul_eq_mul]
  rw [h1, iteratedFDeriv_const_smul_apply' (hcd.of_le (by exact_mod_cast le_top)).contDiffAt,
    ContinuousLinearMap.iteratedFDeriv_comp_right g hφ z (by exact_mod_cast le_top)]
  rw [norm_smul, Real.norm_eq_abs, mul_assoc]
  gcongr
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [hgz]
  have hgn : ‖g‖ ≤ t⁻¹ := by
    rw [hg]
    refine (norm_smul_le t⁻¹ (ContinuousLinearMap.id ℝ (Euc d))).trans ?_
    rw [Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 ht.le) ContinuousLinearMap.norm_id_le
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]
  gcongr

/-- Integrand identity. -/
lemma d3ew_integrand (ψ : Euc d → ℝ) (s : ℝ) {t : ℝ} (ht : 0 < t) (z : Euc d) :
    t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t = t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z) := by
  unfold fdlPhiScale
  have h1 : t ^ ((d : ℝ) - s) = t ^ (d : ℝ) * t ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add ht]
  have h2 : t ^ (-s - 1) = t ^ (-s) * t⁻¹ := by
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_neg_one]
  rw [h1, h2, Real.rpow_natCast]
  have : t ^ d ≠ 0 := (pow_pos ht d).ne'
  field_simp

lemma d3ew_rep {ψ : Euc d → ℝ} (s b lam : ℝ) (z : Euc d) :
    fdlWE ψ s b lam z = ∫ t in Ioc 0 lam, b * t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • z) := by
  unfold fdlWE
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  show b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t) = _
  rw [d3ew_integrand ψ s ht.1, mul_assoc]

/-- Localisation: for `a ≤ ‖w‖`, `a ≥ 0`, only the scales in `(a, λ]` contribute. -/
lemma d3ew_rep_loc {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b lam : ℝ) {a : ℝ} (ha : 0 ≤ a)
    {w : Euc d} (hw : a ≤ ‖w‖) :
    fdlWE ψ s b lam w = ∫ t in Ioc a lam, b * t ^ (-s - 1) * fdlPhi ψ (t⁻¹ • w) := by
  rw [d3ew_rep]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc ?_ ?_
  · exact Ioc_subset_Ioc_left ha
  · intro t ht
    obtain ⟨⟨ht0, htl⟩, hn⟩ := ht
    have hta : t ≤ a := by
      by_contra h
      exact hn ⟨not_le.1 h, htl⟩
    have h1 : 1 ≤ ‖t⁻¹ • w‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), ← div_eq_inv_mul, le_div_iff₀ ht0]
      linarith
    simp [fdle_phi_eq_zero hψ h1]

end HRS.MC.D3EW

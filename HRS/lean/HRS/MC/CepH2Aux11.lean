import HRS.MC.CepH2Aux10

/-!
# CEPH2, helper 11: integration by parts against the kernel

For `φ ∈ C¹`, periodic, transversally compactly supported, and a fixed `y`:
`∫_cell (∂_w φ) Ĝ(x - y) + φ ∂_w Ĝ(x - y) dx = 0` and the same with `Ĝ` replaced by `∂_e Ĝ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_contDiff_per1 {v : ℝ} (hv : 0 < v) : ContDiff ℝ 1 (h2_per1 (N := N) v) := by
  have := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0) (f := h2_per1 (N := N) v)).2
    ⟨h2_per2 v, contDiff_zero.2 (h2_continuous_per2 hv), h2_hasFDerivAt_per1 hv⟩
  simpa using this

theorem h2_hasFDerivAt_per_sub {v : ℝ} (hv : 0 < v) (y x : Ch N) :
    HasFDerivAt (fun x => h2_per v (x - y)) (h2_per1 v (x - y)) x := by
  have h1 : HasFDerivAt (fun x : Ch N => x - y) (ContinuousLinearMap.id ℝ (Ch N)) x :=
    (hasFDerivAt_id x).sub_const y
  have h := (h2_hasFDerivAt_per hv (x - y)).comp x h1
  rw [ContinuousLinearMap.comp_id] at h
  exact h

theorem h2_hasFDerivAt_per1_sub {v : ℝ} (hv : 0 < v) (y x : Ch N) :
    HasFDerivAt (fun x => h2_per1 v (x - y)) (h2_per2 v (x - y)) x := by
  have h1 : HasFDerivAt (fun x : Ch N => x - y) (ContinuousLinearMap.id ℝ (Ch N)) x :=
    (hasFDerivAt_id x).sub_const y
  have h := (h2_hasFDerivAt_per1 hv (x - y)).comp x h1
  rw [ContinuousLinearMap.comp_id] at h
  exact h

theorem h2_per_sub_periodic (v : ℝ) (y x : Ch N) : h2_per v (x + cep_diag N - y) = h2_per v (x - y) := by
  rw [add_sub_right_comm]; exact h2_per_periodic v _

theorem h2_per1_sub_periodic (v : ℝ) (y x : Ch N) : h2_per1 v (x + cep_diag N - y) = h2_per1 v (x - y) := by
  rw [add_sub_right_comm]; exact h2_per1_periodic v _

theorem h2_kernel_ibp1 {v : ℝ} (hv : 0 < v) {φ : Ch N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (x + cep_diag N) = φ x) {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) (y w : Ch N) :
    ∫ x in cep_cell N, (fderiv ℝ φ x w * h2_per v (x - y) + φ x * h2_per1 v (x - y) w) = 0 := by
  have hF : ContDiff ℝ 1 (fun x => φ x * h2_per v (x - y)) :=
    hφ.mul (((h2_contDiff_per hv).of_le (by norm_num)).comp (contDiff_id.sub contDiff_const))
  have hperF : ∀ x, (fun x => φ x * h2_per v (x - y)) (x + cep_diag N) = (fun x => φ x * h2_per v (x - y)) x := by
    intro x; simp only [hper, h2_per_sub_periodic]
  have := h2_ibp_per hF hperF (R := R) (fun x hx => by simp [hR x hx]) w
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have h := (hφ.differentiable (by simp) x).hasFDerivAt.mul (h2_hasFDerivAt_per_sub hv y x)
  change HasFDerivAt (fun x => φ x * h2_per v (x - y)) _ x at h
  show _ = fderiv ℝ (fun x => φ x * h2_per v (x - y)) x w
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem h2_kernel_ibp2 {v : ℝ} (hv : 0 < v) {φ : Ch N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (x + cep_diag N) = φ x) {R : ℝ} (hR : ∀ x, R < ‖h2_perp x‖ → φ x = 0) (y w e : Ch N) :
    ∫ x in cep_cell N, (fderiv ℝ φ x w * h2_per1 v (x - y) e + φ x * h2_per2 v (x - y) w e) = 0 := by
  have hc : ContDiff ℝ 1 (fun x : Ch N => h2_per1 v (x - y) e) :=
    (ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp ((h2_contDiff_per1 hv).comp (contDiff_id.sub contDiff_const))
  have hF : ContDiff ℝ 1 (fun x => φ x * h2_per1 v (x - y) e) := hφ.mul hc
  have hperF : ∀ x, (fun x => φ x * h2_per1 v (x - y) e) (x + cep_diag N) =
      (fun x => φ x * h2_per1 v (x - y) e) x := by
    intro x; simp only [hper, h2_per1_sub_periodic]
  have := h2_ibp_per hF hperF (R := R) (fun x hx => by simp [hR x hx]) w
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have h2 : HasFDerivAt (fun x : Ch N => h2_per1 v (x - y) e) ((h2_per2 v (x - y)).flip e) x := by
    have := (h2_hasFDerivAt_per1_sub hv y x).clm_apply (hasFDerivAt_const e x)
    simpa using this
  have h := (hφ.differentiable (by simp) x).hasFDerivAt.mul h2
  change HasFDerivAt (fun x => φ x * h2_per1 v (x - y) e) _ x at h
  show _ = fderiv ℝ (fun x => φ x * h2_per1 v (x - y) e) x w
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply]
  ring

end HRS.MC.CepH2

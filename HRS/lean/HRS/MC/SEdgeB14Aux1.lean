import HRS.MC.SEdgeB12
import HRS.MC.SEdgeB13a
import HRS.MC.SEdgeB13b
import HRS.MC.SEdgeB13c
import HRS.MC.SEdgeB9cancel
import HRS.MC.SEdgeB11a
import HRS.MC.SEdgeB11b
import HRS.MC.SEdgeB15a
import HRS.MC.SEdgeB15b
import HRS.MC.SEdgeB15c
import HRS.MC.SEdgeB15d
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB4b

/-!
# Packet B14, helper 1: derivative bookkeeping for the second derivatives `g_ab = D^2 f(e_b, e_a)`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B14

open HRS.Sec7
open HRS.MC.SEdge

section Deriv

variable {p : ℕ}

/-- `d_a f` is `C_b^2` if `f` has bounded derivatives of orders `1..3`. -/
theorem b14_dpsi_memCb2 {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : sed_StBdd f 3) (a : Fin p) :
    MemCb 2 (fun z => fderiv ℝ f z (stdVec a)) := by
  obtain ⟨hf3, hfb⟩ := hf
  have hg2 : ContDiff ℝ 2 (fderiv ℝ f) := hf3.fderiv_right (m := 2) (by norm_num)
  refine ⟨hg2.clm_apply contDiff_const, fun j hj => ?_⟩
  obtain ⟨M, hM⟩ := hfb (j + 1) (by omega) (by omega)
  refine ⟨‖stdVec a‖ * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  refine (norm_iteratedFDeriv_clm_apply_const (hg2.contDiffAt) (N := 2) (n := j)
    (by exact_mod_cast hj)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)

/-- directional derivative lowers the `MemCb` order by one. -/
theorem b14_memCb_fderiv {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (h : MemCb 2 ψ)
    (u : EuclideanSpace ℝ (Fin p)) : MemCb 1 (fun z => fderiv ℝ ψ z u) := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ ψ) := h.1.fderiv_right (m := 1) (by norm_num)
  refine ⟨hg1.clm_apply contDiff_const, fun j hj => ?_⟩
  obtain ⟨M, hM⟩ := h.2 (j + 1) (by omega)
  refine ⟨‖u‖ * M, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : ‖iteratedFDeriv ℝ (j + 1) ψ x‖ ≤ M := hM ⟨x, rfl⟩
  refine (norm_iteratedFDeriv_clm_apply_const (hg1.contDiffAt) (N := 1) (n := j)
    (by exact_mod_cast hj)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

theorem b14_g_eq {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f) (a b : Fin p) :
    (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) =
      fun x => fderiv ℝ (fun z => fderiv ℝ f z (stdVec a)) x (stdVec b) :=
  funext fun x => (B12.b12_fderiv_psi hf a b x).symm

theorem b14_g_memCb {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : sed_StBdd f 3) (a b : Fin p) :
    MemCb 1 (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) := by
  rw [b14_g_eq hf.1 a b]
  exact b14_memCb_fderiv (b14_dpsi_memCb2 hf a) _

theorem b14_fderiv_g {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f) (a b c : Fin p)
    (z : EuclideanSpace ℝ (Fin p)) :
    fderiv ℝ (fun x => iteratedFDeriv ℝ 2 f x ![stdVec b, stdVec a]) z (stdVec c) =
      iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec c, stdVec b] := by
  rw [b14_g_eq hf a b]
  have hψ2 : ContDiff ℝ 2 (fun z => fderiv ℝ f z (stdVec a)) :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hc : ContDiff ℝ 1 (fderiv ℝ (fun z => fderiv ℝ f z (stdVec a))) :=
    hψ2.fderiv_right (m := 1) (by norm_num)
  rw [B13c.b13c_fderiv_apply hc]
  have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (fun z => fderiv ℝ f z (stdVec a)) z
    ![stdVec c, stdVec b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [← h2]
  simpa using B13c.b13c_shuffle hf z (stdVec a) (stdVec c) (stdVec b)

/-- the third derivative tensor is symmetric in the last two arguments. -/
theorem b14_T_symm {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f)
    (γ : Measure (EuclideanSpace ℝ (Fin p))) (a b c : Fin p) :
    ∫ z, iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec b, stdVec c] ∂γ =
      ∫ z, iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec c, stdVec b] ∂γ :=
  integral_congr_ae (Filter.Eventually.of_forall fun z =>
    (B15d.sed_B15d_d3_symm_proof hf z a b c).2)

end Deriv

section Smooth

variable {d : ℕ}

theorem b14_drift_smooth {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Torus.IsSmooth (sed_drift v φ) :=
  B13a.b13a_isSmooth_sum (Finset.univ : Finset (Fin d))
    (f := fun k x => v k x * Torus.partialDeriv k φ x)
    (fun k => B13a.b13a_isSmooth_mul (hv k) (HRS.LocalDivAux.isSmooth_partialDeriv hφ k))

end Smooth

end HRS.MC.SEdge.B14

end

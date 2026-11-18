/-
# HRS.Equilibrium.Q84dAuxR — packet Q84d: `configGrad`, `configLap` of `F_N(ψ)` in explicit form
-/
import HRS.Equilibrium.Q84dAuxQ

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_A_line_deriv {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (i : Fin N) (k : Fin d)
    (Y : Config d N) (hY : ∀ a b : Fin N, a ≠ b → Y a ≠ Y b) :
    HasDerivAt (fun τ : ℝ => Aik d ψ i k (lineCfg i k Y τ)) (Cik d ψ i k Y) 0 := by
  have hj : ∀ j ∈ Finset.univ.erase i, HasDerivAt
      (fun τ : ℝ => gK ψ k ((lineCfg i k Y τ) i) ((lineCfg i k Y τ) j)) (hK ψ k (Y i) (Y j)) 0 := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have := q84d_gK_line_deriv hsm (hY i j hji.symm) k
    have e : (fun τ : ℝ => gK ψ k ((lineCfg i k Y τ) i) ((lineCfg i k Y τ) j)) =
        fun τ => gK ψ k (Y i + Torus.mk (τ • ek k)) (Y j) := by
      funext τ; simp [lineCfg, Function.update_of_ne hji]
    rw [e]; exact this
  have hsum := HasDerivAt.fun_sum hj
  have := hsum.const_mul (2 * (N : ℝ) ^ (-(3 / 2 : ℝ)))
  unfold Aik Cik
  exact this

theorem q84d_configGrad_comp {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) (k : Fin d) :
    (configGrad (Fstat ψ) X i) k = Aik d ψ i k X := by
  set c : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hc
  have hφ : (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) =
      fun u => c * (2 * ∑ j ∈ Finset.univ.erase i, ψ (X i + Torus.mk u) (X j) + pairRestQ ψ i X) := by
    funext u
    unfold Fstat
    rw [q84d_pairSum_update ψ hsymm i X (X i + Torus.mk u)]
  have hj : ∀ j ∈ Finset.univ.erase i, HasFDerivAt (fun u : Euc d => ψ (X i + Torus.mk u) (X j))
      (fderiv ℝ (fun u : Euc d => ψ (X i + Torus.mk u) (X j)) 0) 0 := fun j hj =>
    ((q84d_slice_contDiffAt hsm (hX i j (Finset.ne_of_mem_erase hj).symm)).differentiableAt
      (by simp)).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum hj
  have h3 := ((hsum.const_mul 2).add_const (pairRestQ ψ i X)).const_mul c
  unfold configGrad gradient
  rw [hφ, q84d_toDual_symm_apply, h3.fderiv]
  simp only [smul_apply, sum_apply, smul_eq_mul]
  unfold Aik
  rw [← hc]
  have : ∀ j ∈ Finset.univ.erase i,
      (fderiv ℝ (fun u : Euc d => ψ (X i + Torus.mk u) (X j)) 0) (ek k) = gK ψ k (X i) (X j) := by
    intro j hj
    rw [q84d_slice_grad_comp (fun z => ψ z (X j)) (X i) k,
      q84d_grad_comp hsm (hX i j (Finset.ne_of_mem_erase hj).symm) k]
  rw [Finset.sum_congr rfl this]
  ring

theorem q84d_lap_sum {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) {x : Euc d}
    (hf : ∀ j ∈ S, ContDiffAt ℝ 2 (f j) x) :
    Laplacian.laplacian (fun u => ∑ j ∈ S, f j u) x = ∑ j ∈ S, Laplacian.laplacian (f j) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := congrFun (InnerProductSpace.laplacian_const (E := Euc d) (c := (0 : ℝ))) x
    simpa using this
  | insert a S ha ih =>
    have e : (fun u => ∑ j ∈ insert a S, f j u) = f a + (fun u => ∑ j ∈ S, f j u) := by
      funext u; simp [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ 2 (f a) x := hf a (Finset.mem_insert_self _ _)
    have h2 : ContDiffAt ℝ 2 (fun u => ∑ j ∈ S, f j u) x :=
      ContDiffAt.sum fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [e, ContDiffAt.laplacian_add h1 h2, ih fun j hj => hf j (Finset.mem_insert_of_mem hj),
      Finset.sum_insert ha]

theorem q84d_lap_affine_sum {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) {x : Euc d}
    (hf : ∀ j ∈ S, ContDiffAt ℝ 2 (f j) x) (c R : ℝ) :
    Laplacian.laplacian (fun u => c * (2 * ∑ j ∈ S, f j u + R)) x =
      c * (2 * ∑ j ∈ S, Laplacian.laplacian (f j) x) := by
  have hS : ContDiffAt ℝ 2 (fun u => ∑ j ∈ S, f j u) x := ContDiffAt.sum hf
  have e : (fun u => c * (2 * ∑ j ∈ S, f j u + R)) =
      c • (((2 : ℝ) • (fun u => ∑ j ∈ S, f j u)) + fun _ => R) := by
    funext u; simp
  have hS2 : ContDiffAt ℝ 2 ((2 : ℝ) • (fun u => ∑ j ∈ S, f j u)) x := hS.const_smul (2 : ℝ)
  have hG : ContDiffAt ℝ 2 (((2 : ℝ) • (fun u => ∑ j ∈ S, f j u)) + fun _ => R) x :=
    hS2.add contDiffAt_const
  rw [e, InnerProductSpace.laplacian_smul c hG, ContDiffAt.laplacian_add hS2
    contDiffAt_const, InnerProductSpace.laplacian_smul (2 : ℝ) hS,
    congrFun (InnerProductSpace.laplacian_const (E := Euc d) (c := R)) x,
    q84d_lap_sum S f hf]
  simp

theorem q84d_configLap_eq {ψ : Torus d → Torus d → ℝ} (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) :
    configLap (Fstat ψ) X i = ∑ k, Cik d ψ i k X := by
  set c : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hc
  have hφ : (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) =
      fun u => c * (2 * ∑ j ∈ Finset.univ.erase i, ψ (X i + Torus.mk u) (X j) + pairRestQ ψ i X) := by
    funext u
    unfold Fstat
    rw [q84d_pairSum_update ψ hsymm i X (X i + Torus.mk u)]
  have hcd : ∀ j ∈ Finset.univ.erase i,
      ContDiffAt ℝ 2 (fun u : Euc d => ψ (X i + Torus.mk u) (X j)) 0 := fun j hj =>
    (q84d_slice_contDiffAt hsm (hX i j (Finset.ne_of_mem_erase hj).symm)).of_le (by norm_cast)
  unfold configLap
  rw [hφ, q84d_lap_affine_sum _ _ hcd]
  unfold Cik
  rw [← hc]
  have : ∀ j ∈ Finset.univ.erase i,
      Laplacian.laplacian (fun u : Euc d => ψ (X i + Torus.mk u) (X j)) 0 = ∑ k, hK ψ k (X i) (X j) := by
    intro j hj
    rw [q84d_slice_lap (fun z => ψ z (X j)) (X i)]
    exact q84d_lap_comp hsm (hX i j (Finset.ne_of_mem_erase hj).symm)
  rw [Finset.sum_congr rfl this]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end HRS.Q84d

end

import HRS.Uniform.Q54cAux22

/-!
# Q54c, part 23: the `PathData` of an adjoint propagator, and its algebraic/bound fields
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

/-- the path data of the adjoint propagator `(D, μ)` -/
def pd (P : PdeSetup d) (D : DynData d) (μ : ℝ → Torus d → ℝ) : PathData d (P.n : ℝ) where
  y := fun t φ σ => (Sv (P.n : ℝ) (P.flow D μ t φ (t - σ))).2
  y' := fun t φ σ => -(Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2
  w := fun t φ => (Sv ((P.n : ℝ) + 2) (P.flow D μ t φ t)).2

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

theorem hn1 : 1 ≤ P.n := by
  have h1 := P.hnd
  have h2 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have : (0 : ℝ) < P.n := by linarith
  exact_mod_cast this

theorem lev_ge_n2 : ((P.n : ℝ) + 2) ≤ P.lev := by
  have : ((P.n + 2 : ℕ) : ℝ) ≤ ((P.n + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : P.n + 2 ≤ P.n + 4)
  push_cast at this ⊢
  linarith

include h

theorem Data.lin_y {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (α β : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    (P.pd D μ).y t (fun x => α * φ x + β * ψ x) σ =
      α • (P.pd D μ).y t φ σ + β • (P.pd D μ).y t ψ σ := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have a1 := h.flow_adm0 ht hφ hτ (j := (P.n : ℝ)) (by
    have := lev_ge_n2 (P := P); linarith)
  have a2 := h.flow_adm0 ht hψ hτ (j := (P.n : ℝ)) (by
    have := lev_ge_n2 (P := P); linarith)
  show (Sv (P.n : ℝ) (P.flow D μ t (fun x => α * φ x + β * ψ x) (t - σ))).2 =
    α • (Sv (P.n : ℝ) (P.flow D μ t φ (t - σ))).2 + β • (Sv (P.n : ℝ) (P.flow D μ t ψ (t - σ))).2
  rw [h.flow_comb ht hφ hψ α β hτ, Sv_comb a1 a2 α β]
  rfl

theorem Data.lin_y' {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (α β : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    (P.pd D μ).y' t (fun x => α * φ x + β * ψ x) σ =
      α • (P.pd D μ).y' t φ σ + β • (P.pd D μ).y' t ψ σ := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have a1 := h.gen_adm0 ht hφ hτ (j := P.n) (by omega) P.hnd
  have a2 := h.gen_adm0 ht hψ hτ (j := P.n) (by omega) P.hnd
  show -(Sv (P.n : ℝ) (P.gen D μ t (fun x => α * φ x + β * ψ x) (t - σ))).2 =
    α • -(Sv (P.n : ℝ) (P.gen D μ t φ (t - σ))).2 + β • -(Sv (P.n : ℝ) (P.gen D μ t ψ (t - σ))).2
  rw [h.gen_comb ht hφ hψ α β hτ, Sv_comb a1 a2 α β]
  simp [smul_neg]
  abel

theorem Data.lin_w {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    (P.pd D μ).w t (fun x => α * φ x + β * ψ x) =
      α • (P.pd D μ).w t φ + β • (P.pd D μ).w t ψ := by
  have hτ : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
  have a1 := h.flow_adm0 ht hφ hτ (j := (P.n : ℝ) + 2) lev_ge_n2
  have a2 := h.flow_adm0 ht hψ hτ (j := (P.n : ℝ) + 2) lev_ge_n2
  show (Sv ((P.n : ℝ) + 2) (P.flow D μ t (fun x => α * φ x + β * ψ x) t)).2 =
    α • (Sv ((P.n : ℝ) + 2) (P.flow D μ t φ t)).2 + β • (Sv ((P.n : ℝ) + 2) (P.flow D μ t ψ t)).2
  rw [h.flow_comb ht hφ hψ α β hτ, Sv_comb a1 a2 α β]
  rfl

theorem Data.sv_const (c : ℝ) (j : ℝ) : (Sv j (coeffOf (fun _ : Torus d => c))).2 = 0 := by
  show lpFun j (toFun (coeffOf (fun _ : Torus d => c))) = 0
  rw [toFun_coeffOf_const]
  exact lpFun_const j c

theorem Data.const_y {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) (c : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    (P.pd D μ).y t (fun _ => c) σ = 0 := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  show (Sv (P.n : ℝ) (P.flow D μ t (fun _ => c) (t - σ))).2 = 0
  rw [h.flow_const ht c hτ]
  exact Data.sv_const h c _

theorem Data.const_y' {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) (c : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    (P.pd D μ).y' t (fun _ => c) σ = 0 := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  show -(Sv (P.n : ℝ) (P.gen D μ t (fun _ => c) (t - σ))).2 = 0
  rw [h.gen_const ht c hτ]
  show -(((0 : Coeff d) 0).re, lpFun (P.n : ℝ) (toFun (0 : Coeff d))).2 = 0
  have : toFun (0 : Coeff d) = fun _ : Torus d => (0 : ℝ) := by
    funext x; simp [toFun, series]
  rw [this, lpFun_const]
  simp

theorem Data.const_w {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) (c : ℝ) :
    (P.pd D μ).w t (fun _ => c) = 0 := by
  have hτ : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
  show (Sv ((P.n : ℝ) + 2) (P.flow D μ t (fun _ => c) t)).2 = 0
  rw [h.flow_const ht c hτ]
  exact Data.sv_const h c _

theorem Data.w_zero {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (z : NegSobolev d ((P.n : ℝ) + 2)) :
    inner ℝ z ((P.pd D μ).w 0 φ) = NegSobolev.eval z φ := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have hA := coeffOf_adm hD (j := P.lev) le_rfl
  show inner ℝ z (Sv ((P.n : ℝ) + 2) (P.flow D μ 0 φ 0)).2 = _
  rw [h.flow_zero hφ]
  show inner ℝ z (lpFun ((P.n : ℝ) + 2) (toFun (coeffOf φ))) = _
  rw [HRS.PDE.toFun_coeffOf φ hD.1 hA.2.1]
  exact (eval_lpFun z (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ _)).symm

end PdeSetup

end HRS.Uniform.Q54c

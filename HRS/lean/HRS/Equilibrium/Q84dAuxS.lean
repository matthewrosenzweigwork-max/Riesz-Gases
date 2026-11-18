/-
# HRS.Equilibrium.Q84dAuxS — packet Q84d: the flux field `q ∂_{ik}F` and its divergence
-/
import HRS.Equilibrium.Q84dAuxR

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The unnormalised Gibbs density `q = exp(-βH)`. -/
def qd (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X)

/-- The flux component `u_{ik} = q ∂_{ik}F`. -/
def uik (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ψ : Torus d → Torus d → ℝ) {N : ℕ}
    (i : Fin N) (k : Fin d) (X : Config d N) : ℝ :=
  qd d s V β X * Aik d ψ i k X

/-- The divergence component `v_{ik} = q (∂²_{ik}F - β ∂_{ik}H ∂_{ik}F)`. -/
def vik (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ψ : Torus d → Torus d → ℝ) {N : ℕ}
    (i : Fin N) (k : Fin d) (X : Config d N) : ℝ :=
  qd d s V β X * (Cik d ψ i k X - β * (Bik d s V i k X * Aik d ψ i k X))

theorem q84d_u_line_deriv_base (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ}
    (hV : Torus.IsSmooth V) {β : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (i : Fin N) (k : Fin d)
    (Y : Config d N) (hY : ∀ a b : Fin N, a ≠ b → Y a ≠ Y b) :
    HasDerivAt (fun τ : ℝ => uik d s V β ψ i k (lineCfg i k Y τ)) (vik d s V β ψ i k Y) 0 := by
  have hH := q84d_H_line_deriv hd hcrit hV Y hY i k
  have hq : HasDerivAt (fun τ : ℝ => qd d s V β (lineCfg i k Y τ))
      (qd d s V β Y * (-β * Bik d s V i k Y)) 0 := by
    have := (hH.const_mul (-β)).exp
    simp only [lineCfg_zero] at this
    exact this
  have hA := q84d_A_line_deriv hsm i k Y hY
  have := hq.mul hA
  simp only [lineCfg_zero] at this
  unfold uik vik
  convert this using 1
  ring

theorem q84d_u_line_deriv (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ}
    (hV : Torus.IsSmooth V) {β : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (i : Fin N) (k : Fin d)
    (Y : Config d N) (hY : ∀ t : ℝ, lineCfg i k Y t ∉ collisionSet d N) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => uik d s V β ψ i k (lineCfg i k Y τ)) (vik d s V β ψ i k (lineCfg i k Y t)) t := by
  have hfree : ∀ a b : Fin N, a ≠ b → (lineCfg i k Y t) a ≠ (lineCfg i k Y t) b := by
    intro a b hab hX
    exact hY t ⟨a, b, hab, hX⟩
  have h0 := q84d_u_line_deriv_base hd hcrit hV (β := β) hsm i k (lineCfg i k Y t) hfree
  have e : (fun τ : ℝ => uik d s V β ψ i k (lineCfg i k (lineCfg i k Y t) τ)) =
      fun τ => uik d s V β ψ i k (lineCfg i k Y (t + τ)) := by
    funext τ; rw [lineCfg_add]
  rw [e] at h0
  have h1 : HasDerivAt (fun σ : ℝ => uik d s V β ψ i k (lineCfg i k Y (t + σ)))
      (vik d s V β ψ i k (lineCfg i k Y t)) (t - t) := by rw [sub_self]; exact h0
  have h2 := h1.comp_sub_const t t
  have e2 : (fun x : ℝ => uik d s V β ψ i k (lineCfg i k Y (t + (x - t)))) =
      fun x => uik d s V β ψ i k (lineCfg i k Y x) := by
    funext x; rw [add_sub_cancel]
  rw [e2] at h2
  exact h2

end HRS.Q84d

end

/-
# HRS.Equilibrium.Q84bAuxE — packet Q84b: the force `F_μ` and the formula `Jop f = F·∇f + R f`
-/
import HRS.Equilibrium.Q84bAuxD

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

/-- `F_μ = ∇g ⋆ ρ` in the cancellation convention. -/
theorem q84b_force_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {V ρ : Torus d → ℝ} (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) (a : Torus d) :
    forceField d s ρ a = convGradConv (periodicRieszGrad d s) ρ a := by
  have hρ1 : Torus.IsCk 1 ρ := Q84a.q84a_contDiff_one hρs.smooth
  have hV1 : Torus.IsCk 1 V := Q84a.q84a_contDiff_one hV
  have hφ : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ) :=
    (HRS.PDE.MFAux.gibbs_partialDeriv V ρ (convFun (periodicRiesz d s) ρ) β hβ.ne'
      (∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y))) hρ1 hV1 hρs.pos hρ.2).1
  ext j
  rw [HRS.PDE.MFAux.convGradConv_eq_partialDeriv hd s hs0 hsd hρ1 hφ j a]
  unfold forceField
  rw [Q84a.q84a_conv_eq hρs, HRS.PDE.MFAux.grad_apply]

/-- The integrand of the remainder in `Jop f = F·∇f + ∫ ρ(a-u) ∇g(u)·(∇f(a-u) - ∇f(a)) du`. -/
def q84b_Rk (ρ : Torus d → ℝ) (s : ℝ) (f : Torus d → ℝ) (a u : Torus d) : ℝ :=
  ρ (a - u) * inner ℝ (periodicRieszGrad d s u) (Torus.grad f (a - u) - Torus.grad f a)

theorem q84b_Jop_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {V ρ : Torus d → ℝ} (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    {f : Torus d → ℝ} {a b : Torus d} (hab : a ≠ b)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) {u : Euc d | Torus.mk u ≠ b})
    (hint : Integrable (fun z => ‖Torus.grad f z‖)) :
    Integrable (q84b_Rk ρ s f a) ∧
    Jop d s ρ f a = inner ℝ (forceField d s ρ a) (Torus.grad f a) + ∫ u, q84b_Rk ρ s f a u := by
  have hρ1 : Torus.IsCk 1 ρ := Q84a.q84a_contDiff_one hρs.smooth
  obtain ⟨Cg, hGood⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  obtain ⟨hI, hJ⟩ := q84b_Jop_local hd hs0 hsd hρ1 hab hsm hint
  obtain ⟨B, hB0, hB⟩ := HRS.KernelGrad.isCk_bounded hρ1
  obtain ⟨L, hL0, hL⟩ := HRS.KernelGrad.isLipschitz_of_isCk hρ1
  have hK : Integrable (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a) :=
    HRS.KernelGrad.integrable_kern hGood (HRS.PDE.MFAux.continuous_of_isCk hρ1).measurable hB hL hL0 hB0 a
  have hKi : Integrable (fun u => inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a u)
      (Torus.grad f a)) := hK.inner_const _
  have hpt : ∀ u, q84b_pvU (periodicRieszGrad d s) (fun y => ρ y • Torus.grad f y) a u =
      inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a u) (Torus.grad f a) +
        q84b_Rk ρ s f a u := by
    intro u
    unfold q84b_pvU q84b_Rk HRS.KernelGrad.kern
    split_ifs with h
    · simp only [inner_sub_right, real_inner_smul_right, real_inner_smul_left]
      ring
    · simp only [inner_sub_right, real_inner_smul_right, real_inner_smul_left]
      ring
  have hR : Integrable (q84b_Rk ρ s f a) := by
    have := hI.sub hKi
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply]
    rw [hpt u]; ring
  refine ⟨hR, ?_⟩
  rw [hJ]
  simp_rw [hpt]
  have hKint : ∫ u, inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a u) (Torus.grad f a) =
      inner ℝ (forceField d s ρ a) (Torus.grad f a) := by
    calc ∫ u, inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a u) (Torus.grad f a)
        = ∫ u, inner ℝ (Torus.grad f a) (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a u) :=
          integral_congr_ae (Eventually.of_forall fun u => real_inner_comm _ _)
      _ = inner ℝ (Torus.grad f a) (∫ u, HRS.KernelGrad.kern (periodicRieszGrad d s) ρ a u) :=
          integral_inner hK _
      _ = inner ℝ (forceField d s ρ a) (Torus.grad f a) := by
          rw [← HRS.KernelGrad.convGradConv_eq_integral_kern,
            ← q84b_force_eq hd hs0 hsd hβ hV hρ hρs a, real_inner_comm]
  rw [integral_add hKi hR, hKint]

end HRS.Q84b

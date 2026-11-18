import HRS.Sections.AdjKCAux1

/-!
# ADJKC Aux2: packet C2 (interval integrability and joint measurability of the forcing)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjKC

variable {d N : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- Joint continuity of the clamped gradient of a classical adjoint solution on `ℝ × 𝕋^d`. -/
theorem adjkc_grad_clamp_continuous {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    Continuous fun p : ℝ × Torus d => Torus.grad (f (clampTI t p.1)) p.2 := by
  have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) (Torus.mk : Euc d → Torus d)) :=
    IsOpenQuotientMap.prodMap IsOpenQuotientMap.id KernelGrad.isOpenQuotientMap_mk
  rw [hq.isQuotientMap.continuous_iff]
  have : ((fun p : ℝ × Torus d => Torus.grad (f (clampTI t p.1)) p.2) ∘
      Prod.map (id : ℝ → ℝ) (Torus.mk : Euc d → Torus d)) =
      fun p : ℝ × Euc d => gradient (Torus.lift (f (clampTI t p.1))) p.2 := by
    funext p
    simp only [Function.comp, Prod.map]
    exact Torus.grad_mk _ (PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
      (hf.c2 _ (clampTI_mem ht p.1))) p.2
  rw [this]
  exact continuous_gradient_clamp ht hf

theorem adjkc_rho_clamp_continuous {t : ℝ} (ht : 0 ≤ t)
    (hρJ : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ)) :
    Continuous fun q : ℝ × Torus d => ρ (clampTI t q.1) q.2 := by
  have hq : Continuous fun q : ℝ × Torus d => (clampTI t q.1, q.2) :=
    ((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  exact ContinuousOn.comp_continuous hρJ hq (fun q => ⟨clampTI_mem ht q.1, Set.mem_univ _⟩)

/-- Pathwise continuity of the forcing integrand on `[0,t]` along a continuous collision-free path. -/
theorem adjkc_forcing_continuousOn (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {t : ℝ} (ht : 0 ≤ t) {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution htr.dyn ρ t φ F) {Xp : ℝ≥0 → Config d N}
    (hXc : ∀ i, Continuous fun u : ℝ≥0 => Xp u i)
    (hcol : ∀ u : ℝ≥0, (u : ℝ) ≤ t → Xp u ∉ collisionSet d N) :
    ContinuousOn (fun r : ℝ => modulatedEnergy
      (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (F r))) (Xp r.toNNReal)
      (withDensityReal (ρ r))) (Set.Icc 0 t) := by
  have hd1 : 1 ≤ d := by omega
  have hF12 := hF.isC12Test
  obtain ⟨c₀, hc₀, Λ₁, hΛ₁⟩ := Q40b.q40b_rho_bounds hd1 htr
  have hρJ := Q40b.q40b_jointCont hd1 htr t
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hρJ
  obtain ⟨M, hM⟩ := Q40b.q40b_unif_D2 hF
  have hLip : ∀ r : ℝ, IsLipschitzVF (max M 0) (Torus.grad (F (clampTI t r))) := fun r =>
    Q40b.q40b_grad_lip (hF.c2 _ (clampTI_mem ht r))
      (fun y => (hM _ (clampTI_mem ht r) y).trans (le_max_left _ _))
  have hcl := adjkc_modEnergy_continuous (N := N) (s := htr.dyn.s) hd htr.dyn.hs0 htr.dyn.hsd
    (Gf := fun r x => Torus.grad (F (clampTI t r)) x)
    (adjkc_grad_clamp_continuous ht hF12) (le_max_right M 0) hLip
    (ρt := fun r x => ρ (clampTI t r) x) (adjkc_rho_clamp_continuous ht hρJ)
    (Λ := Λ) (fun r y => by
      have := hΛ (clampTI t r, y) ⟨clampTI_mem ht r, Set.mem_univ _⟩
      simpa using this)
    (fun r => (hΛ₁ _ (clampTI_mem ht r).1).1)
    (Xc := fun r => Xp (clampTI t r).toNNReal)
    (continuous_pi fun i => (hXc i).comp (continuous_real_toNNReal.comp (continuous_clampTI t)))
    (fun r i j hij h => hcol _ (by rw [Real.coe_toNNReal _ (clampTI_mem ht r).1]; exact (clampTI_mem ht r).2)
      ⟨i, j, hij, h⟩)
  refine hcl.continuousOn.congr fun r hr => ?_
  simp only [clampTI_of_mem hr]

end HRS.AdjKC

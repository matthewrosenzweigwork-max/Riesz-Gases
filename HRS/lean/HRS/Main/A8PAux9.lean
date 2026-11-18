import HRS.Main.A8PAux8

/-!
# Packet A8P, part 9: the pathwise bound of the remainder `σ ∫_0^t flucInteraction`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_flucInteraction_zero {D : DynData d} (hM : D.M = 0) {N : ℕ} (ψ : Torus d → ℝ)
    (x : Fin N → Torus d) (ρ : Torus d → ℝ) : flucInteraction D ψ x ρ = 0 := by
  have h : ∀ ν ν' : Measure (Torus d), interactionPairing D ψ ν ν' = 0 := by
    intro ν ν'
    unfold interactionPairing
    simp [hM, Torus.matVec]
  unfold flucInteraction
  rw [h, h, h, h]; ring

section Rem

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The a.s. pathwise bound of the remainder integral. -/
theorem a8p_rem_ae (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) :
    ∀ᵐ ω ∂(R N).P,
      |∫ r in (0 : ℝ)..t, flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r)| ≤
        (1 / 2) * (Cq * (cT * a8pK Λ₁ t φ)) * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hCk, hcl, hb⟩ := a8p_adj_pkg hspec hCa hS hN1 ht hφc hφ
  obtain ⟨hXc, hocc, -⟩ := a8p_flow_facts hS hN1
  obtain ⟨hint, -, -⟩ := a8p_energy_integral hS hN1 (C₀ := C₀) (Λ := Λ) hF.progressive
  have hΛ := a8p_Lam_ge_one hS
  have hcom' := hcom.mono hC hCq
  have hK0 := a8pK_nonneg Λ₁ t φ
  have hcoef0 : 0 ≤ (1 / 2 : ℝ) * (Cq * (cT * a8pK Λ₁ t φ)) :=
    mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0))
  have hT0 : 0 ≤ S.T := S.hT.le
  have hten : ∀ᵐ ω ∂(R N).P, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω :=
    Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Icc fun r _ => a8pEn_nonneg S R N C₀ Λ r ω
  rcases hocc with hM0 | hocc
  · -- `M = 0`: the remainder vanishes
    filter_upwards [hten] with ω hω
    have : ∀ r, flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
        ((R N).X (Real.toNNReal r) ω) (S.ρ N r) = 0 := fun r => a8p_flucInteraction_zero hM0 _ _ _
    simp only [this, intervalIntegral.integral_zero, abs_zero]
    exact mul_nonneg hcoef0 hω
  · filter_upwards [hocc, hint] with ω hω hωi
    have hnull : ∀ᵐ r ∂(volume : Measure ℝ), ¬ (r ∈ Set.Icc 0 S.T ∧ (R N).X (Real.toNNReal r) ω ∈ collisionSet d N) :=
      measure_eq_zero_iff_ae_notMem.1 hω
    have hrest : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        ‖flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r)‖ ≤
        (1 / 2) * (Cq * (cT * a8pK Λ₁ t φ)) * a8pEn S R N C₀ Λ r ω := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards [hnull] with r hr hrmem
      have hrt : r ∈ Set.Icc (0 : ℝ) t := ⟨hrmem.1.le, hrmem.2⟩
      have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hrmem.1.le, hrmem.2.trans ht.2⟩
      have hcoll : (R N).X (Real.toNNReal r) ω ∉ collisionSet d N := fun h => hr ⟨hrT, h⟩
      obtain ⟨hmem, hnorm, -⟩ := hb r hrt
      have hCk2 : Torus.IsCk 2 (propagator (S.dyn N) (S.ρ N) r t φ) := hcl.c2 r hrt
      have hTB := hcT (S.dyn N).M hS.matrix_bound _ hCk2 hmem
      have hTB' : HasTransportBound d S.s (gfb2_v (S.dyn N).M (propagator (S.dyn N) (S.ρ N) r t φ))
          (cT * a8pK Λ₁ t φ) := by
        obtain ⟨L, F, hL, hF0, hlip, hfrac, hLK⟩ := hTB
        refine ⟨L, F, hL, hF0, hlip, hfrac, hLK.trans ?_⟩
        exact mul_le_mul_of_nonneg_left hnorm hcT0
      have hdens := (hS.mean_field.solution N hN1).density r hrT
      have hpt := a8p_rem_pointwise S.hd S.hs0 S.hsd hcom' hCq hΛ hN (D := S.dyn N) rfl hdens
        (fun x => a8p_rho_le hS hN1 hrT x) hCk2 hTB' _ hcoll
      rw [Real.norm_eq_abs]
      refine hpt.trans ?_
      have hge := a8pEn_ge S R N C₀ Λ r ω
      unfold correctedEnergy at hge
      exact mul_le_mul_of_nonneg_left hge (mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0)))
    have hIoc : IntegrableOn (fun r => a8pEn S R N C₀ Λ r ω) (Set.Ioc (0 : ℝ) t) :=
      hωi.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))
    rw [intervalIntegral.integral_of_le ht.1, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hIoc.const_mul _) hrest).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hcoef0
    refine setIntegral_mono_set hωi (Eventually.of_forall fun r => a8pEn_nonneg S R N C₀ Λ r ω) ?_
    exact Eventually.of_forall fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩

end Rem

end HRS.Main.A8P

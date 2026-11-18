import HRS.Uniform.Q54cAux20

/-!
# Q54c, part 21: constants, linearity of the generator path, norm bounds for `t ∈ [0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem sobolevNorm_mono_idx {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {a b : ℝ} (hab : a ≤ b) :
    sobolevNorm a φ ≤ sobolevNorm b φ := by
  have ha := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ a
  have hb := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ b
  rw [HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm ha, HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm hb]
  exact hsNorm_mono_q hab (hsNormSq_coeffOf b φ hb).1

theorem sobolevNorm_nonneg' (a : ℝ) (φ : Torus d → ℝ) : 0 ≤ sobolevNorm a φ := Real.sqrt_nonneg _

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.flow_const {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) (c : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    P.flow D μ t (fun _ => c) τ = coeffOf (fun _ => c) := by
  have hs := HRS.Uniform.Q54.isSmooth_const' (d := d) c
  by_cases h0 : t = 0
  · subst h0
    have : τ = 0 := le_antisymm hτ.2 hτ.1
    subst this
    exact h.flow_zero hs
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    have hu : t - τ ∈ Set.Icc 0 t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    obtain ⟨-, h2, -⟩ := h.U_facts ht hs hu
    rw [sub_sub_cancel] at h2
    rw [← h2, HRS.Uniform.Q54.prop_const P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀ P.T μ
      h.hA ht' c hu]

theorem Data.gen_const {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) (c : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    P.gen D μ t (fun _ => c) τ = 0 := by
  unfold PdeSetup.gen
  rw [h.flow_const ht c hτ, coeffOf_const_eq]
  exact HRS.PDE.MFAdjoint.forwardGen_smul_delta D _ _

theorem Data.gen_comb {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (α β : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    P.gen D μ t (fun x => α * φ x + β * ψ x) τ =
      fun k => (α : ℂ) * P.gen D μ t φ τ k + (β : ℂ) * P.gen D μ t ψ τ k := by
  have hr : t - τ ∈ Set.Icc 0 P.T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  obtain ⟨h0, hb⟩ := h.mem0 hr
  have hAφ := h.flow_adm0 ht hφ hτ (j := 1) (by
    have : (1 : ℝ) ≤ P.lev := by exact_mod_cast P.hJ1
    exact this)
  have hAψ := h.flow_adm0 ht hψ hτ (j := 1) (by
    have : (1 : ℝ) ≤ P.lev := by exact_mod_cast P.hJ1
    exact this)
  unfold PdeSetup.gen
  rw [h.flow_comb ht hφ hψ α β hτ]
  have e : (fun k => (α : ℂ) * P.flow D μ t φ τ k + (β : ℂ) * P.flow D μ t ψ τ k) =
      ((α : ℂ) • P.flow D μ t φ τ) + ((β : ℂ) • P.flow D μ t ψ τ) := rfl
  rw [e, forwardGen_add_H1 D (μ (t - τ)) h0 hb 
    (show MemHs 1 ((α : ℂ) • P.flow D μ t φ τ) from HRS.PDE.MFThermalReg.memHs_smul hAφ.2.2 (α : ℂ))
    (show MemHs 1 ((β : ℂ) • P.flow D μ t ψ τ) from HRS.PDE.MFThermalReg.memHs_smul hAψ.2.2 (β : ℂ)), forwardGen_smul, forwardGen_smul]
  rfl

theorem Data.flow_hsNorm0 {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ P.n + 4) :
    HRS.PDE.hsNorm (j : ℝ) (P.flow D μ t φ τ) ≤ (P.c.Cop j + 1) * sobolevNorm (j : ℝ) φ := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have hs0 := sobolevNorm_nonneg' (j : ℝ) φ
  have hc0 := P.c.Cop_nonneg j
  by_cases h0 : t = 0
  · subst h0
    have : τ = 0 := le_antisymm hτ.2 hτ.1
    subst this
    rw [h.flow_zero hφ, ← HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm
      (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ (j : ℝ))]
    nlinarith
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    refine (h.flow_hsNorm ht' hD hτ hj1 hjn).trans ?_
    nlinarith

theorem Data.gen_bd0 {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) {j : ℕ} (hj : j + 2 ≤ P.n + 4) :
    HRS.PDE.hsNorm (j : ℝ) (P.gen D μ t φ τ) ≤
      P.c.Cg j * ((P.c.Cop (j + 2) + 1) * sobolevNorm ((j : ℝ) + 2) φ) := by
  have hr : t - τ ∈ Set.Icc 0 P.T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  have hA := h.flow_adm0 ht hφ hτ (j := (j : ℝ) + 2) (by exact_mod_cast hj)
  have h2 := (P.c.gen D ν₀ μ h.hA h.hν (t - τ) hr j hj _ hA.2.2).2
  have h3 := h.flow_hsNorm0 ht hφ hτ (j := j + 2) (by omega) hj
  have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  rw [hcast] at h3
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_left h3 (P.c.Cg_nonneg j)

end PdeSetup

end HRS.Uniform.Q54c

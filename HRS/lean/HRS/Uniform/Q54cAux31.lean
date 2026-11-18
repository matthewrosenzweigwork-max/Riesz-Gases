import HRS.Uniform.Q54cAux30

/-!
# Q54c, part 31: closeness of the path data `y`, `y'`, `w` of two adjoint dynamics
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem isRealCoeff_sub_q {a b : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    IsRealCoeff (a - b) := fun k => by
  simp only [Pi.sub_apply, map_sub, ha k, hb k]

namespace PdeSetup

variable {P : PdeSetup d} (cc : P.CmpConst) {D₁ D₂ : DynData d} {ν₀ : ℝ} {μ₁ μ₂ : ℝ → Torus d → ℝ}
  (h₁ : P.Data D₁ ν₀ μ₁) (h₂ : P.Data D₂ ν₀ μ₂) (hM : D₁.M = D₂.M) (hV : D₁.V = D₂.V) {δ : ℝ}
  (hδ : ∀ r ∈ Set.Icc 0 P.T, Torus.cbNorm (P.n + 4) (μ₁ r - μ₂ r) ≤ δ)

include cc h₁ h₂ hM hV hδ

theorem Data.cmp_y {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    ‖(P.pd D₁ μ₁).y t φ σ - (P.pd D₂ μ₂).y t φ σ‖ ≤
      cc.Cst * (|D₁.invβ - D₂.invβ| + δ) * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hle : (P.n : ℝ) ≤ P.lev := by have := lev_ge_n2 (P := P); linarith
  have a1 := h₁.flow_adm0 ht hφ hτ hle
  have a2 := h₂.flow_adm0 ht hφ hτ hle
  have e : (P.pd D₁ μ₁).y t φ σ - (P.pd D₂ μ₂).y t φ σ =
      (Sv (P.n : ℝ) (P.flow D₁ μ₁ t φ (t - σ) - P.flow D₂ μ₂ t φ (t - σ))).2 := by
    rw [Sv_sub a1 a2]; rfl
  rw [e]
  refine (norm_snd_Sv_le (a1.sub a2)).trans ?_
  have b1 := h₁.flow_adm0 ht hφ hτ lev_ge_n2
  have b2 := h₂.flow_adm0 ht hφ hτ lev_ge_n2
  refine (hsNorm_mono_q (by linarith) (b1.sub b2).2.2).trans ?_
  exact Data.cmp_flow cc h₁ h₂ hM hV hδ ht hφ hτ

theorem Data.cmp_w {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ‖(P.pd D₁ μ₁).w t φ - (P.pd D₂ μ₂).w t φ‖ ≤
      cc.Cst * (|D₁.invβ - D₂.invβ| + δ) * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hτ : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
  have a1 := h₁.flow_adm0 ht hφ hτ lev_ge_n2
  have a2 := h₂.flow_adm0 ht hφ hτ lev_ge_n2
  have e : (P.pd D₁ μ₁).w t φ - (P.pd D₂ μ₂).w t φ =
      (Sv ((P.n : ℝ) + 2) (P.flow D₁ μ₁ t φ t - P.flow D₂ μ₂ t φ t)).2 := by
    rw [Sv_sub a1 a2]; rfl
  rw [e]
  exact (norm_snd_Sv_le (a1.sub a2)).trans (Data.cmp_flow cc h₁ h₂ hM hV hδ ht hφ hτ)

theorem Data.cmp_y' {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    ‖(P.pd D₁ μ₁).y' t φ σ - (P.pd D₂ μ₂).y' t φ σ‖ ≤
      (cc.Kd * (P.c.Cop (P.n + 2) + 1) + P.c.Cg P.n * cc.Cst) *
        (|D₁.invβ - D₂.invβ| + δ) * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hσT : σ ∈ Set.Icc 0 P.T := ⟨hσ.1, hσ.2.trans ht.2⟩
  have hτ : t - σ ∈ Set.Icc 0 t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hδ0 : 0 ≤ δ := (cbNorm_nonneg_q _ _).trans (hδ σ hσT)
  have hν0 : 0 ≤ |D₁.invβ - D₂.invβ| + δ := by positivity
  have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
  have hle2 : (P.n : ℝ) + 2 ≤ P.lev := lev_ge_n2
  have f1 := h₁.flow_adm0 ht hφ hτ hle2
  have f2 := h₂.flow_adm0 ht hφ hτ hle2
  have hf1' := h₁.flow_adm0 ht hφ hτ (j := 1) (by have := P.hJ1; exact_mod_cast this)
  have hf2' := h₂.flow_adm0 ht hφ hτ (j := 1) (by have := P.hJ1; exact_mod_cast this)
  obtain ⟨h0₂, hb₂⟩ := h₂.mem0 hσT
  obtain ⟨h0₁, hb₁⟩ := h₁.mem0 hσT
  -- the two pieces
  set F₁ := P.flow D₁ μ₁ t φ (t - σ) with hF₁
  set F₂ := P.flow D₂ μ₂ t φ (t - σ) with hF₂
  set E₁ : Coeff d := forwardGen D₁ (μ₁ σ) F₁ - forwardGen D₂ (μ₂ σ) F₁ with hE₁
  set E₂ : Coeff d := forwardGen D₂ (μ₂ σ) (F₁ - F₂) with hE₂
  have hcb : Torus.cbNorm (P.n + 2) (μ₁ σ - μ₂ σ) ≤ δ :=
    (HRS.PDE.cbNorm_mono' (by omega) _).trans (hδ σ hσT)
  obtain ⟨hmE₁, hnE₁⟩ := cc.diff D₁ D₂ ν₀ μ₁ μ₂ h₁.hA h₂.hA hM hV σ hσT δ hcb hb₁ hb₂ F₁ f1.2.2
  have hmE₂ := (P.c.gen D₂ ν₀ μ₂ h₂.hA h₂.hν σ hσT P.n (by omega) (F₁ - F₂) (f1.sub f2).2.2)
  have hreal₁ : IsRealCoeff E₁ := by
    have r1 := forwardGen_isReal' D₁ (μ₁ σ) (isRealCoeff_coeffOf_density h₁.hA.hμ hσT)
      (isRealCoeff_coeffOf_V h₁.hA.hV) f1.1
    have r2 := forwardGen_isReal' D₂ (μ₂ σ) (isRealCoeff_coeffOf_density h₂.hA.hμ hσT)
      (isRealCoeff_coeffOf_V h₂.hA.hV) f1.1
    exact isRealCoeff_sub_q r1 r2
  have hreal₂ : IsRealCoeff E₂ :=
    forwardGen_isReal' D₂ (μ₂ σ) (isRealCoeff_coeffOf_density h₂.hA.hμ hσT)
      (isRealCoeff_coeffOf_V h₂.hA.hV) (f1.sub f2).1
  have hAE₁ : Adm (P.n : ℝ) E₁ :=
    ⟨hreal₁, summable_norm_of_memHs (P.n : ℝ) P.hnd _ hmE₁, hmE₁⟩
  have hAE₂ : Adm (P.n : ℝ) E₂ :=
    ⟨hreal₂, summable_norm_of_memHs (P.n : ℝ) P.hnd _ hmE₂.1, hmE₂.1⟩
  -- the difference of the generator paths
  have eg : P.gen D₁ μ₁ t φ (t - σ) - P.gen D₂ μ₂ t φ (t - σ) = E₁ + E₂ := by
    unfold PdeSetup.gen
    rw [sub_sub_cancel]
    rw [hE₂, forwardGen_sub_H1 D₂ (μ₂ σ) h0₂ hb₂ hf1'.2.2 hf2'.2.2, hE₁]
    abel
  have g1 := h₁.gen_adm0 ht hφ hτ (j := P.n) (by omega) P.hnd
  have g2 := h₂.gen_adm0 ht hφ hτ (j := P.n) (by omega) P.hnd
  have e : (P.pd D₁ μ₁).y' t φ σ - (P.pd D₂ μ₂).y' t φ σ =
      -(Sv (P.n : ℝ) (E₁ + E₂)).2 := by
    rw [← eg, Sv_sub g1 g2]; show -(_) - -(_) = _; simp; abel
  rw [e, norm_neg]
  have hsum : Sv (P.n : ℝ) (E₁ + E₂) = Sv (P.n : ℝ) E₁ + Sv (P.n : ℝ) E₂ := by
    have := Sv_comb hAE₁ hAE₂ 1 1
    have ee : (fun k => ((1 : ℝ) : ℂ) * E₁ k + ((1 : ℝ) : ℂ) * E₂ k) = E₁ + E₂ := by
      funext k; simp
    rw [ee] at this
    rw [this]; simp
  rw [hsum]
  refine (norm_snd_le _).trans ?_
  refine (norm_add_le _ _).trans ?_
  have n1 := hAE₁.norm_Sv_le
  have n2 := hAE₂.norm_Sv_le
  -- bounds on the two pieces
  have b1 : HRS.PDE.hsNorm (P.n : ℝ) E₁ ≤
      cc.Kd * (|D₁.invβ - D₂.invβ| + δ) * ((P.c.Cop (P.n + 2) + 1) * sobolevNorm ((P.n : ℝ) + 4) φ) := by
    refine hnE₁.trans ?_
    have := h₁.flow_hsNorm0 ht hφ hτ (j := P.n + 2) (by omega) (by omega)
    have hcast : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
    rw [hcast] at this
    have h3 := sobolevNorm_mono_idx hφ (a := (P.n : ℝ) + 2) (b := (P.n : ℝ) + 4) (by linarith)
    have hc : 0 ≤ P.c.Cop (P.n + 2) + 1 := by have := P.c.Cop_nonneg (P.n + 2); linarith
    refine mul_le_mul_of_nonneg_left (this.trans ?_) (mul_nonneg cc.Kd_nonneg hν0)
    exact mul_le_mul_of_nonneg_left h3 hc
  have b2 : HRS.PDE.hsNorm (P.n : ℝ) E₂ ≤
      P.c.Cg P.n * (cc.Cst * (|D₁.invβ - D₂.invβ| + δ) * sobolevNorm ((P.n : ℝ) + 4) φ) := by
    refine hmE₂.2.trans ?_
    exact mul_le_mul_of_nonneg_left
      (by
        have := Data.cmp_flow cc h₁ h₂ hM hV hδ ht hφ hτ
        rw [hF₁, hF₂]
        refine (hsNorm_mono_q (le_refl _) (f1.sub f2).2.2).trans ?_
        exact this) (P.c.Cg_nonneg P.n)
  calc _ ≤ HRS.PDE.hsNorm (P.n : ℝ) E₁ + HRS.PDE.hsNorm (P.n : ℝ) E₂ := add_le_add n1 n2
    _ ≤ _ := by
      refine (add_le_add b1 b2).trans (le_of_eq ?_)
      ring

end PdeSetup

end HRS.Uniform.Q54c

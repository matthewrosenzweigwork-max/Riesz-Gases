import HRS.Uniform.Q54cAux28

/-!
# Q54c, part 29: uniform stability constants for two adjoint data (same `M`, `V`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem cbNorm_nonneg_q (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _

namespace PdeSetup

variable (P : PdeSetup d)

/-- stability of the flow (Prop 3.15) and of the generator, uniformly -/
structure CmpConst (P : PdeSetup d) where
  Cst : ℝ
  Kd : ℝ
  Cst_nonneg : 0 ≤ Cst
  Kd_nonneg : 0 ≤ Kd
  stab : ∀ (D₁ D₂ : DynData d) (ν₀ : ℝ) (μ₁ μ₂ : ℝ → Torus d → ℝ),
    AdjointData P.s (P.n + 4) P.R P.MB P.Λ P.VB D₁ ν₀ P.T μ₁ →
    AdjointData P.s (P.n + 4) P.R P.MB P.Λ P.VB D₂ ν₀ P.T μ₂ → D₁.M = D₂.M → D₁.V = D₂.V →
    ∀ δ : ℝ, (∀ r ∈ Set.Icc 0 P.T, Torus.cbNorm (P.n + 4) (μ₁ r - μ₂ r) ≤ δ) →
    ∀ φc : Coeff d, MemHs P.lev φc → ∀ t ∈ Set.Icc 0 P.T, ∀ τ ∈ Set.Icc 0 t,
      HRS.PDE.hsNorm ((P.n : ℝ) + 2)
        (propagatorCoeff D₁ μ₁ P.lev t φc τ - propagatorCoeff D₂ μ₂ P.lev t φc τ) ≤
      Cst * (|D₁.invβ - D₂.invβ| + δ) * HRS.PDE.hsNorm P.lev φc
  diff : ∀ (D₁ D₂ : DynData d) (ν₀ : ℝ) (μ₁ μ₂ : ℝ → Torus d → ℝ),
    AdjointData P.s (P.n + 4) P.R P.MB P.Λ P.VB D₁ ν₀ P.T μ₁ →
    AdjointData P.s (P.n + 4) P.R P.MB P.Λ P.VB D₂ ν₀ P.T μ₂ → D₁.M = D₂.M → D₁.V = D₂.V →
    ∀ r ∈ Set.Icc 0 P.T, ∀ δ : ℝ, Torus.cbNorm (P.n + 2) (μ₁ r - μ₂ r) ≤ δ →
    (∀ j, MemHs 0 (driftCoeff D₁ (μ₁ r) j)) → (∀ j, MemHs 0 (driftCoeff D₂ (μ₂ r) j)) →
    ∀ u : Coeff d, MemHs ((P.n : ℝ) + 2) u →
      MemHs (P.n : ℝ) (forwardGen D₁ (μ₁ r) u - forwardGen D₂ (μ₂ r) u) ∧
      HRS.PDE.hsNorm (P.n : ℝ) (forwardGen D₁ (μ₁ r) u - forwardGen D₂ (μ₂ r) u) ≤
        Kd * (|D₁.invβ - D₂.invβ| + δ) * HRS.PDE.hsNorm ((P.n : ℝ) + 2) u

theorem exists_cmpConst : Nonempty P.CmpConst := by
  obtain ⟨C, C', hC, hC', hst⟩ := propagator_stability P.hd P.s P.hs0 P.hsd (P.n + 2) (by omega) P.R
    P.MB P.Λ P.VB
  obtain ⟨Kd, hKd0, hKd⟩ := HRS.PDE.StabAux.forwardGen_diff_bound P.hd P.s P.hs0 P.hsd P.n P.MB P.Λ
  have hlev : ((P.n + 2 : ℕ) : ℝ) + 2 = P.lev := by unfold PdeSetup.lev; push_cast; ring
  have hlev2 : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
  refine ⟨⟨C * |P.T| * Real.exp (C' * |P.T|), Kd, by positivity, hKd0, ?_, ?_⟩⟩
  · intro D₁ D₂ ν₀ μ₁ μ₂ hA₁ hA₂ hM hV δ hδ φc hφ t ht τ hτ
    have hr : 0 ≤ t - τ := by linarith [hτ.2]
    have hrt : t - τ ≤ t := by linarith [hτ.1]
    have hφ' : MemHs (((P.n + 2 : ℕ) : ℝ) + 2) φc := by rw [hlev]; exact hφ
    have h1 := hst D₁ D₂ ν₀ P.T μ₁ μ₂ hA₁ hA₂ hM hV δ hδ φc hφ' (t - τ) t hr hrt ht.2
    rw [hlev, hlev2, sub_sub_cancel, hR] at h1
    refine h1.trans ?_
    have hτT : τ ≤ |P.T| := (hτ.2.trans ht.2).trans (le_abs_self _)
    have hτ0 : 0 ≤ τ := hτ.1
    have hδ0 : 0 ≤ δ := (cbNorm_nonneg_q _ _).trans (hδ 0 ⟨le_rfl, hτ0.trans (hτ.2.trans ht.2)⟩)
    have hs : 0 ≤ |D₁.invβ - D₂.invβ| + δ := by positivity
    have hn : 0 ≤ HRS.PDE.hsNorm P.lev φc := Real.sqrt_nonneg _
    have hτ' : C * τ * Real.exp (C' * τ) ≤ C * |P.T| * Real.exp (C' * |P.T|) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hτT hC.le)
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτT hC'.le)) (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτ' hs) hn
  · intro D₁ D₂ ν₀ μ₁ μ₂ hA₁ hA₂ hM hV r hr δ hδ hb₁ hb₂ u hu
    have hA₁' : AdjointData P.s P.n P.R P.MB P.Λ P.VB D₁ ν₀ P.T μ₁ :=
      HRS.PDE.StabAux.adjointData_mono (by omega) hA₁
    have hA₂' : AdjointData P.s P.n P.R P.MB P.Λ P.VB D₂ ν₀ P.T μ₂ :=
      HRS.PDE.StabAux.adjointData_mono (by omega) hA₂
    have hr₁ := (HRS.PDE.ET.coeff_memHs_zero_of_data D₁ (μ₁ r) (hA₁.hμ.smooth r hr) hA₁.hV).1
    have hr₂ := (HRS.PDE.ET.coeff_memHs_zero_of_data D₂ (μ₂ r) (hA₂.hμ.smooth r hr) hA₂.hV).1
    have hA₁'' : AdjointData P.s (P.n + 2) P.R P.MB P.Λ P.VB D₁ ν₀ P.T μ₁ :=
      HRS.PDE.StabAux.adjointData_mono (by omega) hA₁
    have hA₂'' : AdjointData P.s (P.n + 2) P.R P.MB P.Λ P.VB D₂ ν₀ P.T μ₂ :=
      HRS.PDE.StabAux.adjointData_mono (by omega) hA₂
    obtain ⟨hm, hsq⟩ := hKd D₁ D₂ hA₁.hs hA₂.hs hM hA₁.hM hV (μ₁ r) (μ₂ r) (hA₁.hμ.prob r hr)
      (hA₂.hμ.prob r hr) (hA₁'.hμ.smooth r hr) (hA₂'.hμ.smooth r hr) (hA₁'.hμ.bound r hr)
      (hA₂'.hμ.bound r hr) hr₁ hr₂ hb₁ hb₂ δ hδ u hu
    refine ⟨hm, ?_⟩
    unfold HRS.PDE.hsNorm
    have hδ0 : 0 ≤ δ := (cbNorm_nonneg_q _ _).trans hδ
    have hs : 0 ≤ Kd * (|D₁.invβ - D₂.invβ| + δ) := by positivity
    calc Real.sqrt (hsNormSq (P.n : ℝ) _) ≤
        Real.sqrt ((Kd * (|D₁.invβ - D₂.invβ| + δ)) ^ 2 * hsNormSq ((P.n : ℝ) + 2) u) :=
          Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs]

end PdeSetup

end HRS.Uniform.Q54c

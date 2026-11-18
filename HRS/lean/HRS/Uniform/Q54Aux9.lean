import HRS.Uniform.Q54Aux8
import HRS.PDE.EnergyTorusDeriv
import HRS.PDE.WellPosed

/-!
# Q54, part 9: the energy inequality along a forward solution at a real index

For a forward solution `F` (`IsForwardSolution`, the coefficient path of `τ ↦ U^{t-τ,t}φ`) which is continuous in `H^{a+2}`
and in `H^{m+2}` (`m` the level of the adjoint data), and coefficients satisfying `GenHyp` on `[0,T]`:
`‖F(τ)‖²_{H^a} ≤ e^{2Cτ} ‖φ‖²_{H^a}` with `C` depending on `(s, K, MB, Bμ, BV, a, ν₀)` only
(the quasi-contractivity of `U` in `H^a`, `a` real).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem forward_energy_bound (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ) (m : ℕ) (R : Regime)
      (MB' Λ VB ν₁ : ℝ), AdjointData s m R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ (φc : Coeff d) (F : ℝ → Coeff d), IsForwardSolution D μ t φc F →
        ContinuousInHs (a + 2) F t → ContinuousInHs ((m : ℝ) + 2) F t →
        ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq a (F τ) ≤ Real.exp (2 * C * τ) * hsNormSq a φc := by
  obtain ⟨C₁, hC₁, hgen⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  obtain ⟨C₂, hC₂, hform⟩ := gen_form s hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ hν₀
  refine ⟨C₂, hC₂, fun D T μ m R MB' Λ VB ν₁ hA hG hν t ht φc F hF hcA hcm τ hτ => ?_⟩
  obtain ⟨B, hB0, hB⟩ := bounded_of_continuousInHs hcA
  set c1 : ℝ := 2 * D.invβ ^ 2 + C₁ with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hgσ : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs a (forwardGen D (μ (t - σ)) (F σ)) ∧
        hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤ c1 * hsNormSq (a + 2) (F σ) := by
    intro σ hσ
    exact hgen D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) (F σ) (hcA.1 σ hσ) (hF.h1 σ hσ)
  have hderiv := hasDeriv_energy_abstract (t := t) a F (fun σ => forwardGen D (μ (t - σ)) (F σ))
    (c1 * B) B (by positivity) hB0 hcA.1 hB (fun σ hσ => (hgσ σ hσ).1)
    (fun σ hσ => (hgσ σ hσ).2.trans (mul_le_mul_of_nonneg_left (hB σ hσ) hc10))
    (fun k => continuousOn_coord_of_continuousInHs hcA k)
    (fun k => gen_coord_continuousOn hA ht hcm k)
    (fun k => hasDerivWithinAt_of_primitive (gen_coord_continuousOn hA ht hcm k) (φc k) (hF.eq k))
  have hle : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (F σ)).re ≤
        (2 * C₂) * ((1 / 2 : ℝ) * hsNormSq a (F σ)) := by
    intro σ hσ
    have h1 := hform D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) hν (F σ) (hcA.1 σ hσ) (hF.h1 σ hσ)
    have h2 : 0 ≤ (ν₀ / 2) * hsNormSq (a + 1) (F σ) :=
      mul_nonneg (by positivity) (hsNormSq_nonnegE _ _)
    nlinarith
  have hgr := gronwall_aux (t := t) (y := fun σ => (1 / 2 : ℝ) * hsNormSq a (F σ))
    (y' := fun σ => (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (F σ)).re) (2 * C₂) hderiv hle τ hτ
  have h0 : F 0 = φc := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
    simpa using this
  simp only [h0] at hgr
  have : (1 / 2 : ℝ) * hsNormSq a (F τ) ≤ Real.exp (2 * C₂ * τ) * ((1 / 2 : ℝ) * hsNormSq a φc) := hgr
  nlinarith

end HRS.Uniform.Q54

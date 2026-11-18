import HRS.Uniform.Q54cAux15

/-!
# Q54c, part 16: uniform PDE constants at integer Sobolev levels

`PdeConst`: the operator bound `‖U^{r,t}φ‖_{H^j} ≤ Cop_j ‖φ‖_{H^j}` (Prop 3.9, `adjoint_torus_classical`) and the
generator bound `‖𝓛u‖_{H^j} ≤ Cg_j ‖u‖_{H^{j+2}}` (`forwardGen_bound`), uniform over all admissible data
(no positivity of the viscosity is used).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

/-- the uniform constants of the PDE estimates at integer levels -/
structure PdeConst (d : ℕ) (s : ℝ) (n : ℕ) (R : Regime) (MB Λ VB T Bν : ℝ) where
  Cop : ℕ → ℝ
  Cg : ℕ → ℝ
  Cop_nonneg : ∀ j, 0 ≤ Cop j
  Cg_nonneg : ∀ j, 0 ≤ Cg j
  op : ∀ (D : DynData d) (ν₀ : ℝ) (μ : ℝ → Torus d → ℝ), AdjointData s (n + 4) R MB Λ VB D ν₀ T μ →
    ∀ t ∈ Set.Ioc 0 T, ∀ φ : Torus d → ℝ, HRS.Uniform.Q54.Dom (n + 4) φ → ∀ j : ℕ, 1 ≤ j → j ≤ n + 4 →
      ∀ r ∈ Set.Icc 0 t, sobolevNorm (j : ℝ) (propagator D μ r t φ) ≤ Cop j * sobolevNorm (j : ℝ) φ
  gen : ∀ (D : DynData d) (ν₀ : ℝ) (μ : ℝ → Torus d → ℝ), AdjointData s (n + 4) R MB Λ VB D ν₀ T μ →
    D.invβ ≤ Bν → ∀ r ∈ Set.Icc 0 T, ∀ j : ℕ, j + 2 ≤ n + 4 → ∀ u : Coeff d, MemHs ((j : ℝ) + 2) u →
      MemHs (j : ℝ) (forwardGen D (μ r) u) ∧
        HRS.PDE.hsNorm (j : ℝ) (forwardGen D (μ r) u) ≤ Cg j * HRS.PDE.hsNorm ((j : ℝ) + 2) u

theorem exists_pdeConst (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (n : ℕ) (hn : mStar d ≤ n + 4)
    (R : Regime) (hR : ∀ C ν₀ θ, R.lambdaM C ν₀ θ = C) (MB Λ VB T Bν : ℝ) :
    Nonempty (PdeConst d s n R MB Λ VB T Bν) := by
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd s hs0 hsd (n + 4) hn R MB Λ VB
  have hgen : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp j VB D.V →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (j + 3) ρ → Torus.cbNorm (j + 3) ρ ≤ Λ →
      ∀ u : Coeff d, MemHs ((j : ℝ) + 2) u →
        MemHs (j : ℝ) (forwardGen D ρ u) ∧
        hsNormSq (j : ℝ) (forwardGen D ρ u) ≤ (4 * D.invβ ^ 2 + c) * hsNormSq ((j : ℝ) + 2) u :=
    fun j => HRS.PDE.StabAux.forwardGen_bound hd s hs0 hsd j MB Λ VB
  choose c hc0 hc using hgen
  refine ⟨⟨fun j => Real.exp (|Cs j| * T), fun j => Real.sqrt (4 * Bν ^ 2 + c j),
    fun j => (Real.exp_pos _).le, fun j => Real.sqrt_nonneg _, ?_, ?_⟩⟩
  · intro D ν₀ μ hA t ht φ hφ j hj1 hjn r hr
    obtain ⟨-, -, hmain', -⟩ := hmain D ν₀ T μ hA t ht φ hφ.1 hφ.2
    obtain ⟨-, hb⟩ := (hmain' j hj1 hjn r hr)
    refine hb.trans ?_
    rw [hR]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
    have h1 : Cs j ≤ |Cs j| := le_abs_self _
    have h2 : t - r ≤ T := by linarith [hr.1, ht.2]
    have h3 : 0 ≤ t - r := by linarith [hr.2]
    have h4 : 0 ≤ |Cs j| := abs_nonneg _
    nlinarith
  · intro D ν₀ μ hA hν r hr j hj u hu
    have hA' : AdjointData s j R MB Λ VB D ν₀ T μ :=
      HRS.PDE.StabAux.adjointData_mono (by omega) hA
    obtain ⟨hm, hsq⟩ := hc j D hA.hs hA.hM hA'.hV (μ r) (hA.hμ.prob r hr)
      (hA'.hμ.smooth r hr) (hA'.hμ.bound r hr) u hu
    refine ⟨hm, ?_⟩
    unfold HRS.PDE.hsNorm
    have hb : 4 * D.invβ ^ 2 + c j ≤ 4 * Bν ^ 2 + c j := by
      have h0 := D.hβ
      have : D.invβ ^ 2 ≤ Bν ^ 2 := pow_le_pow_left₀ h0 hν 2
      linarith
    have hn : 0 ≤ hsNormSq ((j : ℝ) + 2) u := by
      unfold hsNormSq
      exact tsum_nonneg fun k => mul_nonneg (by unfold sobWeight; positivity) (sq_nonneg _)
    calc Real.sqrt (hsNormSq (j : ℝ) (forwardGen D (μ r) u))
        ≤ Real.sqrt ((4 * D.invβ ^ 2 + c j) * hsNormSq ((j : ℝ) + 2) u) := Real.sqrt_le_sqrt hsq
      _ ≤ Real.sqrt ((4 * Bν ^ 2 + c j) * hsNormSq ((j : ℝ) + 2) u) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hb hn)
      _ = _ := by
          rw [Real.sqrt_mul (by nlinarith [hc0 j, sq_nonneg Bν])]

end HRS.Uniform.Q54c

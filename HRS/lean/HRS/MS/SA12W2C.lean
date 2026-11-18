import HRS.MS.SA12W2B

/-!
# S.A.12 C5 (SA12W2 worker), part C: the all-order torus path

For `AdjointData` at every level and a smooth real datum, the level-one propagator path `P τ` (which is also the path at every
level on `[0,t]`) has: all jets of `toFun (P τ)` jointly continuous and `τ`-differentiable with derivative the same jet of the
generator, all jets of the generator path jointly continuous, `ℓ¹` real coefficients of the generator, and
`backwardGenerator D ρ(t-τ) (toFun (P τ)) = toFun (forwardGen D ρ(t-τ) (P τ))` (`sa12w2_torus_path`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

theorem sa12w2_contOn_of_subtype {E : Type*} [TopologicalSpace E] {t : ℝ} {f : ℝ × Euc d → E}
    (hc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f (p.1.1, p.2)) :
    ContinuousOn f (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) := by
  rw [continuousOn_iff_continuous_restrict]
  exact hc.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
    fun p : ↥(Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) => p.2.1).prodMk
    (continuous_snd.comp continuous_subtype_val))

/-- Joint continuity of the jets of the generator path, and its reality and `ℓ¹` summability, at a high fixed level. -/
theorem sa12w2_gen_jets {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (R : PDE.Regime) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (MB Λ VB : ℝ), ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ),
      PDE.AdjointData s N R MB Λ VB D ν₀ T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ φc : PDE.Coeff d,
        PDE.MemHs (N : ℝ) φc → PDE.IsRealCoeff φc →
        (∀ τ ∈ Icc (0 : ℝ) t,
          ClassicalPart.WS 0 (PDE.forwardGen D (μ (t - τ)) (PDE.propagatorCoeff D μ (N : ℝ) t φc τ)) ∧
          PDE.IsRealCoeff (PDE.forwardGen D (μ (t - τ)) (PDE.propagatorCoeff D μ (N : ℝ) t φc τ)) ∧
          ClassicalPart.WS 0 (PDE.propagatorCoeff D μ (N : ℝ) t φc τ) ∧
          Torus.IsCk 2 (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc τ))) ∧
        (∀ j ≤ k, ContinuousOn (fun p : ℝ × Euc d =>
          iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.forwardGen D (μ (t - p.1))
            (PDE.propagatorCoeff D μ (N : ℝ) t φc p.1)))) p.2) (Icc (0 : ℝ) t ×ˢ univ)) := by
  refine ⟨⌊(d : ℝ) / 2⌋₊ + k + 5, by omega, ?_⟩
  intro MB Λ VB D ν₀ T μ hA t ht φc hφ hre
  set N : ℕ := ⌊(d : ℝ) / 2⌋₊ + k + 5 with hN
  have hfl : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hNr : (N : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + k + 5 := by simp [hN]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hm1 : 1 ≤ N := by omega
  have hmd : (d : ℝ) / 2 < N := by linarith
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd N hm1 R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hreal := ClassicalPart.propagatorCoeff_real hd s hs0 hsd N hm1 R MB Λ VB D ν₀ T μ hA t ht φc hφ hre
  obtain ⟨hGc, -⟩ := adjoint_torus_time_regularity hd s hs0 hsd N hm1 R MB Λ VB D ν₀ T μ hA t ht φc hφ
  set F := propagatorCoeff D μ (N : ℝ) t φc with hF
  have hcont : ContinuousInHs ((N : ℝ) - 1) F t :=
    forward_strong_continuity (N : ℝ) t F hw _ (by linarith)
  have hgp := ClassicalPart.gen_path_facts hA hmd ht hsol hreal (m'' := (N : ℝ) - 1) (by linarith) hcont
  have hGreal : ∀ τ ∈ Set.Icc (0 : ℝ) t, IsRealCoeff (forwardGen D (μ (t - τ)) (F τ)) := fun τ hτ =>
    (hgp.1 τ hτ).2
  have hmem := hw.1
  clear_value F
  refine ⟨fun τ hτ => ⟨(hgp.1 τ hτ).1, (hgp.1 τ hτ).2, ClassicalPart.ws0_of_memHs hmd (hmem τ hτ), ?_⟩,
    fun j hj => ?_⟩
  · obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := d) 2 (N : ℝ) (by push_cast; linarith)
    exact (hC2 _ (hmem τ hτ) (hreal τ hτ)).1
  · have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
    have hc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
        iteratedFDeriv ℝ j (Torus.lift (toFun (forwardGen D (μ (t - p.1.1)) (F p.1.1)))) p.2 := by
      refine ClassicalPart.continuous_iteratedFDeriv_toFun (X := Set.Icc (0 : ℝ) t)
        (fun x => forwardGen D (μ (t - x.1)) (F x.1)) j ((N : ℝ) - 2) (by linarith)
        (fun x => hGreal _ x.2) (fun x => hGc.1 _ x.2) (fun x₀ => ?_)
      exact ClassicalPart.tendsto_subtype_of_within (t := t)
        (fun τ => hsNorm ((N : ℝ) - 2) (forwardGen D (μ (t - τ)) (F τ) -
          forwardGen D (μ (t - (x₀ : ℝ))) (F x₀))) x₀ (hGc.2 _ x₀.2)
    exact sa12w2_contOn_of_subtype hc

end HRS.PDE.SA12W2

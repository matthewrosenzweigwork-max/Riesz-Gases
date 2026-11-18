import HRS.MS.SA12W2A

/-!
# S.A.12 C4 (SA12W2 worker): high torus jets, derivative level chosen before the coefficient bounds

`sa12w2_C4` is the contract `r26t5_C4` (R26-T5.T03): there is `N` (depending only on `d, k`) such that for every
`AdjointData` at level `N` and real `H^N` datum, the jets of order `≤ k` of the Fourier series of the propagator are
jointly continuous on `[0,t] × ℝ^d` and differentiable in `τ` with derivative the same jet of the generator.
`sa12w2_torus_jet_regularity` is the spec form `torus_jet_regularity` (T1a of `HRS/MH/AdjointRdSpec.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

theorem sa12w2_C4 {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (R : PDE.Regime) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (MB Λ VB : ℝ), ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ),
      PDE.AdjointData s N R MB Λ VB D ν₀ T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ φc : PDE.Coeff d,
        PDE.MemHs (N : ℝ) φc → PDE.IsRealCoeff φc →
        (∀ j ≤ k, ContinuousOn (fun p : ℝ × Euc d =>
          iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc p.1))) p.2)
            (Icc (0 : ℝ) t ×ˢ univ)) ∧
        (∀ j ≤ k, ∀ y : Euc d, ∀ τ ∈ Icc (0 : ℝ) t,
          HasDerivWithinAt
            (fun τ' => iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc τ'))) y)
            (iteratedFDeriv ℝ j (Torus.lift (PDE.toFun
              (PDE.forwardGen D (μ (t - τ)) (PDE.propagatorCoeff D μ (N : ℝ) t φc τ)))) y)
            (Icc (0 : ℝ) t) τ) := by
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
  set F := propagatorCoeff D μ (N : ℝ) t φc with hF
  have hcont : ContinuousInHs ((N : ℝ) - 1) F t :=
    forward_strong_continuity (N : ℝ) t F hw _ (by linarith)
  have hjet : ∀ j ≤ k, Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (toFun (F p.1))) p.2 := by
    intro j hj
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
    refine ClassicalPart.continuous_iteratedFDeriv_toFun (X := Set.Icc (0 : ℝ) t) (fun x => F x.1) j
      ((N : ℝ) - 1) (by linarith) (fun x => hreal _ x.2) (fun x => hcont.1 _ x.2) (fun x₀ => ?_)
    exact ClassicalPart.tendsto_subtype_of_within (t := t)
      (fun τ => hsNorm ((N : ℝ) - 1) (F τ - F x₀)) x₀ (hcont.2 _ x₀.2)
  obtain ⟨hGc, htr⟩ := adjoint_torus_time_regularity hd s hs0 hsd N hm1 R MB Λ VB D ν₀ T μ hA t ht φc hφ
  have hGreal : ∀ τ ∈ Set.Icc (0 : ℝ) t, IsRealCoeff (forwardGen D (μ (t - τ)) (F τ)) := fun τ hτ =>
    ((ClassicalPart.gen_path_facts hA hmd ht hsol hreal (m'' := (N : ℝ) - 1) (by linarith) hcont).1 τ hτ).2
  refine ⟨fun j hj => ?_, fun j hj y τ hτ => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    exact (hjet j hj).comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
      fun p : ↥(Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) => p.2.1).prodMk
      (continuous_snd.comp continuous_subtype_val))
  · have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
    have hm2 : (d : ℝ) / 2 + j < (N : ℝ) - 2 := by linarith
    obtain ⟨C₁, hC₁⟩ := sa12w2_jet_bound j ((N : ℝ) - 2) hm2
    rw [hasDerivWithinAt_iff_tendsto_slope]
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hup : Tendsto (fun τ' : ℝ => max C₁ 0 * hsNorm ((N : ℝ) - 2) (fun k =>
        (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - forwardGen D (μ (t - τ)) (F τ) k))
        (𝓝[Icc (0 : ℝ) t \ {τ}] τ) (𝓝 0) := by
      simpa using (htr τ hτ).const_mul (max C₁ 0)
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hup
    filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    obtain ⟨hI, hne⟩ := hτ'
    have hne' : τ' - τ ≠ 0 := sub_ne_zero.2 hne
    have hle : (N : ℝ) - 2 ≤ N := by linarith
    have ha := (hw.1 τ' hI).mono hle
    have hb := (hw.1 τ hτ).mono hle
    have he := hGc.1 τ hτ
    have hQ : (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - forwardGen D (μ (t - τ)) (F τ) k) =
        fun k => (((1 / (τ' - τ) : ℝ)) : ℂ) * (F τ' k - F τ k) - forwardGen D (μ (t - τ)) (F τ) k := by
      funext k
      push_cast
      ring
    rw [hQ, slope_def_module, ← one_div, ← sa12w2_jet_comb j ((N : ℝ) - 2) hm2 (F τ') (F τ) _ ha hb he
      (hreal τ' hI) (hreal τ hτ) (hGreal τ hτ) (1 / (τ' - τ)) y]
    have hQm := sa12w2_memHs_comb ha hb he (1 / (τ' - τ))
    have hQr := sa12w2_isReal_comb (hreal τ' hI) (hreal τ hτ) (hGreal τ hτ) (1 / (τ' - τ))
    refine (hC₁ _ hQm hQr y).2.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-- The spec form `torus_jet_regularity` (T1a): the derivative level may also depend on the (earlier) constants. -/
theorem sa12w2_torus_jet_regularity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (R : PDE.Regime)
    (MB Λ VB : ℝ) :
    ∃ N : ℕ, ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ),
      PDE.AdjointData s N R MB Λ VB D ν₀ T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ φc : PDE.Coeff d,
        PDE.MemHs (N : ℝ) φc → PDE.IsRealCoeff φc →
        (∀ j ≤ k, ContinuousOn (fun p : ℝ × Euc d =>
          iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc p.1))) p.2)
            (Icc (0 : ℝ) t ×ˢ univ)) ∧
        (∀ j ≤ k, ∀ y : Euc d, ∀ τ ∈ Icc (0 : ℝ) t,
          HasDerivWithinAt
            (fun τ' => iteratedFDeriv ℝ j (Torus.lift (PDE.toFun (PDE.propagatorCoeff D μ (N : ℝ) t φc τ'))) y)
            (iteratedFDeriv ℝ j (Torus.lift (PDE.toFun
              (PDE.forwardGen D (μ (t - τ)) (PDE.propagatorCoeff D μ (N : ℝ) t φc τ)))) y)
            (Icc (0 : ℝ) t) τ) := by
  obtain ⟨N, -, h⟩ := sa12w2_C4 hd s hs0 hsd k R
  exact ⟨N, h MB Λ VB⟩

end HRS.PDE.SA12W2

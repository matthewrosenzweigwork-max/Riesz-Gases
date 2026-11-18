import HRS.Whole.Orbits

/-!
# S5.7 `fixed_equation`: plan and the formal junk-value defect (worker S57)

Frozen statement `HRS.Whole.fixed_equation` (`HRS/Whole/Orbits.lean`, ~:525; TeX S L4078-4106).

## RESULT OF STEP 1: the frozen statement is FALSE as stated (no `type_of%` tie can exist)

Defect (junk value of the same kind as S.B.7 and S5.2): the hypothesis on the prescribed initial field
`η₀` is `IsLinearOnE b.k ((d+3)/2) (η₀ ζ)` (additivity/homogeneity only) together with
`∫⁻ dualNormE b.k ((d+3)/2) (η₀ ζ) ^ p < ⊤`, and `dualNormE` is a supremum over `C_c^∞` test functions
only (audit repair, `Orbits.lean` ~:299).  Nothing forces `η₀ ζ` to be continuous on `E_{k,(d+3)/2}`, i.e. to
be an element of `F_0`.  But the conclusion applies `η₀ ζ` to `propagatorW C 0 t φ`, which is NOT compactly
supported (not even for the trivial generator).  `s57_exists_wild_functional` below constructs, for any
`f₀` without compact support, a functional `η` that is linear on ALL functions, vanishes on every function of
compact support (so `IsLinearOnE` holds and `dualNormE r P η = 0`) and has `η f₀ = 1`.

Counterexample to `fixed_equation` (all hypotheses checked against the Lean statement):
* `b : WholeBounds d` valid, with `M = 0`, `Q = 0`, `d ≥ 2`, `s = 0`, `T = 1`, `θ` a cutoff, `k, m, L, K, Λ, νstar` large;
* `νN = ν = 0`, `cN = c = 0`, `ρN = ρ = ` a Gaussian probability density (weighted bounds at the demanded levels
  hold for a suitable `Λ`); `aN = 1`, `a = 0`, `qN = q = 0`; `Ω = Unit`, `η₀ ζ = η` constant with
  `η (oscTestFun m 0) = 1` (`oscTestFun m 0` is a positive Gaussian, so it has no compact support).
* the generator of `fixedEqCoeff` is identically `0` (matrix `0`, no drift, no viscosity), so `UlAdjointInput`
  holds for both families (every classical adjoint solution is constant in `r`, hence `propagatorW C r t φ = φ`;
  the bound is the `H_ul`-Sobolev embedding); `η₀` is measurable (constant), a.s. linear, and
  `dualNormE = 0`, so the moment is `0 < ⊤`.
* Any pair of solutions has `eval (YN t ζ) (oscTestFun m 0) = η (oscTestFun m 0) = 1` a.s. (noise level `0`:
  `noiseCovW = 0`, `multivariateGaussian 0 0 = δ₀`; `eval_oscTestFun`), and `eval (Y t ζ) _ = 0`.  Hence the left
  side of the cost inequality is `> 0` for every coupling.
* The right side is `ofReal C * ((ofReal 1 + 0 * 0) * 0 + 0 + 0) = 0` because `dualNormE = 0` makes the factor
  `(∫⁻ dualNormE ^ p)^(1/p)` equal to `0`.  So the inequality fails for every `C`, and the conclusion `∃ Ω₂ ...`
  is false for this instance.

(The conclusion also contains the existence of the two Gaussian solutions; that existence is a separate
construction that is not in the library.)

## Further insufficiencies (would remain after repairing the defect above)

1. Uniqueness of classical adjoint solutions.  `propagatorW` is a `Classical.choose`.  The Duhamel identity
   `(U_N - U)φ = ∫ U_N (L_N - L) U φ` needs uniqueness of classical solutions (F-CAU, `HRS/MS/FcauTie.lean`),
   whose hypotheses (`CoeffHypRd`, `VHypRd`, `MatBound`, a regime `RdRegimeHolds`) are NOT implied by
   `UlAdjointInput`; `WholeSetup` carries `regime`/`force` for this reason (F-CAU-regime), but `fixed_equation`
   has no counterpart.
2. Adjoint level.  The statement assumes `UlAdjointInput ... (b.k + 1) b.K` only.  The difference estimate in
   `C_b^k` applies `U_N` (level `k`, data in `H_ul^{k+1+⌈d/2⌉}`) to `(L_N - L) U φ_α`, which contains `Δ U φ_α`:
   one needs `U φ_α` in `C_b^{k+3+⌈d/2⌉}` (which controls `H_ul` of that order), i.e. `UlAdjointInput` through order
   `≥ k + 3 + ⌈d/2⌉` for both families (the TeX has "the same uniform adjoint branch", i.e. the adjoint theorem
   at the higher levels).  `ul_adjoint_fixed_viscosity` gives such levels only for time-independent `(c, ρ)`, `ν > 0`.
3. The coefficients `(ρ_N, c_N, ν_N)` are not tied to a `WholeSetup` (no `IsWholeMeanFieldSolution`, no `regime`,
   no `force`), so S5.5 (`general_orbits_*`, quantified over `WholeSetup`) does not apply verbatim; its `Go*`
   lemmas must be re-run for `fixedEqCoeff`.

## Proposed repair (for approval; frozen statement not touched)

(R1) replace `IsLinearOnE` by a bounded linear functional on `C^k` functions of finite `E`-norm:
`∀ f, ContDiff ℝ k f → weightedSobolevE k P f < ⊤ → ENNReal.ofReal |η f| ≤ dualNormE k P η * weightedSobolevE k P f`
plus linearity on that class;
(R2) add the F-CAU regime/force hypotheses (as in `WholeSetup`) for both families, or a hypothesis `∀ f, IsClassicalAdjointW ..`
uniqueness;
(R3) raise the adjoint level to `b.k + 3 + ⌈d/2⌉ + 1` (to be recounted against `k + 6 + ⌈d/2⌉ + 4`).

## Plan for the repaired statement (sizes are Lean lines, estimate; total above the 4,000 line stop rule)

* P1 (`FixEqAux2`, ~1.2k): inhomogeneous Duhamel identity and the difference bound `‖(U_N-U)φ‖_{C_b^k} ≤ C Δ_N b_α`
  (needs F-CAU, `UlAdjointInput` at the raised level, `far_derivatives_proof` for the `ρ`-term; stability of
  `s ↦ U^{r,s}φ` in the terminal time, which F-CAU does not provide).
* P2 (`FixEqAux3`, ~0.8k): `E_{k,(d+3)/2}` versus `C_b^k` (`∫⟨x⟩^{-(d+3)} < ∞`), `ℓ²` summation with `b_α = λ_α^{(J-m)/2}`,
  `|η(f)| ≤ ‖η‖ ‖f‖_E`: the initial term.
* P3 (`FixEqAux4`, ~1.2k): feature differences `Γ^N - Γ`, `|√u - √v|² ≤ |u - v|`, Hilbert-Schmidt difference
  `C_T{|√q_N-√q|² + q Δ_N² + q τ_N}`, `orbit_maximal_proof` for the reconstructed difference path.
* P4 (`FixEqAux5`, ~1.5k+): existence of the two linear fluctuation solutions on `Ω × Ω₂` with the SAME cylindrical white
  noise on `L²([0,T]×ℝ^d;ℝ^d)` (Wiener space `wMeasure` of `HRS/Prob/MRepAux13.lean`, Hilbert Itô integral
  `IsHilbertItoIntegral`/`gfb3_exists_hilbert_version`, Gaussian finite-dimensional laws with covariance `noiseCovW`,
  independence of `η₀`, continuity in `B_m` via S5.2).  No existence statement for `IsLinearFluctuationSolutionW`
  is in the library.
* P5 (`FixEqTie`, ~0.4k): assembly, `p = 1` from `p = 2`.
* Dependencies: S5.4 `weighted_higher_order` is NOT needed (sup norms suffice: `E_{k,(d+3)/2}` is controlled by `C_b^k`);
  S5.6 `general_paths` is NOT used (it takes the solution `Y` as a hypothesis; the existence in P4 is new work).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Whole

variable {d : ℕ}

/-- The submodule of compactly supported functions. -/
def s57_cptSub (d : ℕ) : Submodule ℝ (Euc d → ℝ) where
  carrier := {f | HasCompactSupport f}
  add_mem' := fun {f g} hf hg => HasCompactSupport.add hf hg
  zero_mem' := HasCompactSupport.zero
  smul_mem' := fun c f hf => HasCompactSupport.smul_left hf

/-- A functional that is linear on all functions, vanishes on all compactly supported functions, and takes the
value `1` at a function without compact support. -/
theorem s57_exists_wild_functional (f₀ : Euc d → ℝ) (hf₀ : ¬ HasCompactSupport f₀) :
    ∃ η : (Euc d → ℝ) → ℝ, (∀ f g, η (f + g) = η f + η g) ∧ (∀ (c : ℝ) f, η (c • f) = c * η f) ∧
      (∀ f, HasCompactSupport f → η f = 0) ∧ η f₀ = 1 := by
  obtain ⟨ℓ, hℓ, hmap⟩ := (s57_cptSub d).exists_dual_map_eq_bot_of_notMem (x := f₀) hf₀ inferInstance
  refine ⟨fun f => (ℓ f₀)⁻¹ * ℓ f, fun f g => ?_, fun c f => ?_, fun f hf => ?_, ?_⟩
  · simp [mul_add]
  · simp only [map_smul, smul_eq_mul]; ring
  · have : ℓ f = 0 := by
      have hmem : ℓ f ∈ (s57_cptSub d).map ℓ := ⟨f, hf, rfl⟩
      rw [hmap] at hmem
      simpa using hmem
    simp [this]
  · simp [inv_mul_cancel₀ hℓ]

/-- The loophole in `fixed_equation`: for every `f₀` without compact support there is a functional `η` which satisfies
`IsLinearOnE r P` and has `dualNormE r P η = 0` (so it passes the moment hypothesis), but `η f₀ = 1`. -/
theorem s57_wild_functional_dualNormE (r : ℕ) (P : ℝ) (f₀ : Euc d → ℝ) (hf₀ : ¬ HasCompactSupport f₀) :
    ∃ η : (Euc d → ℝ) → ℝ, IsLinearOnE r P η ∧ dualNormE r P η = 0 ∧ η f₀ = 1 := by
  obtain ⟨η, hadd, hsmul, hcs, h1⟩ := s57_exists_wild_functional f₀ hf₀
  refine ⟨η, fun f g _ _ c => ⟨hadd f g, hsmul c f⟩, ?_, h1⟩
  unfold dualNormE
  refine le_antisymm (iSup_le fun f => iSup_le fun hf => ?_) bot_le
  rw [hcs f hf.2.1]
  simp

end HRS.Whole

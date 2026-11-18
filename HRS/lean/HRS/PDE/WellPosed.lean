import HRS.PDE.Energy
import HRS.PDE.Galerkin
import HRS.PDE.EnergyEstimate
import HRS.PDE.HsAnalysis
import HRS.PDE.GalerkinLimit
import HRS.PDE.Assembly
import HRS.PDE.Classical
import HRS.PDE.Uniqueness
import HRS.PDE.Stability
import HRS.PDE.ClassicalPart
import HRS.PDE.TimeRegTop
import HRS.PDE.TimeRegGen

/-!
# Torus PDE layer V: adjoint well-posedness on `𝕋^d` (Proposition 3.9), regime R2c
(Proposition 3.14, second half), and stability (Proposition 3.15)

Sources (HRS periodic main paper):
* Proposition 3.9 `B:thm:adjoint-torus` (lines 1739–1757): existence, uniqueness, the bound
  `B:eq:adjoint-torus-bound` with `Λ_m` of `B:eq:LambdaM`, and parts (a) (classical solution,
  propagator bounds), (b) (plane waves), (c) (time regularity);
* Proposition 3.14 `B:prop:R2c` (lines 1942–1944), second half: Proposition 3.9 holds in regime
  R2c (the energy half is `energy_form_estimate_R2c` in `Energy.lean`);
* Proposition 3.15 `B:prop:propagator-stability` (lines 1981–1986);
* the proof route of Proposition 3.9 (lines 1874–1941 and the proof of Prop 3.13): Galerkin
  (Fourier truncation) approximation, the uniform bound from the form estimate, compactness,
  passage to the limit, uniqueness in `C_w([0,t];H^1)`, strong continuity in `H^{m'}`.

## Representation

* The datum `φ ∈ H^m` is a coefficient family `φc` with `MemHs m φc`; a solution is
  `IsForwardSolution` (integrated coefficient equation) in `C_w([0,t];H^m)`
  (`WeakContinuousInHs`); `C([0,t];H^{m'})` is `ContinuousInHs m'` (real `m' < m` allowed).
* The constant `C` of `Λ_m` is quantified first (`∃ C > 0, ∀ D ν₀ T μ …`), depending only on
  `d, s, m, |M| (MB), Λ, ‖V‖_{C^{m+3}} (VB)`, the regime `R` (and `λ₀` inside `R2b`);
  `Λ_m = Regime.lambdaM R C ν₀ θ` displays the `ν₀` dependence of R3 (`AdjointData` holds the
  hypotheses after the quantifier, including `t ∈ (0,T]` and `ν ≥ ν₀` in R3).
* Part (a) uses `HRS.IsClassicalAdjointSolution` / `HRS.propagator` of the Setup file (with the
  cancellation convention).  The datum `φ` is taken continuous, so that the terminal condition
  `f(t,·) = φ` holds pointwise (`m ≥ m_* > d/2`).  The propagator bounds at levels `m' ≤ m` use
  the constants `Cs m'` of Proposition 3.9 at those levels (`Λ_{m'} = lambdaM R (Cs m') ν₀ θ`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Proposition 3.9: the main statement -/

/-! ### The proof route of Proposition 3.9 (auxiliary statements, sorried) -/

/-- The Galerkin generator `P_n 𝓛 P_n` (Fourier truncation to the box `|k_i| ≤ n`). -/
def galerkinGen (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) (F : Coeff d) : Coeff d :=
  truncCoeff n (forwardGen D ρ (truncCoeff n F))

/-- The Galerkin system of level `n`: `F_n(τ) = P_n φ + ∫_0^τ P_n 𝓛^{t-σ} P_n F_n(σ) dσ`, with
`F_n(τ)` a trigonometric polynomial of degree `≤ n` and continuous coefficients. -/
structure IsGalerkinSolution (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ) (n : ℕ) (φc : Coeff d)
    (F : ℝ → Coeff d) : Prop where
  trig : ∀ τ, IsTrigPoly n (F τ)
  cont : ∀ k, ContinuousOn (fun τ => F τ k) (Set.Icc 0 t)
  eq : ∀ k, ∀ τ ∈ Set.Icc 0 t,
    F τ k = truncCoeff n φc k + ∫ σ in (0 : ℝ)..τ, galerkinGen D (μ (t - σ)) n (F σ) k

/-- Step 1 (Galerkin, lines 1874–1876): the finite-dimensional linear system has a unique solution
(from `HRS.PDE.linear_ode_exists`/`linear_ode_unique`, continuity of the coefficients in time
from `CoeffHyp.cont`). -/
theorem galerkin_exists_unique (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (n : ℕ)
    (φc : Coeff d) :
    ∃ F : ℝ → Coeff d, IsGalerkinSolution D μ t n φc F ∧
      ∀ F', IsGalerkinSolution D μ t n φc F' → ∀ τ ∈ Set.Icc 0 t, F' τ = F τ := by
  obtain ⟨F, hF, hu⟩ := galSol_exists_unique hA.hμ ht D n φc
  exact ⟨F, ⟨hF.trig, hF.cont, hF.eq⟩, fun F' hF' => hu F' ⟨hF'.trig, hF'.cont, hF'.eq⟩⟩

/-- Step 2 (uniform bound, from `energy_form_estimate` and Grönwall): the Galerkin solutions with
real data satisfy `‖F_n(τ)‖_{H^m} ≤ e^{Λ_m τ}‖φ‖_{H^m}` uniformly in `n`, with the same `C` as in
`energy_form_estimate`. -/
theorem galerkin_uniform_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T) (n : ℕ)
      (φc : Coeff d) (_ : MemHs m φc) (_ : IsRealCoeff φc) (F : ℝ → Coeff d)
      (_ : IsGalerkinSolution D μ t n φc F),
      ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤
        Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * τ) * hsNorm m φc := by
  obtain ⟨C, hC, hmain⟩ := energy_form_estimate hd s hs0 hsd m R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA t ht n φc hφ hreal F hF τ hτ => ?_⟩
  have hF' : IsGalSol D μ t n φc F := ⟨hF.trig, hF.cont, hF.eq⟩
  obtain ⟨lam, q, hlq⟩ : ∃ (lam : Fin d → ℝ) (q : Fin d → Euc d),
      R.IsR2 → IsSymDiag D.M lam q := by
    by_cases hR : R.IsR2
    · obtain ⟨lam, q, h⟩ := exists_symDiag (regime_symNonpos hR hA.regime)
      exact ⟨lam, q, fun _ => h⟩
    · exact ⟨0, fun _ => 0, fun h => absurd h hR⟩
  exact galSol_bound hA.hμ hA.hV ht hreal hφ hF' (R.lambdaM C ν₀ (thetaOrder d s))
    (fun r hr G hG hGt =>
      (hmain D ν₀ T μ hA lam q hlq r hr n G hG hGt).2.trans
        (energyRHS_le hd R _ D m lam q (fun hR l => (hlq hR).nonneg l) (μ r) G)) τ hτ

/-- Steps 3–4 (compactness and passage to the limit, from
`HRS.PDE.exists_subseq_tendstoUniformlyOn_coord`): a uniformly `H^m`-bounded sequence of Galerkin
solutions with equicontinuous coefficients has a subsequence converging coordinatewise uniformly
on `[0,t]` to a forward solution in `C_w([0,t];H^m)` obeying the same bound. -/
theorem galerkin_limit (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d)
    (hφ : MemHs m φc) (F : ℕ → ℝ → Coeff d) (hF : ∀ n, IsGalerkinSolution D μ t n φc (F n))
    (B : ℝ) (hB : ∀ n, ∀ τ ∈ Set.Icc 0 t, hsNorm m (F n τ) ≤ B) :
    ∃ (ψ : ℕ → ℕ) (G : ℝ → Coeff d), StrictMono ψ ∧
      (∀ k, TendstoUniformlyOn (fun n τ => F (ψ n) τ k) (fun τ => G τ k) atTop (Set.Icc 0 t)) ∧
      IsForwardSolution D μ t φc G ∧ WeakContinuousInHs m G t ∧
      ∀ τ ∈ Set.Icc 0 t, hsNorm m (G τ) ≤ B :=
  galerkin_limit_core D μ m hm Λ VB T hA.hμ hA.hV t ht φc F (fun n => (hF n).trig)
    (fun n k => (hF n).cont k) (fun n k τ hτ => (hF n).eq k τ hτ) B hB

/-- Step 5 (uniqueness, lines 1936–1939): two forward solutions in `C_w([0,t];H^1)` with the same
datum coincide (energy identity for `P_n z` at level `m = 0` and Grönwall). -/
theorem forward_unique_H1 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d)
    (F₁ F₂ : ℝ → Coeff d) (h₁ : IsForwardSolution D μ t φc F₁) (w₁ : WeakContinuousInHs 1 F₁ t)
    (h₂ : IsForwardSolution D μ t φc F₂) (w₂ : WeakContinuousInHs 1 F₂ t) :
    ∀ τ ∈ Set.Icc 0 t, F₁ τ = F₂ τ :=
  forward_unique_core hd s hs0 hsd m R MB Λ VB D ν₀ T μ hA t ht φc F₁ F₂ h₁ w₁ h₂ w₂

/-- Strong continuity in lower norms (line 1740, `C([0,t];H^{m'})`, any `m' < m`): a weakly
continuous `H^m`-valued path is norm-continuous in `H^{m'}` for every real `m' < m` (compactness of
`H^m ↪ H^{m'}` on the torus; boundedness on `[0,t]` follows from weak continuity). -/
theorem forward_strong_continuity (m : ℝ) (t : ℝ) (F : ℝ → Coeff d)
    (hF : WeakContinuousInHs m F t) : ∀ m' : ℝ, m' < m → ContinuousInHs m' F t :=
  continuousInHs_of_weak hF

/-! ### Proposition 3.9, main statement (assembly of the proof route above) -/

/-- Proposition 3.9 `B:thm:adjoint-torus` (lines 1739–1751), main statement: let `0 ≤ s < d`,
`m ≥ 1`, and assume `B:eq:coeff-hypothesis` and one of the regimes (`AdjointData`).  There is
`C > 0` (depending only on `d, s, m, |M|, Λ, ‖V‖_{C^{m+3}}`, the regime, and `λ₀` in R2b) such
that for every `t ∈ (0,T]` and `φ ∈ H^m(𝕋^d)` there is a unique `F ∈ C_w([0,t];H^m)` solving
`B:eq:adjoint-forward` in the distributional sense; it lies in `C([0,t];H^{m'})` for every
`m' < m`, and `‖F(τ)‖_{H^m} ≤ e^{Λ_m τ}‖φ‖_{H^m}` for `τ ∈ [0,t]` (`B:eq:adjoint-torus-bound`),
`Λ_m = C` in R1/R2 (uniformly in `β ∈ (0,∞]`) and `C(1+ν₀^{-θ/(2-θ)})` in R3 (`B:eq:LambdaM`). -/
theorem adjoint_torus (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T)
      (φc : Coeff d) (_ : MemHs m φc),
      (∃ F : ℝ → Coeff d, IsForwardSolution D μ t φc F ∧ WeakContinuousInHs m F t ∧
        (∀ m' : ℝ, m' < m → ContinuousInHs m' F t) ∧
        ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤
          Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * τ) * hsNorm m φc) ∧
      ∀ F₁ F₂ : ℝ → Coeff d, IsForwardSolution D μ t φc F₁ → WeakContinuousInHs m F₁ t →
        IsForwardSolution D μ t φc F₂ → WeakContinuousInHs m F₂ t →
        ∀ τ ∈ Set.Icc 0 t, F₁ τ = F₂ τ := by
  obtain ⟨C, hC, hmain⟩ := galerkin_uniform_bound hd s hs0 hsd m R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA t ht φc hφ => ?_⟩
  set lam := R.lambdaM C ν₀ (thetaOrder d s) with hlam
  have hex : ∀ n, ∃ F : ℝ → Coeff d, IsGalSol D μ t n φc F ∧
      ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤ Real.exp (lam * τ) * hsNorm m φc := fun n =>
    galSol_complex_exists hA.hμ hA.hV ht (fun τ => Real.exp (lam * τ))
      (fun τ => (Real.exp_pos _).le)
      (fun φ' h1 h2 n F hF τ hτ =>
        hmain D ν₀ T μ hA t ht n φ' h1 h2 F ⟨hF.trig, hF.cont, hF.eq⟩ τ hτ) n φc hφ
  choose F hF hFb using hex
  have hF' : ∀ n, IsGalerkinSolution D μ t n φc (F n) := fun n =>
    ⟨(hF n).trig, (hF n).cont, (hF n).eq⟩
  have hB : ∀ n, ∀ τ ∈ Set.Icc 0 t, hsNorm m (F n τ) ≤ Real.exp (|lam| * t) * hsNorm m φc := by
    intro n τ hτ
    refine (hFb n τ hτ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (Real.sqrt_nonneg _))
    calc lam * τ ≤ |lam| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
      _ ≤ |lam| * t := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
  obtain ⟨ψ, G, hψ, hconv, hGsol, hGw, -⟩ := galerkin_limit hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ
    hA t ht φc hφ F hF' _ hB
  have hGb : ∀ τ ∈ Set.Icc 0 t, hsNorm m (G τ) ≤ Real.exp (lam * τ) * hsNorm m φc := by
    intro τ hτ
    have hsq : ∀ c : Coeff d, hsNorm m c ^ 2 = hsNormSq m c := fun c =>
      Real.sq_sqrt (hsNormSq_nonneg _ _)
    have := (bound_of_coord_limit (m := (m : ℝ)) (Fn := fun n => F (ψ n)) hconv hτ
      ((Real.exp (lam * τ) * hsNorm m φc) ^ 2) (fun n => isTrigPoly_memHs ((hF _).trig τ) _)
      (fun n => by
        rw [← hsq]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hFb _ τ hτ) 2)).2
    rw [← hsq] at this
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) two_ne_zero).1 this
  refine ⟨⟨G, hGsol, hGw, forward_strong_continuity (m : ℝ) t G hGw, hGb⟩, ?_⟩
  intro F₁ F₂ h₁ w₁ h₂ w₂
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact forward_unique_H1 hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φc F₁ F₂ h₁
    (weakContinuousInHs_mono hm1 w₁) h₂ (weakContinuousInHs_mono hm1 w₂)

/-! ### Proposition 3.14, second half -/

/-- Proposition 3.14 `B:prop:R2c` (lines 1942–1944), consequence: Proposition 3.9 holds in regime
R2c (`d-2 < s ≤ d-1`, `S ≤ 0`, no lower bound on `μ`) with `Λ_m = C` uniformly in `β ∈ (0,∞]`.
This is the instance `R = .R2c` of `adjoint_torus` (`lambdaM .R2c C ν₀ θ = C`). -/
theorem adjoint_torus_R2c (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s)
    (hs2 : s ≤ (d : ℝ) - 1)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m .R2c MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T)
      (φc : Coeff d) (_ : MemHs m φc),
      (∃ F : ℝ → Coeff d, IsForwardSolution D μ t φc F ∧ WeakContinuousInHs m F t ∧
        (∀ m' : ℝ, m' < m → ContinuousInHs m' F t) ∧
        ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤ Real.exp (C * τ) * hsNorm m φc) ∧
      ∀ F₁ F₂ : ℝ → Coeff d, IsForwardSolution D μ t φc F₁ → WeakContinuousInHs m F₁ t →
        IsForwardSolution D μ t φc F₂ → WeakContinuousInHs m F₂ t →
        ∀ τ ∈ Set.Icc 0 t, F₁ τ = F₂ τ := by
  have hsd : s < d := by
    have : (0 : ℝ) < 1 := one_pos
    linarith
  obtain ⟨C, hC, h⟩ := adjoint_torus hd s hs0 hsd m hm .R2c MB Λ VB
  exact ⟨C, hC, fun D ν₀ T μ hA t ht φc hφ => h D ν₀ T μ hA t ht φc hφ⟩

/-- The propagator coefficient path `propagatorCoeff D μ m t φc` is, under the hypotheses of
Proposition 3.9 and for `φc ∈ H^m`, the forward solution in `C_w([0,t];H^m)` of `adjoint_torus`
(its existence and uniqueness clauses), with the bound `B:eq:adjoint-torus-bound`
(same constant `C` as `adjoint_torus`). -/
theorem propagatorCoeff_spec (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T)
      (φc : Coeff d) (_ : MemHs m φc),
      IsForwardSolution D μ t φc (propagatorCoeff D μ m t φc) ∧
      WeakContinuousInHs m (propagatorCoeff D μ m t φc) t ∧
      ∀ τ ∈ Set.Icc 0 t, hsNorm m (propagatorCoeff D μ m t φc τ) ≤
        Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * τ) * hsNorm m φc := by
  obtain ⟨C, hC, h⟩ := adjoint_torus hd s hs0 hsd m hm R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA t ht φc hφ => ?_⟩
  obtain ⟨⟨F, hF, hw, -, hb⟩, huniq⟩ := h D ν₀ T μ hA t ht φc hφ
  have hex : ∃ F, IsForwardSolution D μ t φc F ∧ WeakContinuousInHs (m : ℝ) F t := ⟨F, hF, hw⟩
  have hdef : propagatorCoeff D μ m t φc = hex.choose := by
    unfold propagatorCoeff; simp only [hex, dite_true]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  rw [hdef]
  refine ⟨h1, h2, fun τ hτ => ?_⟩
  rw [huniq _ F h1 h2 hF hw τ hτ]
  exact hb τ hτ

/-! ### Proposition 3.15 -/

/-- Proposition 3.15 `B:prop:propagator-stability` (lines 1981–1986): for `a ∈ {1,2}` let
`(ν_a, μ_a)` satisfy the hypotheses of Proposition 3.9 at level `m+2` with a common regime and
common constants (same `R, MB, Λ, VB, ν₀, T`, same `M` and `V`), with propagators `U_a^{r,t}`.
Then for `φ ∈ H^{m+2}` and `0 ≤ r ≤ t ≤ T`,
`‖(U_1^{r,t} - U_2^{r,t})φ‖_{H^m} ≤ C (t-r) e^{Λ_{m+2}(t-r)} (|ν₁-ν₂| + sup_{[0,T]}‖μ₁-μ₂‖_{C^{m+2}}) ‖φ‖_{H^{m+2}}`;
`C'` is the constant of `Λ_{m+2}`, and `δ ≥ sup_{[0,T]}‖μ₁-μ₂‖_{C^{m+2}}` any bound. -/
theorem propagator_stability (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ (D₁ D₂ : DynData d) (ν₀ T : ℝ) (μ₁ μ₂ : ℝ → Torus d → ℝ)
        (_ : AdjointData s (m + 2) R MB Λ VB D₁ ν₀ T μ₁)
        (_ : AdjointData s (m + 2) R MB Λ VB D₂ ν₀ T μ₂) (_ : D₁.M = D₂.M) (_ : D₁.V = D₂.V)
        (δ : ℝ) (_ : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm (m + 2) (μ₁ r - μ₂ r) ≤ δ)
        (φc : Coeff d) (_ : MemHs (m + 2) φc) (r t : ℝ) (_ : 0 ≤ r) (_ : r ≤ t) (_ : t ≤ T),
        hsNorm m (propagatorCoeff D₁ μ₁ (m + 2) t φc (t - r) -
            propagatorCoeff D₂ μ₂ (m + 2) t φc (t - r)) ≤
          C * (t - r) * Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * (t - r)) *
            (|D₁.invβ - D₂.invβ| + δ) * hsNorm (m + 2) φc := by
  obtain ⟨C₂, hC₂, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd (m + 2) (by omega) R MB Λ VB
  obtain ⟨C, C', hC, hC', hcore⟩ := StabAux.stability_core hd s hs0 hsd m R MB Λ VB C₂ hC₂
  refine ⟨C, C', hC, hC', ?_⟩
  intro D₁ D₂ ν₀ T μ₁ μ₂ hA₁ hA₂ hM hV δ hδ φc hφ r t hr hrt htT
  have hcast : (((m + 2 : ℕ)) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rcases (hr.trans hrt).eq_or_lt with h0 | ht0
  · subst h0
    have hz : (0 : ℝ) - r = 0 := by linarith
    have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by
      have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    rw [hz, StabAux.propagatorCoeff_zero D₁ μ₁ ((m : ℝ) + 2) φc hφ hm2,
      StabAux.propagatorCoeff_zero D₂ μ₂ ((m : ℝ) + 2) φc hφ hm2, sub_self]
    simp [hsNorm, hsNormSq]
  · have ht : t ∈ Set.Ioc 0 T := ⟨ht0, htT⟩
    have hφ' : MemHs (((m + 2 : ℕ)) : ℝ) φc := by rw [hcast]; exact hφ
    obtain ⟨s1, w1, b1⟩ := hspec D₁ ν₀ T μ₁ hA₁ t ht φc hφ'
    obtain ⟨s2, w2, b2⟩ := hspec D₂ ν₀ T μ₂ hA₂ t ht φc hφ'
    rw [hcast] at s1 s2 w1 w2 b1 b2
    exact hcore D₁ D₂ ν₀ T μ₁ μ₂ hA₁ hA₂ hM hV δ hδ φc hφ t ht _ _ s1 w1 s2 w2 b1 b2 (t - r)
      (by linarith) (by linarith)

/-- Proposition 3.9(c) (line 1756), time regularity: `∂_τF ∈ C([0,t];H^{m-2})`: the forward
generator `τ ↦ 𝓛^{t-τ}F(τ)` is norm-continuous in `H^{m-2}` and is the `H^{m-2}`-derivative of `F`
(difference quotients converge in `H^{m-2}`, one-sided at the endpoints). -/
theorem adjoint_torus_time_regularity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d)
    (hφ : MemHs m φc) :
    ContinuousInHs ((m : ℝ) - 2)
      (fun τ => forwardGen D (μ (t - τ)) (propagatorCoeff D μ m t φc τ)) t ∧
    ∀ τ ∈ Set.Icc 0 t, Tendsto (fun τ' => hsNorm ((m : ℝ) - 2) (fun k =>
        (propagatorCoeff D μ m t φc τ' k - propagatorCoeff D μ m t φc τ k) / ((τ' - τ : ℝ) : ℂ) -
          forwardGen D (μ (t - τ)) (propagatorCoeff D μ m t φc τ) k))
      (𝓝[Set.Icc 0 t \ {τ}] τ) (𝓝 0) := by
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨hF, hw, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  exact forward_time_regularity_core hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φc hφ _ hF hw
    (fun hν => forward_continuousInHs_top hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA hν t ht φc hφ
      _ hF hw)

/-- Proposition 3.9(b) (line 1755), plane waves, coefficient level (all `m ≥ 1`): for `k ∈ ℤ^d`,
`‖U^{r,t}e_k‖_{H^m} ≤ e^{Λ_m(t-r)} (2π⟨k⟩)^m` (with `U^{r,t}e_k` the forward solution at level `m`
with datum `δ_k`; the bound as stated in the source is weaker than `B:eq:adjoint-torus-bound`
applied to `‖e_k‖_{H^m} = ⟨k⟩^m`). -/
theorem adjoint_torus_planewave (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T) (k : Lattice d),
      ∀ r ∈ Set.Icc 0 t,
        hsNorm m (propagatorCoeff D μ m t (deltaCoeff k) (t - r)) ≤
          Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * (t - r)) * (2 * Real.pi * Lattice.jp k) ^ m := by
  obtain ⟨C, hC, h⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA t ht k r hr => ?_⟩
  have hφ : MemHs (m : ℝ) (deltaCoeff k) := by
    refine summable_of_ne_finset_zero (s := {k}) fun j hj => ?_
    have : j ≠ k := by simpa using hj
    simp [deltaCoeff, this]
  obtain ⟨-, -, hb⟩ := h D ν₀ T μ hA t ht (deltaCoeff k) hφ
  have hτ : t - r ∈ Set.Icc 0 t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine (hb (t - r) hτ).trans ?_
  rw [hsNorm_deltaCoeff]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hj : (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ ((m : ℝ) / 2) = Lattice.jp k ^ m := by
    unfold Lattice.jp
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast
      ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (1 / 2 : ℝ)) m, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hj, mul_pow]
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  exact le_mul_of_one_le_left (pow_nonneg (Torus.jp_pos k).le _) (one_le_pow₀ h2pi)

/-- A classical adjoint solution (Definition 3.5) yields, through its coefficients
`τ ↦ (f(t-τ,·))^`, a forward solution in `C([0,t];H^2) ⊂ C_w([0,t];H^1)` with datum `φ̂`
(integration by parts against `e_k`, `TorusCalculus.funFourierCoeff_partialDeriv`,
`convGradConv_coeff`).  `V ∈ C¹` is needed: otherwise `Torus.grad V` is the junk value `0` while
`driftCoeff` uses the Fourier derivative of `V`. -/
theorem classical_toCoeff_isForwardSolution (hd : 1 ≤ d) (D : DynData d)
    (hV : Torus.IsCk 1 D.V)
    (μ : ℝ → Torus d → ℝ) (t : ℝ) (ht : 0 < t) (hμ : ∀ r ∈ Set.Icc 0 t, Torus.IsCk 1 (μ r))
    (φ : Torus d → ℝ) (f : ℝ → Torus d → ℝ) (hf : IsClassicalAdjointSolution D μ t φ f) :
    IsForwardSolution D μ t (coeffOf φ) (fun τ => coeffOf (f (t - τ))) ∧
      ContinuousInHs 2 (fun τ => coeffOf (f (t - τ))) t :=
  ClassicalAux.classicalToCoeff_aux D (ClassicalAux.convKernelFacts hd D) hV μ t hμ φ f hf

/-- Uniqueness of classical adjoint solutions (Definition 3.5) under the hypotheses of
Proposition 3.9 at any level `m ≥ 1` (a classical solution is a `C_w([0,t];H^1)` solution of the
forward equation, `classical_toCoeff_isForwardSolution`). -/
theorem classical_adjoint_unique (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φ : Torus d → ℝ)
    (f₁ f₂ : ℝ → Torus d → ℝ) (h₁ : IsClassicalAdjointSolution D μ t φ f₁)
    (h₂ : IsClassicalAdjointSolution D μ t φ f₂) : ∀ r ∈ Set.Icc 0 t, f₁ r = f₂ r := by
  intro r hr
  have hμ1 : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 1 (μ r) := fun r hr =>
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
      (hA.hμ.smooth r ⟨hr.1, hr.2.trans ht.2⟩)
  have hV1 : Torus.IsCk 1 D.V :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
  have hK := ClassicalAux.convKernelFacts hd D
  obtain ⟨hs₁, -⟩ := ClassicalAux.classicalToCoeff_aux D hK hV1 μ t hμ1 φ f₁ h₁
  obtain ⟨hs₂, -⟩ := ClassicalAux.classicalToCoeff_aux D hK hV1 μ t hμ1 φ f₂ h₂
  have w₁ := weakContinuousInHs_mono (by norm_num : (1 : ℝ) ≤ 2)
    (ClassicalAux.weakContinuousInHs_two h₁)
  have w₂ := weakContinuousInHs_mono (by norm_num : (1 : ℝ) ≤ 2)
    (ClassicalAux.weakContinuousInHs_two h₂)
  have hu := forward_unique_H1 hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht (coeffOf φ) _ _ hs₁ w₁
    hs₂ w₂ (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  simp only [sub_sub_cancel] at hu
  exact ClassicalAux.eq_of_coeffOf_eq (ClassicalAux.continuous_f_apply h₁ hr)
    (ClassicalAux.continuous_f_apply h₂ hr) hu

/-! ### The classical part of Proposition 3.9 (helpers) -/

namespace ClassicalPart

open ClassicalAux in
/-- For real data, the propagator coefficient path is real. -/
theorem propagatorCoeff_real (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d)
    (hφ : MemHs m φc) (hre : IsRealCoeff φc) :
    ∀ τ ∈ Set.Icc 0 t, IsRealCoeff (propagatorCoeff D μ m t φc τ) := by
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hρ : ∀ σ ∈ Set.Icc (0 : ℝ) t, IsRealCoeff (coeffOf (μ (t - σ))) := fun σ hσ =>
    isRealCoeff_coeffOf_density hA.hμ ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hsol' := isForwardSolution_reflConj hsol ht.1.le hρ (isRealCoeff_coeffOf_V hA.hV)
  rw [(isRealCoeff_iff_reflConj φc).1 hre] at hsol'
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hu := forward_unique_H1 hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φc _ _ hsol'
    (weakContinuousInHs_mono hm1 (weakContinuousInHs_reflConj hw)) hsol
    (weakContinuousInHs_mono hm1 hw)
  intro τ hτ
  rw [isRealCoeff_iff_reflConj]
  exact hu τ hτ

/-- The propagator coefficient paths at levels `m' ≤ m` agree. -/
theorem propagatorCoeff_level (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m' m : ℕ)
    (hm' : 1 ≤ m') (hmm : m' ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ)
    (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d) (hφ : MemHs m φc) :
    ∀ τ ∈ Set.Icc 0 t, propagatorCoeff D μ m' t φc τ = propagatorCoeff D μ m t φc τ := by
  have hA' := adjointData_mono hA hmm
  have hmm' : (m' : ℝ) ≤ m := by exact_mod_cast hmm
  have hφ' : MemHs (m' : ℝ) φc := hφ.mono hmm'
  obtain ⟨C₁, -, h₁⟩ := propagatorCoeff_spec hd s hs0 hsd m' hm' R MB Λ VB
  obtain ⟨C₂, -, h₂⟩ := propagatorCoeff_spec hd s hs0 hsd m (hm'.trans hmm) R MB Λ VB
  obtain ⟨hs1, hw1, -⟩ := h₁ D ν₀ T μ hA' t ht φc hφ'
  obtain ⟨hs2, hw2, -⟩ := h₂ D ν₀ T μ hA t ht φc hφ
  have hm1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'
  exact forward_unique_H1 hd s hs0 hsd m' hm' R MB Λ VB D ν₀ T μ hA' t ht φc _ _ hs1
    (weakContinuousInHs_mono hm1 hw1) hs2
    (weakContinuousInHs_mono hm1 (weakContinuousInHs_mono hmm' hw2))


open ClassicalAux in
/-- The classical solution built from the forward solution. -/
theorem classical_exists (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ)
    (ht : t ∈ Set.Ioc 0 T) (φ : Torus d → ℝ) (hφc : Continuous φ) (hφ : MemSobolev m φ) :
    IsClassicalAdjointSolution D μ t φ
      (fun r x => toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) x) := by
  have hm3 := one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have hmd : (d : ℝ) / 2 < m := by
    obtain ⟨m'', h1, h2⟩ := exists_mid hm
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (m : ℝ) φ hφ
  have hre : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (integrable_of_continuous hφc)
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm1 R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht (coeffOf φ) hcm
  have hreal := propagatorCoeff_real hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA t ht (coeffOf φ)
    hcm hre
  set F := propagatorCoeff D μ m t (coeffOf φ) with hF
  obtain ⟨m'', hm''1, hm''2⟩ := exists_mid hm
  have hcont : ContinuousInHs m'' F t := forward_strong_continuity (m : ℝ) t F hw m'' hm''2
  obtain ⟨hgws, hgc, hder, hjoint⟩ := gen_path_facts hA hmd ht hsol hreal hm''1 hcont
  have hmemF : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs (m : ℝ) (F τ) := hw.1
  have hWS0 : ∀ τ ∈ Set.Icc (0 : ℝ) t, WS 0 (F τ) := fun τ hτ => ws0_of_memHs hmd (hmemF τ hτ)
  obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := d) 2 (m : ℝ) (by
    have := exists_mid (d := d) hm
    obtain ⟨m3, h1, h2⟩ := this
    push_cast
    linarith)
  have hCk2 : ∀ τ ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (toFun (F τ)) := fun τ hτ =>
    (hC2 _ (hmemF τ hτ) (hreal τ hτ)).1
  have hK := convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V :=
    isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
  have hρ1 : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 1 (μ r) := fun r hr =>
    isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
      (hA.hμ.smooth r ⟨hr.1, hr.2.trans ht.2⟩)
  have hbg : ∀ r ∈ Set.Icc (0 : ℝ) t, backwardGenerator D (μ r) (toFun (F (t - r))) =
      toFun (forwardGen D (μ r) (F (t - r))) := by
    intro r hr
    have hτ := mem_Icc_sub t hr
    have h1 := hgws (t - r) hτ
    rw [sub_sub_cancel] at h1
    exact backwardGenerator_eq_toFun D hK hV1 (hρ1 r hr) (hreal _ hτ) (hWS0 _ hτ) (hCk2 _ hτ)
      h1.2 h1.1
  refine ⟨fun r hr => hCk2 _ (mem_Icc_sub t hr), fun j hj => ?_, ?_, ?_, ?_⟩
  · refine continuous_iteratedFDeriv_toFun (X := Set.Icc (0 : ℝ) t) (fun x => F (t - x.1)) j
      m'' (by
        have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
        linarith) (fun x => hreal _ (mem_Icc_sub t x.2)) (fun x => hcont.1 _ (mem_Icc_sub t x.2))
      (fun x₀ => ?_)
    exact tendsto_reflect (f := fun τ => hsNorm m'' (F τ - F (t - (x₀ : ℝ))))
      (hcont.2 _ (mem_Icc_sub t x₀.2))
  · funext x
    show toFun (F (t - t)) x = φ x
    have h0 : F (t - t) = coeffOf φ := by
      rw [sub_self]
      funext k
      rw [hsol.eq k 0 ⟨le_rfl, ht.1.le⟩]
      simp
    rw [h0]
    have hs0' := (WS_zero_iff _).1 (ws0_of_memHs hmd hcm)
    have := eq_of_coeffOf_eq (continuous_toFun _ hs0') hφc (coeffOf_toFun _ hre hs0')
    exact congrFun this x
  · intro x r hr
    have hτ : t - r ∈ Set.Ioo (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h1 := hder x (t - r) hτ
    have h2 : HasDerivAt (fun r' : ℝ => t - r') (-1) r := (hasDerivAt_id r).const_sub t
    have h3 := h1.scomp r h2
    refine h3.congr_deriv ?_
    rw [hbg r (Set.Ioo_subset_Icc_self hr), sub_sub_cancel]
    simp
  · have hg : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
        ((⟨t - p.1.1, mem_Icc_sub t p.1.2⟩ : Set.Icc (0 : ℝ) t), p.2) :=
      (Continuous.subtype_mk (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
        fun p => mem_Icc_sub t p.1.2).prodMk continuous_snd
    have hc := hjoint.comp hg
    refine hc.congr fun p => ?_
    rw [hbg p.1.1 p.1.2]
    show toFun (forwardGen D (μ (t - (t - p.1.1))) (F (t - p.1.1))) p.2 = _
    rw [sub_sub_cancel]

/-- The propagator is the classical solution built from the forward solution. -/
theorem propagator_eq_toFun (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ)
    (ht : t ∈ Set.Ioc 0 T) (φ : Torus d → ℝ) (hφc : Continuous φ) (hφ : MemSobolev m φ) :
    ∀ r ∈ Set.Icc 0 t, propagator D μ r t φ =
      fun x => toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) x := by
  have hm1 : 1 ≤ m := by have := one_le_of_mStar hm; omega
  have hex := classical_exists hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ hφc hφ
  intro r hr
  have hE : ∃ f, IsClassicalAdjointSolution D μ t φ f := ⟨_, hex⟩
  unfold propagator
  rw [dif_pos hE]
  exact classical_adjoint_unique hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA t ht φ _ _
    hE.choose_spec hex r hr

end ClassicalPart

/-! ### Proposition 3.9(a)–(c): the classical solution and plane waves -/

/-- Proposition 3.9(a) (lines 1753–1754): if `m ≥ m_*`, then `f(r,x) := F(t-r,x)` is a classical
adjoint solution (Definition 3.5), `f^r = U^{r,t}φ` (`HRS.propagator`), and the propagator satisfies
`‖U^{r,t}φ‖_{H^{m'}} ≤ e^{Λ_{m'}(t-r)}‖φ‖_{H^{m'}}` for every integer `1 ≤ m' ≤ m` and
`‖U^{r,t}φ‖_{C²_b} ≤ C e^{Λ_{m_*}(t-r)} ‖φ‖_{H^{m_*}}`.  `Cs m'` is the constant of
Proposition 3.9 at level `m'`.  The datum `φ` is the continuous representative of its `H^m` class. -/
theorem adjoint_torus_classical (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) :
    ∃ (C : ℝ) (Cs : ℕ → ℝ), 0 < C ∧ (∀ m', 0 < Cs m') ∧
      ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
        (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T)
        (φ : Torus d → ℝ) (_ : Continuous φ) (_ : MemSobolev m φ),
        IsClassicalAdjointSolution D μ t φ
          (fun r x => toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) x) ∧
        (∀ r ∈ Set.Icc 0 t, propagator D μ r t φ =
          fun x => toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) x) ∧
        (∀ m' : ℕ, 1 ≤ m' → m' ≤ m → ∀ r ∈ Set.Icc 0 t,
          MemSobolev m' (propagator D μ r t φ) ∧
          sobolevNorm m' (propagator D μ r t φ) ≤
            Real.exp (R.lambdaM (Cs m') ν₀ (thetaOrder d s) * (t - r)) * sobolevNorm m' φ) ∧
        ∀ r ∈ Set.Icc 0 t, Torus.cbNorm 2 (propagator D μ r t φ) ≤
          C * Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
            sobolevNorm (mStar d) φ := by
  have hspec : ∀ m' : ℕ, ∃ Cm : ℝ, 0 < Cm ∧ (1 ≤ m' → ∀ (D : DynData d) (ν₀ T : ℝ)
      (μ : ℝ → Torus d → ℝ) (_ : AdjointData s m' R MB Λ VB D ν₀ T μ) (t : ℝ)
      (_ : t ∈ Set.Ioc 0 T) (φc : Coeff d) (_ : MemHs m' φc),
      IsForwardSolution D μ t φc (propagatorCoeff D μ m' t φc) ∧
      WeakContinuousInHs m' (propagatorCoeff D μ m' t φc) t ∧
      ∀ τ ∈ Set.Icc 0 t, hsNorm m' (propagatorCoeff D μ m' t φc τ) ≤
        Real.exp (R.lambdaM Cm ν₀ (thetaOrder d s) * τ) * hsNorm m' φc) := by
    intro m'
    by_cases h : 1 ≤ m'
    · obtain ⟨C, hC, h'⟩ := propagatorCoeff_spec hd s hs0 hsd m' h R MB Λ VB
      exact ⟨C, hC, fun _ => h'⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose Cs hCs hCsspec using hspec
  have hmstar : (d : ℝ) / 2 + (2 : ℕ) < (mStar d : ℝ) := by
    unfold mStar
    push_cast
    have := Nat.lt_floor_add_one ((d : ℝ) / 2)
    linarith
  obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := d) 2 (mStar d : ℝ) hmstar
  refine ⟨max C2 1, Cs, lt_max_of_lt_right one_pos, hCs, ?_⟩
  intro D ν₀ T μ hA t ht φ hφc hφ
  have hm3 := ClassicalPart.one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have hmd : (d : ℝ) / 2 < m := by
    obtain ⟨m'', h1, h2⟩ := ClassicalPart.exists_mid (d := d) hm
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hcls := ClassicalPart.classical_exists hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ
    hφc hφ
  have hpe := ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ
    hφc hφ
  refine ⟨hcls, hpe, ?_, ?_⟩
  all_goals
    obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (m : ℝ) φ hφ
    have hre : IsRealCoeff (coeffOf φ) :=
      isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφc)
    have hreal := ClassicalPart.propagatorCoeff_real hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA t ht
      (coeffOf φ) hcm hre
    obtain ⟨hsol, hw, -⟩ := hCsspec m hm1 D ν₀ T μ hA t ht (coeffOf φ) hcm
    have hs : ∀ τ ∈ Set.Icc (0 : ℝ) t, Summable fun k => ‖propagatorCoeff D μ m t (coeffOf φ) τ k‖ :=
      fun τ hτ => summable_norm_of_memHs (m : ℝ) hmd _ (hw.1 τ hτ)
    have key : ∀ m' : ℕ, 1 ≤ m' → m' ≤ m → ∀ r ∈ Set.Icc (0 : ℝ) t,
        MemHs (m' : ℝ) (propagatorCoeff D μ m t (coeffOf φ) (t - r)) ∧
        hsNorm (m' : ℝ) (propagatorCoeff D μ m t (coeffOf φ) (t - r)) ≤
          Real.exp (R.lambdaM (Cs m') ν₀ (thetaOrder d s) * (t - r)) * sobolevNorm (m' : ℝ) φ := by
      intro m' hm'1 hm'm r hr
      have hτ := ClassicalAux.mem_Icc_sub t hr
      have hmm' : (m' : ℝ) ≤ m := by exact_mod_cast hm'm
      have hcm' : MemHs (m' : ℝ) (coeffOf φ) := hcm.mono hmm'
      refine ⟨(hw.1 _ hτ).mono hmm', ?_⟩
      have hA' := ClassicalPart.adjointData_mono hA hm'm
      obtain ⟨-, -, hb⟩ := hCsspec m' hm'1 D ν₀ T μ hA' t ht (coeffOf φ) hcm'
      rw [← ClassicalPart.propagatorCoeff_level hd s hs0 hsd m' m hm'1 hm'm R MB Λ VB D ν₀ T μ
        hA t ht (coeffOf φ) hcm _ hτ]
      have hSφ : MemSobolev (m' : ℝ) φ :=
        memSobolev_of_memHs _ φ (ClassicalAux.memLp_two_of_continuous hφc) hcm'
      rw [ClassicalPart.sobolevNorm_eq_hsNorm hSφ]
      exact hb _ hτ
  · intro m' hm'1 hm'm r hr
    have hτ := ClassicalAux.mem_Icc_sub t hr
    obtain ⟨hmem, hbd⟩ := key m' hm'1 hm'm r hr
    have hpe' : propagator D μ r t φ = toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) :=
      hpe r hr
    rw [hpe']
    obtain ⟨hMS, hEq⟩ := ClassicalPart.memSobolev_toFun (hs _ hτ) hmem (hreal _ hτ)
    refine ⟨hMS, ?_⟩
    rw [hEq]
    exact hbd
  · intro r hr
    have hτ := ClassicalAux.mem_Icc_sub t hr
    obtain ⟨hmem, hbd⟩ := key (mStar d) (by have := ClassicalPart.three_le_mStar d; omega) hm r hr
    have hpe' : propagator D μ r t φ = toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) :=
      hpe r hr
    rw [hpe']
    have h1 := (hC2 _ hmem (hreal _ hτ)).2
    refine h1.trans ?_
    have hnn : 0 ≤ Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
        sobolevNorm (mStar d : ℝ) φ := by
      have h0 : 0 ≤ hsNorm (mStar d : ℝ) (propagatorCoeff D μ m t (coeffOf φ) (t - r)) :=
        Real.sqrt_nonneg _
      exact h0.trans hbd
    have h0 : 0 ≤ hsNorm (mStar d : ℝ) (propagatorCoeff D μ m t (coeffOf φ) (t - r)) :=
      Real.sqrt_nonneg _
    have hmax : 0 ≤ max C2 1 := le_trans zero_le_one (le_max_right _ _)
    calc C2 * hsNorm (mStar d : ℝ) (propagatorCoeff D μ m t (coeffOf φ) (t - r))
        ≤ max C2 1 * hsNorm (mStar d : ℝ) (propagatorCoeff D μ m t (coeffOf φ) (t - r)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ max C2 1 * (Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
            sobolevNorm (mStar d : ℝ) φ) := mul_le_mul_of_nonneg_left hbd hmax
      _ = _ := by ring

/-- Proposition 3.9(b) (line 1755), real and imaginary parts and the `C²` consequence: for
`m ≥ m_*`, `‖U^{r,t}(cos 2πk·x)‖_{H^m}`, `‖U^{r,t}(sin 2πk·x)‖_{H^m} ≤ e^{Λ_m(t-r)}(2π⟨k⟩)^m`,
and `‖∇^{⊗j}U^{r,t}e_k‖_{L^∞} ≤ C e^{Λ_{m_*}(t-r)} ⟨k⟩^{m_*}` for `j ≤ 2` (for both parts;
`C'` is the constant of Proposition 3.9 at level `m_*`). -/
theorem adjoint_torus_planewave_classical (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) :
    ∃ C C' C'' : ℝ, 0 < C ∧ 0 < C' ∧ 0 < C'' ∧
      ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
        (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T) (k : Lattice d),
        ∀ r ∈ Set.Icc 0 t,
          (sobolevNorm m (propagator D μ r t (Torus.cosMode k)) ≤
              Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * (t - r)) *
                (2 * Real.pi * Lattice.jp k) ^ m ∧
            sobolevNorm m (propagator D μ r t (Torus.sinMode k)) ≤
              Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * (t - r)) *
                (2 * Real.pi * Lattice.jp k) ^ m) ∧
          ∀ j ≤ 2, ∀ x : Euc d,
            ‖iteratedFDeriv ℝ j (Torus.lift (propagator D μ r t (Torus.cosMode k))) x‖ ≤
                C'' * Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * (t - r)) *
                  Lattice.jp k ^ mStar d ∧
            ‖iteratedFDeriv ℝ j (Torus.lift (propagator D μ r t (Torus.sinMode k))) x‖ ≤
                C'' * Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * (t - r)) *
                  Lattice.jp k ^ mStar d := by
  obtain ⟨C₀, Cs, hC₀, hCs, h⟩ := adjoint_torus_classical hd s hs0 hsd m hm R MB Λ VB
  have hm3 := ClassicalPart.one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have h2pi : 0 < 2 * Real.pi := by positivity
  refine ⟨Cs m, Cs (mStar d), C₀ * (2 * Real.pi) ^ mStar d, hCs m, hCs _, by positivity, ?_⟩
  intro D ν₀ T μ hA t ht k r hr
  -- the generic estimate for a continuous test function with `sobolev` bounds
  have gen : ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev (m : ℝ) ψ →
      MemSobolev (mStar d : ℝ) ψ →
      sobolevNorm (m : ℝ) ψ ≤ (2 * Real.pi * Lattice.jp k) ^ m →
      sobolevNorm (mStar d : ℝ) ψ ≤ (2 * Real.pi * Lattice.jp k) ^ mStar d →
      sobolevNorm (m : ℝ) (propagator D μ r t ψ) ≤
          Real.exp (R.lambdaM (Cs m) ν₀ (thetaOrder d s) * (t - r)) *
            (2 * Real.pi * Lattice.jp k) ^ m ∧
        ∀ j ≤ 2, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (Torus.lift (propagator D μ r t ψ)) x‖ ≤
            C₀ * (2 * Real.pi) ^ mStar d *
              Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
                Lattice.jp k ^ mStar d := by
    intro ψ hψc hψm hψs hb1 hb2
    obtain ⟨hcl, hpe, h3, h4⟩ := h D ν₀ T μ hA t ht ψ hψc hψm
    refine ⟨?_, fun j hj x => ?_⟩
    · exact (h3 m hm1 le_rfl r hr).2.trans
        (mul_le_mul_of_nonneg_left hb1 (Real.exp_pos _).le)
    · have hCk : Torus.IsCk 2 (propagator D μ r t ψ) := by rw [hpe r hr]; exact hcl.c2 r hr
      refine (norm_iteratedFDeriv_le_cbNorm 2 j hj _ hCk x).trans ((h4 r hr).trans ?_)
      calc C₀ * Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
            sobolevNorm (mStar d : ℝ) ψ
          ≤ C₀ * Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
              (2 * Real.pi * Lattice.jp k) ^ mStar d :=
            mul_le_mul_of_nonneg_left hb2 (mul_nonneg hC₀.le (Real.exp_pos _).le)
        _ = _ := by rw [mul_pow]; ring
  obtain ⟨c1, c2⟩ := ClassicalPart.sobolev_cosMode m hm1 k
  obtain ⟨c3, c4⟩ := ClassicalPart.sobolev_cosMode (mStar d) (by have := ClassicalPart.three_le_mStar d; omega) k
  obtain ⟨s1, s2⟩ := ClassicalPart.sobolev_sinMode m hm1 k
  obtain ⟨s3, s4⟩ := ClassicalPart.sobolev_sinMode (mStar d) (by have := ClassicalPart.three_le_mStar d; omega) k
  obtain ⟨g1, g2⟩ := gen _ (Torus.continuous_cosMode k) c1 c3 c2 c4
  obtain ⟨g3, g4⟩ := gen _ (Torus.continuous_sinMode k) s1 s3 s2 s4
  exact ⟨⟨g1, g3⟩, fun j hj x => ⟨g2 j hj x, g4 j hj x⟩⟩

/-- Proposition 3.9(c) (line 1756), second half: for `m ≥ m_*` all of `F, ∇F, ∇^{⊗2}F, ∂_τF` are
bounded and continuous on `[0,t] × 𝕋^d` (continuity on the compact set, through the lift for the
space derivatives; boundedness follows). -/
theorem adjoint_torus_joint_continuity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ)
    (ht : t ∈ Set.Ioc 0 T) (φc : Coeff d) (hφ : MemHs m φc) (hre : IsRealCoeff φc) :
    (∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (toFun (propagatorCoeff D μ m t φc p.1))) p.2) ∧
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
      toFun (forwardGen D (μ (t - p.1)) (propagatorCoeff D μ m t φc p.1)) p.2 := by
  have hm3 := ClassicalPart.one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have hmd : (d : ℝ) / 2 < m := by
    obtain ⟨m'', h1, h2⟩ := ClassicalPart.exists_mid (d := d) hm
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm1 R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hreal := ClassicalPart.propagatorCoeff_real hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA t ht
    φc hφ hre
  obtain ⟨m'', hm''1, hm''2⟩ := ClassicalPart.exists_mid (d := d) hm
  have hcont : ContinuousInHs m'' (propagatorCoeff D μ m t φc) t :=
    forward_strong_continuity (m : ℝ) t _ hw m'' hm''2
  obtain ⟨-, -, -, hjoint⟩ := ClassicalPart.gen_path_facts hA hmd ht hsol hreal hm''1 hcont
  refine ⟨fun j hj => ?_, hjoint⟩
  refine ClassicalPart.continuous_iteratedFDeriv_toFun (X := Set.Icc (0 : ℝ) t)
    (fun x => propagatorCoeff D μ m t φc x.1) j m'' (by
      have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      linarith) (fun x => hreal _ x.2) (fun x => hcont.1 _ x.2) (fun x₀ => ?_)
  exact ClassicalPart.tendsto_subtype_of_within (t := t)
    (fun τ => hsNorm m'' (propagatorCoeff D μ m t φc τ - propagatorCoeff D μ m t φc x₀)) x₀
    (hcont.2 _ x₀.2)

/-- The propagator property `U^{r,σ}U^{σ,t} = U^{r,t}` for `0 ≤ r ≤ σ ≤ t` (uniqueness of classical
solutions), for `m ≥ m_*` and continuous data in `H^m`. -/
theorem propagator_semigroup (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T)
    (φ : Torus d → ℝ) (hφc : Continuous φ) (hφ : MemSobolev m φ) (r σ : ℝ) (hr : 0 ≤ r)
    (hrσ : r ≤ σ) (hσt : σ < t) :
    propagator D μ r t φ = propagator D μ r σ (propagator D μ σ t φ) := by
  have hm3 := ClassicalPart.one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have hσ0 : 0 ≤ σ := hr.trans hrσ
  have hrt : r ∈ Set.Icc (0 : ℝ) t := ⟨hr, hrσ.trans hσt.le⟩
  have hσt' : σ ∈ Set.Icc (0 : ℝ) t := ⟨hσ0, hσt.le⟩
  have hcls := ClassicalPart.classical_exists hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ hφc hφ
  have hpe := ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ
    hφc hφ
  obtain ⟨f, hf⟩ : ∃ f : ℝ → Torus d → ℝ,
      f = fun r x => toFun (propagatorCoeff D μ m t (coeffOf φ) (t - r)) x := ⟨_, rfl⟩
  rw [← hf] at hcls
  have hpe' : ∀ r ∈ Set.Icc (0 : ℝ) t, propagator D μ r t φ = f r := by
    intro r hr; rw [hf]; exact hpe r hr
  have hι : Continuous (Set.inclusion (Set.Icc_subset_Icc_right hσt.le) :
      Set.Icc (0 : ℝ) σ → Set.Icc (0 : ℝ) t) := continuous_inclusion _
  have hc2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) σ × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2 := fun j hj =>
    (hcls.cont_c2 j hj).comp (hι.prodMap continuous_id)
  have hct : Continuous fun p : Set.Icc (0 : ℝ) σ × Torus d =>
      backwardGenerator D (μ p.1) (f p.1) p.2 :=
    by
    have h := (hcls.cont_time_deriv).comp (hι.prodMap continuous_id)
    exact h.congr fun p => rfl
  have hrest : IsClassicalAdjointSolution D μ σ (f σ) f :=
    { c2 := fun r' hr' => hcls.c2 r' ⟨hr'.1, hr'.2.trans hσt.le⟩
      cont_c2 := hc2
      terminal := rfl
      time_deriv := fun x r' hr' => hcls.time_deriv x r' ⟨hr'.1, hr'.2.trans hσt⟩
      cont_time_deriv := hct }
  have hE : ∃ g, IsClassicalAdjointSolution D μ σ (f σ) g := ⟨f, hrest⟩
  rw [hpe' r hrt, hpe' σ hσt']
  unfold propagator
  rw [dif_pos hE]
  rcases hσ0.eq_or_lt with h0 | h0
  · have hr0 : r = σ := le_antisymm hrσ (by rw [← h0]; exact hr)
    rw [hr0]
    exact (hE.choose_spec.terminal).symm
  · exact (classical_adjoint_unique hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA σ
      ⟨h0, hσt.le.trans ht.2⟩ (f σ) _ _ hE.choose_spec hrest r ⟨hr, hrσ⟩).symm

/-- `B:eq:adjoint-torus-bound` for regular solutions, from `energy_torus` by Grönwall: a real
forward solution in `C([0,t];H^{m+2})` satisfies `‖F(τ)‖_{H^m} ≤ e^{Λ_mτ}‖φ‖_{H^m}` with the
constant of `energy_torus`. -/
theorem adjoint_torus_bound_of_regular (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (_ : t ∈ Set.Ioc 0 T) (φc : Coeff d)
      (F : ℝ → Coeff d) (_ : IsForwardSolution D μ t φc F) (_ : ContinuousInHs (m + 2) F t)
      (_ : ∀ τ ∈ Set.Icc 0 t, IsRealCoeff (F τ)),
      ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤
        Real.exp (R.lambdaM C ν₀ (thetaOrder d s) * τ) * hsNorm m φc := by
  obtain ⟨C, hC, hmain⟩ := energy_torus hd s hs0 hsd m hm R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA t ht φc F hF hcont hreal τ hτ => ?_⟩
  obtain ⟨lam, q, hlq⟩ : ∃ (lam : Fin d → ℝ) (q : Fin d → Euc d),
      R.IsR2 → IsSymDiag D.M lam q := by
    by_cases hR : R.IsR2
    · obtain ⟨lam, q, h⟩ := exists_symDiag (regime_symNonpos hR hA.regime)
      exact ⟨lam, q, fun _ => h⟩
    · exact ⟨0, fun _ => 0, fun h => absurd h hR⟩
  set a : ℝ := R.lambdaM C ν₀ (thetaOrder d s) with ha
  have hall := fun τ' (hτ' : τ' ∈ Set.Icc 0 t) =>
    hmain D ν₀ T μ hA lam q hlq t ht φc F hF hcont hreal τ' hτ'
  have ht0 : 0 ≤ t := ht.1.le
  have h0 : F 0 = φc := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht0⟩
    simpa using this
  have hy : ∀ τ' ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ'' => (1 / 2 : ℝ) * hsNormSq m (F τ''))
      (hsInner m (forwardGen D (μ (t - τ')) (F τ')) (F τ')).re (Set.Icc 0 t) τ' :=
    fun τ' hτ' => (hall τ' hτ').2.1
  have hle : ∀ τ' ∈ Set.Icc 0 t, (hsInner m (forwardGen D (μ (t - τ')) (F τ')) (F τ')).re ≤
      (2 * a) * ((1 / 2 : ℝ) * hsNormSq m (F τ')) := by
    intro τ' hτ'
    refine ((hall τ' hτ').2.2).trans ?_
    refine (energyRHS_le hd R a D m lam q (fun hR l => (hlq hR).nonneg l) (μ (t - τ')) (F τ')).trans ?_
    linarith
  have hg := gronwall_aux (2 * a) hy hle τ hτ
  rw [h0] at hg
  have hnn0 : 0 ≤ hsNormSq (m : ℝ) φc := hsNormSq_nonneg _ _
  have hg' : hsNormSq (m : ℝ) (F τ) ≤ Real.exp (2 * a * τ) * hsNormSq (m : ℝ) φc := by linarith
  unfold hsNorm
  calc Real.sqrt (hsNormSq (m : ℝ) (F τ))
      ≤ Real.sqrt (Real.exp (2 * a * τ) * hsNormSq (m : ℝ) φc) := Real.sqrt_le_sqrt hg'
    _ = Real.exp (a * τ) * Real.sqrt (hsNormSq (m : ℝ) φc) := by
        rw [Real.sqrt_mul (Real.exp_pos _).le]
        congr 1
        rw [show 2 * a * τ = a * τ + a * τ by ring, Real.exp_add]
        exact Real.sqrt_mul_self (Real.exp_pos _).le

end HRS.PDE

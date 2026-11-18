import HRS.Main.Linearization

/-!
# Packet A34, helper 1: uniform propagator bounds and stability in Sobolev-function form

For `AdjointData` at a level `J ≥ m_*` and a datum `φ` that is continuous and in `H^J`:
* uniform (in the data `D, ρ`) bounds for the classical propagator `U^{r,t} φ`
  (`H^{m'}` bounds, gradient sup bound, classical solution);
* the stability estimate of Proposition 3.15 for the difference of two classical propagators,
  in the form `‖U₁^{r,t}φ - U₂^{r,t}φ‖_{H^m} ≤ C (|β₁⁻¹ - β₂⁻¹| + δ) ‖φ‖_{H^{m+2}}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33

variable {d : ℕ}

theorem a34_exp_le (l T t r : ℝ) (hr : r ∈ Set.Icc 0 t) (ht : t ≤ T) :
    Real.exp (l * (t - r)) ≤ Real.exp (|l| * T) := by
  refine Real.exp_le_exp.2 ?_
  calc l * (t - r) ≤ |l| * (t - r) :=
        mul_le_mul_of_nonneg_right (le_abs_self l) (by linarith [hr.2])
    _ ≤ |l| * T := mul_le_mul_of_nonneg_left (by linarith [hr.1]) (abs_nonneg l)

/-- Uniform bounds for the classical propagator. -/
theorem a34_unif (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB ν₀ T : ℝ) :
    ∃ K : ℕ → ℝ, ∃ K₂ : ℝ, (∀ m, 0 ≤ K m) ∧ 0 ≤ K₂ ∧
      ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ) (_ : AdjointData s J R MB Λ VB D ν₀ T ρ)
        {t : ℝ} (_ : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ} (_ : Continuous φ)
        (_ : MemSobolev (J : ℝ) φ),
        (∃ f : ℝ → Torus d → ℝ, IsClassicalAdjointSolution D ρ t φ f ∧
          ∀ r ∈ Set.Icc 0 t, propagator D ρ r t φ = f r) ∧
        ∀ r ∈ Set.Icc 0 t,
          (∀ m : ℕ, 1 ≤ m → m ≤ J → MemSobolev (m : ℝ) (propagator D ρ r t φ) ∧
            sobolevNorm (m : ℝ) (propagator D ρ r t φ) ≤ K m * sobolevNorm (m : ℝ) φ) ∧
          Torus.IsCk 2 (propagator D ρ r t φ) ∧
          ∀ x : Torus d, ‖Torus.grad (propagator D ρ r t φ) x‖ ≤ K₂ * sobolevNorm (mStar d : ℝ) φ := by
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd s hs0 hsd J hJ R MB Λ VB
  refine ⟨fun m => Real.exp (|R.lambdaM (Cs m) ν₀ (thetaOrder d s)| * T),
    C * Real.exp (|R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s)| * T),
    fun m => (Real.exp_pos _).le, mul_nonneg hC.le (Real.exp_pos _).le, ?_⟩
  intro D ρ hA t ht φ hφc hφ
  obtain ⟨hcl, hpe, h3, h4⟩ := hmain D ν₀ T ρ hA t ht φ hφc hφ
  refine ⟨⟨_, hcl, hpe⟩, fun r hr => ⟨fun m hm1 hmJ => ?_, ?_, fun x => ?_⟩⟩
  · obtain ⟨hm, hb⟩ := h3 m hm1 hmJ r hr
    refine ⟨hm, hb.trans (mul_le_mul_of_nonneg_right (a34_exp_le _ T t r hr ht.2)
      (Real.sqrt_nonneg _))⟩
  · rw [hpe r hr]; exact hcl.c2 r hr
  · have hCk : Torus.IsCk 2 (propagator D ρ r t φ) := by rw [hpe r hr]; exact hcl.c2 r hr
    have h1 : ‖Torus.grad (propagator D ρ r t φ) x‖ ≤ Torus.cbNorm 2 (propagator D ρ r t φ) := by
      have := norm_iteratedFDeriv_le_cbNorm (k := 2) (j := 1) (by norm_num) hCk (Torus.rep x)
      rw [norm_iteratedFDeriv_one] at this
      unfold Torus.grad
      rw [gradient]
      simpa using this
    refine h1.trans ((h4 r hr).trans ?_)
    have h0 : 0 ≤ sobolevNorm (mStar d : ℝ) φ := Real.sqrt_nonneg _
    calc C * Real.exp (R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s) * (t - r)) *
          sobolevNorm (mStar d : ℝ) φ
        ≤ C * Real.exp (|R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d s)| * T) *
          sobolevNorm (mStar d : ℝ) φ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (a34_exp_le _ T t r hr ht.2) hC.le) h0
      _ = _ := by ring

/-- The classical propagator in coefficient form. -/
theorem a34_prop_coeff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ}
    (hφc : Continuous φ) (hφ : MemSobolev (J : ℝ) φ) {r : ℝ} (hr : r ∈ Set.Icc 0 t) :
    propagator D μ r t φ = (fun x => toFun (propagatorCoeff D μ J t (coeffOf φ) (t - r)) x) ∧
      Continuous (propagator D μ r t φ) ∧
      IsRealCoeff (propagatorCoeff D μ J t (coeffOf φ) (t - r)) ∧
      Summable (fun k => ‖propagatorCoeff D μ J t (coeffOf φ) (t - r) k‖) ∧
      MemHs (J : ℝ) (propagatorCoeff D μ J t (coeffOf φ) (t - r)) := by
  have hdom : Dom J φ := ⟨hφc, hφ⟩
  have hJ3 := ClassicalPart.three_le_mStar d
  have hJ1 : 1 ≤ J := by omega
  have hJd : (d : ℝ) / 2 < J := by
    have := a33_mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  obtain ⟨h1, h2⟩ := prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hdom hr
  have hτ : t - r ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  obtain ⟨h3, h4⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB Λ VB D ν₀ T μ hA ht hdom hτ
  have hφcf : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ).1
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB Λ VB
  obtain ⟨-, hw, -⟩ := hspec D ν₀ T μ hA t ht (coeffOf φ) hφcf
  exact ⟨h1, h2, h3, h4, hw.1 _ hτ⟩

/-- Stability of the classical propagator (Proposition 3.15), in Sobolev-function form. -/
theorem a34_stab (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (hms : mStar d ≤ m + 2) (R : Regime) (MB Λ VB ν₀ T : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D₁ D₂ : DynData d) (μ₁ μ₂ : ℝ → Torus d → ℝ)
        (_ : AdjointData s (m + 2) R MB Λ VB D₁ ν₀ T μ₁)
        (_ : AdjointData s (m + 2) R MB Λ VB D₂ ν₀ T μ₂) (_ : D₁.M = D₂.M) (_ : D₁.V = D₂.V)
        (δ : ℝ) (_ : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm (m + 2) (μ₁ r - μ₂ r) ≤ δ)
        {t : ℝ} (_ : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ} (_ : Continuous φ)
        (_ : MemSobolev ((m + 2 : ℕ) : ℝ) φ) {r : ℝ} (_ : r ∈ Set.Icc 0 t),
        MemSobolev (m : ℝ) (fun x => propagator D₁ μ₁ r t φ x - propagator D₂ μ₂ r t φ x) ∧
        sobolevNorm (m : ℝ) (fun x => propagator D₁ μ₁ r t φ x - propagator D₂ μ₂ r t φ x) ≤
          C * (|D₁.invβ - D₂.invβ| + δ) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ := by
  obtain ⟨C₀, C', hC₀, hC', hst⟩ := propagator_stability hd s hs0 hsd m hm R MB Λ VB
  refine ⟨C₀ * |T| * Real.exp (|R.lambdaM C' ν₀ (thetaOrder d s)| * T) + 1, by positivity, ?_⟩
  intro D₁ D₂ μ₁ μ₂ hA₁ hA₂ hM hV δ hδ t ht φ hφc hφ r hr
  have hr0 : 0 ≤ r := hr.1
  have hrt : r ≤ t := hr.2
  obtain ⟨e₁, hc₁, hre₁, hs₁, hmem₁⟩ := a34_prop_coeff hd s hs0 hsd (m + 2) hms R MB Λ VB D₁ ν₀ T μ₁
    hA₁ ht hφc hφ hr
  obtain ⟨e₂, hc₂, hre₂, hs₂, hmem₂⟩ := a34_prop_coeff hd s hs0 hsd (m + 2) hms R MB Λ VB D₂ ν₀ T μ₂
    hA₂ ht hφc hφ hr
  have hcast : (((m + 2 : ℕ)) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast] at e₁ e₂ hre₁ hre₂ hs₁ hs₂ hmem₁ hmem₂
  set c₁ := propagatorCoeff D₁ μ₁ ((m : ℝ) + 2) t (coeffOf φ) (t - r) with hc₁def
  set c₂ := propagatorCoeff D₂ μ₂ ((m : ℝ) + 2) t (coeffOf φ) (t - r) with hc₂def
  have hφcf : MemHs ((m + 2 : ℕ) : ℝ) (coeffOf φ) := (hsNormSq_coeffOf _ φ hφ).1
  have hcoef₁ : coeffOf (propagator D₁ μ₁ r t φ) = c₁ := by
    rw [e₁]; exact coeffOf_toFun c₁ hre₁ hs₁
  have hcoef₂ : coeffOf (propagator D₂ μ₂ r t φ) = c₂ := by
    rw [e₂]; exact coeffOf_toFun c₂ hre₂ hs₂
  have hcoefw : coeffOf (fun x => propagator D₁ μ₁ r t φ x - propagator D₂ μ₂ r t φ x) = c₁ - c₂ := by
    rw [ClassicalAux.coeffOf_sub (ClassicalAux.integrable_of_continuous hc₁)
      (ClassicalAux.integrable_of_continuous hc₂), hcoef₁, hcoef₂]
    rfl
  have hmem₁' : MemHs (m : ℝ) c₁ := hmem₁.mono (by linarith)
  have hmem₂' : MemHs (m : ℝ) c₂ := hmem₂.mono (by linarith)
  have hmw : MemSobolev (m : ℝ) (fun x => propagator D₁ μ₁ r t φ x - propagator D₂ μ₂ r t φ x) := by
    refine memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous (hc₁.sub hc₂)) ?_
    rw [hcoefw]
    exact memHs_sub hmem₁' hmem₂'
  refine ⟨hmw, ?_⟩
  rw [ClassicalPart.sobolevNorm_eq_hsNorm hmw, hcoefw,
    ClassicalPart.sobolevNorm_eq_hsNorm hφ, hcast]
  have h := hst D₁ D₂ ν₀ T μ₁ μ₂ hA₁ hA₂ hM hV δ hδ (coeffOf φ)
    (by rw [← hcast]; exact hφcf) r t hr0 hrt ht.2
  have hδ0 : 0 ≤ δ := by
    refine le_trans ?_ (hδ 0 ⟨le_rfl, ht.1.le.trans ht.2⟩)
    exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hn0 : 0 ≤ HRS.PDE.hsNorm ((m : ℝ) + 2) (coeffOf φ) := Real.sqrt_nonneg _
  refine h.trans ?_
  have hs0' : 0 ≤ |D₁.invβ - D₂.invβ| + δ := by positivity
  have hexp := a34_exp_le (R.lambdaM C' ν₀ (thetaOrder d s)) T t r hr ht.2
  have hexp' : Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * (t - r)) ≤
      Real.exp (|R.lambdaM C' ν₀ (thetaOrder d s)| * T) := hexp
  have htr : t - r ≤ |T| := by
    have : t - r ≤ T := by linarith [ht.2, hr.1]
    exact this.trans (le_abs_self T)
  have htr0 : 0 ≤ t - r := by linarith
  have hK : C₀ * (t - r) * Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * (t - r)) ≤
      C₀ * |T| * Real.exp (|R.lambdaM C' ν₀ (thetaOrder d s)| * T) + 1 := by
    have : C₀ * (t - r) * Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * (t - r)) ≤
        C₀ * |T| * Real.exp (|R.lambdaM C' ν₀ (thetaOrder d s)| * T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htr hC₀.le) hexp' (Real.exp_pos _).le
        (by positivity)
    linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hs0') hn0

end HRS.A34

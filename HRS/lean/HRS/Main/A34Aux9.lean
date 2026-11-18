import HRS.Main.A34Aux8

/-!
# Packet A34, helper 9: the quantitative stability of the surrogate statistic
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

/-- numeric core, small regime -/
theorem a34_num_small {Δ N cX cs ci c1 : ℝ} (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hN : 0 ≤ N)
    (hcX : 0 ≤ cX) (hc1 : 0 ≤ c1) (X σ : ℝ) (hX : X ≤ Δ * N * (cX + 4 * ci * cs))
    (hσ : σ ≤ Real.sqrt (c1 * N ^ 2 * Δ)) (hci : 0 ≤ ci) (hcs : 0 ≤ cs) :
    X + σ ≤ (1 + 4 * cX + 4 * ci * cs + Real.sqrt c1) * N * (Δ + Real.sqrt Δ) := by
  have h1 : Real.sqrt (c1 * N ^ 2 * Δ) = Real.sqrt c1 * N * Real.sqrt Δ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc1, Real.sqrt_sq hN]
  rw [h1] at hσ
  have hs : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
  have hs1 := Real.sqrt_nonneg c1
  have h4 : 0 ≤ cX + 4 * ci * cs := by positivity
  have : X + σ ≤ Δ * N * (cX + 4 * ci * cs) + Real.sqrt c1 * N * Real.sqrt Δ := add_le_add hX hσ
  refine this.trans ?_
  have hp1 : 0 ≤ N * Δ := by positivity
  have hp2 : 0 ≤ N * Real.sqrt Δ := by positivity
  nlinarith [mul_nonneg hp1 h4, mul_nonneg hp1 hcX, mul_nonneg hp2 hs1, mul_nonneg hp2 hcX,
    mul_nonneg hp2 (mul_nonneg hci hcs), mul_nonneg hp1 (mul_nonneg hci hcs), hp1, hp2]

/-- numeric core, large regime -/
theorem a34_num_large {Δ N cX cs ci c2 : ℝ} (hΔ1 : 1 < Δ) (hN : 0 ≤ N)
    (hcX : 0 ≤ cX) (hc2 : 0 ≤ c2) (X σ : ℝ) (hX : X ≤ 3 * Δ * (cX * N))
    (hσ : σ ≤ Real.sqrt (c2 * N ^ 2 * Δ ^ 2)) (hci : 0 ≤ ci) (hcs : 0 ≤ cs) :
    X + σ ≤ (1 + 4 * cX + 4 * ci * cs + Real.sqrt c2) * N * (Δ + Real.sqrt Δ) := by
  have hΔ : 0 ≤ Δ := by linarith
  have h1 : Real.sqrt (c2 * N ^ 2 * Δ ^ 2) = Real.sqrt c2 * N * Δ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc2, Real.sqrt_sq hN, Real.sqrt_sq hΔ]
  rw [h1] at hσ
  have hs : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
  have hs1 := Real.sqrt_nonneg c2
  have : X + σ ≤ 3 * Δ * (cX * N) + Real.sqrt c2 * N * Δ := add_le_add hX hσ
  refine this.trans ?_
  have hp1 : 0 ≤ N * Δ := by positivity
  have hp2 : 0 ≤ N * Real.sqrt Δ := by positivity
  nlinarith [mul_nonneg hp1 hcX, mul_nonneg hp1 hs1, mul_nonneg hp2 hs1, mul_nonneg hp2 hcX,
    mul_nonneg hp2 (mul_nonneg hci hcs), mul_nonneg hp1 (mul_nonneg hci hcs), hp1, hp2]

theorem a34_num_E_small {K₂ N Λ Δ q₂ M0 t T Cst Y : ℝ} (hK₂ : 0 ≤ K₂) (hΛ : 0 ≤ Λ)
    (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hq : 0 ≤ q₂) (hq3 : 2 * q₂ ≤ 3) (hM : 0 ≤ M0) (ht0 : 0 ≤ t)
    (htT : t ≤ T) (hCst : 0 ≤ Cst) (hY : Y ≤ t * (2 * Cst * Δ * N) ^ 2) :
    2 * (K₂ * N) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0 + 2 * (2 * q₂ * Λ) * Y ≤
      (2 * K₂ ^ 2 * (|Λ| + 3) * M0 + 24 * |Λ| * |T| * Cst ^ 2) * N ^ 2 * Δ := by
  have hT : 0 ≤ T := ht0.trans htT
  rw [abs_of_nonneg hΛ, abs_of_nonneg hT]
  have h1 : 2 * (K₂ * N) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0 ≤
      2 * K₂ ^ 2 * (Λ + 3) * M0 * N ^ 2 * Δ := by
    have : Λ * Δ + 2 * q₂ * Δ ≤ (Λ + 3) * Δ := by nlinarith
    have h2 : 0 ≤ 2 * (K₂ * N) ^ 2 * M0 := by positivity
    calc 2 * (K₂ * N) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0
        = (2 * (K₂ * N) ^ 2 * M0) * (Λ * Δ + 2 * q₂ * Δ) := by ring
      _ ≤ (2 * (K₂ * N) ^ 2 * M0) * ((Λ + 3) * Δ) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring
  have h3 : 2 * (2 * q₂ * Λ) * Y ≤ 24 * Λ * T * Cst ^ 2 * N ^ 2 * Δ := by
    have hB : 0 ≤ 2 * (2 * q₂ * Λ) := by positivity
    have hY' : Y ≤ T * (4 * Cst ^ 2 * N ^ 2 * Δ) := by
      refine hY.trans ?_
      have : (2 * Cst * Δ * N) ^ 2 = 4 * Cst ^ 2 * N ^ 2 * Δ ^ 2 := by ring
      rw [this]
      have : Δ ^ 2 ≤ Δ := by nlinarith
      calc t * (4 * Cst ^ 2 * N ^ 2 * Δ ^ 2) ≤ T * (4 * Cst ^ 2 * N ^ 2 * Δ ^ 2) :=
            mul_le_mul_of_nonneg_right htT (by positivity)
        _ ≤ T * (4 * Cst ^ 2 * N ^ 2 * Δ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (by positivity)) hT
    calc 2 * (2 * q₂ * Λ) * Y ≤ 2 * (2 * q₂ * Λ) * (T * (4 * Cst ^ 2 * N ^ 2 * Δ)) :=
          mul_le_mul_of_nonneg_left hY' hB
      _ = (2 * q₂) * (8 * Λ * T * Cst ^ 2 * N ^ 2 * Δ) := by ring
      _ ≤ 3 * (8 * Λ * T * Cst ^ 2 * N ^ 2 * Δ) :=
          mul_le_mul_of_nonneg_right hq3 (by positivity)
      _ = _ := by ring
  nlinarith [h1, h3]

theorem a34_num_E_large {K₂ N Λ Δ q₂ M0 Y : ℝ} (hK₂ : 0 ≤ K₂) (hΛ : 0 ≤ Λ)
    (hΔ1 : 1 < Δ) (hq : 0 ≤ q₂) (hq3 : 2 * q₂ ≤ 2 + Δ) (hM : 0 ≤ M0) (hN : 0 ≤ N)
    (hY : Y ≤ (K₂ * N + K₂ * N) ^ 2 * M0) :
    2 * (K₂ * N) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0 + 2 * (2 * q₂ * Λ) * Y ≤
      (K₂ ^ 2 * M0 * (26 * |Λ| + 6)) * N ^ 2 * Δ ^ 2 := by
  rw [abs_of_nonneg hΛ]
  have hΔ0 : 0 ≤ Δ := by linarith
  have hq3' : 2 * q₂ ≤ 3 * Δ := by linarith
  have h1 : 2 * (K₂ * N) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0 ≤
      2 * (K₂ * N) ^ 2 * ((Λ + 3) * Δ ^ 2) * M0 := by
    have e1 : Λ * Δ ≤ Λ * Δ ^ 2 := by nlinarith [mul_nonneg hΛ hΔ0, mul_nonneg (mul_nonneg hΛ hΔ0) (sub_nonneg.2 hΔ1.le)]
    have e2 : 2 * q₂ * Δ ≤ 3 * Δ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hq3' hΔ0]
    have : Λ * Δ + 2 * q₂ * Δ ≤ (Λ + 3) * Δ ^ 2 := by nlinarith
    have h2 : 0 ≤ 2 * (K₂ * N) ^ 2 * M0 := by positivity
    calc 2 * (K₂ * N) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0
        = (2 * (K₂ * N) ^ 2 * M0) * (Λ * Δ + 2 * q₂ * Δ) := by ring
      _ ≤ (2 * (K₂ * N) ^ 2 * M0) * ((Λ + 3) * Δ ^ 2) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring
  have h3 : 2 * (2 * q₂ * Λ) * Y ≤ 2 * (3 * Δ ^ 2 * Λ) * ((K₂ * N + K₂ * N) ^ 2 * M0) := by
    have hB : 0 ≤ 2 * (2 * q₂ * Λ) := by positivity
    calc 2 * (2 * q₂ * Λ) * Y ≤ 2 * (2 * q₂ * Λ) * ((K₂ * N + K₂ * N) ^ 2 * M0) :=
          mul_le_mul_of_nonneg_left hY hB
      _ ≤ 2 * (3 * Δ ^ 2 * Λ) * ((K₂ * N + K₂ * N) ^ 2 * M0) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : 2 * q₂ ≤ 3 * Δ ^ 2 := by nlinarith
          nlinarith
  nlinarith [h1, h3]

/-- the variance of the Gaussian block of the statistic -/
def a34_cov (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ) : ℝ :=
  2 * q * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
    inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) * ρ r x

theorem a34_stat_unfold {Ω : Type*} [MeasurableSpace Ω] (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (A q t : ℝ) (φ : Torus d → ℝ) (P : Measure Ω) (η : Ω → (Torus d → ℝ) → ℝ) :
    surrogateStatLaw D ρ A q (fun _ : Fin 1 => t) (fun _ => φ) P η =
      law P (fun ω => a34_ι (A * η ω (propagator D ρ 0 t φ))) ∗
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) (Matrix.of fun _ _ =>
          a34_cov D ρ q t φ) := rfl

theorem a34_sobolevNorm_zero_sub (m : ℝ) (φ : Torus d → ℝ) :
    sobolevNorm m (fun x => φ x - φ x) = 0 := by
  simp [sobolevNorm, Torus.mean, Torus.funRealCoeff]

/-- Quantitative stability of the surrogate statistic for abstract coefficient data. -/
theorem a34_stat_real (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T Cin : ℝ) (m m₀ : ℕ) (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (hms : mStar d ≤ m + 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D₁ D₂ : DynData d) (ρ₁ ρ₂ : ℝ → Torus d → ℝ) (A₁ A₂ q₁ q₂ Δ : ℝ),
        AdjointData s (m + 2) Rg MB Λ VB D₁ ν₀ T ρ₁ →
        AdjointData s (m + 2) Rg MB Λ VB D₂ ν₀ T ρ₂ → D₁.M = D₂.M → D₁.V = D₂.V → 0 ≤ Δ →
        (∀ r ∈ Set.Icc (0 : ℝ) T, Torus.cbNorm (m + 2) (ρ₁ r - ρ₂ r) ≤ Δ) →
        |D₁.invβ - D₂.invβ| ≤ Δ → 0 ≤ q₁ → q₁ ≤ 1 → 0 ≤ q₂ → |2 * q₁ - 2 * q₂| ≤ Δ →
        |A₁| ≤ 1 → |A₁ - A₂| ≤ Δ →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (η : Ω → (Torus d → ℝ) → ℝ), XHyp P η m₀ Cin →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, MemSobolev ((m + 2 : ℕ) : ℝ) φ →
          Continuous φ →
          (MemSobolev (m₀ : ℝ) (propagator D₁ ρ₁ 0 t φ) ∧ Continuous (propagator D₁ ρ₁ 0 t φ) ∧
            MemSobolev (m₀ : ℝ) (propagator D₂ ρ₂ 0 t φ) ∧ Continuous (propagator D₂ ρ₂ 0 t φ) ∧
            0 ≤ a34_cov D₁ ρ₁ q₁ t φ ∧ 0 ≤ a34_cov D₂ ρ₂ q₂ t φ ∧
            ∫ ω, |A₁ * η ω (propagator D₁ ρ₁ 0 t φ) - A₂ * η ω (propagator D₂ ρ₂ 0 t φ)| ∂P +
              |Real.sqrt (a34_cov D₁ ρ₁ q₁ t φ) - Real.sqrt (a34_cov D₂ ρ₂ q₂ t φ)| ≤
            C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ * (Δ + Real.sqrt Δ)) := by
  obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd (m + 2) hms Rg MB Λ VB ν₀ T
  obtain ⟨Cst, hCst, hst⟩ := a34_stab hd s hs0 hsd m hm hms Rg MB Λ VB ν₀ T
  set M0 : ℝ := (a33_mu0 d T).real Set.univ with hM0
  have hM0nn : 0 ≤ M0 := measureReal_nonneg
  set m₁ : ℕ := max m₀ 1 with hm₁
  have hm₁1 : 1 ≤ m₁ := le_max_right _ _
  have hm₁m : m₁ ≤ m := max_le hm₀ hm
  set cX : ℝ := |Cin| * K m₁ with hcX
  set cH1 : ℝ := 2 * K₂ ^ 2 * (|Λ| + 3) * M0 + 24 * |Λ| * |T| * Cst ^ 2 with hcH1
  set cH2 : ℝ := K₂ ^ 2 * M0 * (26 * |Λ| + 6) with hcH2
  have hcX0 : 0 ≤ cX := mul_nonneg (abs_nonneg _) (hK0 _)
  have hcH10 : 0 ≤ cH1 := by positivity
  have hcH20 : 0 ≤ cH2 := by positivity
  refine ⟨1 + 4 * cX + 4 * |Cin| * Cst + |Cin| + Real.sqrt cH1 + Real.sqrt cH2, by positivity, ?_⟩
  intro D₁ D₂ ρ₁ ρ₂ A₁ A₂ q₁ q₂ Δ hA₁ hA₂ hM hV hΔ hρΔ hβΔ hq₁0 hq₁1 hq₂0 hqΔ hA₁1 hAΔ
    Ω _ P _ η hη t ht φ hφ hφc
  have hφa : ∀ a : ℝ, a ≤ ((m + 2 : ℕ) : ℝ) → sobolevNorm a φ ≤ sobolevNorm ((m + 2 : ℕ) : ℝ) φ :=
    fun a ha => a34_sobolevNorm_mono ha hφ
  have hΛ0 : 0 ≤ Λ := by
    have := (hA₁.hμ.bound 0 ⟨le_rfl, hA₁.hT.le⟩)
    exact (Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _).trans this
  have hT0 : 0 < T := hA₁.hT
  have hN0 : 0 ≤ sobolevNorm ((m + 2 : ℕ) : ℝ) φ := Real.sqrt_nonneg _
  have hmem₀φ : MemSobolev (m₀ : ℝ) φ := MFAdjoint.memSobolev_mono_idx hφ (by
    exact_mod_cast (by omega : m₀ ≤ m + 2))
  rcases ht.1.eq_or_lt with h0 | hpos
  · -- the case `t = 0`
    subst h0
    have hψ₁ := a34_prop_zero hd (m + 2) hms Rg s MB Λ VB ν₀ T D₁ ρ₁ hA₁ hφc hφ
    have hψ₂ := a34_prop_zero hd (m + 2) hms Rg s MB Λ VB ν₀ T D₂ ρ₂ hA₂ hφc hφ
    have hv : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q : ℝ), a34_cov D ρ q 0 φ = 0 := by
      intro D ρ q
      unfold a34_cov
      rw [min_self, Set.Icc_self, setIntegral_measure_zero _ (by simp), mul_zero]
    rw [hψ₁, hψ₂, hv, hv]
    refine ⟨hmem₀φ, hφc, hmem₀φ, hφc, le_rfl, le_rfl, ?_⟩
    simp only [Real.sqrt_zero, sub_self, abs_zero, add_zero]
    have h1 := a34_X_diff hη hmem₀φ hmem₀φ hφc hφc A₁ A₂
    rw [a34_sobolevNorm_zero_sub] at h1
    have h2 : sobolevNorm (m₀ : ℝ) φ ≤ sobolevNorm ((m + 2 : ℕ) : ℝ) φ :=
      hφa _ (by exact_mod_cast (by omega : m₀ ≤ m + 2))
    refine h1.trans ?_
    have h3 : |A₁ - A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) φ) + |A₂| * (|Cin| * 0) ≤
        Δ * (|Cin| * sobolevNorm ((m + 2 : ℕ) : ℝ) φ) := by
      rw [mul_zero, mul_zero, add_zero]
      exact mul_le_mul hAΔ (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hΔ
    refine h3.trans ?_
    have hs := Real.sqrt_nonneg Δ
    have hp : 0 ≤ Real.sqrt cH1 := Real.sqrt_nonneg _
    have hp2 : 0 ≤ Real.sqrt cH2 := Real.sqrt_nonneg _
    have hx : 0 ≤ sobolevNorm ((m + 2 : ℕ) : ℝ) φ * Δ := mul_nonneg hN0 hΔ
    have hy : 0 ≤ sobolevNorm ((m + 2 : ℕ) : ℝ) φ * Real.sqrt Δ := mul_nonneg hN0 hs
    nlinarith [mul_nonneg hx hcX0, mul_nonneg hx hp, mul_nonneg hx hp2,
      mul_nonneg hx (mul_nonneg (abs_nonneg Cin) hCst.le), mul_nonneg hx (abs_nonneg Cin),
      mul_nonneg hy hcX0, mul_nonneg hy hp, mul_nonneg hy hp2,
      mul_nonneg hy (mul_nonneg (abs_nonneg Cin) hCst.le), mul_nonneg hy (abs_nonneg Cin), hx, hy]
  · -- the case `t > 0`
    have htI : t ∈ Set.Ioc 0 T := ⟨hpos, ht.2⟩
    have h0t : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, hpos.le⟩
    obtain ⟨⟨f₁, hcl₁, hpe₁⟩, hr₁⟩ := hu D₁ ρ₁ hA₁ htI hφc hφ
    obtain ⟨⟨f₂, hcl₂, hpe₂⟩, hr₂⟩ := hu D₂ ρ₂ hA₂ htI hφc hφ
    have hcont : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → Continuous ψ := fun ψ h =>
      ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by norm_num) h)
    set ψ₁ := propagator D₁ ρ₁ 0 t φ with hψ₁
    set ψ₂ := propagator D₂ ρ₂ 0 t φ with hψ₂
    obtain ⟨hm1₁, hC2₁, hg₁⟩ := hr₁ 0 h0t
    obtain ⟨hm1₂, hC2₂, hg₂⟩ := hr₂ 0 h0t
    have hc₁ : Continuous ψ₁ := hcont _ hC2₁
    have hc₂ : Continuous ψ₂ := hcont _ hC2₂
    have hm₁le : (m₁ : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m₁ ≤ m + 2)
    have hm₀m₁ : (m₀ : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast (le_max_left m₀ 1)
    obtain ⟨hs₁, hn₁⟩ := hm1₁ m₁ hm₁1 (by omega)
    obtain ⟨hs₂, hn₂⟩ := hm1₂ m₁ hm₁1 (by omega)
    have hmψ₁ : MemSobolev (m₀ : ℝ) ψ₁ := MFAdjoint.memSobolev_mono_idx hs₁ hm₀m₁
    have hmψ₂ : MemSobolev (m₀ : ℝ) ψ₂ := MFAdjoint.memSobolev_mono_idx hs₂ hm₀m₁
    set Nφ := sobolevNorm ((m + 2 : ℕ) : ℝ) φ with hNφ
    have hnorm : ∀ (ψ : Torus d → ℝ), MemSobolev (m₁ : ℝ) ψ →
        sobolevNorm (m₁ : ℝ) ψ ≤ K m₁ * sobolevNorm (m₁ : ℝ) φ →
        sobolevNorm (m₀ : ℝ) ψ ≤ K m₁ * Nφ := by
      intro ψ hψ hb
      refine (a34_sobolevNorm_mono hm₀m₁ hψ).trans (hb.trans ?_)
      exact mul_le_mul_of_nonneg_left (hφa _ hm₁le) (hK0 _)
    have hn₁' := hnorm ψ₁ hs₁ hn₁
    have hn₂' := hnorm ψ₂ hs₂ hn₂
    -- the stability estimate
    have hstab : ∀ r ∈ Set.Icc (0 : ℝ) t,
        MemSobolev (m : ℝ) (fun x => propagator D₁ ρ₁ r t φ x - propagator D₂ ρ₂ r t φ x) ∧
        sobolevNorm (m : ℝ) (fun x => propagator D₁ ρ₁ r t φ x - propagator D₂ ρ₂ r t φ x) ≤
          2 * Cst * Δ * Nφ := by
      intro r hr
      obtain ⟨h1, h2⟩ := hst D₁ D₂ ρ₁ ρ₂ hA₁ hA₂ hM hV Δ hρΔ htI hφc hφ hr
      refine ⟨h1, h2.trans ?_⟩
      have : Cst * (|D₁.invβ - D₂.invβ| + Δ) * Nφ ≤ Cst * (Δ + Δ) * Nφ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCst.le) hN0
      linarith
    have hJd : (d : ℝ) / 2 < ((m + 2 : ℕ) : ℝ) := by
      have h1 := a33_mStar_gt d
      have h2 : (mStar d : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hms
      linarith
    obtain ⟨hρ₁, hΛ₁⟩ := a34_rho (m + 2) hJd Rg s MB Λ VB ν₀ T D₁ ρ₁ hA₁
    obtain ⟨hρ₂, hΛ₂⟩ := a34_rho (m + 2) hJd Rg s MB Λ VB ν₀ T D₂ ρ₂ hA₂
    have hmst : (mStar d : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hms
    have hK₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖Torus.grad (propagator D₁ ρ₁ r t φ) x‖ ≤ K₂ * Nφ :=
      fun r hr x => ((hr₁ r hr).2.2 x).trans (mul_le_mul_of_nonneg_left (hφa _ hmst) hK₂0)
    have hK₂' : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖Torus.grad (propagator D₂ ρ₂ r t φ) x‖ ≤ K₂ * Nφ :=
      fun r hr x => ((hr₂ r hr).2.2 x).trans (mul_le_mul_of_nonneg_left (hφa _ hmst) hK₂0)
    have hδρ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₁ r x - ρ₂ r x| ≤ Δ := by
      intro r hr x
      have hIsCk : Torus.IsCk (m + 2) (fun y => ρ₁ r y - ρ₂ r y) :=
        ((hA₁.hμ.smooth r hr).of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 3))).sub
          ((hA₂.hμ.smooth r hr).of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 3)))
      exact (HRS.PDE.abs_le_cbNorm (m + 2) (fun y => ρ₁ r y - ρ₂ r y) hIsCk x).trans (hρΔ r hr)
    have hKN0 : 0 ≤ K₂ * Nφ := mul_nonneg hK₂0 hN0
    obtain ⟨hum₁, hub₁⟩ := a34_u_meas_bd D₁ ρ₁ t φ f₁ hcl₁ hpe₁ hKN0 hK₁
    obtain ⟨hum₂, hub₂⟩ := a34_u_meas_bd D₂ ρ₂ t φ f₂ hcl₂ hpe₂ hKN0 hK₂'
    have hq2 : 2 * q₂ ≤ 2 + Δ := by
      have := (abs_le.1 hqΔ).1
      linarith
    have hYsup := a34_Y_sup (T := T) hum₁ hum₂ hub₁ hub₂
    have hYH1 : ∫ p, ‖a34_u D₁ ρ₁ t φ p - a34_u D₂ ρ₂ t φ p‖ ^ 2 ∂(a33_mu0 d T) ≤
        t * (2 * Cst * Δ * Nφ) ^ 2 := by
      refine a34_Y_H1 ht D₁ D₂ ρ₁ ρ₂ hum₁ hum₂ hub₁ hub₂ (fun r hr => (hr₁ r hr).2.1)
        (fun r hr => (hr₂ r hr).2.1) (fun r hr => ?_)
      exact (a34_sobolevNorm_mono (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ)) (hstab r hr).1).trans
        (hstab r hr).2
    have hgauss : ∀ Y : ℝ, (∫ p, ‖a34_u D₁ ρ₁ t φ p - a34_u D₂ ρ₂ t φ p‖ ^ 2 ∂(a33_mu0 d T) ≤ Y) →
        |Real.sqrt (2 * q₁ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
            inner ℝ (Torus.grad (propagator D₁ ρ₁ r t φ) x) (Torus.grad (propagator D₁ ρ₁ r t φ) x) *
              ρ₁ r x) -
          Real.sqrt (2 * q₂ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
            inner ℝ (Torus.grad (propagator D₂ ρ₂ r t φ) x) (Torus.grad (propagator D₂ ρ₂ r t φ) x) *
              ρ₂ r x)| ≤
        Real.sqrt (2 * (K₂ * Nφ) ^ 2 * (Λ * Δ + 2 * q₂ * Δ) * M0 + 2 * (2 * q₂ * Λ) * Y) :=
      fun Y hY => a34_gauss_diff hpos ht.2 hρ₁ hρ₂ hΛ₁ hΛ₂ D₁ D₂ hq₁0 hq₂0 f₁ f₂ hcl₁ hcl₂ hpe₁ hpe₂
        hKN0 hK₁ hK₂' hδρ hqΔ hY
    have hvnn : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q : ℝ), 0 ≤ q → A33Rho T ρ →
        0 ≤ a34_cov D ρ q t φ := by
      intro D ρ q hq hρ
      unfold a34_cov
      refine mul_nonneg (by linarith) (setIntegral_nonneg measurableSet_Icc fun r hr => ?_)
      refine integral_nonneg fun x => ?_
      have hrt : r ≤ t := by simpa using hr.2
      have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hrt.trans ht.2⟩
      exact mul_nonneg real_inner_self_nonneg (hρ.nonneg r hrT x)
    refine ⟨hmψ₁, hc₁, hmψ₂, hc₂, hvnn D₁ ρ₁ q₁ hq₁0 hρ₁, hvnn D₂ ρ₂ q₂ hq₂0 hρ₂, ?_⟩
    have hCnn : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
    have hΔs : 0 ≤ Nφ * (Δ + Real.sqrt Δ) := mul_nonneg hN0 (add_nonneg hΔ hCnn)
    by_cases hΔ1 : Δ ≤ 1
    · have hA₂2 : |A₂| ≤ 2 := by
        have h := abs_sub_abs_le_abs_sub A₂ A₁
        rw [abs_sub_comm] at h
        linarith
      have hX := a34_X_diff hη hmψ₁ hmψ₂ hc₁ hc₂ A₁ A₂
      have hdiff : sobolevNorm (m₀ : ℝ) (fun x => ψ₁ x - ψ₂ x) ≤ 2 * Cst * Δ * Nφ :=
        (a34_sobolevNorm_mono (by exact_mod_cast hm₀ : (m₀ : ℝ) ≤ (m : ℝ)) (hstab 0 h0t).1).trans
          (hstab 0 h0t).2
      have hX' : ∫ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ∂P ≤ Δ * Nφ * (cX + 4 * |Cin| * Cst) := by
        refine hX.trans ?_
        have e1 : |A₁ - A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₁) ≤ Δ * (Nφ * cX) := by
          calc |A₁ - A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₁) ≤ Δ * (|Cin| * (K m₁ * Nφ)) :=
                mul_le_mul hAΔ (mul_le_mul_of_nonneg_left hn₁' (abs_nonneg _)) (by
                  exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hΔ
            _ = Δ * (Nφ * cX) := by rw [hcX]; ring
        have e2 : |A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) (fun x => ψ₁ x - ψ₂ x)) ≤
            2 * (|Cin| * (2 * Cst * Δ * Nφ)) :=
          mul_le_mul hA₂2 (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by norm_num)
        calc _ ≤ Δ * (Nφ * cX) + 2 * (|Cin| * (2 * Cst * Δ * Nφ)) := add_le_add e1 e2
          _ = Δ * Nφ * (cX + 4 * |Cin| * Cst) := by ring
      have hE := a34_num_E_small (N := Nφ) (Y := t * (2 * Cst * Δ * Nφ) ^ 2) hK₂0 hΛ0 hΔ hΔ1
        hq₂0 (by linarith) hM0nn hpos.le ht.2 hCst.le (le_refl _)
      have hσ : |Real.sqrt (2 * q₁ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
            inner ℝ (Torus.grad (propagator D₁ ρ₁ r t φ) x) (Torus.grad (propagator D₁ ρ₁ r t φ) x) *
              ρ₁ r x) -
          Real.sqrt (2 * q₂ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
            inner ℝ (Torus.grad (propagator D₂ ρ₂ r t φ) x) (Torus.grad (propagator D₂ ρ₂ r t φ) x) *
              ρ₂ r x)| ≤ Real.sqrt (cH1 * Nφ ^ 2 * Δ) :=
        (hgauss _ hYH1).trans (Real.sqrt_le_sqrt hE)
      have hfin := a34_num_small hΔ hΔ1 hN0 hcX0 hcH10 _ _ hX' hσ (abs_nonneg Cin) hCst.le
      refine hfin.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hΔ hCnn)
      have := Real.sqrt_nonneg cH2
      have h2 := abs_nonneg Cin
      refine mul_le_mul_of_nonneg_right ?_ hN0
      linarith
    · have hΔ1' : 1 < Δ := not_le.1 hΔ1
      have hA₂2 : |A₂| ≤ 1 + Δ := by
        have h := abs_sub_abs_le_abs_sub A₂ A₁
        rw [abs_sub_comm] at h
        linarith
      have hX := a34_X_crude hη hmψ₁ hmψ₂ hc₁ hc₂ A₁ A₂
      have hX' : ∫ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ∂P ≤ 3 * Δ * (cX * Nφ) := by
        refine hX.trans ?_
        have e1 : |A₁| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₁) ≤ 1 * (cX * Nφ) := by
          refine mul_le_mul hA₁1 ?_ (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) zero_le_one
          calc |Cin| * sobolevNorm (m₀ : ℝ) ψ₁ ≤ |Cin| * (K m₁ * Nφ) :=
                mul_le_mul_of_nonneg_left hn₁' (abs_nonneg _)
            _ = cX * Nφ := by rw [hcX]; ring
        have e2 : |A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₂) ≤ (1 + Δ) * (cX * Nφ) := by
          refine mul_le_mul hA₂2 ?_ (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
          calc |Cin| * sobolevNorm (m₀ : ℝ) ψ₂ ≤ |Cin| * (K m₁ * Nφ) :=
                mul_le_mul_of_nonneg_left hn₂' (abs_nonneg _)
            _ = cX * Nφ := by rw [hcX]; ring
        have hp : 0 ≤ cX * Nφ := mul_nonneg hcX0 hN0
        calc _ ≤ 1 * (cX * Nφ) + (1 + Δ) * (cX * Nφ) := add_le_add e1 e2
          _ ≤ 3 * Δ * (cX * Nφ) := by linarith [mul_nonneg hp (sub_nonneg.2 hΔ1'.le)]
      have hE := a34_num_E_large (Y := (K₂ * Nφ + K₂ * Nφ) ^ 2 * M0) hK₂0 hΛ0 hΔ1' hq₂0 hq2 hM0nn
        hN0 le_rfl
      have hσ : |Real.sqrt (2 * q₁ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
            inner ℝ (Torus.grad (propagator D₁ ρ₁ r t φ) x) (Torus.grad (propagator D₁ ρ₁ r t φ) x) *
              ρ₁ r x) -
          Real.sqrt (2 * q₂ * ∫ r in Set.Icc 0 (min t t), ∫ x : Torus d,
            inner ℝ (Torus.grad (propagator D₂ ρ₂ r t φ) x) (Torus.grad (propagator D₂ ρ₂ r t φ) x) *
              ρ₂ r x)| ≤ Real.sqrt (cH2 * Nφ ^ 2 * Δ ^ 2) :=
        (hgauss _ hYsup).trans (Real.sqrt_le_sqrt hE)
      have hfin := a34_num_large hΔ1' hN0 hcX0 hcH20 _ _ hX' hσ (abs_nonneg Cin) hCst.le
      refine hfin.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hΔ hCnn)
      have := Real.sqrt_nonneg cH1
      have h2 := abs_nonneg Cin
      refine mul_le_mul_of_nonneg_right ?_ hN0
      linarith

/-- Quantitative stability of the surrogate statistic for abstract coefficient data. -/
theorem a34_stat_abstract (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T Cin : ℝ) (m m₀ : ℕ) (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (hms : mStar d ≤ m + 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D₁ D₂ : DynData d) (ρ₁ ρ₂ : ℝ → Torus d → ℝ) (A₁ A₂ q₁ q₂ Δ : ℝ),
        AdjointData s (m + 2) Rg MB Λ VB D₁ ν₀ T ρ₁ →
        AdjointData s (m + 2) Rg MB Λ VB D₂ ν₀ T ρ₂ → D₁.M = D₂.M → D₁.V = D₂.V → 0 ≤ Δ →
        (∀ r ∈ Set.Icc (0 : ℝ) T, Torus.cbNorm (m + 2) (ρ₁ r - ρ₂ r) ≤ Δ) →
        |D₁.invβ - D₂.invβ| ≤ Δ → 0 ≤ q₁ → q₁ ≤ 1 → 0 ≤ q₂ → |2 * q₁ - 2 * q₂| ≤ Δ →
        |A₁| ≤ 1 → |A₁ - A₂| ≤ Δ →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (η : Ω → (Torus d → ℝ) → ℝ), XHyp P η m₀ Cin →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, MemSobolev ((m + 2 : ℕ) : ℝ) φ →
          Continuous φ →
          wassersteinE 1 (surrogateStatLaw D₁ ρ₁ A₁ q₁ (fun _ : Fin 1 => t) (fun _ => φ) P η)
            (surrogateStatLaw D₂ ρ₂ A₂ q₂ (fun _ : Fin 1 => t) (fun _ => φ) P η) ≤
          ENNReal.ofReal (C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ * (Δ + Real.sqrt Δ)) := by
  obtain ⟨C, hC, h⟩ := a34_stat_real hd s hs0 hsd Rg ν₀ MB Λ VB T Cin m m₀ hm hm₀ hms
  refine ⟨C, hC, ?_⟩
  intro D₁ D₂ ρ₁ ρ₂ A₁ A₂ q₁ q₂ Δ hA₁ hA₂ hM hV hΔ hρΔ hβΔ hq₁0 hq₁1 hq₂0 hqΔ hA₁1 hAΔ
    Ω _ P _ η hη t ht φ hφ hφc
  obtain ⟨hm₁, hc₁, hm₂, hc₂, hv₁, hv₂, hbd⟩ := h D₁ D₂ ρ₁ ρ₂ A₁ A₂ q₁ q₂ Δ hA₁ hA₂ hM hV hΔ hρΔ
    hβΔ hq₁0 hq₁1 hq₂0 hqΔ hA₁1 hAΔ P η hη t ht φ hφ hφc
  rw [a34_stat_unfold, a34_stat_unfold]
  refine (a34_W1_conv P (fun ω => A₁ * η ω (propagator D₁ ρ₁ 0 t φ))
    (fun ω => A₂ * η ω (propagator D₂ ρ₂ 0 t φ)) ((hη.meas _).const_mul _) ((hη.meas _).const_mul _)
    ((a34_X_integrable hη hm₁ hc₁ A₁).sub (a34_X_integrable hη hm₂ hc₂ A₂)) _ _ hv₁ hv₂).trans ?_
  exact ENNReal.ofReal_le_ofReal hbd

end HRS.A34

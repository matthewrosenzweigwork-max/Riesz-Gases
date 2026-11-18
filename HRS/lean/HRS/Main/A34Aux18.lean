import HRS.Main.A34Aux17

/-!
# Packet A34, helper 18: `L²(μ₀)` comparison of the noise vectors of two coefficient sets, and the
mode-wise estimate
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_h_diff {T t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) {ρ₁ ρ₂ : ℝ → Torus d → ℝ}
    (hρ₁ : A33Rho T ρ₁) (hρ₂ : A33Rho T ρ₂) {Λ : ℝ}
    (hΛ₁ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₁ r x| ≤ Λ)
    (hΛ₂ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₂ r x| ≤ Λ) (D₁ D₂ : DynData d) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) {φ₁ φ₂ : Torus d → ℝ}
    (f₁ f₂ : ℝ → Torus d → ℝ) (hcl₁ : IsClassicalAdjointSolution D₁ ρ₁ t φ₁ f₁)
    (hcl₂ : IsClassicalAdjointSolution D₂ ρ₂ t φ₂ f₂)
    (hpe₁ : ∀ r ∈ Set.Icc 0 t, propagator D₁ ρ₁ r t φ₁ = f₁ r)
    (hpe₂ : ∀ r ∈ Set.Icc 0 t, propagator D₂ ρ₂ r t φ₂ = f₂ r) {K : ℝ} (hK0 : 0 ≤ K)
    (hK₁ : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Torus.grad (propagator D₁ ρ₁ r t φ₁) x‖ ≤ K)
    (hK₂ : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Torus.grad (propagator D₂ ρ₂ r t φ₂) x‖ ≤ K)
    {δρ δq : ℝ} (hδρ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₁ r x - ρ₂ r x| ≤ δρ)
    (hδq : |2 * q₁ - 2 * q₂| ≤ δq) {Y : ℝ}
    (hY : ∫ p, ‖a34_u D₁ ρ₁ t φ₁ p - a34_u D₂ ρ₂ t φ₂ p‖ ^ 2 ∂(a33_mu0 d T) ≤ Y) :
    ∫ p, ‖a34_h D₁ ρ₁ q₁ t φ₁ p - a34_h D₂ ρ₂ q₂ t φ₂ p‖ ^ 2 ∂(a33_mu0 d T) ≤
    2 * K ^ 2 * (Λ * δq + 2 * q₂ * δρ) * (a33_mu0 d T).real Set.univ +
      2 * (2 * q₂ * Λ) * Y := by
  classical
  have htI : t ∈ Set.Icc 0 T := ⟨ht0.le, htT⟩
  obtain ⟨hm₁, hb₁⟩ := a34_u_meas_bd D₁ ρ₁ t φ₁ f₁ hcl₁ hpe₁ hK0 hK₁
  obtain ⟨hm₂, hb₂⟩ := a34_u_meas_bd D₂ ρ₂ t φ₂ f₂ hcl₂ hpe₂ hK0 hK₂
  have hge₁ := a34_g_eq_u D₁ ρ₁ q₁ t φ₁ ht0
  have hge₂ := a34_g_eq_u D₂ ρ₂ q₂ t φ₂ ht0
  have hgm₁ : Measurable (a33_g D₁ ρ₁ q₁ t φ₁) := by rw [hge₁]; exact hm₁.const_smul (Real.sqrt (2 * q₁))
  have hgm₂ : Measurable (a33_g D₂ ρ₂ q₂ t φ₂) := by rw [hge₂]; exact hm₂.const_smul (Real.sqrt (2 * q₂))
  have hgb₁ : ∀ p, ‖a33_g D₁ ρ₁ q₁ t φ₁ p‖ ≤ Real.sqrt (2 * q₁) * K := fun p => by
    rw [hge₁]; simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hb₁ p) (Real.sqrt_nonneg _)
  have hgb₂ : ∀ p, ‖a33_g D₂ ρ₂ q₂ t φ₂ p‖ ≤ Real.sqrt (2 * q₂) * K := fun p => by
    rw [hge₂]; simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hb₂ p) (Real.sqrt_nonneg _)
  set μ := a33_mu0 d T with hμ
  have : IsFiniteMeasure μ := inferInstance
  -- the functions `a_i`
  set a₁ : ℝ × Torus d → ℝ := fun p => Real.sqrt (ρ₁ p.1 p.2) * Real.sqrt (2 * q₁) with ha₁def
  set a₂ : ℝ × Torus d → ℝ := fun p => Real.sqrt (ρ₂ p.1 p.2) * Real.sqrt (2 * q₂) with ha₂def
  have ha₁m : AEMeasurable a₁ μ := (hρ₁.aemeasurable.sqrt).mul_const _
  have ha₂m : AEMeasurable a₂ μ := (hρ₂.aemeasurable.sqrt).mul_const _
  have hh₁ := a34_h_eq D₁ ρ₁ q₁ t φ₁ ht0
  have hh₂ := a34_h_eq D₂ ρ₂ q₂ t φ₂ ht0
  have hae := a33_ae_mu0 (d := d) T
  have e₁₂ : (∫ p, ‖a34_h D₁ ρ₁ q₁ t φ₁ p - a34_h D₂ ρ₂ q₂ t φ₂ p‖ ^ 2 ∂μ) =
      ∫ p, ‖a₁ p • a34_u D₁ ρ₁ t φ₁ p - a₂ p • a34_u D₂ ρ₂ t φ₂ p‖ ^ 2 ∂μ := by
    rw [hh₁, hh₂]
  rw [e₁₂]
  refine a34_E1 (hm₁.aemeasurable) (hm₂.aemeasurable) ha₁m ha₂m (K := K)
    (Eventually.of_forall hb₁) (Eventually.of_forall hb₂) (ε := Λ * δq + 2 * q₂ * δρ)
    (B := 2 * q₂ * Λ) ?_ ?_ ?_ hY (M := Real.sqrt Λ * Real.sqrt (2 * q₁) * K +
      Real.sqrt Λ * Real.sqrt (2 * q₂) * K) ?_
  · -- 0 ≤ B
    have : 0 ≤ Λ := by
      have := hΛ₁ 0 ⟨le_rfl, (ht0.le.trans htT)⟩ (Classical.arbitrary _)
      exact (abs_nonneg _).trans this
    positivity
  · filter_upwards [hae] with p hp
    have h1 := hρ₁.nonneg p.1 hp p.2
    have h2 := hρ₂.nonneg p.1 hp p.2
    have e1 : a₁ p = Real.sqrt (ρ₁ p.1 p.2 * (2 * q₁)) := by
      simp only [ha₁def]; rw [Real.sqrt_mul h1]
    have e2 : a₂ p = Real.sqrt (ρ₂ p.1 p.2 * (2 * q₂)) := by
      simp only [ha₂def]; rw [Real.sqrt_mul h2]
    rw [e1, e2]
    refine (a34_sq_sub_sqrt_le (mul_nonneg h1 (by linarith)) (mul_nonneg h2 (by linarith))).trans ?_
    have : ρ₁ p.1 p.2 * (2 * q₁) - ρ₂ p.1 p.2 * (2 * q₂) =
        ρ₁ p.1 p.2 * (2 * q₁ - 2 * q₂) + (2 * q₂) * (ρ₁ p.1 p.2 - ρ₂ p.1 p.2) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hΛ₁ p.1 hp p.2) hδq (abs_nonneg _) ((abs_nonneg _).trans (hΛ₁ p.1 hp p.2))
    · rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * q₂)]
      exact mul_le_mul_of_nonneg_left (hδρ p.1 hp p.2) (by linarith)
  · filter_upwards [hae] with p hp
    have h2 := hρ₂.nonneg p.1 hp p.2
    simp only [ha₂def]
    rw [mul_pow, Real.sq_sqrt h2, Real.sq_sqrt (by linarith)]
    calc ρ₂ p.1 p.2 * (2 * q₂) ≤ Λ * (2 * q₂) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hΛ₂ p.1 hp p.2)) (by linarith)
      _ = 2 * q₂ * Λ := by ring
  · filter_upwards [hae] with p hp
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, show a₁ p = _ from rfl]
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      refine mul_le_mul ?_ (hb₁ p) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ((le_abs_self _).trans (hΛ₁ p.1 hp p.2)))
        (Real.sqrt_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs, show a₂ p = _ from rfl]
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      refine mul_le_mul ?_ (hb₂ p) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ((le_abs_self _).trans (hΛ₂ p.1 hp p.2)))
        (Real.sqrt_nonneg _)


theorem a34_h_diff_field (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D₁ D₂ : DynData d) (ρ₁ ρ₂ : ℝ → Torus d → ℝ) (q₁ q₂ Δ : ℝ),
        AdjointData s (mStar d + 2) Rg MB Λ VB D₁ ν₀ T ρ₁ →
        AdjointData s (mStar d + 2) Rg MB Λ VB D₂ ν₀ T ρ₂ → D₁.M = D₂.M → D₁.V = D₂.V →
        0 ≤ Δ → (∀ r ∈ Set.Icc (0 : ℝ) T, Torus.cbNorm (mStar d + 2) (ρ₁ r - ρ₂ r) ≤ Δ) →
        |D₁.invβ - D₂.invβ| ≤ Δ → 0 ≤ q₁ → q₁ ≤ 1 → 0 ≤ q₂ → |2 * q₁ - 2 * q₂| ≤ Δ →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Continuous φ →
          MemSobolev ((mStar d + 2 : ℕ) : ℝ) φ →
          ∫ p, ‖a34_h D₁ ρ₁ q₁ t φ p - a34_h D₂ ρ₂ q₂ t φ p‖ ^ 2 ∂(a33_mu0 d T) ≤
            C * (Δ + Δ ^ 2) * sobolevNorm ((mStar d + 2 : ℕ) : ℝ) φ ^ 2 := by
  have hm3 := ClassicalPart.three_le_mStar d
  have hms : mStar d ≤ mStar d + 2 := by omega
  have hm1 : 1 ≤ mStar d := by omega
  obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd (mStar d + 2) hms Rg MB Λ VB ν₀ T
  obtain ⟨Cst, hCst, hst⟩ := a34_stab hd s hs0 hsd (mStar d) hm1 hms Rg MB Λ VB ν₀ T
  set M0 : ℝ := (a33_mu0 d T).real Set.univ with hM0
  have hM0nn : 0 ≤ M0 := measureReal_nonneg
  set cH1 : ℝ := 2 * K₂ ^ 2 * (|Λ| + 3) * M0 + 24 * |Λ| * |T| * Cst ^ 2 with hcH1
  set cH2 : ℝ := K₂ ^ 2 * M0 * (26 * |Λ| + 6) with hcH2
  have hcH10 : 0 ≤ cH1 := by positivity
  have hcH20 : 0 ≤ cH2 := by positivity
  refine ⟨cH1 + cH2 + 1, by positivity, ?_⟩
  intro D₁ D₂ ρ₁ ρ₂ q₁ q₂ Δ hA₁ hA₂ hM hV hΔ hρΔ hβΔ hq₁0 hq₁1 hq₂0 hqΔ t ht φ hφc hφ
  set Nφ := sobolevNorm ((mStar d + 2 : ℕ) : ℝ) φ with hNφ
  have hN0 : 0 ≤ Nφ := Real.sqrt_nonneg _
  have hΛ0 : 0 ≤ Λ := by
    have := (hA₁.hμ.bound 0 ⟨le_rfl, hA₁.hT.le⟩)
    exact (Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _).trans this
  have hRHS0 : 0 ≤ (cH1 + cH2 + 1) * (Δ + Δ ^ 2) * Nφ ^ 2 := by positivity
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hz : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q : ℝ), a34_h D ρ q 0 φ = 0 := by
      intro D ρ q
      funext p
      simp [a34_h, a34_g_zero D ρ q 0 φ (lt_irrefl 0)]
    simp only [hz, sub_self, norm_zero]
    simpa using hRHS0
  · have htI : t ∈ Set.Ioc 0 T := ⟨hpos, ht.2⟩
    obtain ⟨⟨f₁, hcl₁, hpe₁⟩, hr₁⟩ := hu D₁ ρ₁ hA₁ htI hφc hφ
    obtain ⟨⟨f₂, hcl₂, hpe₂⟩, hr₂⟩ := hu D₂ ρ₂ hA₂ htI hφc hφ
    have hJd : (d : ℝ) / 2 < ((mStar d + 2 : ℕ) : ℝ) := by
      have h1 := a33_mStar_gt d
      push_cast; linarith
    obtain ⟨hρ₁, hΛ₁⟩ := a34_rho (mStar d + 2) hJd Rg s MB Λ VB ν₀ T D₁ ρ₁ hA₁
    obtain ⟨hρ₂, hΛ₂⟩ := a34_rho (mStar d + 2) hJd Rg s MB Λ VB ν₀ T D₂ ρ₂ hA₂
    have hmst : (mStar d : ℝ) ≤ ((mStar d + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hφa : ∀ a : ℝ, a ≤ ((mStar d + 2 : ℕ) : ℝ) → sobolevNorm a φ ≤ Nφ :=
      fun a ha => a34_sobolevNorm_mono ha hφ
    have hK₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖Torus.grad (propagator D₁ ρ₁ r t φ) x‖ ≤ K₂ * Nφ :=
      fun r hr x => ((hr₁ r hr).2.2 x).trans (mul_le_mul_of_nonneg_left (hφa _ hmst) hK₂0)
    have hK₂' : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖Torus.grad (propagator D₂ ρ₂ r t φ) x‖ ≤ K₂ * Nφ :=
      fun r hr x => ((hr₂ r hr).2.2 x).trans (mul_le_mul_of_nonneg_left (hφa _ hmst) hK₂0)
    have hδρ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |ρ₁ r x - ρ₂ r x| ≤ Δ := by
      intro r hr x
      have hIsCk : Torus.IsCk (mStar d + 2) (fun y => ρ₁ r y - ρ₂ r y) :=
        ((hA₁.hμ.smooth r hr).of_le (by exact_mod_cast (by omega : mStar d + 2 ≤ mStar d + 2 + 3))).sub
          ((hA₂.hμ.smooth r hr).of_le (by exact_mod_cast (by omega : mStar d + 2 ≤ mStar d + 2 + 3)))
      exact (HRS.PDE.abs_le_cbNorm (mStar d + 2) (fun y => ρ₁ r y - ρ₂ r y) hIsCk x).trans (hρΔ r hr)
    have hKN0 : 0 ≤ K₂ * Nφ := mul_nonneg hK₂0 hN0
    obtain ⟨hum₁, hub₁⟩ := a34_u_meas_bd D₁ ρ₁ t φ f₁ hcl₁ hpe₁ hKN0 hK₁
    obtain ⟨hum₂, hub₂⟩ := a34_u_meas_bd D₂ ρ₂ t φ f₂ hcl₂ hpe₂ hKN0 hK₂'
    have hq2 : 2 * q₂ ≤ 2 + Δ := by
      have := (abs_le.1 hqΔ).1
      linarith
    have hstab : ∀ r ∈ Set.Icc (0 : ℝ) t,
        sobolevNorm 1 (fun x => propagator D₁ ρ₁ r t φ x - propagator D₂ ρ₂ r t φ x) ≤
          2 * Cst * Δ * Nφ := by
      intro r hr
      obtain ⟨h1, h2⟩ := hst D₁ D₂ ρ₁ ρ₂ hA₁ hA₂ hM hV Δ hρΔ htI hφc hφ hr
      have h3 : Cst * (|D₁.invβ - D₂.invβ| + Δ) * Nφ ≤ Cst * (Δ + Δ) * Nφ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCst.le) hN0
      have h4 := a34_sobolevNorm_mono (by exact_mod_cast hm1 : (1 : ℝ) ≤ (mStar d : ℝ)) h1
      have h5 : (2 : ℝ) * Cst * Δ * Nφ = Cst * (Δ + Δ) * Nφ := by ring
      rw [h5]
      exact h4.trans (h2.trans h3)
    have hYsup := a34_Y_sup (T := T) hum₁ hum₂ hub₁ hub₂
    have hYH1 : ∫ p, ‖a34_u D₁ ρ₁ t φ p - a34_u D₂ ρ₂ t φ p‖ ^ 2 ∂(a33_mu0 d T) ≤
        t * (2 * Cst * Δ * Nφ) ^ 2 :=
      a34_Y_H1 ht D₁ D₂ ρ₁ ρ₂ hum₁ hum₂ hub₁ hub₂ (fun r hr => (hr₁ r hr).2.1)
        (fun r hr => (hr₂ r hr).2.1) hstab
    by_cases hΔ1 : Δ ≤ 1
    · have hh := a34_h_diff hpos ht.2 hρ₁ hρ₂ hΛ₁ hΛ₂ D₁ D₂ hq₁0 hq₂0 f₁ f₂ hcl₁ hcl₂ hpe₁ hpe₂
        hKN0 hK₁ hK₂' hδρ hqΔ hYH1
      have hE := a34_num_E_small (N := Nφ) (Y := t * (2 * Cst * Δ * Nφ) ^ 2) hK₂0 hΛ0 hΔ hΔ1
        hq₂0 (by linarith) hM0nn hpos.le ht.2 hCst.le (le_refl _)
      refine hh.trans (hE.trans ?_)
      have : cH1 * Nφ ^ 2 * Δ ≤ (cH1 + cH2 + 1) * (Δ + Δ ^ 2) * Nφ ^ 2 := by
        have h1 : 0 ≤ cH1 * Nφ ^ 2 := by positivity
        nlinarith [mul_nonneg h1 hΔ, mul_nonneg (mul_nonneg hcH20 (sq_nonneg Nφ)) hΔ,
          mul_nonneg (mul_nonneg hcH20 (sq_nonneg Nφ)) (sq_nonneg Δ), mul_nonneg h1 (sq_nonneg Δ),
          mul_nonneg (sq_nonneg Nφ) hΔ, mul_nonneg (sq_nonneg Nφ) (sq_nonneg Δ)]
      exact this
    · have hΔ1' : 1 < Δ := not_le.1 hΔ1
      have hh := a34_h_diff hpos ht.2 hρ₁ hρ₂ hΛ₁ hΛ₂ D₁ D₂ hq₁0 hq₂0 f₁ f₂ hcl₁ hcl₂ hpe₁ hpe₂
        hKN0 hK₁ hK₂' hδρ hqΔ hYsup
      have hE := a34_num_E_large (Y := (K₂ * Nφ + K₂ * Nφ) ^ 2 * M0) hK₂0 hΛ0 hΔ1' hq₂0 hq2 hM0nn
        hN0 le_rfl
      refine hh.trans (hE.trans ?_)
      have : cH2 * Nφ ^ 2 * Δ ^ 2 ≤ (cH1 + cH2 + 1) * (Δ + Δ ^ 2) * Nφ ^ 2 := by
        have h1 : 0 ≤ cH2 * Nφ ^ 2 := by positivity
        nlinarith [mul_nonneg h1 hΔ, mul_nonneg (mul_nonneg hcH10 (sq_nonneg Nφ)) hΔ,
          mul_nonneg (mul_nonneg hcH10 (sq_nonneg Nφ)) (sq_nonneg Δ), mul_nonneg h1 (sq_nonneg Δ),
          mul_nonneg (sq_nonneg Nφ) hΔ, mul_nonneg (sq_nonneg Nφ) (sq_nonneg Δ)]
      exact this

end HRS.A34

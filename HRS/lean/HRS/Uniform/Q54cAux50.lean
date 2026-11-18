import HRS.Uniform.Q54cAux49

/-!
# Q54c, part 50: the core comparison theorem
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Uniform

variable {d : ℕ}

namespace PdeSetup

set_option maxHeartbeats 2000000 in
theorem core_comparison (P : PdeSetup d) (cc : P.CmpConst) (hn2 : (d : ℝ) / 2 + 2 < (P.n : ℝ))
    (ν₀ : ℝ) (D₁ D₂ : DynData d) (μ₁ μ₂ : ℝ → Torus d → ℝ)
    (h₁ : P.Data D₁ ν₀ μ₁) (h₂ : P.Data D₂ ν₀ μ₂) (hM : D₁.M = D₂.M) (hV : D₁.V = D₂.V)
    (q₁ q₂ A₁ A₂ δ : ℝ) (hq₁ : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1) (hq₂ : 0 ≤ q₂) (hA₁ : |A₁| ≤ 1)
    (hδ : ∀ r ∈ Set.Icc 0 P.T, Torus.cbNorm (P.n + 4) (μ₁ r - μ₂ r) ≤ δ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (PΩ : Measure Ω) [IsProbabilityMeasure PΩ]
    (η₀ : Ω → NegSobolev d ((P.n : ℝ) + 2)) (hη₀ : Measurable η₀)
    (Y₁ Y₂ : ℝ → Ω → NegSobolev d ((P.n : ℝ) + 4))
    (hY₁ : IsLinearFluctuationSolution PΩ D₁ μ₁ ((P.n : ℝ) + 4) q₁ P.T
      (fun ω => A₁ • NegSobolev.embed ((P.n : ℝ) + 4) (η₀ ω)) Y₁)
    (hY₂ : IsLinearFluctuationSolution PΩ D₂ μ₂ ((P.n : ℝ) + 4) q₂ P.T
      (fun ω => A₂ • NegSobolev.embed ((P.n : ℝ) + 4) (η₀ ω)) Y₂) :
    wassersteinE 2 (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁)) (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂)) ≤
      ENNReal.ofReal (P.Ccore cc) * (1 + eLpNorm η₀ 2 PΩ) *
        ENNReal.ofReal ((|D₁.invβ - D₂.invβ| + |q₁ - q₂| + |A₁ - A₂| + δ) +
          Real.sqrt (|D₁.invβ - D₂.invβ| + |q₁ - q₂| + |A₁ - A₂| + δ)) := by
  have hT : 0 < P.T := h₁.hA.hT
  have hδ0 : 0 ≤ δ := (cbNorm_nonneg_q _ _).trans (hδ 0 ⟨le_rfl, hT.le⟩)
  -- data for the noise bundle
  have hprob₁ : ∀ σ ∈ Set.Icc 0 P.T, IsProbDensity (μ₁ σ) := h₁.hA.hμ.prob
  have hprob₂ : ∀ σ ∈ Set.Icc 0 P.T, IsProbDensity (μ₂ σ) := h₂.hA.hμ.prob
  have hck : ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ), P.Data D ν₀ μ → ∀ σ ∈ Set.Icc 0 P.T,
      Torus.IsCk ((P.n + 4 : ℕ) : WithTop ℕ∞) (μ σ) := fun D μ h σ hσ =>
    (h.hA.hμ.smooth σ hσ).of_le (by exact_mod_cast (by omega : P.n + 4 ≤ P.n + 4 + 3))
  have hcts₁ : ∀ σ ∈ Set.Icc 0 P.T, Continuous (μ₁ σ) := fun σ hσ =>
    HRS.PDE.ClassicalAux.continuous_of_isCk (HRS.PDE.ClassicalAux.isCk_of_le
      (by exact_mod_cast (by omega : 1 ≤ P.n + 4 + 3)) (h₁.hA.hμ.smooth σ hσ))
  have hcts₂ : ∀ σ ∈ Set.Icc 0 P.T, Continuous (μ₂ σ) := fun σ hσ =>
    HRS.PDE.ClassicalAux.continuous_of_isCk (HRS.PDE.ClassicalAux.isCk_of_le
      (by exact_mod_cast (by omega : 1 ≤ P.n + 4 + 3)) (h₂.hA.hμ.smooth σ hσ))
  have hδ' : ∀ σ ∈ Set.Icc 0 P.T, ∀ x, |μ₁ σ x - μ₂ σ x| ≤ δ := by
    intro σ hσ x
    have hk : Torus.IsCk ((P.n + 4 : ℕ) : WithTop ℕ∞) (μ₁ σ - μ₂ σ) :=
      HRS.PDE.StabAux.isCk_sub' (hck D₁ μ₁ h₁ σ hσ) (hck D₂ μ₂ h₂ σ hσ)
    have := HRS.PDE.R2Aux.abs_le_cbNorm hk x
    exact this.trans (hδ σ hσ)
  obtain ⟨Ω', mΩ', P', hP', ℱ', G₁, G₂, hc₁, hc₂, hz₁, hz₂, hM₁, hM₂, hbdD, hbdM⟩ :=
    noise_bundle hn2 hT hq₁ hq₂ hprob₁ hprob₂ h₁.hA.hμ.cont h₂.hA.hμ.cont hcts₁ hcts₂ hδ'
  haveI := hP'
  let ℱΩ : Filtration ℝ mΩ := Filtration.const ℝ mΩ le_rfl
  let ℱ₃ := prodFiltration P' PΩ ℱ' ℱΩ
  set P₃ : Measure (Ω' × Ω) := P'.prod PΩ with hP₃
  set Gh₁ : ℝ → Ω' × Ω → NegSobolev d (P.n : ℝ) := fun τ p => G₁ τ p.1 with hGh₁def
  set Gh₂ : ℝ → Ω' × Ω → NegSobolev d (P.n : ℝ) := fun τ p => G₂ τ p.1 with hGh₂def
  set ηh : Ω' × Ω → NegSobolev d ((P.n : ℝ) + 2) := fun p => η₀ p.2 with hηhdef
  have hηh : Measurable ηh := hη₀.comp measurable_snd
  have hGh₁ : IsHilbertMartingaleWithCovariation P₃ ℱ₃ P.T Gh₁ (fun r _ => covDens (P.n : ℝ) q₁ P.T μ₁ r) :=
    hM₁.comp_fst' ℱΩ
  have hGh₂ : IsHilbertMartingaleWithCovariation P₃ ℱ₃ P.T Gh₂ (fun r _ => covDens (P.n : ℝ) q₂ P.T μ₂ r) :=
    hM₂.comp_fst' ℱΩ
  have hGm₁ : ∀ τ, Measurable (G₁ τ) := fun τ => HRS.Uniform.Q07c.measurable_of_isHM hM₁ τ
  have hGm₂ : ∀ τ, Measurable (G₂ τ) := fun τ => HRS.Uniform.Q07c.measurable_of_isHM hM₂ τ
  have hGhm₁ : ∀ τ, Measurable (Gh₁ τ) := fun τ => (hGm₁ τ).comp measurable_fst
  have hGhm₂ : ∀ τ, Measurable (Gh₂ τ) := fun τ => (hGm₂ τ).comp measurable_fst
  have hGhc₁ : ∀ p : Ω' × Ω, Continuous fun s => Gh₁ s p := fun p => hc₁ p.1
  have hGhc₂ : ∀ p : Ω' × Ω, Continuous fun s => Gh₂ s p := fun p => hc₂ p.1
  have hGhz₁ : ∀ p : Ω' × Ω, Gh₁ 0 p = 0 := fun p => hz₁ p.1
  have hGhz₂ : ∀ p : Ω' × Ω, Gh₂ 0 p = 0 := fun p => hz₂ p.1
  have hind₁ := indep_prod_aux P' PΩ η₀ hη₀ G₁ hGm₁ {τ : ℝ | 0 ≤ τ ∧ τ ≤ P.T}
  have hind₂ := indep_prod_aux P' PΩ η₀ hη₀ G₂ hGm₂ {τ : ℝ | 0 ≤ τ ∧ τ ≤ P.T}
  have hlawη : P₃.map ηh = PΩ.map η₀ := map_prod_snd P' PΩ η₀ hη₀
  have hfdd₁ := h₁.fdd_eq hn2 hq₁ hT PΩ P₃ A₁ η₀ hη₀ Y₁ hY₁ ηh hηh hlawη Gh₁ hGh₁ hGhc₁ hGhz₁ hGhm₁ hind₁
  have hfdd₂ := h₂.fdd_eq hn2 hq₂ hT PΩ P₃ A₂ η₀ hη₀ Y₂ hY₂ ηh hηh hlawη Gh₂ hGh₂ hGhc₂ hGhz₂ hGhm₂ hind₂
  set Yh₁ := (P.pd D₁ μ₁).Yproc P.T A₁ ηh Gh₁ with hYh₁
  set Yh₂ := (P.pd D₂ μ₂).Yproc P.T A₂ ηh Gh₂ with hYh₂
  have hYhc₁ : ∀ p, ContinuousOn (fun t => Yh₁ t p) (Set.Icc 0 P.T) := fun p =>
    (Ypath_continuous h₁.spec_pd (hGhc₁ p).continuousOn A₁ (ηh p)).continuousOn
  have hYhc₂ : ∀ p, ContinuousOn (fun t => Yh₂ t p) (Set.Icc 0 P.T) := fun p =>
    (Ypath_continuous h₂.spec_pd (hGhc₂ p).continuousOn A₂ (ηh p)).continuousOn
  have hYhm₁ : ∀ t, Measurable (Yh₁ t) := fun t =>
    Yproc_measurable h₁.spec_pd hGhm₁ hGhc₁ hGhz₁ A₁ hηh t
  have hYhm₂ : ∀ t, Measurable (Yh₂ t) := fun t =>
    Yproc_measurable h₂.spec_pd hGhm₂ hGhc₂ hGhz₂ A₂ hηh t
  have hlaw₁ : law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁) = law P₃ (toPath ((P.n : ℝ) + 4) P.T Yh₁) :=
    toPath_law_eq hT.le PΩ P₃ Y₁ Yh₁ hY₁.meas hYhm₁ hY₁.cont (Filter.Eventually.of_forall hYhc₁) hfdd₁
  have hlaw₂ : law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂) = law P₃ (toPath ((P.n : ℝ) + 4) P.T Yh₂) :=
    toPath_law_eq hT.le PΩ P₃ Y₂ Yh₂ hY₂.meas hYhm₂ hY₂.cont (Filter.Eventually.of_forall hYhc₂) hfdd₂
  rw [hlaw₁, hlaw₂]
  -- constants
  set S := HRS.Uniform.Q14.q14S d ((P.n : ℝ) - 1) with hS
  have hS0 : 0 ≤ S := HRS.Uniform.Q14.q14S_nonneg d _
  set Bd := HilbertBDG.bdgConst 2 with hBd
  have hBd0 : 0 ≤ Bd := HilbertBDG.bdgConst_nonneg 2
  set Γ := Real.sqrt (Bd * (4 * d * S * |P.T|)) with hΓ
  have hΓ0 : 0 ≤ Γ := Real.sqrt_nonneg _
  have hTabs : |P.T| = P.T := abs_of_pos hT
  set Kc := P.Kc with hKc
  have hKc0 : 0 ≤ Kc := P.Kc_nonneg
  set Cst := cc.Cst with hCst
  have hCst0 : 0 ≤ Cst := cc.Cst_nonneg
  set Cy := Cst + (cc.Kd * (P.c.Cop (P.n + 2) + 1) + P.c.Cg P.n * Cst) with hCy
  have hCy0 : 0 ≤ Cy := by
    have := cc.Kd_nonneg; have := P.c.Cop_nonneg (P.n + 2); have := P.c.Cg_nonneg P.n
    positivity
  set Δ0 := |D₁.invβ - D₂.invβ| + δ with hΔ0
  have hΔ00 : 0 ≤ Δ0 := by positivity
  set Δ := |D₁.invβ - D₂.invβ| + |q₁ - q₂| + |A₁ - A₂| + δ with hΔ
  have hΔ0' : 0 ≤ Δ := by positivity
  have hΔ0Δ : Δ0 ≤ Δ := by
    have := abs_nonneg (q₁ - q₂); have := abs_nonneg (A₁ - A₂); rw [hΔ0, hΔ]; linarith
  set c₁ : ℝ := (1 + P.T) * Kc with hc₁def
  set δy : ℝ := Cy * Δ0 with hδy
  set c₂ : ℝ := (1 + P.T) * δy with hc₂def
  set c₃ : ℝ := Kc * |A₁ - A₂| + Cst * Δ0 with hc₃def
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hδy0 : 0 ≤ δy := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  -- the supremum variables
  set fD : Ω' → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) P.T, ‖G₁ t ω - G₂ t ω‖ₑ with hfD
  set fM : Ω' → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) P.T, ‖G₁ t ω‖ₑ with hfM
  have hfDm : Measurable fD :=
    measurable_biSup_Icc hT.le (fun t ω => G₁ t ω - G₂ t ω) (fun t => (hGm₁ t).sub (hGm₂ t))
      (fun ω => ((hc₁ ω).sub (hc₂ ω)).continuousOn)
  have hfMm : Measurable fM :=
    measurable_biSup_Icc hT.le G₁ hGm₁ (fun ω => (hc₁ ω).continuousOn)
  have hηm : Measurable fun ω => ‖η₀ ω‖ₑ := hη₀.enorm
  -- pathwise domination
  have hCyCst : Cst ≤ Cy := by
    have := cc.Kd_nonneg; have := P.c.Cop_nonneg (P.n + 2); have := P.c.Cg_nonneg P.n
    rw [hCy]; have : 0 ≤ cc.Kd * (P.c.Cop (P.n + 2) + 1) + P.c.Cg P.n * Cst := by positivity
    linarith
  have hCyKd : cc.Kd * (P.c.Cop (P.n + 2) + 1) + P.c.Cg P.n * Cst ≤ Cy := by
    rw [hCy]; linarith
  have hy : ∀ t ∈ Set.Icc 0 P.T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖(P.pd D₂ μ₂).y t φ σ - (P.pd D₁ μ₁).y t φ σ‖ ≤ δy * sobolevNorm ((P.n : ℝ) + 4) φ := by
    intro t ht σ hσ φ hφ
    rw [norm_sub_rev]
    refine (Data.cmp_y cc h₁ h₂ hM hV hδ ht hφ hσ).trans ?_
    have hS' := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
    have : Cst * Δ0 ≤ δy := by rw [hδy]; exact mul_le_mul_of_nonneg_right hCyCst hΔ00
    exact mul_le_mul_of_nonneg_right this hS'
  have hy' : ∀ t ∈ Set.Icc 0 P.T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖(P.pd D₂ μ₂).y' t φ σ - (P.pd D₁ μ₁).y' t φ σ‖ ≤ δy * sobolevNorm ((P.n : ℝ) + 4) φ := by
    intro t ht σ hσ φ hφ
    rw [norm_sub_rev]
    refine (Data.cmp_y' cc h₁ h₂ hM hV hδ ht hφ hσ).trans ?_
    have hS' := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
    have : (cc.Kd * (P.c.Cop (P.n + 2) + 1) + P.c.Cg P.n * cc.Cst) * Δ0 ≤ δy := by
      rw [hδy]; exact mul_le_mul_of_nonneg_right hCyKd hΔ00
    exact mul_le_mul_of_nonneg_right this hS'
  have hw : ∀ t ∈ Set.Icc 0 P.T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖A₂ • (P.pd D₂ μ₂).w t φ - A₁ • (P.pd D₁ μ₁).w t φ‖ ≤ c₃ * sobolevNorm ((P.n : ℝ) + 4) φ := by
    intro t ht φ hφ
    have hS' := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
    have e : A₂ • (P.pd D₂ μ₂).w t φ - A₁ • (P.pd D₁ μ₁).w t φ =
        (A₂ - A₁) • (P.pd D₂ μ₂).w t φ + A₁ • ((P.pd D₂ μ₂).w t φ - (P.pd D₁ μ₁).w t φ) := by
      rw [sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have b1 := h₂.spec_pd.bd_w t ht φ hφ
    have b2 : ‖(P.pd D₂ μ₂).w t φ - (P.pd D₁ μ₁).w t φ‖ ≤ Cst * Δ0 * sobolevNorm ((P.n : ℝ) + 4) φ := by
      rw [norm_sub_rev]; exact Data.cmp_w cc h₁ h₂ hM hV hδ ht hφ
    have hAA : |A₂ - A₁| = |A₁ - A₂| := abs_sub_comm _ _
    calc |A₂ - A₁| * ‖(P.pd D₂ μ₂).w t φ‖ + |A₁| * ‖(P.pd D₂ μ₂).w t φ - (P.pd D₁ μ₁).w t φ‖
        ≤ |A₁ - A₂| * (Kc * sobolevNorm ((P.n : ℝ) + 4) φ) +
          1 * (Cst * Δ0 * sobolevNorm ((P.n : ℝ) + 4) φ) := by
          rw [hAA]
          exact add_le_add (mul_le_mul_of_nonneg_left b1 (abs_nonneg _))
            (mul_le_mul hA₁ b2 (norm_nonneg _) zero_le_one)
      _ = c₃ * sobolevNorm ((P.n : ℝ) + 4) φ := by rw [hc₃def]; ring
  have hdom : ∀ p : Ω' × Ω, ‖toPath ((P.n : ℝ) + 4) P.T Yh₁ p - toPath ((P.n : ℝ) + 4) P.T Yh₂ p‖ₑ ≤
      ENNReal.ofReal c₁ * fD p.1 + ENNReal.ofReal c₂ * fM p.1 + ENNReal.ofReal c₃ * ‖η₀ p.2‖ₑ := by
    intro p
    have hfin : fD p.1 ≠ ⊤ := sup_enorm_ne_top (F := fun t => G₁ t p.1 - G₂ t p.1)
      ((hc₁ p.1).sub (hc₂ p.1)).continuousOn
    have hfinM : fM p.1 ≠ ⊤ := sup_enorm_ne_top (F := fun t => G₁ t p.1) (hc₁ p.1).continuousOn
    have hsupD : (⨆ s ∈ Set.Icc (0 : ℝ) P.T, ‖(fun σ => Gh₂ σ p) s - (fun σ => Gh₁ σ p) s‖ₑ) = fD p.1 :=
      iSup_congr fun s => iSup_congr fun hs => enorm_sub_rev _ _
    have key := fun (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) P.T) =>
      yelt_dom (P₁ := P.pd D₂ μ₂) (P₂ := P.pd D₁ μ₁) h₂.spec_pd h₁.spec_pd
      (G₁ := fun σ => Gh₂ σ p) (G₂ := fun σ => Gh₁ σ p) (hGhc₂ p).continuousOn (hGhc₁ p).continuousOn hy hy'
      A₂ A₁ (ηh p) hw hδy0 hc₃0 ht
    set Bp : ℝ := c₁ * (fD p.1).toReal + c₂ * (fM p.1).toReal + c₃ * ‖η₀ p.2‖ with hBp
    have hBp0 : 0 ≤ Bp := by positivity
    have hb : ∀ t ∈ Set.Icc 0 P.T, ‖Yh₁ t p - Yh₂ t p‖ ≤ Bp := by
      intro t ht
      have e₂ : Yh₂ t p = (P.pd D₂ μ₂).Yelt A₂ (ηh p) (fun σ => Gh₂ σ p) t := by
        show (P.pd D₂ μ₂).Ypath P.T A₂ (ηh p) (fun σ => Gh₂ σ p) t = _
        unfold PathData.Ypath; rw [clamp01_of_mem ht]
      have e₁ : Yh₁ t p = (P.pd D₁ μ₁).Yelt A₁ (ηh p) (fun σ => Gh₁ σ p) t := by
        show (P.pd D₁ μ₁).Ypath P.T A₁ (ηh p) (fun σ => Gh₁ σ p) t = _
        unfold PathData.Ypath; rw [clamp01_of_mem ht]
      rw [e₁, e₂, norm_sub_rev]
      refine (key t ht).trans (le_of_eq ?_)
      rw [hsupD, hBp, hc₁def, hc₂def]
    have h1 := norm_toPath_sub_le Yh₁ Yh₂ (hYhc₁ p) (hYhc₂ p) hBp0 hb
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [hBp, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hc₁0,
      ENNReal.ofReal_mul hc₂0, ENNReal.ofReal_mul hc₃0, ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_toReal hfinM, ofReal_norm]
  have hX := aemeasurable_toPath hT.le P₃ Yh₁ hYhm₁ (Filter.Eventually.of_forall hYhc₁)
  have hY := aemeasurable_toPath hT.le P₃ Yh₂ hYhm₂ (Filter.Eventually.of_forall hYhc₂)
  have hW := wasserstein_two_le_of_dom P₃ (toPath ((P.n : ℝ) + 4) P.T Yh₁) (toPath ((P.n : ℝ) + 4) P.T Yh₂)
    hX hY (fun p => fD p.1) (fun p => fM p.1) (fun p => ‖η₀ p.2‖ₑ) (hfDm.comp measurable_fst)
    (hfMm.comp measurable_fst) (hηm.comp measurable_snd) c₁ c₂ c₃ hdom
  refine hW.trans ?_
  -- the moments
  have mD : ∫⁻ p, (fD p.1) ^ (2 : ℝ) ∂P₃ = ∫⁻ ω, fD ω ^ (2 : ℝ) ∂P' :=
    lintegral_prod_fst P' PΩ (hfDm.pow_const _)
  have mM : ∫⁻ p, (fM p.1) ^ (2 : ℝ) ∂P₃ = ∫⁻ ω, fM ω ^ (2 : ℝ) ∂P' :=
    lintegral_prod_fst P' PΩ (hfMm.pow_const _)
  have mH : ∫⁻ p, (‖η₀ p.2‖ₑ) ^ (2 : ℝ) ∂P₃ = ∫⁻ ω, (‖η₀ ω‖ₑ) ^ (2 : ℝ) ∂PΩ :=
    lintegral_prod_snd P' PΩ (hηm.pow_const _)
  have hLH : (∫⁻ ω, (‖η₀ ω‖ₑ) ^ (2 : ℝ) ∂PΩ) ^ (1 / (2 : ℝ)) = eLpNorm η₀ 2 PΩ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hη₀.aestronglyMeasurable]
    simp
  set vD : ℝ := Bd * (4 * d * S * (q₁ * δ + |q₁ - q₂|) * P.T) with hvD
  set vM : ℝ := Bd * (4 * q₁ * d * S * P.T) with hvM
  have hvD0 : 0 ≤ vD := by
    have := abs_nonneg (q₁ - q₂)
    rw [hvD]; positivity
  have hvM0 : 0 ≤ vM := by rw [hvM]; positivity
  have hLD := sqrt_moment_le hvD0 hbdD
  have hLM := sqrt_moment_le hvM0 hbdM
  have hsq1 : Real.sqrt vD ≤ Γ * Real.sqrt Δ := by
    have e : vD = (Bd * (4 * d * S * P.T)) * (q₁ * δ + |q₁ - q₂|) := by rw [hvD]; ring
    rw [e, Real.sqrt_mul (by positivity), hΓ, hTabs]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    have := abs_nonneg (A₁ - A₂)
    have := abs_nonneg (D₁.invβ - D₂.invβ)
    have hq : q₁ * δ ≤ δ := mul_le_of_le_one_left hδ0 hq₁1
    rw [hΔ]; linarith
  have hsq2 : Real.sqrt vM ≤ Γ := by
    rw [hΓ, hTabs]
    refine Real.sqrt_le_sqrt ?_
    rw [hvM]
    have h4 : 0 ≤ 4 * (d : ℝ) * S * P.T := by positivity
    have : 4 * q₁ * d * S * P.T ≤ 4 * d * S * P.T := by
      calc 4 * q₁ * d * S * P.T = q₁ * (4 * d * S * P.T) := by ring
        _ ≤ 1 * (4 * d * S * P.T) := mul_le_mul_of_nonneg_right hq₁1 h4
        _ = _ := one_mul _
    exact mul_le_mul_of_nonneg_left this hBd0
  have hCdef : P.Ccore cc = (1 + P.T) * Kc * Γ + (1 + P.T) * Cy * Γ + Kc + Cst + 1 := by
    unfold PdeSetup.Ccore; rw [hΓ, hCy, hTabs]
  have hT1 : 0 ≤ 1 + P.T := by linarith
  have hC1 : (1 + P.T) * Kc * Γ ≤ P.Ccore cc := by
    rw [hCdef]; have : 0 ≤ (1 + P.T) * Cy * Γ := by positivity
    linarith
  have hC2 : (1 + P.T) * Cy * Γ ≤ P.Ccore cc := by
    rw [hCdef]; have : 0 ≤ (1 + P.T) * Kc * Γ := by positivity
    linarith
  have hC3 : Kc + Cst ≤ P.Ccore cc := by
    rw [hCdef]; have h1 : 0 ≤ (1 + P.T) * Kc * Γ := by positivity
    have h2 : 0 ≤ (1 + P.T) * Cy * Γ := by positivity
    linarith
  have hC0 : 0 ≤ P.Ccore cc := (P.Ccore_pos cc).le
  rw [mD, mM, mH, hLH]
  have step1 : ENNReal.ofReal c₁ * (∫⁻ ω, fD ω ^ (2 : ℝ) ∂P') ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (c₁ * (Γ * Real.sqrt Δ)) := by
    rw [ENNReal.ofReal_mul hc₁0]
    exact mul_le_mul' le_rfl (hLD.trans (ENNReal.ofReal_le_ofReal hsq1))
  have step2 : ENNReal.ofReal c₂ * (∫⁻ ω, fM ω ^ (2 : ℝ) ∂P') ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (c₂ * Γ) := by
    rw [ENNReal.ofReal_mul hc₂0]
    exact mul_le_mul' le_rfl (hLM.trans (ENNReal.ofReal_le_ofReal hsq2))
  refine (add_le_add (add_le_add step1 step2) le_rfl).trans ?_
  refine final_bound (eLpNorm η₀ 2 PΩ) hC0 (by positivity) (by positivity) hc₃0 hΔ0' ?_ ?_ ?_
  · calc c₁ * (Γ * Real.sqrt Δ) = ((1 + P.T) * Kc * Γ) * Real.sqrt Δ := by rw [hc₁def]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (Real.sqrt_nonneg _)
  · calc c₂ * Γ = ((1 + P.T) * Cy * Γ) * Δ0 := by rw [hc₂def, hδy]; ring
      _ ≤ ((1 + P.T) * Cy * Γ) * Δ := mul_le_mul_of_nonneg_left hΔ0Δ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 hΔ0'
  · calc c₃ = Kc * |A₁ - A₂| + Cst * Δ0 := rfl
      _ ≤ Kc * Δ + Cst * Δ := by
          have : |A₁ - A₂| ≤ Δ := by
            have := abs_nonneg (D₁.invβ - D₂.invβ); have := abs_nonneg (q₁ - q₂); rw [hΔ]; linarith
          exact add_le_add (mul_le_mul_of_nonneg_left this hKc0) (mul_le_mul_of_nonneg_left hΔ0Δ hCst0)
      _ = (Kc + Cst) * Δ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC3 hΔ0'

end PdeSetup

end HRS.Uniform.Q54c

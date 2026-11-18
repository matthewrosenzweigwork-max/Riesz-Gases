import HRS.MC.CepH2Core2

/-!
# CEPH2, C6 (c): entropy dissipation for weak solutions with Lipschitz gradient
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The measurable majorant of the Fisher information: `liminf` of the mollified dissipations. -/
def h2_Dlim (θ : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) (r : ℝ) : ℝ≥0∞ :=
  liminf (fun k : ℕ => h2_Dinf θ (2 * θ * (1 / ((k : ℝ) + 1))) U μ r) atTop

/-- **C6 (core), with a measurable majorant of the Fisher information.** -/
theorem cepH2_core' {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) {θ : ℝ} (hθ : 0 < θ)
    {μ : ℝ → Measure (Ch N)} [∀ t, IsProbabilityMeasure (μ t)] (hcell : ∀ t, 0 ≤ t → μ t (cep_cell N)ᶜ = 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : Ch N → ℝ, Continuous g → (∀ z, g (z + cep_diag N) = g z) → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : H2WeakFP θ U μ) (hfin : cep_cylEntropy θ U (μ 0) < ⊤) :
    AEMeasurable (h2_Dlim θ U μ) (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ r ∈ Icc (0 : ℝ) T, cep_cylFisher θ U (μ r) ≤ h2_Dlim θ U μ r) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        cep_cylEntropy θ U (μ t) + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, h2_Dlim θ U μ r : ℝ≥0∞) : EReal)
          ≤ cep_cylEntropy θ U (μ 0) := by
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by simp only [hεdef]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvpos : ∀ k, 0 < 2 * θ * ε k := fun k => by have := hε k; positivity
  set D : ℝ → ℝ≥0∞ := h2_Dlim θ U μ with hD
  have full := fun k => cepH2_mollified_full hU hUper hK hθ hcell hT hmom hnar hfp (hvpos k)
  obtain ⟨M, hMtop, hM⟩ := hmom
  refine ⟨AEMeasurable.liminf (fun k => (full k).1), fun r hr => ?_, fun t ht => ?_⟩
  · exact cepH2_fisher_lsc hU hUper hθ hε hε0 (μ := μ r)
  · obtain ⟨H0, hH0⟩ := h2_cylEntropy_real hfin
    obtain ⟨e, he, hbound⟩ := cepH2_initial_bound hU hUper hK hconf hθ (μ := μ 0) hfin
    have he' : Tendsto (fun k => e (ε k)) atTop (𝓝 0) :=
      he.comp (tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall hε⟩)
    have hmomt : ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂(μ t) < ⊤ := lt_of_le_of_lt (hM t ht) hMtop
    have hl1' := cepH2_entropy_lsc hU hUper hK hconf hθ (μ := μ t) (hcell t ht.1) hmomt hε hε0
    simp only [h2_mol_eq] at hl1'
    have hδ : ∀ δ : ℝ, 0 < δ → δ < 1 →
        cep_cylEntropy θ U (μ t) +
          ((ENNReal.ofReal (θ * (1 - δ)) * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal) ≤ (H0 : EReal) := by
      intro δ hδ0 hδ1
      set J : ℕ → ℝ≥0∞ := fun k => ∫⁻ r in Icc (0 : ℝ) t, h2_Dinf θ (2 * θ * ε k) U μ r with hJdef
      have hJ : ∀ k, J k ≠ ⊤ := fun k => ((full k).2 δ hδ0 hδ1 t ht).1
      set a : ℕ → ℝ := fun k => h2_free θ U (h2_mu (2 * θ * ε k) (μ t)) with hadef
      set Y : ℕ → ℝ := fun k => θ * (1 - δ) * (J k).toReal with hYdef
      have hY0 : ∀ k, 0 ≤ Y k := fun k =>
        mul_nonneg (mul_nonneg hθ.le (by linarith)) ENNReal.toReal_nonneg
      set g : ℝ → ℝ := fun x => t * ((K : ℝ) ^ 2 * (N * (2 * θ * x)) / (4 * θ * δ)) with hg
      set E : ℕ → ℝ := fun k => e (ε k) + g (ε k) with hEdef
      have hE : Tendsto E atTop (𝓝 0) := by
        have hgc : Continuous g := by simp only [hg]; fun_prop
        have h1 : Tendsto (fun k => g (ε k)) atTop (𝓝 (g 0)) := (hgc.tendsto 0).comp hε0
        have h0 : g 0 = 0 := by simp [hg]
        rw [h0] at h1
        simpa using he'.add h1
      have hineq : ∀ k, a k + Y k ≤ H0 + E k := by
        intro k
        have h1 := ((full k).2 δ hδ0 hδ1 t ht).2
        have h2 := hbound (ε k) (hε k)
        rw [hH0, h2_mol_eq, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
        have h3 : (K : ℝ) ^ 2 * (N * (2 * θ * ε k)) / (4 * θ * δ) = (K : ℝ) ^ 2 * (N * (2 * θ * ε k)) / (4 * θ * δ) := rfl
        simp only [hadef, hYdef, hEdef, hg, hJdef]
        linarith
      have hlim := h2_liminf_add_le hE hineq
      -- Fatou
      set c : ℝ≥0∞ := ENNReal.ofReal (θ * (1 - δ)) with hc
      have hcne : c ≠ ⊤ := ENNReal.ofReal_ne_top
      have hFat : ∫⁻ r in Icc (0 : ℝ) t, D r ≤ liminf J atTop := by
        refine lintegral_liminf_le' (fun k => ?_)
        exact (full k).1.mono_set (Icc_subset_Icc le_rfl ht.2)
      have hcJ : ∀ k, c * J k = ENNReal.ofReal (Y k) := fun k => by
        rw [hc, hYdef]
        simp only
        rw [ENNReal.ofReal_mul (mul_nonneg hθ.le (by linarith)), ENNReal.ofReal_toReal (hJ k)]
      have hmono : c * ∫⁻ r in Icc (0 : ℝ) t, D r ≤ liminf (fun k => ENNReal.ofReal (Y k)) atTop := by
        calc c * ∫⁻ r in Icc (0 : ℝ) t, D r ≤ c * liminf J atTop := mul_le_mul' le_rfl hFat
          _ = liminf (fun k => c * J k) atTop := (ENNReal.liminf_const_mul_of_ne_top hcne).symm
          _ = liminf (fun k => ENNReal.ofReal (Y k)) atTop := by simp_rw [hcJ]
      have hmap := Monotone.map_liminf_of_continuousAt (F := atTop) EReal.coe_ennreal_strictMono.monotone
        (fun k => ENNReal.ofReal (Y k)) continuous_coe_ennreal_ereal.continuousAt
      have hl2 : ((c * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal) ≤ liminf (fun k => (Y k : EReal)) atTop := by
        calc ((c * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal)
            ≤ ((liminf (fun k => ENNReal.ofReal (Y k)) atTop : ℝ≥0∞) : EReal) :=
              EReal.coe_ennreal_le_coe_ennreal_iff.2 hmono
          _ = liminf ((fun x : ℝ≥0∞ => (x : EReal)) ∘ fun k => ENNReal.ofReal (Y k)) atTop := hmap
          _ = liminf (fun k => (Y k : EReal)) atTop := by
              congr 1
              funext k
              simp only [Function.comp, EReal.coe_ennreal_ofReal, max_eq_left (hY0 k)]
      calc cep_cylEntropy θ U (μ t) + ((c * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal)
          ≤ liminf (fun k => (a k : EReal)) atTop + liminf (fun k => (Y k : EReal)) atTop :=
            add_le_add hl1' hl2
        _ ≤ (H0 : EReal) := hlim
    rw [hH0]
    exact h2_delta_limit hθ (h2_cylEntropy_ne_bot _) hδ

end HRS.MC.CepH2

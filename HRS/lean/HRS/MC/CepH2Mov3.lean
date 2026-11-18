import HRS.MC.CepH2Mov2

/-!
# CEPH2, G2 (c): passage to the limit in the frozen-potential entropy inequalities
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- **G2**: the dissipation inequality passes to the limit of the frozen potentials. -/
theorem cepH2_freeze_limit {U : Ch N → ℝ} (hU : ContDiff ℝ 2 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {Un : ℕ → Ch N → ℝ} {c C : ℝ} (hc : 0 < c) (hUnc : ∀ n, Continuous (Un n))
    (hlow : ∀ n z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Un n z)
    (hUnle : ∀ n z, Un n z ≤ U z)
    (hUnU : ∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z)
    {θ : ℝ} (hθ : 0 < θ)
    {μ : ℝ → Measure (Ch N)} {μn : ℕ → ℝ → Measure (Ch N)} [∀ t, IsProbabilityMeasure (μ t)]
    [∀ n t, IsProbabilityMeasure (μn n t)]
    (hcell : ∀ t, 0 ≤ t → μ t (cep_cell N)ᶜ = 0) (h0 : ∀ n, μn n 0 = μ 0)
    (hfin : cep_cylEntropy θ U (μ 0) < ⊤)
    (htv : ∀ t, 0 ≤ t → ∀ ψ : Ch N → ℝ, Continuous ψ → (∀ z, ψ (z + cep_diag N) = ψ z) →
      (∃ C, ∀ z, |ψ z| ≤ C) → Tendsto (fun n => ∫ z, ψ z ∂(μn n t)) atTop (𝓝 (∫ z, ψ z ∂(μ t))))
    (hdiss : ∀ n, ∃ D : ℝ → ℝ≥0∞, (∀ T : ℝ, AEMeasurable D (volume.restrict (Icc (0 : ℝ) T))) ∧
      (∀ r : ℝ, 0 ≤ r → cep_cylFisher θ (Un n) (μn n r) ≤ D r) ∧
      ∀ t : ℝ, 0 ≤ t → cep_cylEntropy θ (Un n) (μn n t)
          + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal)
          ≤ cep_cylEntropy θ (Un n) (μn n 0)) :
    ∀ t : ℝ, 0 ≤ t → cep_cylEntropy θ U (μ t)
      + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) : ℝ≥0∞) : EReal)
      ≤ cep_cylEntropy θ U (μ 0) := by
  choose D hDm hDF hDE using hdiss
  have hUc : Continuous U := hU.continuous
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  intro t ht
  have hini : ∀ n, cep_cylEntropy θ (Un n) (μn n 0) ≤ cep_cylEntropy θ U (μ 0) := fun n => by
    rw [h0 n]
    exact h2_entropy_mono hU1 hconf hθ (hUnc n) (hUnle n) ⟨c, C, hc, hlow n⟩ hfin
  -- entropy
  have hent : cep_cylEntropy θ U (μ t) ≤ liminf (fun n => cep_cylEntropy θ (Un n) (μn n t)) atTop :=
    h2_entropy_lsc_moving hUc hUnc hθ hc hlow hUnU hconf (hcell t ht) (htv t ht)
  -- Fisher
  have hfis : ∀ r ∈ Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) ≤ liminf (fun n => D n r) atTop := by
    intro r hr
    exact (h2_fisher_lsc_moving hU1 hUper hUnU (htv r hr.1)).trans
      (liminf_le_liminf (Eventually.of_forall fun n => hDF n r hr.1))
  have hFat : ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) ≤ liminf (fun n => ∫⁻ r in Icc (0 : ℝ) t, D n r) atTop := by
    calc ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) ≤ ∫⁻ r in Icc (0 : ℝ) t, liminf (fun n => D n r) atTop :=
          lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hfis)
      _ ≤ _ := lintegral_liminf_le' (fun n => hDm n t)
  set J : ℕ → ℝ≥0∞ := fun n => ∫⁻ r in Icc (0 : ℝ) t, D n r with hJ
  set c' : ℝ≥0∞ := ENNReal.ofReal θ with hc'
  have hcne : c' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmono : c' * ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) ≤ liminf (fun n => c' * J n) atTop := by
    calc c' * ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) ≤ c' * liminf J atTop := mul_le_mul' le_rfl hFat
      _ = liminf (fun k => c' * J k) atTop := (ENNReal.liminf_const_mul_of_ne_top hcne).symm
  have hmap := Monotone.map_liminf_of_continuousAt (F := atTop) EReal.coe_ennreal_strictMono.monotone
    (fun k => c' * J k) continuous_coe_ennreal_ereal.continuousAt
  have hl2 : ((c' * ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) : ℝ≥0∞) : EReal)
      ≤ liminf (fun k => ((c' * J k : ℝ≥0∞) : EReal)) atTop := by
    calc ((c' * ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) : ℝ≥0∞) : EReal)
        ≤ ((liminf (fun k => c' * J k) atTop : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hmono
      _ = liminf ((fun x : ℝ≥0∞ => (x : EReal)) ∘ fun k => c' * J k) atTop := hmap
  calc cep_cylEntropy θ U (μ t) + ((c' * ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher θ U (μ r) : ℝ≥0∞) : EReal)
      ≤ liminf (fun n => cep_cylEntropy θ (Un n) (μn n t)) atTop + liminf (fun k => ((c' * J k : ℝ≥0∞) : EReal)) atTop :=
        add_le_add hent hl2
    _ ≤ liminf (fun n => cep_cylEntropy θ (Un n) (μn n t) + ((c' * J n : ℝ≥0∞) : EReal)) atTop :=
        EReal.le_liminf_add
    _ ≤ liminf (fun _ : ℕ => cep_cylEntropy θ U (μ 0)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => (hDE n t ht).trans (hini n))
    _ = cep_cylEntropy θ U (μ 0) := liminf_const _

end HRS.MC.CepH2

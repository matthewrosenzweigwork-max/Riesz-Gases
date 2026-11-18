import HRS.MC.S7FCBBnd

/-!
# FC-B, part 12: pointwise bound of `fcbT`, density comparison of the product measures
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

local instance fcb_borel_prod2c : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4c : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

theorem fcbT_pointwise_bound (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < d) :
    ∃ Cenv : ℝ, 0 < Cenv ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (M : ℝ), 0 ≤ M → ∀ f : Torus d × Torus d → ℝ,
      (∀ᵐ q ∂(volume.prod volume : Measure (Torus d × Torus d)), |f q| ≤ M * fcbPhi s ‖q.1 - q.2‖) →
      ∀ x y : Torus d, x ≠ y → |fcbT d n f (x, y)| ≤ M * (Cenv * fcbPhi s ‖x - y‖) := by
  obtain ⟨Cenv, hC, hE⟩ := fcb_envelope hd hs0 hs
  refine ⟨Cenv, hC, fun n hn M hM f hf x y hxy => ?_⟩
  have hΦ : ∀ t : ℝ, 0 ≤ t → 0 ≤ fcbPhi s t := fun t ht => fcb_Phi_nonneg hs0 ht
  have h1 := fcbT_enorm_le hd hn f (x, y)
  have h2 : ∫⁻ q, ENNReal.ofReal (fcbKap d n ((x, y) - q)) * ‖f q‖ₑ ∂(volume.prod volume) ≤
      ∫⁻ q : Torus d × Torus d, ENNReal.ofReal M * (ENNReal.ofReal (fcbK d n (x - q.1)) *
        ENNReal.ofReal (fcbK d n (y - q.2)) * ENNReal.ofReal (fcbPhi s ‖q.1 - q.2‖)) ∂(volume.prod volume) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hf] with q hq
    have hfq : ‖f q‖ₑ ≤ ENNReal.ofReal M * ENNReal.ofReal (fcbPhi s ‖q.1 - q.2‖) := by
      rw [← ENNReal.ofReal_mul hM, ← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal hq
    have hk : ENNReal.ofReal (fcbKap d n ((x, y) - q)) =
        ENNReal.ofReal (fcbK d n (x - q.1)) * ENNReal.ofReal (fcbK d n (y - q.2)) := by
      simp only [fcbKap, Prod.fst_sub, Prod.snd_sub]
      exact ENNReal.ofReal_mul (fcbK_nonneg hd hn _)
    rw [hk]
    calc _ ≤ ENNReal.ofReal (fcbK d n (x - q.1)) * ENNReal.ofReal (fcbK d n (y - q.2)) *
          (ENNReal.ofReal M * ENNReal.ofReal (fcbPhi s ‖q.1 - q.2‖)) := by gcongr
      _ = _ := by ring
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  have h3 := hE n hn x y hxy
  have h4 : ‖fcbT d n f (x, y)‖ₑ ≤ ENNReal.ofReal (M * (Cenv * fcbPhi s ‖x - y‖)) := by
    refine h1.trans (h2.trans ?_)
    rw [ENNReal.ofReal_mul hM]
    exact mul_le_mul' le_rfl h3
  rw [← ofReal_norm, Real.norm_eq_abs] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM (mul_nonneg hC.le (hΦ _ (norm_nonneg _))))).1 h4

theorem fcb_tendsto_transfer {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hle : μ ≤ K • ν) {p : ℝ≥0∞} (hp : p ≠ ⊤) (u : ℕ → α → ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) ν)
    (hu : Tendsto (fun n => eLpNorm (u n) p ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) p μ) atTop (𝓝 0) := by
  have h1 : ∀ n, eLpNorm (u n) p μ ≤ K ^ (1 / p).toReal * eLpNorm (u n) p ν := fun n => by
    have := eLpNorm_mono_measure (p := p) (u n) hle
    rwa [eLpNorm_smul_measure_of_ne_top hp _ _ (hum n), smul_eq_mul] at this
  have h2 : Tendsto (fun n => K ^ (1 / p).toReal * eLpNorm (u n) p ν) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := K ^ (1 / p).toReal) hu
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hK))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => bot_le) h1

theorem fcb_withDensity_prod_le {ρ : Torus d → ℝ} (hρ : Continuous ρ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ (withDensityReal ρ).prod (withDensityReal ρ) ≤ K • (volume.prod volume : Measure (Torus d × Torus d)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  have hle : withDensityReal ρ ≤ ENNReal.ofReal C • (volume : Measure (Torus d)) := by
    rw [← withDensity_const]
    refine withDensity_mono (Eventually.of_forall fun x => ?_)
    have := hC x (mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans this)
  refine ⟨ENNReal.ofReal C * ENNReal.ofReal C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  calc (withDensityReal ρ).prod (withDensityReal ρ)
      ≤ (ENNReal.ofReal C • (volume : Measure (Torus d))).prod (ENNReal.ofReal C • (volume : Measure (Torus d))) :=
        Measure.prod_mono hle hle
    _ = (ENNReal.ofReal C * ENNReal.ofReal C) • (volume.prod volume : Measure (Torus d × Torus d)) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

end HRS.MC.Sec7.FCB

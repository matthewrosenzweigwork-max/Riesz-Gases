import HRS.PDE.TorusFPSpec
import HRS.PDE.TorusFPExistAux17
import HRS.PDE.TorusFPExistAux18
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# D1 comparison, helper 3: comparison of finite measures on `𝕋^n` from smooth test functions

If `∫ ψ dμ ≤ ∫ ψ dν` for all smooth `ψ ≥ 0`, then `μ ≤ ν` (as measures).  Route: smooth approximation
of continuous nonnegative functions (`d1_exists_smooth_approx`) gives the inequality for all continuous
nonnegative functions; thickened indicators of closed sets give `μ F ≤ ν F` for closed `F`; closed inner
regularity gives all measurable sets.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d1c_continuous_of_isSmooth {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) : Continuous ψ :=
  Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) from hψ).continuous

theorem d1c_integrable_of_cont (ρ : Measure (Torus n)) [IsFiniteMeasure ρ] {g : Torus n → ℝ}
    (hg : Continuous g) : Integrable g ρ :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Continuous nonnegative test functions: the smooth inequality extends by approximation. -/
theorem d1c_integral_le_of_cont {μ ν : Measure (Torus n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x ∂μ ≤ ∫ x, ψ x ∂ν)
    {g : Torus n → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set K : ℝ := ν.real Set.univ with hKdef
  have hK0 : 0 ≤ K := measureReal_nonneg
  set δ : ℝ := ε / (2 * (K + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨ψ, hψs, hψ⟩ := d1_exists_smooth_approx hg hδpos
  have hψc : Continuous ψ := d1c_continuous_of_isSmooth hψs
  have hgψ : ∀ x, g x ≤ ψ x + δ := fun x => by
    have := (abs_le.1 (hψ x)).2
    linarith
  have hψg : ∀ x, ψ x + δ ≤ g x + 2 * δ := fun x => by
    have := (abs_le.1 (hψ x)).1
    linarith
  have hpos : ∀ x, 0 ≤ ψ x + δ := fun x => (hg0 x).trans (hgψ x)
  have hsm : Torus.IsSmooth (fun x => ψ x + δ) := by
    have := d1_isSmooth_comb 1 δ hψs (d1_isSmooth_const 1)
    simpa using this
  have h1 := h (fun x => ψ x + δ) hsm hpos
  have i1 : ∫ x, g x ∂μ ≤ ∫ x, (ψ x + δ) ∂μ :=
    integral_mono (d1c_integrable_of_cont μ hg) (d1c_integrable_of_cont μ (hψc.add continuous_const))
      (fun x => hgψ x)
  have i2 : ∫ x, (ψ x + δ) ∂ν ≤ ∫ x, (g x + 2 * δ) ∂ν :=
    integral_mono (d1c_integrable_of_cont ν (hψc.add continuous_const))
      (d1c_integrable_of_cont ν (hg.add continuous_const)) (fun x => hψg x)
  have i3 : ∫ x, (g x + 2 * δ) ∂ν = ∫ x, g x ∂ν + K * (2 * δ) := by
    rw [integral_add (d1c_integrable_of_cont ν hg) (integrable_const _), integral_const]
    simp [hKdef, smul_eq_mul]
  have hKδ : K * (2 * δ) ≤ ε := by
    have hK1 : K / (K + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc K * (2 * δ) = ε * (K / (K + 1)) := by
          rw [hδdef]
          field_simp
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hK1 hε.le
      _ = ε := mul_one ε
  linarith

/-- Closed sets: `μ F ≤ ν F` from the continuous inequality, via thickened indicators. -/
theorem d1c_measure_closed_le {μ ν : Measure (Torus n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : Torus n → ℝ, Continuous g → (∀ x, 0 ≤ g x) → ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν)
    {F : Set (Torus n)} (hF : IsClosed F) : μ F ≤ ν F := by
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hT := fun (ρ : Measure (Torus n)) [IsFiniteMeasure ρ] =>
    tendsto_lintegral_thickenedIndicator_of_isClosed ρ hF hδ hlim
  refine le_of_tendsto_of_tendsto' (hT μ) (hT ν) fun k => ?_
  set g : Torus n → ℝ := fun x => ((thickenedIndicator (hδ k) F x : ℝ≥0) : ℝ) with hgdef
  have hgc : Continuous g := NNReal.continuous_coe.comp (thickenedIndicator (hδ k) F).continuous
  have hg0 : ∀ x, 0 ≤ g x := fun x => NNReal.coe_nonneg _
  have key : ∀ ρ : Measure (Torus n), [IsFiniteMeasure ρ] →
      ∫⁻ ω, ((thickenedIndicator (hδ k) F ω : ℝ≥0) : ℝ≥0∞) ∂ρ = ENNReal.ofReal (∫ x, g x ∂ρ) := by
    intro ρ _
    rw [ofReal_integral_eq_lintegral_ofReal (d1c_integrable_of_cont ρ hgc)
      (ae_of_all _ hg0)]
    refine lintegral_congr fun ω => ?_
    simp [hgdef, ENNReal.ofReal_coe_nnreal]
  rw [key μ, key ν]
  exact ENNReal.ofReal_le_ofReal (h g hgc hg0)

/-- **Comparison of finite measures from smooth test functions.** -/
theorem d1c_le_of_smooth {μ ν : Measure (Torus n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x ∂μ ≤ ∫ x, ψ x ∂ν) : μ ≤ ν := by
  have hc : ∀ g : Torus n → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν := fun g hg hg0 => d1c_integral_le_of_cont h hg hg0
  refine Measure.le_iff.2 fun A hA => ?_
  rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ A)]
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  exact (d1c_measure_closed_le hc hK).trans (measure_mono hKA)

end HRS

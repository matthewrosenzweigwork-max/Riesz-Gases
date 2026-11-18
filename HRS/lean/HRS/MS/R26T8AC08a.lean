import Mathlib

/-!
# S8.2 observed-time layer, packet T8A.C08a: radial lintegrals of powers on annuli in `Euc d`

`∫⁻_{ε<‖z‖≤δ} ‖z‖^{-p} dz = d·vol(B₁)·∫_ε^δ r^{d-1-p} dr`, for `ε > 0` (any `p`) or `ε = 0` and `p < d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A

abbrev EucC8 (d : ℕ) := EuclideanSpace ℝ (Fin d)

def r26t8a_c08a_const (d : ℕ) : ℝ := d * (volume : Measure (EucC8 d)).real (Metric.ball 0 1)

theorem r26t8a_c08a_const_nonneg (d : ℕ) : 0 ≤ r26t8a_c08a_const d :=
  mul_nonneg (Nat.cast_nonneg d) measureReal_nonneg

theorem r26t8a_c08a_radial (d : ℕ) (hd : 1 ≤ d) {p : ℝ} {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hp : 0 < ε ∨ p < d) :
    ∫⁻ z : EucC8 d, ENNReal.ofReal ((Set.Ioc ε δ).indicator (fun r => r ^ (-p)) ‖z‖) =
      ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - p)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfin : Module.finrank ℝ (EucC8 d) = d := finrank_euclideanSpace_fin
  set F : ℝ → ℝ := (Set.Ioc ε δ).indicator (fun r => r ^ (-p)) with hF
  have h1 : ∀ r : ℝ, r ^ (d - 1) * F r = (Set.Ioc ε δ).indicator (fun r => r ^ ((d : ℝ) - 1 - p)) r := by
    intro r
    by_cases hr : r ∈ Set.Ioc ε δ
    · have hr0 : 0 < r := hε.trans_lt hr.1
      rw [hF, indicator_of_mem hr, indicator_of_mem hr, ← Real.rpow_natCast, ← Real.rpow_add hr0]
      congr 1
      have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
      rw [this]; ring
    · simp [hF, indicator_of_notMem hr]
  have hint : IntervalIntegrable (fun r : ℝ => r ^ ((d : ℝ) - 1 - p)) volume ε δ := by
    rcases hp with hp | hp
    · exact intervalIntegral.intervalIntegrable_rpow (Or.inr (by
        rw [Set.uIcc_of_le hεδ]; intro h; exact absurd h.1 (not_le.2 hp)))
    · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hIoc : IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - 1 - p)) (Set.Ioc ε δ) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hεδ).1 hint
  have hIoi : IntegrableOn (fun y : ℝ => y ^ (d - 1) • F y) (Ioi 0) := by
    have : (fun y : ℝ => y ^ (d - 1) • F y) =
        (Set.Ioc ε δ).indicator (fun r => r ^ ((d : ℝ) - 1 - p)) := by
      funext y; rw [smul_eq_mul, h1]
    rw [this]
    exact ((integrable_indicator_iff measurableSet_Ioc).2 hIoc).integrableOn
  have hint2 : Integrable (fun z : EucC8 d => F ‖z‖) volume := by
    have := (integrable_fun_norm_addHaar (volume : Measure (EucC8 d)) (f := F)).2
    rw [hfin] at this
    exact this hIoi
  have hnn : 0 ≤ᵐ[volume] fun z : EucC8 d => F ‖z‖ := Eventually.of_forall fun z => by
    simp only [hF, Pi.zero_apply]
    exact indicator_nonneg (fun r hr => Real.rpow_nonneg (hε.trans hr.1.le) _) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 hnn]
  congr 1
  have := integral_fun_norm_addHaar (volume : Measure (EucC8 d)) F
  rw [hfin] at this
  rw [this]
  simp only [smul_eq_mul, nsmul_eq_mul, r26t8a_c08a_const]
  have e2 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * F y = ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - p) := by
    have : (fun y : ℝ => y ^ (d - 1) * F y) =
        (Set.Ioc ε δ).indicator (fun r => r ^ ((d : ℝ) - 1 - p)) := funext h1
    rw [this, setIntegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hεδ]
    have e : Ioi (0 : ℝ) ∩ Set.Ioc ε δ = Set.Ioc ε δ := by
      ext r; exact ⟨fun h => h.2, fun h => ⟨hε.trans_lt h.1, h⟩⟩
    rw [e]
  rw [e2]
  ring

end HRS.MS.R26T8A

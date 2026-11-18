import HRS.MS.R26T8AR10
import HRS.MS.S82RA1

/-!
# S8.2 observed-time layer, packet T8A.C01a: generic one-site partition bounds and the product split
* `r26t8a_c01_Zlow`: Jensen lower bound `exp (-1 - 1/1000) ≤ ∫ exp (f - S)` for `-1 ≤ f ≤ 1 + 1/1000`, `S ≥ 0`, `∫ S ≤ 1/1000`.
* `r26t8a_c01_qint`, `r26t8a_c01_qmass`: integrability and mass bound of `q (. - x)` against the thermal law (needs `0 < a`).
* `r26t8a_c01_split`: split of an integral over `Measure.pi` at one coordinate (`insertNth`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_c01_Zlow {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f S : α → ℝ) (hfm : Measurable f) (hSm : Measurable S) (hS0 : ∀ y, 0 ≤ S y)
    (hSi : Integrable S μ) (hf1 : ∀ y, f y ≤ 1 + 1 / 1000) (hf2 : ∀ y, -1 ≤ f y)
    (hm : ∫ y, S y ∂μ ≤ 1 / 1000) :
    Integrable (fun y => Real.exp (f y - S y)) μ ∧
      Real.exp (-1 - 1 / 1000) ≤ ∫ y, Real.exp (f y - S y) ∂μ ∧
      ∫⁻ y, ENNReal.ofReal (Real.exp (f y - S y)) ∂μ =
        ENNReal.ofReal (∫ y, Real.exp (f y - S y) ∂μ) := by
  obtain ⟨hi, -, hl⟩ := r26t8a_r09_tilt_bdd μ (fun y => f y - S y) (hfm.sub hSm) (1 + 1 / 1000)
    fun y => by have := hS0 y; have := hf1 y; linarith
  obtain ⟨hui, -, -⟩ := r26t8a_r09_tilt_bdd μ (fun y => -S y) hSm.neg 0 fun y => by
    have := hS0 y; linarith
  have hjen : Real.exp (∫ y, -S y ∂μ) ≤ ∫ y, Real.exp (-S y) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hSi.neg hui
  have hmu : -(1 / 1000 : ℝ) ≤ ∫ y, -S y ∂μ := by rw [integral_neg]; linarith
  refine ⟨hi, ?_, hl⟩
  have hlow : ∀ y, Real.exp (-1) * Real.exp (-S y) ≤ Real.exp (f y - S y) := fun y => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by have := hf2 y; linarith)
  calc Real.exp (-1 - 1 / 1000) = Real.exp (-1) * Real.exp (-(1 / 1000)) := by
        rw [← Real.exp_add]; congr 1
    _ ≤ Real.exp (-1) * ∫ y, Real.exp (-S y) ∂μ :=
        mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 hmu).trans hjen) (Real.exp_pos _).le
    _ = ∫ y, Real.exp (-1) * Real.exp (-S y) ∂μ := (integral_const_mul _ _).symm
    _ ≤ _ := integral_mono (hui.const_mul _) hi hlow

theorem r26t8a_c01_qint {d : ℕ} (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {rho q : Euc d → ℝ} (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho)
    (hq : ShortRangePole d q) (x : Euc d) :
    Integrable (fun z => q (z - x)) (HRS.Whole.withDensityReal rho) := by
  obtain ⟨-, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hG : HRS.Whole.HasR2GaussianUpper (C + 1) c rho := ⟨hc, fun x => by
    have h1 := (le_abs_self (rho x)).trans (hb x).1
    nlinarith [Real.exp_pos (-c * ‖x‖ ^ 2)]⟩
  exact HRS.MS.S82P2.s82p2_q_integrable hd hq (C + 1) c (by linarith) hc rho hrho.2.1 hG x

theorem r26t8a_c01_qmass {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta) (x : Euc d) :
    ∫ z, q (z - x) ∂HRS.Whole.withDensityReal rho ≤ 1 / (1000 * beta) :=
  HRS.MS.S82P2.s82p2_q_mass hW hbeta x

theorem r26t8a_c01_split {d m : ℕ} (μ : Measure (Euc d)) [SigmaFinite μ] (i : Fin (m + 1))
    (Ψ : HRS.Whole.EucConfig d (m + 1) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X, Ψ X ∂(Measure.pi fun _ : Fin (m + 1) => μ) =
      ∫⁻ X', ∫⁻ y, Ψ (i.insertNth y X') ∂μ ∂(Measure.pi fun _ : Fin m => μ) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
  have hemb := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurableEmbedding
  have key := hmp.symm.lintegral_comp_emb hemb Ψ
  rw [← key]
  have hes := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm.measurable
  rw [lintegral_prod_symm (fun a => Ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Euc d) i).symm a))
    (hΨ.comp hes).aemeasurable]
  rfl

end HRS.MS.R26T8A

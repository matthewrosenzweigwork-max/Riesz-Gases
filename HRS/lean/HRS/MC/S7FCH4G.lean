import HRS.MC.S7FCH4F

/-!
# S7FCH4G: moment bookkeeping (H4, part G)

`L^{2q}` moments of the coupled laws: finiteness of the `2q`-th moment of the limit window `procWin` from a coupling,
integrability of `‖·‖²` from an `L^{2q}` bound, and the transfer of `L^p` norms through laws.
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
open Classical
variable {d : ℕ} {r T : ℝ}

theorem S7FCH4_sq_le_one_add_rpow {x q : ℝ} (hx : 0 ≤ x) (hq : 1 ≤ q) : x ^ 2 ≤ 1 + x ^ (2 * q) := by
  have h0 : 0 ≤ x ^ (2 * q) := Real.rpow_nonneg hx _
  by_cases h1 : x ≤ 1
  · have : x ^ 2 ≤ 1 := pow_le_one₀ hx h1
    linarith
  · push_neg at h1
    have : x ^ (2 : ℝ) ≤ x ^ (2 * q) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    rw [Real.rpow_two] at this
    linarith

theorem S7FCH4_sq_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {q : ℝ} (hq : 1 ≤ q) {F : Ω → PathSpace d r T} (hF : AEMeasurable F P)
    (hL : S7FCH4_Lp (2 * q) P (fun ω => ENNReal.ofReal ‖F ω‖) ≠ ⊤) :
    Integrable (fun ω => ‖F ω‖ ^ 2) P := by
  have hp : 0 < 2 * q := by linarith
  have h1 : ∫⁻ ω, ENNReal.ofReal ‖F ω‖ ^ (2 * q) ∂P ≠ ⊤ := by
    intro h
    apply hL
    unfold S7FCH4_Lp
    rw [h]
    exact ENNReal.top_rpow_of_pos (by positivity)
  have hI : Integrable (fun ω => ‖F ω‖ ^ (2 * q)) P := by
    refine ⟨(hF.norm.pow_const _).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ ω, ‖‖F ω‖ ^ (2 * q)‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal ‖F ω‖ ^ (2 * q) ∂P :=
          lintegral_congr fun ω => by
            rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) _), ofReal_norm_rpow hp.le]
      _ < ⊤ := lt_top_iff_ne_top.2 h1
  refine ((integrable_const (1 : ℝ)).add hI).mono' (hF.norm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact S7FCH4_sq_le_one_add_rpow (norm_nonneg _) hq

theorem S7FCH4_Lp_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Ω → PathSpace d r T}
    (hF : AEMeasurable F P) (p : ℝ) {f : PathSpace d r T → ℝ≥0∞} (hf : Measurable f) :
    S7FCH4_Lp p (P.map F) f = S7FCH4_Lp p P (fun ω => f (F ω)) := by
  unfold S7FCH4_Lp
  rw [lintegral_map' (hf.pow_const p).aemeasurable hF]

theorem S7FCH4_nu_moment {q : ℝ} (hq : 1 ≤ q) (μ ν : Measure (PathSpace d r T))
    (hW : wassersteinE (2 * q) μ ν < 1) {c : ℝ≥0∞}
    (hc : S7FCH4_Lp (2 * q) μ (fun u => ENNReal.ofReal ‖u‖) ≤ c) :
    S7FCH4_Lp (2 * q) ν (fun v => ENNReal.ofReal ‖v‖) ≤ c + 2 := by
  have hq2 : 1 ≤ 2 * q := by linarith
  obtain ⟨π, hπ, hlt⟩ := S7FCH4_exists_coupling (by linarith : 0 < 2 * q) μ ν one_ne_zero (ne_top_of_lt hW)
  have hlt2 : S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) ≤ 2 := by
    refine hlt.le.trans ?_
    calc wassersteinE (2 * q) μ ν + 1 ≤ 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have h1 := S7FCH4_Lp_marg1 hπ (2 * q) (f := fun u => ENNReal.ofReal ‖u‖)
    (ENNReal.measurable_ofReal.comp measurable_norm)
  have h2 := S7FCH4_Lp_marg2 hπ (2 * q) (f := fun u => ENNReal.ofReal ‖u‖)
    (ENNReal.measurable_ofReal.comp measurable_norm)
  rw [← h2]
  refine (S7FCH4_snd_le hq2 π).trans ?_
  rw [h1]
  gcongr

theorem S7FCH4_zeta_Lp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {q : ℝ} (hq : 1 ≤ q) {F : Ω → PathSpace d r T} (hF : AEMeasurable F P)
    {C : ℝ} (hint : Integrable (fun ω => ‖F ω‖ ^ (2 * q)) P) (hC : ∫ ω, ‖F ω‖ ^ (2 * q) ∂P ≤ C) :
    S7FCH4_Lp (2 * q) P (fun ω => ENNReal.ofReal ‖F ω‖) ≤ ENNReal.ofReal C ^ (1 / (2 * q)) := by
  have hp : 0 < 2 * q := by linarith
  unfold S7FCH4_Lp
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  calc ∫⁻ ω, ENNReal.ofReal ‖F ω‖ ^ (2 * q) ∂P = ∫⁻ ω, ENNReal.ofReal (‖F ω‖ ^ (2 * q)) ∂P :=
        lintegral_congr fun ω => (ofReal_norm_rpow hp.le).symm
    _ = ENNReal.ofReal (∫ ω, ‖F ω‖ ^ (2 * q) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => Real.rpow_nonneg (norm_nonneg _) _)).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

end HRS.MC.Sec7.S7FCH4

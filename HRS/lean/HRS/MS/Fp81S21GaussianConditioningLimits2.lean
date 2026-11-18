import HRS.MS.Fp81S21GaussianConditioningLimits

/-! Finite-to-L¹ conditioning for the actual drift increment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Condition an integrable drift increment obtained as the L¹ limit of finite
past-measurable directions. The constant is supplied explicitly; the actual
path need only agree almost everywhere with the past-plus-future decomposition. -/
theorem fp81s21_conditioned_drift_limit
    {d : ℕ} {m H : ℝ} {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (past : Ω → A)
    (Y X Z : Ω → OscPath d m H) (hY : Measurable Y)
    (hYpast : Measurable[MeasurableSpace.comap past inferInstance] Y)
    (hX : Measurable X) (hind : IndepFun past X P)
    (hZ : Z =ᵐ[P] fun ω => Y ω + X ω)
    (γ : ℝ → Measure (OscPath d m H)) (r : ℝ)
    [IsProbabilityMeasure (γ r)] (hlaw : P.map X = γ r)
    (Φ : OscPath d m H → ℝ) (hΦ : MemCb 5 Φ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ K)
    (hheat : ∀ ω, ‖fderiv ℝ (r2HeatFn γ Φ r) (Y ω)‖ ≤ K)
    (D : Ω → OscPath d m H) (hD : Integrable D P)
    (k : ℕ → ℕ) (h : (n : ℕ) → Fin (k n) → OscPath d m H)
    (c : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (hc : ∀ n i, Integrable (c n i) P)
    (hcpast : ∀ n i,
      AEStronglyMeasurable[MeasurableSpace.comap past inferInstance] (c n i) P)
    (hlim : Tendsto (fun n => ∫ ω, ‖(∑ i, c n i ω • h n i) - D ω‖ ∂P)
      atTop (𝓝 0)) :
    Integrable (fun ω => fderiv ℝ Φ (Z ω) (D ω)) P ∧
    Integrable (fun ω => fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (D ω)) P ∧
    (∫ ω, fderiv ℝ Φ (Z ω) (D ω) ∂P) =
      ∫ ω, fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (D ω) ∂P := by
  classical
  let Dn : ℕ → Ω → OscPath d m H := fun n ω => ∑ i, c n i ω • h n i
  have hDn (n : ℕ) : Integrable (Dn n) P :=
    integrable_finset_sum _ (fun i _ => (hc n i).smul_const (h n i))
  have hfin (n : ℕ) := fp81s21_heat_derivative_finite_random_drift
    P past Y X hY hYpast hX hind γ r hlaw Φ hΦ (k n) (h n) (c n)
    (hc n) (hcpast n)
  have hcont : Continuous (fun z : OscPath d m H × OscPath d m H =>
      fderiv ℝ Φ z.1 z.2) :=
    ((hΦ.1.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply continuous_snd
  have hcontHeat : Continuous (fun z : OscPath d m H × OscPath d m H =>
      fderiv ℝ (r2HeatFn γ Φ r) z.1 z.2) :=
    (((s102_r2HeatFn_derivs γ r hΦ).1.continuous_fderiv (by norm_num)).comp
      continuous_fst).clm_apply continuous_snd
  have hu := fp81s21_integral_pairing_tendsto_of_l1 P
    (fun ω => fderiv ℝ Φ (Y ω + X ω)) K hK (fun ω => hbound _)
    D Dn hD hDn
    (hcont.comp_aestronglyMeasurable
      ((hY.add hX).aestronglyMeasurable.prodMk hD.aestronglyMeasurable))
    (fun n => (hfin n).1.aestronglyMeasurable) hlim
  have hv := fp81s21_integral_pairing_tendsto_of_l1 P
    (fun ω => fderiv ℝ (r2HeatFn γ Φ r) (Y ω)) K hK hheat
    D Dn hD hDn
    (hcontHeat.comp_aestronglyMeasurable
      (hY.aestronglyMeasurable.prodMk hD.aestronglyMeasurable))
    (fun n => (hfin n).2.1.aestronglyMeasurable) hlim
  have hseq : (fun n => ∫ ω, fderiv ℝ Φ (Y ω + X ω) (Dn n ω) ∂P) =
      (fun n => ∫ ω, fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (Dn n ω) ∂P) :=
    funext fun n => (hfin n).2.2
  have heq : (∫ ω, fderiv ℝ Φ (Y ω + X ω) (D ω) ∂P) =
      ∫ ω, fderiv ℝ (r2HeatFn γ Φ r) (Y ω) (D ω) ∂P :=
    tendsto_nhds_unique hu.2.2 (by rw [hseq]; exact hv.2.2)
  have hz : (fun ω => fderiv ℝ Φ (Z ω) (D ω)) =ᵐ[P]
      fun ω => fderiv ℝ Φ (Y ω + X ω) (D ω) := by
    filter_upwards [hZ] with ω hω
    rw [hω]
  exact ⟨hu.1.congr hz.symm, hv.1, (integral_congr_ae hz).trans heq⟩

#print axioms fp81s21_conditioned_drift_limit
end HRS.Fp81.S21
end

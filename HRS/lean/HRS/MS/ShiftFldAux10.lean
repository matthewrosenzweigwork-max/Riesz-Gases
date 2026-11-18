import HRS.MS.ShiftFldAux9

/-!
# S79P: Gaussian domination and the weighted integration by parts used for the nonlocal term
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.S21 HRS.MH.DualityRd HRS.MS.UniqT3
open HRS (Euc)

variable {d : ℕ}

/-- Domination: `a` Gaussian-bounded, `f` of linear growth. -/
theorem s79g_gdom {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {a f : Euc d → ℝ}
    (ha : AEStronglyMeasurable a volume) (hf : AEStronglyMeasurable f volume)
    (haC : ∀ y, |a y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {K : ℝ} (hK : ∀ x, |f x| ≤ K * (1 + ‖x‖)) :
    Integrable (fun x => a x * f x) := by
  have hK0 : 0 ≤ K := by
    have := hK 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨Cp, hCp0, hCp⟩ := S45.s45_poly_le (c := c / 4) (by positivity)
  have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := 3 * c / 4) (by positivity)
  refine Integrable.mono' (hg.const_mul (C * K * Cp)) (ha.mul hf)
    (Filter.Eventually.of_forall fun x => ?_)
  have hn := norm_nonneg x
  rw [Real.norm_eq_abs, abs_mul]
  have h2 : |f x| ≤ K * (Cp * Real.exp (c / 4 * ‖x‖ ^ 2)) :=
    (hK x).trans (mul_le_mul_of_nonneg_left (hCp ‖x‖ hn) hK0)
  have e : Real.exp (-c * ‖x‖ ^ 2) * Real.exp (c / 4 * ‖x‖ ^ 2) = Real.exp (-(3 * c / 4 * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |a x| * |f x| ≤ (C * Real.exp (-c * ‖x‖ ^ 2)) * (K * (Cp * Real.exp (c / 4 * ‖x‖ ^ 2))) :=
        mul_le_mul (haC x) h2 (abs_nonneg _) (by positivity)
    _ = (C * K * Cp) * (Real.exp (-c * ‖x‖ ^ 2) * Real.exp (c / 4 * ‖x‖ ^ 2)) := by ring
    _ = _ := by rw [e]

/-- `|D1 j ρ| ≤ C exp(-c‖y‖²)` from the thermal data. -/
theorem s79g_D1_rho {s a β C c BU : ℝ} (hT : S45.ThermalData d s a β C c BU) (j : Fin d) (y : Euc d) :
    |D1 j (thermalDensity d s a β) y| ≤ C * Real.exp (-c * ‖y‖ ^ 2) :=
  (HRS.MS.UniqN2b.n2b_D1_le j _ y).trans (hT.h1 y)

/-- Weighted integration by parts `∫ F ∂_v(ρ G) = - ∫ ∂_v F ρ G` for the thermal density `ρ`, when the three
products `F G`, `F ∂_vG`, `∂_vF G` have linear growth. -/
theorem s79g_ibp {s a β C c BU : ℝ} (hT : S45.ThermalData d s a β C c BU) {F G : Euc d → ℝ}
    {v : Euc d} (hFd : Differentiable ℝ F) (hGd : Differentiable ℝ G)
    (hFc : Continuous F) (hGc : Continuous G)
    (hF'c : Continuous fun y => fderiv ℝ F y v) (hG'c : Continuous fun y => fderiv ℝ G y v)
    {K : ℝ} (h1 : ∀ y, |F y * G y| ≤ K * (1 + ‖y‖))
    (h2 : ∀ y, |F y * fderiv ℝ G y v| ≤ K * (1 + ‖y‖))
    (h3 : ∀ y, |fderiv ℝ F y v * G y| ≤ K * (1 + ‖y‖))
    (hv : ∀ y, |fderiv ℝ (thermalDensity d s a β) y v| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) :
    Integrable (fun y => F y * fderiv ℝ (fun z => thermalDensity d s a β z * G z) y v) ∧
    ∫ y, F y * fderiv ℝ (fun z => thermalDensity d s a β z * G z) y v =
      -∫ y, fderiv ℝ F y v * (thermalDensity d s a β y * G y) := by
  have hρd : Differentiable ℝ (thermalDensity d s a β) :=
    (hT.smooth.differentiable (by simp))
  have hρc : Continuous (thermalDensity d s a β) := hT.smooth.continuous
  have hρ0 : ∀ y, |thermalDensity d s a β y| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := hT.h0
  have hprod : ∀ y, fderiv ℝ (fun z => thermalDensity d s a β z * G z) y v =
      fderiv ℝ (thermalDensity d s a β) y v * G y + thermalDensity d s a β y * fderiv ℝ G y v := by
    intro y
    have hh : HasFDerivAt (fun z => thermalDensity d s a β z * G z)
        (thermalDensity d s a β y • fderiv ℝ G y + G y • fderiv ℝ (thermalDensity d s a β) y) y :=
      (hρd y).hasFDerivAt.mul (hGd y).hasFDerivAt
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hρ'c : Continuous fun y => fderiv ℝ (thermalDensity d s a β) y v :=
    (hT.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have iA : Integrable (fun y => thermalDensity d s a β y * (F y * G y)) :=
    s79g_gdom hT.hc hT.C0 hρc.aestronglyMeasurable (hFc.mul hGc).aestronglyMeasurable hρ0 h1
  have iB : Integrable (fun y => thermalDensity d s a β y * (fderiv ℝ F y v * G y)) :=
    s79g_gdom hT.hc hT.C0 hρc.aestronglyMeasurable (hF'c.mul hGc).aestronglyMeasurable hρ0 h3
  have iC1 : Integrable (fun y => fderiv ℝ (thermalDensity d s a β) y v * (F y * G y)) :=
    s79g_gdom hT.hc hT.C0 hρ'c.aestronglyMeasurable (hFc.mul hGc).aestronglyMeasurable hv h1
  have iC2 : Integrable (fun y => thermalDensity d s a β y * (F y * fderiv ℝ G y v)) :=
    s79g_gdom hT.hc hT.C0 hρc.aestronglyMeasurable (hFc.mul hG'c).aestronglyMeasurable hρ0 h2
  have iD : Integrable (fun y => F y * fderiv ℝ (fun z => thermalDensity d s a β z * G z) y v) :=
    (iC1.add iC2).congr (Filter.Eventually.of_forall fun y => by simp only [hprod, Pi.add_apply]; ring)
  refine ⟨iD, ?_⟩
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F)
    (g := fun z => thermalDensity d s a β z * G z) (v := v)
    (iB.congr (Filter.Eventually.of_forall fun y => by simp only; ring))
    iD
    (iA.congr (Filter.Eventually.of_forall fun y => by simp only; ring))
    (fun x _ => hFd x) (fun x _ => (hρd x).mul (hGd x))
  exact this

end HRS.MS.S79G

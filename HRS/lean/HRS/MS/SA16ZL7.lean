import HRS.MS.SA16ZL6

/-!
# S.A.16 (SA16Z) L7: `‖pvOdd_i f‖_p ≤ C (‖f‖_p + ‖∇f‖_p)`, `1 < θ < 2`, `f ∈ C_c^∞`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section L7
variable {d : ℕ}

/-- `f ∈ C_c^∞` as a Schwartz function -/
def sa16z_schw {f : Euc d → ℝ} (hf : IsCcInfty f) : 𝓢(Euc d, ℝ) := hf.2.toSchwartzMap hf.1

lemma sa16z_schw_coe {f : Euc d → ℝ} (hf : IsCcInfty f) : ⇑(sa16z_schw hf) = f := rfl

open HRS.CZ.Pv in
theorem sa16z_pv_W1p (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {p : ℝ} (hp : 1 < p) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, IsCcInfty f →
      eLpNorm (pvOdd d θ (fun u : Euc d => u i) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * (eLpNorm f (ENNReal.ofReal p) volume +
          eLpNorm (fun x => ‖fderiv ℝ f x‖) (ENNReal.ofReal p) volume) := by
  have hθ0 : 0 < θ := by linarith
  have hp0 : 0 < p := by linarith
  set A := ∫⁻ z, sa16z_kap d θ i z with hA
  set B := ∫⁻ z, sa16z_kfar d θ i z with hB
  have hAfin : A ≠ ⊤ := sa16z_kappa_fin hd hθ0 hθ2 i
  have hBfin : B ≠ ⊤ := sa16z_kf_fin hd hθ1 i
  refine ⟨A.toReal + B.toReal, by positivity, fun f hf => ?_⟩
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (pvOdd d θ (fun u : Euc d => u i) f) volume :=
    pvOdd_aesm hd hθ0 hθ2 (isPvKernel_coord i) (sa16z_schw hf)
  have hfm : AEStronglyMeasurable f volume := hf.1.continuous.aestronglyMeasurable
  have hdfm : AEStronglyMeasurable (fun x => ‖fderiv ℝ f x‖) volume :=
    (hf.1.continuous_fderiv (by simp)).norm.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hmeas,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hfm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 hnetop hdfm, ENNReal.toReal_ofReal hp0.le]
  set U : Euc d → ℝ≥0∞ := fun x => ∫⁻ z, sa16z_kap d θ i z * sa16z_D f x z with hU
  set V : Euc d → ℝ≥0∞ := fun x => ∫⁻ z, sa16z_kfar d θ i z * ‖f (x - z)‖ₑ with hV
  have hUm : Measurable U := by
    have : Measurable (fun q : Euc d × Euc d => sa16z_kap d θ i q.2 * sa16z_D f q.1 q.2) :=
      ((sa16z_kap_meas hd θ i).comp measurable_snd).mul (sa16z_D_meas hf)
    exact this.lintegral_prod_right'
  have hVm : Measurable V := by
    have : Measurable (fun q : Euc d × Euc d => sa16z_kfar d θ i q.2 * ‖f (q.1 - q.2)‖ₑ) :=
      ((sa16z_kfar_meas θ i).comp measurable_snd).mul
        (hf.1.continuous.measurable.comp (measurable_fst.sub measurable_snd)).enorm
    exact this.lintegral_prod_right'
  have h1 : ∫⁻ x, ‖pvOdd d θ (fun u : Euc d => u i) f x‖ₑ ^ p ≤ ∫⁻ x, (U + V) x ^ p :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (sa16z_pv_pointwise hd hθ1 hθ2 hf i x) hp0.le
  have h2 := ENNReal.lintegral_Lp_add_le (μ := (volume : Measure (Euc d))) hUm.aemeasurable hVm.aemeasurable hp.le
  have hUb : ∫⁻ x, U x ^ p ≤ A ^ p * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p :=
    sa16z_near_Lp hf (sa16z_kap_meas hd θ i) hAfin hp
  have hVb : ∫⁻ x, V x ^ p ≤ B ^ p * ∫⁻ x, ‖f x‖ₑ ^ p :=
    HRS.Commutator.Whole.XLI.young_lintegral (sa16z_kfar_meas θ i) hf.1.continuous.measurable.enorm hp.le
  have hq : 0 ≤ 1 / p := by positivity
  have e1 : (∫⁻ x, ‖pvOdd d θ (fun u : Euc d => u i) f x‖ₑ ^ p) ^ (1 / p) ≤
      (∫⁻ x, U x ^ p) ^ (1 / p) + (∫⁻ x, V x ^ p) ^ (1 / p) :=
    (ENNReal.rpow_le_rpow h1 hq).trans h2
  have e2 : (∫⁻ x, U x ^ p) ^ (1 / p) ≤ A * (∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p) ^ (1 / p) := by
    refine (ENNReal.rpow_le_rpow hUb hq).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq, ← ENNReal.rpow_mul]
    congr 2; field_simp; simp
  have e3 : (∫⁻ x, V x ^ p) ^ (1 / p) ≤ B * (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) := by
    refine (ENNReal.rpow_le_rpow hVb hq).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq, ← ENNReal.rpow_mul]
    congr 2; field_simp; simp
  have hAle : A ≤ ENNReal.ofReal (A.toReal + B.toReal) := by
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := B)])
  have hBle : B ≤ ENNReal.ofReal (A.toReal + B.toReal) := by
    calc B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := A)])
  have hnf : ∀ x : Euc d, ‖(‖fderiv ℝ f x‖)‖ₑ = ‖fderiv ℝ f x‖ₑ := fun x => enorm_norm _
  simp only [hnf]
  calc (∫⁻ x, ‖pvOdd d θ (fun u : Euc d => u i) f x‖ₑ ^ p) ^ (1 / p)
      ≤ A * (∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p) ^ (1 / p) + B * (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) :=
        e1.trans (add_le_add e2 e3)
    _ ≤ ENNReal.ofReal (A.toReal + B.toReal) * (∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p) ^ (1 / p) +
          ENNReal.ofReal (A.toReal + B.toReal) * (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) := by gcongr
    _ = _ := by rw [← mul_add]; congr 1; exact add_comm _ _

end L7

end HRS.Whole.AppendixA.Phase2SA16R

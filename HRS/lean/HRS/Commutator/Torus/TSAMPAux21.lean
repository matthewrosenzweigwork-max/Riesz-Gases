import HRS.Commutator.Torus.TSAMPAux20

/-!
# T-SAMP helpers, part 21: integrals of radial functions of `tdist` over the torus
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_toEuc_add (n l : Lattice d) : Lattice.toEuc (n + l) = Lattice.toEuc n + Lattice.toEuc l := by
  ext i; simp [Lattice.toEuc]

lemma tsamp_tdist_mk_attained (y : Euc d) : ∃ l : Lattice d, KernelGrad.tdist (Torus.mk y) 0 = ‖y + Lattice.toEuc l‖ := by
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  set z : Torus d := Torus.mk y with hz
  let l₀ : Lattice d := fun i => if (Torus.rep z) i ≤ 1 / 2 then 0 else -1
  have hc : KernelGrad.centeredRep z = Torus.rep z + Lattice.toEuc l₀ := by
    ext i
    rw [KernelGrad.centeredRep_apply]
    show (if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1) =
      (Torus.rep z) i + (l₀ i : ℝ)
    by_cases h : (Torus.rep z) i ≤ 1 / 2
    · have h0 : l₀ i = 0 := if_pos h
      rw [if_pos h, h0]; simp
    · have h0 : l₀ i = -1 := if_neg h
      rw [if_neg h, h0]; push_cast; ring
  refine ⟨n + l₀, ?_⟩
  rw [KernelGrad.tdist_zero_right, hc, hn, tsamp_toEuc_add, add_assoc]

/-- Integrals of radial functions of `tdist` over the torus are dominated by those over `ℝ^d`. -/
lemma tsamp_tdist_lintegral_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z : Torus d, F (KernelGrad.tdist z 0) ≤ ∫⁻ x : Euc d, F ‖x‖ := by
  rw [tpos_torus_lintegral (fun z : Torus d => F (KernelGrad.tdist z 0)), tpos_lintegral_unfold]
  rw [← lintegral_tsum (fun l => ?_)]
  · refine lintegral_mono fun y => ?_
    obtain ⟨l, hl⟩ := tsamp_tdist_mk_attained y
    rw [hl]
    exact ENNReal.le_tsum (f := fun l : Lattice d => F ‖y + Lattice.toEuc l‖) l
  · exact (hF.comp (measurable_norm.comp (measurable_id.add_const _))).aemeasurable

lemma tsamp_lintegral_profile (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) {M : ℕ} (hM : d < M) :
    ∫⁻ z : Torus d, ENNReal.ofReal ((1 + KernelGrad.tdist z 0 / η) ^ (-(M : ℝ))) ≤
      ENNReal.ofReal (η ^ d * ∫ y : Euc d, (1 + ‖y‖) ^ (-(M : ℝ))) := by
  have hFm : Measurable fun t : ℝ => ENNReal.ofReal ((1 + t / η) ^ (-(M : ℝ))) := by fun_prop
  refine (tsamp_tdist_lintegral_le hFm).trans ?_
  have hint : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-(M : ℝ))) := by
    refine integrable_one_add_norm (μ := (volume : Measure (Euc d))) ?_
    rw [finrank_euclideanSpace_fin]; exact_mod_cast hM
  have e : ∀ x : Euc d, (1 + ‖x‖ / η) ^ (-(M : ℝ)) = (fun y : Euc d => (1 + ‖y‖) ^ (-(M : ℝ))) (η⁻¹ • x) := by
    intro x
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    rw [inv_mul_eq_div]
  have hint2 : Integrable (fun x : Euc d => (1 + ‖x‖ / η) ^ (-(M : ℝ))) := by
    simp_rw [e]; exact hint.comp_smul (inv_ne_zero hη.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun x => by positivity)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  simp_rw [e]
  rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (Euc d)))
    (fun y : Euc d => (1 + ‖y‖) ^ (-(M : ℝ))) hη.le, finrank_euclideanSpace_fin, smul_eq_mul]

lemma tsamp_ball_volume_le {R : ℝ} (hR : 0 ≤ R) :
    volume {z : Torus d | KernelGrad.tdist z 0 ≤ R} ≤
      ENNReal.ofReal (R ^ d) * volume (Metric.ball (0 : Euc d) 1) := by
  have h1 : volume {z : Torus d | KernelGrad.tdist z 0 ≤ R} =
      ∫⁻ z : Torus d, (Set.Iic R).indicator (fun _ => (1 : ℝ≥0∞)) (KernelGrad.tdist z 0) := by
    rw [← lintegral_indicator_one (tsamp_measurableSet_ball R)]
    refine lintegral_congr fun z => ?_
    by_cases h : KernelGrad.tdist z 0 ≤ R <;> simp [Set.indicator, h]
  rw [h1]
  refine (tsamp_tdist_lintegral_le (F := (Set.Iic R).indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator measurableSet_Iic)).trans ?_
  have h2 : ∫⁻ x : Euc d, (Set.Iic R).indicator (fun _ => (1 : ℝ≥0∞)) ‖x‖ = volume (Metric.closedBall (0 : Euc d) R) := by
    rw [← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_congr fun x => ?_
    by_cases h : ‖x‖ ≤ R <;> simp [Set.indicator, h]
  rw [h2, Measure.addHaar_closedBall _ _ hR, finrank_euclideanSpace_fin]

end HRS.Commutator.TorusNote

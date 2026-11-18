import HRS.PDE.D3PhiPAux8

/-!
# D3PHIP, helper 9: Fubini in `(r,x)` and the proof of `d3phi_identity_classical`

`Y(t) - Y(0) = ∫_x (A_t - A_0) dP = ∫_x ∫_0^t D dr dP = ∫_0^t ∫_x D dP dr`, and `∫_x D_r dP` is evaluated by
`d3pp_inner`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

section main

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ} {p : ℝ → ℝ}

theorem d3pp_D_integrable (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hpac : AbsolutelyContinuousOnInterval p 0 T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    Integrable (fun z : Torus n × ℝ => d3pp_D κ U ψ ψt w p (deriv p) z.2 z.1)
      ((d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc 0 t))) := by
  have := d3a_gibbs_isProb (κ := κ) hU
  have hT0 := hT.le
  have hpc : ContinuousOn p (Set.Icc 0 T) := by simpa [Set.uIcc_of_le hT0] using hpac.continuousOn
  have cA := d3pp_A_cont_sub hκ hU hw hψ hpc
  have cG1 : Continuous fun q : Set.Icc (0 : ℝ) T × Torus n =>
      d3pp_A κ U ψ w p q.1.1 q.2 * d3pp_ell κ U ψ w q.1.1 q.2 := cA.mul (d3pp_ell_cont_sub hκ hU hw hψ)
  have cG2 : Continuous fun q : Set.Icc (0 : ℝ) T × Torus n =>
      d3pp_A κ U ψ w p q.1.1 q.2 * (p q.1.1 * d3pp_ellr κ U ψ ψt w q.1.1 q.2 + d3pp_mr κ U ψ ψt q.1.1 q.2) :=
    cA.mul (((d3pp_p_cont_sub hpc).mul (d3pp_ellr_cont_sub hκ hU hT hw hψ)).add
      (d3pp_mr_cont_sub hκ hU hT hψ))
  obtain ⟨C1, hC1⟩ := d3a_bound (F := fun r x => d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x) cG1
  obtain ⟨C2, hC2⟩ := d3a_bound (F := fun r x => d3pp_A κ U ψ w p r x *
    (p r * d3pp_ellr κ U ψ ψt w r x + d3pp_mr κ U ψ ψt r x)) cG2
  have hle : volume.restrict (Set.Icc (0 : ℝ) t) ≤ volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right ht.2) le_rfl
  have hle2 : (d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc (0 : ℝ) t)) ≤
      (d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc (0 : ℝ) T)) := Measure.prod_mono le_rfl hle
  have m1 := (d3pp_aesm (G := fun r x => d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x) cG1 (d1_gibbsMeasure κ U)).mono_measure hle2
  have m2 := (d3pp_aesm (G := fun r x => d3pp_A κ U ψ w p r x *
    (p r * d3pp_ellr κ U ψ ψt w r x + d3pp_mr κ U ψ ψt r x)) cG2 (d1_gibbsMeasure κ U)).mono_measure hle2
  have m0 : AEStronglyMeasurable (fun z : Torus n × ℝ => deriv p z.2)
      ((d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    ((measurable_deriv p).comp measurable_snd).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun z : Torus n × ℝ => d3pp_D κ U ψ ψt w p (deriv p) z.2 z.1)
      ((d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
    refine (m0.mul m1 |>.add m2).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, Pi.mul_apply]
    unfold d3pp_D
    ring
  have hpint : Integrable (deriv p) (volume.restrict (Set.Icc (0 : ℝ) t)) := by
    have h1 := (intervalIntegrable_iff_integrableOn_Icc_of_le hT0).1 hpac.intervalIntegrable_deriv
    exact h1.mono_set (Set.Icc_subset_Icc_right ht.2)
  have hg : Integrable (fun z : Torus n × ℝ => C1 * ‖deriv p z.2‖ + C2)
      ((d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    ((hpint.norm.const_mul C1).comp_snd (d1_gibbsMeasure κ U)).add (integrable_const _)
  refine hg.mono' hDm ?_
  have e : (d1_gibbsMeasure κ U).prod (volume.restrict (Set.Icc (0 : ℝ) t)) =
      ((d1_gibbsMeasure κ U).prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) t) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
  have hr : z.2 ∈ Set.Icc (0 : ℝ) T := ⟨hz.2.1, hz.2.2.trans ht.2⟩
  have h1 := hC1 z.2 hr z.1
  have h2 := hC2 z.2 hr z.1
  have hD : d3pp_D κ U ψ ψt w p (deriv p) z.2 z.1 =
      deriv p z.2 * (d3pp_A κ U ψ w p z.2 z.1 * d3pp_ell κ U ψ w z.2 z.1) +
      d3pp_A κ U ψ w p z.2 z.1 * (p z.2 * d3pp_ellr κ U ψ ψt w z.2 z.1 + d3pp_mr κ U ψ ψt z.2 z.1) := by
    unfold d3pp_D; ring
  rw [hD]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (deriv p z.2))
  linarith

theorem d3pp_Y_diff (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hpac : AbsolutelyContinuousOnInterval p 0 T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    d3phi_Y κ U ψ w p t - d3phi_Y κ U ψ w p 0 =
      ∫ r in (0 : ℝ)..t, ∫ x, d3pp_D κ U ψ ψt w p (deriv p) r x ∂(d1_gibbsMeasure κ U) := by
  have := d3a_gibbs_isProb (κ := κ) hU
  have hT0 := hT.le
  have hpc : ContinuousOn p (Set.Icc 0 T) := by simpa [Set.uIcc_of_le hT0] using hpac.continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT0⟩
  have cA := d3pp_A_cont_sub hκ hU hw hψ hpc
  have hAt : Integrable (d3pp_A κ U ψ w p t) (d1_gibbsMeasure κ U) :=
    d3a_hint _ (d3a_contOn_space (F := fun r x => d3pp_A κ U ψ w p r x) cA ht)
  have hA0 : Integrable (d3pp_A κ U ψ w p 0) (d1_gibbsMeasure κ U) :=
    d3a_hint _ (d3a_contOn_space (F := fun r x => d3pp_A κ U ψ w p r x) cA h0)
  rw [d3pp_Y_eq hκ hU hψ ht p, d3pp_Y_eq hκ hU hψ h0 p, ← integral_sub hAt hA0]
  have h1 : ∫ x, (d3pp_A κ U ψ w p t x - d3pp_A κ U ψ w p 0 x) ∂(d1_gibbsMeasure κ U) =
      ∫ x, (∫ r in (0 : ℝ)..t, d3pp_D κ U ψ ψt w p (deriv p) r x) ∂(d1_gibbsMeasure κ U) :=
    integral_congr_ae (ae_of_all _ fun x => (d3pp_FTC_x hκ hU hT hw hψ hpac x ht).symm)
  rw [h1]
  simp_rw [intervalIntegral.integral_of_le ht.1]
  have hI := d3pp_D_integrable hκ hU hT hw hψ hpac ht
  have hI' : Integrable (fun z : Torus n × ℝ => d3pp_D κ U ψ ψt w p (deriv p) z.2 z.1)
      ((d1_gibbsMeasure κ U).prod (volume.restrict (Set.Ioc 0 t))) :=
    hI.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))
  exact integral_integral_swap (μ := d1_gibbsMeasure κ U) (ν := volume.restrict (Set.Ioc 0 t))
    (f := fun x r => d3pp_D κ U ψ ψt w p (deriv p) r x) hI'

end main

end HRS

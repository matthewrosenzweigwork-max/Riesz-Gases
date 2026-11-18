import HRS.MC.CepH2Aux29

/-!
# CEPH2, helper 30: the dissipation inequality without cut-off (`H2Set.result2`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.tendsto_intE (S : H2Set θ v U K μ T M) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ s in Icc (0 : ℝ) t, h2_Echi θ v U μ ((n : ℝ) + 1) s) atTop (𝓝 0) := by
  obtain ⟨CE, hCE0, hbd, htail⟩ := S.E_tail
  have hn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Icc (0 : ℝ) t))
    (F := fun (n : ℕ) (s : ℝ) => h2_Echi θ v U μ ((n : ℝ) + 1) s) (f := fun _ => 0) (fun _ => CE)
    (fun n => (S.int_E (hn n) t).aestronglyMeasurable) (integrableOn_const (by simp))
    (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]
      exact hbd s _ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
    (ae_of_all _ fun s => htail s)
  simpa using h

theorem H2Set.diss_eq (S : H2Set θ v U K μ T M) (s : ℝ) :
    h2_diss θ U (h2_mu v (μ s)) = (h2_Dinf θ v U μ s).toReal := by
  haveI := S.hprob s
  have hℓ := h2_contDiff_ell (θ := θ) S.hv S.hU1 (μ s)
  have hpt : ∀ x, h2_mu v (μ s) x * ‖(h2_mu v (μ s) x)⁻¹ • gradient (h2_mu v (μ s)) x +
      (1 / θ) • gradient U x‖ ^ 2 = h2_dens θ v U (μ s) x := by
    intro x
    have h1 : fderiv ℝ (h2_ell θ v U (μ s)) x = (h2_mu v (μ s) x)⁻¹ • fderiv ℝ (h2_mu v (μ s)) x +
        (1 / θ) • fderiv ℝ U x := by
      rw [h2_fderiv_ell S.hv S.hU1, (h2_hasFDerivAt_mu S.hv (μ s) x).fderiv]
    have h2 : (h2_mu v (μ s) x)⁻¹ • gradient (h2_mu v (μ s)) x + (1 / θ) • gradient U x =
        gradient (h2_ell θ v U (μ s)) x := by
      simp only [gradient, h1, map_add, map_smul]
    rw [h2, h2_norm_gradient]
    rfl
  unfold h2_diss h2_Dinf
  simp only [hpt]
  exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => h2_dens_nonneg S.hv θ U (μ s) x)
    ((h2_continuous_mu S.hv (μ s)).mul ((hℓ.continuous_fderiv (by simp)).norm.pow 2)).aestronglyMeasurable

theorem H2Set.result2' (S : H2Set θ v U K μ T M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∫⁻ s in Icc (0 : ℝ) t, h2_Dinf θ v U μ s ≠ ⊤ ∧
    h2_free θ U (h2_mu v (μ t)) + θ * (1 - δ) * ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu v (μ r)) ≤
      h2_free θ U (h2_mu v (μ 0)) + t * ((K : ℝ) ^ 2 * (N * v) / (4 * θ * δ)) := by
  have hθ := S.hθ
  set c0 : ℝ := (K : ℝ) ^ 2 * (N * v) / (4 * θ * δ) with hc0
  set κ : ℝ := θ * (1 - δ) with hκ
  have hκ0 : 0 < κ := mul_pos hθ (by linarith)
  have hn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  set X : ℕ → ℝ := fun n => ∫ s in Icc (0 : ℝ) t, h2_Dchi θ v U μ ((n : ℝ) + 1) s with hX
  set Y : ℕ → ℝ := fun n => h2_Fchi θ v U μ ((n : ℝ) + 1) 0 + t * c0 -
    (∫ s in Icc (0 : ℝ) t, h2_Echi θ v U μ ((n : ℝ) + 1) s) - h2_Fchi θ v U μ ((n : ℝ) + 1) t with hY
  have r1 : ∀ n : ℕ, Integrable (fun s => h2_Dchi θ v U μ ((n : ℝ) + 1) s) (volume.restrict (Icc (0 : ℝ) t)) ∧
      κ * X n ≤ Y n := fun n => by
    obtain ⟨h1, h2⟩ := S.result1 hδ hδ1 (hn n) ht
    refine ⟨h1, ?_⟩
    have e1 : κ * X n = θ * (1 - δ) * ∫ s in Icc (0 : ℝ) t, h2_Dchi θ v U μ ((n : ℝ) + 1) s := rfl
    rw [e1]
    show _ ≤ h2_Fchi θ v U μ ((n : ℝ) + 1) 0 + t * ((K : ℝ) ^ 2 * (N * v) / (4 * θ * δ)) -
      (∫ s in Icc (0 : ℝ) t, h2_Echi θ v U μ ((n : ℝ) + 1) s) - h2_Fchi θ v U μ ((n : ℝ) + 1) t
    linarith
  have hXnn : ∀ n, 0 ≤ X n := fun n => integral_nonneg fun s => S.Dchi_nonneg _ _
  have hYt : Tendsto Y atTop (𝓝 (h2_free θ U (h2_mu v (μ 0)) + t * c0 - 0 - h2_free θ U (h2_mu v (μ t)))) := by
    rw [hY]
    exact (((S.tendsto_Fchi 0).add_const (t * c0)).sub (S.tendsto_intE t)).sub (S.tendsto_Fchi t)
  set Yl : ℝ := h2_free θ U (h2_mu v (μ 0)) + t * c0 - 0 - h2_free θ U (h2_mu v (μ t)) with hYl
  have hY0 : 0 ≤ Yl :=
    ge_of_tendsto hYt (Eventually.of_forall fun n => (mul_nonneg hκ0.le (hXnn n)).trans (r1 n).2)
  -- Fatou
  have h1 : ∫⁻ s in Icc (0 : ℝ) t, h2_Dinf θ v U μ s ≤ ENNReal.ofReal (Yl / κ) := by
    refine (S.lintegral_Dinf_le t).trans ?_
    have hof : ∀ n : ℕ, ∫⁻ s in Icc (0 : ℝ) t, ENNReal.ofReal (h2_Dchi θ v U μ ((n : ℝ) + 1) s) =
        ENNReal.ofReal (X n) := fun n =>
      (ofReal_integral_eq_lintegral_ofReal (r1 n).1 (ae_of_all _ fun s => S.Dchi_nonneg _ _)).symm
    simp_rw [hof]
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Y n / κ)) atTop (𝓝 (ENNReal.ofReal (Yl / κ))) :=
      ENNReal.tendsto_ofReal ((hYt.div_const κ))
    rw [← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal ?_)
    rw [le_div_iff₀ hκ0, mul_comm]
    exact (r1 n).2
  have hfin : ∫⁻ s in Icc (0 : ℝ) t, h2_Dinf θ v U μ s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have h2 : ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu v (μ r)) ≤ Yl / κ := by
    have e : (fun r => h2_diss θ U (h2_mu v (μ r))) = fun r => (h2_Dinf θ v U μ r).toReal :=
      funext fun r => S.diss_eq r
    rw [e, integral_toReal S.meas_Dinf.aemeasurable (ae_lt_top S.meas_Dinf hfin)]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hY0 hκ0.le) h1
  have h3 : κ * ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu v (μ r)) ≤ Yl := by
    calc _ ≤ κ * (Yl / κ) := mul_le_mul_of_nonneg_left h2 hκ0.le
      _ = Yl := by field_simp
  rw [hYl] at h3
  exact ⟨hfin, by linarith⟩

/-- The dissipation inequality for the mollified densities, in the form needed by `cepH2_mollified_ineq`. -/
theorem H2Set.result2 (S : H2Set θ v U K μ T M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    h2_free θ U (h2_mu v (μ t)) + θ * (1 - δ) * ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu v (μ r)) ≤
      h2_free θ U (h2_mu v (μ 0)) + t * ((K : ℝ) ^ 2 * (N * v) / (4 * θ * δ)) :=
  (S.result2' hδ hδ1 ht).2

end

end HRS.MC.CepH2

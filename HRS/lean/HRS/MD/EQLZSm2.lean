import HRS.MD.EQLZSm1

/-!
# EQ-LZ packet SM, part 2: the energy term and its limit

* `sm_configGradSq_eq`: `configGradSq F X = ‖∇(F ∘ e⁻¹)(e X)‖²` (`e = d1_configEquiv`).
* `sm_energy_tendsto`: for a bounded measurable `g` on `𝕋^{N d}`, along the levels `M = n`,
  `c_n ∫ g dπ_n → ∫ g∘e dgibbsRef`, where `c_n = Z_n / Z` and `π_n = d1_gibbsMeasure D.invβ (b15d_U D n)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

namespace MD

namespace EQLZSm

variable {d N : ℕ}

/-- `C^∞` on the torus gives `C^1` and `C^2`. -/
theorem sm_isCk_of_smooth {n : ℕ} {φ : Torus n → ℝ} (h : Torus.IsSmooth φ) (k : ℕ) : Torus.IsCk k φ :=
  (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from h).of_le
    (WithTop.coe_le_coe.2 (le_top : (k : ℕ∞) ≤ ⊤))

/-- The squared configuration gradient through the torus gradient of `F ∘ e⁻¹`. -/
theorem sm_configGradSq_eq (F : Config d N → ℝ) (X : Config d N) :
    LZ.configGradSq F X =
      ‖Torus.grad (fun x => F ((d1_configEquiv d N).symm x)) (d1_configEquiv d N X)‖ ^ 2 := by
  have hcl : configLift (fun _ : ℝ => F) 0 = d1_cl (fun x => F ((d1_configEquiv d N).symm x)) := by
    funext Y
    simp [configLift, d1_cl]
  unfold LZ.configGradSq
  rw [hcl]
  simp only [← d1_grad_apply]
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Equiv.sum_comp (d1_idx d N) (fun m => (Torus.grad (fun x => F ((d1_configEquiv d N).symm x))
    (d1_configEquiv d N X)).ofLp m ^ 2))

/-- The squared torus gradient of a smooth function is continuous. -/
theorem sm_gradSq_continuous {n : ℕ} {φ : Torus n → ℝ} (h : Torus.IsSmooth φ) :
    Continuous fun x => ‖Torus.grad φ x‖ ^ 2 :=
  by
  have h1 : Continuous (d1_gradDrift φ) := d1_gradDrift_continuous h
  have h2 : Continuous fun x => ‖Torus.grad φ x‖ := by
    have : (fun x => ‖Torus.grad φ x‖) = fun x => ‖d1_gradDrift φ x‖ := by
      funext x; simp [d1_gradDrift]
    rw [this]; exact h1.norm
  exact h2.pow 2

/-- Integral against a density `Zr * w` (with respect to Lebesgue). -/
theorem sm_integral_density (Zr : ℝ) (hZ : 0 ≤ Zr) (w : Config d N → ℝ) (hw0 : ∀ X, 0 ≤ w X)
    (hwm : Measurable w) (G : Config d N → ℝ) :
    ∫ X, G X ∂((volume : Measure (Config d N)).withDensity fun X => ENNReal.ofReal (Zr * w X)) =
      Zr * ∫ X, w X * G X := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun X => ENNReal.ofReal (Zr * w X))
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hwm)).aemeasurable
    (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg hZ (hw0 X)), mul_assoc]

/-- **Energy limit.**  For bounded measurable `g` on `𝕋^{N d}`: `c_n ∫ g dπ_n → ∫ g∘e dgibbsRef`. -/
theorem sm_energy_tendsto (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    (g : Torus (N * d) → ℝ) (hgm : Measurable g) (Cg : ℝ) (hg : ∀ x, |g x| ≤ Cg) :
    Tendsto (fun n : ℕ =>
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) * (gibbsPartition D N)⁻¹).toReal *
        ∫ x, g x ∂(d1_gibbsMeasure D.invβ (b15d_U (N := N) D (n : ℝ)))) atTop
      (𝓝 (∫ X, g (d1_configEquiv d N X) ∂(gibbsRef D N))) := by
  obtain ⟨hZg0, hZgt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  have hZgr : 0 < (gibbsPartition D N).toReal := ENNReal.toReal_pos hZg0.ne' hZgt.ne
  have hVc := b15_continuous_of_isCk hV
  set e := d1_configEquiv d N with he
  set G : Config d N → ℝ := fun X => g (e X) with hGdef
  have hGm : Measurable G := hgm.comp e.measurable
  have hGb : ∀ X, |G X| ≤ Cg := fun X => hg _
  -- the level integrals
  have hlev : ∀ n : ℕ,
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) * (gibbsPartition D N)⁻¹).toReal *
        ∫ x, g x ∂(d1_gibbsMeasure D.invβ (b15d_U (N := N) D (n : ℝ))) =
      (gibbsPartition D N).toReal⁻¹ *
        ∫ X, b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) X * G X := by
    intro n
    obtain ⟨hZk_top, hZk_0⟩ := b15bp_partitionGen_bounds (N := N) D hβ hV (Nat.cast_nonneg n)
    have hZkr : 0 < (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ))).toReal :=
      ENNReal.toReal_pos hZk_0 hZk_top
    have hmap := b15e_gibbsRefGen_map (N := N) D.invβ (b15c_potentialReg (N := N) D (n : ℝ))
    have h1 : ∫ x, g x ∂(d1_gibbsMeasure D.invβ (b15d_U (N := N) D (n : ℝ))) =
        ∫ X, G X ∂(b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ))) := by
      have : d1_gibbsMeasure D.invβ (b15d_U (N := N) D (n : ℝ)) =
          (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ))).map e := hmap.symm
      rw [this, integral_map_equiv]
    rw [h1, b15c_gibbsRefGen_eq_withDensity _ _ hZk_top hZk_0,
      sm_integral_density _ (inv_nonneg.mpr hZkr.le)
        (b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)))
        (fun X => (Real.exp_pos _).le)
        ((Real.measurable_exp.comp (measurable_const.mul
          (b15c_potentialReg_continuous (N := N) D hVc (n : ℝ)).measurable))) G]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    field_simp
  -- the limit integral
  have hlim : ∫ X, G X ∂(gibbsRef D N) =
      (gibbsPartition D N).toReal⁻¹ * ∫ X, gibbsWeight D X * G X := by
    rw [b15bp_gibbsRef_eq_withDensity D hβ hV]
    exact sm_integral_density _ (inv_nonneg.mpr hZgr.le) _
      (fun X => by classical unfold gibbsWeight; split_ifs <;> positivity)
      (b15c_measurable_gibbsWeight D hVc) G
  simp_rw [hlev]
  rw [hlim]
  refine Tendsto.const_mul _ ?_
  obtain ⟨C, hC⟩ := b15c_gibbsWeightReg_le_const (N := N) D hβ hV
  have hC0 : 0 ≤ C := le_trans
    (Real.exp_pos (-(D.invβ⁻¹) * b15c_potentialReg (N := N) D 0 (fun _ => 0))).le
    (hC 0 le_rfl (fun _ => 0))
  refine tendsto_integral_of_dominated_convergence (fun _ => C * Cg) ?_ (integrable_const _) ?_ ?_
  · intro n
    exact ((Real.measurable_exp.comp (measurable_const.mul
      (b15c_potentialReg_continuous (N := N) D hVc (n : ℝ)).measurable)).mul hGm).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun X => ?_
    have hpos : 0 < b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) X := Real.exp_pos _
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hpos, Real.norm_eq_abs]
    exact mul_le_mul (hC _ (Nat.cast_nonneg n) X) (hGb X) (abs_nonneg _) hC0
  · filter_upwards [b15_ae_not_collision (d := d) (N := N) (b15_one_le_d D)] with X hX
    have h2 : ∀ᶠ n : ℕ in atTop, b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D (n : ℝ)) X =
        gibbsWeight D X :=
      tendsto_natCast_atTop_atTop.eventually (b15c_gibbsWeightReg_eventuallyEq D hX)
    exact (tendsto_const_nhds.congr' (h2.mono fun n hn => by rw [hn])).mul_const _

end EQLZSm

end MD

end HRS

end

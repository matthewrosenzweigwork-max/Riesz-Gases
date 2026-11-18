import HRS.Main.TorusTheorems
import HRS.Prob.HilbertMartingale

/-!
# Packet A8P, part 1: the abstract `d_{C²}` comparison (smooth case)

`a8p_smooth_abstract`: for `Z = I_emp + M_T + R` with `I_emp` `ℱ_0`-measurable and `M` a vector martingale with
covariation, `d_{C²}(Law Z, Law Ĩ * N(0,∫Σ̄)) ≤ E‖R‖ + E‖I_emp - Ĩ‖ + ½ E∫‖Σ-Σ̄‖_{S₁}`, for ANY random vector `Ĩ`
(no measurability with respect to `ℱ_0` is needed: only its law enters).  Proved by the G-free interpolation `shift_bound_f`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {p : ℕ}

theorem a8p_cbUnit_deriv_le {Φ : (ℝ^p) → ℝ} (hΦ : Φ ∈ CbUnitBall (ℝ^p) 2) {j : ℕ} (hj : j ≤ 2)
    (x : ℝ^p) : ‖iteratedFDeriv ℝ j Φ x‖ ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := hΦ
  have hbdd := h2 j hj
  have hle : ‖iteratedFDeriv ℝ j Φ x‖ ≤ ⨆ z : ℝ^p, ‖iteratedFDeriv ℝ j Φ z‖ :=
    le_ciSup (f := fun z : ℝ^p => ‖iteratedFDeriv ℝ j Φ z‖) hbdd x
  refine hle.trans (le_trans ?_ h3)
  unfold cbNorm
  have hnn : ∀ i ∈ Finset.range 3, 0 ≤ ⨆ z : ℝ^p, ‖iteratedFDeriv ℝ i Φ z‖ :=
    fun i _ => Real.iSup_nonneg fun z => norm_nonneg _
  exact Finset.single_le_sum hnn (Finset.mem_range.2 (by omega))

theorem a8p_cbUnit_memCb {Φ : (ℝ^p) → ℝ} (hΦ : Φ ∈ CbUnitBall (ℝ^p) 2) : MemCb 2 Φ :=
  ⟨hΦ.1, hΦ.2.1⟩

theorem a8p_cbUnit_hess {Φ : (ℝ^p) → ℝ} (hΦ : Φ ∈ CbUnitBall (ℝ^p) 2) : hessSup Φ ≤ 1 :=
  Real.iSup_le (fun x => a8p_cbUnit_deriv_le hΦ (by norm_num) x) zero_le_one

theorem a8p_cbUnit_lip {Φ : (ℝ^p) → ℝ} (hΦ : Φ ∈ CbUnitBall (ℝ^p) 2) (x y : ℝ^p) :
    |Φ x - Φ y| ≤ ‖x - y‖ := by
  have hd : Differentiable ℝ Φ := hΦ.1.differentiable (by norm_num)
  have h1 : ∀ z, ‖fderiv ℝ Φ z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one]; exact a8p_cbUnit_deriv_le hΦ (by norm_num) z
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := Φ) (s := Set.univ)
    (fun z _ => hd z) (fun z _ => h1 z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

theorem a8p_cbUnit_bdd {Φ : (ℝ^p) → ℝ} (hΦ : Φ ∈ CbUnitBall (ℝ^p) 2) (x : ℝ^p) : |Φ x| ≤ 1 := by
  have := a8p_cbUnit_deriv_le hΦ (j := 0) (by norm_num) x
  simpa [norm_iteratedFDeriv_zero] using this


section Smooth

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem a8p_gaussSmooth_lip {Φ : (ℝ^p) → ℝ} (hΦ : Φ ∈ CbUnitBall (ℝ^p) 2) (γ : Measure (ℝ^p))
    [IsProbabilityMeasure γ] (x y : ℝ^p) :
    |(∫ z, Φ (x + z) ∂γ) - ∫ z, Φ (y + z) ∂γ| ≤ ‖x - y‖ := by
  have hc : Continuous Φ := hΦ.1.continuous
  have hi : ∀ w : ℝ^p, Integrable (fun z => Φ (w + z)) γ := fun w =>
    Integrable.of_bound (C := 1) (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa using a8p_cbUnit_bdd hΦ (w + z))
  rw [← integral_sub (hi x) (hi y)]
  have : ∀ z, |Φ (x + z) - Φ (y + z)| ≤ ‖x - y‖ := fun z => by
    have := a8p_cbUnit_lip hΦ (x + z) (y + z)
    simpa [add_sub_add_right_eq_sub] using this
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖x - y‖) (Filter.Eventually.of_forall fun z => ?_)).trans
    (by simp)
  simpa [Real.norm_eq_abs] using this z

theorem a8p_smooth_abstract (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (Iemp : Ω → (ℝ^p)) (hI : Measurable[ℱ 0] Iemp) (Itil : Ω → (ℝ^p)) (hIt : Measurable Itil)
    (Z R : Ω → (ℝ^p)) (hR : Integrable R P) (hZ : ∀ᵐ ω ∂P, Z ω = Iemp ω + M T ω + R ω)
    (hdiff : Integrable (fun ω => ‖Iemp ω - Itil ω‖) P) :
    smoothDist 2 (law P Z) (law P Itil ∗ multivariateGaussian 0 (integratedCov T sb)) ≤
      ∫ ω, ‖R ω‖ ∂P + ∫ ω, ‖Iemp ω - Itil ω‖ ∂P + (1 / 2) * covDiscrepancyMatrix P T Sg sb := by
  have hm : ℱ 0 ≤ mΩ := ℱ.le 0
  have hIm : Measurable Iemp := hI.mono hm le_rfl
  have hMt : AEMeasurable (M T) P := (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable R P := hR.aestronglyMeasurable.aemeasurable
  have hZm : AEMeasurable Z P := by
    refine ((hIm.aemeasurable.add hMt).add hRm).congr ?_
    filter_upwards [hZ] with ω h using h.symm
  set γ : Measure (ℝ^p) := multivariateGaussian 0 (integratedCov T sb) with hγ
  haveI : IsProbabilityMeasure γ := inferInstance
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) with hg
  have hg0 : 0 ≤ ∫ ω, g ω ∂P :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  have hRn : 0 ≤ ∫ ω, ‖R ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
  have hDn : 0 ≤ ∫ ω, ‖Iemp ω - Itil ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
  have hcov : covDiscrepancyMatrix P T Sg sb = ∫ ω, g ω ∂P := rfl
  refine Real.iSup_le (fun ⟨Φ, hΦ⟩ => ?_) (by rw [hcov]; positivity)
  have hΦm := a8p_cbUnit_memCb hΦ
  have hc : Continuous Φ := hΦ.1.continuous
  set f : (ℝ^p) → ℝ := fun x => ∫ z, Φ (x + z) ∂γ with hf
  have hfi : ∀ w : ℝ^p, Integrable (fun z => Φ (w + z)) γ := fun w =>
    Integrable.of_bound (C := 1) (hc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa using a8p_cbUnit_bdd hΦ (w + z))
  have hflip : ∀ x y, |f x - f y| ≤ ‖x - y‖ := fun x y => a8p_gaussSmooth_lip hΦ γ x y
  have hfc : Continuous f := by
    have : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [dist_eq_norm, Real.dist_eq] using hflip x y
    exact this.continuous
  have hfb : ∀ x, |f x| ≤ 1 := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := γ) (C := 1) (f := fun z => Φ (x + z))
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using a8p_cbUnit_bdd hΦ (x + z))
    simpa [Real.norm_eq_abs, hf] using this
  -- the law of Z and the convolution
  have e1 : ∫ x, Φ x ∂(law P Z) = ∫ ω, Φ (Z ω) ∂P := integral_map hZm hc.aestronglyMeasurable
  have hΦint : Integrable Φ (law P Itil ∗ γ) :=
    Integrable.of_bound (C := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using a8p_cbUnit_bdd hΦ x)
  have e2 : ∫ x, Φ x ∂(law P Itil ∗ γ) = ∫ ω, f (Itil ω) ∂P := by
    rw [integral_conv hΦint, integral_map hIt.aemeasurable (hfc.aestronglyMeasurable.mono_measure le_rfl)]
  show |∫ x, Φ x ∂(law P Z) - ∫ x, Φ x ∂(law P Itil ∗ γ)| ≤ _
  rw [e1, e2, hcov]
  -- integrability facts
  have hiΦ : ∀ F : Ω → ℝ^p, AEMeasurable F P → Integrable (fun ω => Φ (F ω)) P := fun F hF =>
    Integrable.of_bound (C := 1) (hc.measurable.comp_aemeasurable hF).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using a8p_cbUnit_bdd hΦ (F ω))
  have hif : ∀ F : Ω → ℝ^p, AEMeasurable F P → Integrable (fun ω => f (F ω)) P := fun F hF =>
    Integrable.of_bound (C := 1) (hfc.measurable.comp_aemeasurable hF).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using hfb (F ω))
  have hZi := hiΦ Z hZm
  have hi0 := hiΦ (fun ω => Iemp ω + M T ω) (hIm.aemeasurable.add hMt)
  have hfI := hif Iemp hIm.aemeasurable
  have hfT := hif Itil hIt.aemeasurable
  -- step 1: remove R
  have s1 : |(∫ ω, Φ (Z ω) ∂P) - ∫ ω, Φ (Iemp ω + M T ω) ∂P| ≤ ∫ ω, ‖R ω‖ ∂P := by
    rw [← integral_sub hZi hi0, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hR.norm ?_
    filter_upwards [hZ] with ω hω
    rw [Real.norm_eq_abs, hω]
    simpa using a8p_cbUnit_lip hΦ (Iemp ω + M T ω + R ω) (Iemp ω + M T ω)
  -- step 2: Lemma A.27 in its G-free form, `A = univ`
  have s2 : |(∫ ω, Φ (Iemp ω + M T ω) ∂P) - ∫ ω, f (Iemp ω) ∂P| ≤ (1 / 2) * ∫ ω, g ω ∂P := by
    have := shift_bound_f P ℱ T hT M Sg hM sb hsb Iemp hI Φ hΦm f hfc (fun x => rfl)
      (A := Set.univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at this
    have h1 := a8p_cbUnit_hess hΦ
    refine this.trans ?_
    have : 0 ≤ ∫ ω, g ω ∂P := hg0
    nlinarith
  -- step 3: replace `Iemp` by `Itil` in `f`
  have s3 : |(∫ ω, f (Iemp ω) ∂P) - ∫ ω, f (Itil ω) ∂P| ≤ ∫ ω, ‖Iemp ω - Itil ω‖ ∂P := by
    rw [← integral_sub hfI hfT, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hdiff (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hflip _ _
  have : (∫ ω, Φ (Z ω) ∂P) - ∫ ω, f (Itil ω) ∂P =
      ((∫ ω, Φ (Z ω) ∂P) - ∫ ω, Φ (Iemp ω + M T ω) ∂P) +
      (((∫ ω, Φ (Iemp ω + M T ω) ∂P) - ∫ ω, f (Iemp ω) ∂P) +
        ((∫ ω, f (Iemp ω) ∂P) - ∫ ω, f (Itil ω) ∂P)) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add s1 ((abs_add_le _ _).trans (add_le_add s2 s3)) |>.trans (le_of_eq ?_)
  ring

end Smooth

end HRS.Main.A8P

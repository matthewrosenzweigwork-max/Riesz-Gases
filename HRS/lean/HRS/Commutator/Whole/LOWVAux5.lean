import HRS.Commutator.Whole.LOWVAux4

/-!
# CMX-LOWV auxiliary 5: `𝒞_F(V,σ) = 𝒞_F(V,a)` for `a = ψ_Λ * σ`, `Λ > 4`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

theorem lowv_swap_meas (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    (hmom : Integrable (fun y : Euc d => ‖y‖) μ) {K : Euc d → Euc d → ℝ}
    (hKc : Continuous fun p : Euc d × Euc d => K p.1 p.2) {c : ℝ}
    (hKb : ∀ x y, |K x y| ≤ c * (‖x‖ + ‖y‖)) {a : Euc d → ℝ} (hac : Continuous a)
    (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|)) :
    Integrable (fun y => a y * ∫ x, K x y ∂μ) ∧
    ∫ x, (∫ y, K x y * a y) ∂μ = ∫ y, a y * ∫ x, K x y ∂μ := by
  have ha1 : Integrable (fun y : Euc d => |a y|) := by
    refine hai.mono' hac.abs.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have : 0 ≤ |a y| := abs_nonneg _
    nlinarith [norm_nonneg y]
  have ha2 : Integrable (fun y : Euc d => ‖y‖ * |a y|) := by
    refine hai.mono' ((continuous_norm.mul hac.abs).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : 0 ≤ |a y| := abs_nonneg _
    nlinarith [norm_nonneg y]
  have hint : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * a p.2) (μ.prod volume) := by
    have hg : Integrable (fun p : Euc d × Euc d => c * (‖p.1‖ * |a p.2|) + c * (1 * (‖p.2‖ * |a p.2|)))
        (μ.prod volume) :=
      ((hmom.mul_prod ha1).const_mul c).add (((integrable_const (1 : ℝ)).mul_prod ha2).const_mul c)
    refine hg.mono' ((hKc.mul (hac.comp continuous_snd)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |K p.1 p.2| * |a p.2| ≤ (c * (‖p.1‖ + ‖p.2‖)) * |a p.2| := by gcongr; exact hKb _ _
      _ = c * (‖p.1‖ * |a p.2|) + c * (1 * (‖p.2‖ * |a p.2|)) := by ring
  have h2 := integral_integral_swap (f := fun x y => K x y * a y) hint
  have h3 : ∀ y, ∫ x, K x y * a y ∂μ = a y * ∫ x, K x y ∂μ := by
    intro y
    rw [integral_mul_const, mul_comm]
  refine ⟨?_, ?_⟩
  · have := hint.integral_prod_right
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only
    exact h3 y
  · rw [h2]
    exact integral_congr_ae (Eventually.of_forall h3)

theorem lowv_Ccomm_eq {Λ : ℝ} (hΛ : 4 < Λ) {F V : Euc d → Euc d} {Lv B : ℝ}
    (hodd : ∀ x, F (-x) = -F x) (hFc : Continuous F) (hB : ∀ x, ‖F x‖ ≤ B)
    (hVc : Continuous V) (hV : ∀ x y, ‖V x - V y‖ ≤ Lv * ‖x - y‖) (hLv : 0 ≤ Lv)
    (hVi : ∀ i, FourierSuppIn 2 (fun x => V x i)) (hFi : ∀ i, FourierSuppIn 2 (fun x => F x i))
    (hFt : ∀ i, Function.HasTemperateGrowth (fun x => F x i))
    (σ : SMeas d) (hf : σ.IsFinite)
    (hmp : Integrable (fun y : Euc d => ‖y‖) σ.pos) (hmn : Integrable (fun y : Euc d => ‖y‖) σ.neg)
    (a : Euc d → ℝ) (hac : Continuous a) (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|))
    (ha : ∀ x, a x = σ.int (fun z => psiL Λ (x - z))) :
    Ccomm F V σ = CcommFun F V a := by
  have hΛ0 : 0 < Λ := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K : Euc d → Euc d → ℝ := lowv_K F V with hKdef
  have hKc : Continuous fun p : Euc d × Euc d => K p.1 p.2 := lowv_K_continuous hFc hVc
  have hKb : ∀ x y, |K x y| ≤ (Lv * B) * (‖x‖ + ‖y‖) := lowv_K_bound hB hV hLv
  have hsymm : ∀ x y, K y x = K x y := lowv_K_symm hodd V
  have hVg : ∀ x, ‖V x‖ ≤ (‖V 0‖ + Lv) * (1 + ‖x‖) := by
    intro x
    have h1 : ‖V x‖ ≤ ‖V 0‖ + Lv * ‖x‖ := by
      have := hV x 0
      rw [sub_zero] at this
      calc ‖V x‖ = ‖(V x - V 0) + V 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖V x - V 0‖ + ‖V 0‖ := norm_add_le _ _
        _ ≤ Lv * ‖x‖ + ‖V 0‖ := by gcongr
        _ = ‖V 0‖ + Lv * ‖x‖ := by ring
    nlinarith [norm_nonneg (V 0), norm_nonneg x, mul_nonneg hLv (norm_nonneg x)]
  have hband_y : ∀ y z, Pleq Λ (fun x => K x y) z = K z y := by
    intro y z
    refine lowv_bandlimited (R := 4) (by norm_num) hΛ (k := fun x => K x y)
      (hKc.comp (continuous_id.prodMk continuous_const)) (Lv * B * (1 + ‖y‖)) ?_
      (lowv_K_fsupp hVi hFi hFt hVc hFc hVg hB y) z
    intro x
    calc |K x y| ≤ (Lv * B) * (‖x‖ + ‖y‖) := hKb x y
      _ ≤ Lv * B * (1 + ‖y‖) * (1 + ‖x‖) := by
          have : 0 ≤ Lv * B := by positivity
          nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg this (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
      _ = _ := by ring
  have hband_x : ∀ x z, Pleq Λ (fun y => K x y) z = K x z := by
    intro x z
    have : (fun y => K x y) = fun y => K y x := funext fun y => (hsymm x y).symm
    rw [this]
    exact (hband_y x z).trans (hsymm x z)
  -- Step I
  have hI : ∀ x, σ.int (fun y => K x y) = ∫ y, K x y * a y := by
    intro x
    have h := (lowv_pair_sint hΛ0 σ hf hmp hmn (k := fun y => K x y)
      (hKc.comp (continuous_const.prodMk continuous_id)) (Lv * B * (1 + ‖x‖)) ?_ (hband_x x)).2
    · rw [h]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [ha y]
    · intro y
      calc |K x y| ≤ (Lv * B) * (‖x‖ + ‖y‖) := hKb x y
        _ ≤ Lv * B * (1 + ‖x‖) * (1 + ‖y‖) := by
            have : 0 ≤ Lv * B := by positivity
            nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg this (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  -- Step III
  have hIII : ∀ y, σ.int (fun x => K x y) = ∫ x, K x y * a x := by
    intro y
    have h := (lowv_pair_sint hΛ0 σ hf hmp hmn (k := fun x => K x y)
      (hKc.comp (continuous_id.prodMk continuous_const)) (Lv * B * (1 + ‖y‖)) ?_ (hband_y y)).2
    · rw [h]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [ha x]
    · intro x
      calc |K x y| ≤ (Lv * B) * (‖x‖ + ‖y‖) := hKb x y
        _ ≤ Lv * B * (1 + ‖y‖) * (1 + ‖x‖) := by
            have : 0 ≤ Lv * B := by positivity
            nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg this (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  -- Step II
  obtain ⟨hp, hn⟩ := hf
  haveI := hp
  haveI := hn
  obtain ⟨hs1, he1⟩ := lowv_swap_meas σ.pos hmp hKc hKb hac hai
  obtain ⟨hs2, he2⟩ := lowv_swap_meas σ.neg hmn hKc hKb hac hai
  have hII : σ.int (fun x => ∫ y, K x y * a y) = ∫ y, a y * σ.int (fun x => K x y) := by
    unfold SMeas.int
    rw [he1, he2, ← integral_sub hs1 hs2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hL : Ccomm F V σ = ∫ y, a y * ∫ x, K x y * a x := by
    unfold Ccomm SMeas.pair2
    simp_rw [lowv_commKer_eq]
    simp_rw [← hKdef]
    have : (fun x => σ.int fun y => K x y) = fun x => ∫ y, K x y * a y := funext hI
    rw [this, hII]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hIII y]
  rw [hL]
  unfold CcommFun
  simp_rw [lowv_commKer_eq, ← hKdef]
  have e : ∀ x, ∫ y, K x y * a x * a y = a x * ∫ y, K x y * a y := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  simp_rw [e]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [hsymm]

end HRS.Commutator.Whole

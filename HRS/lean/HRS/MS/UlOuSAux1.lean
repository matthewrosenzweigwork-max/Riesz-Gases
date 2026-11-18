import HRS.MS.UlOu
import HRS.MS.UlNormAux3
import HRS.MS.ThCorrSob

/-!
# UL-3, part 1 (UlOuSAux1): uniform composition with the OU flow `e^{-τQ}`

(docstring: see `UlOuS.lean`.)  Helper lemmas carry the prefix `ul3_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}


theorem ul3_det_adjoint (A : Euc d →ₗ[ℝ] Euc d) :
    LinearMap.det (LinearMap.adjoint A) = LinearMap.det A := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b A]
  have := LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin d) ℝ) (EuclideanSpace.basisFun (Fin d) ℝ) A
  rw [this, Matrix.det_conjTranspose]
  simp

theorem ul3_det_symm (e : Euc d ≃ₗ[ℝ] Euc d) :
    LinearMap.det (e.symm : Euc d →ₗ[ℝ] Euc d) = (LinearMap.det (e : Euc d →ₗ[ℝ] Euc d))⁻¹ := by
  have h : LinearMap.det (e : Euc d →ₗ[ℝ] Euc d) * LinearMap.det (e.symm : Euc d →ₗ[ℝ] Euc d) = 1 := by
    rw [← LinearMap.det_comp]
    have : (e : Euc d →ₗ[ℝ] Euc d) ∘ₗ (e.symm : Euc d →ₗ[ℝ] Euc d) = LinearMap.id := by
      ext x; simp
    rw [this]; simp
  exact eq_inv_of_mul_eq_one_right h

/-- Explicit-constant version of `ul0_sobE_comp_equiv` (real order `s ≥ 0`). -/
theorem ul3_sobE_comp (s : ℝ) (hs : 0 ≤ s) (e : Euc d ≃ₗ[ℝ] Euc d) (v : Euc d → ℝ)
    (hv2 : MemLp v 2 volume) (hv1 : Integrable v volume) :
    sobolevNormE s (fun x => v (e x)) ≤
      ENNReal.ofReal (Real.sqrt (|LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ *
        (1 + ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ^ 2) ^ s)) * sobolevNormE s v := by
  classical
  set T0 : Euc d →ₗ[ℝ] Euc d := LinearMap.adjoint (e.symm : Euc d →ₗ[ℝ] Euc d) with hT0
  set S0 : Euc d →ₗ[ℝ] Euc d := LinearMap.adjoint (e : Euc d →ₗ[ℝ] Euc d) with hS0
  have hST : ∀ ξ, S0 (T0 ξ) = ξ := by
    intro ξ
    apply ext_inner_left ℝ
    intro w
    rw [hS0, LinearMap.adjoint_inner_right, hT0, LinearMap.adjoint_inner_right]
    simp
  have hTS : ∀ ξ, T0 (S0 ξ) = ξ := by
    intro ξ
    apply ext_inner_left ℝ
    intro w
    rw [hT0, LinearMap.adjoint_inner_right, hS0, LinearMap.adjoint_inner_right]
    simp
  set T' : Euc d ≃ₗ[ℝ] Euc d := LinearEquiv.ofLinearMap T0 S0 (LinearMap.ext hTS) (LinearMap.ext hST) with hT'
  have hdete : LinearMap.det (e : Euc d →ₗ[ℝ] Euc d) ≠ 0 := (LinearEquiv.isUnit_det' e).ne_zero
  have hdetT : LinearMap.det (T' : Euc d →ₗ[ℝ] Euc d) = (LinearMap.det (e : Euc d →ₗ[ℝ] Euc d))⁻¹ := by
    show LinearMap.det T0 = _
    rw [hT0, ul3_det_adjoint, ul3_det_symm]
  set c1 : ℝ := |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ with hc1
  set c2 : ℝ := |(LinearMap.det (T' : Euc d →ₗ[ℝ] Euc d))⁻¹| with hc2
  have hc2e : c2 = |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)| := by
    rw [hc2, hdetT, inv_inv]
  have hc1pos : 0 < c1 := inv_pos.2 (abs_pos.2 hdete)
  have hc2pos : 0 < c2 := by rw [hc2e]; exact abs_pos.2 hdete
  set ec : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d) with hec
  set Kw : ℝ := 1 + ‖ec‖ ^ 2 with hKw
  have hKw1 : 1 ≤ Kw := by rw [hKw]; nlinarith [sq_nonneg ‖ec‖]
  have hKwpos : 0 < Kw := by linarith
  have hwtle : ∀ ξ : Euc d, wt ξ ≤ Kw * wt (T0 ξ) := by
    intro ξ
    have h1 : ‖ξ‖ ≤ ‖ec‖ * ‖T0 ξ‖ := by
      have hS : LinearMap.toContinuousLinearMap S0 = ContinuousLinearMap.adjoint ec := by
        rw [hS0, LinearMap.adjoint_toContinuousLinearMap]
      have := (ContinuousLinearMap.adjoint ec).le_opNorm (T0 ξ)
      rw [ContinuousLinearMap.adjoint.norm_map ec, ← hS] at this
      simpa [hST ξ] using this
    unfold wt
    have h2 : ‖ξ‖ ^ 2 ≤ ‖ec‖ ^ 2 * ‖T0 ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (‖ec‖ * ‖T0 ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = _ := by ring
    have h3 : 0 ≤ ‖ec‖ ^ 2 * (4 * Real.pi ^ 2 * ‖T0 ξ‖ ^ 2) := by positivity
    rw [hKw]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)]
  have hdet' : LinearMap.det (e : Euc d →ₗ[ℝ] Euc d) ≠ 0 := hdete
  have hmap : Measure.map e (volume : Measure (Euc d)) = ENNReal.ofReal |(LinearMap.det (e : Euc d →ₗ[ℝ] Euc d))⁻¹| •
      (volume : Measure (Euc d)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Euc d)) (f := (e : Euc d →ₗ[ℝ] Euc d)) hdet'
  have heme : Measurable (fun x => e x) := (LinearMap.continuous_of_finiteDimensional (e : Euc d →ₗ[ℝ] Euc d)).measurable
  have hve2 : MemLp (fun x => v (e x)) 2 volume := by
    have h1 : MemLp v 2 (Measure.map e (volume : Measure (Euc d))) := by
      rw [hmap]; exact hv2.smul_measure ENNReal.ofReal_ne_top
    exact (memLp_map_measure_iff (by rw [hmap]; exact hv2.aestronglyMeasurable.smul_measure _) heme.aemeasurable).1 h1
  have hve1 : Integrable (fun x => v (e x)) volume := by
    have h1 : Integrable v (Measure.map e (volume : Measure (Euc d))) := by
      rw [hmap]; exact hv1.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure (by rw [hmap]; exact hv1.aestronglyMeasurable.smul_measure _) heme.aemeasurable).1 h1
  set Fv : Euc d → ℂ := fun w => ((v w : ℝ) : ℂ) with hFv
  have hFc : Continuous (𝓕 Fv) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous₂ hv1.ofReal
  set Ψ : Euc d → ℝ≥0∞ := fun η => ENNReal.ofReal (wt η ^ s * ‖𝓕 Fv η‖ ^ 2) with hΨ
  have hΨm : Measurable Ψ :=
    ENNReal.measurable_ofReal.comp (((continuous_wt_rpow s).mul (hFc.norm.pow 2)).measurable)
  have hΨint : ∫⁻ η, Ψ η = sobolevNormE s v ^ 2 := by
    rw [um_sobE_sq hv2]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 hv1 hv2] with η hη
    simp only [hΨ, hη, hFv]
  have hlhs : sobolevNormE s (fun x => v (e x)) ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖c1 • 𝓕 Fv (T0 ξ)‖ ^ 2) := by
    rw [um_sobE_sq hve2]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 hve1 hve2] with ξ hξ
    rw [hξ]
    congr 3
    exact congrArg norm (ul0_fourier_comp_equiv e Fv ξ)
  have hpt : ∀ ξ, ENNReal.ofReal (wt ξ ^ s * ‖c1 • 𝓕 Fv (T0 ξ)‖ ^ 2) ≤
      ENNReal.ofReal (c1 ^ 2 * Kw ^ s) * Ψ (T' ξ) := by
    intro ξ
    have hT'ξ : T' ξ = T0 ξ := rfl
    rw [hT'ξ, hΨ]
    simp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc1pos]
    have h1 : wt ξ ^ s ≤ Kw ^ s * wt (T0 ξ) ^ s := by
      rw [← Real.mul_rpow hKwpos.le (wt_pos _).le]
      exact Real.rpow_le_rpow (wt_pos ξ).le (hwtle ξ) hs
    have h2 : 0 ≤ ‖𝓕 Fv (T0 ξ)‖ ^ 2 := sq_nonneg _
    calc wt ξ ^ s * (c1 * ‖𝓕 Fv (T0 ξ)‖) ^ 2
        = c1 ^ 2 * (wt ξ ^ s * ‖𝓕 Fv (T0 ξ)‖ ^ 2) := by ring
      _ ≤ c1 ^ 2 * ((Kw ^ s * wt (T0 ξ) ^ s) * ‖𝓕 Fv (T0 ξ)‖ ^ 2) := by gcongr
      _ = _ := by ring
  have hmain : sobolevNormE s (fun x => v (e x)) ^ 2 ≤
      ENNReal.ofReal (Real.sqrt (c1 ^ 2 * Kw ^ s * c2)) ^ 2 * sobolevNormE s v ^ 2 := by
    rw [hlhs]
    calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖c1 • 𝓕 Fv (T0 ξ)‖ ^ 2)
        ≤ ∫⁻ ξ, ENNReal.ofReal (c1 ^ 2 * Kw ^ s) * Ψ (T' ξ) := lintegral_mono hpt
      _ = ENNReal.ofReal (c1 ^ 2 * Kw ^ s) * ∫⁻ ξ, Ψ (T' ξ) := by
          have hΨT : Measurable (fun ξ => Ψ (T' ξ)) := hΨm.comp T'.toContinuousLinearEquiv.continuous.measurable
          rw [lintegral_const_mul _ hΨT]
      _ = ENNReal.ofReal (c1 ^ 2 * Kw ^ s) * (ENNReal.ofReal c2 * ∫⁻ η, Ψ η) := by
          rw [ul0_lintegral_comp_equiv T' Ψ hΨm]
      _ = ENNReal.ofReal (Real.sqrt (c1 ^ 2 * Kw ^ s * c2)) ^ 2 * sobolevNormE s v ^ 2 := by
          rw [hΨint, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
            ENNReal.ofReal_mul (p := c1 ^ 2 * Kw ^ s) (q := c2) (by positivity), mul_assoc]
  have hK : Real.sqrt (c1 ^ 2 * Kw ^ s * c2) = Real.sqrt (|LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ *
        (1 + ‖ec‖ ^ 2) ^ s) := by
    congr 1
    rw [hc2e, hc1]
    have : 0 < |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)| := abs_pos.2 hdete
    field_simp
    rfl
  rw [← mul_pow] at hmain
  have := (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hmain
  rwa [hK] at this



theorem ul3_cb_apply {m j : ℕ} {f : Euc d → ℝ} (hf : HRS.MemCb m f) (hj : j ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ HRS.cbNorm m f := by
  refine (le_ciSup (hf.2 j hj) x).trans ?_
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem ul3_memCb_of_cs (m : ℕ) {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    HRS.MemCb m χ := by
  refine ⟨hχ.of_le (by exact_mod_cast le_top), fun j hj => ?_⟩
  have h1 : Continuous (iteratedFDeriv ℝ j χ) := hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  exact (h1.norm).bddAbove_range_of_hasCompactSupport ((hc.iteratedFDeriv j).norm)

/-- the `C_b^m` norm of a cutoff composed with a linear map of norm at most `K` -/
theorem ul3_cb_comp (m : ℕ) {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (es : Euc d →L[ℝ] Euc d) {K : ℝ} (hK : 1 ≤ K) (hes : ‖es‖ ≤ K) :
    HRS.MemCb m (fun x => χ (es x)) ∧
      HRS.cbNorm m (fun x => χ (es x)) ≤ (m + 1) * K ^ m * HRS.cbNorm m χ := by
  have hcb := ul3_memCb_of_cs m hχ hc
  have hK0 : 0 ≤ K := by linarith
  have hpt : ∀ j ≤ m, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun x => χ (es x)) x‖ ≤
      K ^ m * HRS.cbNorm m χ := by
    intro j hj x
    have h1 := ContinuousLinearMap.iteratedFDeriv_comp_right es (hχ.of_le (by exact_mod_cast le_top) : ContDiff ℝ (j : WithTop ℕ∞) χ) x le_rfl
    have h2 : (fun x => χ (es x)) = χ ∘ es := rfl
    rw [h2, h1]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h3 : ∏ _i : Fin j, ‖es‖ ≤ K ^ j := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (norm_nonneg _) hes j
    have h4 := ul3_cb_apply hcb hj (es x)
    have h5 : K ^ j ≤ K ^ m := pow_le_pow_right₀ hK hj
    have h6 : 0 ≤ ‖iteratedFDeriv ℝ j χ (es x)‖ := norm_nonneg _
    calc ‖iteratedFDeriv ℝ j χ (es x)‖ * ∏ _i : Fin j, ‖es‖
        ≤ HRS.cbNorm m χ * K ^ j := mul_le_mul h4 h3 (by positivity) (h6.trans h4)
      _ ≤ HRS.cbNorm m χ * K ^ m := by gcongr; exact (h6.trans h4)
      _ = _ := by ring
  have hcb0 : 0 ≤ HRS.cbNorm m χ := (norm_nonneg _).trans (ul3_cb_apply hcb (Nat.zero_le _) 0)
  refine ⟨⟨(hχ.of_le (by exact_mod_cast le_top)).comp es.contDiff, fun j hj => ⟨K ^ m * HRS.cbNorm m χ, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact hpt j hj x
  · refine le_trans (le_of_eq (rfl : HRS.cbNorm m (fun x => χ (es x)) = ∑ j ∈ Finset.range (m + 1),
        ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => χ (es x)) z‖)) ?_
    calc ∑ j ∈ Finset.range (m + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (fun x => χ (es x)) z‖
        ≤ ∑ j ∈ Finset.range (m + 1), K ^ m * HRS.cbNorm m χ := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact ciSup_le fun x => hpt j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring


/-- the key lemma of `ul0_key` with the cutoff `a` entering only through its multiplier constant `C1` -/
theorem ul3_key (m : ℕ) (b : Euc d → ℝ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (Y : Finset (Euc d)) (R : ℝ) (hR : 0 < R)
    (hY : ∀ p : Euc d, ‖p‖ ≤ R → ∃ y ∈ Y, b (p - y) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Euc d → ℝ) (C1 : ℝ), 0 ≤ C1 →
      (∀ (z : Euc d) (u : Euc d → ℝ), sobolevNormE (m : ℝ) (fun x => a (x - z) * u x) ≤
        ENNReal.ofReal C1 * sobolevNormE (m : ℝ) u) →
      (∀ p : Euc d, a p ≠ 0 → ‖p‖ ≤ R) →
      ∀ (z : Euc d) (u : Euc d → ℝ), sobolevNormE (m : ℝ) (fun x => a (x - z) * u x) ≤
        ENNReal.ofReal (C1 * C) * ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => b (x - (z + y)) * u x) := by
  set Sg : Euc d → ℝ := fun p => ∑ y ∈ Y, b (p - y) ^ 2 with hSg
  have hS : ContDiff ℝ ∞ Sg :=
    ContDiff.sum fun y _ => (hb.comp (contDiff_id.sub contDiff_const)).pow 2
  have hge : ∀ p : Euc d, ‖p‖ ≤ R → 1 ≤ Sg p := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := hY p hp
    calc (1 : ℝ) = b (p - y) ^ 2 := by rw [hpy]; norm_num
      _ ≤ Sg p := Finset.single_le_sum (f := fun y => b (p - y) ^ 2)
          (fun y _ => sq_nonneg _) hy
  obtain ⟨ρ, hρ, hρc, hρ1⟩ := ul0_exists_inv Sg hS R hR hge
  obtain ⟨C2, hC2, h2⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) ρ hρ hρc
  obtain ⟨C3, hC3, h3⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) b hb hbc
  refine ⟨C2 * C3, by positivity, fun a C1 hC1 h1 hsup z u => ?_⟩
  have hpt : (fun x => a (x - z) * u x) =
      fun x => a (x - z) * (ρ (x - z) * ∑ y ∈ Y, (b (x - (z + y)) * (b (x - (z + y)) * u x))) := by
    funext x
    by_cases hx : a (x - z) = 0
    · simp [hx]
    · have hn : ‖x - z‖ ≤ R := hsup _ hx
      have := hρ1 (x - z) hn
      have e : ∑ y ∈ Y, (b (x - (z + y)) * (b (x - (z + y)) * u x)) = Sg (x - z) * u x := by
        rw [hSg]
        simp only
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [sub_sub]; ring
      rw [e, ← mul_assoc (ρ (x - z)), this, one_mul]
  rw [hpt]
  calc sobolevNormE (m : ℝ) (fun x => a (x - z) *
        (ρ (x - z) * ∑ y ∈ Y, (b (x - (z + y)) * (b (x - (z + y)) * u x))))
      ≤ ENNReal.ofReal C1 * sobolevNormE (m : ℝ)
          (fun x => ρ (x - z) * ∑ y ∈ Y, (b (x - (z + y)) * (b (x - (z + y)) * u x))) := h1 z _
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * sobolevNormE (m : ℝ)
          (fun x => ∑ y ∈ Y, (b (x - (z + y)) * (b (x - (z + y)) * u x)))) := by
        gcongr
        exact h2 z _
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * ∑ y ∈ Y, sobolevNormE (m : ℝ)
          (fun x => b (x - (z + y)) * (b (x - (z + y)) * u x))) := by
        gcongr
        exact HRS.MS.UlocCut.uc_sum_le (m : ℝ) Y (fun y x => b (x - (z + y)) * (b (x - (z + y)) * u x))
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * ∑ y ∈ Y, (ENNReal.ofReal C3 * sobolevNormE (m : ℝ)
          (fun x => b (x - (z + y)) * u x))) := by
        gcongr with y hy
        exact h3 (z + y) _
    _ = ENNReal.ofReal (C1 * (C2 * C3)) * ∑ y ∈ Y, sobolevNormE (m : ℝ)
          (fun x => b (x - (z + y)) * u x) := by
        rw [← Finset.mul_sum, ENNReal.ofReal_mul hC1, ENNReal.ofReal_mul hC2.le]
        ring


/-- **Uniform pullback** by linear equivalences with norm, inverse norm and determinant under control. -/
theorem ul3_comp_unif (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : Euc d ≃ₗ[ℝ] Euc d,
      ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ≤ K →
      ‖LinearMap.toContinuousLinearMap (e.symm : Euc d →ₗ[ℝ] Euc d)‖ ≤ K →
      K⁻¹ ≤ |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)| →
      ∀ h : Euc d → ℝ, ulocNormE m χ (fun x => h (e x)) ≤ ENNReal.ofReal C * ulocNormE m χ h := by
  have hK0 : 0 < K := by linarith
  set R0 : ℝ := 2 * K + 1 with hR0
  have hR0pos : 0 < R0 := by positivity
  obtain ⟨Y, hY⟩ := HRS.MS.UlocCut.uc_cover (fun y : Euc d => y)
    (fun p => ⟨p, by simpa using one_pos⟩) R0
  obtain ⟨C23, hC23, hkey⟩ := ul3_key m χ hχ.1 hχ.2.1 Y R0 hR0pos
    (fun p hp => by
      obtain ⟨y, hy, hpy⟩ := hY p hp
      exact ⟨y, hy, hχ.2.2.2.2 _ (by simpa using hpy.le)⟩)
  obtain ⟨CQ, hCQ, hQ⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  set Mχ : ℝ := HRS.cbNorm m χ with hMχ
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (ul3_cb_apply (ul3_memCb_of_cs m hχ.1 hχ.2.1) (Nat.zero_le _) 0)
  set C1 : ℝ := CQ * ((m + 1) * K ^ m * Mχ) with hC1
  have hC1pos : 0 ≤ C1 := by positivity
  set Kc : ℝ := Real.sqrt (K * (1 + K ^ 2) ^ m) with hKc
  have hKcpos : 0 < Kc := Real.sqrt_pos.2 (by positivity)
  refine ⟨Kc * (C1 * C23 * Y.card) + 1, by positivity, fun e he hes hdet h => ?_⟩
  set ec : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d) with hec
  set es : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (e.symm : Euc d →ₗ[ℝ] Euc d) with hes'
  set χe : Euc d → ℝ := fun w => χ (e.symm w) with hχe
  obtain ⟨hcbm, hcbn⟩ := ul3_cb_comp m hχ.1 hχ.2.1 es hK hes
  have hχes : ContDiff ℝ ∞ χe := hχ.1.comp es.contDiff
  have hχec : HasCompactSupport χe :=
    hχ.2.1.comp_homeomorph (e.symm.toContinuousLinearEquiv.toHomeomorph)
  have hsup : ∀ p : Euc d, χe p ≠ 0 → ‖p‖ ≤ R0 := by
    intro p hp
    have h1 : e.symm p ∈ tsupport χ := subset_tsupport _ hp
    have h2 : ‖e.symm p‖ < 2 := by simpa using hχ.2.2.1 h1
    have h3 : ‖p‖ ≤ ‖ec‖ * ‖e.symm p‖ := by
      have := ec.le_opNorm (e.symm p)
      rw [show ec (e.symm p) = p by simp [hec]] at this
      exact this
    have h4 : 0 ≤ ‖ec‖ := norm_nonneg _
    nlinarith
  have hmulC1 : ∀ (z : Euc d) (u : Euc d → ℝ), sobolevNormE (m : ℝ) (fun x => χe (x - z) * u x) ≤
      ENNReal.ofReal C1 * sobolevNormE (m : ℝ) u := by
    intro z u
    have e1 : (fun x => χe (x - z) * u x) = fun x => (fun y => χe y * u (y + z)) (x - z) := by
      ext x; simp
    rw [e1, HRS.MS.SobMul.sobolevNormE_translate (m : ℝ) (fun y => χe y * u (y + z)) z]
    refine (hQ χe hcbm _).trans ?_
    have h5 := HRS.MS.SobMul.sobolevNormE_translate (m : ℝ) u (-z)
    simp only [sub_neg_eq_add] at h5
    rw [h5]
    gcongr
    calc CQ * HRS.cbNorm m χe ≤ CQ * ((m + 1) * K ^ m * Mχ) := by gcongr; exact hcbn
      _ = C1 := rfl
  set Cfin : ℝ := C1 * C23 with hCfin
  have hkey' := hkey χe C1 hC1pos hmulC1 hsup
  refine iSup_le fun z0 => ?_
  set U : ℝ≥0∞ := ulocNormE m χ h with hU
  set v : Euc d → ℝ := fun w => χe (w - e z0) * h w with hv
  have hfun : (fun x => χ (x - z0) * h (e x)) = fun x => v (e x) := by
    funext x
    show χ (x - z0) * h (e x) = χ (e.symm (e x - e z0)) * h (e x)
    rw [← map_sub, LinearEquiv.symm_apply_apply]
  rw [hfun]
  have hbd := hkey' (e z0) h
  have hsum : ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => χ (x - (e z0 + y)) * h x) ≤ Y.card • U :=
    Finset.sum_le_card_nsmul _ _ _ fun y _ => le_iSup (fun z : Euc d =>
      sobolevNormE (m : ℝ) fun x => χ (x - z) * h x) (e z0 + y)
  have hv_le : sobolevNormE (m : ℝ) v ≤ ENNReal.ofReal Cfin * (Y.card • U) :=
    hbd.trans (by gcongr)
  have hKdet : ENNReal.ofReal (Real.sqrt (|LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ *
        (1 + ‖ec‖ ^ 2) ^ (m : ℝ))) ≤ ENNReal.ofReal Kc := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    have h1 : |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ ≤ K := by
      have := inv_anti₀ (inv_pos.2 hK0) hdet
      simpa using this
    have h2 : (1 + ‖ec‖ ^ 2) ^ (m : ℝ) ≤ (1 + K ^ 2) ^ m := by
      rw [Real.rpow_natCast]
      gcongr
    calc _ ≤ K * (1 + K ^ 2) ^ m := by
          apply mul_le_mul h1 h2 (by positivity) hK0.le
      _ = _ := rfl
  by_cases hvS : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) v
  swap
  · have hvt : sobolevNormE (m : ℝ) v = ⊤ := by unfold sobolevNormE; rw [if_neg hvS]
    by_cases hUtop : U = ⊤
    · rw [hUtop, ENNReal.mul_top (by simp; positivity)]; exact le_top
    · exfalso
      have hlt : ENNReal.ofReal Cfin * (Y.card • U) < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
          rw [nsmul_eq_mul]; exact ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.2 hUtop))
      exact (lt_top_iff_ne_top.1 (lt_of_le_of_lt hv_le hlt)) hvt
  · have hv1 : Integrable v volume := by
      refine ul0_integrable_of_support v hvS.1 (R0 + ‖e z0‖) fun w hw => ?_
      by_contra hne
      have : χe (w - e z0) ≠ 0 := fun h0 => hne (by simp [hv, h0])
      have := hsup _ this
      have h5 : ‖w‖ ≤ ‖w - e z0‖ + ‖e z0‖ := by simpa using norm_add_le (w - e z0) (e z0)
      linarith
    refine (ul3_sobE_comp (m : ℝ) (Nat.cast_nonneg m) e v hvS.1 hv1).trans ?_
    calc _ ≤ ENNReal.ofReal Kc * sobolevNormE (m : ℝ) v := by gcongr
      _ ≤ ENNReal.ofReal Kc * (ENNReal.ofReal Cfin * (Y.card • U)) := by gcongr
      _ = ENNReal.ofReal (Kc * (C1 * C23 * Y.card)) * U := by
          have e2 : ENNReal.ofReal (Kc * (C1 * C23 * Y.card)) =
              ENNReal.ofReal Kc * (ENNReal.ofReal C1 * ENNReal.ofReal C23 * Y.card) := by
            rw [ENNReal.ofReal_mul hKcpos.le, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul hC1pos, ENNReal.ofReal_natCast]
          rw [e2, hCfin, ENNReal.ofReal_mul hC1pos, nsmul_eq_mul]
          ring
      _ ≤ ENNReal.ofReal (Kc * (C1 * C23 * Y.card) + 1) * U := by
          gcongr
          linarith


/-- the OU flow `E_τ = e^{-τQ}`, `τ ∈ [0,T]`, with uniform control -/
theorem ul3_exp_unif (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ‖ouExp Q τ‖ ≤ K ∧ ‖ouExp Q (-τ)‖ ≤ K ∧
      K⁻¹ ≤ |LinearMap.det ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| := by
  obtain ⟨K1, hK1, hK⟩ := ul2_exp_bound Q T
  have hdetc : Continuous fun τ : ℝ =>
      |LinearMap.det ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| :=
    (ContinuousLinearMap.continuous_det.comp (ul2_exp_cont Q)).abs
  obtain ⟨K2, hK2⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn hdetc.continuousOn
  have hprod : ∀ τ : ℝ, LinearMap.det ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) *
      LinearMap.det ((ouExp Q (-τ) : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) = 1 := by
    intro τ
    rw [← LinearMap.det_comp]
    have : ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) ∘ₗ
        ((ouExp Q (-τ) : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      have := congrArg (fun A : Euc d →L[ℝ] Euc d => A x) (ul2_exp_mul_neg Q τ)
      exact this
    rw [this]; simp
  refine ⟨max K1 (max K2 1), le_max_of_le_left hK1, fun τ hτ => ⟨?_, ?_, ?_⟩⟩
  · exact (hK τ (by rw [abs_of_nonneg hτ.1]; exact hτ.2)).trans (le_max_left _ _)
  · exact (hK (-τ) (by rw [abs_neg, abs_of_nonneg hτ.1]; exact hτ.2)).trans (le_max_left _ _)
  · have h1 : |LinearMap.det ((ouExp Q (-τ) : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| ≤ K2 := by
      have := hK2 (-τ) ⟨by linarith [hτ.1, hτ.2], by linarith [hτ.1, hτ.2]⟩
      simpa using this
    have h2 := hprod τ
    have hpos : 0 < |LinearMap.det ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| := by
      apply abs_pos.2; intro h0; rw [h0, zero_mul] at h2; exact zero_ne_one h2
    have h3 : |LinearMap.det ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)|⁻¹ =
        |LinearMap.det ((ouExp Q (-τ) : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| := by
      rw [← abs_inv]; congr 1; exact inv_eq_of_mul_eq_one_right h2
    have : |LinearMap.det ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)|⁻¹ ≤ max K1 (max K2 1) :=
      by rw [h3]; exact h1.trans ((le_max_left _ _).trans (le_max_right _ _))
    rw [inv_le_comm₀ (lt_of_lt_of_le one_pos (le_max_of_le_left hK1)) hpos]
    exact this


/-- `e^{-τQ}` as a linear equivalence -/
theorem ul3_equiv_exp (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) :
    ∃ e : Euc d ≃ₗ[ℝ] Euc d, (∀ x, e x = ouExp Q τ x) ∧ (∀ x, e.symm x = ouExp Q (-τ) x) := by
  have h1 : ∀ x, ouExp Q (-τ) (ouExp Q τ x) = x := fun x => by
    have := congrArg (fun A : Euc d →L[ℝ] Euc d => A x) (ul2_exp_mul_neg Q (-τ))
    simpa using this
  have h2 : ∀ x, ouExp Q τ (ouExp Q (-τ) x) = x := fun x => by
    have := congrArg (fun A : Euc d →L[ℝ] Euc d => A x) (ul2_exp_mul_neg Q τ)
    exact this
  refine ⟨(ContinuousLinearEquiv.equivOfInverse (ouExp Q τ) (ouExp Q (-τ)) h1 h2).toLinearEquiv,
    fun x => rfl, fun x => rfl⟩

theorem ul3_toCLM_exp (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (e : Euc d ≃ₗ[ℝ] Euc d)
    (he : ∀ x, e x = ouExp Q τ x) :
    LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d) = ouExp Q τ :=
  ContinuousLinearMap.ext he

end HRS.MS.Ul

import HRS.Commutator.Whole.LOWVAux9
import HRS.Commutator.Whole.External
import HRS.Commutator.Whole.XNRSAux31

/-!
# CMX-LOWV auxiliary 10: the estimate for each `Λ ∈ (4,5)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole HRS.Commutator.Whole.SAMP2

variable {d : ℕ} {s : ℝ}

theorem lowv_perLam (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ σ : SMeas d, IsAdmissible σ → (s = 0 → σ.mass = 0) → ∀ Λ : ℝ, 4 < Λ → Λ < 5 →
        ENNReal.ofReal |Ccomm (gloForce s) (Pleq 1 v) σ| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (lowFreq Λ σ.fourier) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cn, hCn, hnrs⟩ := nrs_commutator hd hs0 hsd
  obtain ⟨Cv, hCv, hvlo⟩ := vlo_bound hd hs0 hsd
  obtain ⟨hFcd, hF0, hFodd, hFder⟩ := gloForce_props hd hs0 hsd
  obtain ⟨B, hBd⟩ := hFder 0
  have hB : ∀ x, ‖gloForce s x‖ ≤ B := fun x => by simpa using hBd x
  have hFc : Continuous (gloForce s : Euc d → Euc d) := hFcd.continuous
  have hFT : Function.HasTemperateGrowth (gloForce s : Euc d → Euc d) :=
    ⟨hFcd, fun n => by
      obtain ⟨Bn, hBn⟩ := hFder n
      exact ⟨0, Bn, fun x => by simpa using hBn x⟩⟩
  have hFt : ∀ i : Fin d, Function.HasTemperateGrowth (fun x : Euc d => gloForce s x i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasTemperateGrowth.comp hFT
  have hk1 : Integrable (fun x : Euc d => ‖x‖ * ‖ghiForce s x‖) :=
    memLp_one_iff_integrable.1 (kernel_remainder_Lp hd hs0 hsd).1
  have hghim : Measurable (ghiForce s : Euc d → Euc d) :=
    (cmxSA_kernGrad_measurable s).sub hFc.measurable
  set N1 : ℝ := ∫ x : Euc d, ‖x‖ * ‖ghiForce s x‖ with hN1
  have hN10 : 0 ≤ N1 := integral_nonneg fun x => by positivity
  set α := alphaE d s with hαdef
  have hα0 : 0 ≤ α := by
    rw [hαdef]; unfold alphaE
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨Cn * Cv + Cv * N1 * (20 * Real.pi) ^ (2 * α) + 1, by positivity, ?_⟩
  intro v K hv σ hσ hmass Λ hΛ4 hΛ5
  have hΛ0 : 0 < Λ := by linarith
  have hVsub : SubTransport d s (Pleq 1 v) (Cv * K) := hvlo v K hv
  obtain ⟨Lv, Fv, hFv0, hLip, hw, hsum⟩ := hVsub
  have hLv0 : (0 : ℝ) ≤ Lv := Lv.coe_nonneg
  have hCvK : 0 ≤ Cv * K := by
    have : (0 : ℝ) ≤ Lv + Fv := by positivity
    linarith
  have hK0 : 0 ≤ K := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg hCv h
    linarith
  have hLvK : (Lv : ℝ) ≤ Cv * K := by linarith
  have hVc : Continuous (Pleq 1 v : Euc d → Euc d) := hLip.continuous
  have hV : ∀ x y, ‖Pleq 1 v x - Pleq 1 v y‖ ≤ Lv * ‖x - y‖ := fun x y => by
    simpa [dist_eq_norm] using hLip.dist_le_mul x y
  -- Fourier support of the components of `V = P_{≤1} v`
  obtain ⟨Lv0, Fv0, -, hLipv, -, -⟩ := hv
  have hvc : Continuous v := hLipv.continuous
  have hvg : ∀ x, ‖v x‖ ≤ (‖v 0‖ + Lv0) * (1 + ‖x‖) := by
    intro x
    have h1 : ‖v x‖ ≤ ‖v 0‖ + Lv0 * ‖x‖ := by
      have := hLipv.dist_le_mul x 0
      simp only [dist_eq_norm, sub_zero] at this
      calc ‖v x‖ = ‖(v x - v 0) + v 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖v x - v 0‖ + ‖v 0‖ := norm_add_le _ _
        _ ≤ Lv0 * ‖x‖ + ‖v 0‖ := by gcongr
        _ = ‖v 0‖ + Lv0 * ‖x‖ := by ring
    have : (0 : ℝ) ≤ Lv0 := Lv0.coe_nonneg
    nlinarith [norm_nonneg (v 0), norm_nonneg x, mul_nonneg this (norm_nonneg x)]
  have hVi : ∀ i : Fin d, FourierSuppIn 2 (fun x => Pleq 1 v x i) := by
    intro i
    have hf : ∀ x, |v x i| ≤ (‖v 0‖ + Lv0) * (1 + ‖x‖) := fun x =>
      (by simpa using PiLp.norm_apply_le (v x) i : |v x i| ≤ ‖v x‖).trans (hvg x)
    have hm : Measurable fun z => v z i :=
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hvc).measurable
    have h := Pleq_fourierSupp (d := d) hd1 1 one_pos (fun z => v z i) _ hf hm
    have e : (fun x => Pleq 1 v x i) = Pleq 1 (fun z => v z i) :=
      funext fun x => lowv_Pleq_comp one_pos hvc hvg x i
    rw [e]
    simpa using h
  -- the low-frequency part
  obtain ⟨a, φ, ha, hφa, hφF, hac, hai, ⟨M, hM⟩, ha2, hmass'⟩ := lowv_a_props hΛ0 σ hσ
  obtain ⟨hmp, hmn⟩ := moments_admissible σ hσ 1
  simp only [pow_one] at hmp hmn
  have hEq : Ccomm (gloForce s) (Pleq 1 v) σ = CcommFun (gloForce s) (Pleq 1 v) a :=
    lowv_Ccomm_eq (by linarith : (4 : ℝ) < Λ) hFodd hFc hB hVc hV hLv0 hVi
      (lowv_gloForce_fsupp hd hs0 hsd) hFt σ hσ.1 hmp hmn a hac hai ha
  obtain ⟨ha1, -⟩ := lowv_a_int_aux hac hai
  have hglo := lowv_glo_piece hFc hB hVc hV hLv0 hac hai
  obtain ⟨hghi, hghib⟩ := lowv_ghi_piece hghim hVc hV hLv0 hk1 hac hM ha1 ha2
  have hsplit := lowv_Ccomm_split hglo hghi
  have hG : (fun z : Euc d => gloForce s z + ghiForce s z) = kernGrad s := by
    funext z; simp [ghiForce]
  rw [hG] at hsplit
  -- NRS
  have hmass2 : s = 0 → ∫ x, a x = 0 := fun h0 => by rw [hmass', hmass h0]
  have hN := hnrs (Pleq 1 v) (Cv * K) ⟨Lv, Fv, hFv0, hLip, hw, hsum⟩ a ⟨φ, hφa⟩ hmass2
  -- the weighted norm
  have hFL : homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) =
      homSqE (-alphaE d s) (lowFreq Λ σ.fourier) := by
    unfold homSqE
    refine lintegral_congr_ae ?_
    filter_upwards [HRS.Commutator.Whole.XNRS.xfourierL2_eq hφa] with ξ hξ
    rw [hξ]
    have : (𝓕 φ : SchwartzMap (Euc d) ℂ) ξ = 𝓕 (⇑φ) ξ := by rw [SchwartzMap.fourier_coe]
    rw [this, hφF]
    rfl
  rw [hFL] at hN
  -- the `L²` norm
  have hsupp : ∀ ξ : Euc d, 2 * Λ ≤ ‖ξ‖ → 𝓕 (⇑φ) ξ = 0 := by
    intro ξ hξ
    rw [hφF]
    have : chi (Λ⁻¹ • ξ) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hΛ0.le, inv_mul_eq_div, le_div_iff₀ hΛ0]
      linarith
    simp [cmxFB_gL, this]
  have hAle := lowv_L2_le hd1 hΛ0 hα0 φ hsupp
  have hAeq : ∫ x, ‖φ x‖ ^ 2 = ∫ x, a x ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hφa x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hAeq] at hAle
  have hH : (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * (-α))) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2) =
      homSqE (-alphaE d s) (lowFreq Λ σ.fourier) := by
    unfold homSqE
    refine lintegral_congr fun ξ => ?_
    rw [hφF]
    rfl
  rw [hH] at hAle
  set H := homSqE (-alphaE d s) (lowFreq Λ σ.fourier) with hHdef
  -- assemble
  have hpow : (4 * Real.pi * Λ) ^ (2 * α) ≤ (20 * Real.pi) ^ (2 * α) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    nlinarith [Real.pi_pos]
  have hT2 : ENNReal.ofReal |CcommFun (ghiForce s) (Pleq 1 v) a| ≤
      ENNReal.ofReal (Cv * K * N1 * (20 * Real.pi) ^ (2 * α)) * H := by
    calc ENNReal.ofReal |CcommFun (ghiForce s) (Pleq 1 v) a|
        ≤ ENNReal.ofReal (Lv * N1 * ∫ x, a x ^ 2) := ENNReal.ofReal_le_ofReal hghib
      _ = ENNReal.ofReal (Lv * N1) * ENNReal.ofReal (∫ x, a x ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (Lv * N1) * (ENNReal.ofReal ((4 * Real.pi * Λ) ^ (2 * α)) * H) := by
          gcongr
      _ = ENNReal.ofReal (Lv * N1 * (4 * Real.pi * Λ) ^ (2 * α)) * H := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cv * K * N1 * (20 * Real.pi) ^ (2 * α)) * H := by
          gcongr
  have hT1 := hN
  have hle : |CcommFun (gloForce s) (Pleq 1 v) a| ≤
      |CcommFun (kernGrad s) (Pleq 1 v) a| + |CcommFun (ghiForce s) (Pleq 1 v) a| := by
    have : CcommFun (gloForce s) (Pleq 1 v) a =
        CcommFun (kernGrad s) (Pleq 1 v) a - CcommFun (ghiForce s) (Pleq 1 v) a := by
      linarith
    rw [this]
    exact abs_sub _ _
  rw [hEq]
  calc ENNReal.ofReal |CcommFun (gloForce s) (Pleq 1 v) a|
      ≤ ENNReal.ofReal (|CcommFun (kernGrad s) (Pleq 1 v) a| +
          |CcommFun (ghiForce s) (Pleq 1 v) a|) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal |CcommFun (kernGrad s) (Pleq 1 v) a| +
          ENNReal.ofReal |CcommFun (ghiForce s) (Pleq 1 v) a| := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (Cn * (Cv * K)) * H +
          ENNReal.ofReal (Cv * K * N1 * (20 * Real.pi) ^ (2 * α)) * H := add_le_add hT1 hT2
    _ = ENNReal.ofReal (Cn * (Cv * K) + Cv * K * N1 * (20 * Real.pi) ^ (2 * α)) * H := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((Cn * Cv + Cv * N1 * (20 * Real.pi) ^ (2 * α) + 1) * K) * H := by
        gcongr
        nlinarith [mul_nonneg hK0 hK0, hK0, mul_nonneg hCv.le hK0,
          mul_nonneg (mul_nonneg hCv.le hN10) (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 20 * Real.pi) (2 * α))]

end HRS.Commutator.Whole

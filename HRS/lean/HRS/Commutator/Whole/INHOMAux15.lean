import HRS.Commutator.Whole.INHOMAux14
import HRS.Commutator.Whole.ProductEstimate

/-!
# CMX-INHOM auxiliary 15: the product term `𝒞_{g_{≤1}}(v_{>1}, a₁)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_lintegral_sq_lt_top (ψ : SchwartzMap (Euc d) ℂ) : ∫⁻ x, ‖ψ x‖ₑ ^ 2 < ⊤ := by
  have hi : Integrable (fun x => ‖ψ x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm ψ.continuous.aestronglyMeasurable).1 (ψ.memLp 2)
  have e : ∀ x, ‖ψ x‖ₑ ^ 2 = ENNReal.ofReal (‖ψ x‖ ^ 2) := by
    intro x; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [e]
  exact hi.lintegral_lt_top

lemma inhom_Sob_lt_top {t : ℝ} (ht : t ≤ 0) (φ : SchwartzMap (Euc d) ℂ) : inhom_Sob t φ < ⊤ := by
  have h1 : inhom_Sob t φ ≤ ∫⁻ ξ, ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
    unfold inhom_Sob
    refine lintegral_mono fun ξ => ?_
    have : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (Real.pi * ‖ξ‖)]) ht
    calc ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2
        ≤ 1 * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
          gcongr
          exact ENNReal.ofReal_le_one.2 this
      _ = _ := one_mul _
  rw [← inhom_plancherel] at h1
  exact lt_of_le_of_lt h1 (inhom_lintegral_sq_lt_top φ)

/-- `√X · √X = X` in `ℝ≥0∞`. -/
lemma inhom_sqrt_mul_sqrt (X : ℝ≥0∞) : X ^ ((1 : ℝ) / 2) * X ^ ((1 : ℝ) / 2) = X := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

theorem inhom_T_prod (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ ψ : SchwartzMap (Euc d) ℂ) (b : Euc d → ℝ), (∀ x, ψ x = ((b x : ℝ) : ℂ)) →
        (∀ ξ, 𝓕 (⇑ψ) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) →
        ENNReal.ofReal |CcommFun (gloForce s) (Pgt 1 v) b| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  obtain ⟨Cp, hCp, hprod⟩ := product_estimate_aesm hd hs0 hsd
  obtain ⟨Cps, hCps, hps⟩ := potentialSobolev hd hs0 hsd
  obtain ⟨Cb, hCb, hbd⟩ := vhi_bounded (d := d) hd
  obtain ⟨hFcd, hF0, hFodd, hFder⟩ := gloForce_props hd hs0 hsd
  obtain ⟨B, hBd⟩ := hFder 0
  have hB : ∀ x, ‖gloForce s x‖ ≤ B := fun x => by simpa using hBd x
  have hα : 0 < alphaE d s := by
    unfold alphaE; have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set c1 : ℝ := (1 + 64 / Real.pi ^ 2) ^ alphaE d s with hc1
  have hc10 : 0 < c1 := by positivity
  refine ⟨2 * Cp * Cps * c1 ^ ((1 : ℝ) / 2) + 1, by positivity, fun v K hv φ ψ b hψ hF => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨hac, hai, hM, ha1, ha2⟩ := inhom_schw_props hψ
  obtain ⟨L, F, hF0', hL, ⟨w, hrep, hw⟩, hK⟩ := hv
  have hfd : HasFracData d s v L w F := ⟨hL, hrep, hw⟩
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  obtain ⟨hVc, -, hVb⟩ := hbd v L hL
  have hglom : Measurable (gloForce s : Euc d → Euc d) := hFcd.continuous.measurable
  have hVg : ∀ x, ‖Pgt 1 v x‖ ≤ (Cb * L) * (1 + ‖x‖) := fun x =>
    (hVb x).trans (by nlinarith [norm_nonneg x, mul_nonneg hCb.le hL0])
  have hpair := inhom_pairing_bdd hglom hFodd hB hVc hVg hac hai
  set u : Euc d → Euc d := inhom_conv (gloForce s) b with hu
  have hint : ∀ x : Euc d, Integrable (fun y => b y • gloForce s (x - y)) volume := by
    intro x
    refine (ha1.norm.const_mul B).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (hac.measurable.smul (hglom.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · rw [norm_smul]
      calc ‖b y‖ * ‖gloForce s (x - y)‖ ≤ ‖b y‖ * B := mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
        _ = B * ‖b y‖ := by ring
  have hucont : Continuous u := inhom_conv_continuous hFcd.continuous hB ha1
  have hsupp : ∀ i, FourierSuppIn 2 (fun x => u x i) := by
    intro i
    have hfun : (fun x => u x i) = fun x => ∫ y, b y * gloForce s (x - y) i := by
      funext x; exact inhom_conv_comp x i (hint x)
    rw [hfun]
    refine inhom_fs_conv (lowv_gloForce_fsupp hd hs0 hsd i)
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hFcd.continuous) (B := B) ?_ hac ha1
    intro x
    exact (by simpa using PiLp.norm_apply_le (gloForce s x) i : |gloForce s x i| ≤ ‖gloForce s x‖).trans (hB x)
  -- potential Sobolev
  have hadm := inhom_ofDensity_admissible hψ
  have hmass : s = 0 → (SMeas.ofDensity b).mass = 0 := fun _ => by
    rw [inhom_ofDensity_mass hac.measurable ha1]; exact inhom_mass_zero hψ hF
  have hconv : ∀ x, (SMeas.ofDensity b).convForce (gloForce s) x = u x := by
    intro x
    unfold SMeas.convForce
    exact inhom_ofDensity_intV hac.measurable (hint x)
  have hpsb := hps (SMeas.ofDensity b) hadm hmass
  have hN2 : homSqE (-alphaE d s) (lowFreq 4 (SMeas.ofDensity b).fourier) ≤
      ENNReal.ofReal c1 * inhom_Sob (-alphaE d s) φ := by
    refine inhom_hom_le hα _ (fun ξ => ?_)
    refine (inhom_lowFreq_norm_le _ ξ).trans ?_
    rw [inhom_ofDensity_fourier hac.measurable ha1 ξ]
    have : (fun x : Euc d => ((b x : ℝ) : ℂ)) = ⇑ψ := by funext x; rw [hψ x]
    rw [this, hF ξ, norm_mul]
  set S := inhom_Sob (-alphaE d s) φ with hS
  have hStop : S < ⊤ := inhom_Sob_lt_top (by linarith) φ
  have hunorm : eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume ≤
      ENNReal.ofReal Cps * (ENNReal.ofReal (c1 ^ ((1 : ℝ) / 2)) * S ^ ((1 : ℝ) / 2)) := by
    have h1 : eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume ≤
        ENNReal.ofReal Cps * homSqE (-alphaE d s) (lowFreq 4 (SMeas.ofDensity b).fourier) ^ ((1 : ℝ) / 2) := by
      have e : (fun x => ‖(SMeas.ofDensity b).convForce (gloForce s) x‖) = fun x => ‖u x‖ := by
        funext x; rw [hconv x]
      rw [e] at hpsb
      exact hpsb
    refine h1.trans ?_
    gcongr
    calc homSqE (-alphaE d s) (lowFreq 4 (SMeas.ofDensity b).fourier) ^ ((1 : ℝ) / 2)
        ≤ (ENNReal.ofReal c1 * S) ^ ((1 : ℝ) / 2) := by gcongr
      _ = ENNReal.ofReal (c1 ^ ((1 : ℝ) / 2)) * S ^ ((1 : ℝ) / 2) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg hc10.le (by norm_num)]
  have hSq : S ^ ((1 : ℝ) / 2) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hStop.ne
  have hmemu : MemLp (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume := by
    rw [memLp_iff]
    refine lt_of_le_of_lt hunorm ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSq)
  obtain ⟨hg2, hgb⟩ := hprod v L w F hfd u hucont.aestronglyMeasurable hmemu hsupp
  have hb2 : MemLp b 2 volume := (memLp_two_iff_integrable_sq hac.aestronglyMeasurable).2 ha2
  have hcs := inhom_pairing_le hb2 hg2 (-alphaE d s)
  rw [neg_neg] at hcs
  have hSb : sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 b) ≤ S := by
    rw [inhom_sobSqE_eq hψ]; exact inhom_sob_le _ hF
  -- assemble
  have hpair' : CcommFun (gloForce s) (Pgt 1 v) b =
      2 * ∫ x, b x * inner ℝ (Pgt 1 v x) (u x) := hpair
  rw [hpair', abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_mul (by norm_num)]
  have hF' : ENNReal.ofReal F ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (by
    have : (0 : ℝ) ≤ L := hL0
    linarith)
  calc ENNReal.ofReal 2 * ENNReal.ofReal |∫ x, b x * inner ℝ (Pgt 1 v x) (u x)|
      ≤ ENNReal.ofReal 2 * (sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 b) ^ ((1 : ℝ) / 2) *
          sobSqE (alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 fun x => inner ℝ (Pgt 1 v x) (u x)) ^ ((1 : ℝ) / 2)) := by
        gcongr
    _ ≤ ENNReal.ofReal 2 * (S ^ ((1 : ℝ) / 2) * (ENNReal.ofReal (Cp * F) *
          eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume)) := by
        gcongr
    _ ≤ ENNReal.ofReal 2 * (S ^ ((1 : ℝ) / 2) * (ENNReal.ofReal (Cp * F) *
          (ENNReal.ofReal Cps * (ENNReal.ofReal (c1 ^ ((1 : ℝ) / 2)) * S ^ ((1 : ℝ) / 2))))) := by
        gcongr
    _ = ENNReal.ofReal (2 * Cp * Cps * c1 ^ ((1 : ℝ) / 2)) * ENNReal.ofReal F * S := by
        have e1 : ENNReal.ofReal (Cp * F) = ENNReal.ofReal Cp * ENNReal.ofReal F :=
          ENNReal.ofReal_mul hCp.le
        have e2 : ENNReal.ofReal (2 * Cp * Cps * c1 ^ ((1 : ℝ) / 2)) = ENNReal.ofReal 2 *
            ENNReal.ofReal Cp * ENNReal.ofReal Cps * ENNReal.ofReal (c1 ^ ((1 : ℝ) / 2)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
        have hS2 := inhom_sqrt_mul_sqrt S
        rw [e1, e2]
        generalize S ^ ((1 : ℝ) / 2) = X at hS2 ⊢
        rw [← hS2]
        ring
    _ ≤ ENNReal.ofReal (2 * Cp * Cps * c1 ^ ((1 : ℝ) / 2)) * ENNReal.ofReal K * S := by gcongr
    _ ≤ ENNReal.ofReal ((2 * Cp * Cps * c1 ^ ((1 : ℝ) / 2) + 1) * K) * S := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        gcongr
        nlinarith

end HRS.Commutator.Whole

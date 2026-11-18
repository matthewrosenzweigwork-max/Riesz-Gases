import HRS.Commutator.Whole.LocalAuxSAMP2Reg
import HRS.Commutator.Whole.LocalAuxSAMP2Cube

/-!
# CMX-SAMP (`potentialSobolev`), part 5: the limit `ε → 0`, Fatou, and the componentwise bound
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.SAMP2

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma norm_sfourier_le (σ : SMeas d) (hf : σ.IsFinite) (ξ : Euc d) :
    ‖σ.fourier ξ‖ ≤ σ.pos.real Set.univ + σ.neg.real Set.univ := by
  obtain ⟨hp, hn⟩ := hf
  haveI := hp
  haveI := hn
  have h : σ.fourier ξ = fm σ.pos ξ - fm σ.neg ξ := rfl
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (norm_fm_le _ ξ) (norm_fm_le _ ξ))

lemma Msym_sfourier_integrable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : ℂ)
    (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (hf : σ.IsFinite) (i : Fin d) :
    Integrable (fun ξ => Msym d s c i ξ * σ.fourier ξ) := by
  have hM := Msym_integrable hd hs0 hsd c i
  refine (hM.norm.mul_const (σ.pos.real Set.univ + σ.neg.real Set.univ)).mono'
    (hM.1.mul hσ.continuous.aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_sfourier_le σ hf ξ) (norm_nonneg _)

lemma gL_eventually_zero {ξ : Euc d} (hξ : ξ ≠ 0) :
    ∀ᶠ n : ℕ in atTop, cmxFB_gL d (1 / ((n : ℝ) + 1)) ξ = 0 := by
  have hxn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ‖ξ‖ / 2 := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [this] with n hn
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have : 2 ≤ ‖(1 / ((n : ℝ) + 1))⁻¹ • ξ‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  unfold cmxFB_gL
  rw [cmxFB_chi_zero this]
  simp

lemma integrable_exp_mul {g : Euc d → ℂ} (hg : Integrable g) (x : Euc d) :
    Integrable (fun ξ => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * g ξ) := by
  have h1 : Continuous fun ξ : Euc d =>
      Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) := by fun_prop
  exact hg.bdd_mul (c := 1) h1.aestronglyMeasurable
    (Eventually.of_forall fun ξ => by rw [Complex.norm_exp_ofReal_mul_I])

lemma gL_norm_le_one (ε : ℝ) (ξ : Euc d) : ‖cmxFB_gL d ε ξ‖ ≤ 1 := by
  unfold cmxFB_gL
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cmxFB_chi_nonneg _)]
  exact cmxFB_chi_le_one _

lemma fReg_tendsto (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : ℂ) (σ : SMeas d)
    (hσ : ContDiff ℝ ∞ σ.fourier) (hf : σ.IsFinite) (i : Fin d) (x : Euc d) :
    Tendsto (fun n : ℕ => fReg (s := s) c σ hσ i
        (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity) x) atTop
      (𝓝 (𝓕⁻ (fun ξ => Msym d s c i ξ * σ.fourier ξ) x)) := by
  have hint := Msym_sfourier_integrable hd hs0 hsd c σ hσ hf i
  set η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hη
  have hηpos : ∀ n, 0 < η n := fun n => by simp only [hη]; positivity
  have hGint : ∀ n, Integrable (Gfun d s c σ i (η n)) := by
    intro n
    have hc : Continuous fun ξ : Euc d => (1 : ℂ) - cmxFB_gL d (η n) ξ :=
      continuous_const.sub (cmxFB_gL_contDiff (η n)).continuous
    refine hint.bdd_mul (c := 1) hc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    exact gL_norm_le (η n) ξ
  have hdiff : ∀ n, 𝓕⁻ (fun ξ => Msym d s c i ξ * σ.fourier ξ) x -
      fReg (s := s) c σ hσ i (hηpos n) x =
      ∫ ξ, Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        (cmxFB_gL d (η n) ξ * (Msym d s c i ξ * σ.fourier ξ)) := by
    intro n
    rw [fReg_apply, Real.fourierInv_eq', Real.fourierInv_eq']
    simp only [smul_eq_mul]
    rw [← integral_sub (integrable_exp_mul hint x) (integrable_exp_mul (hGint n) x)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Gfun]
    ring
  have hlim : Tendsto (fun n => ∫ ξ, Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
      Complex.I) * (cmxFB_gL d (η n) ξ * (Msym d s c i ξ * σ.fourier ξ))) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (F := fun n ξ => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        (cmxFB_gL d (η n) ξ * (Msym d s c i ξ * σ.fourier ξ)))
      (f := fun _ => (0 : ℂ)) (fun ξ => ‖Msym d s c i ξ * σ.fourier ξ‖) (fun n => ?_) hint.norm
      (fun n => ?_) ?_
    · simpa using this
    · have h1 : Continuous fun ξ : Euc d =>
          Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) := by fun_prop
      exact h1.aestronglyMeasurable.mul (((cmxFB_gL_contDiff (η n)).continuous.aestronglyMeasurable).mul
        hint.1)
    · refine Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (gL_norm_le_one _ ξ)
    · filter_upwards [ae_ne_zero_euc (d := d) (by omega)] with ξ hξ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [gL_eventually_zero hξ] with n hn
      simp [show cmxFB_gL d (η n) ξ = 0 from hn]
  have := (tendsto_const_nhds (x := 𝓕⁻ (fun ξ => Msym d s c i ξ * σ.fourier ξ) x)).sub hlim
  simp only [sub_zero] at this
  refine this.congr fun n => ?_
  rw [← hdiff n]
  ring

lemma component_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {c : ℂ}
    (hc : ∀ (i : Fin d) (Φ : SchwartzMap (Euc d) ℂ),
      ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
        c * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ)
    {C_H : ℝ} {q : ℝ≥0∞}
    (hC : ∀ φ : SchwartzMap (Euc d) ℂ, eLpNorm (⇑φ) q volume ≤
      ENNReal.ofReal C_H * eLpNorm (cmxHLS_frac (alphaE d s - 1) φ) 2 volume)
    (σ : SMeas d) (hadm : IsAdmissible σ) (i : Fin d) :
    AEStronglyMeasurable (fun x => ((σ.convForce (gloForce s) x i : ℝ) : ℂ)) volume ∧
    eLpNorm (fun x => ((σ.convForce (gloForce s) x i : ℝ) : ℂ)) q volume ≤
      ENNReal.ofReal C_H *
        (ENNReal.ofReal ((‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2) *
          homSqE (-alphaE d s) (lowFreq 4 σ.fourier)) ^ (1 / (2 : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hσ := contDiff_sfourier σ hadm
  have hf := hadm.1
  have hηpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hlim : ∀ x : Euc d, Tendsto (fun n : ℕ => (fReg (s := s) c σ hσ i (hηpos n)) x) atTop
      (𝓝 (((σ.convForce (gloForce s) x i : ℝ) : ℂ))) := by
    intro x
    rw [conv_component hd hs0 hsd hc σ hf x i]
    exact fReg_tendsto hd hs0 hsd c σ hσ hf i x
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (⇑(fReg (s := s) c σ hσ i (hηpos n))) volume :=
    fun n => (fReg (s := s) c σ hσ i (hηpos n)).continuous.aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun x => ((σ.convForce (gloForce s) x i : ℝ) : ℂ)) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas (Eventually.of_forall hlim)
  refine ⟨hg, ?_⟩
  exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun n =>
    reg_norm_bound hd1 hC c σ hσ i (hηpos n)) hmeas hg (Eventually.of_forall hlim)

lemma hls_exponents (hd : 3 ≤ d) (hsd : s < (d : ℝ) - 2) (hs0 : 0 ≤ s) :
    (2 : ℝ≥0∞) < ENNReal.ofReal (p2E d s) ∧ 0 < alphaE d s - 1 ∧
      (ENNReal.ofReal (p2E d s))⁻¹ = (2 : ℝ≥0∞)⁻¹ - ENNReal.ofReal ((alphaE d s - 1) / d) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hp2 : 2 < p2E d s := by
    unfold p2E
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hα : 0 < alphaE d s - 1 := by unfold alphaE; linarith
  refine ⟨?_, hα, ?_⟩
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp2
  · rw [← ENNReal.ofReal_inv_of_pos (by linarith), show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    unfold p2E alphaE
    field_simp
    ring

theorem potential_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : SMeas d, IsAdmissible σ →
      eLpNorm (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume ≤
        ENNReal.ofReal C * (homSqE (-alphaE d s) (lowFreq 4 σ.fourier)) ^ ((1 : ℝ) / 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc⟩ := kernGrad_fourier_full hd hs0 hsd (s := s)
  obtain ⟨hq2, hα, hrel⟩ := hls_exponents hd hsd hs0
  obtain ⟨C_H, hCH, hHLS⟩ := cmxHLS_main hd1 (alphaE d s - 1) 2 (ENNReal.ofReal (p2E d s))
    (by norm_num) hq2 ENNReal.ofReal_lt_top hα hrel
  set X : ℝ := ‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1) with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨d * C_H * X + 1, by positivity, fun σ hadm => ?_⟩
  set q : ℝ≥0∞ := ENNReal.ofReal (p2E d s) with hq
  set h : ℝ≥0∞ := homSqE (-alphaE d s) (lowFreq 4 σ.fourier) with hh
  have hcomp := fun i => component_bound hd hs0 hsd hc hHLS σ hadm i
  have hP1 : 1 ≤ q := (ENNReal.one_lt_two.trans hq2).le
  -- measurability of the vector function
  set f : Euc d → Euc d := fun x => σ.convForce (gloForce s) x with hf
  have hfi : ∀ i, AEStronglyMeasurable (fun x => f x i) volume := fun i =>
    Complex.continuous_re.comp_aestronglyMeasurable (hcomp i).1
  have hfnorm : AEStronglyMeasurable (fun x => ‖f x‖) volume := by
    have : AEMeasurable f volume := by
      have e : f = fun x => (WithLp.toLp 2 (fun i => f x i) : Euc d) := by
        funext x; simp
      rw [e]
      exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
        (AEMeasurable.of_eval fun i => (hfi i).aemeasurable)
    exact this.aestronglyMeasurable.norm
  have hcb : ∀ i, eLpNorm (fun x => f x i) q volume ≤
      ENNReal.ofReal C_H * (ENNReal.ofReal (X ^ 2) * h) ^ (1 / (2 : ℝ)) := by
    intro i
    have h1 := (hcomp i).2
    have hnorm : eLpNorm (fun x => ((f x i : ℝ) : ℂ)) q volume = eLpNorm (fun x => f x i) q volume :=
      eLpNorm_congr_norm_ae (p := q) (hcomp i).1 (hfi i)
        (Eventually.of_forall fun x => by simp)
    rw [← hnorm]
    exact h1
  have hsum : eLpNorm (fun x => ‖f x‖) q volume ≤
      ∑ i : Fin d, eLpNorm (fun x => f x i) q volume := by
    calc eLpNorm (fun x => ‖f x‖) q volume
        ≤ eLpNorm (fun x => ∑ i : Fin d, ‖f x i‖) q volume := by
          refine eLpNorm_mono_real hfnorm fun x => ?_
          rw [norm_norm]
          refine (norm_le_sum_abs (f x)).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs]
      _ = eLpNorm (∑ i : Fin d, fun x => ‖f x i‖) q volume := by
          congr 1
          funext x
          simp [Finset.sum_apply]
      _ ≤ ∑ i : Fin d, eLpNorm (fun x => ‖f x i‖) q volume := eLpNorm_sum_le hP1
      _ = ∑ i : Fin d, eLpNorm (fun x => f x i) q volume :=
          Finset.sum_congr rfl fun i _ => eLpNorm_norm _ (hfi i)
  have hroot : ENNReal.ofReal C_H * (ENNReal.ofReal (X ^ 2) * h) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (C_H * X) * h ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by norm_num)]
    have : (X ^ 2) ^ (1 / (2 : ℝ)) = X := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hX0]
    rw [this, ← mul_assoc, ← ENNReal.ofReal_mul hCH.le]
  calc eLpNorm (fun x => ‖f x‖) q volume
      ≤ ∑ i : Fin d, eLpNorm (fun x => f x i) q volume := hsum
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal (C_H * X) * h ^ ((1 : ℝ) / 2) :=
        Finset.sum_le_sum fun i _ => (hcb i).trans (le_of_eq hroot)
    _ = (d : ℝ≥0∞) * (ENNReal.ofReal (C_H * X) * h ^ ((1 : ℝ) / 2)) := by simp
    _ ≤ ENNReal.ofReal (d * C_H * X + 1) * h ^ ((1 : ℝ) / 2) := by
        rw [← mul_assoc]
        gcongr
        rw [show (d : ℝ≥0∞) = ENNReal.ofReal d by simp, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)

end HRS.Commutator.Whole.SAMP2

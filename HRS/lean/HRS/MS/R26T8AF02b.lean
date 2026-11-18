import HRS.MS.R26T8AF02a
import HRS.MS.R26T8AF04
import HRS.MH.ScreenedS4Aux1
import HRS.MH.ScreenedS5a
import HRS.MH.CoercTestW1

/-!
# S8.2 observed-time layer, packet T8A.F02b: Sobolev bound of the critical convolution

`T_i h = forceConv i h` has `L²` Fourier transform `M = c 2π ξ_i |ξ|^{-d/2} i ĥ`, `|M|² ≤ C |ξ|^{2-d} |ĥ|²`; hence
`‖T_i h‖_{H^r} ≤ C (‖h‖_{H^r} + ‖h‖_{L¹})` (low frequencies by `|ĥ| ≤ ‖h‖₁` and local integrability of `|ξ|^{2-d}`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- the symbol times the transform of the datum -/
def r26t8a_f02b_M (c : ℝ) (i : Fin d) (h : SchwartzMap (Euc d) ℝ) (ξ : Euc d) : ℂ :=
  ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (-criticalS d) : ℝ) : ℂ) * Complex.I *
    𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ

theorem r26t8a_f02b_M_sq (c : ℝ) (hc : 0 < c) (i : Fin d) (h : SchwartzMap (Euc d) ℝ) {ξ : Euc d}
    (hξ : ξ ≠ 0) :
    ‖r26t8a_f02b_M c i h ξ‖ ^ 2 ≤
      (c * (2 * Real.pi)) ^ 2 * ‖ξ‖ ^ (2 - (d : ℝ)) *
        ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2 := by
  have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold r26t8a_f02b_M
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  have h1 : |ξ i| ≤ ‖ξ‖ := HRS.MS.UniqN0.n0_coord_le ξ i
  have h2 : ‖ξ‖ ^ (-criticalS d) * ‖ξ‖ = ‖ξ‖ ^ (1 - criticalS d) := by
    rw [← Real.rpow_add_one hp.ne']; congr 1; ring
  set N : ℝ := ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ with hN
  have h3 : |c| * |2 * Real.pi * ξ i| * ‖ξ‖ ^ (-criticalS d) * N ≤
      c * (2 * Real.pi) * ‖ξ‖ ^ (1 - criticalS d) * N := by
    rw [abs_of_pos hc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), ← h2]
    have : 0 ≤ ‖ξ‖ ^ (-criticalS d) := Real.rpow_nonneg hp.le _
    have hN0 : 0 ≤ N := norm_nonneg _
    calc c * (2 * Real.pi * |ξ i|) * ‖ξ‖ ^ (-criticalS d) * N
        ≤ c * (2 * Real.pi * ‖ξ‖) * ‖ξ‖ ^ (-criticalS d) * N := by gcongr
      _ = c * (2 * Real.pi) * (‖ξ‖ ^ (-criticalS d) * ‖ξ‖) * N := by ring
  have h4 : (‖ξ‖ ^ (1 - criticalS d)) ^ 2 = ‖ξ‖ ^ (2 - (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1; unfold criticalS; push_cast; ring
  calc (|c| * |2 * Real.pi * ξ i| * ‖ξ‖ ^ (-criticalS d) * N) ^ 2
      ≤ (c * (2 * Real.pi) * ‖ξ‖ ^ (1 - criticalS d) * N) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
    _ = (c * (2 * Real.pi)) ^ 2 * (‖ξ‖ ^ (1 - criticalS d)) ^ 2 * N ^ 2 := by ring
    _ = _ := by rw [h4]

/-- local integrability of `|ξ|^{2-d}` on the unit ball, as a finite `lintegral` -/
theorem r26t8a_f02b_J (hd : 2 ≤ d) :
    ∫⁻ ξ in Metric.ball (0 : Euc d) 1, ENNReal.ofReal (‖ξ‖ ^ (2 - (d : ℝ))) < ⊤ := by
  rcases Nat.eq_or_lt_of_le hd with h2 | h3
  · subst h2
    have : ∀ ξ : Euc 2, ENNReal.ofReal (‖ξ‖ ^ (2 - ((2 : ℕ) : ℝ))) = 1 := by
      intro ξ; simp
    simp_rw [this]
    simpa using measure_ball_lt_top (x := (0 : Euc 2)) (r := 1)
  · have hdR : (2 : ℝ) < d := by exact_mod_cast h3
    have h0 := HRS.Whole.u2_integrableOn_ball_rpow (d := d) (by omega) (a := (d : ℝ) - 2) (by linarith)
      (by linarith)
    have e : -((d : ℝ) - 2) = 2 - (d : ℝ) := by ring
    simp_rw [e] at h0
    exact h0.lintegral_lt_top

theorem r26t8a_f02b_hat_le (h : Euc d → ℝ) (ξ : Euc d) :
    ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ≤ ∫ y, ‖h y‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [Circle.norm_smul]

theorem r26t8a_f02b_pt (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) (i : Fin d) (h : SchwartzMap (Euc d) ℝ) (r : ℕ)
    {ξ : Euc d} (hξ : ξ ≠ 0) :
    wt ξ ^ (r : ℝ) * ‖r26t8a_f02b_M c i h ξ‖ ^ 2 ≤
      (c * (2 * Real.pi)) ^ 2 * (wt ξ ^ (r : ℝ) * ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2 +
        (Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d =>
          (1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2 * ‖z‖ ^ (2 - (d : ℝ))) ξ) := by
  have hM := r26t8a_f02b_M_sq c hc i h hξ
  have hw : 0 < wt ξ ^ (r : ℝ) := Real.rpow_pos_of_pos (wt_pos ξ) _
  have hK : 0 ≤ (c * (2 * Real.pi)) ^ 2 := sq_nonneg _
  have hN0 : 0 ≤ ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2 := sq_nonneg _
  have hp : 0 ≤ ‖ξ‖ ^ (2 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hE : 0 ≤ (1 + 4 * Real.pi ^ 2) ^ r := by positivity
  have hL : 0 ≤ (∫ y, ‖h y‖) ^ 2 := sq_nonneg _
  by_cases hb : ξ ∈ Metric.ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hb]
    have hn : ‖ξ‖ < 1 := by simpa using hb
    have hwle : wt ξ ^ (r : ℝ) ≤ (1 + 4 * Real.pi ^ 2) ^ r := by
      rw [Real.rpow_natCast]
      refine pow_le_pow_left₀ (wt_pos ξ).le ?_ r
      unfold wt
      have : ‖ξ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ξ]
      nlinarith [Real.pi_pos]
    have hhat : ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2 ≤ (∫ y, ‖h y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (r26t8a_f02b_hat_le h ξ) 2
    calc wt ξ ^ (r : ℝ) * ‖r26t8a_f02b_M c i h ξ‖ ^ 2
        ≤ (1 + 4 * Real.pi ^ 2) ^ r * ((c * (2 * Real.pi)) ^ 2 * ‖ξ‖ ^ (2 - (d : ℝ)) *
            ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2) :=
          mul_le_mul hwle hM (sq_nonneg _) hE
      _ ≤ (1 + 4 * Real.pi ^ 2) ^ r * ((c * (2 * Real.pi)) ^ 2 * ‖ξ‖ ^ (2 - (d : ℝ)) *
            (∫ y, ‖h y‖) ^ 2) := by gcongr
      _ = (c * (2 * Real.pi)) ^ 2 * ((1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2 *
            ‖ξ‖ ^ (2 - (d : ℝ))) := by ring
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)
  · rw [Set.indicator_of_notMem hb, add_zero]
    have hn : 1 ≤ ‖ξ‖ := by simpa using hb
    have h1 : ‖ξ‖ ^ (2 - (d : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                                                  linarith)
    calc wt ξ ^ (r : ℝ) * ‖r26t8a_f02b_M c i h ξ‖ ^ 2
        ≤ wt ξ ^ (r : ℝ) * ((c * (2 * Real.pi)) ^ 2 * ‖ξ‖ ^ (2 - (d : ℝ)) *
            ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2) := mul_le_mul_of_nonneg_left hM hw.le
      _ ≤ wt ξ ^ (r : ℝ) * ((c * (2 * Real.pi)) ^ 2 * 1 *
            ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2) := by gcongr
      _ = _ := by ring

theorem r26t8a_f02b_hat_cont (h : SchwartzMap (Euc d) ℝ) :
    Continuous (fun ξ : Euc d => 𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
    h.integrable.ofReal

theorem r26t8a_f02b_lint (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) (i : Fin d) (h : SchwartzMap (Euc d) ℝ) (r : ℕ) :
    ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (r : ℝ)) * ENNReal.ofReal (‖r26t8a_f02b_M c i h ξ‖ ^ 2) ≤
      ENNReal.ofReal ((c * (2 * Real.pi)) ^ 2) *
        ((∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (r : ℝ)) *
            ENNReal.ofReal (‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2)) +
          ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2) *
            ∫⁻ z in Metric.ball (0 : Euc d) 1, ENNReal.ofReal (‖z‖ ^ (2 - (d : ℝ)))) := by
  have hae : ∀ᵐ ξ : Euc d ∂volume, ξ ≠ 0 := by
    filter_upwards [r26t8a_f02a_ae_ne (d := d) (by omega) 0] with ξ hξ
    intro h0; apply hξ; simp [h0]
  have hK : 0 ≤ (c * (2 * Real.pi)) ^ 2 := sq_nonneg _
  have hE : 0 ≤ (1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2 := by positivity
  have hmeas : Measurable (fun ξ : Euc d => ENNReal.ofReal (wt ξ ^ (r : ℝ)) *
      ENNReal.ofReal (‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2)) := by
    refine (ENNReal.measurable_ofReal.comp (continuous_wt_rpow (d := d) (r : ℝ)).measurable).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((continuous_pow 2).comp (r26t8a_f02b_hat_cont h).norm).measurable
  calc ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (r : ℝ)) * ENNReal.ofReal (‖r26t8a_f02b_M c i h ξ‖ ^ 2)
      ≤ ∫⁻ ξ : Euc d, ENNReal.ofReal ((c * (2 * Real.pi)) ^ 2) *
          (ENNReal.ofReal (wt ξ ^ (r : ℝ)) *
            ENNReal.ofReal (‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2) +
          (Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d =>
            ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2) *
              ENNReal.ofReal (‖z‖ ^ (2 - (d : ℝ)))) ξ) := by
        refine lintegral_mono_ae (hae.mono fun ξ hξ => ?_)
        have hw : 0 ≤ wt ξ ^ (r : ℝ) := (Real.rpow_pos_of_pos (wt_pos ξ) _).le
        have hN : 0 ≤ ‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2 := sq_nonneg _
        have hpt := r26t8a_f02b_pt hd hc i h r hξ
        rw [← ENNReal.ofReal_mul hw]
        by_cases hb : ξ ∈ Metric.ball (0 : Euc d) 1
        · rw [Set.indicator_of_mem hb] at hpt
          simp only [Set.indicator_of_mem hb]
          refine (ENNReal.ofReal_le_ofReal hpt).trans (le_of_eq ?_)
          have hq : 0 ≤ ‖ξ‖ ^ (2 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
          rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_add (mul_nonneg hw hN) (by positivity),
            ENNReal.ofReal_mul hw, ENNReal.ofReal_mul hE]
        · rw [Set.indicator_of_notMem hb] at hpt
          simp only [Set.indicator_of_notMem hb]
          refine (ENNReal.ofReal_le_ofReal hpt).trans (le_of_eq ?_)
          rw [add_zero, add_zero, ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hw]
    _ = ENNReal.ofReal ((c * (2 * Real.pi)) ^ 2) *
          ∫⁻ ξ : Euc d, (ENNReal.ofReal (wt ξ ^ (r : ℝ)) *
            ENNReal.ofReal (‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2) +
          (Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d =>
            ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2) *
              ENNReal.ofReal (‖z‖ ^ (2 - (d : ℝ)))) ξ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        rw [lintegral_add_left hmeas, lintegral_indicator measurableSet_ball,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem r26t8a_f02b_l1 (h : SchwartzMap (Euc d) ℝ) :
    eLpNorm (⇑h) 1 volume = ENNReal.ofReal (∫ y, ‖h y‖) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm (h.integrable (μ := volume))]
  exact h.continuous.aestronglyMeasurable

/-- the `L²` Fourier transform of `forceConv` is the symbol times `ĥ` -/
theorem r26t8a_f02b_ident {c : ℝ} (i : Fin d) (h : SchwartzMap (Euc d) ℝ)
    (hM1 : Integrable (r26t8a_f02b_M c i h)) (hM2 : MemLp (r26t8a_f02b_M c i h) 2 volume)
    (hrep : ∀ x : Euc d, ((r26t8a_forceConv i h x : ℝ) : ℂ) =
      ∫ xi : Euc d, r26t8a_f02b_M c i h xi *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x xi : ℝ))) :
    MemLp (r26t8a_forceConv i h) 2 volume ∧
      HRS.PDE.ToolboxRd.fourierL2 (r26t8a_forceConv i h) =ᵐ[volume] r26t8a_f02b_M c i h := by
  set g : MeasureTheory.Lp (α := Euc d) ℂ 2 := (FT d).symm (hM2.toLp (r26t8a_f02b_M c i h)) with hg
  have hT' : (fun y : Euc d => ((r26t8a_forceConv i h y : ℝ) : ℂ)) =ᵐ[volume] ⇑g := by
    filter_upwards [HRS.MH.Screened.s4_bridge hM1 hM2] with y hy
    rw [hrep y, ← hy]
  have hmemC : MemLp (fun y : Euc d => ((r26t8a_forceConv i h y : ℝ) : ℂ)) 2 volume :=
    (MeasureTheory.Lp.memLp g).ae_eq hT'.symm
  have hT : MemLp (r26t8a_forceConv i h) 2 volume := by
    have := hmemC.re
    simpa using this
  refine ⟨hT, ?_⟩
  have hLp : ofRealLp hT = g := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [ofRealLp_coe hT, hT'] with y a b
    rw [a, b]
  rw [fourierL2_eq hT, hLp, hg, LinearIsometryEquiv.apply_symm_apply]
  exact MemLp.coeFn_toLp hM2

theorem r26t8a_f02b_core (hd : 2 ≤ d) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (h : SchwartzMap (Euc d) ℝ),
      HRS.PDE.ToolboxRd.MemSobolev (r : ℝ) (r26t8a_forceConv i h) ∧
      sobolevNormE (r : ℝ) (r26t8a_forceConv i h) ≤
        ENNReal.ofReal C * (sobolevNormE (r : ℝ) (⇑h) + eLpNorm (⇑h) 1 volume) := by
  obtain ⟨c, hc, H⟩ := r26t8a_forceConv_fourier_int d hd
  have hJ := r26t8a_f02b_J hd
  set J : ℝ≥0∞ := ∫⁻ z in Metric.ball (0 : Euc d) 1, ENNReal.ofReal (‖z‖ ^ (2 - (d : ℝ))) with hJdef
  set K : ℝ := (c * (2 * Real.pi)) ^ 2 with hKdef
  set E : ℝ := (1 + 4 * Real.pi ^ 2) ^ r with hEdef
  have hK : 0 ≤ K := sq_nonneg _
  have hE : 0 ≤ E := by positivity
  have hJr : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ.ne).symm
  set Jr : ℝ := J.toReal with hJrdef
  have hJr0 : 0 ≤ Jr := ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (K * (1 + E * Jr)), Real.sqrt_nonneg _, fun i h => ?_⟩
  -- finiteness of the datum terms
  have hhS : ∀ t : ℕ, HRS.PDE.ToolboxRd.MemSobolev (t : ℝ) (⇑h) := fun t =>
    HRS.MS.MovC1.movc1_memSob_schwartz h (t : ℝ)
  have hhfin : ∀ t : ℕ, sobolevNormE (t : ℝ) (⇑h) ≠ ⊤ := fun t => by
    unfold sobolevNormE; rw [if_pos (hhS t)]; exact ENNReal.ofReal_ne_top
  have hhsq : ∀ t : ℕ, (sobolevNormE (t : ℝ) (⇑h)) ^ 2 =
      ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (t : ℝ)) *
        ENNReal.ofReal (‖𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ‖ ^ 2) := fun t => by
    rw [HRS.MH.Screened.s5a_sobolevNormE_sq (hhS t)]
    refine lintegral_congr_ae ?_
    filter_upwards [fourierL2_schwartz h] with ξ hξ
    rw [hξ]
  have hL0 : 0 ≤ (∫ y, ‖h y‖) ^ 2 := sq_nonneg _
  -- the lintegral bound
  have hbd : ∀ t : ℕ, ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (t : ℝ)) *
        ENNReal.ofReal (‖r26t8a_f02b_M c i h ξ‖ ^ 2) ≤
      ENNReal.ofReal K * ((sobolevNormE (t : ℝ) (⇑h)) ^ 2 +
        ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ t * (∫ y, ‖h y‖) ^ 2) * J) := fun t => by
    rw [hhsq t]; exact r26t8a_f02b_lint hd hc i h t
  have hfin : ∀ t : ℕ, ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (t : ℝ)) *
        ENNReal.ofReal (‖r26t8a_f02b_M c i h ξ‖ ^ 2) < ⊤ := fun t => by
    refine lt_of_le_of_lt (hbd t) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.pow_lt_top (lt_top_iff_ne_top.2 (hhfin t))
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ
  -- membership in `L²` and identification
  have hM1 : Integrable (r26t8a_f02b_M c i h) := (H i h).1
  have hM2 : MemLp (r26t8a_f02b_M c i h) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hM1.aestronglyMeasurable]
    refine ⟨(HRS.PDE.ToolboxRd.FourierAux.aesm_sq hM1.aestronglyMeasurable), ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (hfin 0)
    refine lintegral_congr fun ξ => ?_
    simp only [Nat.cast_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    rw [← Real.enorm_eq_ofReal (sq_nonneg _)]
  obtain ⟨hT, hF⟩ := r26t8a_f02b_ident i h hM1 hM2 (fun x => (H i h).2 x)
  have hSq : ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (r : ℝ)) *
        ENNReal.ofReal (‖HRS.PDE.ToolboxRd.fourierL2 (r26t8a_forceConv i h) ξ‖ ^ 2) =
      ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (r : ℝ)) *
        ENNReal.ofReal (‖r26t8a_f02b_M c i h ξ‖ ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hF] with ξ hξ
    rw [hξ]
  have hmem : HRS.PDE.ToolboxRd.MemSobolev (r : ℝ) (r26t8a_forceConv i h) :=
    HRS.MH.Screened.s5a_memSobolev hT (by rw [hSq]; exact hfin r)
  refine ⟨hmem, ?_⟩
  have hS2 := HRS.MH.Screened.s5a_sobolevNormE_sq hmem
  rw [hSq] at hS2
  set a : ℝ≥0∞ := sobolevNormE (r : ℝ) (⇑h) with ha
  set b : ℝ≥0∞ := eLpNorm (⇑h) 1 volume with hb
  have hb' : b = ENNReal.ofReal (∫ y, ‖h y‖) := r26t8a_f02b_l1 h
  have hbsq : b ^ 2 = ENNReal.ofReal ((∫ y, ‖h y‖) ^ 2) := by
    rw [hb', ← ENNReal.ofReal_pow (integral_nonneg fun y => norm_nonneg _)]
  have h1 : (sobolevNormE (r : ℝ) (r26t8a_forceConv i h)) ^ 2 ≤
      (ENNReal.ofReal (Real.sqrt (K * (1 + E * Jr))) * (a + b)) ^ 2 := by
    rw [hS2]
    refine (hbd r).trans ?_
    have hEJ : 0 ≤ E * Jr := mul_nonneg hE hJr0
    have e1 : ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ r * (∫ y, ‖h y‖) ^ 2) * J =
        ENNReal.ofReal (E * Jr) * b ^ 2 := by
      rw [hbsq, hJr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hEJ]
      congr 1
      simp only [hEdef]
      ring
    have e2 : ENNReal.ofReal K * ENNReal.ofReal (1 + E * Jr) =
        ENNReal.ofReal (Real.sqrt (K * (1 + E * Jr))) ^ 2 := by
      rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
        Real.sq_sqrt (mul_nonneg hK (by linarith))]
    have e3 : ENNReal.ofReal (1 + E * Jr) = 1 + ENNReal.ofReal (E * Jr) := by
      rw [ENNReal.ofReal_add zero_le_one hEJ]; simp
    rw [e1, mul_pow, ← e2, mul_assoc]
    refine mul_le_mul_right ?_ _
    rw [e3, add_mul, one_mul]
    gcongr
    · exact le_self_add
    · exact le_add_self
  by_contra hlt
  push Not at hlt
  exact absurd h1 (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero hlt))

/-- **T8A.F02b**: the critical convolution maps Schwartz data to `H^r` with a bound by `‖h‖_{H^r} + ‖h‖_{L¹}`. -/
theorem r26t8a_forceConv_sobolev (d : ℕ) (hd : 2 ≤ d) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (h : SchwartzMap (Euc d) ℝ),
      r26t8a_SobSmooth (r26t8a_forceConv i h) ∧
      sobolevNormE (r : ℝ) (r26t8a_forceConv i h) ≤
        ENNReal.ofReal C * (sobolevNormE (r : ℝ) h + eLpNorm h 1 volume) := by
  obtain ⟨C, hC, H⟩ := r26t8a_f02b_core hd r
  refine ⟨C, hC, fun i h => ⟨⟨?_, fun t => ?_⟩, (H i h).2⟩⟩
  · have hd1 : 1 ≤ d := by omega
    have := HRS.MS.Ul.tail_conv hd (s := criticalS d) (HRS.MS.S82R.s82r_criticalS_pos hd1).le
      (HRS.MS.S82R.s82r_criticalS_lt hd1) h
    exact (EuclideanSpace.proj i).contDiff.comp this.2.1
  · obtain ⟨C', -, H'⟩ := r26t8a_f02b_core hd t
    exact (H' i h).1

end HRS.MS.R26T8A

end

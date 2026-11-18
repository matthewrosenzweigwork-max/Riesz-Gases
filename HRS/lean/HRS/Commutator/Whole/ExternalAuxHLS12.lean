import HRS.Commutator.Whole.ExternalAuxHLS11

/-!
# The Sobolev embedding for fractional transport bounds (packet X-HLS, part 12)
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma cmxHLS_aesm_of_rep {α : ℝ} {v w : Euc d → ℝ} (hrep : IsFracDerivRep α v w) :
    AEStronglyMeasurable w volume := by
  have hb : ∀ n : ℕ, AEStronglyMeasurable w (volume.restrict (closedBall (0 : Euc d) (n + 1))) := by
    intro n
    let b : ContDiffBump (0 : Euc d) := ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
    have hcs : HasCompactSupport (fun x : Euc d => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have hcd : ContDiff ℝ ∞ (fun x : Euc d => ((b x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp b.contDiff
    obtain ⟨-, h2, -⟩ := hrep (hcs.toSchwartzMap hcd)
    have h3 : AEStronglyMeasurable (fun x : Euc d => (((w x : ℝ) : ℂ) * ((b x : ℝ) : ℂ)).re) volume :=
      (Complex.continuous_re.comp_aestronglyMeasurable h2.1)
    refine (h3.restrict (s := closedBall (0 : Euc d) ((n : ℝ) + 1))).congr ?_
    refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
    have : b x = 1 := b.one_of_mem_closedBall hx
    simp [this]
  have hU : (⋃ n : ℕ, closedBall (0 : Euc d) ((n : ℝ) + 1)) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨n, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    linarith
  have := (aestronglyMeasurable_iUnion_iff (μ := volume) (s := fun n : ℕ => closedBall (0 : Euc d) ((n : ℝ) + 1))
    (f := w)).2 hb
  rwa [hU, Measure.restrict_univ] at this


lemma cmxHLS_rep_congr {α : ℝ} {v w w' : Euc d → ℝ} (hrep : IsFracDerivRep α v w)
    (h : w =ᵐ[volume] w') : IsFracDerivRep α v w' := by
  intro φ
  obtain ⟨h1, h2, h3⟩ := hrep φ
  refine ⟨h1, h2.congr ?_, ?_⟩
  · filter_upwards [h] with x hx
    simp [hx]
  · rw [h3]
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    simp [hx]

lemma cmxHLS_norm_toLp_le (y : Fin d → ℝ) : ‖(WithLp.toLp 2 y : Euc d)‖ ≤ ∑ i, |y i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |y i|)
    (fun i _ => abs_nonneg _)
  simpa [sq_abs] using this

lemma cmxHLS_measurable_toLp {g : Fin d → Euc d → ℝ} (hg : ∀ i, Measurable (g i)) :
    Measurable (fun x : Euc d => (WithLp.toLp 2 (fun i => g i x) : Euc d)) := by
  have h1 : Measurable (fun x : Euc d => (fun i => g i x : Fin d → ℝ)) := measurable_pi_iff.2 hg
  exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp h1

lemma cmxHLS_lip_bound {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (i : Fin d)
    (x : Euc d) : |v x i| ≤ (‖v 0‖ + L) * (1 + ‖x‖) := by
  have h1 : ‖v x‖ ≤ ‖v 0‖ + L * ‖x‖ := by
    have := hL.dist_le_mul x 0
    rw [dist_eq_norm, dist_zero_right] at this
    have h2 : ‖v x‖ ≤ ‖v x - v 0‖ + ‖v 0‖ := by
      calc ‖v x‖ = ‖(v x - v 0) + v 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖v x - v 0‖ + ‖v 0‖ := norm_add_le _ _
    linarith
  have h3 : |v x i| ≤ ‖v x‖ := by
    have := PiLp.norm_apply_le (v x) i
    simpa using this
  have h4 : (0 : ℝ) ≤ L := L.2
  nlinarith [norm_nonneg x, norm_nonneg (v 0)]


theorem cmxHLS_embedding (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ),
      HasFracTransportBound (a / 2) (2 * d / (a - 2)) v K →
        HasFracTransportBound (((d : ℝ) - s) / 2) (2 * d / ((d : ℝ) - s - 2)) v (C * K) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha2 : 0 < a - 2 := by linarith [ha.1]
  have hq2 : 0 < (d : ℝ) - s - 2 := by linarith
  set σ : ℝ := (a - d + s) / 2 with hσdef
  set β : ℝ := ((d : ℝ) - s) / 2 with hβdef
  set p : ℝ := 2 * d / (a - 2) with hpdef
  set q : ℝ := 2 * d / ((d : ℝ) - s - 2) with hqdef
  have hσ : 0 < σ := by rw [hσdef]; linarith [ha.1]
  have hσd : σ < d := by rw [hσdef]; linarith [ha.2]
  have hp : 1 < p := by
    rw [hpdef, lt_div_iff₀ ha2]; linarith [ha.2]
  have hpq : p < q := by
    rw [hpdef, hqdef]
    exact div_lt_div_of_pos_left (by linarith) hq2 (by linarith [ha.1])
  have hrel : 1 / q = 1 / p - σ / d := by
    rw [hqdef, hpdef, hσdef]
    field_simp
    ring
  have hβ : 1 < β := by rw [hβdef]; linarith
  have hαβ : a / 2 = β + σ := by rw [hβdef, hσdef]; ring
  obtain ⟨C₁, hC₁, hK⟩ := cmxHLS_kernel hd1 hσ hp hpq hrel
  have hc1 := cmxHLS_c1_pos d hσ hσd
  set c₁ : ℝ := cmxHLS_c1 d σ with hc1def
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  set Ch : ℝ := d * c₁ * C₁ ^ (1 / q) with hCh
  have hCh0 : 0 ≤ Ch := by positivity
  refine ⟨1 + Ch, by positivity, ?_⟩
  rintro v K ⟨L, F, hF0, hLip, ⟨w, hrep, hwLp⟩, hLF⟩
  -- measurable representatives of the components of `w`
  have hex : ∀ i : Fin d, ∃ wt : Euc d → ℝ, Measurable wt ∧ (fun x => w x i) =ᵐ[volume] wt := by
    intro i
    have h := cmxHLS_aesm_of_rep (hrep i)
    exact ⟨h.mk _, h.stronglyMeasurable_mk.measurable, h.ae_eq_mk⟩
  choose wt hwtm hwt using hex
  set wt' : Euc d → Euc d := fun y => (WithLp.toLp 2 (fun i => wt i y) : Euc d) with hwt'
  have hwt'm : Measurable wt' := cmxHLS_measurable_toLp hwtm
  have hae : ∀ᵐ y ∂(volume : Measure (Euc d)), w y = wt' y := by
    have := ae_all_iff.2 hwt
    filter_upwards [this] with y hy
    ext i
    simp [hwt', hy i]
  have hnormae : (fun x => ‖w x‖) =ᵐ[volume] (fun x => ‖wt' x‖) := by
    filter_upwards [hae] with x hx; rw [hx]
  have hrep' : ∀ i : Fin d, IsFracDerivRep (a / 2) (fun x => v x i) (wt i) := fun i =>
    cmxHLS_rep_congr (hrep i) (hwt i)
  -- the `L^p` norm of `wt'`
  have hnormp : eLpNorm (fun x => ‖wt' x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F := by
    rw [← eLpNorm_congr_ae hnormae]; exact hwLp
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hSp : ∫⁻ y, ((‖wt' y‖₊ : ℝ≥0) : ℝ≥0∞) ^ p ≤ ENNReal.ofReal F ^ p := by
    have h1 := hnormp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top
      (hwt'm.norm.aestronglyMeasurable), ENNReal.toReal_ofReal hp0.le] at h1
    have h2 := ENNReal.rpow_le_rpow h1 hp0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at h2
    have e : ∀ y : Euc d, ‖‖wt' y‖‖ₑ = ((‖wt' y‖₊ : ℝ≥0) : ℝ≥0∞) := fun y => by
      rw [enorm_norm]; rfl
    simp_rw [e] at h2
    exact h2
  have hSpt : ∫⁻ y, ((‖wt' y‖₊ : ℝ≥0) : ℝ≥0∞) ^ p ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hSp
  have hwtp : ∀ i : Fin d, ∫⁻ y, ‖wt i y‖ₑ ^ p ≠ ⊤ := by
    intro i
    refine ne_top_of_le_ne_top hSpt (lintegral_mono fun y => ?_)
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    have : ‖wt i y‖ ≤ ‖wt' y‖ := by
      have := PiLp.norm_apply_le (wt' y) i
      simpa [hwt'] using this
    exact_mod_cast (show ‖wt i y‖₊ ≤ ‖wt' y‖₊ from this)
  -- the representation of `|∇|^β v_i`
  have hvc : ∀ i : Fin d, Continuous (fun x => v x i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hLip.continuous
  have hrepW : ∀ i : Fin d, IsFracDerivRep β (fun x => v x i)
      (fun x => c₁ * cmxHLS_RP σ (wt i) x) := fun i =>
    cmxHLS_fracRep hd1 hσ hσd hp hpq hrel hβ (hvc i) (cmxHLS_lip_bound hLip i) (hwtm i) (hwtp i)
      (by rw [← hαβ]; exact hrep' i)
  set Wi : Fin d → Euc d → ℝ := fun i x => c₁ * cmxHLS_RP σ (wt i) x with hWi
  have hWim : ∀ i, Measurable (Wi i) := fun i => (cmxHLS_RP_measurable σ (hwtm i)).const_mul _
  set w' : Euc d → Euc d := fun x => (WithLp.toLp 2 (fun i => Wi i x) : Euc d) with hw'
  have hw'm : Measurable w' := cmxHLS_measurable_toLp hWim
  set fb : Euc d → ℝ≥0∞ := fun y => ((‖wt' y‖₊ : ℝ≥0) : ℝ≥0∞) with hfb
  have hmono : ∀ (i : Fin d) (x : Euc d),
      cmxHLS_I σ (fun y => ((‖wt i y‖₊ : ℝ≥0) : ℝ≥0∞)) x ≤ cmxHLS_I σ fb x := by
    intro i x
    refine lintegral_mono fun y => ?_
    refine mul_le_mul_right ?_ _
    have : ‖wt i y‖ ≤ ‖wt' y‖ := by
      have := PiLp.norm_apply_le (wt' y) i
      simpa [hwt'] using this
    show ((‖wt i y‖₊ : ℝ≥0) : ℝ≥0∞) ≤ ((‖wt' y‖₊ : ℝ≥0) : ℝ≥0∞)
    exact_mod_cast (show ‖wt i y‖₊ ≤ ‖wt' y‖₊ from this)
  have hbound : ∀ x : Euc d, ‖w' x‖ₑ ≤ ENNReal.ofReal (d * c₁) * cmxHLS_I σ fb x := by
    intro x
    have h1 : ‖w' x‖ ≤ ∑ i, |Wi i x| := cmxHLS_norm_toLp_le _
    have h2 : ‖w' x‖ₑ ≤ ∑ i, ‖Wi i x‖ₑ := by
      rw [← ofReal_norm]
      calc ENNReal.ofReal ‖w' x‖ ≤ ENNReal.ofReal (∑ i, |Wi i x|) := ENNReal.ofReal_le_ofReal h1
        _ = ∑ i, ENNReal.ofReal |Wi i x| := ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _
        _ = ∑ i, ‖Wi i x‖ₑ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ofReal_norm, Real.norm_eq_abs]
    refine h2.trans ?_
    calc ∑ i, ‖Wi i x‖ₑ ≤ ∑ _i : Fin d, ENNReal.ofReal c₁ * cmxHLS_I σ fb x := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hWi]; simp only
          rw [enorm_mul, Real.enorm_of_nonneg hc1.le]
          exact mul_le_mul_right ((cmxHLS_RP_enorm_le σ (wt i) x).trans (hmono i x)) _
      _ = ENNReal.ofReal (d * c₁) * cmxHLS_I σ fb x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have hfbm : Measurable fb := hwt'm.nnnorm.coe_nnreal_ennreal
  have hq0' : 0 ≤ 1 / q := by positivity
  have hLq : ∫⁻ x, ‖w' x‖ₑ ^ q ≤
      ENNReal.ofReal (d * c₁) ^ q * (ENNReal.ofReal C₁ * (∫⁻ y, fb y ^ p) ^ (q / p)) := by
    calc ∫⁻ x, ‖w' x‖ₑ ^ q ≤ ∫⁻ x, (ENNReal.ofReal (d * c₁) * cmxHLS_I σ fb x) ^ q :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hbound x) hq0.le
      _ = ENNReal.ofReal (d * c₁) ^ q * ∫⁻ x, cmxHLS_I σ fb x ^ q := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
      _ ≤ _ := mul_le_mul_right (hK (fun y => ‖wt' y‖₊) hwt'm.nnnorm) _
  have hqne : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hnormq : eLpNorm (fun x => ‖w' x‖) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal (Ch * F) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top
      hw'm.norm.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    have e : ∀ x : Euc d, ‖‖w' x‖‖ₑ = ‖w' x‖ₑ := fun x => enorm_norm _
    simp_rw [e]
    calc (∫⁻ x, ‖w' x‖ₑ ^ q) ^ (1 / q)
        ≤ (ENNReal.ofReal (d * c₁) ^ q * (ENNReal.ofReal C₁ * (∫⁻ y, fb y ^ p) ^ (q / p))) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hLq hq0'
      _ = ENNReal.ofReal (d * c₁) * (ENNReal.ofReal C₁ ^ (1 / q) * (∫⁻ y, fb y ^ p) ^ (1 / p)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0', ENNReal.mul_rpow_of_nonneg _ _ hq0',
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
          have : q / p * (1 / q) = 1 / p := by field_simp
          rw [this]
      _ ≤ ENNReal.ofReal (d * c₁) * (ENNReal.ofReal C₁ ^ (1 / q) * ENNReal.ofReal F) := by
          gcongr
          have h3 := ENNReal.rpow_le_rpow hSp (by positivity : 0 ≤ 1 / p)
          rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h3
      _ = ENNReal.ofReal (Ch * F) := by
          have e1 : Ch * F = (d * c₁) * (C₁ ^ (1 / q) * F) := by rw [hCh]; ring
          rw [e1, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d * c₁),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C₁ ^ (1 / q)),
            ENNReal.ofReal_rpow_of_pos hC₁]
  refine ⟨L, Ch * F, mul_nonneg hCh0 hF0, hLip, ⟨w', fun i => ?_, hnormq⟩, ?_⟩
  · simpa [hw', hWi] using hrepW i
  · have hL0 : (0 : ℝ) ≤ L := L.2
    nlinarith [mul_nonneg hCh0 (add_nonneg hL0 hF0)]

end HRS.Commutator.Whole

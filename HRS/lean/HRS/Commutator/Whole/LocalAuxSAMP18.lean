import HRS.Commutator.Whole.LocalAuxSAMP17
import HRS.Commutator.Whole.ExternalAuxMult4

/-!
# `vhi_Lp` (packet CMX-SAMP, helper file 18)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ} {s : ℝ}

lemma eLpNorm_Wcomp {k wf : Euc d → ℝ} (hk : Integrable k) (hf : AEStronglyMeasurable wf volume)
    {p : ℝ} (hp : 1 < p) :
    eLpNorm (fun x => wf x - (∫ y, psiL 1 y * wf (x - y)) + ∫ y, k (-y) * wf (x - y))
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (1 + (∫ y : Euc d, ‖psiL 1 y‖) + ∫ y, ‖k (-y)‖) *
        eLpNorm wf (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  set a : ℝ := ∫ y : Euc d, ‖psiL 1 y‖ with ha
  set b : ℝ := ∫ y, ‖k (-y)‖ with hb
  have ha0 : 0 ≤ a := integral_nonneg fun y => norm_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun y => norm_nonneg _
  have e : (fun x => wf x - (∫ y, psiL 1 y * wf (x - y)) + ∫ y, k (-y) * wf (x - y)) =
      (wf - fun x => ∫ y, psiL 1 y * wf (x - y)) + fun x => ∫ y, k (-y) * wf (x - y) := rfl
  rw [e]
  have h1 := eLpNorm_add_le (μ := volume) (f := wf - fun x => ∫ y, psiL 1 y * wf (x - y))
    (g := fun x => ∫ y, k (-y) * wf (x - y)) hp1
  have h2 := eLpNorm_sub_le (μ := volume) (f := wf) (g := fun x => ∫ y, psiL 1 y * wf (x - y)) hp1
  have h3 := eLpNorm_conv_real psi_integrable hf hp
  have h4 := eLpNorm_conv_real (k := fun y => k (-y)) hk.comp_neg hf hp
  refine h1.trans ?_
  calc eLpNorm (wf - fun x => ∫ y, psiL 1 y * wf (x - y)) (ENNReal.ofReal p) volume +
        eLpNorm (fun x => ∫ y, k (-y) * wf (x - y)) (ENNReal.ofReal p) volume
      ≤ (eLpNorm wf (ENNReal.ofReal p) volume +
          ENNReal.ofReal a * eLpNorm wf (ENNReal.ofReal p) volume) +
        ENNReal.ofReal b * eLpNorm wf (ENNReal.ofReal p) volume := by
        gcongr
        exact h2.trans (by gcongr)
    _ = ENNReal.ofReal (1 + a + b) * eLpNorm wf (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_add (by linarith) hb0, ENNReal.ofReal_add (by linarith) ha0,
          ENNReal.ofReal_one]
        ring

theorem vhi_Lp_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ),
      LipschitzWith L v →
      (∀ i, IsFracDerivRep (alphaE d s) (fun x => v x i) (fun x => w x i)) →
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (p1E d s)) volume ≤ ENNReal.ofReal F →
      ∃ W : Euc d → Euc d,
        (∀ i, IsBesselRep (alphaE d s) (fun x => Pgt 1 v x i) (fun x => W x i)) ∧
        eLpNorm (fun x => ‖W x‖) (ENNReal.ofReal (p1E d s)) volume +
            eLpNorm (fun x => ‖Pgt 1 v x‖) (ENNReal.ofReal (p1E d s)) volume ≤
          ENNReal.ofReal (C * F) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hα1, hαd, hα0, hp1, hαp⟩ := exponents hd hs0 hsd
  have hp0 : 0 < p1E d s := by linarith
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p1E d s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  obtain ⟨K, hK, hKF, hKq, -⟩ := kernel_data hd hs0 hsd
  obtain ⟨k, hk, hkF⟩ := cmxMY_mult_kernel_bessel hd (alphaE d s) hα0 (by exact_mod_cast hαd)
  obtain ⟨Cb, hCb, hb⟩ := vhi_bounded_core d
  set a : ℝ := ∫ y : Euc d, ‖psiL 1 y‖ with ha
  set b : ℝ := ∫ y : Euc d, ‖k (-y)‖ with hbdef
  set c : ℝ := ∫ y : Euc d, ‖K (-y)‖ with hc
  have ha0 : 0 ≤ a := integral_nonneg fun y => norm_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun y => norm_nonneg _
  have hc0 : 0 ≤ c := integral_nonneg fun y => norm_nonneg _
  set C₀ : ℝ := d * (1 + a + b) + c with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 1, by positivity, fun v L w F hLip hrep hnorm => ?_⟩
  obtain ⟨w', hw'm, hw', hrep', hid⟩ := vhi_identity hd hs0 hsd hK hKF hKq hLip hrep hnorm
  have hPc : Continuous (Pgt 1 v) := (hb v L hLip).1
  have hw'L : MemLp (fun x => ‖w' x‖) (ENNReal.ofReal (p1E d s)) volume := by
    rw [memLp_iff]; exact lt_of_le_of_lt hw' ENNReal.ofReal_lt_top
  have hw'P : MemLp w' (ENNReal.ofReal (p1E d s)) volume :=
    (memLp_norm_iff hw'm.aestronglyMeasurable).1 hw'L
  have hproj : ∀ i : Fin d, Measurable (fun x => w' x i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hw'm
  set Wi : Fin d → Euc d → ℝ := fun i x =>
    w' x i - (∫ y, psiL 1 y * w' (x - y) i) + ∫ y, k (-y) * w' (x - y) i with hWi
  set W : Euc d → Euc d := fun x => (WithLp.toLp 2 (fun i => Wi i x) : Euc d) with hW
  have hWim : ∀ i, AEStronglyMeasurable (Wi i) volume := by
    intro i
    have h1 : AEStronglyMeasurable (fun x => ∫ y, psiL 1 y * w' (x - y) i) volume := by
      have := aesm_conv (E := ℝ) psi_continuous.aestronglyMeasurable
        (hproj i).aestronglyMeasurable
      simpa [smul_eq_mul] using this
    have h2 : AEStronglyMeasurable (fun x => ∫ y, k (-y) * w' (x - y) i) volume := by
      have := aesm_conv (E := ℝ) (hk.comp_neg).1 (hproj i).aestronglyMeasurable
      simpa [smul_eq_mul] using this
    exact (((hproj i).aestronglyMeasurable.sub h1).add h2)
  have hWm : AEStronglyMeasurable W volume := by
    have : AEMeasurable (fun x => (fun i => Wi i x : Fin d → ℝ)) volume :=
      aemeasurable_pi_iff.2 fun i => (hWim i).aemeasurable
    exact ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable this).aestronglyMeasurable
  refine ⟨W, fun i => ?_, ?_⟩
  · -- Bessel representation
    have hVb : ∀ x, |Pgt 1 v x i| ≤ Cb * L := fun x => by
      have h1 : |Pgt 1 v x i| ≤ ‖Pgt 1 v x‖ := by
        simpa using PiLp.norm_apply_le (Pgt 1 v x) i
      exact h1.trans ((hb v L hLip).2.2 x)
    have hV : ∀ x, Pgt 1 v x i = ∫ y, K (-(x - y)) * w' y i := by
      intro x
      have hint := conv_integrable (hp := hp1) hKq hw'P x
      have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
      have h2 := congrArg (fun z : Euc d => z i) (hid x)
      simp only at h2
      rw [h2]
      simpa using this.symm
    exact bessel_rep_comp hd1 hK hk hKF hkF hp1 (hproj i) (lintegral_comp_ne_top hw'm hp0 hw' i)
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hPc) hVb hV
  · -- the norms
    set P : ℝ≥0∞ := ENNReal.ofReal (p1E d s) with hP
    have hcomp : ∀ i : Fin d, eLpNorm (fun x => w' x i) P volume ≤ ENNReal.ofReal F := by
      intro i
      refine le_trans ?_ hw'
      refine eLpNorm_mono_ae (hproj i).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      simpa using PiLp.norm_apply_le (w' x) i
    have hWi : ∀ i : Fin d, eLpNorm (Wi i) P volume ≤
        ENNReal.ofReal (1 + a + b) * ENNReal.ofReal F := fun i =>
      (eLpNorm_Wcomp hk (hproj i).aestronglyMeasurable hp1).trans (by gcongr; exact hcomp i)
    have hWn : eLpNorm (fun x => ‖W x‖) P volume ≤ ∑ i : Fin d, eLpNorm (Wi i) P volume := by
      calc eLpNorm (fun x => ‖W x‖) P volume ≤ eLpNorm (fun x => ∑ i : Fin d, ‖Wi i x‖) P volume := by
            refine eLpNorm_mono_ae hWm.norm (Eventually.of_forall fun x => ?_)
            have := cmxHLS_norm_toLp_le (fun i => Wi i x)
            rw [norm_norm, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
            simpa [Real.norm_eq_abs, hW] using this
        _ ≤ ∑ i : Fin d, eLpNorm (fun x => ‖Wi i x‖) P volume := by
            have e : (fun x => ∑ i : Fin d, ‖Wi i x‖) = ∑ i : Fin d, (fun x => ‖Wi i x‖) := by
              funext x; simp [Finset.sum_apply]
            rw [e]
            exact eLpNorm_sum_le (μ := volume) (p := P) (s := Finset.univ)
              (f := fun (i : Fin d) (x : Euc d) => ‖Wi i x‖) hP1
        _ = ∑ i : Fin d, eLpNorm (Wi i) P volume :=
            Finset.sum_congr rfl fun i _ => eLpNorm_norm _ (hWim i)
    have hPgt : eLpNorm (fun x => ‖Pgt 1 v x‖) P volume ≤ ENNReal.ofReal c * ENNReal.ofReal F := by
      have e : Pgt 1 v = fun x => ∫ z, K (-z) • w' (x - z) := by
        funext x
        rw [hid x]
        have := integral_sub_left_eq_self (μ := volume) (fun z : Euc d => K (-z) • w' (x - z)) x
        simpa [sub_sub_cancel] using this
      rw [eLpNorm_norm _ hPc.aestronglyMeasurable, e]
      refine (eLpNorm_conv_le (k := fun z => K (-z)) hK.comp_neg hw'm.aestronglyMeasurable hp1).trans ?_
      gcongr
      rw [← eLpNorm_norm _ hw'm.aestronglyMeasurable]
      exact hw'
    calc eLpNorm (fun x => ‖W x‖) P volume + eLpNorm (fun x => ‖Pgt 1 v x‖) P volume
        ≤ (∑ i : Fin d, ENNReal.ofReal (1 + a + b) * ENNReal.ofReal F) +
            ENNReal.ofReal c * ENNReal.ofReal F := by
          gcongr
          exact hWn.trans (Finset.sum_le_sum fun i _ => hWi i)
      _ = ENNReal.ofReal C₀ * ENNReal.ofReal F := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hC₀,
            ENNReal.ofReal_add (by positivity) hc0, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
          ring
      _ ≤ ENNReal.ofReal (C₀ + 1) * ENNReal.ofReal F := by
          gcongr; linarith
      _ = ENNReal.ofReal ((C₀ + 1) * F) := (ENNReal.ofReal_mul (by positivity)).symm

end HRS.Commutator.Whole.SAMP1

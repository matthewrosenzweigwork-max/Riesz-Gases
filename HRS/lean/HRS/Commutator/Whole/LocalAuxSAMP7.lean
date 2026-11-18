import HRS.Commutator.Whole.LocalAuxSAMP6

/-!
# `vlo_bound` (packet CMX-SAMP, helper file 7)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- A measurable representative of the transport field `w`. -/
lemma exists_meas_rep {v w : Euc d → Euc d} {α p F : ℝ}
    (hrep : ∀ i, IsFracDerivRep α (fun x => v x i) (fun x => w x i))
    (hw : eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F) :
    ∃ w' : Euc d → Euc d, Measurable w' ∧
      (∀ i, IsFracDerivRep α (fun x => v x i) (fun x => w' x i)) ∧
      eLpNorm (fun x => ‖w' x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F := by
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
  refine ⟨wt', hwt'm, fun i => ?_, ?_⟩
  · exact cmxHLS_rep_congr (hrep i) (hwt i)
  · rw [← eLpNorm_congr_ae hnormae]; exact hw

lemma lintegral_rpow_ne_top_of_le {g : Euc d → ℝ} (hgm : AEStronglyMeasurable g volume) {p F : ℝ}
    (hp : 0 < p) (h : eLpNorm g (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F) :
    ∫⁻ y, ‖g y‖ₑ ^ p ≠ ⊤ := by
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hgm,
    ENNReal.toReal_ofReal hp.le] at h
  have h2 := ENNReal.rpow_le_rpow h hp.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one] at h2
  exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top) h2

lemma lintegral_comp_ne_top {w : Euc d → Euc d} (hwm : Measurable w) {p F : ℝ} (hp : 0 < p)
    (h : eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F) (i : Fin d) :
    ∫⁻ y, ‖w y i‖ₑ ^ p ≠ ⊤ := by
  have h1 := lintegral_rpow_ne_top_of_le hwm.norm.aestronglyMeasurable hp h
  refine ne_top_of_le_ne_top h1 (lintegral_mono fun y => ?_)
  refine ENNReal.rpow_le_rpow ?_ hp.le
  rw [enorm_norm]
  have := PiLp.norm_apply_le (w y) i
  exact enorm_le_iff_norm_le.2 this

lemma psi_smul_integrable_Lp {W : Euc d → Euc d} (hWm : AEStronglyMeasurable W volume) {p : ℝ}
    (hp : 1 < p) (hW : MemLp (fun x => ‖W x‖) (ENNReal.ofReal p) volume) (x : Euc d) :
    Integrable (fun y => psiL 1 y • W (x - y)) := by
  have hp0 : 0 < p := by linarith
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have : P.HolderConjugate (ENNReal.conjExponent P) := ENNReal.HolderConjugate.conjExponent hP1
  have hψ : MemLp (fun y : Euc d => |psiL 1 y|) (ENNReal.conjExponent P) volume := by
    have := ((Om d).memLp (ENNReal.conjExponent P) (volume : Measure (Euc d))).norm
    refine this.ae_eq (Eventually.of_forall fun y => ?_)
    simp [norm_Om]
  have hWx : MemLp (fun y : Euc d => ‖W (x - y)‖) P volume :=
    hW.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hprod := MemLp.integrable_mul (p := ENNReal.conjExponent P) (q := P) hψ hWx
  refine hprod.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (psi_continuous.aestronglyMeasurable).smul
      (hWm.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving)
  · simp [norm_smul, Pi.mul_apply]

lemma Pleq_apply_comp (f : Euc d → Euc d) (x : Euc d)
    (hf : Integrable (fun y => psiL 1 y • f (x - y))) (i : Fin d) :
    (Pleq 1 f x) i = ∫ y : Euc d, psiL 1 y * f (x - y) i := by
  have h := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hf
  unfold Pleq
  simpa using h.symm

lemma Pleq_lip {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (x x' : Euc d) :
    ‖Pleq 1 v x - Pleq 1 v x'‖ ≤ (∫ y : Euc d, |psiL 1 y|) * L * ‖x - x'‖ := by
  have e : Pleq 1 v x - Pleq 1 v x' = ∫ y : Euc d, psiL 1 y • (v (x - y) - v (x' - y)) := by
    unfold Pleq
    rw [← integral_sub (psi_smul_integrable hL x) (psi_smul_integrable hL x')]
    simp_rw [smul_sub]
  rw [e]
  have hb : Integrable (fun y : Euc d => |psiL 1 y| * (L * ‖x - x'‖)) :=
    psi_integrable.abs.mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := lip_norm_le hL (x - y) (x' - y)
    rwa [sub_sub_sub_cancel_right] at this
  · rw [integral_mul_const]; nlinarith [norm_nonneg (x - x')]

theorem vlo_core {s : ℝ} (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      SubTransport d s (Pleq 1 v) (C * K) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  set p : ℝ := 2 * d / ((d : ℝ) - s - 2) with hp
  have hα1 : 1 < α := by rw [hα]; linarith
  have hq2 : 0 < (d : ℝ) - s - 2 := by linarith
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hq2]; linarith
  have hp0 : 0 < p := by linarith
  set M : ℝ := ∫ y : Euc d, |psiL 1 y| with hM
  have hM0 : 0 ≤ M := integral_nonneg fun y => abs_nonneg _
  refine ⟨M + 1, by positivity, ?_⟩
  rintro v K ⟨L, F, hF0, hLip, ⟨w, hrep, hw⟩, hLF⟩
  obtain ⟨w', hw'm, hrep', hw'⟩ := exists_meas_rep hrep hw
  have hLK : 0 ≤ K := by
    have : (0 : ℝ) ≤ L := L.2
    linarith
  have hw'L : MemLp (fun x => ‖w' x‖) (ENNReal.ofReal p) volume := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hw' ENNReal.ofReal_lt_top
  refine ⟨Real.toNNReal M * L, M * F, mul_nonneg hM0 hF0, ?_, ⟨Pleq 1 w', ?_, ?_⟩, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    refine (Pleq_lip hLip x x').trans (le_of_eq ?_)
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hM0]
  · intro i
    have e1 : (fun x => Pleq 1 v x i) = fun x => ∫ y : Euc d, psiL 1 y * v (x - y) i :=
      funext fun x => Pleq_apply_comp v x (psi_smul_integrable hLip x) i
    have e2 : (fun x => Pleq 1 w' x i) = fun x => ∫ y : Euc d, psiL 1 y * w' (x - y) i :=
      funext fun x => Pleq_apply_comp w' x
        (psi_smul_integrable_Lp hw'm.aestronglyMeasurable hp1 hw'L x) i
    rw [e1, e2]
    have hvc : Continuous (fun x => v x i) :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hLip.continuous
    exact rep_conv hd1 hα1 psi_measurable psi_integrable
      (by simpa using psi_moment (d := d) 1) hvc (cmxHLS_lip_bound hLip i)
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hw'm) hp1
      (lintegral_comp_ne_top hw'm hp0 hw' i) (hrep' i)
  · have h1 := eLpNorm_conv_le (k := fun y : Euc d => psiL 1 y) psi_integrable
      hw'm.aestronglyMeasurable hp1
    simp only [Real.norm_eq_abs] at h1
    have e : (fun x => ‖Pleq 1 w' x‖) = fun x => ‖∫ y : Euc d, psiL 1 y • w' (x - y)‖ := rfl
    rw [e, eLpNorm_norm _ (aesm_conv psi_integrable.1 hw'm.aestronglyMeasurable)]
    refine h1.trans ?_
    have h2 : eLpNorm w' (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F := by
      rw [← eLpNorm_norm _ hw'm.aestronglyMeasurable]; exact hw'
    rw [← hM, ENNReal.ofReal_mul hM0]
    gcongr
  · have : ((Real.toNNReal M * L : ℝ≥0) : ℝ) = M * L := by
      simp [Real.coe_toNNReal _ hM0]
    rw [this]
    nlinarith

end HRS.Commutator.Whole.SAMP1

import HRS.Commutator.Whole.XNRSAux33

/-!
# Packet X-NRS, part 34: mollification preserves the transport bound
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

open HRS.Commutator.Whole HRS.Commutator.Whole.SAMP1

lemma xmol_smul_integrable_Lp {k : Euc d → ℝ} (hk : XMolKer k) {W : Euc d → Euc d}
    (hWm : AEStronglyMeasurable W volume) {p : ℝ} (hp : 1 < p)
    (hW : MemLp (fun x => ‖W x‖) (ENNReal.ofReal p) volume) (x : Euc d) :
    Integrable (fun y => k y • W (x - y)) := by
  have hp0 : 0 < p := by linarith
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have : P.HolderConjugate (ENNReal.conjExponent P) := ENNReal.HolderConjugate.conjExponent hP1
  have hψ : MemLp (fun y : Euc d => |k y|) (ENNReal.conjExponent P) volume := by
    have := (hk.cont.memLp_of_hasCompactSupport (μ := (volume : Measure (Euc d)))
      (p := ENNReal.conjExponent P) hk.cpt).norm
    refine this.ae_eq (Eventually.of_forall fun y => ?_)
    simp
  have hWx : MemLp (fun y : Euc d => ‖W (x - y)‖) P volume :=
    hW.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hprod := MemLp.integrable_mul (p := ENNReal.conjExponent P) (q := P) hψ hWx
  refine hprod.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (hk.cont.aestronglyMeasurable).smul
      (hWm.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving)
  · simp [norm_smul, Pi.mul_apply]

lemma xmol_apply_comp {k : Euc d → ℝ} (f : Euc d → Euc d) (x : Euc d)
    (hf : Integrable (fun y => k y • f (x - y))) (i : Fin d) :
    (xmol k f x) i = ∫ y : Euc d, k y * f (x - y) i := by
  have h := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hf
  unfold xmol
  simpa using h.symm

theorem xmol_transport (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {k : Euc d → ℝ} (hk : XMolKer k) {v : Euc d → Euc d} {K : ℝ} (hv : SubTransport d s v K) :
    SubTransport d s (xmol k v) K := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  set p : ℝ := 2 * d / ((d : ℝ) - s - 2) with hp
  have hα1 : 1 < α := by rw [hα]; linarith
  have hq2 : 0 < (d : ℝ) - s - 2 := by linarith
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hq2]; linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨L, F, hF0, hLip, ⟨w, hrep, hw⟩, hLF⟩ := hv
  obtain ⟨w', hw'm, hrep', hw'⟩ := exists_meas_rep hrep hw
  have hw'L : MemLp (fun x => ‖w' x‖) (ENNReal.ofReal p) volume := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hw' ENNReal.ofReal_lt_top
  refine ⟨L, F, hF0, ?_, ⟨xmol k w', ?_, ?_⟩, hLF⟩
  · refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact xmol_lip hk hLip x x'
  · intro i
    have e1 : (fun x => xmol k v x i) = fun x => ∫ y : Euc d, k y * v (x - y) i :=
      funext fun x => xmol_apply_comp v x (xmol_integrable hk hLip x) i
    have e2 : (fun x => xmol k w' x i) = fun x => ∫ y : Euc d, k y * w' (x - y) i :=
      funext fun x => xmol_apply_comp w' x
        (xmol_smul_integrable_Lp hk hw'm.aestronglyMeasurable hp1 hw'L x) i
    rw [e1, e2]
    have hvc : Continuous (fun x => v x i) :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hLip.continuous
    exact rep_conv hd1 hα1 hk.cont.measurable hk.integrable
      (by simpa using hk.moment) hvc (cmxHLS_lip_bound hLip i)
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hw'm) hp1
      (lintegral_comp_ne_top hw'm hp0 hw' i) (hrep' i)
  · have h1 := eLpNorm_conv_le (k := k) hk.integrable hw'm.aestronglyMeasurable hp1
    have e : (fun x => ‖xmol k w' x‖) = fun x => ‖∫ y : Euc d, k y • w' (x - y)‖ := rfl
    rw [e, eLpNorm_norm _ (aesm_conv hk.integrable.1 hw'm.aestronglyMeasurable)]
    refine h1.trans ?_
    have h2 : eLpNorm w' (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F := by
      rw [← eLpNorm_norm _ hw'm.aestronglyMeasurable]; exact hw'
    rw [hk.norm_integral, ENNReal.ofReal_one, one_mul]
    exact h2

end HRS.Commutator.Whole.XNRS

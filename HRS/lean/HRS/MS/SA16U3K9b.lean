import HRS.MS.SA16CutK5
import HRS.MS.SA16StrongSL2
import HRS.MS.CzPvAsmAux2
import HRS.MS.CzElemAux1
import HRS.MS.CzHlsAux1

/-!
# S.A.16 K9, part (b): `splice_screened_low` at `θ = 1` (worker SA16U3)

Split `spliceKernel d 1 δ i = kout + kin` at radius `δ`.  `kout = pvkKtr (pvasmK d i) δ` is the truncated
Calderon-Zygmund kernel, so `∫ kout(z) h(x-z) dz = pvTrunc d 1 (u_i) h δ x` is bounded on `L^p` uniformly in `δ`
(`pvasm_Lp_ae_pv`).  `kin` is dominated by `δ^{-1} |z|^{1-d} 1_{|z| ≤ δ}`, whose `L^1` norm is the scale-free
constant `I0` (`sa16s_moment` at `θ = 1`), so Young's inequality applies.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.Pvk HRS.CZ.PvAsm HRS.CZ.ElemA
  HRS.CZ.Hls Phase2SA16

section K9b
variable {d : ℕ}

/-- the part of the splice kernel outside the ball of radius `δ` -/
def sa16u3_kout (d : ℕ) (δ : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  if δ < ‖z‖ then spliceKernel d 1 δ i z else 0

/-- the part of the splice kernel inside the closed ball of radius `δ` -/
def sa16u3_kin (d : ℕ) (δ : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  if δ < ‖z‖ then 0 else spliceKernel d 1 δ i z

lemma sa16u3_split (δ : ℝ) (i : Fin d) (z : Euc d) :
    sa16u3_kout d δ i z + sa16u3_kin d δ i z = spliceKernel d 1 δ i z := by
  unfold sa16u3_kout sa16u3_kin
  split_ifs <;> simp

lemma sa16u3_kout_meas (δ : ℝ) (i : Fin d) : Measurable (sa16u3_kout d δ i) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_norm) (sa16k5_ks_meas 1 δ i)
    measurable_const

lemma sa16u3_kin_meas (δ : ℝ) (i : Fin d) : Measurable (sa16u3_kin d δ i) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
    (sa16k5_ks_meas 1 δ i)

lemma sa16u3_kout_eq {δ : ℝ} (hδ : 0 < δ) (i : Fin d) :
    sa16u3_kout d δ i = pvkKtr (pvasmK d i) δ := by
  funext z
  unfold sa16u3_kout pvkKtr
  by_cases hz : δ < ‖z‖
  · rw [if_pos hz, if_pos hz]
    have hn : 0 < ‖z‖ := hδ.trans hz
    unfold spliceKernel pvasmK pvkOmegaK
    rw [if_pos hz]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [Real.rpow_add hn, Real.rpow_one, Real.rpow_natCast]
    field_simp
  · rw [if_neg hz, if_neg hz]

/-- integrable majorant of the inner part, with `L^1` norm independent of `δ` -/
def sa16u3_mm (d : ℕ) (δ : ℝ) (z : Euc d) : ℝ :=
  δ ^ (-(1 : ℝ)) * (closedBall (0 : Euc d) δ).indicator
    (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 1))) z

lemma sa16u3_mm_nonneg {δ : ℝ} (hδ : 0 < δ) (z : Euc d) : 0 ≤ sa16u3_mm d δ z := by
  unfold sa16u3_mm
  exact mul_nonneg (Real.rpow_nonneg hδ.le _)
    (Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) z)

lemma sa16u3_mm_meas (δ : ℝ) : Measurable (sa16u3_mm d δ) :=
  measurable_const.mul ((measurable_norm.pow_const _).indicator measurableSet_closedBall)

/-- the `L^1` norm of the majorant is a constant independent of `δ` -/
lemma sa16u3_mm_data (hd : 1 ≤ d) :
    ∃ I0 : ℝ, 0 ≤ I0 ∧ ∀ δ : ℝ, 0 < δ →
      Integrable (sa16u3_mm d δ) ∧ ∫ z, sa16u3_mm d δ z = I0 := by
  obtain ⟨I0, hI0, hI⟩ := sa16s_moment (d := d) hd (θ := 1) (by norm_num)
  refine ⟨I0, hI0, fun δ hδ => ?_⟩
  obtain ⟨hint, hval⟩ := hI δ hδ
  refine ⟨hint.const_mul _, ?_⟩
  unfold sa16u3_mm
  rw [integral_const_mul, hval, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_neg_one]
  field_simp

lemma sa16u3_kin_le {δ : ℝ} (hδ : 0 < δ) (i : Fin d) (z : Euc d) :
    |sa16u3_kin d δ i z| ≤ sa16u3_mm d δ z := by
  by_cases hz : δ < ‖z‖
  · simp only [sa16u3_kin, if_pos hz, abs_zero]
    exact sa16u3_mm_nonneg hδ z
  · simp only [sa16u3_kin, if_neg hz]
    have h1 := sa16k5_ks_small hδ (θ := 1) zero_le_one i hz
    have hz' : z ∈ closedBall (0 : Euc d) δ := by simpa using not_lt.1 hz
    unfold sa16u3_mm
    rw [Set.indicator_of_mem hz']
    have e : 2 - ((d : ℝ) + 1) = -((d : ℝ) - 1) := by ring
    rw [e]; exact h1

/-- Young bound for the inner part, uniformly in `δ` -/
lemma sa16u3_J_bound {δ I0 p : ℝ} (hδ : 0 < δ) (hI : ∫ z, sa16u3_mm d δ z = I0)
    (hmi : Integrable (sa16u3_mm d δ)) (hp : 1 ≤ p) (i : Fin d) {h : Euc d → ℝ} (hh : Measurable h) :
    eLpNorm (fun x => ∫ z, sa16u3_kin d δ i z * h (x - z)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal I0 * eLpNorm h (ENNReal.ofReal p) volume := by
  have hJ : ∫⁻ z, ENNReal.ofReal (sa16u3_mm d δ z) = ENNReal.ofReal I0 := by
    rw [← hI]
    exact (ofReal_integral_eq_lintegral_ofReal hmi (Eventually.of_forall (sa16u3_mm_nonneg hδ))).symm
  have hF : ∀ x, ‖∫ z, sa16u3_kin d δ i z * h (x - z)‖ₑ ≤
      ∫⁻ z, ENNReal.ofReal (sa16u3_mm d δ z) * ‖h (x - z)‖ₑ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
    rw [enorm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (sa16u3_kin_le hδ i z)
  have hFm : AEStronglyMeasurable (fun x => ∫ z, sa16u3_kin d δ i z * h (x - z)) volume :=
    hlsg_aesm_conv (sa16u3_kin_meas δ i) hh.aestronglyMeasurable
  have key := elema_young (sa16u3_mm_meas (d := d) δ) hh hFm hp hF
  rw [hJ] at key
  exact key

/-- for a.e. `x` the inner integrand is integrable (finite Young bound) -/
lemma sa16u3_J_int_ae {δ I0 p : ℝ} (hδ : 0 < δ) (hI : ∫ z, sa16u3_mm d δ z = I0)
    (hmi : Integrable (sa16u3_mm d δ)) (hp : 1 ≤ p) (i : Fin d) {h : Euc d → ℝ}
    (hh : Measurable h) (hhp : MemLp h (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), Integrable (fun z => sa16u3_kin d δ i z * h (x - z)) := by
  have hp0 : 0 < p := by linarith
  have hJ : ∫⁻ z, ENNReal.ofReal (sa16u3_mm d δ z) = ENNReal.ofReal I0 := by
    rw [← hI]
    exact (ofReal_integral_eq_lintegral_ofReal hmi (Eventually.of_forall (sa16u3_mm_nonneg hδ))).symm
  have hy := HRS.Commutator.Whole.XLI.young_lintegral (d := d)
    (a := fun z => ENNReal.ofReal (sa16u3_mm d δ z)) (b := fun z => ‖h z‖ₑ)
    (ENNReal.measurable_ofReal.comp (sa16u3_mm_meas δ)) hh.enorm hp
  have hhf : ∫⁻ x, ‖h x‖ₑ ^ p < ⊤ := by
    have h1 := hhp.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
      hh.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 h1
  have hfin : ∫⁻ x, (∫⁻ z, ENNReal.ofReal (sa16u3_mm d δ z) * ‖h (x - z)‖ₑ) ^ p ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hy ?_)
    rw [hJ]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hhf
  have hmeasA : Measurable (fun x : Euc d => ∫⁻ z, ENNReal.ofReal (sa16u3_mm d δ z) * ‖h (x - z)‖ₑ) := by
    have hm : Measurable (fun q : Euc d × Euc d =>
        ENNReal.ofReal (sa16u3_mm d δ q.2) * ‖h (q.1 - q.2)‖ₑ) :=
      (ENNReal.measurable_ofReal.comp ((sa16u3_mm_meas δ).comp measurable_snd)).mul
        (hh.enorm.comp (measurable_fst.sub measurable_snd))
    exact hm.lintegral_prod_right'
  have hae := ae_lt_top' (hmeasA.pow_const p).aemeasurable hfin
  filter_upwards [hae] with x hx
  have hx' : ∫⁻ z, ENNReal.ofReal (sa16u3_mm d δ z) * ‖h (x - z)‖ₑ < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos hp0).1 hx
  refine ⟨(sa16u3_kin_meas δ i).aestronglyMeasurable.mul
    (hh.comp (measurable_const.sub measurable_id)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hx'
  rw [enorm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (sa16u3_kin_le hδ i z)

end K9b

section Core
variable {d : ℕ}

lemma sa16u3_core (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ (i : Fin d) (h : Euc d → ℝ), Measurable h →
      MemLp h (ENNReal.ofReal p) volume →
      eLpNorm (spliceOdd d 1 δ i h) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal p) volume := by
  obtain ⟨C1, hC1, hP⟩ := pvasm_Lp_ae_pv hd hp
  obtain ⟨I0, hI0, hM⟩ := sa16u3_mm_data hd
  refine ⟨C1 + I0 + 1, by positivity, fun δ hδ i h hh hhp => ?_⟩
  obtain ⟨hmi, hmI⟩ := hM δ hδ
  have hp1 : (1 : ℝ) ≤ p := hp.le
  have hp1' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  have hTint : ∀ x, Integrable (fun z => sa16u3_kout d δ i z * h (x - z)) := by
    intro x
    rw [sa16u3_kout_eq hδ i]
    exact (pvasm_holder_int hp (pvasm_Ktr_meas hd i δ) hh
      (pvasm_Lq_Ktr hd i (pvasm_conj_gt hp) hδ) hhp x).1
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), spliceOdd d 1 δ i h x =
      (∫ z, sa16u3_kout d δ i z * h (x - z)) + ∫ z, sa16u3_kin d δ i z * h (x - z) := by
    filter_upwards [sa16u3_J_int_ae hδ hmI hmi hp1 i hh hhp] with x hx
    unfold spliceOdd
    rw [← integral_add (hTint x) hx]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [← add_mul, sa16u3_split]
  have hTm : AEStronglyMeasurable (fun x => ∫ z, sa16u3_kout d δ i z * h (x - z)) volume :=
    hlsg_aesm_conv (sa16u3_kout_meas δ i) hh.aestronglyMeasurable
  have hJm : AEStronglyMeasurable (fun x => ∫ z, sa16u3_kin d δ i z * h (x - z)) volume :=
    hlsg_aesm_conv (sa16u3_kin_meas δ i) hh.aestronglyMeasurable
  have hTn : (fun x => ∫ z, sa16u3_kout d δ i z * h (x - z)) =
      fun x => pvTrunc d 1 (fun v : Euc d => v i) h δ x := by
    funext x
    rw [pvasm_trunc_eq, sa16u3_kout_eq hδ i]
  have hT := ((hP i h hhp).1 δ hδ)
  have hJ := sa16u3_J_bound hδ hmI hmi hp1 i hh
  calc eLpNorm (spliceOdd d 1 δ i h) (ENNReal.ofReal p) volume
      = eLpNorm (fun x => (∫ z, sa16u3_kout d δ i z * h (x - z)) +
          ∫ z, sa16u3_kin d δ i z * h (x - z)) (ENNReal.ofReal p) volume := eLpNorm_congr_ae hae
    _ ≤ eLpNorm (fun x => ∫ z, sa16u3_kout d δ i z * h (x - z)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => ∫ z, sa16u3_kin d δ i z * h (x - z)) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hp1'
    _ ≤ ENNReal.ofReal C1 * eLpNorm h (ENNReal.ofReal p) volume +
          ENNReal.ofReal I0 * eLpNorm h (ENNReal.ofReal p) volume := by
        rw [hTn]; exact add_le_add hT hJ
    _ ≤ ENNReal.ofReal (C1 + I0 + 1) * eLpNorm h (ENNReal.ofReal p) volume := by
        rw [← add_mul, ← ENNReal.ofReal_add hC1 hI0]
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le

lemma sa16u3_spliceOdd_congr {θ δ : ℝ} (i : Fin d) {h h' : Euc d → ℝ} (hh : h =ᵐ[volume] h') :
    spliceOdd d θ δ i h = spliceOdd d θ δ i h' := by
  funext x
  unfold spliceOdd
  refine integral_congr_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hh]
    with z hz
  simp only [Function.comp] at hz
  rw [hz]

/-- K9 at `θ = 1` -/
theorem sa16u3_screened_one (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ i : Fin d, ∀ a W : Euc d → ℝ,
      MemLp a ⊤ volume → MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (spliceOdd d 1 δ i (fun y => a y * W y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hcore⟩ := sa16u3_core hd (show 1 < p by linarith)
  refine ⟨C, hC, fun δ hδ i a W ha hW => ?_⟩
  have hprod : eLpNorm (a • W) (ENNReal.ofReal p) volume ≤
      eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume :=
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm _ ha.aestronglyMeasurable
  have hg : MemLp (fun x => a x * W x) (ENNReal.ofReal p) volume := by
    have : (fun x => a x * W x) = a • W := rfl
    rw [this]
    exact lt_of_le_of_lt hprod (ENNReal.mul_lt_top ha hW)
  have hae := hg.aestronglyMeasurable.ae_eq_mk
  set h' := hg.aestronglyMeasurable.mk (fun x => a x * W x) with hh'
  have hh'm : Measurable h' := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hh'p : MemLp h' (ENNReal.ofReal p) volume := hg.ae_eq hae
  rw [sa16u3_spliceOdd_congr i hae]
  refine (hcore δ hδ.1 i h' hh'm hh'p).trans ?_
  rw [← eLpNorm_congr_ae hae, mul_assoc]
  exact mul_le_mul_of_nonneg_left hprod zero_le

end Core
end HRS.Whole.AppendixA.Phase2SA16Cutoff

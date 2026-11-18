import HRS.Equilibrium.Parametrix.PX4aAuxN

/-!
# Packet PX4a auxiliaries O: the torus convolution in the cube representation

`conv_cube_repr`: `(g * h)(mk (Y + z)) = ∫_{cube} g(z - w) h(mk (Y + w)) dw`;
`cube_reflect`: reflection `w ↦ z - w` of the cube integral of a periodic function.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem px4a_measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

lemma measurable_mk : Measurable (Torus.mk : Euc d → Torus d) :=
  (LocalDivAux.mk_measurePreserving (d := d)).measurable

lemma measurable_ghat_torus (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Measurable (periodicRiesz d s) :=
  CoercAux.measurable_periodicRiesz_one (by omega) hs0 hsd

theorem conv_cube_repr (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hm : Measurable h) (Y z : Euc d) :
    convFun (periodicRiesz d s) h (Torus.mk (Y + z)) =
      ∫ w in LocalDivAux.cube d, ghat d s (z - w) * h (Torus.mk (Y + w)) := by
  have hg := measurable_ghat_torus hd hs0 hsd
  unfold convFun
  have hG : Measurable (fun u : Torus d => periodicRiesz d s (Torus.mk (Y + z) - u) * h u) :=
    (hg.comp (measurable_const.sub measurable_id)).mul hm
  rw [LocalDivAux.integral_shift_cube (Torus.mk Y) _ hG]
  refine setIntegral_congr_fun LocalDivAux.measurableSet_cube fun w _ => ?_
  simp only [ghat]
  have e1 : Torus.mk (Y + z) - (Torus.mk Y + Torus.mk w) = Torus.mk (z - w) := by
    rw [mk_sub_eq, mk_add_eq]; abel
  have e2 : Torus.mk Y + Torus.mk w = Torus.mk (Y + w) := (mk_add_eq _ _).symm
  rw [e1, e2]

theorem cube_reflect (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ}
    (hFm : Measurable F) (hper : ∀ w n : Euc d, IsLat n → F (w + n) = F w) (z : Euc d) :
    ∫ w in LocalDivAux.cube d, ghat d s (z - w) * F w =
      ∫ w in LocalDivAux.cube d, ghat d s w * F (z - w) := by
  have hg := measurable_ghat_torus hd hs0 hsd
  set Ft : Torus d → ℝ := fun u => F (Torus.rep u) with hFt
  have hFtm : Measurable Ft := hFm.comp (px4a_measurable_rep d)
  have hFtk : ∀ v : Euc d, Ft (Torus.mk v) = F v := by
    intro v
    obtain ⟨k, hk, e⟩ := rep_exists_lat v
    simp only [hFt]
    rw [e, hper v k hk]
  set Φ : Torus d → ℝ := fun u => periodicRiesz d s (Torus.mk z - u) * Ft u with hΦ
  have hneg' : Measurable (fun u : Torus d => Torus.mk z - u) := by fun_prop
  have hΦm : Measurable Φ := (hg.comp hneg').mul hFtm
  have h1 : ∫ w in LocalDivAux.cube d, ghat d s (z - w) * F w =
      ∫ w in LocalDivAux.cube d, Φ (Torus.mk w) := by
    refine setIntegral_congr_fun LocalDivAux.measurableSet_cube fun w _ => ?_
    simp only [hΦ, ghat, hFtk, mk_sub_eq]
  have h2 : ∫ w in LocalDivAux.cube d, ghat d s w * F (z - w) =
      ∫ w in LocalDivAux.cube d, (fun v : Torus d => periodicRiesz d s v * Ft (Torus.mk z - v)) (Torus.mk w) := by
    refine setIntegral_congr_fun LocalDivAux.measurableSet_cube fun w _ => ?_
    simp only [ghat]
    rw [← hFtk (z - w), mk_sub_eq]
  have hneg : Measurable (fun v : Torus d => Torus.mk z - v) := by fun_prop
  rw [h1, h2, ← LocalDivAux.integral_torus_cube Φ hΦm,
    ← LocalDivAux.integral_torus_cube (fun v : Torus d => periodicRiesz d s v * Ft (Torus.mk z - v))
      (hg.mul (hFtm.comp hneg))]
  have := integral_sub_left_eq_self Φ (volume : Measure (Torus d)) (Torus.mk z)
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [hΦ]
  congr 2
  abel

lemma Gsrc_zero_of_ge (F : Torus d → Torus d → ℝ) (X w : Euc d) (hw : 1 / 32 ≤ ‖w‖) :
    Gsrc F (X, w) = 0 := by
  simp only [Gsrc]
  rw [px3a_zeta_eq_zero (by norm_num : (0 : ℝ) < 1 / 32) hw, zero_mul]

lemma integrable_ghat_shift_cube (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (z : Euc d) :
    Integrable (fun w => ghat d s (z - w)) (volume.restrict (LocalDivAux.cube d)) := by
  have hmp := LocalDivAux.mk_measurePreserving (d := d)
  have hI : Integrable (periodicRiesz d s) (volume : Measure (Torus d)) :=
    integrable_periodicRiesz_one_le (by omega) hs0 hsd
  have h1 : Integrable (fun u : Torus d => periodicRiesz d s (Torus.mk z - u)) (volume : Measure (Torus d)) :=
    hI.comp_sub_left (Torus.mk z)
  have h2 := (hmp.integrable_comp h1.aestronglyMeasurable).mpr h1
  refine h2.congr (Eventually.of_forall fun w => ?_)
  simp only [Function.comp, ghat, mk_sub_eq]

theorem conv_split (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {F : Torus d → Torus d → ℝ}
    {σ : ℝ} {b m : ℕ} {A : ℝ} (hA : 0 ≤ A) (hσ : σ < d) (hG : SrcCls d σ b m A (Gsrc F))
    (Y z : Euc d) (hz : z ≠ 0) (hzb : ∀ i, |z i| ≤ 1 / 2 + 1 / 64)
    (hFm : Measurable (fun u : Torus d => F u (Torus.mk Y)))
    (hFc : Continuous (fun w : Euc d => Fsrc F (Y, w)))
    (hFb : ∃ N : ℝ, ∀ w : Euc d, |Fsrc F (Y, w)| ≤ N) :
    convFun (periodicRiesz d s) (fun u => F u (Torus.mk Y)) (Torus.mk (Y + z)) =
      kPot d (ghat d s) (Gsrc F) (Y, z) + farConv d s (Fsrc F) (Y, z) := by
  have hd1 : 1 ≤ d := by omega
  have hk := locKer_riesz hd hs0 hsd
  rw [conv_cube_repr hd hs0.le hsd _ hFm Y z]
  -- integrability of the near part
  have hz' : ∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc F (X, w) = 0 := fun X w hw =>
    Gsrc_zero_of_ge F X w hw.le
  have hIA : Integrable (fun w => ghat d s (z - w) * Gsrc F (Y, w)) := by
    have h1 := kPot_integrable hd1 hk hσ hA hG hz' Y z hz
    have h2 : Integrable (fun w => Lam d s (z - w) * Gsrc F (Y, w)) := by
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y, ‖Lam d s y‖ ≤ C := by
        obtain ⟨M0, -, hM0⟩ := Lam_bdd hd hs0.le hsd 0
        exact ⟨M0, fun y => by simpa [norm_iteratedFDeriv_zero] using hM0 y⟩
      have hgi := hG.slice_integrable hd1 hσ Y
      have hmeas : AEStronglyMeasurable (fun w => Lam d s (z - w)) volume :=
        ((Lam_contDiff hd hs0.le hsd 0).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      have := hgi.bdd_mul hmeas (Eventually.of_forall fun w => hC _)
      simpa [mul_comm] using this
    refine (h1.add h2).congr (Eventually.of_forall fun w => ?_)
    show rieszK d s (z - w) * Gsrc F (Y, w) + Lam d s (z - w) * Gsrc F (Y, w) = ghat d s (z - w) * Gsrc F (Y, w)
    by_cases hw : ‖w‖ < 1 / 32
    · rw [← add_mul]
      congr 1
      exact (ghat_split z w hzb hw).symm
    · rw [Gsrc_zero_of_ge F Y w (not_lt.mp hw)]; simp
  have hIAc : Integrable (fun w => ghat d s (z - w) * Gsrc F (Y, w)) (volume.restrict (LocalDivAux.cube d)) :=
    hIA.restrict
  obtain ⟨N, hN⟩ := hFb
  have hIB : Integrable (fun w => ghat d s (z - w) * Fsrc F (Y, w)) (volume.restrict (LocalDivAux.cube d)) := by
    have h1 := integrable_ghat_shift_cube hd hs0.le hsd z
    have := h1.bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs] using hN w)
    simpa [mul_comm] using this
  -- the integrand splits on the cube
  have hsplit : ∀ w ∈ LocalDivAux.cube d, ghat d s (z - w) * F (Torus.mk (Y + w)) (Torus.mk Y) =
      ghat d s (z - w) * Gsrc F (Y, w) + ghat d s (z - w) * Fsrc F (Y, w) := by
    intro w hw
    have hwb : ∀ i, |w i| ≤ 1 / 2 := fun i => by
      have h := hw i
      simp only [Set.mem_Ioc] at h
      rw [abs_le]; constructor <;> linarith [h.1, h.2]
    have hp := perCut_eq_on_cube (d := d) (r := 1 / 32) (by norm_num) (by norm_num) w hwb
    rw [← mul_add]
    congr 1
    simp only [Gsrc, Fsrc, leftCh]
    rw [hp]; ring
  rw [setIntegral_congr_fun LocalDivAux.measurableSet_cube hsplit, integral_add hIAc hIB]
  congr 1
  · -- near part
    unfold kPot
    simp only []
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro w hw
    have : 1 / 32 ≤ ‖w‖ := by
      by_contra hlt
      apply hw
      intro i
      have h1 := PiLp.norm_apply_le w i
      simp only [Real.norm_eq_abs] at h1
      have h2 := abs_lt.mp (lt_of_le_of_lt h1 (not_le.mp hlt))
      simp only [Set.mem_Ioc]
      constructor <;> linarith [h2.1, h2.2]
    rw [Gsrc_zero_of_ge F Y w this, mul_zero]
  · -- far part
    unfold farConv
    exact cube_reflect hd hs0.le hsd hFc.measurable (fun w n hn => Fsrc_periodic_w F Y w n hn) z

end HRS.Parx

end

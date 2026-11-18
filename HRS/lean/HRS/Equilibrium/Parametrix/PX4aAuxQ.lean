import HRS.Equilibrium.Parametrix.PX4aAuxP

/-!
# Packet PX4a auxiliaries Q: differentiability of the convolution with the Riesz kernel
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma Lam_bound0 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : ∃ C : ℝ, ∀ y, ‖Lam d s y‖ ≤ C := by
  obtain ⟨M0, -, hM0⟩ := Lam_bdd hd hs0 hsd 0
  exact ⟨M0, fun y => by simpa [norm_iteratedFDeriv_zero] using hM0 y⟩

lemma Lam_mul_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {σ : ℝ} (hσ : σ < d) {b m : ℕ}
    {A : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g) (Y z : Euc d) :
    Integrable (fun w => Lam d s (z - w) * g (Y, w)) := by
  obtain ⟨C, hC⟩ := Lam_bound0 hd hs0 hsd
  have hgi := h.slice_integrable (by omega) hσ Y
  have hmeas : AEStronglyMeasurable (fun w => Lam d s (z - w)) volume :=
    ((Lam_contDiff hd hs0 hsd 0).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have := hgi.bdd_mul hmeas (Eventually.of_forall fun w => hC _)
  simpa [mul_comm] using this

lemma kPot_ghat_split (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {σ : ℝ} (hσ : σ < d) {b m : ℕ}
    {A : ℝ} (hA : 0 ≤ A) {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    (hz : ∀ X w : Euc d, 1 / 32 ≤ ‖w‖ → g (X, w) = 0) (Y z : Euc d) (hz0 : z ≠ 0)
    (hzb : ∀ i, |z i| ≤ 1 / 2 + 1 / 64) :
    kPot d (ghat d s) g (Y, z) = kPot d (rieszK d s) g (Y, z) + kPot d (Lam d s) g (Y, z) := by
  have hd1 : 1 ≤ d := by omega
  have hk := locKer_riesz hd hs0 hsd
  have h1 := kPot_integrable hd1 hk hσ hA h (fun X w hw => hz X w hw.le) Y z hz0
  have h2 := Lam_mul_integrable hd hs0.le hsd hσ h Y z
  unfold kPot
  show ∫ w, ghat d s (z - w) * g (Y, w) = (∫ w, rieszK d s (z - w) * g (Y, w)) + ∫ w, Lam d s (z - w) * g (Y, w)
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  show ghat d s (z - w) * g (Y, w) = rieszK d s (z - w) * g (Y, w) + Lam d s (z - w) * g (Y, w)
  by_cases hw : ‖w‖ < 1 / 32
  · rw [← add_mul]
    congr 1
    exact ghat_split z w hzb hw
  · rw [hz Y w (not_lt.mp hw)]; simp

theorem Vi_hasFDerivAt (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {F : Torus d → Torus d → ℝ}
    {σ : ℝ} {b m : ℕ} {A : ℝ} (hA : 0 ≤ A) (hσ : σ < (d : ℝ) - 1) (hG : SrcCls d σ b (m + 1) A (Gsrc F))
    (Y z0 : Euc d) (hz0 : z0 ≠ 0) (hz0b : ∀ i, |z0 i| ≤ 1 / 2)
    (hFm : Measurable (fun u : Torus d => F u (Torus.mk Y)))
    (hFs : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Fsrc F)) {N : ℕ → ℝ}
    (hN : ∀ j ≤ m + 1, ∀ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (Fsrc F) p‖ ≤ N j) :
    ∃ D : Euc d →L[ℝ] ℝ,
      HasFDerivAt (fun z => convFun (periodicRiesz d s) (fun u => F u (Torus.mk Y)) (Torus.mk (Y + z))) D z0 ∧
      ∀ e : Euc d, D e = kPot d (rieszK d s) (dirD ((0 : Euc d), e) (Gsrc F)) (Y, z0) +
        kPot d (Lam d s) (dirD ((0 : Euc d), e) (Gsrc F)) (Y, z0) +
        farConv d s (dirD ((0 : Euc d), e) (Fsrc F)) (Y, z0) := by
  have hd1 : 1 ≤ d := by omega
  have hσd : σ < d := by linarith
  have hk := locKer_riesz hd hs0 hsd
  have hz' : ∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc F (X, w) = 0 := fun X w hw =>
    Gsrc_zero_of_ge F X w hw.le
  obtain ⟨Dα, hα, hαe⟩ := kPot_slice_deriv hd hk hσ hA hG hz' Y z0 hz0
  obtain ⟨Dβ, hβ, hβe⟩ := Lam_deriv hd hs0.le hsd hσ hA hG Y z0
  obtain ⟨Dγ, hγ, hγe⟩ := farConv_deriv hd hs0.le hsd hFs hN Y z0
  refine ⟨Dα + Dβ + Dγ, ?_, fun e => ?_⟩
  · have hsum := (hα.add hβ).add hγ
    refine hsum.congr_of_eventuallyEq ?_
    -- the identification near `z0`
    have hopen : IsOpen {z : Euc d | z ≠ 0 ∧ ∀ i, |z i| < 1 / 2 + 1 / 64} := by
      refine IsOpen.and (isOpen_ne : IsOpen {z : Euc d | z ≠ 0}) ?_
      have : {z : Euc d | ∀ i, |z i| < 1 / 2 + 1 / 64} = ⋂ i, {z : Euc d | |z i| < 1 / 2 + 1 / 64} := by
        ext z; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_lt
        (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).abs) continuous_const
    have hmem : z0 ∈ {z : Euc d | z ≠ 0 ∧ ∀ i, |z i| < 1 / 2 + 1 / 64} :=
      ⟨hz0, fun i => lt_of_le_of_lt (hz0b i) (by norm_num)⟩
    filter_upwards [hopen.mem_nhds hmem] with z hz
    obtain ⟨hzne, hzb⟩ := hz
    have hFc : Continuous (fun w : Euc d => Fsrc F (Y, w)) :=
      hFs.continuous.comp (by fun_prop)
    have hFb : ∃ N' : ℝ, ∀ w : Euc d, |Fsrc F (Y, w)| ≤ N' := by
      refine ⟨N 0, fun w => ?_⟩
      have := hN 0 (by omega) (Y, w)
      simpa [norm_iteratedFDeriv_zero] using this
    have hcs := conv_split hd hs0 hsd hA hσd hG Y z hzne (fun i => (hzb i).le) hFm hFc hFb
    have hgs := kPot_ghat_split hd hs0 hsd hσd hA hG (fun X w hw => Gsrc_zero_of_ge F X w hw) Y z hzne
      (fun i => (hzb i).le)
    simp only [Pi.add_apply]
    rw [hcs, hgs]
  · rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, hαe, hβe, hγe]

end HRS.Parx

end

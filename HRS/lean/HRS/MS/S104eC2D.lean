import HRS.MS.S104eC2B

/-!
# S104E route C, packet C2, part D: vanishing at infinity, identification with `movForce`, differentiation of `ultK` on Hölder data

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.

* `s104c2_K_van`: `ultK κ g x → 0` along `cocompact` for `g` continuous, Hölder near, with weighted decay;
* `s104c2_conv_comp`: `convGradConvW (rieszKernelGrad d s) g x i = ultK (u2_kap d s i) g x` for such `g` (and the integrand is integrable);
* `s104c2_K_iter`: `D^m (ultK κ k) = ultK κ (D^m k)`, `ultK κ k ∈ C^j`, for `k ∈ U2Dec j L A` with all `D^m k` (`m ≤ j`) Hölder near.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

lemma s104c2_cocompact_cg : (cocompact (Euc d)).IsCountablyGenerated := by
  have : cocompact (Euc d) = comap norm atTop := by
    exact (Metric.cobounded_eq_cocompact (α := Euc d)).symm.trans (comap_norm_atTop (E := Euc d)).symm
  rw [this]
  infer_instance

lemma s104c2_near_van (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {g : Euc d → F} (hg : Continuous g) (hh : HolNear η H g)
    (hv : Tendsto g (cocompact (Euc d)) (𝓝 0)) :
    Tendsto (ultNear κ g) (cocompact (Euc d)) (𝓝 0) := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  haveI := s104c2_cocompact_cg (d := d)
  have hmain := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := cocompact (Euc d))
    (F := fun x z => ultKN κ z • (g (x - z) - g x)) (f := fun _ => (0 : F))
    (bound := fun z => C0 * H * s104c2_Psi d s η z)
    (Filter.Eventually.of_forall fun x => ult_near_meas hK.meas hg x) ?_
    ((s104c2_Psi_int hd hK.hs0 hη1 hηd).const_mul (C0 * H)) ?_
  · have h0 : (∫ _ : Euc d, (0 : F)) = 0 := by simp
    rw [h0] at hmain
    exact hmain
  · refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [u2_ae_ne_zero hd] with z hz
    refine s104c2_near_dom hC0 hb hH hz (fun h1 => ?_)
    have := hh (x - z) x (by simpa using h1)
    simpa using this
  · refine Filter.Eventually.of_forall fun z => ?_
    have h1 : Tendsto (fun x : Euc d => g (x - z)) (cocompact (Euc d)) (𝓝 0) :=
      hv.comp ((Homeomorph.subRight z).isClosedEmbedding.tendsto_cocompact)
    simpa using (h1.sub hv).const_smul (ultKN κ z)

lemma s104c2_wt_van {L A0 : ℝ} (hL : 0 < L) :
    Tendsto (fun y : Euc d => A0 * u2Wt L y) (cocompact (Euc d)) (𝓝 0) := by
  have h1 : Tendsto (fun y : Euc d => 1 + ‖y‖) (cocompact (Euc d)) atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_norm_cocompact_atTop
  have := (tendsto_rpow_neg_atTop hL).comp h1
  simpa [u2Wt] using this.const_mul A0

lemma s104c2_K_van (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {L : ℝ} (hL : (d : ℝ) < L) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {g : Euc d → F} (hg : Continuous g) (hh : HolNear η H g) {A0 : ℝ}
    (hA0 : 0 ≤ A0) (hb : ∀ y, ‖g y‖ ≤ A0 * u2Wt L y) :
    Tendsto (ultK κ g) (cocompact (Euc d)) (𝓝 0) := by
  have hLp : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg d) hL
  have hv : Tendsto g (cocompact (Euc d)) (𝓝 0) :=
    squeeze_zero_norm hb (s104c2_wt_van hLp)
  have h1 := s104c2_near_van hd hK hη1 hηd hH hg hh hv
  have h2 := s104c2_far_van hd hK hL hg hA0 hb
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3

lemma s104c2_conv_comp (hd : 1 ≤ d) {s η H : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {L A0 : ℝ} (hL : (d : ℝ) < L) (hA : 0 ≤ A0)
    {h : Euc d → ℝ} (hc : Continuous h) (hh : HolNear η H h) (hb : ∀ y, ‖h y‖ ≤ A0 * u2Wt L y)
    (x : Euc d) :
    Integrable (ultInt s h x) volume ∧
      ∀ i : Fin d, convGradConvW (rieszKernelGrad d s) h x i = ultK (u2_kap d s i) h x := by
  have hker := fun i : Fin d => ult_ker_kap hs0 hsd i
  have hF : ∀ (i : Fin d) (y : Euc d), ultInt s h x y i =
      (fun z => ultKN (u2_kap d s i) z • (h (x - z) - h x) +
        ultKF (u2_kap d s i) z • h (x - z)) (x - y) := by
    intro i y
    simp only [sub_sub_cancel, ultInt, ultKN, ultKF, u2_kap]
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · simp only [if_pos hy, PiLp.smul_apply, smul_eq_mul, zero_smul, add_zero]; ring
    · simp only [if_neg hy, PiLp.smul_apply, smul_eq_mul, zero_smul, zero_add]; ring
  have hnf : ∀ i : Fin d, Integrable (fun z => ultKN (u2_kap d s i) z • (h (x - z) - h x)) volume ∧
      Integrable (fun z => ultKF (u2_kap d s i) z • h (x - z)) volume := fun i =>
    ⟨s104c2_near_integrable hd (hker i) hη1 hηd hH hc hh x,
      u2_conv_integrable (ult_far_U2Ker hd (hker i)) hL hc hA hb x⟩
  have hint : ∀ i : Fin d, Integrable (fun y => ultInt s h x y i) volume := by
    intro i
    obtain ⟨n, f⟩ := hnf i
    have := (n.add f).comp_sub_left x
    exact this.congr (Filter.Eventually.of_forall fun y => (hF i y).symm)
  have hI : Integrable (ultInt s h x) volume :=
    u2_integrable_of_coord (ult_int_meas s hc x) hint
  refine ⟨hI, fun i => ?_⟩
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) hI
  rw [ult_conv_unfold]
  have e1 : (∫ y, ultInt s h x y) i = ∫ y, ultInt s h x y i := by simpa using this.symm
  rw [e1]
  simp only [hF i]
  rw [integral_sub_left_eq_self (fun z => ultKN (u2_kap d s i) z • (h (x - z) - h x) +
    ultKF (u2_kap d s i) z • h (x - z)) volume x]
  obtain ⟨n, f⟩ := hnf i
  rw [integral_add n f]
  rfl

theorem s104c2_K_iter (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {L A : ℝ} (hL : (d : ℝ) < L) (hA : 0 ≤ A) {j : ℕ}
    {k : Euc d → ℝ} (hdec : U2Dec j L A k) (hh : ∀ m ≤ j, HolNear η H (iteratedFDeriv ℝ m k)) :
    (∀ m ≤ j, ∀ x, iteratedFDeriv ℝ m (ultK κ k) x = ultK κ (iteratedFDeriv ℝ m k) x) ∧
      ContDiff ℝ j (ultK κ k) := by
  obtain ⟨hnf, hnc⟩ := s104c2_near_iter hd hK hη1 hηd hH hdec.1 hh
  obtain ⟨hff, hfc⟩ := u2_conv_iter (ult_far_U2Ker hd hK) hL hA hdec
  refine ⟨fun m hm x => ?_, ?_⟩
  · have hsum : ultK κ k = ultNear κ k + u2Conv (ultKF κ) k := rfl
    have hmk : (m : ℕ∞ω) ≤ (j : ℕ∞ω) := by exact_mod_cast hm
    rw [hsum]
    rw [iteratedFDeriv_add_apply ((hnc.of_le hmk).contDiffAt) ((hfc.of_le hmk).contDiffAt),
      hnf m hm x, hff m hm x]
    rfl
  · exact hnc.add hfc

end HRS.MS.S104e.C

end

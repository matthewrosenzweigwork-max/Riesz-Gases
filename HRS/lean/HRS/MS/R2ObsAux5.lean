import HRS.MS.R2ObsAux4
import HRS.MS.R2SeAux12

/-!
# S9.10 path row, packet 5: the covariance of a series of observables

Worker S910, namespace `HRS.MS.R2Obs`.  `μ = thermalMeasure`, `a_ψ = aRep ψ` (the continuous representative of the response).

* `s910_resp_spec`: for `ψ ∈ C_b^{J1}` the function `a_ψ` is continuous and an `IsResponse`;
* `s910_resInv_ae`, `s910_susc_eq`: `HRS.Whole.responseInverse ψ = a_ψ` `μ`-a.e. and `C(φ,ψ) = ∫ (φ - μφ) a_ψ dμ`;
* `s910_hasSum_mul`: termwise integration of a pointwise-bounded series against a bounded continuous function;
* `s910_susc_series`: `C(∑ c_n f_n, ∑ c'_m f'_m) = ∑_n c_n ∑_m c'_m C(f_n, f'_m)`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

section Spec

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ)

include hd hs0 hsd ha hβ hγ

theorem s910_resp_spec {ψ : Euc d → ℝ} (hψ : MemCb (J1 d) ψ) :
    Continuous (aRep d s a β γ ψ) ∧
      HRS.Whole.IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ ψ (aRep d s a β γ ψ) := by
  obtain ⟨K, hK0, hK⟩ := s99_chi hd hs0 hsd (k0 d) (k0_ge_one d) a β γ ha hβ hγ (J1 d) (k0_lt_J1 d)
  obtain ⟨χ, -, -, -, hresp, hmem, -⟩ := hK ψ hψ
  exact ⟨hmem.1.continuous, hresp⟩

theorem s910_resInv_ae {ψ : Euc d → ℝ} (hψ : MemCb (J1 d) ψ) :
    HRS.Whole.responseInverse (rieszKernel d s) (thermalMeasure d s a β) γ ψ =ᵐ[thermalMeasure d s a β]
      aRep d s a β γ ψ := by
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β)
    (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hSρ⟩ := hU 0
  have hTc := hSρ a β le_rfl le_rfl le_rfl le_rfl
  have hr := (s910_resp_spec hd hs0 hsd ha hβ hγ hψ).2
  have hex : ∃ h, HRS.Whole.IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ ψ h := ⟨_, hr⟩
  have hch := hex.choose_spec
  have hae := HRS.MS.S98.s98_resp_unique (by omega : 1 ≤ d) hs0 hsd hc₀ hTc hγ hch hr
  unfold HRS.Whole.responseInverse
  rw [dif_pos hex]
  exact hae

theorem s910_susc_eq {ψ : Euc d → ℝ} (hψ : MemCb (J1 d) ψ) (φ : Euc d → ℝ) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ φ ψ =
      ∫ x, (φ x - ∫ y, φ y ∂(thermalMeasure d s a β)) * aRep d s a β γ ψ x ∂(thermalMeasure d s a β) := by
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  refine integral_congr_ae ?_
  filter_upwards [s910_resInv_ae hd hs0 hsd ha hβ hγ hψ] with x hx
  rw [hx]
  simp [HRS.Whole.projMean, HRS.Whole.pair]

end Spec

theorem s910_hasSum_mul {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {F : ℕ → Euc d → ℝ}
    (hF : ∀ n, Continuous (F n)) {b : ℕ → ℝ} (hb : Summable b) (hFb : ∀ n x, |F n x| ≤ b n)
    {h : Euc d → ℝ} (hh : Continuous h) {Bh : ℝ} (hhb : ∀ x, |h x| ≤ Bh) (hsum : ∀ x, Summable fun n => F n x) :
    HasSum (fun n => ∫ x, F n x * h x ∂μ) (∫ x, (∑' n, F n x) * h x ∂μ) := by
  have hBh : 0 ≤ Bh := (abs_nonneg _).trans (hhb 0)
  have hb' : Summable fun n => b n * Bh := hb.mul_right Bh
  have hbd : ∀ n x, |F n x * h x| ≤ b n * Bh := fun n x => by
    rw [abs_mul]
    exact mul_le_mul (hFb n x) (hhb x) (abs_nonneg _) ((abs_nonneg _).trans (hFb n x))
  have h1 := s99_integral_tsum (μ := μ) (F := fun n x => F n x * h x) hb'
    (fun n => ((hF n).mul hh).aestronglyMeasurable) hbd
  have hint : ∀ n, Integrable (fun x => F n x * h x) μ := fun n =>
    Integrable.of_bound ((hF n).mul hh).aestronglyMeasurable (b n * Bh)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd n x)
  have hsm : Summable fun n => ∫ x, F n x * h x ∂μ := by
    refine Summable.of_norm_bounded hb' (fun n => ?_)
    rw [Real.norm_eq_abs]
    calc |∫ x, F n x * h x ∂μ| ≤ ∫ x, |F n x * h x| ∂μ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => F n x * h x)
      _ ≤ ∫ _x, b n * Bh ∂μ := integral_mono (hint n).abs (integrable_const _) (fun x => hbd n x)
      _ = b n * Bh := by simp
  have e : ∫ x, (∑' n, F n x) * h x ∂μ = ∫ x, ∑' n, F n x * h x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only
      rw [tsum_mul_right])
  rw [e, ← h1]
  exact hsm.hasSum

/-- `∫ ∑ F_n = ∑ ∫ F_n` (the case `h = 1`). -/
theorem s910_hasSum_int {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {F : ℕ → Euc d → ℝ}
    (hF : ∀ n, Continuous (F n)) {b : ℕ → ℝ} (hb : Summable b) (hFb : ∀ n x, |F n x| ≤ b n)
    (hsum : ∀ x, Summable fun n => F n x) :
    HasSum (fun n => ∫ x, F n x ∂μ) (∫ x, ∑' n, F n x ∂μ) := by
  have := s910_hasSum_mul (μ := μ) hF hb hFb (h := fun _ => (1 : ℝ)) continuous_const (Bh := 1)
    (fun _ => by simp) hsum
  simpa using this

section Series

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ)

include hd hs0 hsd ha hβ hγ

/-- The covariance of two series of observables is the iterated series of the covariances. -/
theorem s910_susc_series {f f' : ℕ → Euc d → ℝ} (hf : ∀ n, MemCb (J1 d) (f n))
    (hsum : Summable fun n => cbNorm (J1 d) (f n)) (hf' : ∀ n, MemCb (J1 d) (f' n))
    (hsum' : Summable fun n => cbNorm (J1 d) (f' n)) (c c' : ℕ → ℝ) {B : ℝ} (hB : ∀ n, |c n| ≤ B)
    (hB' : ∀ n, |c' n| ≤ B) {g g' : Euc d → ℝ} (hg : ∀ x, HasSum (fun n => c n * f n x) (g x))
    (hg' : ∀ x, HasSum (fun n => c' n * f' n x) (g' x)) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ g g' =
      ∑' n, c n * ∑' m, c' m * HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (f n) (f' m) := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) := by
    obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β)
      (βp := β) ha hβ le_rfl le_rfl
    obtain ⟨S, hS0, hSρ⟩ := hU 0
    exact HRS.Whole.Q34.isProbabilityMeasure_nu (hSρ a β le_rfl le_rfl le_rfl le_rfl).prob
  set μ := thermalMeasure d s a β with hμdef
  obtain ⟨K, hK0, hK⟩ := s910_resp_sup hd hs0 hsd ha hβ hγ
  obtain ⟨hg0, hAg'⟩ := s910_resp_series hd hs0 hsd ha hβ hγ hf' hsum' c' hB' hg'
  obtain ⟨hg0', -⟩ := s910_resp_series hd hs0 hsd ha hβ hγ hf hsum c hB hg
  set w : ℕ → ℝ := fun n => cbNorm (J1 d) (f n) with hw
  set w' : ℕ → ℝ := fun n => cbNorm (J1 d) (f' n) with hw'
  have hw0 : ∀ n, 0 ≤ w n := fun n => HRS.MS.Tc5.tc5_cb_nonneg (J1 d) (f n)
  have hw0' : ∀ n, 0 ≤ w' n := fun n => HRS.MS.Tc5.tc5_cb_nonneg (J1 d) (f' n)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hfb : ∀ n x, |f n x| ≤ w n := fun n x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hf n) x
    rwa [Real.norm_eq_abs] at this
  have hfb' : ∀ n x, |f' n x| ≤ w' n := fun n x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hf' n) x
    rwa [Real.norm_eq_abs] at this
  have hfc : ∀ n, Continuous (f n) := fun n => (hf n).1.continuous
  have hfc' : ∀ n, Continuous (f' n) := fun n => (hf' n).1.continuous
  -- the mean of `g`
  have hmeanf : ∀ n, |∫ y, f n y ∂μ| ≤ w n := fun n => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := f n) (C := w n)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfb n y)
    simpa [Real.norm_eq_abs, Measure.real] using this
  have hmean : HasSum (fun n => c n * ∫ y, f n y ∂μ) (∫ y, g y ∂μ) := by
    have h1 := s910_hasSum_int (μ := μ) (F := fun n y => c n * f n y) (b := fun n => B * w n)
      (fun n => continuous_const.mul (hfc n)) (hsum.mul_left B)
      (fun n x => by
        rw [abs_mul]; exact mul_le_mul (hB n) (hfb n x) (abs_nonneg _) hB0)
      (fun x => (hg x).summable)
    have e : ∫ x, ∑' n, c n * f n x ∂μ = ∫ x, g x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => (hg x).tsum_eq)
    rw [e] at h1
    convert h1 using 2 with n
    rw [integral_const_mul]
  -- the centred series
  have hcent : ∀ x, HasSum (fun n => c n * (f n x - ∫ y, f n y ∂μ)) (g x - ∫ y, g y ∂μ) := fun x => by
    have := (hg x).sub hmean
    convert this using 2 with n
    ring
  set P : ℕ → Euc d → ℝ := fun n x => c n * (f n x - ∫ y, f n y ∂μ) with hP
  have hPc : ∀ n, Continuous (P n) := fun n =>
    continuous_const.mul ((hfc n).sub continuous_const)
  have hPb : ∀ n x, |P n x| ≤ B * (2 * w n) := fun n x => by
    simp only [hP]
    rw [abs_mul]
    refine mul_le_mul (hB n) ((abs_sub _ _).trans ?_) (abs_nonneg _) hB0
    linarith [hfb n x, hmeanf n]
  have hAc : Continuous (aRep d s a β γ g') := (s910_resp_spec hd hs0 hsd ha hβ hγ hg0).1
  have hAb : ∀ x, |aRep d s a β γ g' x| ≤ K * cbNorm (J1 d) g' := hK g' hg0
  -- the first sum
  have hs1 := s910_hasSum_mul (μ := μ) (F := P) hPc ((hsum.mul_left 2).mul_left B) hPb hAc hAb
    (fun x => (hcent x).summable)
  have hterm : ∀ n, ∫ x, P n x * aRep d s a β γ g' x ∂μ =
      c n * ∑' m, c' m * HRS.Whole.susceptibilityCov (rieszKernel d s) μ γ (f n) (f' m) := by
    intro n
    have hF' : ∀ m, Continuous fun x => c' m * aRep d s a β γ (f' m) x := fun m =>
      continuous_const.mul (s910_resp_spec hd hs0 hsd ha hβ hγ (hf' m)).1
    have hFb' : ∀ m x, |c' m * aRep d s a β γ (f' m) x| ≤ (B * K) * w' m := fun m x => by
      rw [abs_mul]
      calc |c' m| * |aRep d s a β γ (f' m) x| ≤ B * (K * w' m) :=
            mul_le_mul (hB' m) (hK (f' m) (hf' m) x) (abs_nonneg _) hB0
        _ = (B * K) * w' m := by ring
    have h2 := s910_hasSum_mul (μ := μ) (F := fun m x => c' m * aRep d s a β γ (f' m) x) hF'
      (hsum'.mul_left (B * K)) hFb' (hPc n) (hPb n) (fun x => (hAg' x).summable)
    have e1 : ∫ x, P n x * aRep d s a β γ g' x ∂μ =
        ∫ x, (∑' m, c' m * aRep d s a β γ (f' m) x) * P n x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only
        rw [(hAg' x).tsum_eq, mul_comm])
    have e2 : ∀ m, ∫ x, (c' m * aRep d s a β γ (f' m) x) * P n x ∂μ =
        c n * (c' m * HRS.Whole.susceptibilityCov (rieszKernel d s) μ γ (f n) (f' m)) := fun m => by
      rw [s910_susc_eq hd hs0 hsd ha hβ hγ (hf' m) (f n)]
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hP]
      ring
    rw [e1, ← h2.tsum_eq]
    simp_rw [e2]
    rw [tsum_mul_left]
  have hsusc := s910_susc_eq hd hs0 hsd ha hβ hγ hg0 g
  have e3 : ∫ x, (g x - ∫ y, g y ∂μ) * aRep d s a β γ g' x ∂μ =
      ∫ x, (∑' n, P n x) * aRep d s a β γ g' x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only
      rw [(hcent x).tsum_eq])
  rw [hsusc, e3, ← hs1.tsum_eq]
  exact tsum_congr hterm

end Series

end HRS.MS.R2Obs

end

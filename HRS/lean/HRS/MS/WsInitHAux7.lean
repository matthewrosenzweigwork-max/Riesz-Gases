import HRS.MS.WsInitHAux6
import HRS.MS.QsfOsc7
import HRS.MS.QsfAsm11
import HRS.MS.SharpCritAux2

/-!
# S21H packet H, part 7: coordinate second moments of the Gaussian and of the particle feature law

For the thermal reference `μ = μ_{a,β}` and a summable feature family `φ ⊂ C_b^J` (sup norms `B_k = ‖φ_k‖_{C_b^J}`):

* `s21h_cov_le`: `C_{β,μ}(f, f) ≤ 4 B²` when `|f| ≤ B` (`C = ⟨P f, R P f⟩ ≤ ‖P f‖² ≤ 4B²`, `R = (I+βK)^{-1}` a contraction);
* `s21h_gauss_coord`: `∫⁻ z_k² dγ ≤ 4 B_k²` for a centred Gaussian `γ` on `ℓ²` with the susceptibility covariance;
* `s21h_particle_coord`: `∫⁻ v_k² d(law_P featureVec φ m_N) ≤ C_s B_k²` (calibrated linear variance bound `N Var μ_N(f) ≤ C_s ‖f‖²_{L²(μ)}`,
  exact centring at the first marginal `m_N`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21h_cov_le (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {f : Euc d → ℝ} (hf : MemLp f 2 (thermalMeasure d s a β)) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β f f ≤ 4 * B ^ 2 := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hd1 : 1 ≤ d := by omega
  have : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β),
      S45.IsKData (thermalMeasure d s a β) (rieszKernel d s) K :=
    S45.s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  rw [S45.s45_susceptibilityCov_eq hK hβ hf hf]
  refine (S45.s45_inner_Rr_le hK hβ.le _).trans ?_
  have h := S45.s45_U_norm_le hf hB
  have h0 := norm_nonneg (S45.s45_U f hf)
  nlinarith

theorem s21h_gauss_coord (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) {γ : Measure SeqL2}
    (hγ : IsCenteredGaussianSeq γ fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (φ i) (φ j)) (k : ℕ) :
    ∫⁻ z, ENNReal.ofReal (SeqL2.coord z k ^ 2) ∂γ ≤ ENNReal.ofReal (4 * cbNorm J (φ k) ^ 2) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨hi, hv⟩ := hγ.2 k k
  have hmem : MemLp (φ k) 2 (thermalMeasure d s a β) := HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 k)
  have hcov := s21h_cov_le hd hs0 hsd ha hβ hmem (fun x => HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x)
  have hnn : ∀ z : SeqL2, 0 ≤ SeqL2.coord z k * SeqL2.coord z k := fun z => mul_self_nonneg _
  have e : ∫⁻ z, ENNReal.ofReal (SeqL2.coord z k ^ 2) ∂γ =
      ENNReal.ofReal (∫ z, SeqL2.coord z k * SeqL2.coord z k ∂γ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn)]
    exact lintegral_congr fun z => by rw [sq]
  rw [e]
  exact ENNReal.ofReal_le_ofReal (hv.le.trans hcov)


theorem s21h_particle_coord (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) (hC : 0 ≤ C) (hS : S45.S45Static d s a β C N)
    {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (k : ℕ) :
    ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
        (featureVec φ (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) ≤
      ENNReal.ofReal (C * cbNorm J (φ k) ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  set P := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hP
  haveI : IsProbabilityMeasure P := hS.prob
  haveI hν : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := S45.s45_nu_prob hN hS.prob
  have hfm : Measurable (featureVec φ (HRS.Whole.firstMarginal P) : EucConfig d N → SeqL2) :=
    S45.s45_feature_measurable hN1 hφ
  obtain ⟨C0, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  haveI hthp : IsProbabilityMeasure (thermalMeasure d s a β) := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set f := φ k with hf
  set B := cbNorm J f with hB
  have hfb : ∀ x, |f x| ≤ B := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x
    rwa [Real.norm_eq_abs] at this
  have hfm2 : MemLp f 2 (thermalMeasure d s a β) := HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 k)
  have hfmeas : Measurable f := (hφ.1 k).1.continuous.measurable
  have hlin := hS.linear f hfm2
  have hmeas : Measurable fun v : SeqL2 => ENNReal.ofReal (SeqL2.coord v k ^ 2) :=
    ENNReal.measurable_ofReal.comp ((s21h_continuous_coord k).pow 2).measurable
  rw [lintegral_map hmeas hfm]
  have hEl : ∫ X, linStat f X ∂P = HRS.Whole.pair (HRS.Whole.firstMarginal P) f :=
    HRS.Whole.S78.s78_integral_linStat hN1 hS.exch hfmeas hfb
  have hcoord : ∀ X : EucConfig d N, SeqL2.coord (featureVec φ (HRS.Whole.firstMarginal P) X) k =
      Real.sqrt N * (linStat f X - ∫ X', linStat f X' ∂P) := by
    intro X
    unfold featureVec
    rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN1 hφ X), hEl]
    rfl
  have hev : ∀ X : EucConfig d N, ENNReal.ofReal (SeqL2.coord (featureVec φ (HRS.Whole.firstMarginal P) X) k ^ 2) =
      ENNReal.ofReal N * ‖linStat f X - ∫ X', linStat f X' ∂P‖ₑ ^ 2 := by
    intro X
    rw [hcoord, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    congr 1
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [hev]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hlin' : ∫⁻ X, ‖linStat f X - ∫ X', linStat f X' ∂P‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(thermalMeasure d s a β)) := hlin
  refine (mul_le_mul' le_rfl hlin').trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hI : ∫ x, f x ^ 2 ∂(thermalMeasure d s a β) ≤ B ^ 2 := by
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfb 0)
    calc ∫ x, f x ^ 2 ∂(thermalMeasure d s a β) ≤ ∫ _x, B ^ 2 ∂(thermalMeasure d s a β) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_const _)
            (ae_of_all _ fun x => ?_)
          exact (sq_abs (f x)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2)
      _ = B ^ 2 := by simp
  rw [← ENNReal.ofReal_mul hN0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (N : ℝ) * (C / N * ∫ x, f x ^ 2 ∂(thermalMeasure d s a β)) = C * ∫ x, f x ^ 2 ∂(thermalMeasure d s a β) := by
        field_simp
    _ ≤ C * B ^ 2 := mul_le_mul_of_nonneg_left hI hC

end HRS.MS.S21

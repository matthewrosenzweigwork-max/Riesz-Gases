import HRS.Sections.QuenchAux9

/-!
# Packet QUENCH (Q27), part 10: the process `B = (G + λ∫G)/σ` is Brownian

Law of finite combinations `c₀ Y + ∑ c_i B_{t_i}` (`bm_combo_law`), then: `B` is a Gaussian process with the
Brownian covariance, `(Y, B)` jointly Gaussian with `Cov(Y, B_t) = 0`; consequently `B` is a pre-Brownian motion
and independent of `Y`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

section BMmain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

/-- `B_t = (G_t + λ∫_0^t G)/σ`. -/
def bmProc (lam σ : ℝ) (G : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (G t ω + lam * ∫ u in Set.Icc (0 : ℝ) t, G u ω) / σ

lemma bm_combo_lim (hN : OUNoise lam v vY P Y G) {σ : ℝ} {ι : Type*} [Fintype ι] (ts : ι → ℝ)
    (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ) (c₀ : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Vapp lam σ G Y ts c c₀ m ω) atTop
      (𝓝 (c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω)) := by
  filter_upwards [hN.cont, hN.zero] with ω hc h0
  unfold Vapp
  refine (tendsto_const_nhds.add (tendsto_finset_sum _ fun i _ => ?_))
  refine Tendsto.const_mul _ ?_
  unfold bmProc
  have := (xi_sum_tendsto G ω lam hc h0 (hts i)).const_mul (1 / σ)
  simpa [div_eq_inv_mul] using this

lemma bm_combo_aemeas (hN : OUNoise lam v vY P Y G) {σ : ℝ} {ι : Type*} [Fintype ι] (ts : ι → ℝ)
    (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ) (c₀ : ℝ) :
    AEMeasurable (fun ω => c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω) P :=
  aemeasurable_of_tendsto_metrizable_ae atTop
    (fun m => (Vapp_gauss hN (σ := σ) ts hts c c₀ m).aemeasurable) (bm_combo_lim hN ts hts c c₀)

lemma limit_nonneg (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ)
    (c₀ : ℝ) : 0 ≤ c₀ ^ 2 * vY + ∑ i, ∑ i', c i * c i' * min (ts i) (ts i') := by
  refine ge_of_tendsto (tendsto_vApp hlam vY ts hts c c₀) (Eventually.of_forall fun m => ?_)
  rw [← Vapp_sq_eq hN hv hlam hσ ts c c₀ m]
  exact integral_nonneg fun ω => sq_nonneg _

theorem bm_combo_law (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ)
    (c₀ : ℝ) :
    P.map (fun ω => c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω) =
      gaussianReal 0 (c₀ ^ 2 * vY + ∑ i, ∑ i', c i * c i' * min (ts i) (ts i')).toNNReal := by
  have hVm : ∀ m, AEMeasurable (Vapp lam σ G Y ts c c₀ m) P := fun m =>
    (Vapp_gauss hN (σ := σ) ts hts c c₀ m).aemeasurable
  refine gauss_limit P (V := fun m => Vapp lam σ G Y ts c c₀ m) (v := fun m => (vApp lam vY ts c c₀ m).toNNReal)
    (fun m => Vapp_law hN hv hlam hσ ts hts c c₀ m) ?_ (bm_combo_lim hN ts hts c c₀)
    (bm_combo_aemeas (σ := σ) hN ts hts c c₀) hVm
  exact (continuous_real_toNNReal.tendsto _).comp (tendsto_vApp hlam vY ts hts c c₀)

theorem bm_combo_gauss (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ)
    (c₀ : ℝ) :
    HasGaussianLaw (fun ω => c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω) P := by
  haveI : IsGaussian (P.map (fun ω => c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω)) := by
    rw [bm_combo_law hN hv hlam hσ ts hts c c₀]; infer_instance
  exact IsGaussian.hasGaussianLaw (bm_combo_aemeas (σ := σ) hN ts hts c c₀)

theorem bm_combo_mean (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ)
    (c₀ : ℝ) : ∫ ω, (c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω) ∂P = 0 := by
  have h := integral_map (bm_combo_aemeas (σ := σ) hN ts hts c c₀) (f := fun x : ℝ => x)
    aestronglyMeasurable_id
  rw [bm_combo_law hN hv hlam hσ ts hts c c₀, integral_id_gaussianReal] at h
  exact h.symm

theorem bm_combo_sq (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) {ι : Type*} [Fintype ι] (ts : ι → ℝ) (hts : ∀ i, 0 ≤ ts i) (c : ι → ℝ)
    (c₀ : ℝ) : ∫ ω, (c₀ * Y ω + ∑ i, c i * bmProc lam σ G (ts i) ω) ^ 2 ∂P =
      c₀ ^ 2 * vY + ∑ i, ∑ i', c i * c i' * min (ts i) (ts i') := by
  have h := integral_map (bm_combo_aemeas (σ := σ) hN ts hts c c₀) (f := fun x : ℝ => x ^ 2)
    (by fun_prop)
  rw [bm_combo_law hN hv hlam hσ ts hts c c₀] at h
  rw [← h]
  have hn := limit_nonneg hN hv hlam hσ ts hts c c₀
  rw [integral_sq_gaussianReal_zero]
  simp [Real.coe_toNNReal _ hn]

variable (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ} (hσ : σ ^ 2 = 2 * lam * v)
include hN hv hlam hσ

lemma bm_single_gauss {t : ℝ} (ht : 0 ≤ t) : HasGaussianLaw (bmProc lam σ G t) P := by
  have := bm_combo_gauss hN hv hlam hσ (ι := Unit) (fun _ => t) (fun _ => ht) (fun _ => 1) 0
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp

lemma bm_single_sq {t : ℝ} (ht : 0 ≤ t) : ∫ ω, bmProc lam σ G t ω ^ 2 ∂P = t := by
  have := bm_combo_sq hN hv hlam hσ (ι := Unit) (fun _ => t) (fun _ => ht) (fun _ => 1) 0
  simpa using this

lemma bm_single_mean {t : ℝ} (ht : 0 ≤ t) : ∫ ω, bmProc lam σ G t ω ∂P = 0 := by
  have := bm_combo_mean hN hv hlam hσ (ι := Unit) (fun _ => t) (fun _ => ht) (fun _ => 1) 0
  simpa using this

lemma bm_cov_BB {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, bmProc lam σ G s ω * bmProc lam σ G t ω ∂P = s := by
  have ht : 0 ≤ t := hs.trans hst
  have h := bm_combo_sq hN hv hlam hσ (ι := Fin 2) ![s, t] (by intro i; fin_cases i <;> simp [hs, ht])
    ![1, 1] 0
  simp only [Fin.sum_univ_two, zero_pow two_ne_zero, zero_mul, zero_add, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, mul_one, zero_mul] at h
  have h1 := (bm_single_gauss hN hv hlam hσ hs).memLp_two
  have h2 := (bm_single_gauss hN hv hlam hσ ht).memLp_two
  have e : ∀ ω, (bmProc lam σ G s ω + bmProc lam σ G t ω) ^ 2 =
      bmProc lam σ G s ω ^ 2 + 2 * (bmProc lam σ G s ω * bmProc lam σ G t ω) + bmProc lam σ G t ω ^ 2 := by
    intro ω; ring
  have i1 : Integrable (fun ω => bmProc lam σ G s ω ^ 2) P := by
    have : Integrable (fun ω => bmProc lam σ G s ω * bmProc lam σ G s ω) P := h1.integrable_mul h1
    simpa [sq] using this
  have i2 : Integrable (fun ω => bmProc lam σ G t ω ^ 2) P := by
    have : Integrable (fun ω => bmProc lam σ G t ω * bmProc lam σ G t ω) P := h2.integrable_mul h2
    simpa [sq] using this
  have i3 : Integrable (fun ω => 2 * (bmProc lam σ G s ω * bmProc lam σ G t ω)) P :=
    (h1.integrable_mul h2).const_mul 2
  simp_rw [e] at h
  rw [integral_add (f := fun ω => bmProc lam σ G s ω ^ 2 + 2 * (bmProc lam σ G s ω * bmProc lam σ G t ω))
      (g := fun ω => bmProc lam σ G t ω ^ 2) (i1.add i3) i2,
    integral_add (f := fun ω => bmProc lam σ G s ω ^ 2)
      (g := fun ω => 2 * (bmProc lam σ G s ω * bmProc lam σ G t ω)) i1 i3, integral_const_mul,
    bm_single_sq hN hv hlam hσ hs, bm_single_sq hN hv hlam hσ ht] at h
  simp only [min_self, min_eq_left hst, min_eq_right hst] at h
  linarith

lemma bm_cov_YB {t : ℝ} (ht : 0 ≤ t) : ∫ ω, Y ω * bmProc lam σ G t ω ∂P = 0 := by
  have h := bm_combo_sq hN hv hlam hσ (ι := Unit) (fun _ => t) (fun _ => ht) (fun _ => 1) 1
  simp only [Finset.univ_unique, Finset.sum_singleton, one_pow, one_mul, mul_one] at h
  have h1 := (bm_single_gauss hN hv hlam hσ ht).memLp_two
  have h2 := hN.memLpY
  have e : ∀ ω, (Y ω + bmProc lam σ G t ω) ^ 2 =
      Y ω ^ 2 + 2 * (Y ω * bmProc lam σ G t ω) + bmProc lam σ G t ω ^ 2 := by
    intro ω; ring
  have i1 : Integrable (fun ω => Y ω ^ 2) P := by
    have : Integrable (fun ω => Y ω * Y ω) P := h2.integrable_mul h2
    simpa [sq] using this
  have i2 : Integrable (fun ω => bmProc lam σ G t ω ^ 2) P := by
    have : Integrable (fun ω => bmProc lam σ G t ω * bmProc lam σ G t ω) P := h1.integrable_mul h1
    simpa [sq] using this
  have i3 : Integrable (fun ω => 2 * (Y ω * bmProc lam σ G t ω)) P :=
    (h2.integrable_mul h1).const_mul 2
  simp_rw [e] at h
  rw [integral_add (f := fun ω => Y ω ^ 2 + 2 * (Y ω * bmProc lam σ G t ω))
      (g := fun ω => bmProc lam σ G t ω ^ 2) (i1.add i3) i2,
    integral_add (f := fun ω => Y ω ^ 2)
      (g := fun ω => 2 * (Y ω * bmProc lam σ G t ω)) i1 i3, integral_const_mul,
    bm_single_sq hN hv hlam hσ ht] at h
  have hY2 : ∫ ω, Y ω ^ 2 ∂P = vY := by
    rw [← hN.covYY]; simp [sq]
  rw [hY2] at h
  simp only [min_self] at h
  linarith

end BMmain

end Qch

end HRS

import HRS.MS.ShiftFldAux27

/-!
# S79P: stationarity of the covariance of the Gaussian field on Hermite tests
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_noise_comm (s a β : ℝ) (q τ τ' : ℝ) (φ ψ : Euc d → ℝ) :
    noiseCovW (Cst d s a β) q τ τ' φ ψ = noiseCovW (Cst d s a β) q τ' τ ψ φ := by
  unfold noiseCovW
  rw [min_comm]
  congr 2
  funext r
  congr 1
  funext x
  rw [real_inner_comm]

theorem s79g_cov_comm (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {f g : Euc d → ℝ} (hf : HRS.MemCb 2 f) (hg : HRS.MemCb 2 g) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β f g =
      HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β g f := by
  haveI := s79g_prob hd hs0 hsd ha hβ
  obtain ⟨K, hK⟩ := s79g_kdata hd hs0 hsd ha hβ
  have hmem : ∀ {f : Euc d → ℝ}, HRS.MemCb 2 f → MemLp f 2 (thermalMeasure d s a β) := by
    intro f hf
    obtain ⟨f0, f1, f2, hf0, -, -, hb0, -, -⟩ := s79g_memcb_bounds hf
    exact s79g_memLp_lin hd hs0 hsd ha hβ hf.1.continuous (K := f0) (fun x => s79g_lin_of_le (hb0 x) x)
  rw [S45.s45_susceptibilityCov_eq hK hβ (hmem hf) (hmem hg),
    S45.s45_susceptibilityCov_eq hK hβ (hmem hg) (hmem hf)]
  exact S45.s45_inner_Rr_comm hK hβ.le _ _

theorem s79g_Kcov_comm (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (m : ℝ) (α α' : MultiIndex d) {τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') :
    Kcov d s a β τ τ' (oscTestFun m α) (oscTestFun m α') =
      Kcov d s a β τ' τ (oscTestFun m α') (oscTestFun m α) := by
  obtain ⟨u, hu, hpu⟩ := s79g_classical hd hs.le hsd ha hβ m α hτ
  obtain ⟨v, hv, hpv⟩ := s79g_classical hd hs.le hsd ha hβ m α' hτ'
  unfold Kcov
  rw [s79g_noise_comm, hpu 0 ⟨le_rfl, hτ⟩, hpv 0 ⟨le_rfl, hτ'⟩]
  rw [s79g_cov_comm hd hs.le hsd ha hβ (goodPath_of_classical hu |>.memCb 0 ⟨le_rfl, hτ⟩)
    (goodPath_of_classical hv |>.memCb 0 ⟨le_rfl, hτ'⟩)]

theorem s79g_Kcov_shift (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β)) (m : ℝ)
    (α α' : MultiIndex d) {t t' a₀ : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (ha₀ : 0 ≤ a₀) :
    Kcov d s a β (a₀ + t) (a₀ + t') (oscTestFun m α) (oscTestFun m α') =
      Kcov d s a β t t' (oscTestFun m α) (oscTestFun m α') := by
  rcases le_total t t' with h | h
  · have e1 := s79g_Kstat hd hs hsd ha hβ hρ m α α' (τ0 := a₀ + t) (δ := t' - t) (by linarith) (by linarith)
    have e2 := s79g_Kstat hd hs hsd ha hβ hρ m α α' (τ0 := t) (δ := t' - t) ht (by linarith)
    have h1 : a₀ + t + (t' - t) = a₀ + t' := by ring
    have h2 : t + (t' - t) = t' := by ring
    rw [h1] at e1
    rw [h2] at e2
    rw [e1, e2]
  · rw [s79g_Kcov_comm hd hs hsd ha hβ m α α' (by linarith) (by linarith),
      s79g_Kcov_comm hd hs hsd ha hβ m α α' ht ht']
    have e1 := s79g_Kstat hd hs hsd ha hβ hρ m α' α (τ0 := a₀ + t') (δ := t - t') (by linarith) (by linarith)
    have e2 := s79g_Kstat hd hs hsd ha hβ hρ m α' α (τ0 := t') (δ := t - t') ht' (by linarith)
    have h1 : a₀ + t' + (t - t') = a₀ + t := by ring
    have h2 : t' + (t - t') = t := by ring
    rw [h1] at e1
    rw [h2] at e2
    rw [e1, e2]

end HRS.MS.S79G

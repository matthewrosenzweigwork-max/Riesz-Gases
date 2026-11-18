import HRS.MS.WsInitHAux12

/-!
# S21H packet H, part 13: `s21h_w1_half`, the `W_1` half of `S21Init` for a fixed orbit family

`s21h_w1_half`: let `φ ⊂ C_b^J` (`J > d/2 + 2`) be a summable family enumerated by `σ : ℕ ≃ ℕ × MultiIndex d` (`φ k = f_{σ k}`) with the product decay
`‖φ_k‖_{C_b^J} ≤ A (1+n)^{-5/4} λ_α^{-γ}`, `5d/4 < γ` (cosine orbit family of packet G), `ι : ℓ² → C([0,T];B_m)` bounded, `γ̃` the centred
Gaussian on `ℓ²` with the susceptibility covariance.  Then there is `C_W ≥ 0` (independent of `N`) with, for every `N ≥ 2` such that
`s21IP = ι ∘ featureVec φ m_N` (the cosine series of the initial orbit path, packet G),

`W_1(law_{P_{N,β}} s21IP, ι_* γ̃) ≤ C_W δ_N^{3/20}`.

With `γ₀ = ι_* γ̃` this is the `W_1` conjunct of `S21InitAt` (WsStatAux34).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21h_w1_half (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {J : ℕ} (hJ : (d : ℝ) / 2 + 2 < J) (m T : ℝ) (hT : 0 ≤ T) (C : WholeCoeff d)
    (σ : ℕ ≃ ℕ × MultiIndex d) (ι : SeqL2 →L[ℝ] OscPath d m T) (φ : ℕ → Euc d → ℝ)
    (hφ : IsSummableFeatureFamily J φ) {γ₀ A : ℝ} (hγ₀ : 5 * (d : ℝ) / 4 < γ₀)
    (hdecay : ∀ k, cbNorm J (φ k) ≤ A * (((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 4) *
      oscEigenvalue d (σ k).2 ^ (-γ₀)))
    (γ : Measure SeqL2) (hγ : IsCenteredGaussianSeq γ fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) β (φ i) (φ j)) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ N : ℕ, 2 ≤ N →
      (∀ x : EucConfig d N, s21IP m T hT C N (HRS.Whole.meanEmpirical
          (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x =
        ι (featureVec φ (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x)) →
      wassersteinE 1 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (s21IP m T hT C N (HRS.Whole.meanEmpirical
            (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) (γ.map ι) ≤
        ENNReal.ofReal (CW * HRS.deltaN d s N ^ ((3 : ℝ) / 20)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cτ, Cq, hCτ, hCq, h⟩ := s21h_init_w1 hd hs0 hsd ha hβ hJ
  obtain ⟨K, τ₀, hK, hτ₀, hbox⟩ := s21h_box_osc hd1 σ hγ₀ (fun k => cbNorm J (φ k))
    (fun k => HRS.MS.Tc5.tc5_cb_nonneg J (φ k)) hdecay
  have hS0 : 0 ≤ featureSum J φ := tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg J (φ j)
  refine ⟨‖ι‖ * (2 * (Cτ * τ₀) + 4 * Real.sqrt K + Cq * featureSum J φ + Cq * featureSum J φ ^ 2), by positivity, ?_⟩
  intro N hN hpath
  have := h m T hT C N hN ι φ hφ γ hγ hpath hK hτ₀ hbox
  rw [← mul_assoc] at this
  exact this

end HRS.MS.S21

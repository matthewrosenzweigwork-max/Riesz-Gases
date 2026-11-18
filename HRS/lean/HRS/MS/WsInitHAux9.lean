import HRS.MS.WsInitHAux8
import HRS.MS.WsStatAux34

/-!
# S21H packet H, part 9: `s21h_init_w1`, the `W_1` half of `S21Init` in the shape of the S21 assembly

`s21h_init_w1`: the law of the centred initial orbit path `s21IP` under the stationary Gibbs law `P_{N,β}`, compared with `ι_*γ̃` (the
Gaussian path measure `γ₀ = ι_*γ̃` of `S21Init`), where the orbit feature family `φ` (packet G) satisfies:

* `hpath`: `s21IP x = ι (featureVec φ m_N x)` for every configuration (the cosine series of the initial orbit path);
* `φ` is a summable `C_b^J` family (`J > d/2 + 2`) and `γ̃` is the centred Gaussian on `ℓ²` with the susceptibility covariance;
* the box decay `∀ Q ≥ 1, ∃ I, |I| ≤ K Q², ∑_{k ∉ I} ‖φ_k‖²_{C_b^J} ≤ τ₀² Q^{-3/2}` (for the cosine family `f_{n,j}`:
  `‖f_{n,j}‖_{C_b^J} ≤ C (1+n)^{-5/4} b_j`, `I = {n, j ≤ Q}`, tails `Q^{-3/2}` in the `n`-sum and in the `j`-sum).

Conclusion: `W_1 ≤ ‖ι‖ (2 C_τ τ₀ + 4√K + C_q S + C_q S²) δ_N^{3/20}` with `C_τ, C_q` depending only on `d, s, a, β, J`.
The corollary `s21h_init_w1_unif` takes uniform bounds `‖ι‖ ≤ C_ι`, `S ≤ S₀` and gives a single constant.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21h_init_w1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {J : ℕ} (hJ : (d : ℝ) / 2 + 2 < J) :
    ∃ Cτ Cq : ℝ, 0 ≤ Cτ ∧ 0 ≤ Cq ∧ ∀ (m T : ℝ) (hT : 0 ≤ T) (C : WholeCoeff d) (N : ℕ), 2 ≤ N →
      ∀ (ι : SeqL2 →L[ℝ] OscPath d m T) (φ : ℕ → Euc d → ℝ), IsSummableFeatureFamily J φ →
      ∀ (γ : Measure SeqL2), (IsCenteredGaussianSeq γ fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
        (thermalMeasure d s a β) β (φ i) (φ j)) →
      (∀ x : EucConfig d N, s21IP m T hT C N (HRS.Whole.meanEmpirical
          (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x =
        ι (featureVec φ (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x)) →
      ∀ {K τ₀ : ℝ}, 0 ≤ K → 0 ≤ τ₀ →
      (∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
        ∑' k : ℕ, (if k ∈ I then 0 else cbNorm J (φ k) ^ 2) ≤ τ₀ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2)) →
      wassersteinE 1 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (s21IP m T hT C N (HRS.Whole.meanEmpirical
            (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) (γ.map ι) ≤
        ENNReal.ofReal (‖ι‖ * ((2 * (Cτ * τ₀) + 4 * Real.sqrt K + Cq * featureSum J φ + Cq * featureSum J φ ^ 2) *
          HRS.deltaN d s N ^ ((3 : ℝ) / 20))) := by
  obtain ⟨Cτ, Cq, hCτ, hCq, h⟩ := s21h_init_w1_stat hd hs0 hsd ha hβ hJ
  refine ⟨Cτ, Cq, hCτ, hCq, ?_⟩
  intro m T hT C N hN ι φ hφ γ hγ hpath K τ₀ hK hτ₀ hbox
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Cs, hCs0, hCs⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  set P := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hP
  have hSt := hCs N hN
  haveI : IsProbabilityMeasure P := hSt.prob
  have hme : HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P :=
    HRS.Whole.meanEmpirical_eq_firstMarginal P hSt.exch hN1
  haveI hν : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := S45.s45_nu_prob hN hSt.prob
  have hfm : Measurable (featureVec φ (HRS.Whole.firstMarginal P) : EucConfig d N → SeqL2) :=
    S45.s45_feature_measurable hN1 hφ
  have e : s21IP m T hT C N (HRS.Whole.meanEmpirical P) =
      fun x => ι (featureVec φ (HRS.Whole.firstMarginal P) x) := funext hpath
  rw [e, show (fun x => ι (featureVec φ (HRS.Whole.firstMarginal P) x)) =
    ι ∘ featureVec φ (HRS.Whole.firstMarginal P) from rfl, ← Measure.map_map ι.continuous.measurable hfm]
  exact h ι N hN φ hφ γ hγ hK hτ₀ hbox

/-- Uniform form: a single constant for all `N`, given uniform bounds on `‖ι‖`, `S` and the box data. -/
theorem s21h_init_w1_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {J : ℕ} (hJ : (d : ℝ) / 2 + 2 < J) {Cι S₀ K τ₀ : ℝ} (hCι : 0 ≤ Cι) (hS₀ : 0 ≤ S₀) (hK : 0 ≤ K) (hτ₀ : 0 ≤ τ₀) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ (m T : ℝ) (hT : 0 ≤ T) (C : WholeCoeff d) (N : ℕ), 2 ≤ N →
      ∀ (ι : SeqL2 →L[ℝ] OscPath d m T), ‖ι‖ ≤ Cι → ∀ (φ : ℕ → Euc d → ℝ), IsSummableFeatureFamily J φ →
      featureSum J φ ≤ S₀ →
      ∀ (γ : Measure SeqL2), (IsCenteredGaussianSeq γ fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
        (thermalMeasure d s a β) β (φ i) (φ j)) →
      (∀ x : EucConfig d N, s21IP m T hT C N (HRS.Whole.meanEmpirical
          (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x =
        ι (featureVec φ (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)) x)) →
      (∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
        ∑' k : ℕ, (if k ∈ I then 0 else cbNorm J (φ k) ^ 2) ≤ τ₀ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2)) →
      wassersteinE 1 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (s21IP m T hT C N (HRS.Whole.meanEmpirical
            (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) (γ.map ι) ≤
        ENNReal.ofReal (CW * HRS.deltaN d s N ^ ((3 : ℝ) / 20)) := by
  obtain ⟨Cτ, Cq, hCτ, hCq, h⟩ := s21h_init_w1 hd hs0 hsd ha hβ hJ
  refine ⟨Cι * (2 * (Cτ * τ₀) + 4 * Real.sqrt K + Cq * S₀ + Cq * S₀ ^ 2), by positivity, ?_⟩
  intro m T hT C N hN ι hι φ hφ hS γ hγ hpath hbox
  refine (h m T hT C N hN ι φ hφ γ hγ hpath hK hτ₀ hbox).trans (ENNReal.ofReal_le_ofReal ?_)
  have hS0 : 0 ≤ featureSum J φ := tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg J (φ j)
  have hd3 : 0 ≤ HRS.deltaN d s N ^ ((3 : ℝ) / 20) := Real.rpow_nonneg (s21_deltaN_pos hs0 hsd N (by omega)).le _
  have h1 : Cq * featureSum J φ ≤ Cq * S₀ := mul_le_mul_of_nonneg_left hS hCq
  have h2 : Cq * featureSum J φ ^ 2 ≤ Cq * S₀ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2) hCq
  have h3 : ‖ι‖ * ((2 * (Cτ * τ₀) + 4 * Real.sqrt K + Cq * featureSum J φ + Cq * featureSum J φ ^ 2) *
      HRS.deltaN d s N ^ ((3 : ℝ) / 20)) ≤
      Cι * ((2 * (Cτ * τ₀) + 4 * Real.sqrt K + Cq * S₀ + Cq * S₀ ^ 2) * HRS.deltaN d s N ^ ((3 : ℝ) / 20)) := by
    refine mul_le_mul hι (mul_le_mul_of_nonneg_right (by linarith) hd3) (by positivity) hCι
  calc _ ≤ _ := h3
    _ = _ := by ring

end HRS.MS.S21

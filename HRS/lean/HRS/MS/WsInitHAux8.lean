import HRS.MS.WsInitHAux7
import HRS.MS.WsStatAux3

/-!
# S21H packet H, part 8: the stationary `W_1` rate `δ_N^{3/20}` for a feature family (all static inputs proved)

`s21h_init_w1_stat`: for `d ≥ 2`, `0 ≤ s < d`, `a, β > 0` and an integer `J > d/2 + 2` there are constants `C_τ, C_q ≥ 0` such that for every
`N ≥ 2`, every summable family `φ ⊂ C_b^J`, every centred Gaussian `γ` on `ℓ²` with the susceptibility covariance, every bounded linear
`ι : ℓ² → X` into a separable Banach space (`X = C([0,T];B_m)`) and every box decomposition
`∀ Q ≥ 1, ∃ I, |I| ≤ K Q², ∑_{k ∉ I} ‖φ_k‖²_{C_b^J} ≤ τ₀² Q^{-3/2}` of the cb-norms,

`W_1^X(ι_*(featureVec φ m_N)_* P_{N,β}, ι_*γ) ≤ ‖ι‖ (2 C_τ τ₀ + 4√K + C_q S + C_q S²) δ_N^{3/20}`,   `S = ∑_k ‖φ_k‖_{C_b^J}`.

This uses ONLY merged results: `quadratic_static_field_proof` (derivative-only comparison), `S45Static.linear` (variance of linear statistics),
the susceptibility covariance bound `C(f,f) ≤ 4‖f‖²_∞` (`s21h_cov_le`) and the abstract projection/smoothing theorem (`WsInitHAux1-6`).
What is NOT proved here (packet G): the cosine-orbit family `f_{n,j}` with `∑_{k∉I_Q} ‖f_k‖² ≲ Q^{-3/2}` for a box decomposition,
`ι` with `s21IP = ι ∘ featureVec`, and the identification of `ι_*γ` with the Gaussian path measure `γ₀` of `S21Init`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s21h_init_w1_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {J : ℕ} (hJ : (d : ℝ) / 2 + 2 < J) :
    ∃ Cτ Cq : ℝ, 0 ≤ Cτ ∧ 0 ≤ Cq ∧ ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
      [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X] (ι : SeqL2 →L[ℝ] X) (N : ℕ), 2 ≤ N →
      ∀ (φ : ℕ → Euc d → ℝ), IsSummableFeatureFamily J φ → ∀ (γ : Measure SeqL2),
      (IsCenteredGaussianSeq γ fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
        (thermalMeasure d s a β) β (φ i) (φ j)) → ∀ {K τ₀ : ℝ}, 0 ≤ K → 0 ≤ τ₀ →
      (∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
        ∑' k : ℕ, (if k ∈ I then 0 else cbNorm J (φ k) ^ 2) ≤ τ₀ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2)) →
      wassersteinE 1 (((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (featureVec φ (HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))).map ι)
        (γ.map ι) ≤
        ENNReal.ofReal (‖ι‖ * ((2 * (Cτ * τ₀) + 4 * Real.sqrt K + Cq * featureSum J φ + Cq * featureSum J φ ^ 2) *
          HRS.deltaN d s N ^ ((3 : ℝ) / 20))) := by
  obtain ⟨Cs, hCs0, hCs⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  obtain ⟨Cq0, hQ⟩ := S45.quadratic_static_field_proof hd hs0 hsd a β ha hβ J hJ
  set Cm : ℝ := max Cs 4 with hCm
  have hCm4 : 4 ≤ Cm := le_max_right _ _
  have hCm0 : 0 ≤ Cm := by linarith
  set Cq : ℝ := max Cq0 0 with hCq
  refine ⟨Real.sqrt Cm, Cq, Real.sqrt_nonneg _, le_max_right _ _, ?_⟩
  intro X _ _ _ _ _ _ ι N hN φ hφ γ hγ K τ₀ hK hτ₀ hbox
  have hN1 : 1 ≤ N := by omega
  set P := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hP
  have hSt := hCs N hN
  haveI : IsProbabilityMeasure P := hSt.prob
  haveI hν : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := S45.s45_nu_prob hN hSt.prob
  have hstat := hQ φ hφ N hN γ hγ
  have hcb0 : ∀ k, 0 ≤ cbNorm J (φ k) := fun k => HRS.MS.Tc5.tc5_cb_nonneg J (φ k)
  have hsc0 : ∀ k, 0 ≤ Cm * cbNorm J (φ k) ^ 2 := fun k => by positivity
  have hsum : Summable fun k => Cm * cbNorm J (φ k) ^ 2 :=
    (S45.s45_summable_sq hcb0 hφ.2).mul_left Cm
  have hsμ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂(P.map (featureVec φ (HRS.Whole.firstMarginal P))) ≤
      ENNReal.ofReal (Cm * cbNorm J (φ k) ^ 2) := fun k =>
    (s21h_particle_coord hd hs0 hsd ha hβ hN hCs0 hSt hφ k).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  have hsγ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂γ ≤ ENNReal.ofReal (Cm * cbNorm J (φ k) ^ 2) :=
    fun k => (s21h_gauss_coord hd hs0 hsd ha hβ hφ hγ k).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCm4 (sq_nonneg _)))
  have hbox' : ∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
      ∑' k : ℕ, (if k ∈ I then 0 else Cm * cbNorm J (φ k) ^ 2) ≤
        (Real.sqrt Cm * τ₀) ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
    intro Q hQ1
    obtain ⟨I, hI, hT⟩ := hbox Q hQ1
    refine ⟨I, hI, ?_⟩
    have e : (∑' k : ℕ, (if k ∈ I then 0 else Cm * cbNorm J (φ k) ^ 2)) =
        Cm * ∑' k : ℕ, (if k ∈ I then 0 else cbNorm J (φ k) ^ 2) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      split_ifs <;> simp
    rw [e, mul_pow, Real.sq_sqrt hCm0, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hT hCm0
  have hδ0 : 0 < HRS.deltaN d s N := s21_deltaN_pos hs0 hsd N hN1
  have hδ1 : HRS.deltaN d s N ≤ 1 := s21_deltaN_le_one hs0 hsd N hN1
  have := s21h_init_w1_feat ι hN1 P (HRS.Whole.firstMarginal P) hφ hγ.1 (le_max_left Cq0 0) (le_max_right Cq0 0) hstat
    hδ0 hδ1 hK (mul_nonneg (Real.sqrt_nonneg _) hτ₀) _ hsc0 hsum hsμ hsγ hbox'
  simpa only [mul_assoc] using this

end HRS.MS.S21

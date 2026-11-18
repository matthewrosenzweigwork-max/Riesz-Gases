import HRS.MS.QsfAsm8

/-!
# S4.5 packet B5 (assembly), part 9: the `hfin` data of `static_stein_hilbert`
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s45_partial_sum_le {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
    (n : ℕ) : ∑ i : Fin n, cbNorm J (φ i) ≤ featureSum J φ := by
  have h := (Fin.sum_univ_eq_sum_range (fun i => cbNorm J (φ i)) n)
  rw [h]
  exact hφ.2.sum_le_tsum _ fun i _ => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)

section Ctx

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β Cs C c BU KR KT : ℝ}
  (ha : 0 < a) (hβ : 0 < β) (hsu : S45Setup d s a β Cs C c BU KR KT) (hN : 2 ≤ N) {J : ℕ}
  (hJ : 1 ≤ J) {φ χ : ℕ → Euc d → ℝ} {Cc : ℝ} (hCc : 0 ≤ Cc)
  (hφ : HRS.Whole.IsSummableFeatureFamily J φ)
  (hfeat : ∀ i, S45Feat d s a β (φ i) (χ i) (Cc * cbNorm J (φ i)))
  {γ : Measure SeqL2} [IsProbabilityMeasure γ]

include hd hs0 hsd ha hβ hsu hN hJ hCc hφ hfeat

theorem s45_hfin
    (hγ : IsCenteredGaussianSeq γ fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) β (φ i) (φ j)) (n : ℕ) :
    ∃ (R : EucConfig d N × SeqL2 → EuclideanSpace ℝ (Fin n))
      (T : EucConfig d N × SeqL2 → Matrix (Fin n) (Fin n) ℝ),
      Integrable R ((s45_P d s a β N).prod γ) ∧
      (∀ i j, AEStronglyMeasurable (fun w => T w i j) ((s45_P d s a β N).prod γ)) ∧
      Integrable (fun w => HRS.traceNormMatrix (T w)) ((s45_P d s a β N).prod γ) ∧
      SteinIdentity ((s45_P d s a β N).prod γ)
        (fun w => hilbertCoords s45_seqBasis n (featureVec φ (s45_nu d s a β N) w.1)) R T ∧
      ∫ w, ‖R w‖ ∂((s45_P d s a β N).prod γ) ≤
        KR * Cc * featureSum J φ * Real.sqrt (HRS.deltaN d s N) ∧
      ∫ w, HRS.traceNormMatrix (T w - Matrix.of fun i j : Fin n =>
          ∫ w', ⟪s45_seqBasis i, w'.2⟫ * ⟪s45_seqBasis j, w'.2⟫ ∂((s45_P d s a β N).prod γ))
        ∂((s45_P d s a β N).prod γ) ≤
        β⁻¹ * KT * Cc * featureSum J φ ^ 2 * Real.sqrt (HRS.deltaN d s N) := by
  have hN1 : 1 ≤ N := by omega
  have hSN := hsu.hS N hN
  haveI hP : IsProbabilityMeasure (s45_P d s a β N) := hSN.prob
  haveI hνprob : IsProbabilityMeasure (s45_nu d s a β N) := s45_nu_prob hN hP
  obtain ⟨hφ1, hφb, hφD⟩ := s45_phi_facts hJ hφ
  have hδ0 : 0 ≤ Real.sqrt (HRS.deltaN d s N) := Real.sqrt_nonneg _
  have hSsum := s45_partial_sum_le hφ n
  have hSn0 : 0 ≤ ∑ i : Fin n, cbNorm J (φ i) :=
    Finset.sum_nonneg fun i _ => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  refine ⟨s45_Rvec d s a β N n χ, s45_Tmat d β N n φ χ,
    s45_Rvec_integrable hd hs0 hsd hsu hN hfeat n, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨hc, -⟩ := s45_fij_facts hd hs0 hsd hβ hsu hN hJ hφ hfeat i j
    exact ((measurable_const.mul ((s45_measurable_pair_empirical hN1 hc.measurable).comp
      measurable_fst)).aestronglyMeasurable)
  · refine s45_traceNorm_integrable (b := β⁻¹ * ((Cc * featureSum J φ) * featureSum J φ)) ?_ ?_
    · intro i j
      obtain ⟨hc, -⟩ := s45_fij_facts hd hs0 hsd hβ hsu hN hJ hφ hfeat i j
      exact measurable_const.mul ((s45_measurable_pair_empirical hN1 hc.measurable).comp measurable_fst)
    · intro w i j
      obtain ⟨-, hb⟩ := s45_fij_facts hd hs0 hsd hβ hsu hN hJ hφ hfeat i j
      simp only [s45_Tmat, Matrix.of_apply]
      rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβ.le)
      have hcbS : ∀ k : ℕ, cbNorm J (φ k) ≤ featureSum J φ := fun k =>
        hφ.2.le_tsum k fun m _ => HRS.MS.Tc5.tc5_cb_nonneg J (φ m)
      have h1 := s45_abs_pair_empirical_le hN1 hb w.1
      refine h1.trans ?_
      have hi := hcbS i
      have hj := hcbS j
      have hi0 := HRS.MS.Tc5.tc5_cb_nonneg (d := d) J (φ i)
      have hj0 := HRS.MS.Tc5.tc5_cb_nonneg (d := d) J (φ j)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hi hCc) hj hj0
        (mul_nonneg hCc (hi0.trans hi))
  · -- the Stein identity
    set P := s45_P d s a β N with hPdef
    set ν := s45_nu d s a β N with hν
    set c' : ℕ → ℝ := fun j => pair ν (φ j) with hc'
    have hX : (fun w : EucConfig d N × SeqL2 => hilbertCoords s45_seqBasis n (featureVec φ ν w.1)) =
        fun w => s45_Yv n N φ c' w.1 := funext fun w => s45_hcoords hN1 hφ n w.1
    rw [hX]
    have hYm : Measurable (s45_Yv n N φ c' : EucConfig d N → EuclideanSpace ℝ (Fin n)) :=
      (s45_Yv_contDiff hN1 hφ1 c').continuous.measurable
    have hrm : ∀ i : Fin n, AEStronglyMeasurable (fun X => Real.sqrt N * s45_Rp
        (thermalMeasure d s a β) ν P (commutatorKernel d s (gradient (χ i))) X) P := fun i =>
      ((s45_Rp_integrable hd hs0 hsd hsu.hT hN hSN (hfeat i).smooth (hfeat i).B2).const_mul
        (Real.sqrt N)).aestronglyMeasurable
    have hTm : ∀ i j : Fin n, Measurable fun X : EucConfig d N => β⁻¹ * pair (empirical X)
        (fun x => ⟪gradient (χ i) x, gradient (φ j) x⟫) := fun i j =>
      measurable_const.mul (s45_measurable_pair_empirical hN1
        (s45_fij_facts hd hs0 hsd hβ hsu hN hJ hφ hfeat i j).1.measurable)
    exact s45_stein_prod (γ := γ) hYm hrm hTm fun f hf ⟨Cf, hCf⟩ ⟨Cf', hCf'⟩ i => by
      have h := s45_vec_stein hd hs0 hsd ha hβ hN hsu.hT hSN hφ1 hφb hφD hfeat hf hCf hCf' i
      have e : ∀ x, s45_Yv n N φ c' x i = s45_Yi N (φ i) (pair ν (φ i)) x := fun x =>
        s45_Yv_apply n N φ c' x i
      simp only [e]
      exact h
  · refine (s45_Rvec_bound hd hs0 hsd hsu hN hfeat n).trans ?_
    have : 0 ≤ KR * Cc := mul_nonneg hsu.hKR hCc
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSsum this) hδ0
  · refine (s45_Tmat_tau hd hs0 hsd hβ hsu hN hJ hφ hfeat hγ n).trans ?_
    have : 0 ≤ β⁻¹ * KT * Cc := mul_nonneg (mul_nonneg (inv_nonneg.2 hβ.le) hsu.hKT) hCc
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSn0 hSsum 2) this) hδ0

end Ctx

end S45

end

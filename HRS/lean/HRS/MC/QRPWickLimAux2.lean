import HRS.MC.QRPWickLimAux1

/-!
# QRPWickLim, auxiliary file 2: variance bound for the finite sections `Q_S - Q_F`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.QRSpec.Wick

open HRS.Sec7

variable {d : ℕ}

section Sect

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}

open Classical in
lemma qrpw_sect {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η) {K : ℝ}
    (hK : ModeCovBound P η K) (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ)
    (hHS : Summable fun p : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h p.1 p.2 ^ 2)
    (F S : Finset (NonzeroLattice d)) (hFS : F ⊆ S) :
    MemLp (fun ω => wickSection P η μ h S ω - wickSection P η μ h F ω) 2 P ∧
    ∫ ω, (wickSection P η μ h S ω - wickSection P η μ h F ω) ^ 2 ∂P ≤
      (1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) F := by
  set a := wickCoeff μ h with ha
  set ξ : S → Ω → ℝ := fun i ω => NegSobolev.fourierCoeff (η ω) i.1 with hξ
  set A : S → S → ℝ := fun i j => if i.1 ∈ F ∧ j.1 ∈ F then 0 else a i.1 j.1 with hA
  have hK' : ∀ b : S → ℝ, ∫ ω, (∑ i, b i * ξ i ω) ^ 2 ∂P ≤ K * ∑ i, b i ^ 2 := by
    intro b
    set b' : NonzeroLattice d → ℝ := fun k => if hk : k ∈ S then b ⟨k, hk⟩ else 0 with hb'
    have e1 : ∀ ω, ∑ i, b i * ξ i ω = ∑ k ∈ S, b' k * NegSobolev.fourierCoeff (η ω) k := by
      intro ω
      rw [← Finset.sum_coe_sort S (fun k => b' k * NegSobolev.fourierCoeff (η ω) k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hb', hξ]
    have e2 : ∑ i, b i ^ 2 = ∑ k ∈ S, b' k ^ 2 := by
      rw [← Finset.sum_coe_sort S (fun k => b' k ^ 2)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hb']
    simp_rw [e1]
    rw [e2]
    exact hK S b'
  have hfin := qrs_wick_var_fin_proof P ξ (hη S).1 (fun i => (hη S).2 i.1) K hK' A
  have hZ : ∀ ω, wickSection P η μ h S ω - wickSection P η μ h F ω =
      (1 / 2) * ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P) := by
    intro ω
    have e : ∑ i : S, ∑ j : S, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P) =
        ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then 0 else a k l *
          (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
            ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)) := by
      rw [← qrpw_sum_attach S (fun k l => if k ∈ F ∧ l ∈ F then 0 else a k l *
          (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
            ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P))]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : i.1 ∈ F ∧ j.1 ∈ F <;> simp [hA, hξ, hc]
    rw [e, ← qrpw_diff_alg S F hFS]
    unfold wickSection
    ring
  have hmem : MemLp (fun ω => wickSection P η μ h S ω - wickSection P η μ h F ω) 2 P := by
    have := hfin.1.const_mul (1 / 2 : ℝ)
    refine this.ae_eq (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hZ]
  refine ⟨hmem, ?_⟩
  simp_rw [hZ]
  have e3 : ∀ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P)) ^ 2 =
      (1 / 4 : ℝ) * (∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P)) ^ 2 := by
    intro ω; ring
  simp_rw [e3]
  rw [integral_const_mul]
  have hA2 : ∑ i, ∑ j, A i j ^ 2 ≤ tailHS a F := by
    have := qrpw_tail_le a hHS F S
    refine le_trans (le_of_eq ?_) this
    rw [← qrpw_sum_attach S (fun k l => if k ∈ F ∧ l ∈ F then 0 else a k l ^ 2)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : i.1 ∈ F ∧ j.1 ∈ F <;> simp [hA, hc]
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  nlinarith [hfin.2, mul_le_mul_of_nonneg_left hA2 hK2]

end Sect

end HRS.MC.QRSpec.Wick

end

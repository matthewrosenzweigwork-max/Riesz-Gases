import HRS.MC.QRPWick

/-!
# QRPWickLim, auxiliary file 1: finite sections of the half-Wick form

Coordinate facts, the identity `Q_S - Q_F = ½ ∑_{S×S∖F×F} ...`, and the finite-section variance bound obtained from
`qrs_wick_var_fin_proof`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.QRSpec.Wick

open HRS.Sec7

variable {d : ℕ}

section Sect

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}

lemma qrpw_coord_gauss {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η)
    (k : NonzeroLattice d) : HasGaussianLaw (fun ω => NegSobolev.fourierCoeff (η ω) k) P :=
  HasGaussianLaw.eval (X := fun (j : ({k} : Finset (NonzeroLattice d))) ω =>
    NegSobolev.fourierCoeff (η ω) j.1) (hη {k}).1 ⟨k, by simp⟩

lemma qrpw_coord_mem {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η)
    (k : NonzeroLattice d) : MemLp (fun ω => NegSobolev.fourierCoeff (η ω) k) 2 P :=
  (qrpw_coord_gauss hη k).memLp_two

lemma qrpw_coord_int {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η)
    (k l : NonzeroLattice d) :
    Integrable (fun ω => NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l) P :=
  (qrpw_coord_mem hη k).integrable_mul (qrpw_coord_mem hη l)

lemma qrpw_wickSection_empty (η : Ω → NegSobolev d r) (μ : Measure (Torus d))
    (h : Torus d → Torus d → ℝ) (ω : Ω) : wickSection P η μ h ∅ ω = 0 := by
  simp [wickSection]

lemma qrpw_wickSection_meas {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η)
    (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (F : Finset (NonzeroLattice d)) :
    AEStronglyMeasurable (wickSection P η μ h F) P := by
  unfold wickSection
  refine AEStronglyMeasurable.const_mul ?_ _
  refine Finset.aestronglyMeasurable_fun_sum F fun k _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum F fun l _ => ?_
  refine AEStronglyMeasurable.const_mul ?_ _
  exact (((qrpw_coord_gauss hη k).aemeasurable.mul (qrpw_coord_gauss hη l).aemeasurable).sub
    aemeasurable_const).aestronglyMeasurable

lemma qrpw_wickSection_integral {η : Ω → NegSobolev d r} (hη : HasFiniteGaussianCoeffs P η)
    (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (F : Finset (NonzeroLattice d)) :
    ∫ ω, wickSection P η μ h F ω ∂P = 0 := by
  unfold wickSection
  rw [integral_const_mul]
  have hi : ∀ k l : NonzeroLattice d, Integrable (fun ω => wickCoeff μ h k l *
      (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
        ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)) P :=
    fun k l => ((qrpw_coord_int hη k l).sub (integrable_const _)).const_mul _
  rw [integral_finsetSum _ (fun k _ => integrable_finset_sum _ fun l _ => hi k l)]
  have : ∀ k ∈ F, ∫ ω, ∑ l ∈ F, wickCoeff μ h k l *
      (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
        ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P) ∂P = 0 := by
    intro k _
    rw [integral_finsetSum _ (fun l _ => hi k l)]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, integral_sub (qrpw_coord_int hη k l) (integrable_const _)]
    simp
  rw [Finset.sum_eq_zero this]; simp

end Sect

section Alg

lemma qrpw_sum_attach (S : Finset (NonzeroLattice d)) (f : NonzeroLattice d → NonzeroLattice d → ℝ) :
    ∑ i : S, ∑ j : S, f i.1 j.1 = ∑ k ∈ S, ∑ l ∈ S, f k l := by
  rw [← Finset.sum_coe_sort S (fun k => ∑ l ∈ S, f k l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_coe_sort S (fun l => f i.1 l)

open Classical in
lemma qrpw_diff_alg (S F : Finset (NonzeroLattice d)) (hFS : F ⊆ S)
    (g : NonzeroLattice d → NonzeroLattice d → ℝ) :
    ∑ k ∈ S, ∑ l ∈ S, g k l - ∑ k ∈ F, ∑ l ∈ F, g k l =
      ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then 0 else g k l) := by
  have h1 : ∑ k ∈ F, ∑ l ∈ F, g k l = ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then g k l else 0) := by
    have e : ∀ k l, (if k ∈ F ∧ l ∈ F then g k l else 0) = if k ∈ F then (if l ∈ F then g k l else 0)
        else 0 := fun k l => by by_cases hk : k ∈ F <;> by_cases hl : l ∈ F <;> simp [hk, hl]
    simp_rw [e]
    have e2 : ∀ k, (∑ l ∈ S, if l ∈ F then g k l else 0) = ∑ l ∈ F, g k l := fun k => by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hFS]
    have e3 : ∀ k, (∑ l ∈ S, if k ∈ F then (if l ∈ F then g k l else 0) else 0) =
        if k ∈ F then ∑ l ∈ F, g k l else 0 := fun k => by
      by_cases hk : k ∈ F
      · simp [hk, e2]
      · simp [hk]
    simp_rw [e3]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hFS]
  rw [h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hc : k ∈ F ∧ l ∈ F <;> simp [hc]

open Classical in
lemma qrpw_tail_le (a : NonzeroLattice d → NonzeroLattice d → ℝ)
    (hs : Summable fun p : NonzeroLattice d × NonzeroLattice d => a p.1 p.2 ^ 2)
    (F S : Finset (NonzeroLattice d)) :
    ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then 0 else a k l ^ 2) ≤ tailHS a F := by
  unfold tailHS
  set g : NonzeroLattice d × NonzeroLattice d → ℝ := fun p => if p.1 ∈ F ∧ p.2 ∈ F then 0
    else a p.1 p.2 ^ 2 with hg
  have hgs : Summable g := Summable.of_nonneg_of_le (fun p => by simp only [hg]; split_ifs <;> positivity)
    (fun p => by simp only [hg]; split_ifs <;> first | positivity | exact le_rfl) hs
  have : ∑ k ∈ S, ∑ l ∈ S, (if k ∈ F ∧ l ∈ F then 0 else a k l ^ 2) = ∑ p ∈ S ×ˢ S, g p := by
    rw [Finset.sum_product]
  rw [this]
  refine (hgs.sum_le_tsum (S ×ˢ S) (fun p _ => by simp only [hg]; split_ifs <;> positivity)).trans ?_
  refine le_of_eq (tsum_congr fun p => ?_)
  simp only [hg]
  split_ifs <;> rfl

end Alg

end HRS.MC.QRSpec.Wick

end

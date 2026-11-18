import HRS.MS.QsfCorr3

/-!
# S4.5 packet B3': bridging the Gibbs law and Lebesgue integrals, marginals, empirical means

Namespace `S45`.  For the canonical Gibbs law `P = Z⁻¹ e^{-βH_N} dX` (a probability measure): `Z > 0`, the integral
formula `∫ f dP = Z⁻¹ ∫ f e^{-βH_N} dX`, transfer of Lebesgue-a.e. statements about a single particle to `P`-a.e.
statements about all particles, the marginals `P^{(k)} = firstMarginal P`, and `E μ_N(f) = m_N(f)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

theorem s45_measurable_ham {g V : Euc d → ℝ} (hg : Measurable g) (hV : Measurable V) :
    Measurable (canonicalHamiltonian g V : EucConfig d N → ℝ) := by
  unfold canonicalHamiltonian
  refine (Finset.measurable_sum _ fun i _ => hV.comp (measurable_pi_apply i)).add
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))
  exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem s45_Z_pos {g V : Euc d → ℝ} {β : ℝ}
    (hP : IsProbabilityMeasure (canonicalGibbs g V N β)) : 0 < canonicalPartition g V N β := by
  by_contra h
  push_neg at h
  have h0 : ENNReal.ofReal (canonicalPartition g V N β) = 0 := ENNReal.ofReal_of_nonpos h
  have h1 := hP.measure_univ
  unfold canonicalGibbs at h1
  rw [h0, Measure.smul_apply, smul_eq_mul, ENNReal.inv_zero] at h1
  by_cases hx : ((volume : Measure (EucConfig d N)).withDensity
      fun X => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))) Set.univ = 0
  · rw [hx, mul_zero] at h1; exact zero_ne_one h1
  · rw [ENNReal.top_mul hx] at h1; exact ENNReal.top_ne_one h1

/-- `∫ f dP = Z⁻¹ ∫ f e^{-βH_N} dX`. -/
theorem s45_integral_P {g V : Euc d → ℝ} (hg : Measurable g) (hV : Measurable V) {β : ℝ}
    (hP : IsProbabilityMeasure (canonicalGibbs g V N β)) (f : EucConfig d N → ℝ) :
    ∫ X, f X ∂(canonicalGibbs g V N β) =
      (canonicalPartition g V N β)⁻¹ * ∫ X, f X * Real.exp (-β * canonicalHamiltonian g V X) := by
  have hZ := s45_Z_pos hP
  unfold canonicalGibbs
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, smul_eq_mul]
  congr 1
  have hm : Measurable (fun X : EucConfig d N =>
      ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))) :=
    (Real.measurable_exp.comp (measurable_const.mul (s45_measurable_ham hg hV))).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp [ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]

theorem s45_preimage_null {A : Set (Euc d)} (hA : (volume : Measure (Euc d)) A = 0) (k : Fin N) :
    (volume : Measure (EucConfig d N)) {X | X k ∈ A} = 0 := by
  have : {X : EucConfig d N | X k ∈ A} = Set.univ.pi (Function.update (fun _ : Fin N => Set.univ) k A) := by
    ext X; simp [Set.mem_pi, Function.update_apply]
  rw [this, volume_pi, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simpa using hA)

/-- A Lebesgue-a.e. statement about one particle holds `P`-a.s. for every particle. -/
theorem s45_ae_P {g V : Euc d → ℝ} {β : ℝ} {E : Euc d → Prop}
    (hE : ∀ᵐ x ∂(volume : Measure (Euc d)), E x) :
    ∀ᵐ X ∂(canonicalGibbs g V N β), ∀ k, E (X k) := by
  have hac : canonicalGibbs g V N β ≪ (volume : Measure (EucConfig d N)) :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  refine hac.ae_le ?_
  refine Filter.eventually_all.2 fun k => ?_
  rw [ae_iff]
  have := s45_preimage_null (A := {x | ¬ E x}) (ae_iff.1 hE) k
  simpa using this

/-- Every coordinate of an exchangeable law has the law `firstMarginal`. -/
theorem s45_marginal_eq (hN : 1 ≤ N) {P : Measure (EucConfig d N)} (hex : IsExchangeable P) (k : Fin N) :
    P.map (fun X : EucConfig d N => X k) = firstMarginal P := by
  have hN' : 0 < N := hN
  have hT : ∀ τ : Equiv.Perm (Fin N), Measurable (fun X : EucConfig d N => X ∘ τ) :=
    fun τ => measurable_pi_iff.2 fun i => measurable_pi_apply (τ i)
  unfold firstMarginal
  rw [dif_pos hN']
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply k) hA,
    Measure.map_apply (measurable_pi_apply (⟨0, hN'⟩ : Fin N)) hA]
  have h := hex (Equiv.swap k ⟨0, hN'⟩)
  have hm : MeasurableSet {X : EucConfig d N | X k ∈ A} := measurable_pi_apply k hA
  calc P {X | X k ∈ A} = (P.map (fun X : EucConfig d N => X ∘ (Equiv.swap k ⟨0, hN'⟩))) {X | X k ∈ A} := by
        rw [h]
    _ = P {X | X ⟨0, hN'⟩ ∈ A} := by
        rw [Measure.map_apply (hT _) hm]
        congr 1
        ext X
        simp

/-- `E μ_N(f) = m_N(f)` for bounded measurable `f`. -/
theorem s45_E_pair_empirical (hN : 1 ≤ N) {P : Measure (EucConfig d N)} [IsProbabilityMeasure P]
    (hex : IsExchangeable P) {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hbd : ∀ x, |f x| ≤ B) :
    ∫ X, pair (empirical X) f ∂P = pair (firstMarginal P) f := by
  have hN' : 0 < N := hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN'.ne'
  simp_rw [pair_empirical hN']
  have hint : ∀ k : Fin N, Integrable (fun X : EucConfig d N => f (X k)) P := fun k =>
    Integrable.of_bound ((hf.comp (measurable_pi_apply k)).aestronglyMeasurable) B
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hbd _)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hint k)]
  have hk : ∀ k : Fin N, ∫ X, f (X k) ∂P = pair (firstMarginal P) f := by
    intro k
    unfold pair
    rw [← s45_marginal_eq hN hex k, integral_map (measurable_pi_apply k).aemeasurable
      hf.aestronglyMeasurable]
  simp_rw [hk]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end S45

end

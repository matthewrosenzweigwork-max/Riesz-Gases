import HRS.MC.QRPChaosAux3

/-!
# Packet CHAOS-LP (aux 4): Gaussian second chaos in `L^p`, law form

For a centred Gaussian law `ν` on `ι → ℝ` with covariance operator bound `K` the centred quadratic form
has `L^p(ν)` norm at most `2 K ‖A‖_HS (‖id‖_{L^p(N(0,1))})²` (decoupling + conditional Gaussianity).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.QRPChaos

variable {ι : Type} [Fintype ι]

/-- Jensen step (symmetrisation): a centred integrable function has `L^p` norm at most that of its
difference with an independent copy. -/
lemma qpc_symmetrize {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (X : E → ℝ) (hXm : Measurable X) (hXi : Integrable X ν) (hX0 : ∫ x, X x ∂ν = 0)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm X (ENNReal.ofReal p) ν ≤
      eLpNorm (fun z : E × E => X z.1 - X z.2) (ENNReal.ofReal p) (ν.prod ν) := by
  have hp0 : 0 < p := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hFm : Measurable (fun z : E × E => X z.1 - X z.2) := by fun_prop
  have hJ : ∀ x : E, ‖X x‖ₑ ≤ eLpNorm (fun y => X x - X y) (ENNReal.ofReal p) ν := by
    intro x
    have hm : Measurable (fun y => X x - X y) := by fun_prop
    have hint : ∫ y, (X x - X y) ∂ν = X x := by
      rw [integral_sub (integrable_const _) hXi, hX0]; simp
    calc ‖X x‖ₑ = ‖∫ y, (X x - X y) ∂ν‖ₑ := by rw [hint]
      _ ≤ ∫⁻ y, ‖X x - X y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun y => X x - X y) 1 ν := (eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable).symm
      _ ≤ eLpNorm (fun y => X x - X y) (ENNReal.ofReal p) ν :=
          eLpNorm_le_eLpNorm_of_exponent_le hq1
  have hmain : eLpNorm X (ENNReal.ofReal p) ν ^ p ≤
      eLpNorm (fun z : E × E => X z.1 - X z.2) (ENNReal.ofReal p) (ν.prod ν) ^ p := by
    rw [qpc_prod_pow ν ν _ hFm hp0, qpc_pow_eLpNorm hXm.aestronglyMeasurable hp0]
    exact lintegral_mono fun x => ENNReal.rpow_le_rpow (hJ x) hp0.le
  exact (ENNReal.rpow_le_rpow_iff hp0).1 hmain

/-- Law form of the second-chaos `L^p` bound. -/
theorem qpc_nu_bound (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] [IsGaussian ν]
    (h0 : ∀ i, ∫ x, x i ∂ν = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ a : ι → ℝ, ∫ x, (∑ i, a i * x i) ^ 2 ∂ν ≤ K * ∑ i, a i ^ 2)
    (A : ι → ι → ℝ) {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm (fun x : ι → ℝ => ∑ i, ∑ j, A i j * (x i * x j - ∫ y, y i * y j ∂ν))
        (ENNReal.ofReal p) ν ≤
      2 * (ENNReal.ofReal (K * Real.sqrt (∑ i, ∑ j, A i j ^ 2)) * qpcG p ^ 2) := by
  set X : (ι → ℝ) → ℝ := fun x => ∑ i, ∑ j, A i j * (x i * x j - ∫ y, y i * y j ∂ν) with hXdef
  have hXm : Measurable X := by simp only [hXdef]; fun_prop
  have hprod : ∀ i j, Integrable (fun x : ι → ℝ => x i * x j) ν := fun i j =>
    (qpc_coord_gauss ν i).memLp_two.integrable_mul (qpc_coord_gauss ν j).memLp_two
  have hij : ∀ i j, Integrable (fun x : ι → ℝ => A i j * (x i * x j - ∫ y, y i * y j ∂ν)) ν :=
    fun i j => ((hprod i j).sub (integrable_const _)).const_mul _
  have hi : ∀ i, Integrable (fun x : ι → ℝ => ∑ j, A i j * (x i * x j - ∫ y, y i * y j ∂ν)) ν :=
    fun i => integrable_finset_sum _ fun j _ => hij i j
  have hXi : Integrable X ν := integrable_finset_sum _ fun i _ => hi i
  have hX0 : ∫ x, X x ∂ν = 0 := by
    simp only [hXdef]
    rw [integral_finset_sum _ (fun i _ => hi i)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => hij i j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, integral_sub (hprod i j) (integrable_const _)]
    simp
  refine (qpc_symmetrize ν X hXm hXi hX0 (by linarith)).trans ?_
  -- rotate
  have hc := qpc_sqrt2_sq
  have hF : (fun z : (ι → ℝ) × (ι → ℝ) => X z.1 - X z.2) = fun z =>
      (∑ i, ∑ j, A i j * (qpcRot 1 z i * qpcRot (-1) z j)) +
      (∑ i, ∑ j, A i j * (qpcRot (-1) z i * qpcRot 1 z j)) := by
    funext z
    simp only [hXdef, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [qpcRot]
    linear_combination (-2 * A i j * (z.1 i * z.1 j - z.2 i * z.2 j)) * hc
  rw [hF]
  have hm1 : AEStronglyMeasurable (fun z : (ι → ℝ) × (ι → ℝ) =>
      ∑ i, ∑ j, A i j * (qpcRot 1 z i * qpcRot (-1) z j)) (ν.prod ν) :=
    (by simp only [qpcRot]; fun_prop : Measurable _).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun z : (ι → ℝ) × (ι → ℝ) =>
      ∑ i, ∑ j, A i j * (qpcRot (-1) z i * qpcRot 1 z j)) (ν.prod ν) :=
    (by simp only [qpcRot]; fun_prop : Measurable _).aestronglyMeasurable
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have d1 := qpc_decoupled (P := ν.prod ν) (qpc_rot_gauss ν 1) (qpc_rot_gauss ν (-1))
    (qpc_rot_indep ν h0) (qpc_rot_mean ν h0 1) (qpc_rot_mean ν h0 (-1)) hK0
    (fun a => (qpc_rot_second ν h0 (ε := 1) (by norm_num) a).le.trans (hK a))
    (fun a => (qpc_rot_second ν h0 (ε := -1) (by norm_num) a).le.trans (hK a)) A hp
  have d2 := qpc_decoupled (P := ν.prod ν) (qpc_rot_gauss ν (-1)) (qpc_rot_gauss ν 1)
    (qpc_rot_indep ν h0).symm (qpc_rot_mean ν h0 (-1)) (qpc_rot_mean ν h0 1) hK0
    (fun a => (qpc_rot_second ν h0 (ε := -1) (by norm_num) a).le.trans (hK a))
    (fun a => (qpc_rot_second ν h0 (ε := 1) (by norm_num) a).le.trans (hK a)) A hp
  exact (eLpNorm_add_le hq1).trans ((add_le_add d1 d2).trans (le_of_eq (by rw [two_mul])))

end HRS.MC.QRPChaos

end

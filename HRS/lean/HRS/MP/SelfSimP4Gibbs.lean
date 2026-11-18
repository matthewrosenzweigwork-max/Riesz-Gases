import HRS.MP.SelfSimP4Kern
import HRS.Energy.PressureDV
import HRS.Appendix.B15BDV

/-!
# MP-SSP4GIBBS: `p4_gibbs` (Gibbs references on `ℝ^{dN}`)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4g_`.  Theorem `p4_gibbs_proof`, tied to `HRS.MP.SelfSimP4.p4_gibbs`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

variable {d N : ℕ}

/-! ### The reference measures -/

theorem p4g_ref_apply (G : EucConfig d N → ℝ) (hG : Measurable G) (s : Set (EucConfig d N))
    (hs : MeasurableSet s) :
    gibbsRefW G s = (gibbsPartitionW G)⁻¹ * ∫⁻ x in s, ENNReal.ofReal (G x) := by
  unfold gibbsRefW
  rw [Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]

theorem p4g_ref_prob (G : EucConfig d N → ℝ) (hG : Measurable G) (h0 : gibbsPartitionW G ≠ 0)
    (ht : gibbsPartitionW G ≠ ⊤) : IsProbabilityMeasure (gibbsRefW G) := by
  refine ⟨?_⟩
  rw [p4g_ref_apply G hG _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel h0 ht

theorem p4g_ref_ac (G : EucConfig d N → ℝ) : gibbsRefW G ≪ (volume : Measure (EucConfig d N)) := by
  unfold gibbsRefW
  exact (withDensity_absolutelyContinuous _ _).smul_left _

theorem p4g_ref_zero (G : EucConfig d N → ℝ) (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x) :
    gibbsRefW G {x | G x = 0} = 0 := by
  have hm : MeasurableSet {x | G x = 0} := hG (measurableSet_singleton 0)
  rw [p4g_ref_apply G hG _ hm]
  have : ∫⁻ x in {x | G x = 0}, ENNReal.ofReal (G x) = 0 := by
    rw [setLIntegral_congr_fun hm (g := fun _ => 0) (fun x hx => by simp [show G x = 0 from hx])]
    simp
  rw [this, mul_zero]


/-- The density of `gibbsRefW G` with respect to `gibbsRefW G'` for `0 ≤ G ≤ G'`, `G' > 0`. -/
def p4g_ratio (G G' : EucConfig d N → ℝ) (x : EucConfig d N) : ℝ≥0∞ :=
  (gibbsPartitionW G' / gibbsPartitionW G) * ENNReal.ofReal (G x / G' x)

theorem p4g_ratio_meas {G G' : EucConfig d N → ℝ} (hG : Measurable G) (hG' : Measurable G') :
    Measurable (p4g_ratio G G') := by
  unfold p4g_ratio
  exact (hG.div hG').ennreal_ofReal.const_mul _

theorem p4g_ref_eq {G G' : EucConfig d N → ℝ} (hG : Measurable G) (hG' : Measurable G')
    (hG0 : ∀ x, 0 ≤ G x) (hle : ∀ x, G x ≤ G' x) (hpos : ∀ x, 0 < G' x)
    (hZ0 : gibbsPartitionW G ≠ 0) (hZt : gibbsPartitionW G ≠ ⊤)
    (hZ0' : gibbsPartitionW G' ≠ 0) (hZt' : gibbsPartitionW G' ≠ ⊤) :
    gibbsRefW G = (gibbsRefW G').withDensity (p4g_ratio G G') := by
  ext s hs
  rw [p4g_ref_apply G hG s hs, withDensity_apply _ hs]
  unfold gibbsRefW
  rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, restrict_withDensity hs,
    lintegral_withDensity_eq_lintegral_mul _ hG'.ennreal_ofReal (p4g_ratio_meas hG hG')]
  have hpt : ∀ x, ((fun X => ENNReal.ofReal (G' X)) * p4g_ratio G G') x =
      (gibbsPartitionW G' / gibbsPartitionW G) * ENNReal.ofReal (G x) := by
    intro x
    simp only [Pi.mul_apply, p4g_ratio]
    rw [mul_left_comm, ← ENNReal.ofReal_mul (hpos x).le]
    have : G' x * (G x / G' x) = G x := by
      have h := (hpos x).ne'
      field_simp
    rw [this]
  simp_rw [hpt]
  rw [lintegral_const_mul _ hG.ennreal_ofReal, ← mul_assoc]
  congr 1
  rw [ENNReal.div_eq_inv_mul, mul_left_comm, ENNReal.inv_mul_cancel hZ0' hZt', mul_one]


theorem p4g_llr_le {G G' : EucConfig d N → ℝ} (hG : Measurable G) (hG' : Measurable G')
    (hG0 : ∀ x, 0 ≤ G x) (hle : ∀ x, G x ≤ G' x) (hpos : ∀ x, 0 < G' x)
    (hZ0 : gibbsPartitionW G ≠ 0) (hZt : gibbsPartitionW G ≠ ⊤)
    (hZ0' : gibbsPartitionW G' ≠ 0) (hZt' : gibbsPartitionW G' ≠ ⊤)
    (μ : Measure (EucConfig d N)) [IsFiniteMeasure μ] (hμν : μ ≪ gibbsRefW G) :
    ∀ᵐ x ∂μ, llr μ (gibbsRefW G') x ≤ llr μ (gibbsRefW G) x +
      Real.log ((gibbsPartitionW G').toReal / (gibbsPartitionW G).toReal) := by
  haveI := p4g_ref_prob G hG hZ0 hZt
  haveI := p4g_ref_prob G' hG' hZ0' hZt'
  have heq := p4g_ref_eq hG hG' hG0 hle hpos hZ0 hZt hZ0' hZt'
  have hνν' : gibbsRefW G ≪ gibbsRefW G' := by rw [heq]; exact withDensity_absolutelyContinuous _ _
  have hρ : (gibbsRefW G).rnDeriv (gibbsRefW G') =ᵐ[gibbsRefW G'] p4g_ratio G G' := by
    have := Measure.rnDeriv_withDensity (gibbsRefW G') (p4g_ratio_meas hG hG')
    rwa [← heq] at this
  have hzero : ∀ᵐ x ∂gibbsRefW G, G x ≠ 0 := by
    have := p4g_ref_zero G hG hG0
    rw [measure_eq_zero_iff_ae_notMem] at this
    exact this
  filter_upwards [hμν.trans hνν' |>.ae_le (Measure.rnDeriv_mul_rnDeriv hμν),
    (hμν.trans hνν').ae_le hρ, Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ (gibbsRefW G)), hμν.ae_le hzero] with x h1 h2 h3 h4 h5
  have hGx : 0 < G x := lt_of_le_of_ne (hG0 x) (Ne.symm h5)
  have hG'x := hpos x
  have hcpos : 0 < (gibbsPartitionW G').toReal / (gibbsPartitionW G).toReal := by
    have a1 : 0 < (gibbsPartitionW G').toReal := ENNReal.toReal_pos hZ0' hZt'
    have a2 : 0 < (gibbsPartitionW G).toReal := ENNReal.toReal_pos hZ0 hZt
    positivity
  have hr : (p4g_ratio G G' x).toReal =
      (gibbsPartitionW G').toReal / (gibbsPartitionW G).toReal * (G x / G' x) := by
    unfold p4g_ratio
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (hG0 x) hG'x.le),
      ENNReal.toReal_div]
  have hapos : 0 < (μ.rnDeriv (gibbsRefW G) x).toReal := ENNReal.toReal_pos h3.ne' h4.ne
  have hq : 0 < G x / G' x := div_pos hGx hG'x
  have hq1 : G x / G' x ≤ 1 := (div_le_one hG'x).2 (hle x)
  unfold llr
  rw [← h1]
  simp only [Pi.mul_apply]
  rw [h2, ENNReal.toReal_mul, hr, Real.log_mul hapos.ne' (by positivity),
    Real.log_mul hcpos.ne' hq.ne']
  have : Real.log (G x / G' x) ≤ 0 := Real.log_nonpos hq.le hq1
  linarith


theorem p4g_entropy_eq {G : EucConfig d N → ℝ} (hG : Measurable G)
    (hZ0 : gibbsPartitionW G ≠ 0) (hZt : gibbsPartitionW G ≠ ⊤)
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hKL : klDiv μ (gibbsRefW G) ≠ ⊤) :
    gibbsEntropyW G μ =
      ((∫ x, llr μ (gibbsRefW G) x ∂μ - Real.log (gibbsPartitionW G).toReal : ℝ) : EReal) := by
  haveI := p4g_ref_prob G hG hZ0 hZt
  obtain ⟨hμν, -⟩ := klDiv_ne_top_iff.1 hKL
  have h1 : (klDiv μ (gibbsRefW G)).toReal = ∫ x, llr μ (gibbsRefW G) x ∂μ :=
    toReal_klDiv_of_measure_eq hμν (by rw [measure_univ, measure_univ])
  unfold gibbsEntropyW relEntropy
  rw [← EReal.coe_ennreal_toReal hKL, h1, ← EReal.coe_sub]

theorem p4g_entropy_mono {G G' : EucConfig d N → ℝ} (hG : Measurable G) (hG' : Measurable G')
    (hG0 : ∀ x, 0 ≤ G x) (hle : ∀ x, G x ≤ G' x) (hpos : ∀ x, 0 < G' x)
    (hZ0 : gibbsPartitionW G ≠ 0) (hZt : gibbsPartitionW G ≠ ⊤)
    (hZ0' : gibbsPartitionW G' ≠ 0) (hZt' : gibbsPartitionW G' ≠ ⊤)
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    gibbsEntropyW G' μ ≤ gibbsEntropyW G μ := by
  haveI := p4g_ref_prob G hG hZ0 hZt
  haveI := p4g_ref_prob G' hG' hZ0' hZt'
  by_cases hKL : klDiv μ (gibbsRefW G) = ⊤
  · have : gibbsEntropyW G μ = ⊤ := by
      unfold gibbsEntropyW relEntropy
      rw [hKL]
      exact EReal.top_sub_coe _
    rw [this]; exact le_top
  obtain ⟨hμν, hint⟩ := klDiv_ne_top_iff.1 hKL
  have heq := p4g_ref_eq hG hG' hG0 hle hpos hZ0 hZt hZ0' hZt'
  have hνν' : gibbsRefW G ≪ gibbsRefW G' := by rw [heq]; exact withDensity_absolutelyContinuous _ _
  have hμν' : μ ≪ gibbsRefW G' := hμν.trans hνν'
  have hneg := b15dv_llr_negPart_integrable μ (gibbsRefW G') hμν'
  have hae := p4g_llr_le hG hG' hG0 hle hpos hZ0 hZt hZ0' hZt' μ hμν
  set c := Real.log ((gibbsPartitionW G').toReal / (gibbsPartitionW G).toReal) with hc
  have hint' : Integrable (llr μ (gibbsRefW G')) μ := by
    refine Integrable.mono' ((hint.add (integrable_const c)).abs.add hneg)
      (measurable_llr _ _).aestronglyMeasurable ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    rcases le_total 0 (llr μ (gibbsRefW G') x) with h | h
    · rw [abs_of_nonneg h]
      have := le_abs_self (llr μ (gibbsRefW G) x + c)
      have := le_max_left (-llr μ (gibbsRefW G') x) 0
      have h0 : 0 ≤ max (-llr μ (gibbsRefW G') x) 0 := le_max_right _ _
      linarith
    · rw [abs_of_nonpos h]
      have := abs_nonneg (llr μ (gibbsRefW G) x + c)
      have := le_max_left (-llr μ (gibbsRefW G') x) 0
      linarith
  have hKL' : klDiv μ (gibbsRefW G') ≠ ⊤ := klDiv_ne_top hμν' hint'
  rw [p4g_entropy_eq hG' hZ0' hZt' μ hKL', p4g_entropy_eq hG hZ0 hZt μ hKL]
  refine EReal.coe_le_coe_iff.2 ?_
  have hI : ∫ x, llr μ (gibbsRefW G') x ∂μ ≤ ∫ x, llr μ (gibbsRefW G) x ∂μ + c := by
    calc ∫ x, llr μ (gibbsRefW G') x ∂μ ≤ ∫ x, (llr μ (gibbsRefW G) x + c) ∂μ :=
          integral_mono_ae hint' (hint.add (integrable_const c)) hae
      _ = _ := by rw [integral_add hint (integrable_const c)]; simp
  have a1 : 0 < (gibbsPartitionW G').toReal := ENNReal.toReal_pos hZ0' hZt'
  have a2 : 0 < (gibbsPartitionW G).toReal := ENNReal.toReal_pos hZ0 hZt
  rw [hc, Real.log_div a1.ne' a2.ne'] at hI
  linarith


/-! ### Gaussian majorants -/

theorem p4g_integrable_gauss (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euc d => Real.exp (-(b * ‖x‖ ^ 2))) (volume : Measure (Euc d)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem p4g_integrable_gauss_pi {c : ℝ} (hc : 0 < c) :
    Integrable (fun Ξ : EucConfig d N => Real.exp (-(c * ‖Ξ‖ ^ 2)))
      (volume : Measure (EucConfig d N)) := by
  have hprod : Integrable (fun Ξ : EucConfig d N =>
      ∏ i, Real.exp (-((c / N) * ‖Ξ i‖ ^ 2))) (Measure.pi fun _ : Fin N => (volume : Measure (Euc d))) :=
    Integrable.fintype_prod (f := fun _ : Fin N => fun w : Euc d => Real.exp (-((c / N) * ‖w‖ ^ 2)))
      (μ := fun _ => (volume : Measure (Euc d)))
      (fun i => p4g_integrable_gauss d (by
        have : (0 : ℝ) < N := by exact_mod_cast Fin.pos i
        positivity))
  have hvol : (volume : Measure (EucConfig d N)) = Measure.pi fun _ : Fin N => (volume : Measure (Euc d)) :=
    rfl
  rw [hvol]
  refine hprod.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun Ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, neg_le_neg_iff]
  have h1 : ∑ i, ‖Ξ i‖ ^ 2 ≤ N * ‖Ξ‖ ^ 2 := by
    calc ∑ i, ‖Ξ i‖ ^ 2 ≤ ∑ _i : Fin N, ‖Ξ‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm Ξ i) 2
      _ = N * ‖Ξ‖ ^ 2 := by simp
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp; positivity
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    calc c / N * ∑ i, ‖Ξ i‖ ^ 2 ≤ c / N * (N * ‖Ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c * ‖Ξ‖ ^ 2 := by field_simp


/-! ### The collision set -/

theorem p4g_collision_eq (d N : ℕ) : eucCollisionSet d N =
    ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X : EucConfig d N | X i = X j} := by
  ext X; simp [eucCollisionSet]

theorem p4g_collision_meas (d N : ℕ) : MeasurableSet (eucCollisionSet d N) := by
  rw [p4g_collision_eq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)

theorem p4g_collision_null (hd : 1 ≤ d) (N : ℕ) :
    (volume : Measure (EucConfig d N)) (eucCollisionSet d N) = 0 := by
  rw [p4g_collision_eq]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  let L : EucConfig d N →ₗ[ℝ] Euc d := LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j
  have hset : {X : EucConfig d N | X i = X j} = (LinearMap.ker L : Set (EucConfig d N)) := by
    ext X; simp [L, sub_eq_zero]
  rw [hset]
  refine Measure.addHaar_submodule _ _ ?_
  intro htop
  have hmem : (Pi.single i (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) : EucConfig d N) ∈
      LinearMap.ker L := by rw [htop]; trivial
  simp only [LinearMap.mem_ker, L, LinearMap.sub_apply, LinearMap.coe_proj, Function.eval,
    Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, sub_zero] at hmem
  have := congrArg (fun v : Euc d => v ⟨0, hd⟩) hmem
  simp at this


/-! ### The weights -/

theorem p4g_riesz_meas (d : ℕ) (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  by_cases h : s = 0
  · simp only [h, ite_true]; exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [h, ite_false]; exact measurable_norm.pow_const _

theorem p4g_pot_meas_aux (k : Euc d → ℝ) (hk : Measurable k) (a : ℝ) :
    Measurable (fun Ξ : EucConfig d N => a * ∑ i, ∑ j ∈ Finset.univ.erase i, k (Ξ i - Ξ j) +
      (1 / 4) * ∑ i, ‖Ξ i‖ ^ 2) := by
  refine Measurable.add (Measurable.const_mul ?_ _) (Measurable.const_mul ?_ _)
  · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hk.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  · exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).norm).pow_const 2

theorem p4g_p4Pot_meas {k : Euc d → ℝ} (hk : Measurable k) (s : ℝ) (N : ℕ) (τ : ℝ) :
    Measurable (p4Pot k s N τ) :=
  p4g_pot_meas_aux k hk _

theorem p4g_ssPot_meas (d : ℕ) (s : ℝ) (N : ℕ) (τ : ℝ) : Measurable (selfSimPotential d s N τ) :=
  p4g_pot_meas_aux (rieszKernel d s) (p4g_riesz_meas d s) _

theorem p4g_ssWeight_meas (d : ℕ) (s invβ : ℝ) (N : ℕ) (τ : ℝ) :
    Measurable (selfSimWeight d s invβ N τ) := by
  classical
  unfold selfSimWeight
  exact Measurable.ite (p4g_collision_meas d N) measurable_const
    (Real.measurable_exp.comp (((p4g_ssPot_meas d s N τ).const_mul _)))

theorem p4g_gibbsOf_meas {N : ℕ} (θ : ℝ) {V : EucConfig d N → ℝ} (hV : Measurable V) :
    Measurable (p4GibbsOf θ V) :=
  Real.measurable_exp.comp (hV.const_mul _)

theorem p4g_pot_le {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (τ : ℝ)
    (Ξ : EucConfig d N) (hΞ : Ξ ∉ eucCollisionSet d N) :
    p4Pot k s N τ Ξ ≤ selfSimPotential d s N τ Ξ := by
  unfold p4Pot selfSimPotential
  refine add_le_add_left (mul_le_mul_of_nonneg_left ?_ (by
    have := p4k_aSelfSim_pos s τ
    positivity)) _
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
  have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
  refine hk.le_riesz _ (sub_ne_zero.2 fun h => hΞ ⟨i, j, hij, h⟩)

theorem p4g_weight_le {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {invβ : ℝ}
    (hβ : 0 < invβ) (τ : ℝ) (Ξ : EucConfig d N) :
    selfSimWeight d s invβ N τ Ξ ≤ p4GibbsOf invβ (p4Pot k s N τ) Ξ := by
  classical
  unfold selfSimWeight p4GibbsOf
  by_cases hΞ : Ξ ∈ eucCollisionSet d N
  · rw [if_pos hΞ]; exact (Real.exp_pos _).le
  · rw [if_neg hΞ]
    refine Real.exp_le_exp.2 ?_
    have := p4g_pot_le hk τ Ξ hΞ
    have hi : 0 < invβ⁻¹ := inv_pos.2 hβ
    nlinarith

theorem p4g_gibbsOf_le {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {invβ : ℝ}
    (hβ : 0 < invβ) (τ : ℝ) (Ξ : EucConfig d N) :
    p4GibbsOf invβ (p4Pot k s N τ) Ξ ≤
      Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) * Real.exp (-(invβ⁻¹ / 8 * ‖Ξ‖ ^ 2)) := by
  unfold p4GibbsOf
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := p4k_conf_gen hk N τ Ξ
  have hi : 0 < invβ⁻¹ := inv_pos.2 hβ
  nlinarith


/-! ### Partition functions -/

theorem p4g_vol_univ_pos (d N : ℕ) : 0 < (volume : Measure (EucConfig d N)) Set.univ :=
  Measure.measure_univ_pos.2 (NeZero.ne _)

theorem p4g_lintegral_pos_of_pos {G : EucConfig d N → ℝ} (hG : Measurable G) (hpos : ∀ x, 0 < G x) :
    0 < gibbsPartitionW G := by
  unfold gibbsPartitionW
  rw [lintegral_pos_iff_support (hG.ennreal_ofReal)]
  have : Function.support (fun X => ENNReal.ofReal (G X)) = Set.univ := by
    ext X; simp [hpos X]
  rw [this]
  exact p4g_vol_univ_pos d N

theorem p4g_Zk_lt_top {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {invβ : ℝ}
    (hβ : 0 < invβ) (τ : ℝ) :
    gibbsPartitionW (p4GibbsOf invβ (p4Pot k s N τ)) < ⊤ := by
  unfold gibbsPartitionW
  have hint : Integrable (fun Ξ : EucConfig d N =>
      Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) * Real.exp (-(invβ⁻¹ / 8 * ‖Ξ‖ ^ 2)))
      volume :=
    (p4g_integrable_gauss_pi (c := invβ⁻¹ / 8) (by positivity)).const_mul _
  calc ∫⁻ Ξ : EucConfig d N, ENNReal.ofReal (p4GibbsOf invβ (p4Pot k s N τ) Ξ)
      ≤ ∫⁻ Ξ : EucConfig d N, ENNReal.ofReal (Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) *
          Real.exp (-(invβ⁻¹ / 8 * ‖Ξ‖ ^ 2))) :=
        lintegral_mono fun Ξ => ENNReal.ofReal_le_ofReal (p4g_gibbsOf_le hk hβ τ Ξ)
    _ < ⊤ := hint.lintegral_lt_top

theorem p4g_Zk_pos {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (invβ : ℝ) (τ : ℝ) :
    0 < gibbsPartitionW (p4GibbsOf invβ (p4Pot k s N τ)) :=
  p4g_lintegral_pos_of_pos (p4g_gibbsOf_meas _ (p4g_p4Pot_meas hk.smooth.continuous.measurable s N τ))
    fun _ => Real.exp_pos _

theorem p4g_Zss_lt_top {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {invβ : ℝ}
    (hβ : 0 < invβ) (τ : ℝ) :
    gibbsPartitionW (selfSimWeight d s invβ N τ) < ⊤ := by
  unfold gibbsPartitionW
  refine lt_of_le_of_lt (lintegral_mono fun Ξ => ENNReal.ofReal_le_ofReal (p4g_weight_le hk hβ τ Ξ)) ?_
  exact p4g_Zk_lt_top hk hβ τ

theorem p4g_Zss_pos (hd : 1 ≤ d) (s invβ : ℝ) (N : ℕ) (τ : ℝ) :
    0 < gibbsPartitionW (selfSimWeight d s invβ N τ) := by
  classical
  unfold gibbsPartitionW
  rw [lintegral_pos_iff_support ((p4g_ssWeight_meas d s invβ N τ).ennreal_ofReal)]
  have hsub : (eucCollisionSet d N)ᶜ ⊆ Function.support
      (fun X => ENNReal.ofReal (selfSimWeight d s invβ N τ X)) := by
    intro X hX
    have : X ∉ eucCollisionSet d N := hX
    simp [Function.mem_support, selfSimWeight, this, Real.exp_pos]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have hnull := p4g_collision_null hd N
  have hu : (volume : Measure (EucConfig d N)) Set.univ ≤
      (volume : Measure (EucConfig d N)) (eucCollisionSet d N) +
        (volume : Measure (EucConfig d N)) (eucCollisionSet d N)ᶜ := by
    calc _ = (volume : Measure (EucConfig d N)) (eucCollisionSet d N ∪ (eucCollisionSet d N)ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  rw [hnull, zero_add] at hu
  exact lt_of_lt_of_le (p4g_vol_univ_pos d N) hu


/-! ### Finite entropy implies a finite second moment -/

theorem p4g_ssWeight_nonneg (d : ℕ) (s invβ : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) :
    0 ≤ selfSimWeight d s invβ N τ Ξ := by
  classical
  unfold selfSimWeight
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem p4g_moment (hd : 1 ≤ d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {invβ : ℝ}
    (hβ : 0 < invβ) (τ : ℝ) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hfin : gibbsEntropyW (selfSimWeight d s invβ N τ) μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤ := by
  set G := selfSimWeight d s invβ N τ with hGdef
  have hGm : Measurable G := p4g_ssWeight_meas d s invβ N τ
  have hZ0 : gibbsPartitionW G ≠ 0 := (p4g_Zss_pos hd s invβ N τ).ne'
  have hZt : gibbsPartitionW G ≠ ⊤ := (p4g_Zss_lt_top hk hβ τ).ne
  haveI hQ := p4g_ref_prob G hGm hZ0 hZt
  have hKL : klDiv μ (gibbsRefW G) ≠ ⊤ := by
    intro h
    have : gibbsEntropyW G μ = ⊤ := by
      unfold gibbsEntropyW relEntropy
      rw [h]
      exact EReal.top_sub_coe _
    rw [this] at hfin
    exact lt_irrefl _ hfin
  set c : ℝ := invβ⁻¹ / 16 with hc
  have hcpos : 0 < c := by positivity
  set F : EucConfig d N → ℝ := fun x => c * ‖x‖ ^ 2 with hF
  have hFm : Measurable F := (measurable_norm.pow_const 2).const_mul _
  have hF0 : ∀ x, 0 ≤ F x := fun x => by positivity
  -- the integral against the reference
  set M : ℝ := Real.exp (invβ⁻¹ * (2 * (aSelfSim s τ * N) ^ 2)) with hM
  have hJ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) * ENNReal.ofReal (G x) < ⊤ := by
    have hint : Integrable (fun Ξ : EucConfig d N => M * Real.exp (-(c * ‖Ξ‖ ^ 2))) volume :=
      (p4g_integrable_gauss_pi (c := c) hcpos).const_mul _
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := (p4g_weight_le hk hβ τ x).trans (p4g_gibbsOf_le hk hβ τ x)
    calc Real.exp (F x) * G x ≤ Real.exp (F x) * (M * Real.exp (-(invβ⁻¹ / 8 * ‖x‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = M * Real.exp (-(c * ‖x‖ ^ 2)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          simp only [hF, hc]; ring
  set J := ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) * ENNReal.ofReal (G x) with hJdef
  have hQint : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂(gibbsRefW G) =
      (gibbsPartitionW G)⁻¹ * J := by
    unfold gibbsRefW
    rw [lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ hGm.ennreal_ofReal
        (show Measurable fun a => ENNReal.ofReal (Real.exp (F a)) from
          (Real.measurable_exp.comp hFm).ennreal_ofReal)]
    congr 1
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  have hfinJ : (gibbsPartitionW G)⁻¹ * J ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ0) hJ.ne
  set q : ℝ := ((gibbsPartitionW G)⁻¹ * J).toReal with hq
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hK : 0 ≤ Real.log (1 + q) := Real.log_nonneg (by linarith)
  have hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂(gibbsRefW G) ≤
      ENNReal.ofReal (Real.exp (Real.log (1 + q))) := by
    rw [hQint, Real.exp_log (by linarith), ← ENNReal.ofReal_toReal hfinJ]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hdv := dv_lintegral (gibbsRefW G) μ hKL hFm hF0 hK hZ
  have hlt : ∫⁻ x, ENNReal.ofReal (F x) ∂μ < ⊤ :=
    lt_of_le_of_lt hdv (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hKL, ENNReal.ofReal_lt_top⟩)
  have hrew : ∀ x : EucConfig d N, ENNReal.ofReal (‖x‖ ^ 2) =
      ENNReal.ofReal (16 * invβ) * ENNReal.ofReal (F x) := fun x => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hF, hc]
    field_simp
  simp_rw [hrew]
  rw [lintegral_const_mul _ hFm.ennreal_ofReal]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt

/-! ### The interface lemma -/

theorem p4_gibbs_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ) (invβ : ℝ) (hβ : 0 < invβ) (τ : ℝ)
    {r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) :
    (0 < gibbsPartitionW (selfSimWeight d s invβ N τ) ∧ gibbsPartitionW (selfSimWeight d s invβ N τ) < ⊤) ∧
    (0 < gibbsPartitionW (p4GibbsOf invβ (p4Pot k s N τ)) ∧
      gibbsPartitionW (p4GibbsOf invβ (p4Pot k s N τ)) < ⊤) ∧
    ∀ (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ],
      gibbsEntropyW (p4GibbsOf invβ (p4Pot k s N τ)) μ ≤ gibbsEntropyW (selfSimWeight d s invβ N τ) μ ∧
      (gibbsEntropyW (selfSimWeight d s invβ N τ) μ < ⊤ → ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤) := by
  have hZ0 := p4g_Zss_pos hd s invβ N τ
  have hZt := p4g_Zss_lt_top (N := N) hk hβ τ
  have hZ0' := p4g_Zk_pos hk invβ (N := N) τ
  have hZt' := p4g_Zk_lt_top hk hβ (N := N) τ
  refine ⟨⟨hZ0, hZt⟩, ⟨hZ0', hZt'⟩, fun μ _ => ⟨?_, p4g_moment hd hk hβ τ μ⟩⟩
  exact p4g_entropy_mono (p4g_ssWeight_meas d s invβ N τ)
    (p4g_gibbsOf_meas _ (p4g_p4Pot_meas hk.smooth.continuous.measurable s N τ))
    (p4g_ssWeight_nonneg d s invβ N τ) (p4g_weight_le hk hβ τ) (fun _ => Real.exp_pos _)
    hZ0.ne' hZt.ne hZ0'.ne' hZt'.ne μ

example := (@p4_gibbs_proof : type_of% @HRS.MP.SelfSimP4.p4_gibbs)

end HRS.MP.SelfSimP4Impl

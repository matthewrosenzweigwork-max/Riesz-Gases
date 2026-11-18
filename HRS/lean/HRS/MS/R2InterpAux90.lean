import HRS.MS.R2InterpAux89
import HRS.MS.R2PolyAux2
import HRS.MS.R2ChaosAux52

/-!
# S10.2 (worker S10R), part 90 (packet M1b): polynomial moments of the one-particle marginals of the actual law

For `P₀` with `HasR2ActualDensity` (and a Gaussian-bounded reference density), `∫ ⟨x⟩^{Pw} d(meanEmpirical P₀) < ∞`.  This is S9.5 applied to the symmetric kernel
`a(x) + a(y)`, `a = ⟨·⟩^{Pw}`, whose pair energy is `-(1/N²) ∑_i a(x_i)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_pairEnergy_sumKernel {N : ℕ} (hN : 0 < N) (a : Euc d → ℝ) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (ha : Integrable a μ) (X : EucConfig d N) :
    pairEnergy (fun x y => a x + a y) X μ = -((N : ℝ) ^ 2)⁻¹ * ∑ i, a (X i) := by
  unfold pairEnergy
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (a (X i) + a (X j)) =
      ((N : ℝ) - 2) * a (X i) + (∑ j, a (X j)) := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hN]
    have := Finset.add_sum_erase (Finset.univ : Finset (Fin N)) (fun j => a (X j)) (Finset.mem_univ i)
    simp only [Nat.cast_one]
    linarith
  have h2 : ∀ x : Euc d, ∫ y, (a x + a y) ∂μ = a x + ∫ y, a y ∂μ := by
    intro x
    rw [integral_add (integrable_const _) ha]
    simp
  have h3 : ∫ x, ∫ y, (a x + a y) ∂μ ∂μ = 2 * ∫ y, a y ∂μ := by
    simp_rw [h2]
    rw [integral_add ha (integrable_const _)]
    simp
    ring
  beta_reduce
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 (X i), h3]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem s102_marginal_moment (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L C₀ c₀ β p K : ℝ)
    (hc : 0 < c₀) (hβ : 0 < β) (hp : 1 < p) {Pw : ℝ} (hPw : 0 ≤ Pw) {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) (hG : ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) {N : ℕ} (hN : 2 ≤ N)
    {P₀ : Measure (EucConfig d N)} (hP : HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) P₀) :
    Integrable (fun x : Euc d => jbracket x ^ Pw) (HRS.Whole.meanEmpirical P₀) := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Poly.s95_conj1 hd hs0 hs M L C₀ c₀ β p K 1 Pw hc hβ hp le_rfl hPw
  have hN0 : 0 < N := by omega
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ.prob
  haveI : IsProbabilityMeasure P₀ := hP.1
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set a : Euc d → ℝ := fun x => jbracket x ^ Pw with ha
  have ham : Measurable a := ((by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
    (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')).measurable
  have ha0 : ∀ x, 0 ≤ a x := fun x => Real.rpow_nonneg (by unfold jbracket; positivity) _
  have haint : Integrable a μ := by
    obtain ⟨C1, hC1⟩ := HRS.MS.R2Chaos.s94_moment_rpow hρ.prob ⟨hc, hG⟩ hPw
    refine ⟨ham.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall ha0)]
    exact lt_of_le_of_lt hC1 ENNReal.ofReal_lt_top
  have hker : IsR2PolyPairKernel s Pw 2 (fun x y => a x + a y) := by
    refine ⟨(ham.comp measurable_fst).add (ham.comp measurable_snd), fun x y => add_comm _ _, fun x y _ => ?_⟩
    have hjx : 0 ≤ jbracket x := by unfold jbracket; positivity
    have hjy : 0 ≤ jbracket y := by unfold jbracket; positivity
    have h1 : a x ≤ (jbracket x + jbracket y) ^ Pw := Real.rpow_le_rpow hjx (by linarith) hPw
    have h2 : a y ≤ (jbracket x + jbracket y) ^ Pw := Real.rpow_le_rpow hjy (by linarith) hPw
    have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (x - y)
    rw [abs_of_nonneg (add_nonneg (ha0 x) (ha0 y))]
    have hq : 0 ≤ (jbracket x + jbracket y) ^ Pw := Real.rpow_nonneg (by linarith) _
    nlinarith [mul_nonneg hq hW]
  obtain ⟨h1, -⟩ := hC ρ hρ hG N hN P₀ hP 2 (by norm_num) _ hker
  have hmeasE : Measurable fun X : EucConfig d N => (N : ℝ) * pairEnergy (fun x y => a x + a y) X μ :=
    (HRS.MS.Wr.wr9_measurable_pairEnergy (hker.measurable)).const_mul _
  obtain ⟨hi, -⟩ := s102_integrable_of_eLpNorm_one hmeasE.aestronglyMeasurable (by positivity) h1
  have hS : Integrable (fun X : EucConfig d N => ∑ i, a (X i)) P₀ := by
    have : (fun X : EucConfig d N => ∑ i, a (X i)) = fun X => -(N : ℝ) * ((N : ℝ) * pairEnergy (fun x y => a x + a y) X μ) := by
      funext X
      rw [s102_pairEnergy_sumKernel hN0 a μ haint X]
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
      field_simp
    rw [this]
    exact hi.const_mul _
  have hcoord : ∀ i : Fin N, Integrable (fun X : EucConfig d N => a (X i)) P₀ := by
    intro i
    refine Integrable.mono' hS (ham.comp (measurable_pi_apply i)).aestronglyMeasurable (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 _)]
    exact Finset.single_le_sum (f := fun j => a (X j)) (fun j _ => ha0 _) (Finset.mem_univ i)
  rw [HRS.MS.S21.s21_meanEmpirical_eq_sum]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by exact_mod_cast hN0.ne'))
  refine integrable_finsetSum_measure.2 fun i _ => ?_
  exact (integrable_map_measure ham.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).2 (hcoord i)

end HRS.MS.R2Interp

end

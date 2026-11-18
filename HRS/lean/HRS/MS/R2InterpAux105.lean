import HRS.MS.R2InterpAux104

/-!
# S10.2 (worker S10R), part 105 (packet M2a): a uniform bound for the polynomial moment of the one-particle marginal
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_marginal_moment_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L C₀ c₀ β p K : ℝ) (hc : 0 < c₀) (hβ : 0 < β) (hp : 1 < p) {Pw : ℝ} (hPw : 0 ≤ Pw) :
    ∃ Cm : ℝ, ∀ {ρ : Euc d → ℝ}, IsRound2Density d s M L ρ → (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∀ {N : ℕ}, 2 ≤ N → ∀ {P₀ : Measure (EucConfig d N)},
        HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) P₀ →
        ∫ x, jbracket x ^ Pw ∂(HRS.Whole.meanEmpirical P₀) ≤ Cm := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Poly.s95_conj1 hd hs0 hs M L C₀ c₀ β p K 1 Pw hc hβ hp le_rfl hPw
  refine ⟨2 * C, fun {ρ} hρ hG {N} hN {P₀} hP => ?_⟩
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
  obtain ⟨hi, hb⟩ := s102_integrable_of_eLpNorm_one hmeasE.aestronglyMeasurable (by positivity) h1
  have hS : ∀ X : EucConfig d N, ∑ i, a (X i) = ‖(N : ℝ) * ((N : ℝ) * pairEnergy (fun x y => a x + a y) X μ)‖ := by
    intro X
    rw [s102_pairEnergy_sumKernel hN0 a μ haint X]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    have : (N : ℝ) * ((N : ℝ) * (-((N : ℝ) ^ 2)⁻¹ * ∑ i, a (X i))) = -∑ i, a (X i) := by
      field_simp
    rw [this, norm_neg, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => ha0 _)]
  have hSint : Integrable (fun X : EucConfig d N => ∑ i, a (X i)) P₀ := by
    have : (fun X : EucConfig d N => ∑ i, a (X i)) = fun X => ‖(N : ℝ) * ((N : ℝ) * pairEnergy (fun x y => a x + a y) X μ)‖ := by
      funext X; exact hS X
    rw [this]
    exact (hi.const_mul (N : ℝ)).norm
  have hmean : ∫ x, a x ∂(HRS.Whole.meanEmpirical P₀) = (N : ℝ)⁻¹ * ∫ X, ∑ i, a (X i) ∂P₀ := by
    have hcoord : ∀ i : Fin N, Integrable (fun X : EucConfig d N => a (X i)) P₀ := by
      intro i
      refine Integrable.mono' hSint (ham.comp (measurable_pi_apply i)).aestronglyMeasurable
        (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (ha0 _)]
      exact Finset.single_le_sum (f := fun j => a (X j)) (fun j _ => ha0 _) (Finset.mem_univ i)
    rw [HRS.MS.S21.s21_meanEmpirical_eq_sum, integral_smul_measure, integral_finsetSum_measure]
    · rw [integral_finset_sum _ fun i _ => hcoord i]
      congr 1
      · simp [ENNReal.toReal_inv]
      · refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_map (measurable_pi_apply i).aemeasurable ham.aestronglyMeasurable
    · intro i _
      exact (integrable_map_measure ham.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).2 (hcoord i)
  rw [hmean]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have : ∫ X, ∑ i, a (X i) ∂P₀ ≤ N * (2 * C) := by
    calc ∫ X, ∑ i, a (X i) ∂P₀ = ∫ X, ‖(N : ℝ) * ((N : ℝ) * pairEnergy (fun x y => a x + a y) X μ)‖ ∂P₀ :=
          integral_congr_ae (Eventually.of_forall hS)
      _ = N * ∫ X, ‖(N : ℝ) * pairEnergy (fun x y => a x + a y) X μ‖ ∂P₀ := by
          simp_rw [norm_mul, Real.norm_natCast]
          rw [integral_const_mul]
      _ ≤ N * (C * 2) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = N * (2 * C) := by ring
  calc (N : ℝ)⁻¹ * ∫ X, ∑ i, a (X i) ∂P₀ ≤ (N : ℝ)⁻¹ * (N * (2 * C)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * C := by field_simp

end HRS.MS.R2Interp

end

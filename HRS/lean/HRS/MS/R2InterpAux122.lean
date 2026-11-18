import HRS.MS.R2InterpAux121

/-!
# S10.2 (worker S10S), part 122 (packet M1c): `Env` of the polynomial envelope is integrable under the time marginals, with a uniform bound
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_gk_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀)
    {Pw : ℝ} (hP0 : 0 ≤ Pw) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      (∀ x, Integrable (s102_gk s Pw x) (HRS.Whole.withDensityReal ρ)) ∧
      Integrable (fun x => ∫ y, s102_gk s Pw x y ∂(HRS.Whole.withDensityReal ρ)) (HRS.Whole.withDensityReal ρ) ∧
      ∀ x, ∫ y, s102_gk s Pw x y ∂(HRS.Whole.withDensityReal ρ) ≤ A * jbracket x ^ Pw := by
  obtain ⟨A, hA0, hpoly⟩ := HRS.MS.R2Poly.s95_poly_int hd hs0 hs M C₀ c₀ hc hP0
  refine ⟨A, hA0, fun ρ hρ hM hG => ?_⟩
  obtain ⟨h1, h2⟩ := hpoly ρ hρ hM hG 1 zero_le_one _ (s102_gk_poly s Pw)
  obtain ⟨hi1, hi2⟩ := HRS.MS.R2Poly.s95_poly_integrable hd hs0 hs M C₀ c₀ hc hP0 ρ hρ hM hG 1 zero_le_one _
    (s102_gk_poly s Pw)
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  refine ⟨hi1, hi2.integral_prod_left, fun x => ?_⟩
  have hnn : 0 ≤ᵐ[HRS.Whole.withDensityReal ρ] fun y => s102_gk s Pw x y :=
    Eventually.of_forall fun y => s102_gk_nonneg s Pw x y
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hi1 x).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA0 (Real.rpow_nonneg (by unfold jbracket; positivity) _)) ?_
  refine le_trans (le_of_eq ?_) ((h1 x).trans (le_of_eq (by rw [mul_one])))
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal (s102_gk_nonneg s Pw x y)]

theorem s102_Env_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L C₀ c₀ β p K : ℝ)
    (hc : 0 < c₀) (hβ : 0 < β) (hp : 1 < p) {Pw : ℝ} (hPw : 0 ≤ Pw) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ {ρ : Euc d → ℝ}, IsRound2Density d s M L ρ →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ {N : ℕ}, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → EucConfig d N), Measurable Y →
      HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map Y) →
        Integrable (fun ζ => s102_Env (s102_gk s Pw) (Y ζ) (HRS.Whole.withDensityReal ρ)) P ∧
          ∫ ζ, s102_Env (s102_gk s Pw) (Y ζ) (HRS.Whole.withDensityReal ρ) ∂P ≤ CE := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cc, hCc0, hconj⟩ := HRS.MS.R2Poly.s95_conj1 hd hs0 hs M L C₀ c₀ β p K 1 Pw hc hβ hp le_rfl hPw
  obtain ⟨A, hA0, hApoly⟩ := s102_gk_int hd1 hs0 hs M C₀ c₀ hc hPw
  obtain ⟨Cm, hCm⟩ := s102_marginal_moment_bound hd hs0 hs M L C₀ c₀ β p K hc hβ hp hPw
  refine ⟨Cc + 2 * A * max Cm 0, by positivity, fun {ρ} hρ hG {N} hN {Ω} _ P _ Y hY hP => ?_⟩
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ.prob
  haveI : IsProbabilityMeasure (P.map Y) := hP.1
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set G : Euc d → Euc d → ℝ := s102_gk s Pw with hGdef
  obtain ⟨hgi, hgH, hrowb⟩ := hApoly ρ hρ.prob hρ.bdd hG
  obtain ⟨h1, -⟩ := hconj ρ hρ hG N hN (P.map Y) hP 1 zero_le_one G (s102_gk_poly s Pw)
  have hmeasE : Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy G X μ) :=
    (HRS.MS.Wr.wr9_measurable_pairEnergy (s102_gk_meas s Pw)).const_mul _
  obtain ⟨hiQ, hbQ⟩ := s102_integrable_of_eLpNorm_one hmeasE.aestronglyMeasurable (by positivity) h1
  have hiP : Integrable (fun ζ => (N : ℝ) * pairEnergy G (Y ζ) μ) P :=
    (integrable_map_measure hmeasE.aestronglyMeasurable hY.aemeasurable).1 hiQ
  have hbP : ∫ ζ, ‖(N : ℝ) * pairEnergy G (Y ζ) μ‖ ∂P ≤ Cc * 1 := by
    rw [← integral_map hY.aemeasurable hmeasE.norm.aestronglyMeasurable]
    exact hbQ
  set a : Euc d → ℝ := fun x => jbracket x ^ Pw with ha
  have ham : Measurable a := ((by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
    (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')).measurable
  have ha0 : ∀ x, 0 ≤ a x := fun x => Real.rpow_nonneg (by unfold jbracket; positivity) _
  have hmomint := s102_marginal_moment hd hs0 hs M L C₀ c₀ β p K hc hβ hp hPw hρ hG hN hP
  obtain ⟨hJi, hJeq⟩ := s102_empMoment hN0 P Y hY ham ha0 hmomint
  have hJb : ∫ ζ, (N : ℝ)⁻¹ * ∑ k, a (Y ζ k) ∂P ≤ max Cm 0 := by
    rw [hJeq]
    exact (hCm hρ hG hN hP).trans (le_max_left _ _)
  set F : Ω → ℝ := fun ζ => (N : ℝ)⁻¹ * ‖(N : ℝ) * pairEnergy G (Y ζ) μ‖ +
    2 * A * ((N : ℝ)⁻¹ * ∑ k, a (Y ζ k)) with hF
  have hFi : Integrable F P := (hiP.norm.const_mul _).add (hJi.const_mul _)
  have hpt : ∀ ζ, s102_Env G (Y ζ) μ ≤ F ζ := by
    intro ζ
    rw [s102_Env_eq]
    have hrs : ∑ i, ∫ y, G (Y ζ i) y ∂μ ≤ ∑ i, A * a (Y ζ i) :=
      Finset.sum_le_sum fun i _ => hrowb _
    have hpe : pairEnergy G (Y ζ) μ ≤ (N : ℝ)⁻¹ * ‖(N : ℝ) * pairEnergy G (Y ζ) μ‖ := by
      rw [norm_mul, Real.norm_natCast, ← mul_assoc, inv_mul_cancel₀ hN'.ne', one_mul, Real.norm_eq_abs]
      exact le_abs_self _
    have h2 : (2 / (N : ℝ)) * ∑ i, ∫ y, G (Y ζ i) y ∂μ ≤ 2 * A * ((N : ℝ)⁻¹ * ∑ k, a (Y ζ k)) := by
      calc (2 / (N : ℝ)) * ∑ i, ∫ y, G (Y ζ i) y ∂μ ≤ (2 / (N : ℝ)) * ∑ i, A * a (Y ζ i) :=
            mul_le_mul_of_nonneg_left hrs (by positivity)
        _ = 2 * A * ((N : ℝ)⁻¹ * ∑ k, a (Y ζ k)) := by
            rw [← Finset.mul_sum]; ring
    simp only [hF]
    linarith
  have hEm : Measurable fun ζ => s102_Env G (Y ζ) μ := (s102_Env_meas (s102_gk_meas s Pw)).comp hY
  have hEnn : ∀ ζ, 0 ≤ s102_Env G (Y ζ) μ := fun ζ => s102_Env_nonneg (s102_gk_nonneg s Pw) _ _
  have hEi : Integrable (fun ζ => s102_Env G (Y ζ) μ) P := by
    refine Integrable.mono' hFi hEm.aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnn ζ)]
    exact hpt ζ
  refine ⟨hEi, ?_⟩
  calc ∫ ζ, s102_Env G (Y ζ) μ ∂P ≤ ∫ ζ, F ζ ∂P := integral_mono hEi hFi hpt
    _ = (N : ℝ)⁻¹ * ∫ ζ, ‖(N : ℝ) * pairEnergy G (Y ζ) μ‖ ∂P +
        2 * A * ∫ ζ, (N : ℝ)⁻¹ * ∑ k, a (Y ζ k) ∂P := by
        simp only [hF]
        rw [integral_add (hiP.norm.const_mul _) (hJi.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ 1 * (Cc * 1) + 2 * A * max Cm 0 := by
        gcongr
        · exact inv_le_one_of_one_le₀ (by exact_mod_cast hN0)
    _ = Cc + 2 * A * max Cm 0 := by ring

end HRS.MS.R2Interp

end

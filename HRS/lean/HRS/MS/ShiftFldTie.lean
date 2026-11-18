import HRS.MS.ShiftFldAux3

/-!
# S79: `HRS.Whole.shifted_field_static` (S7.9, static clause of `S:cor:shifted-field-path`)

`shifted_field_static_proof : type_of% @HRS.Whole.shifted_field_static` (no statement adjusted).  Route (TeX S L6171-6188):
`eta_N = zeta_N + sqrt N (m_N - mu)` (`eta_eq_zeta_add`), the exactly centered static field bound
`d_{C_b^2(B_m)}(zeta_N, Z) <= C_1 sqrt(delta_N)` (S4.5 `S45.quadratic_static_field_osc_proof`), the deterministic remainder
`||sqrt N (m_N - mu) - N^{3/2-p} b|| <= K C_b N^{3/2-p-theta}` (S7.1 `S71.sharp_bias_quadratic_proof`, `s79_shift_bound`), and
`s79_smoothDist_shifted_le` (translations preserve the `C_b^2` ball).  The constant is `max C_1 0 + K max C_b 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

theorem shifted_field_static_proof : type_of% @HRS.Whole.shifted_field_static := by
  intro d s hd hs hsd a β ha hβ J hJ m hm
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have hmd : (d : ℝ) < m := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ d := hd0
    linarith [show (0 : ℝ) < d from by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith]
  obtain ⟨C1, hC1⟩ := S45.quadratic_static_field_osc_proof hd hs0 hsd a β ha hβ J hJ m hm
  obtain ⟨hprob, -, -, hcan, Cb, hCb⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  obtain ⟨K, hK0, hK⟩ := s79_shift_bound hd hs hsd hmd
  obtain ⟨Cs, -, hS⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  refine ⟨max C1 0 + K * max Cb 0, ?_⟩
  intro N hN γ hγ
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hSN := hS N hN
  set P := canonicalGibbs (rieszKernel d s) (confinement a) N β with hPdef
  haveI : IsProbabilityMeasure P := hSN.prob
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hprob
  haveI : IsGaussian γ := hγ.1.1
  obtain ⟨hmeasζ, hdist⟩ := hC1 N hN γ hγ
  set μ := thermalMeasure d s a β with hμdef
  set c : OscDual d m := Real.sqrt N • OscDual.ofMeasureDiff m (meanEmpirical P) μ with hc
  set c' : OscDual d m := (N : ℝ) ^ (3 / 2 - biasP d s) •
    biasField m d s β (thermalDensity d s a β) with hc'
  have hη : ∀ X : EucConfig d N, etaB m X μ = zetaB m P X + c := fun X =>
    eta_eq_zeta_add m hmd P μ X hN1
  have hfun : (fun X : EucConfig d N => etaB m X μ) = fun X => zetaB m P X + c := funext hη
  have hmeasη : Measurable (fun X : EucConfig d N => etaB m X μ) := by
    rw [hfun]; exact hmeasζ.add_const c
  refine ⟨hmeasη, ?_⟩
  have hlaw : HRS.law P (fun X : EucConfig d N => etaB m X μ) =
      (HRS.law P (zetaB m P)).map (· + c) := by
    unfold HRS.law
    rw [Measure.map_map (measurable_add_const c) hmeasζ, hfun]
    rfl
  rw [hlaw]
  -- the deterministic remainder
  have hmean : meanEmpirical P = firstMarginal (modulatedGibbs (rieszKernel d s) N β μ) := by
    rw [meanEmpirical_eq_firstMarginal P hSN.exch hN1, hPdef, hcan N]
  have hrem : ‖c - c'‖ ≤ K * max Cb 0 * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by
    have := hK β (thermalDensity d s a β) hprob N hN Cb (hCb N hN1)
    rw [hc, hc', hmean]
    exact this
  have hδ0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  have hpow : 0 ≤ (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := Real.rpow_nonneg hN0.le _
  have hCb0 : 0 ≤ K * max Cb 0 := mul_nonneg hK0 (le_max_right _ _)
  calc HRS.smoothDist 2 ((HRS.law P (zetaB m P)).map (· + c)) (γ.map fun z => z + c')
      ≤ HRS.smoothDist 2 (HRS.law P (zetaB m P)) γ + ‖c - c'‖ :=
        s79_smoothDist_shifted_le _ _ c c'
    _ ≤ max C1 0 * Real.sqrt (deltaN d s N) +
          K * max Cb 0 * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) :=
        add_le_add (hdist.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0)) hrem
    _ ≤ (max C1 0 + K * max Cb 0) * (Real.sqrt (deltaN d s N) +
          (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) := by
        have h1 : 0 ≤ max C1 0 := le_max_right _ _
        nlinarith [mul_nonneg h1 hpow, mul_nonneg hCb0 hδ0]

example := (@shifted_field_static_proof : type_of% @HRS.Whole.shifted_field_static)

end HRS.Whole.S79

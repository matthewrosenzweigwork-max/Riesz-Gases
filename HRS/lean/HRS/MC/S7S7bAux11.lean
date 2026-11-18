import HRS.MC.S7S7bAux10
import HRS.MC.SEdgeB5a
import HRS.MC.SEdgeB1

/-!
# Packet `s7_S7b_weighted_moments`, helper 11: the uniform mean bias
`|E_Q mu_N(w) - mu(w)| <= C sup|w| / N` for every smooth `w`, with `C` independent of `w` and `N`
(`sed_B6_mean_bias` made uniform: the transport field is the Poisson solution with an `H^1` bound).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE

variable {d : ℕ} {s : ℝ}

/-- The exact form of the mean bias (the proof of `sed_B6_mean_bias`, for a given transport field). -/
theorem s7b_bias_formula (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {w r : Torus d → ℝ} (hw : Torus.IsSmooth w)
    (hr : Torus.IsSmooth r) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x))
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) w x) {N : ℕ} (hN : 1 ≤ N) :
    |∫ X, pair (empirical X) w ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) w| =
      β * |∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
        ∂(sed_Q d s N β ρ)| / N := by
  obtain ⟨hint, -⟩ := HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ hv
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  haveI hQ : IsProbabilityMeasure (sed_Q d s N β ρ) := B5a.b5a_Q_prob hd hs0 hs hβ hρ hN
  obtain ⟨hwm, Mw, hwb⟩ := B5a.b5a_w_facts hd hs0 hs hρ hr hresp
  have key := HRS.MC.SEdge.B5a.sed_B5a_stein_raw_proof hd hs0 hs hβ hρ hN hr hv hdiv hresp (hint N hN)
    (Ψ := fun _ => 1) (dΨ := fun _ _ _ => 0) measurable_const ⟨1, fun _ => by simp⟩
    (fun _ _ => measurable_const) ⟨0, fun _ _ _ => by simp⟩
    (fun i k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [one_mul, mul_zero, Finset.sum_const_zero, integral_zero] at key
  have hmeas : Measurable (fun X : Config d N => pair (empirical X) w) := by
    have : (fun X : Config d N => pair (empirical X) w) = fun X => (N : ℝ)⁻¹ * ∑ i, w (X i) :=
      funext fun X => pair_empirical (by omega) X w
    rw [this]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hwm.comp (measurable_pi_apply i))
  have hI1 : Integrable (fun X : Config d N => pair (empirical X) w) (sed_Q d s N β ρ) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable Mw (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    rw [pair_empirical (by omega) X w, abs_mul, abs_of_pos (inv_pos.2 hNp)]
    have h1 : |∑ i, w (X i)| ≤ N * Mw := by
      calc |∑ i, w (X i)| ≤ ∑ i, |w (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Mw := Finset.sum_le_sum fun i _ => hwb _
        _ = N * Mw := by simp
    calc (N : ℝ)⁻¹ * |∑ i, w (X i)| ≤ (N : ℝ)⁻¹ * (N * Mw) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNp.le)
      _ = Mw := by field_simp
  have hI2 : Integrable (fun X : Config d N =>
      (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) (sed_Q d s N β ρ) :=
    (hint N hN).const_mul _
  have hsplit : ∫ X, ((N : ℝ) * (pair (empirical X) w - pair (withDensityReal ρ) w) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)))
      ∂(sed_Q d s N β ρ) =
      (N : ℝ) * (∫ X, pair (empirical X) w ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) w) +
        β * ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
          ∂(sed_Q d s N β ρ) := by
    have hA : Integrable (fun X : Config d N => (N : ℝ) *
        (pair (empirical X) w - pair (withDensityReal ρ) w)) (sed_Q d s N β ρ) :=
      (hI1.sub (integrable_const _)).const_mul _
    have hA2 : Integrable (fun X : Config d N => β * ((N : ℝ) *
        modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) (sed_Q d s N β ρ) :=
      hI2.const_mul _
    rw [integral_add hA hA2, integral_const_mul, integral_const_mul,
      integral_sub hI1 (integrable_const _)]
    simp
  rw [hsplit] at key
  have heq : ∫ X, pair (empirical X) w ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) w =
      -(β * ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
          ∂(sed_Q d s N β ρ)) / N := by
    field_simp
    linarith
  rw [heq, abs_div, abs_neg, abs_of_pos hNp, abs_mul, abs_of_nonneg hβ]

/-- **Uniform mean bias**: `|E_Q mu_N(w) - mu(w)| <= C T / N` for every smooth `w` with `|w| <= T`. -/
theorem s7b_bias_uniform (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Torus d → ℝ) (T : ℝ), Torus.IsSmooth w → (∀ x, |w x| ≤ T) →
      ∀ N : ℕ, 1 ≤ N →
        |∫ X, pair (empirical X) w ∂(sed_Q d s N γ ρ) - pair (withDensityReal ρ) w| ≤ C * T / N := by
  obtain ⟨A0, hA0, hA⟩ := HRS.MC.Sec7.S7a.s7a_L2 hd hs0 hs hγ hρ
  obtain ⟨P, hP0, hP⟩ := s7b_v_exists_H1 hd hρ
  obtain ⟨C9, hC9, h9⟩ := s7b_hv_L2 hd hs0 hs hρ
  obtain ⟨C10, hC10, h10⟩ := s7b_energy_mean hd hs0 hs hγ hρ
  refine ⟨γ * (C10 * Real.sqrt (C9 * (d * (P ^ 2 * A0)))), by positivity, ?_⟩
  intro w T hw hwT N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨r, v₀, hr, -, -, hresp, hmean, -⟩ :=
    HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hγ hρ hw
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hwT 0)
  have hwc : Continuous w := HRS.Q66.q66_cont_of_smooth hw
  have hrc : Continuous r := HRS.Q66.q66_cont_of_smooth hr
  have hr2 : hsNormSq 0 (coeffOf r) ≤ A0 * T ^ 2 := hA r w T hrc hwc hwT hresp hmean
  obtain ⟨v, hvs, hvdiv, hvH⟩ := hP r hr hmean
  rw [HRS.MC.Sec7.S7b.s7b_bias_formula hd hs0 hs hγ hρ hw hr hvs hvdiv hresp hN]
  have hH1 : ∑ j, hsNormSq (1 : ℝ) (coeffOf (v j)) ≤ d * (P ^ 2 * (A0 * T ^ 2)) := by
    have hj : ∀ j, hsNormSq (1 : ℝ) (coeffOf (v j)) ≤ P ^ 2 * (A0 * T ^ 2) := by
      intro j
      obtain ⟨-, hb⟩ := hvH j
      have h0 : 0 ≤ hsNormSq (1 : ℝ) (coeffOf (v j)) :=
        tsum_nonneg fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
      have hn0 : 0 ≤ hsNormSq (0 : ℝ) (coeffOf r) :=
        tsum_nonneg fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)
      have e1 : hsNormSq (1 : ℝ) (coeffOf (v j)) = HRS.PDE.hsNorm (1 : ℝ) (coeffOf (v j)) ^ 2 := by
        unfold HRS.PDE.hsNorm; rw [Real.sq_sqrt h0]
      have e2 : hsNormSq (0 : ℝ) (coeffOf r) = HRS.PDE.hsNorm (0 : ℝ) (coeffOf r) ^ 2 := by
        unfold HRS.PDE.hsNorm; rw [Real.sq_sqrt hn0]
      rw [e1]
      calc HRS.PDE.hsNorm (1 : ℝ) (coeffOf (v j)) ^ 2
          ≤ (P * HRS.PDE.hsNorm (0 : ℝ) (coeffOf r)) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
        _ = P ^ 2 * hsNormSq (0 : ℝ) (coeffOf r) := by rw [mul_pow, ← e2]
        _ ≤ P ^ 2 * (A0 * T ^ 2) := mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)
    calc ∑ j, hsNormSq (1 : ℝ) (coeffOf (v j)) ≤ ∑ _j : Fin d, P ^ 2 * (A0 * T ^ 2) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = d * (P ^ 2 * (A0 * T ^ 2)) := by simp
  have hL2 := h9 v hvs (fun j => (hvH j).1)
  have hEn := h10 v hvs N hN
  set Th := ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hTh
  have hTh' : Th ≤ C9 * (d * (P ^ 2 * (A0 * T ^ 2))) :=
    hL2.trans (mul_le_mul_of_nonneg_left hH1 hC9)
  have hsq : Real.sqrt Th ≤ Real.sqrt (C9 * (d * (P ^ 2 * A0))) * T := by
    calc Real.sqrt Th ≤ Real.sqrt (C9 * (d * (P ^ 2 * (A0 * T ^ 2)))) := Real.sqrt_le_sqrt hTh'
      _ = Real.sqrt ((C9 * (d * (P ^ 2 * A0))) * T ^ 2) := by congr 1; ring
      _ = Real.sqrt (C9 * (d * (P ^ 2 * A0))) * T := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hT0]
  calc γ * |∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
          ∂(sed_Q d s N γ ρ)| / N
      ≤ γ * (C10 * Real.sqrt Th) / N := by
        gcongr
    _ ≤ γ * (C10 * (Real.sqrt (C9 * (d * (P ^ 2 * A0))) * T)) / N := by
        gcongr
    _ = _ := by ring

end HRS.MC.Sec7.S7b

end

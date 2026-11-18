import HRS.MC.S7S7bAux9
import HRS.MC.SEdgeB4b

/-!
# Packet `s7_S7b_weighted_moments`, helper 10: the mean energy under `Q_{N,gamma}` in terms of `||h_v||_{L^2}`
`|E_Q N mE(h_v)| <= C (iint h_v^2)^{1/2}`, `C` independent of `v` and `N` (Holder transfer + `q08_energy_L2`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE

variable {d : ℕ} {s : ℝ}

theorem s7b_energy_mean (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin d → Torus d → ℝ, (∀ j, Torus.IsSmooth (v j)) → ∀ N : ℕ, 1 ≤ N →
      |∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) ∂(sed_Q d s N γ ρ)| ≤
        C * Real.sqrt (∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ)) := by
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨C2, hC2, T2⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hγ hρ (r := 2)
    (by norm_num)
  refine ⟨C2 * Real.sqrt 3 + 1 / 2, by positivity, fun v hv N hN => ?_⟩
  haveI hG : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  haveI hPP : IsProbabilityMeasure (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
    infer_instance
  set T : ℝ := ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hT
  have hT0 : 0 ≤ T := integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _
  set J : ℝ := ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  have hJT : |J| ≤ Real.sqrt T := by
    -- Cauchy-Schwarz on the probability product measure
    have hint2 := HRS.MC.SEdge.B2b.sed_B2b_hs_proof hd hs0 hs hρ hv
    have hmeas : Measurable (fun p : Torus d × Torus d => Q66.q66_hv d s v p.1 p.2) := by
      have hsd : s < (d : ℝ) := by
        have : (0 : ℝ) ≤ d := by positivity
        linarith
      exact Q66.q66_hv_measurable hsd (fun j => HRS.StaticLimitAux.continuous_of_smooth (hv j))
    have hmem : MemLp (fun p : Torus d × Torus d => Q66.q66_hv d s v p.1 p.2) 2
        ((withDensityReal ρ).prod (withDensityReal ρ)) := by
      refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hint2
    have hi1 : Integrable (fun p : Torus d × Torus d => Q66.q66_hv d s v p.1 p.2)
        ((withDensityReal ρ).prod (withDensityReal ρ)) := hmem.integrable (by norm_num)
    set m : ℝ := ∫ p : Torus d × Torus d, Q66.q66_hv d s v p.1 p.2
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hm
    have hJm : J = m := by
      rw [hJ, hm, integral_prod _ hi1]
    have hTm : T = ∫ p : Torus d × Torus d, Q66.q66_hv d s v p.1 p.2 ^ 2
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) := by
      rw [hT, integral_prod _ hint2]
    have h0 : 0 ≤ ∫ p : Torus d × Torus d, (Q66.q66_hv d s v p.1 p.2 - m) ^ 2
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) :=
      integral_nonneg fun p => sq_nonneg _
    have e : ∫ p : Torus d × Torus d, (Q66.q66_hv d s v p.1 p.2 - m) ^ 2
        ∂((withDensityReal ρ).prod (withDensityReal ρ)) =
        T - m ^ 2 := by
      have : (fun p : Torus d × Torus d => (Q66.q66_hv d s v p.1 p.2 - m) ^ 2) =
          fun p => (Q66.q66_hv d s v p.1 p.2 ^ 2 - (2 * m) * Q66.q66_hv d s v p.1 p.2) + m ^ 2 :=
        funext fun p => by ring
      have hs1 : Integrable (fun p : Torus d × Torus d =>
          Q66.q66_hv d s v p.1 p.2 ^ 2 - (2 * m) * Q66.q66_hv d s v p.1 p.2)
          ((withDensityReal ρ).prod (withDensityReal ρ)) := hint2.sub (hi1.const_mul _)
      rw [this, integral_add hs1 (integrable_const _), integral_sub hint2 (hi1.const_mul _),
        integral_const_mul, ← hTm, ← hm]
      simp
      ring
    have hm2 : m ^ 2 ≤ T := by linarith
    calc |J| = Real.sqrt (J ^ 2) := (Real.sqrt_sq_eq_abs J).symm
      _ ≤ Real.sqrt T := by rw [hJm]; exact Real.sqrt_le_sqrt hm2
  obtain ⟨hYm, hYL, hYint⟩ := HRS.MC.SEdge.B4b.b4b_L2 hd hs0 hs hρ hv N hN
  set Y : Config d N → ℝ := HRS.MC.SEdge.B4b.b4b_Y d s ρ v N with hYdef
  have hYsq : ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
      ENNReal.ofReal (3 * T) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hYL.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hYint
  have hA : ∫⁻ X, ENNReal.ofReal |Y X| ∂(sed_Q d s N γ ρ) ≤
      ENNReal.ofReal (C2 * Real.sqrt (3 * T)) := by
    have h1 := T2 N hN (fun X => ENNReal.ofReal |Y X|) hYm.abs.ennreal_ofReal
    have h2 : ∫⁻ X, (ENNReal.ofReal |Y X|) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)
        = ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) := by
      refine lintegral_congr fun X => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
    rw [h2] at h1
    refine h1.trans ?_
    calc ENNReal.ofReal C2 * (∫⁻ X, ENNReal.ofReal (Y X ^ 2)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / (2 : ℝ))
        ≤ ENNReal.ofReal C2 * (ENNReal.ofReal (3 * T)) ^ (1 / (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal (C2 * Real.sqrt (3 * T)) := by
        rw [ENNReal.ofReal_mul hC2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          Real.sqrt_eq_rpow]
  have hGY : Integrable Y (sed_Q d s N γ ρ) := by
    refine ⟨hYm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hA ENNReal.ofReal_lt_top
  have hYabs : ∫ X, |Y X| ∂(sed_Q d s N γ ρ) ≤ C2 * Real.sqrt (3 * T) := by
    have := ofReal_integral_eq_lintegral_ofReal hGY.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    rw [← this] at hA
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hA
  have hNmE : ∀ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) =
      Y X - J / 2 := by
    intro X
    simp only [hYdef, HRS.MC.SEdge.B4b.b4b_Y, hJ]
    ring
  have hint2 : ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
      ∂(sed_Q d s N γ ρ) = (∫ X, Y X ∂(sed_Q d s N γ ρ)) - J / 2 := by
    simp_rw [hNmE]
    rw [integral_sub hGY (integrable_const _)]
    simp
  rw [hint2]
  have hcA : |∫ X, Y X ∂(sed_Q d s N γ ρ)| ≤ C2 * Real.sqrt (3 * T) :=
    (abs_integral_le_integral_abs).trans hYabs
  have h3 : Real.sqrt (3 * T) = Real.sqrt 3 * Real.sqrt T := Real.sqrt_mul (by norm_num) T
  calc |(∫ X, Y X ∂(sed_Q d s N γ ρ)) - J / 2|
      ≤ |∫ X, Y X ∂(sed_Q d s N γ ρ)| + |J / 2| := abs_sub _ _
    _ ≤ C2 * Real.sqrt (3 * T) + Real.sqrt T / 2 := by
        have : |J / 2| = |J| / 2 := by rw [abs_div]; norm_num
        rw [this]
        linarith
    _ = (C2 * Real.sqrt 3 + 1 / 2) * Real.sqrt T := by rw [h3]; ring

end HRS.MC.Sec7.S7b

end

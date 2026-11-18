import HRS.MC.S7S7cAux8

/-!
# Packet `s7_S7c_hilbert_stein`, helper 9: dominated convergence along the Fourier truncations
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

open Classical

variable {d : ℕ}

theorem s7c_continuous_truncE {r : ℝ} (K : Finset (NonzeroLattice d)) :
    Continuous (fun x : NegSobolev d r => truncE K x) := by
  have : (fun x : NegSobolev d r => truncE K x) =
      fun x => ∑ k ∈ K, NegSobolev.coord x k • s7_eps r k := rfl
  rw [this]
  exact continuous_finset_sum _ fun k _ => (negCoordCLM k).continuous.smul continuous_const

section DCT

variable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6)
  {N : ℕ} (hN : 1 ≤ N)
include hd hs0 hs hγ hρ hr hN

/-- Dominated convergence for `E[Phi * G(Pi_K W_N)]` with `G` continuous and bounded. -/
theorem s7c_dct_prod {G : NegSobolev d r → ℝ} (hG : Continuous G) {M : ℝ}
    (hGM : ∀ y, |G y| ≤ M) {Φ : Config d N → ℝ} (hΦ : Integrable Φ (sed_Q d s N γ ρ)) :
    Tendsto (fun K : Finset (NonzeroLattice d) =>
        ∫ X, Φ X * G (truncE K (zetaE r (sed_Q d s N γ ρ) X)) ∂(sed_Q d s N γ ρ)) atTop
      (𝓝 (∫ X, Φ X * G (zetaE r (sed_Q d s N γ ρ) X) ∂(sed_Q d s N γ ρ))) := by
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hWm := s7c_zeta_meas hN hr' (sed_Q d s N γ ρ)
  refine tendsto_integral_filter_of_dominated_convergence (fun X => |Φ X| * M)
    (Filter.Eventually.of_forall fun K => ?_) (Filter.Eventually.of_forall fun K => ?_)
    (hΦ.abs.mul_const M) (Filter.Eventually.of_forall fun X => ?_)
  · exact hΦ.aestronglyMeasurable.mul
      (hG.measurable.comp ((s7c_continuous_truncE K).measurable.comp hWm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hGM _) (abs_nonneg _)
  · exact ((hG.tendsto _).comp (s7c_tendsto_trunc _)).const_mul _

theorem s7c_lim_L {F : NegSobolev d r → ℝ} (hF : s7_C2b F) :
    Tendsto (fun K : Finset (NonzeroLattice d) =>
        ∫ X, fderiv ℝ F (truncE K (zetaE r (sed_Q d s N γ ρ) X))
          (truncE K (zetaE r (sed_Q d s N γ ρ) X)) ∂(sed_Q d s N γ ρ)) atTop
      (𝓝 (∫ X, fderiv ℝ F (zetaE r (sed_Q d s N γ ρ) X) (zetaE r (sed_Q d s N γ ρ) X)
        ∂(sed_Q d s N γ ρ))) := by
  obtain ⟨hF2, M1, M2, hM1, hM2, h1, h2⟩ := s7c_C2b_facts hF
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hWm := s7c_zeta_meas hN hr' (sed_Q d s N γ ρ)
  have hcont : Continuous (fun y : NegSobolev d r => fderiv ℝ F y y) :=
    (hF2.continuous_fderiv (by norm_num)).clm_apply continuous_id
  refine tendsto_integral_filter_of_dominated_convergence
    (fun X => M1 * ‖zetaE r (sed_Q d s N γ ρ) X‖)
    (Filter.Eventually.of_forall fun K => ?_) (Filter.Eventually.of_forall fun K => ?_)
    ((s7c_W_integrable hd hs0 hs hγ hρ hr hN).const_mul M1) (Filter.Eventually.of_forall fun X => ?_)
  · exact (hcont.measurable.comp ((s7c_continuous_truncE K).measurable.comp hWm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs]
    calc |fderiv ℝ F (truncE K (zetaE r (sed_Q d s N γ ρ) X)) (truncE K (zetaE r (sed_Q d s N γ ρ) X))|
        ≤ ‖fderiv ℝ F (truncE K (zetaE r (sed_Q d s N γ ρ) X))‖ *
            ‖truncE K (zetaE r (sed_Q d s N γ ρ) X)‖ :=
          (Real.norm_eq_abs _).symm.le.trans (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ M1 * ‖zetaE r (sed_Q d s N γ ρ) X‖ :=
          mul_le_mul (h1 _) (s7c_norm_trunc_le K _) (norm_nonneg _) hM1
  · exact (hcont.tendsto _).comp (s7c_tendsto_trunc _)

end DCT

end HRS.MC.Sec7.S7c

end

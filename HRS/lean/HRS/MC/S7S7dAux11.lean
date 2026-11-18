import HRS.MC.S7S7dAux10

/-!
# Packet `s7_S7d_uniform_limits`, helper 11: the law of the finite marginals of `G`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_memLp_smooth {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) : MemLp ψ 2 (withDensityReal ρ) := by
  have hc : Continuous ψ := HRS.Q66.q66_cont_of_smooth hψ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  exact MemLp.of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

theorem s7d_law_G (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) {p : ℕ} (κ : Fin p → NonzeroLattice d)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) :
    G.map (s7d_Wmap r κ) = multivariateGaussian 0 (sed_Cmat d s γ ρ (fun a => s7_phi r (κ a))) := by
  classical
  haveI : IsGaussian G := hG.1.1
  set W := s7d_Wmap r κ with hW
  set φ : Fin p → Torus d → ℝ := fun a => s7_phi r (κ a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ a)
  set C := sed_Cmat d s γ ρ φ with hC
  have hpsd : C.PosSemidef := HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hγ hρ hφ
  have hWm : Measurable W := W.continuous.measurable
  have hWa : ∀ (u : NegSobolev d r) (a : Fin p), W u a = NegSobolev.eval u (φ a) := fun u a => by
    rw [hW, s7d_Wmap_apply]
    exact (s7d_eval_phi u (κ a)).symm
  have hint : ∀ a b : Fin p, Integrable (fun u => W u a * W u b) G := by
    intro a b
    have hLa : ∀ c : Fin p, MemLp (fun u => W u c) 2 G := by
      intro c
      have : (fun u => W u c) = ⇑(negCoordCLM (m := r) (κ c)) := by
        funext u; rw [hW, s7d_Wmap_apply]; rfl
      rw [this]
      exact IsGaussian.memLp_dual G _ 2 (by simp)
    exact (hLa a).integrable_mul (hLa b)
  have hrep : ∀ b : Fin p, ∀ x, responseRep (periodicRiesz d s) (withDensityReal ρ) γ (φ b) x =
      a (κ b) x := fun b x =>
    HRS.MC.Sec7.S7e.s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ (s7d_memLp_smooth hρ (hφ b))
      (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a (κ b))) (by simpa [pair] using hmode.mean_zero (κ b))
      (hmode.resp (κ b)) x
  have hcov : ∀ a b : Fin p, ∫ u, W u a * W u b ∂G = C a b := by
    intro a b
    simp_rw [hWa]
    rw [hG.2 _ _ (hφ a) (hφ b)]
    have hae := s7d_respInv_ae hd hs0 hs hγ hρ (s7d_memLp_smooth hρ (hφ b))
      (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a (κ b))) (by simpa [pair] using hmode.mean_zero (κ b))
      (hmode.resp (κ b))
    show _ = ∫ x, φ a x * responseInverse (periodicRiesz d s) (withDensityReal ρ) γ (φ b) x
      ∂(withDensityReal ρ)
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, hrep b x]
  haveI : IsGaussian (G.map W) := inferInstance
  haveI : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C) := inferInstance
  have hmean : ∫ z, id z ∂(G.map W) = 0 := by
    set m0 : EuclideanSpace ℝ (Fin p) := ∫ z, id z ∂(G.map W) with hm0
    have h1 : inner ℝ m0 m0 = ∫ z, inner ℝ m0 (id z) ∂(G.map W) := by
      rw [integral_inner IsGaussian.integrable_id]
    rw [integral_map hWm.aemeasurable (by fun_prop)] at h1
    have h2 : ∫ u, inner ℝ m0 (id (W u)) ∂G =
        ∫ u, ((innerSL ℝ m0).comp W) u ∂G := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp
    rw [h2, hG.1.2 ((innerSL ℝ m0).comp W)] at h1
    exact inner_self_eq_zero.1 h1
  refine IsGaussian.ext ?_ ?_
  · rw [hmean]
    simp
  · ext x y
    rw [covarianceBilin_multivariateGaussian hpsd]
    rw [covarianceBilin_apply IsGaussian.memLp_two_id, hmean]
    simp only [id, sub_zero]
    rw [integral_map hWm.aemeasurable (by fun_prop)]
    have hexp : ∀ u, inner ℝ x (W u) * inner ℝ y (W u) =
        ∑ a, ∑ b, (x a * y b) * (W u a * W u b) := by
      intro u
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [hexp]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _]
    simp_rw [integral_finsetSum _ fun b _ => (hint _ b).const_mul _, integral_const_mul, hcov]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end HRS.MC.Sec7.S7d

end

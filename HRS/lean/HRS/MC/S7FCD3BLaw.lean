import HRS.MC.SEdgeS16aAux4
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB11a
import HRS.MC.S7S7dAux11
import HRS.MC.S7S7eAux2

/-!
# FC-D3 (L5), helper: Gaussian identification at a general smooth positive background

The Haar-specific identification `s16a_law_G` of packet S16a, generalised to a smooth positive background
`ρ` and a temperature parameter `γ ≥ 0`.  The covariance hypothesis is stated with `responseRep`
(as in `static_field`); for smooth test functions `responseRep` is `withDensityReal ρ`-a.e. equal to
`responseInverse` (`d3b_rep_ae`, via `sed_B1_regular_proof` and `s7e_responseRep_eq_of_eq`), which gives
the matrix `sed_Cmat`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCD3B

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.SEdge.S16a

variable {d : ℕ} {s : ℝ}

/-- `responseRep` is the `withDensityReal ρ`-a.e. representative of `responseInverse` for smooth `ψ`. -/
theorem d3b_rep_ae (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ =ᵐ[withDensityReal ρ]
      responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ := by
  obtain ⟨rr, _, hr_s, _, hr_ae, heq, hmean, _⟩ :=
    HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hγ hρ hψ
  have hrc : Continuous rr := HRS.Q66.q66_cont_of_smooth hr_s
  have hmem : MemLp ψ 2 (withDensityReal ρ) := HRS.MC.Sec7.S7d.s7d_memLp_smooth hρ hψ
  have hrep := HRS.MC.Sec7.S7e.s7e_responseRep_eq_of_eq hd hs0 hs hγ hρ hmem hrc hmean heq
  filter_upwards [hr_ae] with x hx
  rw [hrep x, hx]

/-- The covariance matrix entries: `responseInverse` may be replaced by `responseRep`. -/
theorem d3b_Cmat_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∫ x, φ x * responseInverse (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) =
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ) := by
  refine integral_congr_ae ?_
  filter_upwards [d3b_rep_ae hd hs0 hs hγ hρ hψ] with x hx
  rw [hx]

/-- **Law of the coefficient vector under `G`** at a general smooth positive background. -/
theorem d3b_law_G (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ}
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    (S : Finset (NonzeroLattice d)) :
    G.map (s16a_Wmap r S) =
      multivariateGaussian 0 (sed_Cmat d s γ ρ (s16a_phi S)) := by
  classical
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  haveI : IsGaussian G := hG.1.1
  set W := s16a_Wmap r S with hW
  set C := sed_Cmat d s γ ρ (s16a_phi S) with hC
  have hpsd : C.PosSemidef :=
    HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hγ hρ (fun a => s16a_phi_smooth S a)
  have hWm : Measurable W := W.continuous.measurable
  have hWa : ∀ (u : NegSobolev d r) (a : Fin S.card),
      W u a = NegSobolev.eval u (s16a_phi S a) := fun u a => by
    rw [hW, s16a_Wmap_apply]
    exact (s16a_eval_realMode u _).symm
  have hint : ∀ a b : Fin S.card, Integrable (fun u => W u a * W u b) G := by
    intro a b
    have hLa : ∀ c : Fin S.card, MemLp (fun u => W u c) 2 G := by
      intro c
      have : (fun u => W u c) = ⇑(s16a_cf r (s16a_e S c)) := by
        funext u; rw [hW, s16a_Wmap_apply]; rfl
      rw [this]
      exact IsGaussian.memLp_dual G _ 2 (by simp)
    exact (hLa a).integrable_mul (hLa b)
  have hcov : ∀ a b : Fin S.card, ∫ u, W u a * W u b ∂G = C a b := by
    intro a b
    simp_rw [hWa]
    rw [hG.2 _ _ (s16a_phi_smooth S a) (s16a_phi_smooth S b)]
    exact (d3b_Cmat_eq hd hs0 hs hγ hρ (φ := s16a_phi S a) (s16a_phi_smooth S b)).symm
  haveI : IsGaussian (G.map W) := inferInstance
  haveI : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin S.card)) C) := inferInstance
  -- mean of the push-forward
  have hmean : ∫ z, id z ∂(G.map W) = 0 := by
    set m0 : EuclideanSpace ℝ (Fin S.card) := ∫ z, id z ∂(G.map W) with hm0
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

end HRS.MC.Sec7.FCD3B

end

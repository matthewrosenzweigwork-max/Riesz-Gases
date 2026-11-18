import HRS.MC.SEdgeS16aAux3

/-!
# S16a, Aux4: the law of the finite-dimensional marginals of `G`

`G.map (s16a_Wmap m S) = multivariateGaussian 0 (sed_Cmat ...)` (Gaussian measures on `ℝ^p` with the same
mean and covariance coincide, `ProbabilityTheory.IsGaussian.ext`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.S16a

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {m : ℝ}

theorem s16a_eval_realMode (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal k k]
    simp
  · intro l hl
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal l k, if_neg hl]
    simp

section Resp

variable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
include hd hs0 hs hβ

/-- `responseRep` is the `volume`-a.e. representative of `responseInverse` at the Haar background. -/
theorem s16a_rep_ae {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    responseRep (periodicRiesz d s) (volume : Measure (Torus d)) β ψ =ᵐ[volume]
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β ψ := by
  have hsd : s < d := by
    have : (d : ℝ) / 2 ≤ d := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    linarith
  have hc : Continuous ψ := HRS.Q66.q66_cont_of_smooth hψ
  have hdens : IsProbDensity (fun _ : Torus d => (1 : ℝ)) := (s16a_smoothPos (d := d)).density
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hmem : MemLp ψ 2 (withDensityReal (fun _ : Torus d => (1 : ℝ))) := by
    rw [s16a_wdr_one]
    exact MemLp.of_bound hc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  obtain ⟨h, hh, _⟩ := exists_unique_response hd hs0 hsd (fun _ : Torus d => (1 : ℝ)) hdens 1
    (fun _ => le_rfl) β hβ ψ hmem
  rw [s16a_wdr_one] at hh
  have hex : ∃ h, IsResponse (periodicRiesz d s) (volume : Measure (Torus d)) β ψ h := ⟨h, hh⟩
  have hr : IsResponse (periodicRiesz d s) (volume : Measure (Torus d)) β ψ
      (responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β ψ) := by
    unfold responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  filter_upwards [hr.2.2] with x hx
  unfold responseRep
  linarith

theorem s16a_Cmat_eq {φ ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∫ x, φ x * responseInverse (periodicRiesz d s) (withDensityReal fun _ : Torus d => (1 : ℝ)) β ψ x
        ∂(withDensityReal fun _ : Torus d => (1 : ℝ)) =
      ∫ x, φ x * responseRep (periodicRiesz d s) (volume : Measure (Torus d)) β ψ x
        ∂(volume : Measure (Torus d)) := by
  rw [s16a_wdr_one]
  refine integral_congr_ae ?_
  filter_upwards [s16a_rep_ae hd hs0 hs hβ hψ] with x hx
  rw [hx]

/-- **Law of the coefficient vector under `G`.** -/
theorem s16a_law_G (hm : (d : ℝ) / 2 < m) (G : Measure (NegSobolev d m)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov m G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (volume : Measure (Torus d)) β ψ x
        ∂(volume : Measure (Torus d)))
    (S : Finset (NonzeroLattice d)) :
    G.map (s16a_Wmap m S) =
      multivariateGaussian 0 (sed_Cmat d s β (fun _ : Torus d => (1 : ℝ)) (s16a_phi S)) := by
  classical
  haveI : IsGaussian G := hG.1.1
  set W := s16a_Wmap m S with hW
  set C := sed_Cmat d s β (fun _ : Torus d => (1 : ℝ)) (s16a_phi S) with hC
  have hpsd : C.PosSemidef :=
    HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hβ (s16a_smoothPos (d := d))
      (fun a => s16a_phi_smooth S a)
  have hWm : Measurable W := W.continuous.measurable
  have hWa : ∀ (u : NegSobolev d m) (a : Fin S.card),
      W u a = NegSobolev.eval u (s16a_phi S a) := fun u a => by
    rw [hW, s16a_Wmap_apply]
    exact (s16a_eval_realMode u _).symm
  have hint : ∀ a b : Fin S.card, Integrable (fun u => W u a * W u b) G := by
    intro a b
    have hLa : ∀ c : Fin S.card, MemLp (fun u => W u c) 2 G := by
      intro c
      have : (fun u => W u c) = ⇑(s16a_cf m (s16a_e S c)) := by
        funext u; rw [hW, s16a_Wmap_apply]; rfl
      rw [this]
      exact IsGaussian.memLp_dual G _ 2 (by simp)
    exact (hLa a).integrable_mul (hLa b)
  have hcov : ∀ a b : Fin S.card, ∫ u, W u a * W u b ∂G = C a b := by
    intro a b
    simp_rw [hWa]
    rw [hG.2 _ _ (s16a_phi_smooth S a) (s16a_phi_smooth S b)]
    exact (s16a_Cmat_eq hd hs0 hs hβ (s16a_phi_smooth S b)).symm
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

end Resp

end HRS.MC.SEdge.S16a

end

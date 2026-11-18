import HRS.MS.SuppU11Aux3
import HRS.Whole.CriticalNoise

/-!
# U11: `HRS.Whole.return_map_bounded` (S8.8, first assertion)

Route.  The coefficients `a_{αℓ} = β⟨P_μφ_α, R_{β,μ}e_ℓ⟩` satisfy the Bessel bound
`∑_ℓ a_{αℓ}² ≤ β ‖P_μφ_α‖²_{L²(μ)}` because the responses `R e_ℓ` are orthonormal for the
nonnegative form `β⟨(I+βK)·,·⟩` (the hypothesis `IsSpectralData.orth`; positivity of the Riesz
operator `K_μ` is the Q34 packet), and `∑_α ‖P_μφ_α‖² ≤ C ∑_α λ_α^{-m} < ∞` for `m > d`.  Cauchy-Schwarz
gives the operator bound `ℓ² → ℓ²` of the matrix `(a_{αℓ})`, and the diagonal semigroup
`e^{-sω_ℓ}` is a continuous contraction for `s ≥ 0`.  Only `IsSpectralData.centered/orth` are used.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open HRS.Whole

namespace HRS.MS.SuppU11

theorem return_map_bounded_proof : type_of% @HRS.Whole.return_map_bounded := by
  intro d hd a β ha hβ ρβ hρ e om hdata t₀ ht₀ C4 hL4 τ hτ b hb m hm T hT
  obtain ⟨B, hB, hB0, hbes⟩ := u11_coef_bessel hd ha hβ hρ hdata.centered hdata.orth hm
  have hom : ∀ l, 0 < om l := hdata.pos
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ b + t - τ / 2 := fun t ht => by
    linarith [ht.1]
  have hrm : ∀ (z : SeqL2) (t : ℝ), 0 ≤ b + t - τ / 2 →
      returnMapW d β ρβ e om m τ b z t =
        u11Theta (u11Coef d β ρβ e m) m (u11Diag om (b + t - τ / 2) z) := by
    intro z t ht
    unfold returnMapW u11Theta
    congr 1
    funext α
    refine tsum_congr fun l => ?_
    have hc := u11_coord_ofSeq (u11_diag_memℓp om hom ht z) l
    unfold u11Diag
    rw [hc]
    unfold u11Coef
    ring
  refine ⟨Real.sqrt (∑' α, B α), fun z => ⟨?_, ?_, ?_⟩⟩
  · intro t ht
    have hs := hpos t ht
    have hcsum : Summable fun l => (Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l) ^ 2 :=
      memℓp_two_iff.1 (u11_diag_memℓp om hom hs z)
    obtain ⟨h1, h2, _⟩ := u11_matrix_bound (u11Coef d β ρβ e m) B hB hB0 hbes
      (fun l => Real.exp (-(b + t - τ / 2) * om l) * SeqL2.coord z l) hcsum
    refine ⟨fun α => (h1 α).congr fun l => by simp only [u11Coef]; ring, ?_⟩
    refine memℓp_two_iff.2 (h2.congr fun α => ?_)
    congr 1
    exact tsum_congr fun l => by simp only [u11Coef]; ring
  · have hcont : ContinuousOn (fun t => u11Diag om (b + t - τ / 2) z) (Set.Icc 0 T) :=
      (u11_diag_continuousOn om hom z).comp (by fun_prop)
        (fun t ht => Set.mem_Ici.2 (hpos t ht))
    have hlip : LipschitzWith ⟨Real.sqrt (∑' α, B α), Real.sqrt_nonneg _⟩
        (u11Theta (u11Coef d β ρβ e m) m) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]
        exact u11_theta_lip _ B hB hB0 hbes m x y
    exact (hlip.continuous.comp_continuousOn hcont).congr
      (fun t ht => hrm z t (hpos t ht))
  · intro t ht
    have hs := hpos t ht
    rw [hrm z t hs]
    calc ‖u11Theta (u11Coef d β ρβ e m) m (u11Diag om (b + t - τ / 2) z)‖
        ≤ Real.sqrt (∑' α, B α) * ‖u11Diag om (b + t - τ / 2) z‖ :=
          u11_theta_norm_le _ B hB hB0 hbes m _
      _ ≤ Real.sqrt (∑' α, B α) * ‖z‖ :=
          mul_le_mul_of_nonneg_left (u11_diag_norm_le om hom hs z) (Real.sqrt_nonneg _)

end HRS.MS.SuppU11

import HRS.MS.Fp81S21WickFam3
import HRS.MS.Fp81S21GaussIncrFull5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- A square-root modulus yields continuity on an interval. -/
private theorem fp81s21_wickFam_continuous_of_square_bound
    {E : Type*} [NormedAddCommGroup E] (H C : ℝ) (hC : 0 ≤ C)
    (F : ℝ → E)
    (hsquare : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ‖F t - F s‖ ^ 2 ≤ C * |t - s|) :
    ContinuousOn F (Icc (0 : ℝ) H) := by
  apply Metric.continuousOn_iff.mpr
  intro s hs ε hε
  have hpos : 0 < C + 1 := by linarith
  refine ⟨ε ^ 2 / (C + 1), div_pos (sq_pos_of_pos hε) hpos, ?_⟩
  intro t ht hdist
  have hdist' : |t - s| < ε ^ 2 / (C + 1) := by
    simpa [Real.dist_eq] using hdist
  have hm : (C + 1) * |t - s| < ε ^ 2 := by
    apply (lt_div_iff₀ hpos).mp at hdist'
    nlinarith
  have hb := hsquare s hs t ht
  have hnon : 0 ≤ |t - s| := abs_nonneg _
  have hnorm : ‖F t - F s‖ < ε := by
    nlinarith [norm_nonneg (F t - F s)]
  simpa [dist_eq_norm] using hnorm

/-- The supplied increment estimate makes each oscillator-coordinate image
continuous in L² for any family of extensions agreeing with its evaluations. -/
theorem fp81s21_wickFam_oscillator_coordinate_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H → ∀ G : GaussianRealization R,
          ∀ (F : ℝ → Lp ℝ 2 G.P) (α : MultiIndex p.d),
            (∀ u : ℝ, 0 ≤ u → (fun ω : G.Ω => (F u) ω) =ᵐ[G.P]
              fun ω => OscDual.eval (G.Z u ω)
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) →
            ContinuousOn (fun u => F u) (Icc (0 : ℝ) H) := by
  obtain ⟨δ0, hδ0, hδhalf, hinc⟩ := fp81s21_gaussian_increment_bound p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R H hH G F α hagree
  obtain ⟨C, hC, _, hCinc⟩ := hinc δ hδ hδle R H hH
  have hsquare : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ‖F t - F s‖ ^ 2 ≤ C α * |t - s| := by
    intro s hs t ht
    have hsq : ‖F t - F s‖ ^ 2 =
        ∫ ω, |OscDual.eval (G.Z t ω) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
          OscDual.eval (G.Z s ω) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)| ^ 2 ∂G.P := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (F t) (F s), hagree t ht.1,
        hagree s hs.1] with ω hsub ht' hs'
      simp only [hsub, Pi.sub_apply, ht', hs', RCLike.inner_apply, conj_trivial, sq_abs]
      ring
    rw [hsq]
    simpa using (hCinc 0 (le_refl 0) G s hs t ht α).2
  exact fp81s21_wickFam_continuous_of_square_bound H (C α) (hC α)
    (fun u => F u) hsquare

#print axioms fp81s21_wickFam_oscillator_coordinate_continuous
end HRS.Fp81.S21
end

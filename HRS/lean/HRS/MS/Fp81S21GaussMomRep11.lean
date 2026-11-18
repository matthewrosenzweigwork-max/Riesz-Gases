import HRS.MS.Fp81S21GaussMomRep10

/-! Coordinate identity for the selected strong-chart Gaussian moment representative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

theorem fp81s21_gaussian_strong_coord (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ G : GaussianRealization R,
          ∃ q : ℝ → G.Ω → r26t6_Coeff,
            fp81s21_MomentRep Es G.P (fun u ω f => OscDual.eval (G.Z u ω) f) q M ∧
            ∀ u, 0 ≤ u → ∀ j, ∀ᵐ ω ∂G.P,
              q u ω j = OscDual.eval (G.Z u ω) (Es.test j) := by
  obtain ⟨δa, hδa, hδah, ha⟩ := fp81s21_gaussian_strong_chart_coordinates p
  obtain ⟨δb, hδb, _, hb⟩ := fp81s21_wickFam_supplied_linear_continuous p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨M, hM, hcoords⟩ := ha δ hδ (hδle.trans (min_le_left _ _)) R Es E
  obtain ⟨K, hK, hfamily⟩ := hb δ hδ (hδle.trans (min_le_right _ _)) R
  have hdReal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 6 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 4) (2 * p.d + 6) p.hs0 p.hs p.ha p.hβ hr hP R.ρβ R.thermal
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨q, hqm, hqs⟩ := hcoords G
  obtain ⟨T, hT, _⟩ := hfamily G
  refine ⟨q, fp81s21_oscillator_MomentRep_of_secondMoment_bound hP Es G.P G.Z q M
    hqm (fun u hu => ⟨(hqs u hu).1, (hqs u hu).2.1⟩) ?_ ?_, ?_⟩
  · intro u hu
    obtain ⟨hL, _, hagree, _⟩ := hT u hu
    refine ⟨K ^ 2 * B, mul_nonneg (sq_nonneg K) hB, ?_⟩
    intro f hf
    have hfw : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f :=
      weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP hf)
    have hf2 := (hOp f hfw).1
    let v := hf2.toLp f
    have hA := hagree f (r2Test_isOscTest _ hf) hf2
    have hmem : MemLp (fun ω => OscDual.eval (G.Z u ω) f) 2 G.P :=
      (Lp.memLp (T u v)).ae_eq hA
    refine ⟨hmem, ?_⟩
    have he : (∫ ω, OscDual.eval (G.Z u ω) f ^ 2 ∂G.P) = ‖T u v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae (hA.symm.mono fun ω hω => ?_)
      simp [hω, sq, v]
    have hv : ‖v‖ ^ 2 = ∫ x, f x ^ 2 ∂HRS.Whole.withDensityReal R.ρβ := by
      symm
      exact HRS.Whole.Q34.integral_sq_eq hf2.coeFn_toLp.symm
    have hn : ‖T u v‖ ≤ K * ‖v‖ :=
      ((T u).le_opNorm v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    calc
      _ = ‖T u v‖ ^ 2 := he
      _ ≤ (K * ‖v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).2 hn
      _ = K ^ 2 * (∫ x, f x ^ 2 ∂HRS.Whole.withDensityReal R.ρβ) := by rw [mul_pow, hv]
      _ ≤ (K ^ 2 * B) * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4) f).toReal ^ 2 := by
        nlinarith [(hOp f hfw).2.1]
  · intro u hu j
    exact ((hqs u hu).2.2).mono fun ω hω => hω j
  · intro u hu j
    exact ((hqs u hu).2.2).mono fun ω hω => hω j

#print axioms fp81s21_gaussian_strong_coord
end HRS.Fp81.S21
end

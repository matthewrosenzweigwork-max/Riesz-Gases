import HRS.Sections.AdjKAAux2

/-!
# ADJKA part 3: the embedding `E_j ↪ E_{j+2}` and the near/far increment bounds for the dual evolution
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.AdjK

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjka_embed_coord {r a : ℝ} (hra : r ≤ a) (x : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.embed a x) k = q48bW k ^ (-a) * NegSobolev.fourierCoeff x k := by
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-a) * NegSobolev.fourierCoeff x k) 2 := by
    rw [Torus.memℓp_two_iff]
    refine (summable_fsq_term hra x).congr fun l => ?_
    show q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff x l ^ 2 =
      (q48bW l ^ (-a) * NegSobolev.fourierCoeff x l) ^ 2
    rw [mul_pow, q48b_rpow_sq (q48bW_pos l), show (2 * -a) = -2 * a by ring]
  exact NegSobolev.coord_ofSeq_of_mem _ hmem k

theorem adjka_norm_embed_sq {r a : ℝ} (hra : r ≤ a) (x : NegSobolev d r) :
    ‖NegSobolev.embed a x‖ ^ 2 = fsq a x := by
  rw [q48b_norm_sq]
  unfold fsq
  refine tsum_congr fun l => ?_
  rw [adjka_embed_coord hra, mul_pow, q48b_rpow_sq (q48bW_pos l)]
  ring_nf

/-- Near range: `‖V^{t,u} z - z‖_{E_{j+2}} ≤ C (t-u) ‖z‖_{E_j}` for `t - u ≤ 1`. -/
theorem adjka_inc_near (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ)
    (hj : (d : ℝ) + 2 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Vev : ℝ → ℝ → NegSobolev d (j : ℝ) →L[ℝ] NegSobolev d (j : ℝ),
      IsDualEvolution htr.dyn ρ (j : ℝ) Vev →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → t - u ≤ 1 → ∀ z : NegSobolev d (j : ℝ),
        ‖NegSobolev.embed ((j : ℝ) + 2) (Vev t u z - z)‖ ≤ C * (t - u) * ‖z‖ := by
  obtain ⟨M, hM0, hM⟩ := adjka_traj_lip hd htr j hj
  refine ⟨M, hM0, fun Vev hV u t hu hut htu z => ?_⟩
  set W : NegSobolev d (j : ℝ) →L[ℝ] NegSobolev d (j : ℝ) := Vev t u - ContinuousLinearMap.id ℝ _ with hW
  have hτ0 : 0 ≤ t - u := by linarith
  have hM' : 0 ≤ M * (t - u) := mul_nonneg hM0 hτ0
  have hdual : ∀ (z : NegSobolev d (j : ℝ)) (φ : Torus d → ℝ), Torus.IsSmooth φ →
      NegSobolev.eval (W z) φ =
        NegSobolev.eval z ((fun φ x => propagator htr.dyn ρ u t φ x - φ x) φ) := by
    intro z φ hφ
    obtain ⟨h1, h2, -⟩ := hM φ hφ u t hu hut htu
    have hφm : MemSobolev (j : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
    have e : W z = Vev t u z - z := by simp [hW]
    rw [e, eval_sub_left _ _ hφm, hV u t hu hut z φ hφ]
    exact (eval_sub_fun z h2 h1 hφm).symm
  have hWB : WB2 ((j : ℝ) + 2) (j : ℝ) (M * (t - u)) (q48bMat (j : ℝ) W) := by
    refine wb2_of_duality (fun φ x => propagator htr.dyn ρ u t φ x - φ x) W hdual _ hM' fun T c => ?_
    obtain ⟨-, h2, h3⟩ := hM (q48bTest T c) (q48bTest_smooth T c) u t hu hut htu
    refine ⟨h2, ?_⟩
    rw [q48bTest_sobolevNorm T c ((j : ℝ) + 2)] at h3
    exact h3
  obtain ⟨-, hf⟩ := fsq_le_of_wb2 W hWB le_rfl z
  have e2 : Vev t u z - z = W z := by simp [hW]
  rw [e2]
  have hle : ‖NegSobolev.embed ((j : ℝ) + 2) (W z)‖ ^ 2 ≤ (M * (t - u) * ‖z‖) ^ 2 := by
    rw [fsq_self z] at hf
    rw [adjka_norm_embed_sq (by linarith)]
    calc fsq ((j : ℝ) + 2) (W z) ≤ (M * (t - u)) ^ 2 * ‖z‖ ^ 2 := hf
      _ = (M * (t - u) * ‖z‖) ^ 2 := by ring
  exact le_of_sq_le_sq hle (by positivity)

end HRS.AdjK

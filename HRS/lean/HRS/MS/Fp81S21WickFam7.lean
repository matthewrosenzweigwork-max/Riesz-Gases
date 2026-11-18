import HRS.MS.Fp81S21WickFam6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- A common bound and a time-continuous linear Gaussian extension for every
supplied realization. The extension agrees with all oscillator tests at every
nonnegative time and carries the centered half-Wick operators. -/
theorem fp81s21_wickFam_supplied_linear_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Kstar : ℝ, 0 ≤ Kstar ∧
          ∀ G : GaussianRealization R,
            ∃ T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P,
              (∀ u : ℝ, 0 ≤ u →
                ∃ hL : ‖T u‖ ≤ Kstar,
                  ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
                    HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
                    (∀ φ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
                      ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
                        T u (hφ.toLp φ) =ᵐ[G.P] fun ω => OscDual.eval (G.Z u ω) φ) ∧
                    (∀ f, ∫ ω, (T u f) ω ∂G.P = 0) ∧
                    ‖fp81s21_wickFam_operator R G (T u) Kstar hL hJoint‖ ≤
                      Kstar ^ 2 / Real.sqrt 2 ∧
                    ∀ k, ∫ ω, fp81s21_wickFam_operator R G (T u) Kstar hL hJoint k ω ∂G.P = 0) ∧
              ∀ f, ContinuousOn (fun u => T u f) (Ici (0 : ℝ)) := by
  classical
  obtain ⟨δa, hδa, hδah, ha⟩ := fp81s21_wickFam_supplied_operator p
  obtain ⟨δb, hδb, hδbh, hb⟩ := fp81s21_wickFam_linear_family_continuous p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R
  obtain ⟨K, hK, hKfam⟩ := ha δ hδ (hδle.trans (min_le_left _ _)) R
  refine ⟨K, hK, ?_⟩
  intro G
  let ex (u : ℝ) := hKfam G (max u 0) (le_max_right u 0)
  let T := fun u : ℝ => Classical.choose (ex u)
  have hT (u : ℝ) := Classical.choose_spec (ex u)
  have hgood : ∀ u : ℝ, 0 ≤ u →
      ∃ hL : ‖T u‖ ≤ K,
        ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
          HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
          (∀ φ : Euc p.d → ℝ, IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
            ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
              T u (hφ.toLp φ) =ᵐ[G.P] fun ω => OscDual.eval (G.Z u ω) φ) ∧
          (∀ f, ∫ ω, (T u f) ω ∂G.P = 0) ∧
          ‖fp81s21_wickFam_operator R G (T u) K hL hJoint‖ ≤ K ^ 2 / Real.sqrt 2 ∧
          ∀ k, ∫ ω, fp81s21_wickFam_operator R G (T u) K hL hJoint k ω ∂G.P = 0 := by
    intro u hu
    obtain ⟨hL, hJoint, hagree, hcenter, hnorm, hwick⟩ := hT u
    refine ⟨hL, hJoint, ?_, hcenter, hnorm, hwick⟩
    intro φ hφ hφLp
    filter_upwards [hagree φ hφ hφLp] with ω hω
    have hz : G.Z (max u 0) ω = G.Z u ω := by rw [max_eq_left hu]
    exact hω.trans (congrArg (fun z => OscDual.eval z φ) hz)
  refine ⟨T, hgood, ?_⟩
  apply hb δ hδ (hδle.trans (min_le_right _ _)) R G T K
  · intro u hu
    exact (hgood u hu).choose
  · intro u hu α hα
    obtain ⟨_, _, hagree, _⟩ := hgood u hu
    exact hagree _ (HRS.MS.GenPath.s56_isOscTest _ α) hα

#print axioms fp81s21_wickFam_supplied_linear_continuous
end HRS.Fp81.S21
end

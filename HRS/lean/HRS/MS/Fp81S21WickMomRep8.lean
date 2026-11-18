import HRS.MS.Fp81S21WickMomRep7
import HRS.MS.Fp81S21GaussMomRep10

/-! Physical half-Wick moment representations in both chart scales. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The coherent positive half-Wick field has strong and embedded moment
representations with the same bound. Each compact-test output is a version
of the supplied operator output; the operator's chosen representatives are
not asserted to agree simultaneously across tests. -/
theorem fp81s21_wick_momentRep_physical (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∃ Kstar B : ℝ, 0 ≤ Kstar ∧ 0 ≤ B ∧ ∀ G : GaussianRealization R,
      ∃ T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P,
      ∃ W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
        (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P,
      ∃ q : ℝ → G.Ω → r26t6_Coeff,
        (∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ Kstar,
          ∃ hJoint : ∀ n (v : Fin n → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
            HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
            W u = fp81s21_wickFam_operator R G (T u) Kstar hL hJoint) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
          (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P]
            fun ω => OscDual.eval (G.Z u ω) φ) ∧
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es q) q
          (Kstar ^ 4 * B / 2) ∧
        fp81s21_MomentRep E G.P (fp81s21_wickChartField Es q)
          (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω))
          (Kstar ^ 4 * B / 2) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
          ∃ hker : MemLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
          (fun ω => fp81s21_wickChartField Es q u ω f) =ᵐ[G.P]
            (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
              commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ)) ∧
        ∀ u : ℝ, 0 ≤ u →
          (AEMeasurable (fun ω => dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (fp81s21_wickChartField Es q u ω)) G.P ∧
            (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_wickChartField Es q u ω) ∂G.P) ≤
                ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2))) ∧
          (AEMeasurable (fun ω => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
            (fp81s21_wickChartField Es q u ω)) G.P ∧
            (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
              (fp81s21_wickChartField Es q u ω) ∂G.P) ≤
                ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2))) := by
  obtain ⟨δ0, hδ0, hhalf, hphysical⟩ := fp81s21_wick_physical_compact_versions p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨K, B, hK, hB, hG⟩ := hphysical δ hδ hδle R Es E
  refine ⟨K, B, hK, hB, ?_⟩
  intro G
  obtain ⟨T, W, q, hW, hT, hs, hag⟩ := hG G
  have hw : fp81s21_MomentRep E G.P (fp81s21_wickChartField Es q)
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω))
      (K ^ 4 * B / 2) := by
    exact fp81s21_MomentRep_embedField_normalized (by omega) (by ring)
      (by nlinarith) (by nlinarith) Es E G.P
      (fp81s21_wickChartField Es q) q (K ^ 4 * B / 2) hs
  refine ⟨T, W, q, hW, hT, hs, hw, hag, ?_⟩
  intro u hu
  exact ⟨fp81s21_MomentRep_firstMoment Es G.P _ q _ hs u hu,
    fp81s21_MomentRep_firstMoment E G.P _ _ _ hw u hu⟩

#print axioms fp81s21_wick_momentRep_physical
end HRS.Fp81.S21
end

import HRS.MS.Fp81S21WickMomRep6

/-! Physical coherent half-Wick field and its compact-test L² versions. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The coherent chart field has a `MomentRep` with the common quadratic
bound and represents the supplied positive half-Wick output for every fixed
compact test. -/
theorem fp81s21_wick_physical_compact_versions (p : Parameters) :
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
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es q) q (Kstar ^ 4 * B / 2) ∧
        ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
          ∃ hker : MemLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
          (fun ω => fp81s21_wickChartField Es q u ω f) =ᵐ[G.P]
            (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
              commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ) := by
  obtain ⟨δ0, hδ0, hδhalf, hcoords⟩ := fp81s21_wick_strong_chart_coordinates p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨K, B, hk, hK, hB, _, _, hfamily⟩ := hcoords δ hδ hδle R Es E
  have hdReal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 6 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨C, hC, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 4) (2 * p.d + 6) p.hs0 p.hs p.ha p.hβ hr hP R.ρβ R.thermal
  refine ⟨K, B, hK, hB, ?_⟩
  intro G
  obtain ⟨T, W, q, hW, hag, hqm, hsec⟩ := hfamily G
  refine ⟨T, W, q, hW, hag, fp81s21_wickChartField_momentRep hP Es G.P q
    (K ^ 4 * B / 2) hqm (fun u hu => ⟨(hsec u hu).1, (hsec u hu).2.1⟩), ?_⟩
  intro u hu f hf
  let hfW : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f :=
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP hf)
  let hker := (hOp f hfW).2.2.1
  refine ⟨hker, ?_⟩
  have hcoord : ∀ j, (fun ω => q u ω j) =ᵐ[G.P]
      (W u ((hk j).toLp (fun xy : Euc p.d × Euc p.d =>
        commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2)) : G.Ω → ℝ) := by
    intro j
    exact ((hsec u hu).2.2).mono fun ω hω => hω j
  simpa only [fp81s21_wickChartField] using
    fp81s21_wick_compact_test_agreement p.hd p.s p.a p.β p.hs0 p.hs p.ha p.hβ
      hr hP R.ρβ R.thermal Es G.P (W u) hk (q u) (hsec u hu).1 hcoord f hf hker

#print axioms fp81s21_wick_physical_compact_versions
end HRS.Fp81.S21
end

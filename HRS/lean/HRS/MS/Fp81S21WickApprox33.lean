import HRS.MS.Fp81S21WickMomRep11

/-! Fixed physical quadratic Gaussian selectors and their uniform spatial tails. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- All clauses of the physical quadratic Gaussian producer for one realization. -/
def fp81s21_QuadraticPhysical31Payload (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (Kstar B : ℝ) (G : GaussianRealization R)
    (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P)
    (q qe : ℝ → G.Ω → r26t6_Coeff) : Prop :=
    (∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ Kstar,
          ∃ hJoint : ∀ n (v : Fin n → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
            HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
            W u = fp81s21_wickFam_operator R G (T u) Kstar hL hJoint) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
          (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P]
            fun ω => OscDual.eval (G.Z u ω) φ) ∧
        (∀ u ω, qe u ω = fp81s21_gaussian_chartEmbed p Es E (q u ω)) ∧
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es q) q
          (Kstar ^ 4 * B / 2) ∧
        fp81s21_MomentRep E G.P (fp81s21_wickChartField Es q) qe
          (Kstar ^ 4 * B / 2) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
          ∃ hker : MemLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
          (fun ω => fp81s21_wickChartField Es q u ω f) =ᵐ[G.P]
            (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
              commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ)) ∧
        (∀ u : ℝ, 0 ≤ u →
          (AEMeasurable (fun ω => dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (fp81s21_wickChartField Es q u ω)) G.P ∧
            (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_wickChartField Es q u ω) ∂G.P) ≤
                ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2))) ∧
          (AEMeasurable (fun ω => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
            (fp81s21_wickChartField Es q u ω)) G.P ∧
            (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
              (fp81s21_wickChartField Es q u ω) ∂G.P) ≤
                ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2)))) ∧
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
          ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            fp81s21_TimeL2Rep G.P qe (Kstar ^ 4 * B / 2) a H U ∧
            fp81s21_TimeRep E G.P (fun u ω => fp81s21_chartAction E (qe u ω))
              qe (Kstar ^ 4 * B / 2) a H U ∧
            ∀ m, fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (U ω))
              (Real.sqrt (H * (Kstar ^ 4 * B / 2)) * ε m) ∧
              ∀ ρ : ℝ, 0 < ρ →
                G.P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
                  ENNReal.ofReal (H * (Kstar ^ 4 * B / 2) * (ε m) ^ 2 / ρ ^ 2)

/-- A realization-indexed selection, fixed before approximation parameters. -/
structure fp81s21_QuadraticPhysical31 (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) where
  Kstar : ℝ
  B : ℝ
  Kstar_nonneg : 0 ≤ Kstar
  B_nonneg : 0 ≤ B
  T : (G : GaussianRealization R) → ℝ →
    Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P
  W : (G : GaussianRealization R) → ℝ →
    Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P
  qs : (G : GaussianRealization R) → ℝ → G.Ω → r26t6_Coeff
  qe : (G : GaussianRealization R) → ℝ → G.Ω → r26t6_Coeff
  payload : ∀ G, fp81s21_QuadraticPhysical31Payload p R Es E ε Kstar B G
    (T G) (W G) (qs G) (qe G)

/-- Select all quadratic witnesses once, with constants uniform in realizations. -/
theorem fp81s21_quadraticPhysical31_exists (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ ε : ℕ → ℝ, (∀ m, 0 ≤ ε m) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      Nonempty (fp81s21_QuadraticPhysical31 p R Es E ε) := by
  obtain ⟨ε, hε, hεlim, δ0, hδ0, hhalf, hphys⟩ :=
    fp81s21_gaussian_wick_weakChart_time_tails p Es E
  refine ⟨ε, hε, hεlim, δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨K, B, hK, hB, hG⟩ := hphys δ hδ hδle R
  choose T W q qe h using hG
  exact ⟨⟨K, B, hK, hB, T, W, q, qe, h⟩⟩

#print axioms fp81s21_QuadraticPhysical31Payload
#print axioms fp81s21_QuadraticPhysical31
#print axioms fp81s21_quadraticPhysical31_exists
end HRS.Fp81.S21
end

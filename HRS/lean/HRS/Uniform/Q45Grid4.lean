import HRS.Uniform.Q45Grid3

/-!
# Q45: the grid comparison
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- **Grid comparison.**  The grid-interpolated, spatially projected Riemann-sum paths of two Hilbert martingales
(the second with deterministic covariance density), started from the same `ℱ₀`-measurable initial state, differ in `C_b²`
by at most `½ C² E∫‖Σ - Cb‖_{𝔖₁}`, `C = detConst T K`. -/
theorem path_grid_comparison {T : ℝ} (hT : 0 < T) {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) {d : ℕ}
    {b : Fin d → E} (hb : Orthonormal ℝ b) {K : ℝ} (S : EvolData H E) (hS : S.MaxHyp T K)
    {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {G : ℝ → Ω → H} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity T Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
    (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) {Φ : PathSp T E → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T E) 2) :
    |∫ ω, Φ (hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        rsum S T g κ M i ω))) ∂P -
      ∫ ω, Φ (hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        rsum S T g κ G i ω))) ∂P| ≤
      (1 / 2) * detConst T K ^ 2 * covDiscrepancy P T Sg Cb := by
  have hNb : 1 ≤ g * κ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hξ : StronglyMeasurable[ℱ 0] (fun ω => initCoord (T := T) (g := g) b S (X₀ ω)) := by
    have hX' : StronglyMeasurable[ℱ 0] X₀ := hX.stronglyMeasurable
    refine stronglyMeasurable_of_coord fun j => ?_
    have hc : Continuous fun x : H => inner ℝ (b (finProdFinEquiv.symm j).2)
        (S.VE (unifPart T g (finProdFinEquiv.symm j).1) 0 (S.j x)) :=
      continuous_const.inner ((S.VE _ 0).continuous.comp S.j.continuous)
    exact hc.comp_stronglyMeasurable hX'
  have key := finite_comparison P hT hNb (gridα S T g κ d b) (pathMap hT hg hb) (norm_pathMap_le hT hg hb)
    (detConst_pos T K).le (fun k _ x => pathMap_block_bound hT hg hκ hb S hS k x) hM hCb hG
    (fun ω => initCoord (T := T) (g := g) b S (X₀ ω)) hξ hΦ
  simp only [pathMap_zeta hT hg hκ hb S] at key
  exact key

end HRS.Uniform.Q45

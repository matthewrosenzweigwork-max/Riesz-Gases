import HRS.Uniform.Q45Core3

/-!
# Q45: the CLT core of Proposition 3.21
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- **The CLT core.**  For two stochastic convolutions `Z = ∫V dM`, `Zb = ∫V dG` of Hilbert martingales (`G` with
deterministic covariance density), added to the same `ℱ₀`-measurable transported initial path, the `C_b²` expectations
differ by at most `½ C² E∫‖Σ - Cb‖_{𝔖₁}`. -/
theorem clt_core {T K : ℝ} (hT : 0 < T) (S : EvolData H E) (hS : S.MaxHyp T K)
    {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {G : ℝ → Ω → H} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity T Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
    (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) (Z Zb : ℝ → Ω → E)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Z t))
    (hZbm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Zb t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
    {Φ : PathSp T E → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T E) 2) :
    |∫ ω, Φ (vpath S hS.1 (X₀ ω) + windowPath 0 T Z ω) ∂P -
      ∫ ω, Φ (vpath S hS.1 (X₀ ω) + windowPath 0 T Zb ω) ∂P| ≤
      (1 / 2) * detConst T K ^ 2 * covDiscrepancy P T Sg Cb := by
  obtain ⟨d, b, hb, hspat⟩ := exists_spatial_approx E
  have hlimZ := core_limit P hT S hS hb (fun y ε hε => hspat T y ε hε) X₀ hX Z hZm hZc hΦ
  have hlimZb := core_limit P hT S hS hb (fun y ε hε => hspat T y ε hε) X₀ hX Zb hZbm hZbc hΦ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε4 : 0 < ε / 4 := by positivity
  have e1 := (Metric.tendsto_atTop.1 hlimZ) (ε / 4) hε4
  have e2 := (Metric.tendsto_atTop.1 hlimZb) (ε / 4) hε4
  obtain ⟨n1, hn1⟩ := e1
  obtain ⟨n2, hn2⟩ := e2
  set n := max n1 n2 with hn
  have h1 := hn1 n (le_max_left _ _)
  have h2 := hn2 n (le_max_right _ _)
  rw [Real.dist_eq] at h1 h2
  set g := n + 1 with hg
  have hg1 : 1 ≤ g := Nat.le_add_left 1 n
  have hη : 0 < ε / 4 / ((g : ℝ) + 1) := by positivity
  obtain ⟨κ1, hκ1⟩ := core_close P hT hg1 (b n) (hb n) S hM X₀ hX Z hZ hZm hΦ hη
  obtain ⟨κ2, hκ2⟩ := core_close P hT hg1 (b n) (hb n) S hG X₀ hX Zb hZb hZbm hΦ hη
  set κ := max (max κ1 κ2) 1 with hκ
  have c1 := hκ1 κ ((le_max_left _ _).trans (le_max_left _ _)) (le_max_right _ _)
  have c2 := hκ2 κ ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)
  have hgrid := path_grid_comparison P hT hg1 (le_max_right _ _ : 1 ≤ κ) (hb n) S hS hM hCb hG X₀ hX hΦ
  have hcalc : (g + 1 : ℝ) * (ε / 4 / ((g : ℝ) + 1)) = ε / 4 := by field_simp
  rw [hcalc] at c1 c2
  set a1 := ∫ ω, Φ (vpath S hS.1 (X₀ ω) + windowPath 0 T Z ω) ∂P
  set a2 := ∫ ω, Φ (vpath S hS.1 (X₀ ω) + windowPath 0 T Zb ω) ∂P
  set b1 := ∫ ω, Φ (hatPath T g (fun i => projB (b n) (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        Z (unifPart T g i) ω))) ∂P
  set b2 := ∫ ω, Φ (hatPath T g (fun i => projB (b n) (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        Zb (unifPart T g i) ω))) ∂P
  set m1 := ∫ ω, Φ (hatPath T g (fun i => projB (b n) (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        rsum S T g κ M i ω))) ∂P
  set m2 := ∫ ω, Φ (hatPath T g (fun i => projB (b n) (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        rsum S T g κ G i ω))) ∂P
  rw [abs_lt] at h1 h2
  rw [abs_le] at c1 c2 hgrid ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, c1.1, c1.2, c2.1, c2.2, hgrid.1, hgrid.2]

end HRS.Uniform.Q45

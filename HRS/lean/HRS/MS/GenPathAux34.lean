import HRS.MS.GenPathAux33

/-!
# S5.6 packet P6f: the remainder `R = Ξ - A(k₀) - 𝒯M` and its bound
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

/-- The fluctuation field `Ξ_t = σ(μ_N^t - ρ_N^t) ∈ B_m`. -/
def s56Xi {b : WholeBounds d} (S : WholeSetup b) {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N)
    (t : ℝ) (ζ : Ω) : OscDual d b.m :=
  S.σ N • OscDual.ofMeasureDiff b.m (HRS.Whole.empirical (X (Real.toNNReal t) ζ))
    (HRS.Whole.withDensityReal (S.ρ N t))

/-- The initial state `k₀ ∈ 𝒦` of the particle path. -/
def s56K0 {b : WholeBounds d} (S : WholeSetup b) {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N)
    (ζ : Ω) : KSpace d b.m b.T :=
  s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical (X 0 ζ)) (HRS.Whole.withDensityReal (S.ρ N 0))

/-- The remainder. -/
def s56R {b : WholeBounds d} (S : WholeSetup b) {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d b.m b.T) (t : ℝ) (ζ : Ω) : OscDual d b.m :=
  s56Xi S X t ζ - (s56K0 S X ζ).evalA t - reconstructPath b.m b.T M ζ t

theorem s56_xi_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) b.T) : Measurable (s56Xi S X t) := by
  have hd : 1 ≤ d := by have := hbv.hd; omega
  have hm : (d : ℝ) < b.m := by
    have := hbv.hm
    have h1 : (0 : ℝ) ≤ b.J := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have := HRS.MS.Thm.cb_withDensityReal_isProb ((S.mf N).density t ht)
  exact (s56_xi_cont_config hd hm (S.σ N) hN (HRS.Whole.withDensityReal (S.ρ N t))).measurable.comp
    (hXm _)

theorem s56_xi_cont (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 0 < N)
    {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (hX : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    ContinuousOn (fun t => s56Xi S X t ζ) (Set.Icc (0 : ℝ) b.T) := by
  have hd : 1 ≤ d := by have := hbv.hd; omega
  have hm : (d : ℝ) < b.m := by
    have := hbv.hm
    have h1 : (0 : ℝ) ≤ b.J := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  obtain ⟨Λ', hcoef⟩ := HRS.MS.Go.s55f_coeffHyp b hbv S N
  exact s56_xi_cont_time hd hm (S.σ N) hN (S.ρ N) hcoef.prob hcoef.cont (fun t => X (Real.toNNReal t) ζ)
    (fun i => (hX i).comp continuous_real_toNNReal)

end HRS.MS.GenPath

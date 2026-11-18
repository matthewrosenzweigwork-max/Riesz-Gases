import HRS.Main.Det16A3
import HRS.Main.Det16B3
import HRS.Main.A34Aux5

/-!
# det16d: the deterministic particle path and the law of `flucPath` (Example A.16 assembly)

`det16b_law_flucPath_dirac` (Det16B3) assumes the particle path is *constant* in time (`X^t = y`), which is
false for the deterministic dynamics (the particles move along the drift flow).  Here the version for a
deterministic *path* `x : ℝ≥0 → Config d N` (taken from `det16_deterministic`) is proved.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

/-- a deterministic continuous particle path for the zero-temperature strong solution (L5 + continuity). -/
theorem det16d_det_path {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (hβ : D.invβ = 0)
    (T : ℝ) (X₀ : Ω → Config d N) (x₀ : Config d N) (hX₀ : ∀ᵐ ω ∂P, X₀ ω = x₀)
    (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (hU : PathwiseUnique P D T X₀ W)
    (X : ℝ≥0 → Ω → Config d N) (hX : IsStrongSolution P D T X₀ W X) :
    ∃ x : ℝ≥0 → Config d N, (∀ i, Continuous fun t => x t i) ∧ x 0 = x₀ ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = x t := by
  have h1 := det16_deterministic P D hβ T X₀ x₀ hX₀ W hU X hX
  obtain ⟨ω₀, h, hc, hi, hx⟩ := (h1.and (hX.cont.and (hX.init.and hX₀))).exists
  exact ⟨fun t => X t ω₀, hc, hi.trans hx, h⟩

/-- continuity of the deterministic fluctuation path along a continuous particle path `x`. -/
theorem det16d_path_cont (S : MainData d) {r : ℕ} {Λ : ℝ} (hr : d + 1 ≤ r)
    (hmf : MeanFieldRegularity S r Λ) (hV : Torus.IsCk 1 S.V) {N : ℕ} (hN : 1 ≤ N)
    {m : ℝ} (hm2 : (d : ℝ) < 2 * m) (σ : ℝ) (x : ℝ≥0 → Config d N)
    (hx : ∀ i, Continuous fun t => x t i) :
    Continuous fun t : Set.Icc (0 : ℝ) S.T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (x (Real.toNNReal t))) (withDensityReal (S.ρ N t)) :=
  det16b_fluc_cont S hr hmf hV hN hm2 (fun (t : ℝ≥0) (_ : Unit) => x t) σ () hx

/-- the fluctuation path of a deterministic particle path, as an element of the path space. -/
def det16d_xPath {N : ℕ} (m T σ : ℝ) (ρ : ℝ → Torus d → ℝ) (x : ℝ≥0 → Config d N)
    (hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (x (Real.toNNReal t))) (withDensityReal (ρ t))) :
    PathSpace d m T :=
  ⟨_, hcont⟩

/-- If the particle path equals the deterministic path `x` a.s. on `[0,T]`, then `law (flucPath)` is the Dirac
mass at the fluctuation path of `x`. -/
theorem det16d_law_flucPath_dirac {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (m T σ : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ : ℝ → Torus d → ℝ) (x : ℝ≥0 → Config d N)
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = x t)
    (hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (x (Real.toNNReal t))) (withDensityReal (ρ t))) :
    law P (flucPath m T σ X ρ) = Measure.dirac (det16d_xPath m T σ ρ x hcont) := by
  have hae : flucPath m T σ X ρ =ᵐ[P] fun _ => det16d_xPath m T σ ρ x hcont := by
    filter_upwards [hX] with ω hω
    have e : (fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))) =
        fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
          (empirical (x (Real.toNNReal t))) (withDensityReal (ρ t)) := by
      funext t
      rw [hω (Real.toNNReal t) (by rw [Real.coe_toNNReal _ t.2.1]; exact t.2.2)]
    have hc : Continuous fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by rw [e]; exact hcont
    have key : flucPath m T σ X ρ ω = (⟨_, hc⟩ : PathSpace d m T) := by
      unfold flucPath
      exact dif_pos hc
    rw [key]
    exact ContinuousMap.ext fun t => congrFun e t
  refine (Measure.map_congr hae).trans ?_
  rw [Measure.map_const, measure_univ, one_smul]

/-- zero temperature: `σ_N = κ_N`, `A_N = 1`, `q_N = 0`. -/
theorem det16d_zero_temp_scales (S : MainData d) (hβ : ∀ N, S.invβ N = 0) (N : ℕ) :
    S.sigma N = S.κ N ∧ S.AN N = 1 ∧ S.qN N = 0 := by
  simp [MainData.sigma, MainData.AN, MainData.qN, sigmaScale, Ascale, qScale, hβ]

/-- zero temperature forces `L.A = 1` (`A_N = 1` and `|A_N - A| ≤ Δ_N → 0`). -/
theorem det16d_LA_eq_one (S : MainData d) (L : LimitCoeffs d) (Rg : PDE.Regime) (ν₀ MB Λ VB : ℝ)
    (hβ : ∀ N, S.invβ N = 0)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d)) : L.A = 1 := by
  have hΔt : Tendsto (fun N => S.coeffDiscrepancy L (gammaIdx d) N) atTop (𝓝 0) := hcoef.tendsto
  have h : Tendsto (fun N : ℕ => |S.AN N - L.A|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hΔt
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (HRS.A34.a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN))
      (HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint)).2.2.2.2
  have h2 : Tendsto (fun N : ℕ => |S.AN N - L.A|) atTop (𝓝 |1 - L.A|) := by
    have : (fun N : ℕ => |S.AN N - L.A|) = fun _ => |1 - L.A| :=
      funext fun N => by rw [(det16d_zero_temp_scales S hβ N).2.1]
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique h2 h
  have h3 : 1 - L.A = 0 := abs_eq_zero.1 this
  linarith

end HRS.Main.Det16

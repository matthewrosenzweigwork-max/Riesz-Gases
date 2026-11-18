import HRS.MS.R2GenInitAux27

/-!
# S10.5 window comparison, packet C2: the initial state `k₀`, the fluctuation field and the remainder of the window

`s105Xi`, `s105K0`, `s105R` (the window remainder `R_b(u) = Ξ(b+u) - A(k₀)(u) - (𝒯M_b)(u)`), measurability of `k₀`, the coordinates of `A(k₀)(u)`
(`s105_k0_eval`) and the a.s. continuity of `u ↦ R_b(u)` on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem

variable {d : ℕ}

/-- The fluctuation field `Ξ_t = σ(μ_N^t - ρ dx) ∈ B_m`. -/
def s105Xi (m σ : ℝ) (ρ : Euc d → ℝ) {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ) (ζ : Ω) :
    OscDual d m :=
  σ • OscDual.ofMeasureDiff m (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) (HRS.Whole.withDensityReal ρ)

/-- The initial state `k₀ ∈ 𝒦_T` of the window. -/
def s105K0 (C : WholeCoeff d) (m T b σ : ℝ) (ρ : Euc d → ℝ) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : KSpace d m T :=
  s105k0 (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) σ
    (HRS.Whole.empirical (X 0 ζ)) (HRS.Whole.withDensityReal ρ)

/-- The window remainder. -/
def s105R (C : WholeCoeff d) (m T b σ : ℝ) (ρ : Euc d → ℝ) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (M : ℝ → Ω → KSpace d m T) (u : ℝ) (ζ : Ω) : OscDual d m :=
  s105Xi m σ ρ X (b + u) ζ - (s105K0 C m T b σ ρ X ζ).evalA u -
    reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ u

theorem s105_K0_meas (C : WholeCoeff d) (m T b σ : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) {N : ℕ} (hN : 1 ≤ N) {τ₀ : ℝ} (hτ : b ≤ τ₀)
    (hb : 0 ≤ b) (hF : S105Feat d m T τ₀ (fun a r x => r2WindowFeature C m T (gradComp a) b r x))
    {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → EucConfig d N) (hX0 : Measurable (X 0)) :
    Measurable (s105K0 C m T b σ ρ X) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) τ₀ := ⟨le_rfl, hb.trans hτ⟩
  obtain ⟨B, hB0, hB⟩ := hF.bound
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => r2WindowFeature C m T (gradComp a) b 0 z :=
    fun a => (hF.cont_x a 0 h0).measurable
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hμint := s56_integrable_norm_withDensity hρ hρ2
  exact (s105_k0_meas (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) σ B hB0 hmeas
    (fun a z => hB a 0 h0 z) (by omega) _ hμint).comp hX0

theorem s105_k0_eval (C : WholeCoeff d) {m T b : ℝ} (hb : 0 ≤ b) {τ₀ : ℝ} (hτ : τ₀ = b + T)
    (hC : OscAdjointInput C m τ₀) (σ : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) {N : ℕ} (hN : 1 ≤ N) (x : EucConfig d N) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d)
    (hF : S105Feat d m T τ₀ (fun a r x => r2WindowFeature C m T (gradComp a) b r x))
    (hK : ∀ (a : Fin d), ∀ z, S105WinK C m T b a 0 z)
    (hcl : IsClassicalAdjointW C (b + u) (oscTestFun m α) (fun r => propagatorW C r (b + u) (oscTestFun m α))) :
    OscDual.coord ((s105k0 (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) σ
        (HRS.Whole.empirical x) (HRS.Whole.withDensityReal ρ)).evalA u) α =
      σ * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW C 0 (b + u) (oscTestFun m α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW C 0 (b + u) (oscTestFun m α))) := by
  have hC' : OscAdjointInput C m (b + T) := hτ ▸ hC
  have hτ0 : 0 ≤ τ₀ := by rw [hτ]; linarith [hu.1, hu.2]
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) τ₀ := ⟨le_rfl, hτ0⟩
  obtain ⟨Bf, hBf0, hBf⟩ := hF.bound
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => r2WindowFeature C m T (gradComp a) b 0 z :=
    fun a => (hF.cont_x a 0 h0).measurable
  have : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure (by omega) x
  have hνint : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical x) :=
    HRS.Whole.Q09A.integrable_empirical (by omega) x _
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hμint := s56_integrable_norm_withDensity hρ hρ2
  obtain ⟨Bb, hBb⟩ := hcl.bdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW C 0 (b + u) (oscTestFun m α)) :=
    (hcl.c2 0 ⟨le_rfl, by linarith [hu.1]⟩).of_le (by norm_num)
  rw [s52_coord_evalA hu.1 hu.2]
  rw [s105_k0_inner (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) σ Bf hBf0 hmeas
    (fun a z => hBf a 0 h0 z) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal ρ) hνint hμint
    (s52y1 m T u α) (propagatorW C 0 (b + u) (oscTestFun m α)) hh Bb
    (fun z => by
      have := hBb 0 ⟨le_rfl, by linarith [hu.1]⟩ z
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun a z => by
      obtain ⟨h1, h2, h3, h4⟩ := hK a z
      rw [s105_pair_y1 C hC' hb le_rfl (by linarith [hu.1, hu.2]) hu a z h1 h3 h4 α]
      simp [show (0 : ℝ) ≤ b + u by linarith [hu.1]])]
  rfl

end HRS.MS.R2GenInit

import HRS.MS.R2GenInitAux28
import HRS.MS.GenPathAux54
import HRS.MS.R2IidPathTie

/-!
# S21T2 packet A2: the initial path `K_b` of the window master equals the S10.5 coupling path

`s21mPath0` (WMASTER, `WsPrepM5`) is `s56EvalPath` of the initial state `k₀ = s105K0` of the window.  The INIT
comparison (`s21i_init_law`, S21T2_I8) is stated for `r2InitCouplingPath` (S10.5 coupling path with `η₀ = 0`).
This file proves that the two coincide pointwise on the sample space whenever `X 0 ζ = X₀ ζ`, under exactly the
hypotheses of `s105_k0_eval` (no new assumption).

* `s21t2_ellVec_eq_of_coord`: an element of `ℓ²` with prescribed coordinates is `ellVec` of them;
* `s21t2_K0_eq`: `s56EvalPath hT (s105K0 C m T b √N ρ₀ X ζ) = r2InitCouplingPath C m T (withDensityReal ρ₀) b X₀ 0 ζ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21T2

open HRS.Whole HRS.MS.GenPath HRS.MS.R2GenInit

variable {d : ℕ}

/-- An `ℓ²` element is `ellVec` of its coordinates (`s11p_ellVec_coord`). -/
theorem s21t2_ellVec_eq_of_coord {m : ℝ} {c : MultiIndex d → ℝ} {x : OscDual d m}
    (h : ∀ α, OscDual.coord x α = c α) : x = ellVec m c := by
  have e : c = fun α => OscDual.coord x α := funext fun α => (h α).symm
  rw [e, HRS.Whole.s11p_ellVec_coord]

/-- The window initial path `k₀` of WMASTER is the S10.5 coupling path with `η₀ = 0`. -/
theorem s21t2_K0_eq (C : WholeCoeff d) {m T b : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) {ρ0 : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ0) (hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ0 x))
    {N : ℕ} (hN : 1 ≤ N) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (X₀ : Ω → EucConfig d N)
    (hC : OscAdjointInput C m (b + T))
    (hF : S105Feat d m T (b + T) (fun a r x => r2WindowFeature C m T (gradComp a) b r x))
    (hK : ∀ (a : Fin d), ∀ z, S105WinK C m T b a 0 z)
    (hcl : ∀ (α : MultiIndex d) (u : ℝ), u ∈ Set.Icc (0 : ℝ) T →
      IsClassicalAdjointW C (b + u) (oscTestFun m α) (fun r => propagatorW C r (b + u) (oscTestFun m α)))
    (ζ : Ω) (hX : X 0 ζ = X₀ ζ) :
    s56EvalPath hT (s105K0 C m T b (Real.sqrt N) ρ0 X ζ) =
      r2InitCouplingPath C m T (HRS.Whole.withDensityReal ρ0) b X₀ (fun _ _ => 0) ζ := by
  have hX' : s105K0 C m T b (Real.sqrt N) ρ0 X ζ =
      s105k0 (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) (Real.sqrt N)
        (HRS.Whole.empirical (X₀ ζ)) (HRS.Whole.withDensityReal ρ0) := by
    unfold s105K0
    rw [hX]
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) T, (s105K0 C m T b (Real.sqrt N) ρ0 X ζ).evalA u =
      r2InitCouplingFun C m (HRS.Whole.withDensityReal ρ0) b X₀ (fun _ _ => 0) ζ u := by
    intro u hu
    unfold r2InitCouplingFun
    apply s21t2_ellVec_eq_of_coord
    intro α
    rw [hX']
    have h := s105_k0_eval C hb rfl hC (Real.sqrt N) hρ hρ2 hN (X₀ ζ) hu α hF hK (hcl α u hu)
    rw [h]
    simp
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      r2InitCouplingFun C m (HRS.Whole.withDensityReal ρ0) b X₀ (fun _ _ => 0) ζ (0 + (t : ℝ)) := by
    have e : (fun t : Set.Icc (0 : ℝ) T =>
        r2InitCouplingFun C m (HRS.Whole.withDensityReal ρ0) b X₀ (fun _ _ => 0) ζ (0 + (t : ℝ))) =
        fun t : Set.Icc (0 : ℝ) T => (s105K0 C m T b (Real.sqrt N) ρ0 X ζ).evalA (t : ℝ) := by
      funext t
      rw [zero_add, hpt t t.2]
    rw [e]
    exact continuousOn_iff_continuous_restrict.1 (HRS.MS.U9.u9_continuousOn_evalA hT _)
  unfold s56EvalPath r2InitCouplingPath windowPathOf
  simp only [hcont, ↓reduceDIte]
  refine ContinuousMap.ext fun t => ?_
  show (s105K0 C m T b (Real.sqrt N) ρ0 X ζ).evalA (t : ℝ) =
    r2InitCouplingFun C m (HRS.Whole.withDensityReal ρ0) b X₀ (fun _ _ => 0) ζ (0 + (t : ℝ))
  rw [zero_add, hpt t t.2]

end HRS.MS.S21T2

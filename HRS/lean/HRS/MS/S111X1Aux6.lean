import HRS.MS.S111X1Aux5

/-!
# S11.1 X1, part 6: the analytic input `X1Input` and the linearity of the covariance functional
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- The stationary coefficient of the quadratic model. -/
def x1C (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) : WholeCoeff d :=
  (HRS.Whole.quadraticGradientDyn d s a β).coeff (fun _ => ρ)

/-- The analytic inputs of the `L²` covariance core (everything except the abstract assembly).
* `exist`: classical adjoint solutions exist for every oscillator test function and every horizon;
* `uniq`: classical adjoint solutions are unique, and `comb`: linear combinations of classical solutions are classical;
* `resp`: the response operator `R_{γ,μ}` is `L²(μ)`-bounded by `‖P_μ ·‖`;
* `energy`: the fluctuation-dissipation (energy) estimates for classical solutions. -/
structure X1Input (d : ℕ) (s a β γ : ℝ) (ρ : Euc d → ℝ) : Prop where
  meas : Measurable ρ
  pos : ∀ x, 0 < ρ x
  int : Integrable ρ
  bdd : ∃ M : ℝ, ∀ x, ρ x ≤ M
  exist : ∀ t : ℝ, 0 ≤ t → ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ →
    ∃ f, IsClassicalAdjointW (x1C d s a β ρ) t ψ f
  uniq : ∀ t : ℝ, 0 ≤ t → ∀ (φ : Euc d → ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
    IsClassicalAdjointW (x1C d s a β ρ) t φ f₁ → IsClassicalAdjointW (x1C d s a β ρ) t φ f₂ →
    ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r
  comb : ∀ t : ℝ, 0 ≤ t → ∀ (φ ψ : Euc d → ℝ) (c : ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
    IsClassicalAdjointW (x1C d s a β ρ) t φ f₁ → IsClassicalAdjointW (x1C d s a β ρ) t ψ f₂ →
    IsClassicalAdjointW (x1C d s a β ρ) t (fun x => φ x + c * ψ x) (fun r x => f₁ r x + c * f₂ r x)
  energy : ∀ t : ℝ, 0 ≤ t → ∃ c : ℝ, 0 ≤ c ∧ ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ →
    ∀ f : ℝ → Euc d → ℝ, IsClassicalAdjointW (x1C d s a β ρ) t ψ f →
      (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (f 0) x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        c * ∫ x, ψ x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ∧
      (∫ s in Set.Icc (0 : ℝ) t, ∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * ρ x ≤
        c * ∫ x, ψ x ^ 2 ∂(HRS.Whole.withDensityReal ρ))

variable {s a β γ : ℝ} {ρ : Euc d → ℝ}

theorem X1Input.nonneg (h : X1Input d s a β γ ρ) : ∀ x, 0 ≤ ρ x := fun x => (h.pos x).le

theorem X1Input.finite (h : X1Input d s a β γ ρ) : IsFiniteMeasure (HRS.Whole.withDensityReal ρ) := by
  unfold HRS.Whole.withDensityReal
  exact isFiniteMeasure_withDensity_ofReal h.int.2

/-- a classical solution is square-integrable at every time -/
theorem x1_classical_memLp {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (μ : Measure (Euc d))
    [IsFiniteMeasure μ] : MemLp (f r) 2 μ := by
  obtain ⟨B, hB⟩ := hf.bdd 0 (by norm_num)
  refine MemLp.of_bound (hf.c2 r hr).continuous.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => ?_)
  have := hB r hr x
  rwa [norm_iteratedFDeriv_zero] at this

/-- linearity of the propagator on oscillator tests -/
theorem X1Input.prop_lin (h : X1Input d s a β γ ρ) {r : ℝ} (hr : 0 ≤ r) {ψ₁ ψ₂ : Euc d → ℝ}
    (h₁ : IsOscTest (wholeSpaceIndex d : ℝ) ψ₁) (h₂ : IsOscTest (wholeSpaceIndex d : ℝ) ψ₂) (c : ℝ) :
    ∀ u ∈ Set.Icc (0 : ℝ) r, propagatorW (x1C d s a β ρ) u r (fun x => ψ₁ x + c * ψ₂ x) =
      fun x => propagatorW (x1C d s a β ρ) u r ψ₁ x + c * propagatorW (x1C d s a β ρ) u r ψ₂ x := by
  intro u hu
  have c₁ := x1_prop_classical (h.exist r hr ψ₁ h₁)
  have c₂ := x1_prop_classical (h.exist r hr ψ₂ h₂)
  have hc := h.comb r hr _ _ c _ _ c₁ c₂
  have c₃ := x1_prop_classical (⟨_, hc⟩ : ∃ f, IsClassicalAdjointW (x1C d s a β ρ) r
    (fun x => ψ₁ x + c * ψ₂ x) f)
  exact h.uniq r hr _ _ _ c₃ hc u hu

end HRS.MS.S111X1

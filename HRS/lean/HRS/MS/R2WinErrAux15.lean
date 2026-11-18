import HRS.MS.R2WinErrAux14

/-!
# S10.4 packet E5a: input classes and small conversions for the assembly

* `S104ClassInput` : the facts about the class of mean-field trajectories (`IsR2WindowTrajectory`) used by `r2_window_errors`
  (uniform density, moment and log-moment bounds, the completion constant, joint measurability of the clamped density `(r,y) ↦ ρ(clamp r) y`);
  they come from `IsResultingSolution`/the thermal equilibrium/S6.6, not from the particle process.
* `S104Phi` : the oscillator test functions have `∂_aφ_α ∈ C_b^k` with norm `≤ C_φ b_α` (`s103_phi_cb` of `R2WinOrbAux1`).
* conversions: collision-free configurations are injective; `secondMomentOf (empirical Z) = movSecondMoment Z`; monotonicity of `oN` and of
  `R2OrbitGrad` in the amplitude.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- `b_α = λ_α^{(J-m)/2}` with `J = 18d+180`, `m = 24d+240`. -/
def s104_b (d : ℕ) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)

lemma s104_b_nonneg (α : MultiIndex d) : 0 ≤ s104_b d α :=
  Real.rpow_nonneg (oscEigenvalue_pos α).le _

/-- Facts about the class of mean-field trajectories (see the module docstring). -/
def S104ClassInput (d : ℕ) (s a β εstar c₁ C₁ : ℝ) : Prop :=
  ∃ M L Mom C₀c : ℝ, 0 ≤ C₀c ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
    IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ →
    (∀ t : ℝ, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) ∧ (∀ x, ρ t x ≤ M) ∧
      Integrable (fun x => ‖x‖ ^ 2 * ρ t x) ∧ secondMomentOf (HRS.Whole.withDensityReal (ρ t)) ≤ Mom ∧
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal (ρ t)) L)) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀c N) ∧
    (∀ T' : ℝ, 0 ≤ T' → Measurable fun p : ℝ × Euc d => ρ (max 0 (min p.1 T')) p.2)

/-- The oscillator test functions: `∂_aφ_α ∈ C_b^{4d+42}` with norm `≤ C_φ b_α`. -/
def S104Phi (d : ℕ) : Prop :=
  ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∀ (α : MultiIndex d) (a : Fin d),
    ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞)
      (fun x => gradComp a (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) ∧
    ∀ j ≤ 4 * d + 42, ∀ x, ‖iteratedFDeriv ℝ j
      (fun x => gradComp a (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) x‖ ≤ Cphi * s104_b d α

lemma s104_injective_of_not_collision {N : ℕ} {X : EucConfig d N} (h : X ∉ eucCollisionSet d N) :
    Function.Injective X := fun i j hij => by
  by_contra hne
  exact h ⟨i, j, hne, hij⟩

lemma s104_secondMoment_eq {N : ℕ} (hN : 0 < N) (Z : EucConfig d N) :
    secondMomentOf (HRS.Whole.empirical Z) = movSecondMoment Z := by
  unfold secondMomentOf movSecondMoment
  rw [HRS.Whole.pair_empirical hN]
  rw [one_div]

lemma s104_oN_mono (d : ℕ) (s : ℝ) {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) (N : ℕ) :
    HRS.oN d s C₁ N ≤ HRS.oN d s C₂ N := by
  unfold HRS.oN
  have : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith

lemma s104_R2OrbitGrad_mono (C : WholeCoeff d) {k : ℕ} {t : ℝ} {ψ : Euc d → ℝ} {A A' c : ℝ}
    (h : R2OrbitGrad C k t ψ A c) (hA : A ≤ A') : R2OrbitGrad C k t ψ A' c := by
  intro f hf r hr
  obtain ⟨h1, h2⟩ := h f hf r hr
  refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have : 0 ≤ Real.exp (-c * (t - r)) := (Real.exp_pos _).le
  nlinarith

end HRS.MS.R2WinErr

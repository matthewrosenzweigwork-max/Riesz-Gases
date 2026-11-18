import HRS.MS.Fp81S21WindowFeature3
import HRS.MS.Fp81S21MovingStd2

/-!
# HRS S2.1 packet 15c: the physical terminal derivative identity

The S101 time derivative is a derivative within the finite physical interval.
For a common-radius trajectory, the orbit difference-quotient data identify it
with propagation of the generator terminal input whenever the interval is
nondegenerate.  The final-time singleton is treated separately by consumers.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.R26T3 HRS.MS.R2WinErr
open HRS.MS.R2WinOrbNL

/-- Common-radius trajectories have the correct physical terminal derivative
on every nondegenerate finite time interval. -/
theorem fp81s21_moving_terminal_derivative_within
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, v < H → ∀ x : Euc p.d,
        HasDerivWithinAt
          (fun z => propagatorW (r26t3_coeff R) v z
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x)
          (propagatorW (r26t3_coeff R) v t
            (generatorW (r26t3_coeff R) t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
          (Icc v H) t := by
  intro α v hv t ht hvH x
  let C : WholeCoeff p.d := r26t3_coeff R
  let φ : MultiIndex p.d → Euc p.d → ℝ :=
    fun β => oscTestFun (wholeSpaceIndex p.d : ℝ) β
  have horb : S104nOrbit C (φ α) H :=
    s104b_orbit_of_termRegGen hterm R.admissible R.resulting α H hH.le
  let Fa : ℝ → Euc p.d → ℝ := fun τ => propagatorW C v (v + τ) (φ α)
  let Fb : ℝ → Euc p.d → ℝ := fun τ =>
    propagatorW C v (v + τ) (generatorW C (v + τ) (φ α))
  have hτ : t - v ∈ Icc (0 : ℝ) (H - v) := by
    constructor <;> linarith [ht.1, ht.2]
  have hcdA : ∀ τ ∈ Icc (0 : ℝ) (H - v),
      ContDiff ℝ (0 : WithTop ℕ∞) (Fa τ) := by
    intro τ hτ'
    have hz : v + τ ∈ Icc (0 : ℝ) H := by
      constructor <;> linarith [hv.1, hτ'.1, hτ'.2]
    obtain ⟨f, hf⟩ := horb.ex0 (v + τ) hz
    have hc := (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩).c2 v
      ⟨hv.1, by linarith [hτ'.1]⟩
    exact hc.of_le (by norm_num)
  have hcdB : ∀ τ ∈ Icc (0 : ℝ) (H - v),
      ContDiff ℝ (0 : WithTop ℕ∞) (Fb τ) := by
    intro τ hτ'
    have hz : v + τ ∈ Icc (0 : ℝ) H := by
      constructor <;> linarith [hv.1, hτ'.1, hτ'.2]
    obtain ⟨f, hf⟩ := horb.ex1 (v + τ) hz
    have hc := (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩).c2 v
      ⟨hv.1, by linarith [hτ'.1]⟩
    exact hc.of_le (by norm_num)
  have hdiff : ∀ τ ∈ Icc (0 : ℝ) (H - v), ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, h ≠ 0 → |h| < η →
        τ + h ∈ Icc (0 : ℝ) (H - v) → ∀ y : Euc p.d,
          ‖iteratedFDeriv ℝ 0
            (fun z => h⁻¹ * (Fa (τ + h) z - Fa τ z) - Fb τ z) y‖ ≤ ε := by
    intro τ hτ' ε hε
    obtain ⟨η, hη, hq⟩ := horb.diff01 v hv τ hτ' ε hε
    refine ⟨η, hη, fun h hne hlt hτh y => ?_⟩
    exact hq h hne hlt hτh 0 (by norm_num) y
  have hderτ := HRS.MS.R2WinOrb.s103_hasDeriv_val hcdA hcdB hdiff x
    (t - v) hτ
  have hshift : HasDerivWithinAt (fun z : ℝ => z - v) 1 (Icc v H) t :=
    ((hasDerivAt_id t).sub_const v).hasDerivWithinAt
  have hmaps : MapsTo (fun z : ℝ => z - v) (Icc v H)
      (Icc (0 : ℝ) (H - v)) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  have hcomp := hderτ.comp t hshift hmaps
  have hcomp' : HasDerivWithinAt (fun z => Fa (z - v) x)
      (Fb (t - v) x) (Icc v H) t := by
    simpa [Function.comp_def] using hcomp
  have heq : ∀ z ∈ Icc v H,
      Fa (z - v) x = propagatorW C v z (φ α) x := by
    intro z hz
    dsimp [Fa]
    congr 1
    ring
  have hactual := hcomp'.congr_of_mem (fun z hz => (heq z hz).symm) ht
  have htarget : Fb (t - v) x =
      propagatorW C v t (generatorW C t (φ α)) x := by
    dsimp [Fb]
    congr 2 <;> ring
  exact hactual.congr_deriv htarget

#print axioms fp81s21_moving_terminal_derivative_within

end HRS.Fp81.S21

end

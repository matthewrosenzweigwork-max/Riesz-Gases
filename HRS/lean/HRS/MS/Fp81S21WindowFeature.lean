import HRS.MS.Fp81S21WindowOrbitDecay2
import HRS.MS.CovMeasAux30

/-!
# HRS S2.1(iii), SOL40 packet 15c: the observation-window covariance feature

The existing full-history feature in `HRS.MS.CovMeas` is
`s101Gamma C m T v x : KSpace d m T`, namely
`KSpace.mk (s101Bv C m v x) (s101Av C m T v x) (s101Bv C m v x)`.
Its `A₀` and `B` coordinates are both
`(propagatorW C v v (oscTestFun m α) x)_α`; its `A'` coordinate is the
`L²([0,T]; ℓ²)` class of
`s101Fl C m T v s x`, whose `α` coordinate is
`if v < s ∧ s ≤ T then s101Dt C m T v s α x else 0`.
Here `s101Dt` is the within-time derivative of `U^{v,s} φ_α`.  The existing
reconstruction is `s56_reconCLM` (equivalently `reconstructPath`): from a
`KSpace`-valued path `y`, its coordinate at time `t` is the `A₀` coordinate
at the terminal time plus the integral of `A'` through `t`, minus the terminal
`B` coordinate, plus the current `B` coordinate.  In `r2_covariance_measure_proof`,
`s101_D_data` uses this feature in `s101Fm Γ Bil = Σ_k Bil(∂_k Γ,∂_k Γ)`;
`s101_Fm_Rk_eq_inner` identifies its rank-one test with the spatial gradient
pairing required by the covariance test.

For a window `[a,a+H]`, the feature below is the SOL40 feature in
`KSpace d m H`.  Its middle coordinate uses the shifted physical time
`a+t` and the physical-history derivative on `[v,a+H]`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

/-- The initial `ℓ²` coordinate of the observation-window feature. -/
def fp81s21_window_feature_A0 (C : WholeCoeff d) (m a v : ℝ) (x : Euc d) : OscDual d m :=
  ellVec m (fun α => if v ≤ a then propagatorW C v a (oscTestFun m α) x
    else oscTestFun m α x)

/-- The shifted time-derivative coordinate of the observation-window feature. -/
def fp81s21_window_feature_Aprime (C : WholeCoeff d) (m H a v t : ℝ) (x : Euc d) : OscDual d m :=
  ellVec m (fun α => if v < a + t then s101Dt C m (a + H) v (a + t) α x else 0)

/-- The terminal `ℓ²` coordinate, supported on noise times after the window start. -/
def fp81s21_window_feature_B (m : ℝ) (a v : ℝ) (x : Euc d) : OscDual d m :=
  ellVec m (fun α => if a < v then oscTestFun m α x else 0)

/-- The observation-window feature `Γ_{a,v}(x) ∈ KSpace d m H`. -/
def fp81s21_window_feature (C : WholeCoeff d) (m H a v : ℝ) (x : Euc d) : KSpace d m H :=
  open Classical in
  KSpace.mk (fp81s21_window_feature_A0 C m a v x)
    (if h : MemLp (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) 2
        (volume.restrict (Set.Icc (0 : ℝ) H)) then h.toLp _ else 0)
    (fp81s21_window_feature_B m a v x)

theorem fp81s21_window_feature_A0_coord
    {C : WholeCoeff d} {m a v : ℝ} {x : Euc d}
    (h : Memℓp (fun α : MultiIndex d => if v ≤ a then
      propagatorW C v a (oscTestFun m α) x else oscTestFun m α x) 2)
    (α : MultiIndex d) :
    inner ℝ (fp81s21_window_feature_A0 C m a v x) (s101e m α) =
      if v ≤ a then propagatorW C v a (oscTestFun m α) x else oscTestFun m α x := by
  exact s101_inner_ellVec_e h α

theorem fp81s21_window_feature_Aprime_coord
    {C : WholeCoeff d} {m H a v t : ℝ} {x : Euc d}
    (h : Memℓp (fun α : MultiIndex d => if v < a + t then
      s101Dt C m (a + H) v (a + t) α x else 0) 2)
    (α : MultiIndex d) :
    inner ℝ (fp81s21_window_feature_Aprime C m H a v t x) (s101e m α) =
      if v < a + t then s101Dt C m (a + H) v (a + t) α x else 0 := by
  exact s101_inner_ellVec_e h α

theorem fp81s21_window_feature_B_coord
    {m a v : ℝ} {x : Euc d}
    (h : Memℓp (fun α : MultiIndex d => if a < v then oscTestFun m α x else 0) 2)
    (α : MultiIndex d) :
    inner ℝ (fp81s21_window_feature_B m a v x) (s101e m α) =
      if a < v then oscTestFun m α x else 0 := by
  exact s101_inner_ellVec_e h α

#print axioms fp81s21_window_feature_A0_coord
#print axioms fp81s21_window_feature_Aprime_coord
#print axioms fp81s21_window_feature_B_coord

end HRS.Fp81.S21

end

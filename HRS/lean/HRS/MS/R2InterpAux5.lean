import HRS.MS.R2InterpAux4
import HRS.MC.S7PIS3Law
import HRS.MS.GenPathAux47

/-!
# S10.2 (worker S102), part 5: the finite-dimensional observations of the Gaussian future `Γ_u`

For nodes `τ_i ∈ [0,T]` and Hermite indices `α_i` put `obs(w) = (w(τ_i)(φ_{α_i}))_i ∈ ℝ^q` (a continuous linear map on `OscPath`) and
`obsCov u = (2ν ∫_u^{τ_i∧τ_j} ∫ ∇U^{v,τ_i}φ_{α_i} · ∇U^{v,τ_j}φ_{α_j} ρ_v dx dv)_{ij}`.  If `γ` satisfies `IsR2FutureGaussian C m T u γ`, then
`γ.map obs = multivariateGaussian 0 (obsCov u)` (whole-space port of `s7_PIS_obs_law`; the generic step is `S7PIS3_map_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

theorem s102_ellp_eval' (τ : Set.Icc (0 : ℝ) T) (α : MultiIndex d) (w : OscPath d m T) :
    OscDual.coord (OscPath.at' w τ) α = OscDual.eval (r2PathAt w (τ : ℝ)) (oscTestFun m α) := by
  rw [r2PathAt, dif_pos τ.2, OscDual.eval_oscTestFun]

instance s102_oscPath_complete : CompleteSpace (OscPath d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, OscDual d m))

/-- The observation map `w ↦ (w(τ_i)(φ_{α_i}))_i`. -/
def s102_obs {q : ℕ} (τ : Fin q → Set.Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) :
    OscPath d m T →L[ℝ] EuclideanSpace ℝ (Fin q) :=
  (EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => s102_ell (τ i) (α i))

theorem s102_obs_apply {q : ℕ} (τ : Fin q → Set.Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (w : OscPath d m T) (i : Fin q) :
    s102_obs τ α w i = OscDual.coord (OscPath.at' w (τ i)) (α i) := rfl

/-- The covariance matrix of the observations of `Γ_u`. -/
def s102_obsCov (C : WholeCoeff d) (m : ℝ) {q : ℕ} (τ : Fin q → Set.Icc (0 : ℝ) T)
    (α : Fin q → MultiIndex d) (u : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun i j => 2 * C.ν * ∫ v in Set.Icc u (min (τ i : ℝ) (τ j : ℝ)), ∫ x,
    inner ℝ (gradient (propagatorW C v (τ i) (oscTestFun m (α i))) x)
      (gradient (propagatorW C v (τ j) (oscTestFun m (α j))) x) * C.ρ v x

theorem s102_obs_law (C : WholeCoeff d) {u : ℝ} {γ : Measure (OscPath d m T)}
    (hγ : IsR2FutureGaussian C m T u γ) {q : ℕ} (τ : Fin q → Set.Icc (0 : ℝ) T)
    (α : Fin q → MultiIndex d) :
    (s102_obsCov C m τ α u).PosSemidef ∧
      γ.map (s102_obs τ α) = multivariateGaussian 0 (s102_obsCov C m τ α u) := by
  obtain ⟨⟨hG, hc⟩, hcov⟩ := hγ
  haveI : IsGaussian γ := hG
  refine HRS.MC.Sec7.S7PIS3.S7PIS3_map_eq hc (s102_obs τ α) _ fun i j => ?_
  have := hcov (τ i) (τ j) (oscTestFun m (α i)) (oscTestFun m (α j)) (HRS.MS.GenPath.s56_isOscTest m (α i))
    (HRS.MS.GenPath.s56_isOscTest m (α j)) (τ i).2 (τ j).2
  simp only [s102_obs_apply]
  have e : ∀ (k : Fin q) (w : OscPath d m T), OscDual.coord (OscPath.at' w (τ k)) (α k) =
      OscDual.eval (r2PathAt w (τ k)) (oscTestFun m (α k)) := fun k w =>
    (s102_ellp_eval' (τ k) (α k) w)
  simp only [e]
  simpa [s102_obsCov] using this.symm

end HRS.MS.R2Interp

end

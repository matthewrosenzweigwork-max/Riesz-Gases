import HRS.MS.WsStatAux33

/-!
# S21 packet K-3: the initial-path input `S21Init` and its relation to the centred initial path of the master

`S21Init d s a beta T hT` is the (clean `Prop`) input of packets G, H: for the stationary Gibbs law `P_{N,beta}` the centred initial orbit
path `s21IP = A(k_0)` (`k_0 = s56k0 C m T sqrt(N) (empirical x) nubar`, the `zeta`-normalised initial state, `C` the stationary coefficient)
is within `C sqrt(delta_N)` in the smooth metric and `C delta_N^{3/20}` in `W_1` of a Gaussian path measure `gamma0` on `C([0,T];B_m)` whose
finite-dimensional coordinate laws are `multivariateGaussian 0 (C_{beta,rho}(U^{0,t_a} phi_a, U^{0,t_c} phi_c))` (static susceptibility
covariance transported by the adjoint orbit; positive semidefinite).

`s21_path0_eq`: for `sigma = sqrt N sqrt beta`, `s21Path0 = sqrt beta * s21IP` (the master works with `Xi = sqrt beta zeta`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc)

variable {d : ℕ}

/-- The `zeta`-normalised centred initial orbit path `x ↦ A(k_0)` of a configuration. -/
def s21IP (m T : ℝ) (hT : 0 ≤ T) (C : WholeCoeff d) (N : ℕ) (νb : Measure (Euc d)) (x : EucConfig d N) :
    OscPath d m T :=
  s56EvalPath hT (s56k0 C m T (Real.sqrt N) (HRS.Whole.empirical x) νb)

/-- The initial-path input of S2.1 (i) (packets G, H), at a general index `m` (to be instantiated with `m = wholeSpaceIndex d`;
the general form avoids rewriting inside types in the assembly). -/
def S21InitAt (d : ℕ) (s a β T m : ℝ) (hT : 0 ≤ T) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ N : ℕ, 2 ≤ N →
    ∃ γ0 : Measure (OscPath d m T), IsProbabilityMeasure γ0 ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
        (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
            (oscTestFun m (αs i)))
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
            (oscTestFun m (αs j)))).PosSemidef ∧
        γ0.map (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
            OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
            (HRS.Whole.withDensityReal ρ) β
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
              (oscTestFun m (αs i)))
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
              (oscTestFun m (αs j))))) ∧
      smoothDist 2 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (s21IP m T hT ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) N
            (HRS.Whole.meanEmpirical (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) γ0 ≤
        C * Real.sqrt (HRS.deltaN d s N) ∧
      wassersteinE 1 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (s21IP m T hT ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) N
            (HRS.Whole.meanEmpirical (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) γ0 ≤
        ENNReal.ofReal (C * HRS.deltaN d s N ^ ((3 : ℝ) / 20))

/-- The initial-path input of S2.1 (i) with `m = wholeSpaceIndex d`. -/
def S21Init (d : ℕ) (s a β T : ℝ) (hT : 0 ≤ T) : Prop :=
  S21InitAt d s a β T ((wholeSpaceIndex d : ℕ) : ℝ) hT

theorem s21_path0_eq {b : WholeBounds d} (hT : 0 ≤ b.T) (S : WholeSetup b) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) {β : ℝ}
    (hσ : S.σ N = Real.sqrt (N : ℝ) * Real.sqrt β) (ζ : Ω) :
    s21Path0 hT S X νb ζ = Real.sqrt β • s21IP b.m b.T hT (S.coeff N) N νb (X 0 ζ) := by
  unfold s21Path0 s21K0c s21IP s56k0
  rw [hσ, mul_comm, ← smul_smul, map_smul]

theorem s21_smul_clm_norm (c : ℝ) (hc : 0 ≤ c) {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] :
    ‖(c • (ContinuousLinearMap.id ℝ B) : B →L[ℝ] B)‖ ≤ c := by
  refine (norm_smul_le (c : ℝ) (ContinuousLinearMap.id ℝ B)).trans ?_
  rw [Real.norm_of_nonneg hc]
  calc c * ‖(ContinuousLinearMap.id ℝ B)‖ ≤ c * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hc
    _ = c := mul_one c

end HRS.MS.S21

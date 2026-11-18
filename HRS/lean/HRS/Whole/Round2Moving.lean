import HRS.Whole.Window
import HRS.Whole.Q33Aux1
import HRS.Whole.Q33bAux2

/-!
# Whole-space supplement, Section 11.3-11.6: power integrability for moving Gibbs preparations, moment transfer on
moving and shifted windows, the exponential rows of the centered logarithm, independent logarithmic preparation --
statements S11.3-S11.6

Source: HRS whole-space supplement (S), lines 8861-9146 (S11.3, S11.4), 9532-9623 (S11.5, S11.6, rows `S:O:lem:log-row`, `S:O:cor:log-path`).

Standing assumptions (S L8880-8892, L9153-9171): `d ≥ 2`, `0 ≤ σ < d/2`, the physical inverse temperature `β > 0` and the quadratic
confinement fixed (here `q` is the confinement constant, as in `Moving.lean`; the supplement's `a`), `μ^t = ρ^t dx` one of the small nonlinear
trajectories of Theorem S6.3, `Q_N^t = Q_{N,β}^g(μ^t)`, `f_N^t` the canonical particle law with initial preparation `Q_{N,γ}^g(μ^0)`,
`γ > 0` for `σ > 0` and `γ ≥ 0` for `σ = 0` (`γ = 0` is the iid preparation `(μ^0)^{⊗N}`).

## Representation decisions

* The trajectories and particle realizations are those of `mov_entropy` (`MovNonlinearConclusion`, `MovInitialClass`, `MovInSmallClass`,
  `MovParticleSetup`, `MovPrepared`); the indices `(j,m)` of S6.3 are existentially quantified (AMBIGUITY inherited from S6.6: the supplement does
  not name them).  The velocity `u^t` is `movU`, `L(t) = ‖∇u^t‖_∞` is `r2MovL` (the sup of the operator norm of the derivative, as
  a real number; its finiteness and integrability are asserted).
* `h_N^t = f_N^t/q_N^t` (ratio of Lebesgue densities) is the Radon--Nikodym derivative `d f_N^t/dQ_N^t` (`f_N^t ≪ Q_N^t` is asserted).
* Families of particle laws over all `N ≥ 2` are sequences of realizations `Ω : ℕ → Type`, time marginals `P_N^t = Law(X_N^t)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### S11.3: power integrability for moving Gibbs preparations -/

section MovingLp

/-- `L(t) = ‖∇u^t‖_∞` (S L8888): the supremum of the operator norm of `D u^t`, `u^t = ν∇log ρ^t + qx + ∇g*ρ^t`
(`movU`), as a real number (finiteness is asserted by `r2_moving_Lp`). -/
def r2MovL (d : ℕ) (s q β : ℝ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) : ℝ :=
  (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖).toReal

/-- The variable exponent `p(t) = [1 - (1 - p₀⁻¹)exp(-c₀⁻¹∫_0^tL(r)dr)]⁻¹` of `W:eq:r2-moving-power` (S L8906-8907). -/
def r2MovExponent (cL p₀ : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * ∫ r in Set.Icc (0 : ℝ) t, L r))⁻¹

/-- The limit exponent `p_∞ = lim_{t→∞}p(t) = [1 - (1 - p₀⁻¹)exp(-c₀⁻¹∫_0^∞L)]⁻¹` (S L8908). -/
def r2MovExponentInf (cL p₀ : ℝ) (L : ℝ → ℝ) : ℝ :=
  (1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * ∫ r in Set.Ioi (0 : ℝ), L r))⁻¹

/-- The density ratio `h = d f/dQ_{N,β}(μ^t)` of a law `f` with respect to the moving Gibbs reference at time `t`, as a real function. -/
def r2MovRatio (d : ℕ) (s β : ℝ) (ρ : ℝ → Euc d → ℝ) (N : ℕ) (f : Measure (EucConfig d N)) (t : ℝ)
    (Y : EucConfig d N) : ℝ :=
  ((f.rnDeriv (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t)))) Y).toReal

/-- The `p`-th density moment `∫(h_N^t)^p dQ_N^t` (`ℝ≥0∞`-valued: `⊤` if infinite). -/
def r2MovPowerMoment (d : ℕ) (s β : ℝ) (ρ : ℝ → Euc d → ℝ) (N : ℕ) (f : Measure (EucConfig d N)) (t p : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ Y, ENNReal.ofReal (r2MovRatio d s β ρ N f t Y ^ p) ∂(modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t)))

/-- Proposition 11.3 (S:W:thm:r2-moving-Lp, TeX S L8878-8923): uniform power integrability for moving Gibbs preparations.
`d ≥ 2`, `0 ≤ σ < d/2`, `μ^t` one of the small nonlinear trajectories of S6.3 (`MovNonlinearConclusion`; compact relative perturbations of the
quadratic thermal equilibrium are included), `β > 0`, `L(t) = ‖∇u^t‖_∞` with `∫_0^∞L < ∞` (asserted), `f_N^t` the canonical particle law with initial
preparation `Q_{N,γ}(μ^0)` (`γ > 0` for `σ > 0`, `γ ≥ 0` for `σ = 0`).  There are `a_* > 0` (from the logarithmic row estimate; used only for `σ = 0`, `γ = 0`)
and `c₀ > 0` independent of `N, t` (`cL` here), such that for every `p₀ > 1` with `θ₀ = p₀γ - (p₀-1)β > 0` (`γ > 0`), resp. `> -a_*` (`γ = 0`):
(1) the initial `p₀` density moment `sup_N∫(h_N^0)^{p₀}dQ_N^0` is bounded for the Gibbs preparations;
(2) with `p(t)`, `p_∞ = lim p(t) > 1` (`r2MovExponent`, `r2MovExponentInf`): `sup_N sup_t ∫(h_N^t)^{p(t)}dQ_N^t < ∞` and `sup_N sup_t‖h_N^t‖_{L^{p_∞}(Q_N^t)} < ∞`
(`f_N^t ≪ Q_N^t` included);
(3) more generally, for every `p₀ > 1` (no condition on `θ₀`) and every initial law `f_N^0 ≪ Q_N^0` with `∫(h_N^0)^{p₀}dQ_N^0 ≤ K₀` (uniformly in `N`) the first bound in (2) holds with a constant depending only on `K₀` (and `p₀`).
The constants may depend on the positive temperatures, the uniform density bounds and the chosen small class (they are chosen after the class, before the
trajectory and the particles).  Not asserted (as in the source): iid preparation for `σ > 0`.  The `c₀` of the exponential moment `W:eq:r2-moving-source-exponential`
and the constant `C₀` are internal to the proof (`cL` is the `c₀` of `W:eq:r2-moving-power`, admissible for every `p₀` of the stated range).
Technical: `N ≥ 2`. -/
theorem r2_moving_Lp (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ) :
    ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        (∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
          ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            (∀ t : ℝ, 0 ≤ t → (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖) < ⊤) ∧
            Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
        ∃ astar cL : ℝ, 0 < astar ∧ 0 < cL ∧
          (∀ p₀ : ℝ, 1 < p₀ → ∀ K₀ : ℝ, ∃ K : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
              MovParticleSetup P d s q β N X₀ W X →
              P.map X₀ ≪ modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ 0)) →
              r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ ≤ ENNReal.ofReal K₀ →
              ∀ t : ℝ, 0 ≤ t →
                P.map (X t.toNNReal) ≪ modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t)) ∧
                r2MovPowerMoment d s β ρ N (P.map (X t.toNNReal)) t
                  (r2MovExponent cL p₀ (r2MovL d s q β ρ) t) ≤ ENNReal.ofReal K) ∧
          ∀ p₀ : ℝ, 1 < p₀ →
          (0 < γ → 0 < p₀ * γ - (p₀ - 1) * β) → (γ = 0 → -astar < p₀ * γ - (p₀ - 1) * β) →
          ∃ K : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            1 < r2MovExponentInf cL p₀ (r2MovL d s q β ρ) ∧
            ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
              MovParticleSetup P d s q β N X₀ W X →
              MovPrepared d s N γ (withDensityReal (ρ 0)) (P.map X₀) →
              r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ ≤ ENNReal.ofReal K ∧
              ∀ t : ℝ, 0 ≤ t →
                P.map (X t.toNNReal) ≪ modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t)) ∧
                r2MovPowerMoment d s β ρ N (P.map (X t.toNNReal)) t
                  (r2MovExponent cL p₀ (r2MovL d s q β ρ) t) ≤ ENNReal.ofReal K ∧
                eLpNorm (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t)
                  (ENNReal.ofReal (r2MovExponentInf cL p₀ (r2MovL d s q β ρ)))
                  (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t))) ≤ ENNReal.ofReal K := by
  sorry

end MovingLp

/-! ### S11.4: singular moment transfer on moving and shifted windows -/

section MovingTransfer

/-- The family of particle laws of sequences of realizations: `Pfam t N = Law(X_N^t)`. -/
def r2MovFamily {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N) : ℝ≥0 → ∀ N, Measure (EucConfig d N) :=
  fun t N => (P N).map (X N t)

/-- The tail assertion of S9.2 for a *family* `h_θ`, `h_{θ,j}` of kernels, uniformly in the parameter `θ`
(`lim_j sup_θ sup_{N,i}‖N F_N^{h_{θ,j}-h_θ}‖_{L^r(P_N^i)} = 0`, also centered). -/
def R2ActualFTailFam {ι Θ : Type*} (μ : ι → Measure (Euc d)) (r : ℝ) (h : Θ → Euc d → Euc d → ℝ)
    (hj : Θ → ℕ → Euc d → Euc d → ℝ) (P : ι → ∀ N, Measure (EucConfig d N)) : Prop :=
  Tendsto (fun j => ⨆ (θ : Θ) (i : ι) (N : {N : ℕ // 2 ≤ N}),
    eLpNorm (fun X => ((N : ℕ) : ℝ) * pairEnergy (fun x y => hj θ j x y - h θ x y) X (μ i))
      (ENNReal.ofReal r) (P i N)) atTop (𝓝 0) ∧
  Tendsto (fun j => ⨆ (θ : Θ) (i : ι) (N : {N : ℕ // 2 ≤ N}),
    eLpNorm (fun X => ((N : ℕ) : ℝ) * (pairEnergy (fun x y => hj θ j x y - h θ x y) X (μ i) -
        ∫ Y, pairEnergy (fun x y => hj θ j x y - h θ x y) Y (μ i) ∂(P i N)))
      (ENNReal.ofReal r) (P i N)) atTop (𝓝 0)

/-- A family of kernels `h_θ` with finite-rank approximations `h_{θ,j}` retaining a common singular bound `C B W_σ` and converging
uniformly in `θ` in `L^r(μ_*^{⊗2})` (`rσ < d`): the hypothesis "the kernel approximations converge uniformly in the required `L^r(μ_*^{⊗2})` norm
and retain the common singular bound" of S11.4 (S L9120-9122). -/
structure IsR2UniformApprox {Θ : Type*} (s C B : ℝ) (μ : Measure (Euc d)) (h : Θ → Euc d → Euc d → ℝ)
    (hj : Θ → ℕ → Euc d → Euc d → ℝ) : Prop where
  finiteRank : ∀ θ j, ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
    IsR2FiniteRankData c u ∧ hj θ j = r2FiniteRankKernel c u
  envelope : ∀ θ j x y, x ≠ y → |hj θ j x y| ≤ C * B * (1 + rieszWeight s (x - y))
  converges : ∀ r : ℝ, 1 ≤ r → r * s < d →
    Tendsto (fun j => ⨆ θ, eLpNorm (fun p : Euc d × Euc d => hj θ j p.1 p.2 - h θ p.1 p.2)
      (ENNReal.ofReal r) (μ.prod μ)) atTop (𝓝 0)

/-- The bounded `C_b²` ball of velocities `‖v‖_{C_b²} ≤ Λ`. -/
def IsR2VelocityBall (d : ℕ) (Λ : ℝ) (v : Euc d → Euc d) : Prop :=
  ContDiff ℝ 2 v ∧ cbNormVecE 2 v ≤ ENNReal.ofReal Λ

/-- Corollary 11.4 (S:W:cor:r2-moving-moment-transfer, TeX S L9109-9126): singular moment transfer on moving and shifted windows.
For the Gibbs preparations of Proposition 11.3 (`γ > 0` for `σ > 0`, `γ ≥ 0` for `σ = 0`), along the small nonlinear trajectories (`MovNonlinearConclusion`
class), and for a sequence of canonical realizations with `MovPrepared` initial laws:
(1) the actual-law hypothesis `W:eq:round2-actual-density` holds with one exponent `p_∞ > 1` and one constant `K` at every time `t ≥ 0`, for the actual reference `Q_N^t`
(`HasR2ActualDensity s β p_∞ K μ^t (Law X_N^t)`);
(2) Proposition 9.2 applies uniformly in time: for the kernel class `IsBoundedPairKernel s B` and every finite `r ≥ 1` there is `C` (common for all
trajectories of the class, all times, hence all windows) with the bounds `R2ActualFBound`, `R2ActualLinearBound` (centers `μ^t`), and the tail
`R2ActualFTail` uniformly in time for kernel approximations `IsRound2Approx` relative to the fixed reference `μ_* = ρ_*dx` (convergence in `L^r(μ_*^{⊗2})` transfers
to `μ^t` by `μ^t ≤ Cμ_*`);
(3) the tail assertion is uniform over any family of kernels with uniformly convergent approximations retaining a common singular bound (`IsR2UniformApprox`);
(4) for the commutator families `h_v(x,y) = (v(x)-v(y))·∇g(x-y)` of a bounded `C_b²` ball of velocities (`IsR2VelocityBall d Λ`) there are such uniformly
convergent finite-rank approximations (the uniform mollification and partition of S L9138-9140), hence (3) applies;
(5) time integrals over a window `[b,b+T]` are controlled by the same Hölder/Minkowski arguments: for jointly measurable time-dependent kernels with the common
envelope, `E(∫_b^{b+T}|N F_N^{h_t}(X_N^t,μ^t)|²dt)^{r/2} ≤ C`, uniformly in `b ≥ 0` (`r ≥ 2`).
Constants: `p_∞, K` after the class, `C` after `(B, r)` and `CT` after `(B, r, T)`, both before the trajectory/particles (repair P2,
2026-10-20: `CT` was quantified after the trajectory; by Minkowski `CT = (T C²)^{r/2}` is class-uniform).  AMBIGUITY: item (2) is the transfer for kernels
dominated by `B W_σ` (the fixed dominated kernel); item (4) existence is asserted for all `Λ` with the envelope constant and the approximants chosen after `Λ`. -/
theorem r2_moving_moment_transfer (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) :
    ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        ∃ pinf K : ℝ, 1 < pinf ∧
          (∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
              MovParticleSetup P d s q β N X₀ W X → MovPrepared d s N γ (withDensityReal (ρ 0)) (P.map X₀) →
              ∀ t : ℝ, 0 ≤ t → HasR2ActualDensity s β pinf K (withDensityReal (ρ t)) (P.map (X t.toNNReal))) ∧
          (∀ Λ : ℝ, ∃ (B C₂ : ℝ) (hj : {v : Euc d → Euc d // IsR2VelocityBall d Λ v} → ℕ → Euc d → Euc d → ℝ),
            (∀ v : {v : Euc d → Euc d // IsR2VelocityBall d Λ v},
              IsBoundedPairKernel s B (commutatorKernel d s v.1)) ∧
            IsR2UniformApprox s C₂ B (withDensityReal ρ₀)
              (fun v : {v : Euc d → Euc d // IsR2VelocityBall d Λ v} => commutatorKernel d s v.1) hj) ∧
          ∀ (B : ℝ) (rr : ℝ), 1 ≤ rr →
            (∃ C : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
              ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
              ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
                [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → EucConfig d N)
                (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N),
                (∀ N, 2 ≤ N → MovParticleSetup (P N) d s q β N (X₀ N) (W N) (X N) ∧
                  MovPrepared d s N γ (withDensityReal (ρ 0)) ((P N).map (X₀ N))) →
                (∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
                  R2ActualFBound (fun t : ℝ≥0 => withDensityReal (ρ t)) rr C h (r2MovFamily P X)) ∧
                R2ActualLinearBound (fun t : ℝ≥0 => withDensityReal (ρ t)) rr C (r2MovFamily P X) ∧
                (∀ (C₂ : ℝ) (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ), IsBoundedPairKernel s B h →
                  IsRound2Approx s C₂ B (withDensityReal ρ₀) h hj →
                  R2ActualFTail (fun t : ℝ≥0 => withDensityReal (ρ t)) rr h hj (r2MovFamily P X)) ∧
                (∀ (Θ : Type) (h : Θ → Euc d → Euc d → ℝ) (hj : Θ → ℕ → Euc d → Euc d → ℝ) (C₂ : ℝ),
                  (∀ θ, IsBoundedPairKernel s B (h θ)) → IsR2UniformApprox s C₂ B (withDensityReal ρ₀) h hj →
                  R2ActualFTailFam (fun t : ℝ≥0 => withDensityReal (ρ t)) rr h hj (r2MovFamily P X))) ∧
            (2 ≤ rr → ∀ T : ℝ, 0 < T → ∃ CT : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
              ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
              ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
                [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → EucConfig d N)
                (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N),
                (∀ N, 2 ≤ N → MovParticleSetup (P N) d s q β N (X₀ N) (W N) (X N) ∧
                  MovPrepared d s N γ (withDensityReal (ρ 0)) ((P N).map (X₀ N))) →
                ∀ h : ℝ → Euc d → Euc d → ℝ,
                  (Measurable fun p : ℝ × Euc d × Euc d => h p.1 p.2.1 p.2.2) →
                  (∀ t, 0 ≤ t → IsBoundedPairKernel s B (h t)) → ∀ b : ℝ, 0 ≤ b → ∀ N : ℕ, 2 ≤ N →
                    ∫⁻ ζ, (∫⁻ t in Set.Icc b (b + T), ENNReal.ofReal
                        (((N : ℝ) * pairEnergy (h t) (X N t.toNNReal ζ) (withDensityReal (ρ t))) ^ 2)) ^ (rr / 2)
                      ∂(P N) ≤ ENNReal.ofReal CT) := by
  sorry

end MovingTransfer

/-! ### S11.5, S11.6: independent logarithmic preparation -/

section LogPreparation

/-- Lemma 11.5 (S:O:lem:log-row, TeX S L9537-9547): uniform exponential rows of the centered logarithm, whole space.
`μ = ρ dx` on `ℝ^d`, `d ≥ 1`, `0 ≤ ρ(x) ≤ C₀e^{-a₀|x|²}`, `a₀ > 0`; `g(x,y) = -log|x-y|`, `h(x) = ∫g(x,y)dμ(y)`, `I = ½∫h dμ`.  Then `g ∈ L¹(μ^{⊗2})`
and for some `ε > 0` and `C < ∞` (depending only on `d, C₀, a₀`, quantified before `ρ`): `sup_y∫e^{ε|g(x,y)-h(x)-h(y)+2I|}dμ(x) ≤ C`; in particular the centered
kernel `k` satisfies uniform factorial row bounds `sup_y∫|k(x,y)|^pdμ(x) ≤ C p! ε^{-p}` for all `p ∈ ℕ` (from `z^p ≤ p!ε^{-p}e^{εz}`).  `ρ` is a measurable function (technical).
`μ` is a probability measure (`∫ρ = 1`; repair 2026-10-16, ISSUES §I "S11.5"): the source's proof uses that adding one-body
functions does not change a canonically centered kernel, which needs mass one, and the lemma is applied to `μ^0`; for mass
`m ≠ 1` the centered kernel grows like `(m-1)log|y|` and the row bound fails. -/
theorem r2_log_row_whole (hd : 1 ≤ d) (C₀ a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ ρ : Euc d → ℝ, Measurable ρ → (∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₀ * Real.exp (-a₀ * ‖x‖ ^ 2)) →
      ∫ x, ρ x = 1 →
      Integrable (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2))
        ((withDensityReal ρ).prod (withDensityReal ρ)) ∧
      (∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * |rieszKernel d 0 (x - y) -
          convMeasure (rieszKernel d 0) (withDensityReal ρ) x - convMeasure (rieszKernel d 0) (withDensityReal ρ) y +
          2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) (withDensityReal ρ) z ∂(withDensityReal ρ))|))
        ∂(withDensityReal ρ) ≤ ENNReal.ofReal C) ∧
      (∀ (p : ℕ) (y : Euc d), ∫⁻ x, ENNReal.ofReal (|rieszKernel d 0 (x - y) -
          convMeasure (rieszKernel d 0) (withDensityReal ρ) x - convMeasure (rieszKernel d 0) (withDensityReal ρ) y +
          2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) (withDensityReal ρ) z ∂(withDensityReal ρ))| ^ p)
        ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (p.factorial : ℝ) * (ε⁻¹) ^ p)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hεd : (1 / 2 : ℝ) < d := by linarith
  have hC₁ : 0 ≤ max C₀ 0 := le_max_right _ _
  have hKfin := q33b_K_ne_top hd hεd hC₁ ha₀
  refine ⟨1 / 2, Real.exp (2 * (q33b_K d (1 / 2) (max C₀ 0) a₀).toReal) *
    (q33b_K d (1 / 2) (max C₀ 0) a₀).toReal, by norm_num, fun ρ hm hρ hint => ?_⟩
  have hρ' : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ max C₀ 0 * Real.exp (-a₀ * ‖x‖ ^ 2) := fun x =>
    ⟨(hρ x).1, (hρ x).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
  haveI : IsProbabilityMeasure (withDensityReal ρ) := q33b_prob hm (fun x => (hρ x).1) hint
  have hε0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hℓ := q33b_ell_integrable hε0 hε1 hC₁ ha₀ hm hρ'
  have hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (1 / 2 * q33b_b x y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (q33b_K d (1 / 2) (max C₀ 0) a₀).toReal := fun y => by
    rw [ENNReal.ofReal_toReal hKfin]
    exact q33b_row hd hε0 hε1 hεd hC₁ ha₀ hm hρ' y
  exact q33b_main (μ := withDensityReal ρ) hε0 ENNReal.toReal_nonneg hℓ hrow

/-- Lemma 11.5 (S:O:lem:log-row, TeX S L9546-9547), torus clause: "on the torus the same conclusions hold for the periodic logarithm when `‖ρ‖_∞` is
bounded": for `d ≥ 2`, a probability density `ρ ≤ Λ` on `𝕋^d`, `g * ρ`-centered periodic logarithm `g_μ(x,y) = g(x-y) - g*μ(x) - g*μ(y) + ∬g dμdμ`
(`HRS.centeredKernel (HRS.periodicRiesz d 0)`; note `∬g dμ dμ = 2I`), the periodic logarithm is in `L¹(μ^{⊗2})` and `sup_x∫e^{ε|g_μ(x,y)|}dμ(y) ≤ C`.  The torus clause keeps the standing `d ≥ 2` of the periodic paper (M L419) and of the project's periodic kernel (`HRS.periodic_log_row` is stated for `2 ≤ d`; the TeX lemma's `d ≥ 1` is for the whole-space clause).  The row bound is the
already formalised `HRS.periodic_log_row` (Lemma 4.24, any `a ∈ (0,d)`); `C, ε` are chosen after the bound `Λ` (and `d`). -/
theorem r2_log_row_torus (hd : 2 ≤ d) (Λ : ℝ) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ ρ : HRS.Torus d → ℝ, HRS.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      Integrable (fun p : HRS.Torus d × HRS.Torus d => HRS.periodicRiesz d 0 (p.1 - p.2))
        ((HRS.withDensityReal ρ).prod (HRS.withDensityReal ρ)) ∧
      ∀ x, ∫⁻ y, ENNReal.ofReal (Real.exp (ε * |HRS.centeredKernel (HRS.periodicRiesz d 0)
        (HRS.withDensityReal ρ) x y|)) ∂(HRS.withDensityReal ρ) ≤ ENNReal.ofReal C := by
  refine ⟨1, q33C d Λ, one_pos, fun ρ _ hρ => ⟨q33_integrable hd Λ ρ hρ, fun x => ?_⟩⟩
  exact q33_row_le hd Λ ρ hρ x

/-- Proposition 11.6 (S:O:cor:log-path, TeX S L9578-9585): verification of independent logarithmic preparation.  `σ = 0` (the logarithmic kernel
`g = -log|x|`), `d ≥ 2`, `a, β > 0`, `T > 0`, `μ^t = ρ^t dx` the stationary measure or one of the small nonlinear trajectories of S2.1 (`IsR2WindowTrajectory`; small relative
perturbations of the thermal measure, bounded above by a common Gaussian density); `β₊ > 0` an upper bound for the positive temperatures.  The independent
preparation `Q_{N,0}(μ^0) = (μ^0)^{⊗N}` satisfies the initial power-moment and initial-correction hypotheses used in S2.1(iii) and S11.3:
(a) bounded normalizers on a fixed interval around zero with constants independent of `N` (there is `a_* > 0` and `K₀` with `|log K_{N,θ}(μ^0)| ≤ K₀` for
`θ ∈ [-a_*,β₊]`, `N ≥ 2`; S L9593-9594);
(b) the initial power moment (`S:eq:iid-log-initial-moment`): for `p > 1` sufficiently close to one,
`∫(d(μ^0)^{⊗N}/dQ_{N,β}(μ^0))^pdQ_{N,β}(μ^0) ≤ C`, uniformly in `N`;
(c) the initial correction hypotheses at `γ = 0`: the static Edgeworth expansion of `R2StaticEdgeworth` for the oscillator indices `m > 6d+44` (i.e. `m > J+2d+4`, `J = 4d+40`) and, given the
bounded adjoint-orbit inputs of S10 (adjoint solutions and the summable cosine orbit tests at index `k ≥ 4d+40`; the content of S L9533 that the quadratic-model
orbit estimates verify the hypothesis), the expansion of the whole initial propagated path (`R2InitPathEdgeworth`, coefficients along the trajectory), the initial covariance being the
bridge covariance (`R_0 = I`).
"The trajectory and weighted spaces are unchanged."  AMBIGUITY: the row is informal ("satisfies the hypotheses used in ..."); the formal reading is (a)-(c), (c) being the
initial-correction input of S10.2 (the uniformity of the projection tails for shifted windows, S L9533-9534, is not separately stated).  The constants `ε_*, c₁, C₁` (the class of S2.1, `R2ClassExists`) and `a_*` are
chosen first (before the trajectory); the logarithmic row estimate `r2_log_row_whole` enters (S L9588-9590). -/
theorem r2_log_path (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) (βplus : ℝ)
    (hβplus : 0 < βplus) :
    ∃ εstar c₁ C₁ : ℝ, 0 < εstar ∧ 0 < c₁ ∧ 0 < C₁ ∧ R2ClassExists d 0 a β εstar c₁ C₁ ∧
      ∃ astar : ℝ, 0 < astar ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d 0 a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
        IsR2WindowTrajectory d 0 a β ρβ εstar c₁ C₁ ρ →
        (∃ K₀ : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (-astar) βplus,
          0 < gibbsNormalizer (rieszKernel d 0) N θ (withDensityReal (ρ 0)) ∧
          |Real.log (gibbsNormalizer (rieszKernel d 0) N θ (withDensityReal (ρ 0)))| ≤ K₀) ∧
        (∃ p₁ : ℝ, 1 < p₁ ∧ ∀ p : ℝ, 1 < p → p < p₁ → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
          (Measure.pi fun _ : Fin N => withDensityReal (ρ 0)) ≪
              modulatedGibbs (rieszKernel d 0) N β (withDensityReal (ρ 0)) ∧
          ∫⁻ Y, ENNReal.ofReal
              ((((Measure.pi fun _ : Fin N => withDensityReal (ρ 0)).rnDeriv
                (modulatedGibbs (rieszKernel d 0) N β (withDensityReal (ρ 0)))) Y).toReal ^ p)
            ∂(modulatedGibbs (rieszKernel d 0) N β (withDensityReal (ρ 0))) ≤ ENNReal.ofReal C) ∧
        (∀ m : ℕ, ((4 * d + 40 : ℕ) : ℝ) + 2 * d + 4 < m → R2StaticEdgeworth d 0 0 m (ρ 0)) ∧
        (∀ k m : ℕ, 4 * d + 40 ≤ k → (k : ℝ) + 2 * d + 4 < m →
          (∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ f : ℝ → Euc d → ℝ,
            IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t (oscTestFun (m : ℝ) α) f) →
          (∀ n α, MemCb k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T n α)) →
          (Summable fun p : ℕ × MultiIndex d =>
            cbNorm k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T p.1 p.2)) →
          R2InitPathEdgeworth ((quadraticGradientDyn d 0 a β).coeff ρ) 0 0 m T (ρ 0)) := by
  sorry

end LogPreparation

end HRS.Whole

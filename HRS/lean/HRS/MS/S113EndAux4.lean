import HRS.MS.S113EndAux3
import HRS.MS.R2S11Aux7
import HRS.MS.R2S11Aux6

/-!
# S11.3 endpoint (worker S113X), part 4: the X cores, stated exactly

Notation: `Q_N^t = s113x_Q` (`Q_{N,β}(μ^t)`, `μ^t = ρ^t dx`), `R_N^t = s113x_source` (`W:r2mov:source-identity`).

* `S113XSource` (X1): the source is measurable, vanishes when `L(t) = 0`, and has the exponential moment
  `W:eq:r2-moving-source-exponential` with constants uniform in the class, `N`, `t` (source identity of S6.9 for non-translated
  trajectories + the pressure bound S3.1; TeX S L8925-8963).
* `S113XLocalized` (X2): for the actual law `f^t` of a particle setup with `f^0 ≪ Q^0` and `∫(h^0)^{p₀}dQ^0 < ∞` there are bounded measurable
  nonnegative ratios `r_n(t,·)` (killed densities divided by `q_N^t`, after smooth approximation of the initial density)
  such that `r_n(t) → h^t` in `L¹(Q^t)` with `f^t ≪ Q^t` (path representation, killed transition contraction; TeX S L9063-9093),
  initial power moments `≤ M₀ + 1/(n+1)`, and for every locally absolutely continuous exponent `p > 1`
  the mass `M_n(t) = ∫ r_n(t)^{p(t)}dQ^t` is positive, locally absolutely continuous and satisfies almost everywhere the
  power chain inequality `W:eq:r2-moving-power-chain` (killed Dirichlet Fokker-Planck, `Φ_{p,ε}` regularization; TeX S L8965-9030).
* `S113XMeas` (X5): `t ↦ L(t) = ‖∇u^t‖_∞` is a.e.-strongly measurable on `(0,∞)`.
* `S113XLogNormalizer` (X4): bounded `log K_{N,θ}(μ^0)` for `θ ∈ [-a_*,0]` on the class (`r2_log_path` (a) for this class; used only for `γ = 0`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- `Q_N^t = Q_{N,β}(μ^t)` with `μ^t = ρ^t dx`. -/
abbrev s113x_Q (d : ℕ) (s β : ℝ) (ρ : ℝ → Euc d → ℝ) (N : ℕ) (t : ℝ) : Measure (EucConfig d N) :=
  HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t))

open Classical in
/-- The source `R_N^t = (𝓛_N^* q_N^t - ∂_t q_N^t)/q_N^t` of the moving reference (zero on the collision set; the time derivative
is the one-sided derivative at `t ≥ 0`). -/
def s113x_source (d : ℕ) (s q β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (X : EucConfig d N) : ℝ :=
  if X ∈ eucCollisionSet d N then 0 else
    (movFP d s q β N (movQDensity d s β N (ρ t)) X -
      derivWithin (fun τ => movQDensity d s β N (ρ τ) X) (Set.Ici t) t) / movQDensity d s β N (ρ t) X

/-- X1: the exponential moment of the source (`W:eq:r2-moving-source-exponential`). -/
def S113XSource (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∃ cL C₀ : ℝ, 0 < cL ∧ 0 ≤ C₀ ∧
    ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        Measurable (s113x_source d s q β N ρ t) ∧
        (r2MovL d s q β ρ t = 0 → ∀ X, s113x_source d s q β N ρ t X = 0) ∧
        (0 < r2MovL d s q β ρ t →
          ∫⁻ X, ENNReal.ofReal (Real.exp ((cL / r2MovL d s q β ρ t) * |s113x_source d s q β N ρ t X|))
              ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal (Real.exp C₀))

/-- X2: the killed (localized) approximations of the actual law (killed Dirichlet diffusion, power chain rule, removal of localization). -/
def S113XLocalized (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      MovParticleSetup P d s q β N X₀ W X →
      P.map X₀ ≪ s113x_Q d s β ρ N 0 →
      ∀ p₀ : ℝ, 1 < p₀ → r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ < ⊤ →
      ∃ rr : ℕ → ℝ → EucConfig d N → ℝ,
        (∀ n t, Measurable (rr n t)) ∧ (∀ n t x, 0 ≤ rr n t x) ∧
        (∀ n (T : ℝ), ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, rr n t x ≤ B) ∧
        (∀ t : ℝ, 0 ≤ t → P.map (X t.toNNReal) ≪ s113x_Q d s β ρ N t ∧
          Tendsto (fun n => ∫⁻ x, ‖rr n t x - r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t x‖ₑ
            ∂(s113x_Q d s β ρ N t)) atTop (𝓝 0)) ∧
        (∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (rr n 0 x ^ p₀) ∂(s113x_Q d s β ρ N 0) ≤
          r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ + ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
        ∀ p : ℝ → ℝ, (∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval p 0 T) →
          (∀ t : ℝ, 0 ≤ t → 1 < p t) → ∀ n : ℕ,
          (∀ t : ℝ, 0 ≤ t → 0 < s113_powerMass (s113x_Q d s β ρ N t) (rr n t) (p t)) ∧
          ∀ T : ℝ, 0 ≤ T →
            AbsolutelyContinuousOnInterval
              (fun t => s113_powerMass (s113x_Q d s β ρ N t) (rr n t) (p t)) 0 T ∧
            ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 T →
              deriv (fun u => s113_powerMass (s113x_Q d s β ρ N u) (rr n u) (p u)) t ≤
                (p t - 1) * s113_powerMass (s113x_Q d s β ρ N t) (rr n t) (p t) *
                    (∫ x, s113x_source d s q β N ρ t x
                      ∂(s113_powerTilt (s113x_Q d s β ρ N t) (rr n t) (p t))) +
                  deriv p t * s113_powerMass (s113x_Q d s β ρ N t) (rr n t) (p t) *
                    (∫ x, Real.log (rr n t x)
                      ∂(s113_powerTilt (s113x_Q d s β ρ N t) (rr n t) (p t)))

/-- X5: measurability of `t ↦ L(t) = ‖∇u^t‖_∞` on `(0,∞)`. -/
def S113XMeas (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
      AEStronglyMeasurable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ)))

/-- X4: bounded logarithmic normalizers at small negative temperatures on the class (used only for `γ = 0`, `σ = 0`). -/
def S113XLogNormalizer (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∃ astar : ℝ, 0 < astar ∧ ∃ K₀ : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (-astar) (0 : ℝ),
      0 < HRS.Whole.gibbsNormalizer (rieszKernel d s) N θ (HRS.Whole.withDensityReal (ρ 0)) ∧
      |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N θ (HRS.Whole.withDensityReal (ρ 0)))| ≤ K₀

/-- All X cores for the class `(j, m, ε_*, r, c₀)` and the preparation parameter `γ`. -/
def S113XCores (d : ℕ) (s q β γ : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  S113XSource d s q β ρ₀ j m εstar r c₀ ∧ S113XLocalized d s q β ρ₀ j m εstar r c₀ ∧
    S113XMeas d s q β ρ₀ j m εstar r c₀ ∧
    (γ = 0 → S113XLogNormalizer d s q β ρ₀ j m εstar r c₀)

/-- `Q_N^t` is a probability measure on the small class (uniform two-sided Gibbs bounds, S3.1). -/
theorem s113x_Q_prob (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} {εstar r c₀ c C₁ : ℝ}
    (hC₁ : 0 < C₁) (hc₀ : 0 < c₀)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (s113x_Q d s β ρ N t) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE, hfam⟩ :=
    HRS.MS.MovEnt.s66_fam_exists hd hs0 hsd hq hβ hρ₀ hC₁ hc₀.le hNL
  have hfm := hfam f0 hf0 ρ hρ
  exact HRS.MS.R2S11.s11_Q_prob hd hs0 hs hβ (M := M) (L := L)
    ⟨hfm.prob t ht, hfm.bound t ht, hfm.logm t ht⟩ hN

end HRS.MS.S113BD

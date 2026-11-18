import HRS.MS.GenPathAux60

/-!
# S5.6 packet P7l: the `L^p` distance of the initial paths, through the joint law of `(X 0, c)`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

/-- The initial-path discrepancy `‖A(k₀(x)) - g(c)‖^p` as a function of the configuration and the array. -/
def s56Hfun (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ}
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d b.m b.T) (p : ℝ) (x : EucConfig d N)
    (c : ℕ × MultiIndex d → ℝ) : ℝ≥0∞ :=
  ‖s56EvalPath hbv.hT.le (s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical x)
    (HRS.Whole.withDensityReal (S.ρ N 0))) - g c‖ₑ ^ p

theorem s56Hfun_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T)
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d b.m b.T) (hg : Measurable g) (p : ℝ) :
    Measurable fun z : EucConfig d N × (ℕ × MultiIndex d → ℝ) => s56Hfun b hbv S g p z.1 z.2 := by
  unfold s56Hfun
  have h1 : Measurable fun x : EucConfig d N => s56EvalPath hbv.hT.le
      (s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal (S.ρ N 0))) :=
    (s56EvalPath hbv.hT.le).continuous.measurable.comp (s56_k0_meas' b hbv S hN hC (S.σ N))
  exact ((h1.comp measurable_fst).sub (hg.comp measurable_snd)).enorm.pow_const p

theorem s56_eps_integral (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (s : ℕ → Set.Icc (0 : ℝ) b.T) (hs : DenseRange s)
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d b.m b.T)
    (hgleft : ∀ c ∈ Set.range (s56PathCoords (d := d) b.m b.T s), s56PathCoords (d := d) b.m b.T s (g c) = c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → EucConfig d N) (X0 : Ω → EucConfig d N)
    (hX0 : ∀ᵐ ζ ∂P, X0 ζ = X₀ ζ) (η₀ : Ω → (Euc d → ℝ) → ℝ) (Ψt : Ω → (ℕ × MultiIndex d → ℝ))
    (hΨ : ∀ᵐ ζ ∂P, s56Psic S N s η₀ ζ = Ψt ζ)
    (hrange : ∀ᵐ ζ ∂P, s56Psic S N s η₀ ζ ∈ Set.range (s56PathCoords (d := d) b.m b.T s)) (p : ℝ) (hp : 0 < p) :
    ∫⁻ ζ, s56Hfun b hbv S g p (X0 ζ) (Ψt ζ) ∂P ≤
      ENNReal.ofReal (S.A N) ^ p * ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE fun α : MultiIndex d =>
        S.κ N * (HRS.Whole.pair (HRS.Whole.empirical (X₀ ζ))
            (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) -
          η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) ^ p ∂P := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
  refine lintegral_mono_ae ?_
  filter_upwards [hX0, hΨ, hrange] with ζ h1 h2 h3
  unfold s56Hfun
  rw [← h2, h1, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  refine ENNReal.rpow_le_rpow ?_ hp.le
  exact s56_eps_pointwise b hbv S hN hC s hs g (X₀ ζ) (η₀ ζ) (s56Psic S N s η₀ ζ)
    (fun i => rfl) (hgleft _ h3)

end HRS.MS.GenPath

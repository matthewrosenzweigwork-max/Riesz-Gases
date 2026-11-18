import HRS.MC.S7FCF5Defs
import HRS.MC.S7FCF5A1
import HRS.MC.S7FCF5BE
import HRS.MC.S7FCW12B

/-!
# Packet fcf5g, E1: a.s. continuity of the windows `η_N^{a+·}` and `ζ_N^{a+·}` in `E_r`

Proof of `fcf5_E1_window_cont` (`S7FCF5Plan.lean`), for `a ≥ 0`, `N ≥ 1`.

* `η`: a.s. every coordinate path `s ↦ X_s(ω)_i` is continuous (`IsStrongSolution.cont`).  Then, on `[0,T]`, the
  two families `t ↦ empirical (X_{a+t})` and `t ↦ withDensityReal (ρ^{a+t})` are probability measures whose real
  Fourier coefficients are continuous (empirical: finite sums of continuous functions; density: `A1` joint continuity of
  `ρ` on `[0,∞) × 𝕋^d`, `Regime.bounds` and dominated convergence).  `E1a` gives continuity of `ofMeasureDiff`, and
  `etaE = √N • ofMeasureDiff (empirical ·) μ`.
* `ζ`: `zetaAt r P X t ω = zetaE r (P.map (X t)) (X t ω)` and `s7fcw12_zetaAt_continuousOn` (FC-E helper, proved)
  gives continuity of `t ↦ zetaAt r P X t ω` on all of `ℝ` for a.e. `ω` (its mean is a continuous function of `t`
  by dominated convergence, the coefficients are bounded by `2√2`).

Namespace `HRS.MC.Sec7.S7FCF5G`, prefix `S7FCF5G_` for helpers, `_proof` for the theorem.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5G

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The real Fourier coefficient of the empirical measure along a continuous path of configurations is continuous. -/
theorem S7FCF5G_coef_emp_cont {N : ℕ} (Y : ℝ → Config d N) (hY : ∀ i, Continuous fun s => Y s i)
    (k : NonzeroLattice d) :
    Continuous fun s => Torus.measureRealCoeff (empirical (Y s)) k := by
  have hfun : (fun s => Torus.measureRealCoeff (empirical (Y s)) k) =
      fun s => (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (Y s i) := by
    funext s
    unfold Torus.measureRealCoeff
    rw [integral_empirical _ (continuous_realMode' k)]
  rw [hfun]
  exact continuous_const.mul (continuous_finset_sum _ fun i _ => (continuous_realMode' k).comp (hY i))

/-- Real Fourier coefficients of the density measures `ρ^{a+t}`, `t ∈ [0,T]`, are continuous in `t`. -/
theorem S7FCF5G_coef_density_cont (R : Regime d) (k : NonzeroLattice d) {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    ContinuousOn (fun t => Torus.measureRealCoeff (withDensityReal (R.ρ (a + t))) k) (Set.Icc 0 T) := by
  obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
  have hpos : ∀ s : ℝ, 0 ≤ s → ∀ x, 0 ≤ R.ρ s x := fun s hs x => le_trans hm₀.le (hb s hs x).1
  have hmeas : ∀ s : ℝ, 0 ≤ s → Measurable (R.ρ s) := fun s hs =>
    (HRS.MC.Sec7.S7FCF5A.S7FCF5A_rho_cont_x R hs).measurable
  -- pointwise continuity in `t`, from the joint continuity `A1`
  have hcs : ∀ x : Torus d, ContinuousOn (fun t => R.ρ (a + t) x * Torus.realMode k x) (Set.Icc 0 T) := by
    intro x
    have hf : ContinuousOn (fun t : ℝ => (a + t, x)) (Set.Icc 0 T) :=
      (by fun_prop : Continuous fun t : ℝ => (a + t, x)).continuousOn
    have hmap : Set.MapsTo (fun t : ℝ => (a + t, x)) (Set.Icc 0 T) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
      fun t ht => Set.mk_mem_prod (Set.mem_Ici.2 (by linarith [ht.1])) (Set.mem_univ _)
    have hA := (HRS.MC.Sec7.S7FCF5A.fcf5_A1_rho_cont_proof R).comp hf hmap
    exact hA.mul continuousOn_const
  -- dominated convergence for the parametric integral
  have hint : ContinuousOn (fun t => ∫ x, R.ρ (a + t) x * Torus.realMode k x) (Set.Icc 0 T) := by
    refine continuousOn_of_dominated (bound := fun _ => M₀ * Real.sqrt 2) (fun t ht => ?_) (fun t ht => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun x => hcs x)
    · exact ((hmeas (a + t) (by linarith [ht.1])).mul (continuous_realMode' k).measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hs : 0 ≤ a + t := by linarith [ht.1]
      have h1 : |R.ρ (a + t) x| ≤ M₀ := by
        rw [abs_of_nonneg (hpos _ hs x)]; exact (hb _ hs x).2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 (Torus.abs_realMode_le k x) (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  refine hint.congr fun t ht => ?_
  have hρt : Measurable (R.ρ (a + t)) := hmeas (a + t) (by linarith [ht.1])
  unfold Torus.measureRealCoeff
  exact integral_withDensityReal_eq _ hρt (hpos (a + t) (by linarith [ht.1])) _

/-- Continuity of the `η`-window in `E_r` on `[0,T]` for a path of configurations with continuous coordinates. -/
theorem S7FCF5G_eta_cont (R : Regime d) (r : ℝ) (hr : (d : ℝ) < 2 * r) {N : ℕ} (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (Y : ℝ → Config d N) (hY : ∀ i, Continuous fun s => Y s i) :
    ContinuousOn (fun t => etaE r (Y (a + t)) (withDensityReal (R.ρ (a + t)))) (Set.Icc 0 T) := by
  have hN0 : 0 < N := by omega
  have hdens : ∀ s : ℝ, 0 ≤ s → IsProbDensity (R.ρ s) := fun s hs =>
    (R.mf (s + 1) (by linarith)).density s ⟨hs, by linarith⟩
  have hE := HRS.MC.Sec7.S7FCF5B.fcf5_E1a_ofMeasureDiff_cont_proof r hr
    (fun t => empirical (Y (a + t))) (fun t => withDensityReal (R.ρ (a + t))) (Set.Icc 0 T)
    (fun t ht => empirical_isProbabilityMeasure hN0 (Y (a + t)))
    (fun t ht => isProb_withDensityReal (hdens (a + t) (by linarith [ht.1])))
    (fun k => (S7FCF5G_coef_emp_cont (fun s => Y (a + s))
      (fun i => (hY i).comp (continuous_const.add continuous_id)) k).continuousOn)
    (fun k => S7FCF5G_coef_density_cont R k ha T)
  exact hE.const_smul (Real.sqrt N)

/-- **E1 (a.s. continuity of the windows `η_N^{a+·}` and `ζ_N^{a+·}` in `E_r`)**, proof. -/
theorem fcf5_E1_window_cont_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : FCPrepared R P X₀ W X) (a : ℝ) (ha : 0 ≤ a) :
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
        etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ∧
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
        zetaE r (P.map (X (a + t).toNNReal)) (X (a + t).toNNReal ω)) := by
  have hd : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN0 : 0 < N := by omega
  have hcont := hreal.solution 0 |>.cont
  have hadapt := hreal.solution 0 |>.adapted
  have hR : ∀ᵐ ω ∂P, ∀ i, Continuous fun s : ℝ => X s.toNNReal ω i :=
    hcont.mono fun ω hω i => (hω i).comp continuous_real_toNNReal
  constructor
  · filter_upwards [hR] with ω hω
    have key := S7FCF5G_eta_cont R r hd hN a ha T (fun s => X s.toNNReal ω) hω
    exact continuousOn_iff_continuous_restrict.1 key
  · filter_upwards [hcont, hR] with ω hω hω'
    have h2 := HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_continuousOn r hd P X hadapt hcont hN0 ω hω' Set.univ
    have h3 : Continuous fun t : ℝ => zetaAt r P X (a + t) ω :=
      (continuousOn_univ.1 h2).comp (continuous_const.add continuous_id)
    exact h3.comp continuous_subtype_val

end HRS.MC.Sec7.S7FCF5G

end

import HRS.MC.S7PIDefs
import HRS.MC.L2C0
import HRS.Kernel.D1
import HRS.Stochastic.SelectedFlow

/-!
# Packet piF1 (F3): the bracket identity `F:eq:bracket-exact`

`s7_PIF_bracket_proof`: `∑_k (√N Φ^i_k)(√N Φ^j_k) = obsRate(s)_{ij} + N^{-1/2} · 2β⁻¹ · η_N^s(∇obsTest_i·∇obsTest_j)`,
pure algebra: the left side is `2β⁻¹ ∫ ∇obsTest_i·∇obsTest_j dμ_N` and `eval (η_N) g = √N (∫ g dμ_N - ∫ g ρ)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIF1_isSmooth_zero : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := by
  unfold Torus.IsSmooth Torus.IsCk
  exact contDiff_const

theorem S7PIF1_grad_zero (x : Torus d) : Torus.grad (0 : Torus d → ℝ) x = 0 := by
  unfold Torus.grad
  have : Torus.lift (0 : Torus d → ℝ) = fun _ => 0 := rfl
  rw [this]
  simp [gradient]

/-- The test functions seen by the observations are smooth in space (for `0 ≤ s`). -/
theorem S7PIF1_obsTest_smooth (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) {s : ℝ} (hs : 0 ≤ s) :
    Torus.IsSmooth (obsTest R.D R.ρ t φ i s) := by
  unfold obsTest
  split_ifs with h
  · exact (HRS.MC.L2C0.l2c0_proof R (φ i) (hφ i) s (t i) hs h).1
  · exact S7PIF1_isSmooth_zero

/-- `eval` is homogeneous. -/
theorem S7PIF1_eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (g : Torus d → ℝ) :
    NegSobolev.eval (c • F) g = c * NegSobolev.eval F g := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
    unfold NegSobolev.fourierCoeff NegSobolev.coord
    have h1 : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from c • F) k
        = c * ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k) :=
      lp.coeFn_smul c (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) ▸ rfl
    rw [h1]
    ring
  rw [this]
  ring

/-- Smoothness of the inner product of two gradients. -/
theorem S7PIF1_isSmooth_inner_grad {g h : Torus d → ℝ} (hg : Torus.IsSmooth g) (hh : Torus.IsSmooth h) :
    Torus.IsSmooth (fun y => inner ℝ (Torus.grad g y) (Torus.grad h y)) := by
  have h1 := HRS.KernelD1Aux.isSmooth_grad hg
  have h2 := HRS.KernelD1Aux.isSmooth_grad hh
  unfold Torus.IsSmooth Torus.IsCk at h1 h2 ⊢
  exact h1.inner ℝ h2

/-- **F3 (bracket identity `F:eq:bracket-exact`, pure algebra)** (statement of
`HRS.MC.Sec7.PIPlan.s7_PIF_bracket`, copied verbatim). -/
theorem s7_PIF_bracket_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i j : Fin q) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ∑ k : Fin N × Fin d,
        (Real.sqrt N * empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω k) *
        (Real.sqrt N * empiricalNoiseIntegrand R.D (t j) (fun r => propagator R.D R.ρ r (t j) (φ j)) X s ω k) =
      obsRate R.D R.ρ t φ s i j + (Real.sqrt N)⁻¹ * (2 * R.D.invβ *
        NegSobolev.eval (etaE m (X s.toNNReal ω) (withDensityReal (R.ρ s)))
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i s) y) (Torus.grad (obsTest R.D R.ρ t φ j s) y))) := by
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hβ : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  have hsqb : Real.sqrt (2 * R.D.invβ) * Real.sqrt (2 * R.D.invβ) = 2 * R.D.invβ :=
    Real.mul_self_sqrt (by positivity)
  have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  have hnoise : ∀ (l : Fin q) (p : Fin N) (a : Fin d),
      empiricalNoiseIntegrand R.D (t l) (fun r => propagator R.D R.ρ r (t l) (φ l)) X s ω (p, a)
        = (Real.sqrt (2 * R.D.invβ) / N) *
          (Torus.grad (obsTest R.D R.ρ t φ l s) (X s.toNNReal ω p)) a := by
    intro l p a
    unfold empiricalNoiseIntegrand obsTest
    by_cases h : s ≤ t l
    · simp [h, hs.1]
    · have : s ∉ Set.Icc 0 (t l) := fun hh => h hh.2
      simp [this, h, S7PIF1_grad_zero]
  -- smoothness of the test functions and of the integrand
  have hsm : ∀ l, Torus.IsSmooth (obsTest R.D R.ρ t φ l s) := fun l =>
    S7PIF1_obsTest_smooth R t φ hφ l hs.1
  set g : Torus d → ℝ := fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i s) y)
    (Torus.grad (obsTest R.D R.ρ t φ j s) y) with hg
  have hgsm : Torus.IsSmooth g := S7PIF1_isSmooth_inner_grad (hsm i) (hsm j)
  -- the mean-field density is a probability density
  have hmf := R.mf (T + 1) (by linarith [hs.1, hs.2])
  have hdens : IsProbDensity (R.ρ s) := hmf.density s ⟨hs.1, by linarith [hs.2]⟩
  have : IsProbabilityMeasure (withDensityReal (R.ρ s)) := isProb_withDensityReal hdens
  have : IsProbabilityMeasure (empirical (X s.toNNReal ω)) := empirical_isProbabilityMeasure hN0 _
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the right-hand side
  have heval : NegSobolev.eval (etaE m (X s.toNNReal ω) (withDensityReal (R.ρ s))) g
      = Real.sqrt N * (pair (empirical (X s.toNNReal ω)) g - pair (withDensityReal (R.ρ s)) g) := by
    unfold etaE flucE
    rw [S7PIF1_eval_smul, NegSobolev.eval_ofMeasureDiff hm2 _ _ g hgsm]
  have hpe : pair (empirical (X s.toNNReal ω)) g = (N : ℝ)⁻¹ * ∑ p, g (X s.toNNReal ω p) :=
    pair_empirical hN0 _ g
  have hpd : pair (withDensityReal (R.ρ s)) g = ∫ x, g x * R.ρ s x := by
    unfold pair
    rw [PDE.MFPairing.integral_withDensityReal hdens.measurable hdens.nonneg g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hrate : obsRate R.D R.ρ t φ s i j = 2 * R.D.invβ * ∫ x, g x * R.ρ s x := rfl
  have hL : ∑ k : Fin N × Fin d,
        (Real.sqrt N * empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω k) *
        (Real.sqrt N * empiricalNoiseIntegrand R.D (t j) (fun r => propagator R.D R.ρ r (t j) (φ j)) X s ω k)
      = (2 * R.D.invβ / N) * ∑ p, g (X s.toNNReal ω p) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hgp : g (X s.toNNReal ω p) = ∑ a, (Torus.grad (obsTest R.D R.ρ t φ i s) (X s.toNNReal ω p)) a *
        (Torus.grad (obsTest R.D R.ρ t φ j s) (X s.toNNReal ω p)) a := by
      simp only [hg, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [hgp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hnoise i p a, hnoise j p a]
    calc (Real.sqrt N * (Real.sqrt (2 * R.D.invβ) / N *
            (Torus.grad (obsTest R.D R.ρ t φ i s) (X s.toNNReal ω p)) a)) *
          (Real.sqrt N * (Real.sqrt (2 * R.D.invβ) / N *
            (Torus.grad (obsTest R.D R.ρ t φ j s) (X s.toNNReal ω p)) a))
        = (Real.sqrt N * Real.sqrt N) * (Real.sqrt (2 * R.D.invβ) * Real.sqrt (2 * R.D.invβ)) / ((N : ℝ) * N) *
          ((Torus.grad (obsTest R.D R.ρ t φ i s) (X s.toNNReal ω p)) a *
            (Torus.grad (obsTest R.D R.ρ t φ j s) (X s.toNNReal ω p)) a) := by ring
      _ = _ := by rw [hsqN, hsqb]; field_simp
  rw [hL, hrate, heval, hpe, hpd]
  field_simp
  ring

end HRS.MC.Sec7.S7PIF1

end

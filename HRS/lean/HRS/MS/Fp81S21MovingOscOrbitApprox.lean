import HRS.MS.Fp81S21MovingEncodedOrbit
import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.ProClosureS111OscOrbitApprox

/-!
# S2.1(iii): oscillator approximation for the moving propagator

The moving standard-data radius precedes the trajectory and shifted horizon.
On each such horizon the square-summable mode envelope gives one constant
for all oscillator tests and both propagation times. Applying that bound to
the terminal Hermite-section error yields the full K4 approximation contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3
open HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111K4AT

/-- One radius supplies the all-oscillator-test K4 approximation for the
actual moving coefficient on every shifted horizon. The Hermite section is
applied to the terminal datum before propagation. -/
theorem fp81s21_moving_osc_orbit_approx (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ a : ℝ, 0 ≤ a →
        HRS.MS.S111K4AT.K4OscOrbitApprox
          (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (2 * p.d + 8) := by
  obtain ⟨δ₀, hδ₀, hδ₀half, hstdAll⟩ := fp81s21_moving_std p
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R a ha
  have hH : 0 < a + p.T := by linarith [p.hT]
  obtain ⟨c, hstd⟩ := hstdAll δ hδ hδle R a ha
  let K : ℝ := Real.sqrt (∑' α, c α ^ 2)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  -- Coordinate partial derivatives are bounded by multilinear operator norms.
  -- No summation over derivative orders (and hence no enlarged constant) is needed.
  have hbd : ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      ∀ v ∈ Icc (0 : ℝ) (a + p.T), ∀ t ∈ Icc v (a + p.T),
        weightedSupE (2 * p.d + 8 + 1) 0
          (propagatorW (r26t3_coeff R) v t φ) ≤
            ENNReal.ofReal (K * oscNorm (wholeSpaceIndex p.d : ℝ) φ) := by
    intro φ hφ v hv t ht
    have hjet := (fp81s21_moving_orbit_jet_bound p R hH hstd hφ hv ht).2
    unfold weightedSupE derivSupE
    refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
    simp only [Real.rpow_zero, one_mul]
    apply ENNReal.ofReal_le_ofReal
    have hj : (j : ℕ) ≤ 2 * p.d + 9 := by
      have := Nat.lt_succ_iff.1 j.2
      omega
    calc
      |partialDeriv i (propagatorW (r26t3_coeff R) v t φ) x| ≤
          ‖iteratedFDeriv ℝ (j : ℕ)
            (propagatorW (r26t3_coeff R) v t φ) x‖ :=
        HRS.MS.Lc.lc4_partial_le (j : ℕ) i x
      _ ≤ oscNorm (wholeSpaceIndex p.d : ℝ) φ * K := hjet j hj x
      _ = K * oscNorm (wholeSpaceIndex p.d : ℝ) φ := mul_comm _ _
  refine ⟨?_, ?_, ⟨K, hK, hbd⟩, ?_⟩
  · intro φ hφ t ht
    exact ⟨_, fp81s21_U_osc_test_classical p R hφ ht.1⟩
  · intro φ hφ v hv t ht
    exact (fp81s21_moving_orbit_jet_bound p R hH hstd hφ hv ht).1.1
  · intro φ hφ
    let ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ) := ⟨φ, hφ⟩
    let ψn : ℕ → oscSub p.d (wholeSpaceIndex p.d : ℝ) :=
      fun n => initialTestSection ψ n
    -- The available tail theorem uses the opposite subtraction order.
    have hnorm : ∀ n,
        oscNorm (wholeSpaceIndex p.d : ℝ)
          ((ψn n - ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ)) : Euc p.d → ℝ) =
        oscNorm (wholeSpaceIndex p.d : ℝ)
          ((ψ - ψn n : oscSub p.d (wholeSpaceIndex p.d : ℝ)) : Euc p.d → ℝ) := by
      intro n
      rw [← OscSpace.norm_ofFun _ (ψn n - ψ).property.2,
        ← OscSpace.norm_ofFun _ (ψ - ψn n).property.2,
        initialTest_ofFun_sub, initialTest_ofFun_sub, norm_sub_rev]
    have hlim : Tendsto (fun n => ENNReal.ofReal (K *
        oscNorm (wholeSpaceIndex p.d : ℝ)
          ((ψn n - ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ)) : Euc p.d → ℝ)))
        atTop (𝓝 0) := by
      have ht := (initialTestSection_tail ψ).const_mul K
      have he := ENNReal.tendsto_ofReal ht
      simpa only [hnorm, mul_zero, ENNReal.ofReal_zero] using he
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hlim (fun _ => bot_le)
    intro n
    refine iSup_le fun v => iSup_le fun hv => iSup_le fun t => iSup_le fun ht => ?_
    -- Linearity identifies the propagated terminal error with the orbit difference.
    have hp : propagatorW (r26t3_coeff R) v t
        ((ψn n - ψ : oscSub p.d (wholeSpaceIndex p.d : ℝ)) : Euc p.d → ℝ) =
        propagatorW (r26t3_coeff R) v t (ψn n : Euc p.d → ℝ) -
          propagatorW (r26t3_coeff R) v t φ := by
      change propagatorW (r26t3_coeff R) v t
          (fun x => (ψn n : Euc p.d → ℝ) x - φ x) =
        (fun x => propagatorW (r26t3_coeff R) v t (ψn n : Euc p.d → ℝ) x -
          propagatorW (r26t3_coeff R) v t φ x)
      have hh := fp81s21_U_linear_of_osc_test p R (ψn n).property hφ (-1)
        (hv.1.trans ht.1) ⟨hv.1, ht.1⟩
      simpa only [r26t3_U, neg_one_mul, sub_eq_add_neg] using hh
    have hsec : k4hs (wholeSpaceIndex p.d : ℝ) n φ = (ψn n : Euc p.d → ℝ) :=
      hermiteSection_eq_initialTestSection _ n ψ
    rw [hsec, ← hp]
    exact hbd _ (ψn n - ψ).property v hv t ht

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_moving_osc_orbit_approx

end

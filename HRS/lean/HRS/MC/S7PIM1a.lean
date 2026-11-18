import HRS.MC.S7FCW7Aux
import HRS.MC.S7FCW12E
import HRS.MD.EQInterpHolder

/-!
# Packet piM, part M1a: deterministic bounds on the coefficients of the quadratic field `ℬ̃_N` (prefix `S7PIM_`)

For every configuration `X` of `N ≥ 1` particles and every `t ≥ 0`, the coefficients
`c_k = N F_N^{h_{e_k}}(X, μ_t)` of `quadFieldTilde` satisfy `|c_k| ≤ A ⟨k⟩²`, where for `N = 1` the constant `A` does
not depend on `X` (the pair sum is empty).  Consequences: `quadFieldTilde r` is the honest weighted sequence for
`r > d/2 + 2`, `quadFieldTilde m = embed (quadFieldTilde r)`, and for `N = 1` the field is bounded in `E_m`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

/-- The envelope of the transport kernel of a mode with the explicit `⟨k⟩²` growth. -/
theorem S7PIM_env (R : Regime d) :
    ∃ K1 c : ℝ, 0 ≤ K1 ∧ (∀ z : Torus d, 0 ≤ periodicRiesz d R.D.s z + c) ∧
      ∀ (k : NonzeroLattice d) (x y : Torus d),
        |hTransport d R.D.s (Torus.realMode k) x y| ≤
          K1 * Lattice.jp k.1 ^ 2 * (periodicRiesz d R.D.s (x - y) + c) := by
  obtain ⟨K, c, hK0, hc0, hwc, henv⟩ := HRS.MC.Sec7.S7b.s7b_envelope R.hd R.D.hs0 R.hs
  have hgc : ∀ z : Torus d, 0 ≤ periodicRiesz d R.D.s z + c := by
    intro z
    by_cases hz : z = 0
    · subst hz; exact hc0
    · linarith [hwc z hz]
  refine ⟨K * d * (3 * Real.sqrt 2) + 1, c, ?_, hgc, fun k x y => ?_⟩
  · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  · exact HRS.MC.Sec7.S7FCW3.s7fcw3_hT_env hK0 k henv x y (hgc _)

/-- The mean of the transport kernel of a mode against `μ_t`, `t ≥ 0`: `|∫ h_{e_k}(x,y) dμ_t(y)| ≤ K2 ⟨k⟩²`. -/
theorem S7PIM_mean (R : Regime d) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ t : ℝ, 0 ≤ t → ∀ (k : NonzeroLattice d) (x : Torus d),
      |∫ y, hTransport d R.D.s (Torus.realMode k) x y ∂(withDensityReal (R.ρ t))| ≤
        K2 * Lattice.jp k.1 ^ 2 := by
  obtain ⟨K1, c, hK1, hgc, henv⟩ := S7PIM_env R
  obtain ⟨m0, M0, hm0, hb⟩ := R.bounds
  have hsd : R.D.s < (d : ℝ) := HRS.MC.Sec7.S7FCW7.s7fcw7_sd R.hd R.hs
  have hgI : Integrable (fun z : Torus d => periodicRiesz d R.D.s z + c) :=
    (HRS.KernelAux.integrable_periodicRiesz R.hd R.D.hs0 hsd).add (integrable_const c)
  have hM0 : 0 ≤ M0 := (hm0.le.trans (hb 0 le_rfl 0).1).trans (hb 0 le_rfl 0).2
  have hI0 : 0 ≤ ∫ z : Torus d, (periodicRiesz d R.D.s z + c) := integral_nonneg hgc
  refine ⟨M0 * K1 * ∫ z : Torus d, (periodicRiesz d R.D.s z + c), by positivity, fun t ht k x => ?_⟩
  have hρ : IsProbDensity (R.ρ t) := (R.mf (t + 1) (by linarith)).density t ⟨ht, by linarith⟩
  have hρM : ∀ y, R.ρ t y ≤ M0 := fun y => (hb t ht y).2
  have hj : 0 ≤ Lattice.jp k.1 ^ 2 := sq_nonneg _
  rw [HRS.PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
  have hint : Integrable (fun y : Torus d => M0 * (K1 * Lattice.jp k.1 ^ 2 *
      (periodicRiesz d R.D.s (x - y) + c))) :=
    (hgI.comp_sub_left x).const_mul _ |>.const_mul _
  calc |∫ y, R.ρ t y * hTransport d R.D.s (Torus.realMode k) x y|
      = ‖∫ y, R.ρ t y * hTransport d R.D.s (Torus.realMode k) x y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, M0 * (K1 * Lattice.jp k.1 ^ 2 * (periodicRiesz d R.D.s (x - y) + c)) := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
        exact mul_le_mul (hρM y) (henv k x y) (abs_nonneg _) hM0
    _ = M0 * K1 * (∫ z : Torus d, (periodicRiesz d R.D.s z + c)) * Lattice.jp k.1 ^ 2 := by
        rw [integral_const_mul, integral_const_mul,
          integral_sub_left_eq_self (fun z : Torus d => periodicRiesz d R.D.s z + c) volume x]
        ring

/-- The explicit bound for the coefficients `c_k = N F_N^{h_{e_k}}(X, μ_t)` of the quadratic field. -/
theorem S7PIM_coeff_bound (R : Regime d) :
    ∃ K1 K2 c : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ t : ℝ, 0 ≤ t → ∀ {N : ℕ}, 0 < N → ∀ (X : Config d N)
      (k : NonzeroLattice d),
      |(N : ℝ) * modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) X (withDensityReal (R.ρ t))| ≤
        Lattice.jp k.1 ^ 2 * (K1 / (2 * N) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c) + 3 / 2 * N * K2) := by
  obtain ⟨K1, c, hK1, hgc, henv⟩ := S7PIM_env R
  obtain ⟨K2, hK2, hmean⟩ := S7PIM_mean R
  refine ⟨K1, K2, c, hK1, hK2, fun t ht N hN X k => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : IsProbDensity (R.ρ t) := (R.mf (t + 1) (by linarith)).density t ⟨ht, by linarith⟩
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ t)) := HRS.isProb_withDensityReal hρ
  set h := hTransport d R.D.s (Torus.realMode k) with hh
  set μ := withDensityReal (R.ρ t) with hμ
  set j2 := Lattice.jp k.1 ^ 2 with hj2
  have hj0 : 0 ≤ j2 := sq_nonneg _
  -- the three pieces
  have hS : |∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| ≤
      j2 * (K1 * ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c)) := by
    calc _ ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, h (X i) (X j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |h (X i) (X j)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (K1 * j2 * (periodicRiesz d R.D.s (X i - X j) + c)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => henv k (X i) (X j)
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have hI : |∑ i, ∫ y, h (X i) y ∂μ| ≤ N * (K2 * j2) := by
    calc _ ≤ ∑ i, |∫ y, h (X i) y ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, K2 * j2 := Finset.sum_le_sum fun i _ => hmean t ht k (X i)
      _ = N * (K2 * j2) := by simp
  have hJ : |∫ x, ∫ y, h x y ∂μ ∂μ| ≤ K2 * j2 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := K2 * j2)
      (f := fun x => ∫ y, h x y ∂μ) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hmean t ht k x)
    simpa [Real.norm_eq_abs] using this
  have heq : (N : ℝ) * modulatedEnergy h X μ =
      (1 / (2 * (N : ℝ))) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
        - ∑ i, ∫ y, h (X i) y ∂μ + ((N : ℝ) / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ := by
    unfold modulatedEnergy
    field_simp
  rw [heq]
  have hG0 : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hgc _
  have e1 : |(1 / (2 * (N : ℝ))) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| ≤
      j2 * (K1 / (2 * N) * ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc _ ≤ 1 / (2 * (N : ℝ)) * (j2 * (K1 * ∑ i, ∑ j ∈ Finset.univ.erase i,
          (periodicRiesz d R.D.s (X i - X j) + c))) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by ring
  have e3 : |((N : ℝ) / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ| ≤ (N : ℝ) / 2 * (K2 * j2) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hJ (by positivity)
  calc _ ≤ |(1 / (2 * (N : ℝ))) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) -
          ∑ i, ∫ y, h (X i) y ∂μ| + |((N : ℝ) / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ| := abs_add_le _ _
    _ ≤ (|(1 / (2 * (N : ℝ))) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| +
          |∑ i, ∫ y, h (X i) y ∂μ|) + |((N : ℝ) / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ (j2 * (K1 / (2 * N) * ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d R.D.s (X i - X j) + c)) +
          N * (K2 * j2)) + (N : ℝ) / 2 * (K2 * j2) := add_le_add (add_le_add e1 hI) e3
    _ = _ := by ring

end HRS.MC.Sec7.S7PIM

end

import HRS.MC.E213U18a
import HRS.Sections.Q38bAux1
import HRS.Equilibrium.LocalDivSub

/-!
# Packet e213u18 (part b): Fourier expansion of the gradient on the torus

For a smooth `φ`, `∇φ = ∑_k φ̂_k ∇e_k` (absolutely, uniformly in `x`), with `‖∇e_k‖ ≤ √2 ⟨k⟩`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS

variable {d : ℕ}

theorem u18_two_pi_enorm_le_jp (k : Lattice d) : 2 * Real.pi * Lattice.enorm k ≤ Lattice.jp k := by
  unfold Lattice.jp
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (Lattice.enorm k)]

open Classical in
/-- The Fréchet derivative of the lifted real mode. -/
theorem u18_fderiv_lift_realMode (k : NonzeroLattice d) (y : Euc d) :
    HasFDerivAt (Torus.lift (Torus.realMode k))
      (if Lattice.IsPosHalf k.1 then Real.sqrt 2 • (-Real.sin (Torus.freqFunctional k.1 y) • Torus.freqFunctional k.1)
        else Real.sqrt 2 • (Real.cos (Torus.freqFunctional k.1 y) • Torus.freqFunctional k.1)) y := by
  by_cases hp : Lattice.IsPosHalf k.1
  · have hl : Torus.lift (Torus.realMode k) =
        fun z => Real.sqrt 2 * Real.cos (Torus.freqFunctional k.1 z) := by
      funext z
      simp [Torus.lift, Torus.realMode, hp, Torus.cosMode_mk, Torus.freqFunctional_apply]
    rw [hl, if_pos hp]
    exact (((Torus.freqFunctional k.1).hasFDerivAt (x := y)).cos).const_mul (Real.sqrt 2)
  · have hl : Torus.lift (Torus.realMode k) =
        fun z => Real.sqrt 2 * Real.sin (Torus.freqFunctional k.1 z) := by
      funext z
      simp [Torus.lift, Torus.realMode, hp, Torus.sinMode_mk, Torus.freqFunctional_apply]
    rw [hl, if_neg hp]
    exact (((Torus.freqFunctional k.1).hasFDerivAt (x := y)).sin).const_mul (Real.sqrt 2)

theorem u18_norm_fderiv_lift_realMode (k : NonzeroLattice d) (y : Euc d) :
    ‖fderiv ℝ (Torus.lift (Torus.realMode k)) y‖ ≤ Real.sqrt 2 * Lattice.jp k.1 := by
  classical
  rw [(u18_fderiv_lift_realMode k y).fderiv]
  have hF : ‖Torus.freqFunctional k.1‖ ≤ Lattice.jp k.1 :=
    (Torus.norm_freqFunctional_le k.1).trans (u18_two_pi_enorm_le_jp k.1)
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  split_ifs
  · rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |Real.sqrt 2| * (|Real.sin (Torus.freqFunctional k.1 y)| * ‖Torus.freqFunctional k.1‖)
        ≤ Real.sqrt 2 * (1 * Lattice.jp k.1) := by
          rw [abs_of_nonneg h2]
          gcongr
          exact Real.abs_sin_le_one _
      _ = _ := by ring
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |Real.sqrt 2| * (|Real.cos (Torus.freqFunctional k.1 y)| * ‖Torus.freqFunctional k.1‖)
        ≤ Real.sqrt 2 * (1 * Lattice.jp k.1) := by
          rw [abs_of_nonneg h2]
          gcongr
          exact Real.abs_cos_le_one _
      _ = _ := by ring


theorem u18_summable_weighted {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (N : ℕ) :
    Summable fun k : NonzeroLattice d => |Torus.funRealCoeff φ k| * Lattice.jp k.1 ^ N := by
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n => (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).of_le (by exact_mod_cast le_top)
  have hcont : Continuous φ := by
    have := (hd 0).continuous
    exact (KernelGrad.isOpenQuotientMap_mk (d := d)).continuous_comp_iff.mp this
  have hint : Integrable φ := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (hd (N + (d + 1)))
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2)
    (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (Torus.jp_pos k.1).le N)) (fun k => ?_) (hs.mul_left (Real.sqrt 2 * B))
  have hj := Torus.jp_pos k.1
  have e : Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) / 2))) = (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
      Real.rpow_natCast]
  rw [e]
  have h1 := Torus.abs_funRealCoeff_le hint k
  have h2 := hB k
  rw [pow_add] at h2
  have h3 : |Torus.funRealCoeff φ k| * Lattice.jp k.1 ^ N ≤
      Real.sqrt 2 * ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ N := by gcongr
  refine h3.trans ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hj _)]
  have h4 : ‖Torus.fcoef φ k.1‖ * (Lattice.jp k.1 ^ N * Lattice.jp k.1 ^ (d + 1)) ≤ B := by
    simpa [mul_assoc] using h2
  calc Real.sqrt 2 * ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ N * Lattice.jp k.1 ^ (d + 1)
      = Real.sqrt 2 * (‖Torus.fcoef φ k.1‖ * (Lattice.jp k.1 ^ N * Lattice.jp k.1 ^ (d + 1))) := by ring
    _ ≤ Real.sqrt 2 * B := by gcongr
    _ = _ := by ring


theorem u18_hasSum_fderiv {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (y : Euc d) :
    HasSum (fun k : NonzeroLattice d =>
      Torus.funRealCoeff φ k • fderiv ℝ (Torus.lift (Torus.realMode k)) y) (fderiv ℝ (Torus.lift φ) y) := by
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n =>
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).of_le (by exact_mod_cast le_top)
  have hcont : Continuous φ :=
    (KernelGrad.isOpenQuotientMap_mk (d := d)).continuous_comp_iff.mp (hd 0).continuous
  have hs := Torus.summable_fcoef_of_contDiff hd
  have hsum1 := u18_summable_weighted hφ 1
  have hu : Summable fun k : NonzeroLattice d => |Torus.funRealCoeff φ k| * (Real.sqrt 2 * Lattice.jp k.1) := by
    refine (hsum1.mul_left (Real.sqrt 2)).congr fun k => ?_
    ring
  have hdiff : ∀ k : NonzeroLattice d, ∀ x : Euc d, DifferentiableAt ℝ (Torus.lift (Torus.realMode k)) x :=
    fun k x => (u18_fderiv_lift_realMode k x).differentiableAt
  have hf : ∀ (k : NonzeroLattice d) (x : Euc d),
      HasFDerivAt (fun z => Torus.funRealCoeff φ k * Torus.lift (Torus.realMode k) z)
        (Torus.funRealCoeff φ k • fderiv ℝ (Torus.lift (Torus.realMode k)) x) x :=
    fun k x => (hdiff k x).hasFDerivAt.const_mul _
  have hf' : ∀ (k : NonzeroLattice d) (x : Euc d),
      ‖Torus.funRealCoeff φ k • fderiv ℝ (Torus.lift (Torus.realMode k)) x‖ ≤
        |Torus.funRealCoeff φ k| * (Real.sqrt 2 * Lattice.jp k.1) := by
    intro k x
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (u18_norm_fderiv_lift_realMode k x) (abs_nonneg _)
  have hexp : ∀ z : Euc d, HasSum (fun k : NonzeroLattice d =>
      Torus.funRealCoeff φ k * Torus.lift (Torus.realMode k) z) (Torus.lift φ z - Torus.mean φ) :=
    fun z => Torus.hasSum_realExpansion hcont hs (Torus.mk z)
  have hf0 : Summable fun k : NonzeroLattice d => Torus.funRealCoeff φ k * Torus.lift (Torus.realMode k) y :=
    (hexp y).summable
  have h1 := hasFDerivAt_tsum hu hf hf' hf0 y
  have e1 : (fun z => ∑' k : NonzeroLattice d, Torus.funRealCoeff φ k * Torus.lift (Torus.realMode k) z) =
      fun z => Torus.lift φ z - Torus.mean φ := funext fun z => (hexp z).tsum_eq
  rw [e1] at h1
  have h2 : HasFDerivAt (fun z => Torus.lift φ z - Torus.mean φ) (fderiv ℝ (Torus.lift φ) y) y :=
    ((hd 1).differentiable (by norm_num) y).hasFDerivAt.sub_const _
  have h3 := h1.unique h2
  have hsm : Summable fun k : NonzeroLattice d =>
      Torus.funRealCoeff φ k • fderiv ℝ (Torus.lift (Torus.realMode k)) y :=
    Summable.of_norm_bounded hu (fun k => hf' k y)
  rw [← h3]
  exact hsm.hasSum

/-- `∇φ = ∑_k φ̂_k ∇e_k` pointwise. -/
theorem u18_hasSum_grad {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (x : Torus d) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff φ k • Torus.grad (Torus.realMode k) x)
      (Torus.grad φ x) := by
  have h := u18_hasSum_fderiv hφ (Torus.rep x)
  have hL := ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.toContinuousLinearMap).hasSum h
  simpa [Torus.grad, gradient, map_smul] using hL

end HRS.MC.E213U18

end

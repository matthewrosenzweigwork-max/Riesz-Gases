import HRS.Main.T25PAux9

/-!
# T25P, part 10: the finite-dimensional laws of the linear process `Y` and of `V(·,0) X₀' + Z̄` agree (port of `GFB4Aux8/9`)

The propagated test functions `U^{σ,t}φ` lie in `H^m` because the dual evolution is bounded on `E_m`
(`t25p_memSobolev_of_dual`: a bounded functional on `E_m` is represented by an `H^m` function), which replaces
`GFEvo.adjoint`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- A continuous function whose pairing with `E_m` is a bounded functional is in `H^m`. -/
theorem t25p_memSobolev_of_dual {m : ℝ} {ψ : Torus d → ℝ} (hψc : Continuous ψ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z : NegSobolev d m, |NegSobolev.eval z ψ| ≤ B * ‖z‖) : MemSobolev m ψ := by
  classical
  refine ⟨PDE.ClassicalAux.memLp_two_of_continuous hψc, ?_⟩
  set c : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff ψ k with hc
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (2 * m) * c k ^ 2 := fun k =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  refine summable_of_sum_le (c := B ^ 2) hnn fun F => ?_
  set zF : NegSobolev d m := ∑ k ∈ F, (Lattice.jp k.1 ^ (2 * m) * c k) • adjkdEps m k with hzF
  have hcoeff : ∀ l : NonzeroLattice d, NegSobolev.fourierCoeff zF l =
      if l ∈ F then Lattice.jp l.1 ^ (2 * m) * c l else 0 := by
    intro l
    rw [← adjkdCoord_apply, hzF, map_sum]
    simp only [map_smul, adjkdCoord_apply, adjkdEps_fourier, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq F l]
  set S : ℝ := ∑ k ∈ F, Lattice.jp k.1 ^ (2 * m) * c k ^ 2 with hS
  have hev : NegSobolev.eval zF ψ = S := by
    unfold NegSobolev.eval
    rw [tsum_eq_sum (s := F)]
    · refine Finset.sum_congr rfl fun l hl => ?_
      rw [hcoeff l, if_pos hl]
      simp only [hc]
      ring
    · intro l hl
      rw [hcoeff l, if_neg hl, zero_mul]
  have hnorm : ‖zF‖ ^ 2 = S := by
    obtain ⟨-, hGn⟩ := NegSobolev.coord_sq zF
    rw [hGn, tsum_eq_sum (s := F)]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have h1 : NegSobolev.coord zF l = Lattice.jp l.1 ^ (-m) * NegSobolev.fourierCoeff zF l := by
        unfold NegSobolev.fourierCoeff
        rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
        simp
      rw [h1, hcoeff l, if_pos hl, mul_pow, Torus.jp_rpow_sq]
      have hx := Torus.jp_pos l.1
      have h2 : (Lattice.jp l.1 ^ (2 * m)) ^ 2 * Lattice.jp l.1 ^ (-(2 * m)) = Lattice.jp l.1 ^ (2 * m) := by
        rw [sq, mul_assoc, ← Real.rpow_add hx]; simp
      have e1 : (2 * -m) = -(2 * m) := by ring
      rw [e1]
      calc Lattice.jp l.1 ^ (-(2 * m)) * (Lattice.jp l.1 ^ (2 * m) * c l) ^ 2
          = ((Lattice.jp l.1 ^ (2 * m)) ^ 2 * Lattice.jp l.1 ^ (-(2 * m))) * c l ^ 2 := by ring
        _ = _ := by rw [h2]
    · intro l hl
      have h1 : NegSobolev.coord zF l = Lattice.jp l.1 ^ (-m) * NegSobolev.fourierCoeff zF l := by
        unfold NegSobolev.fourierCoeff
        rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
        simp
      rw [h1, hcoeff l, if_neg hl]
      simp
  have hS0 : 0 ≤ S := by rw [← hnorm]; positivity
  have hle : S ≤ B * ‖zF‖ := by
    have := hB zF
    rw [hev, abs_of_nonneg hS0] at this
    exact this
  by_contra hcon
  push Not at hcon
  have hr : B < ‖zF‖ := by
    by_contra h'
    push Not at h'
    have : S ≤ B ^ 2 := by
      calc S = ‖zF‖ ^ 2 := hnorm.symm
        _ ≤ B ^ 2 := by gcongr
    linarith
  nlinarith [norm_nonneg zF, hnorm]

/-- `U^{r,t}φ ∈ H^m` for smooth `φ`, from the boundedness of the dual evolution on `E_m`. -/
theorem t25p_memSobolev_propagator (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (hKb : ‖Vev t r‖ ≤ K)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : MemSobolev m (propagator htr.dyn ρ r t φ) := by
  have hφm : MemSobolev m φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  have hck : Torus.IsCk 2 (propagator htr.dyn ρ r t φ) := adjkd_propagator_ck2 htr.dyn ρ hr hrt φ
  have hcont : Continuous (propagator htr.dyn ρ r t φ) :=
    Torus.continuous_of_continuous_lift hck.continuous
  refine t25p_memSobolev_of_dual hcont (B := K * ‖lpFun m φ‖) (by positivity) fun z => ?_
  rw [← hdual r t hr hrt z φ hφ, eval_lpFun _ hφm]
  calc |inner ℝ (Vev t r z) (lpFun m φ)| ≤ ‖Vev t r z‖ * ‖lpFun m φ‖ := abs_real_inner_le_norm _ _
    _ ≤ (K * ‖z‖) * ‖lpFun m φ‖ := by
        gcongr
        exact ((Vev t r).le_opNorm z).trans (mul_le_mul_of_nonneg_right hKb (norm_nonneg _))
    _ = K * ‖lpFun m φ‖ * ‖z‖ := by ring

end HRS.T25P

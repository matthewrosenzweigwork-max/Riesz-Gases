import HRS.Sections.AdjKGlueAux12

/-!
# ADJK-GLUE, part 13: regularity of `U^{0,t}φ`, the pairing functional, and the `linCoord` identification
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_isSmooth_integrable {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Integrable φ := by
  have hc : Continuous φ :=
    Torus.continuous_of_continuous_lift ((adjkd_isCk_of_smooth 0 hφ).continuous)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem adjkg_smooth_weighted_summable {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (M : ℕ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ M * |Torus.funRealCoeff φ k| := by
  have hint := adjkg_isSmooth_integrable hφ
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (φ := φ) (n := M + (d + 1))
    (adjkd_isCk_of_smooth (M + (d + 1)) hφ)
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2)
    (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _))
    (fun k => ?_) ((hs.mul_left (Real.sqrt 2 * B)))
  have hj := Torus.jp_pos k.1
  have e : Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) / 2))) = (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
      Real.rpow_natCast]
  rw [e]
  have h1 := hB k
  have h2 := Torus.abs_funRealCoeff_le hint k
  have h3 : ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ M * Lattice.jp k.1 ^ (d + 1) ≤ B := by
    calc _ = ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ (M + (d + 1)) := by rw [pow_add]; ring
      _ ≤ B := h1
  have hp : 0 < Lattice.jp k.1 ^ (d + 1) := pow_pos hj _
  have h4 : ‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ M ≤ B * (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    exact h3
  calc Lattice.jp k.1 ^ M * |Torus.funRealCoeff φ k|
      ≤ Lattice.jp k.1 ^ M * (Real.sqrt 2 * ‖Torus.fcoef φ k.1‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.sqrt 2 * (‖Torus.fcoef φ k.1‖ * Lattice.jp k.1 ^ M) := by ring
    _ ≤ Real.sqrt 2 * (B * (Lattice.jp k.1 ^ (d + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * B * (Lattice.jp k.1 ^ (d + 1))⁻¹ := by ring

/-- Polynomial decay of the Fourier coefficients of `U^{0,t}φ` for smooth `φ`. -/
theorem adjkg_prop_coeff_decay (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {t : ℝ}
    (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (M : ℕ) :
    ∃ B : ℝ, ∀ j : NonzeroLattice d,
      |Torus.funRealCoeff (propagator htr.dyn ρ 0 t φ) j| ≤ B * Lattice.jp j.1 ^ (-(M : ℝ)) := by
  obtain ⟨C, c, hC, hc, Vev, hdual, -, hdec, -⟩ := adjk_evolution_along_trajectory hd htr (M : ℝ)
  have hV : ‖Vev t 0‖ ≤ C := by
    refine (hdec 0 t le_rfl ht).trans ?_
    have : Real.exp (-c * (t - 0)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hS := adjkg_smooth_weighted_summable hφ M
  set S : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ M * |Torus.funRealCoeff φ k| with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun k =>
    mul_nonneg (pow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _)
  refine ⟨C * S, fun j => ?_⟩
  set F : NegSobolev d (M : ℝ) := Vev t 0 (adjkdEps (M : ℝ) j) with hF
  have e1 : Torus.funRealCoeff (propagator htr.dyn ρ 0 t φ) j = NegSobolev.eval F φ := by
    rw [hF, hdual 0 t le_rfl ht _ φ hφ]
    unfold NegSobolev.eval
    rw [tsum_eq_single j]
    · rw [adjkdEps_fourier]; simp
    · intro i hi
      rw [adjkdEps_fourier, if_neg hi, zero_mul]
  have hFn : ‖F‖ ≤ C * Lattice.jp j.1 ^ (-(M : ℝ)) := by
    calc ‖F‖ ≤ ‖Vev t 0‖ * ‖adjkdEps (M : ℝ) j‖ := (Vev t 0).le_opNorm _
      _ ≤ C * Lattice.jp j.1 ^ (-(M : ℝ)) := by
        rw [adjkdEps_norm]
        exact mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hbd : ∀ k : NonzeroLattice d, ‖NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k‖ ≤
      ‖F‖ * (Lattice.jp k.1 ^ M * |Torus.funRealCoeff φ k|) := by
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    have := adjkd_abs_fourierCoeff_le (M : ℝ) k F
    rw [Real.rpow_natCast] at this
    calc |NegSobolev.fourierCoeff F k| * |Torus.funRealCoeff φ k|
        ≤ (Lattice.jp k.1 ^ M * ‖F‖) * |Torus.funRealCoeff φ k| :=
          mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = ‖F‖ * (Lattice.jp k.1 ^ M * |Torus.funRealCoeff φ k|) := by ring
  have h2 : ‖NegSobolev.eval F φ‖ ≤ ‖F‖ * S := by
    unfold NegSobolev.eval
    exact tsum_of_norm_bounded (hS.hasSum.mul_left ‖F‖) hbd
  rw [e1]
  calc |NegSobolev.eval F φ| = ‖NegSobolev.eval F φ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖F‖ * S := h2
    _ ≤ (C * Lattice.jp j.1 ^ (-(M : ℝ))) * S := mul_le_mul_of_nonneg_right hFn hS0
    _ = C * S * Lattice.jp j.1 ^ (-(M : ℝ)) := by ring

theorem adjkg_prop_sobolev (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {t : ℝ}
    (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (m' : ℝ) :
    Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * m') *
      Torus.funRealCoeff (propagator htr.dyn ρ 0 t φ) j ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, m' + (d : ℝ) + 1 ≤ M := ⟨⌈m' + d + 1⌉₊, Nat.le_ceil _⟩
  obtain ⟨B, hB⟩ := adjkg_prop_coeff_decay hd htr ht hφ M
  refine adjkd_sobolev_summable (m := (M : ℝ)) (m' := m') ?_ _ hB
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem adjkg_prop_fcoef_summable (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {t : ℝ}
    (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous (propagator htr.dyn ρ 0 t φ) ∧
      Summable fun k : Lattice d => ‖Torus.fcoef (propagator htr.dyn ρ 0 t φ) k‖ := by
  have hck : Torus.IsCk 2 (propagator htr.dyn ρ 0 t φ) := adjkd_propagator_ck2 htr.dyn ρ le_rfl ht φ
  have hc : Continuous (propagator htr.dyn ρ 0 t φ) :=
    Torus.continuous_of_continuous_lift (hck.continuous)
  refine ⟨hc, ?_⟩
  have hint : Integrable (propagator htr.dyn ρ 0 t φ) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := adjkg_prop_sobolev hd htr ht hφ (d : ℝ)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have := (Torus.sobolev_coeff_bound (d := d) (m := (d : ℝ)) (i := 0) (by push_cast; linarith) hint hs).1
  simpa using this

theorem adjkg_coord_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl

theorem adjkg_fourier_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  rw [adjkg_coord_smul]
  ring

theorem adjkg_eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (f : Torus d → ℝ) :
    NegSobolev.eval (c • F) f = c * NegSobolev.eval F f := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by rw [adjkg_fourier_smul]; ring

/-- The pairing with a fixed function of finite Sobolev norm is continuous on `E_m`. -/
theorem adjkg_eval_continuous {m : ℝ} {f : Torus d → ℝ}
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2) :
    Continuous fun F : NegSobolev d m => NegSobolev.eval F f := by
  set y : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff f k with hy
  have hy2 : Summable fun k => y k ^ 2 := by
    refine hs.congr fun k => ?_
    simp only [hy]; rw [mul_pow, Torus.jp_rpow_sq]
  have hsum : ∀ F : NegSobolev d m, Summable fun k => NegSobolev.fourierCoeff F k * Torus.funRealCoeff f k := by
    intro F
    obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
    have hcs := Torus.cs_tsum (fun k => |NegSobolev.coord F k|) (fun k => |y k|) (fun _ => abs_nonneg _)
      (fun _ => abs_nonneg _) (by simpa [sq_abs] using hF2) (by simpa [sq_abs] using hy2)
    have : Summable fun k => NegSobolev.coord F k * y k := by
      refine Summable.of_norm ?_
      simpa [abs_mul] using hcs.1
    refine this.congr fun k => ?_
    simp only [hy, NegSobolev.fourierCoeff]; ring
  let ℓ : NegSobolev d m →ₗ[ℝ] ℝ :=
    { toFun := fun F => NegSobolev.eval F f
      map_add' := fun F G => by
        show NegSobolev.eval (F + G) f = NegSobolev.eval F f + NegSobolev.eval G f
        unfold NegSobolev.eval
        rw [← (hsum F).tsum_add (hsum G)]
        exact tsum_congr fun k => by rw [adjkg_fourier_add]; ring
      map_smul' := fun c F => by
        show NegSobolev.eval (c • F) f = c * NegSobolev.eval F f
        exact adjkg_eval_smul c F f }
  have hbound : ∀ F : NegSobolev d m, ‖ℓ F‖ ≤
      Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2) * ‖F‖ := by
    intro F
    rw [Real.norm_eq_abs, mul_comm]
    exact NegSobolev.abs_eval_le F f hs
  exact (LinearMap.mkContinuous ℓ _ hbound).continuous

theorem adjkg_linCoord_eq_eval {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 0 < N)
    {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ} (hc : Continuous f)
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef f k‖) (X : Config d N) :
    linCoord μ f X = NegSobolev.eval (etaE m X μ) f := by
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN X
  unfold etaE flucE
  rw [adjkg_eval_smul, NegSobolev.eval_ofMeasureDiff_of_summable hm _ _ f hc hs, pair_empirical hN X f]
  unfold linCoord
  rw [one_div]

end HRS.AdjK

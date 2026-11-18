import HRS.Main.ThermLinPlan2
import HRS.Main.ThermLin2Mo2
import HRS.Main.ThermLin2Mo4

/-!
# THERMLIN2 Mo5: helper lemmas for `tl2_Zw_moment` (C1)

* `tl2Mo5_gradSq_le`: `∫|∇ψ|² ≤ ‖lpFun 1 ψ‖²` (Parseval on the torus through the diagonal form `covForm m (1/2) vol`).
* `tl2Mo5_cov_diag`: `covDensT` of the pulled-back `W`-vectors along the actual path `S.ρ`
  (the variant of `t25p_cov_eq` with two different trajectories: `S.ρ` for the noise, the constant path for `W`).
* `tl2Mo5_lp1_bound`: operator bound for the frozen propagator on `H^1` from the level-1 dual evolution.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q48c

variable {d : ℕ}

/-- Parseval: `∫|∇ψ|² ≤ ‖ψ‖²_{H¹}`. -/
theorem tl2Mo5_gradSq_le {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {ψ : Torus d → ℝ} (h₁ : MemSobolev m ψ)
    (c₁ : Continuous ψ) (d₁ : Torus.IsCk 1 ψ) (h1 : MemSobolev 1 ψ) :
    ∫ x, inner ℝ (Torus.grad ψ x) (Torus.grad ψ x) ≤ ‖lpFun 1 ψ‖ ^ 2 := by
  have hq : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have e1 := covForm_lpFun hm hq (ρ := fun _ => (1 : ℝ)) continuous_const (fun _ => zero_le_one)
    h₁ c₁ d₁ h₁ c₁ d₁
  have hvol : withDensityReal (fun _ : Torus d => (1 : ℝ)) = volume := by
    simp [withDensityReal]
  rw [hvol] at e1
  simp only [mul_one] at e1
  have hs := RelCov.hasSum_form_diag (basis d m) (covForm m (1 / 2) (volume : Measure (Torus d)))
    (dd0 m (1 / 2)) (fun i y => covForm_volume_diag hm hq i y) (lpFun m ψ) (lpFun m ψ)
  have hr : HasSum (fun k => NegSobolev.coord (lpFun 1 ψ) k ^ 2) (‖lpFun 1 ψ‖ ^ 2) := by
    obtain ⟨hsu, hn⟩ := NegSobolev.coord_sq (lpFun 1 ψ)
    rw [hn]; exact hsu.hasSum
  have hle := hasSum_le (fun k => ?_) hs hr
  · rw [e1] at hle
    simpa using hle
  · rw [inner_basis, coord_lpFun h₁, coord_lpFun h1]
    unfold dd0 wt
    have hj := Torus.jp_pos k.1
    have hjm : Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m = 1 := by
      rw [← Real.rpow_add hj]; simp
    have hj2 : Lattice.jp k.1 ^ 2 = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 := by
      unfold Lattice.jp
      rw [Real.sq_sqrt (by positivity)]
    have hj1 : Lattice.jp k.1 ^ (1 : ℝ) = Lattice.jp k.1 := Real.rpow_one _
    rw [hj1]
    have : 2 * (1 / 2) * (Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ (-m)) * (4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) *
        ((Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k) * (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k)) =
        (4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2) * (Torus.funRealCoeff ψ k) ^ 2 * (Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m) ^ 2 := by
      ring
    rw [this, hjm]
    nlinarith [sq_nonneg (Torus.funRealCoeff ψ k), sq_nonneg (Lattice.enorm k.1), sq_nonneg Real.pi,
      mul_nonneg (sq_nonneg (Torus.funRealCoeff ψ k)) (mul_nonneg (sq_nonneg Real.pi) (sq_nonneg (Lattice.enorm k.1)))]

/-- Norm of a pullback vector for a single pair of times. -/
theorem tl2Mo5_norm_pullback_le {m : ℝ} (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (t r : ℝ)
    (ℓ : NegSobolev d m →L[ℝ] ℝ) :
    ‖pullbackVec (HRS.Uniform.Comp28.plainData V) t r ℓ‖ ≤ ‖V t r‖ * ‖ℓ‖ := by
  unfold pullbackVec
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
  simp only [ContinuousLinearMap.comp_apply, HRS.Uniform.Comp28.plainData_VE, HRS.Uniform.Comp28.plainData_j,
    ContinuousLinearMap.id_apply]
  calc ‖ℓ (V t r b)‖ ≤ ‖ℓ‖ * ‖V t r b‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * (‖V t r‖ * ‖b‖) := mul_le_mul_of_nonneg_left ((V t r).le_opNorm b) (norm_nonneg _)
    _ = ‖V t r‖ * ‖ℓ‖ * ‖b‖ := by ring

/-- Operator bound for the frozen propagator on `H^1` (level-1 dual evolution `W₁`, stationary path). -/
theorem tl2Mo5_lp1_bound (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    {W₁ : ℝ → ℝ → NegSobolev d 1 →L[ℝ] NegSobolev d 1}
    (hW₁ : IsDualEvolution S.dyn (fun _ => ρβ) 1 W₁) {σ t : ℝ} (hσ : 0 ≤ σ) (hσt : σ ≤ t)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ‖lpFun 1 (propagator S.dyn (fun _ => ρβ) σ t φ)‖ ≤ ‖W₁ t σ‖ * ‖lpFun 1 φ‖ := by
  have htr := HRS.ThermLin.thermlin_stationary_traj S h
  have hφm : MemSobolev 1 φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ 1
  have e := t25p_pullback_eq_lpFun S.hd htr hW₁ (K := ‖W₁ t σ‖) (norm_nonneg _) hσ hσt le_rfl hφ
  have e' : lpFun 1 (propagator S.dyn (fun _ => ρβ) σ t φ) = pullbackVec (HRS.Uniform.Comp28.plainData W₁) t σ (gfb4_ell 1 φ) := e.symm
  rw [e']
  refine (tl2Mo5_norm_pullback_le W₁ t σ _).trans ?_
  unfold gfb4_ell
  rw [innerSL_apply_norm]

/-- Variant of `t25p_cov_eq` (diagonal case) with two trajectories: the noise covariation is `covDensT` along `S.ρ`, the
evolution `W` is the dual evolution along the constant path `ρβ`.  The pulled-back vector is `lpFun m (U^β_{σ,t}φ)`. -/
theorem tl2Mo5_cov_diag (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m)
    {T' : ℝ} (hT' : 0 < T') {W : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution S.dyn (fun _ => ρβ) m W) {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖W t r‖ ≤ K)
    {σ t : ℝ} (hσ : σ ∈ Set.Icc 0 t) (ht : t ≤ T') {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    covDensT m S.β⁻¹ T' S.ρ σ (pullbackVec (HRS.Uniform.Comp28.plainData W) t σ (gfb4_ell m φ))
      (pullbackVec (HRS.Uniform.Comp28.plainData W) t σ (gfb4_ell m φ)) =
    2 * S.β⁻¹ * ∫ x, inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ t φ) x)
      (Torus.grad (propagator S.dyn (fun _ => ρβ) σ t φ) x) * S.ρ σ x := by
  have htr := HRS.ThermLin.thermlin_stationary_traj S h
  have hq : 0 ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
  have hσT : σ ∈ Set.Icc 0 T' := ⟨hσ.1, hσ.2.trans ht⟩
  simp only [covDensT, if_pos hσT]
  have hp := t25p_pullback_eq_lpFun S.hd htr hdual hK hσ.1 hσ.2 (hKb σ t hσ.1 hσ.2 ht) hφ
  have hp' : pullbackVec (HRS.Uniform.Comp28.plainData W) t σ (gfb4_ell m φ) =
      lpFun m (propagator S.dyn (fun _ => ρβ) σ t φ) := hp
  rw [hp']
  have hρc : Continuous (S.ρ σ) := tl2Mo_rho_continuous S hσT.1
  have hρ0 := (tl2Mo_rho_density S hσT.1).nonneg
  have hck := adjkd_propagator_ck2 htr.dyn (fun _ => ρβ) hσ.1 hσ.2 φ
  have hmem := t25p_memSobolev_propagator S.hd htr hdual hK hσ.1 hσ.2 (hKb σ t hσ.1 hσ.2 ht) hφ
  have hcont : Continuous (propagator S.dyn (fun _ => ρβ) σ t φ) :=
    Torus.continuous_of_continuous_lift hck.continuous
  have hC1 : Torus.IsCk 1 (propagator S.dyn (fun _ => ρβ) σ t φ) := ContDiff.of_le hck (by norm_num)
  exact covForm_lpFun hm hq hρc hρ0 hmem hcont hC1 hmem hcont hC1

end HRS.ThermLin.Plan2

import HRS.Uniform.Q54cAux35

/-!
# EQ-GAUSS (a): the particle-noise covariance form on `E_M`, `M > d/2 + 1`

`covForm M q (ρ dx) (lpFun M ψ₁) (lpFun M ψ₂) = 2q ∫ ∇ψ₁·∇ψ₂ ρ dx` for smooth `ψ₁, ψ₂`.

The existing lemmas (`Q14Aux6.q14_covForm_apply`, `Q54cAux35.covForm_lpFun`) need `M > d/2 + 2`; here the
continuity of `x ↦ b_{x,j}` in `E_M` is obtained by dominated convergence (instead of a Lipschitz bound), and the
series for `∂_jψ(a)` is taken at a larger index (`ψ` is smooth).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MD.EQGaussLyapCov

open HRS HRS.Uniform HRS.Uniform.Q14 HRS.Uniform.Q54c

variable {d : ℕ}

theorem eqglc_norm_bVec_sq_le {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) (j : Fin d) (x : Torus d) :
    ‖bVec γ j x‖ ^ 2 ≤ 2 * q14S d (γ - 1) := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq (bVec γ j x)
  rw [hn]
  have hs2 := summable_jp_rpow (d := d) (γ - 1) (by linarith)
  calc ∑' k, NegSobolev.coord (bVec γ j x) k ^ 2
      ≤ ∑' k : NonzeroLattice d, 2 * Lattice.jp k.1 ^ (-(2 * (γ - 1))) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hs (hs2.mul_left 2)
        rw [q14_coord_bVec hγ j x k]
        have := q14_term_bound γ 1 k (c := Torus.partialDeriv j (Torus.realMode k) x) (t := 1)
          (by simpa using q14_coef_bound j k x)
        simpa using this
    _ = 2 * q14S d (γ - 1) := by rw [tsum_mul_left]; rfl

theorem eqglc_continuous_bVec {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) (j : Fin d) :
    Continuous (bVec γ j) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hs2 := summable_jp_rpow (d := d) (γ - 1) (by linarith)
  have hcoord : ∀ k : NonzeroLattice d, Continuous fun x : Torus d =>
      Torus.partialDeriv j (Torus.realMode k) x := fun k =>
    HRS.PDE.continuous_partialDeriv j _ (by
      have := HRS.Uniform.Q48b.q48b_isSmooth_realMode k
      exact (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.realMode k)) from this).of_le
        (by exact_mod_cast le_top))
  have key : Continuous fun x => ‖bVec γ j x - bVec γ j x₀‖ ^ 2 := by
    have e : (fun x => ‖bVec γ j x - bVec γ j x₀‖ ^ 2) =
        fun x => ∑' k : NonzeroLattice d, NegSobolev.coord (bVec γ j x - bVec γ j x₀) k ^ 2 := by
      funext x; exact (NegSobolev.coord_sq _).2
    rw [e]
    refine continuous_tsum (u := fun k : NonzeroLattice d => 8 * Lattice.jp k.1 ^ (-(2 * (γ - 1))))
      (fun k => ?_) (hs2.mul_left 8) (fun k x => ?_)
    · have : (fun x => NegSobolev.coord (bVec γ j x - bVec γ j x₀) k ^ 2) = fun x =>
          (Lattice.jp k.1 ^ (-γ) * (Torus.partialDeriv j (Torus.realMode k) x -
            Torus.partialDeriv j (Torus.realMode k) x₀)) ^ 2 := by
        funext x
        rw [q14_coord_sub, q14_coord_bVec hγ j x k, q14_coord_bVec hγ j x₀ k, ← mul_sub]
      rw [this]
      exact (continuous_const.mul ((hcoord k).sub continuous_const)).pow 2
    · rw [q14_coord_sub, q14_coord_bVec hγ j x k, q14_coord_bVec hγ j x₀ k, ← mul_sub,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : |Torus.partialDeriv j (Torus.realMode k) x - Torus.partialDeriv j (Torus.realMode k) x₀| ≤
          Real.sqrt 2 * Lattice.jp k.1 ^ (1 : ℕ) * 2 := by
        refine (abs_sub _ _).trans ?_
        have h1 := q14_coef_bound j k x
        have h2 := q14_coef_bound j k x₀
        simp only [pow_one]
        linarith
      have := q14_term_bound γ 1 k (c := Torus.partialDeriv j (Torus.realMode k) x -
        Torus.partialDeriv j (Torus.realMode k) x₀) (t := 2) hb
      refine this.trans (le_of_eq ?_)
      norm_num
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have h0 := (Real.continuous_sqrt.comp key).tendsto x₀
  simp only [Function.comp, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Real.sqrt_zero] at h0
  refine h0.congr fun y => ?_
  simp only [Function.comp_apply, dist_eq_norm]
  exact Real.sqrt_sq (norm_nonneg _)

theorem eqglc_covForm_apply {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) {q : ℝ} (hq : 0 ≤ q)
    (μ : Measure (Torus d)) [IsFiniteMeasure μ] (x y : NegSobolev d γ) :
    covForm γ q μ x y = ∑ j : Fin d, ∫ a,
      inner ℝ (Real.sqrt (2 * q) • bVec γ j a) x * inner ℝ (Real.sqrt (2 * q) • bVec γ j a) y ∂μ := by
  unfold covForm
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ChartAux.outerCov_apply (eqglc_continuous_bVec hγ j) (M := 2 * q14S d (γ - 1))
    (fun a => eqglc_norm_bVec_sq_le hγ j a) μ x y, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [inner_smul_left, conj_trivial]
  have : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
  calc 2 * q * (inner ℝ (bVec γ j a) x * inner ℝ (bVec γ j a) y)
      = (Real.sqrt (2 * q) * Real.sqrt (2 * q)) * (inner ℝ (bVec γ j a) x * inner ℝ (bVec γ j a) y) := by
        rw [this]
    _ = _ := by ring

theorem eqglc_inner_bVec_lpFun {M : ℝ} (hM : (d : ℝ) / 2 + 1 < M) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) (j : Fin d) (a : Torus d) :
    inner ℝ (bVec M j a) (lpFun M ψ) = Torus.partialDeriv j ψ a := by
  have hψM : MemSobolev M ψ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hψ M
  set n : ℝ := (d : ℝ) / 2 + 3 with hnd
  have hn : (d : ℝ) / 2 + 2 < n := by rw [hnd]; linarith
  have hψn : MemSobolev n ψ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hψ n
  have hc : Continuous ψ := HRS.PDE.MFLinear.continuous_of_isSmooth hψ
  have hψ1 : Torus.IsCk 1 ψ := by
    simpa using HRS.PDE.MFSemigroup.isCk_nat_of_isSmooth hψ 1
  rw [HRS.Uniform.Q54.inner_eq_tsum_coord]
  have hs := partialDeriv_series hn hψn hc hψ1 j a
  refine (tsum_congr fun k => ?_).trans hs.tsum_eq
  rw [q14_coord_bVec hM j a k, coord_lpFun hψM]
  have hj := Real.rpow_pos_of_pos (Torus.jp_pos k.1) M
  have : Lattice.jp k.1 ^ (-M) * Lattice.jp k.1 ^ M = 1 := by
    rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
  calc Lattice.jp k.1 ^ (-M) * Torus.partialDeriv j (Torus.realMode k) a *
        (Lattice.jp k.1 ^ M * Torus.funRealCoeff ψ k)
      = (Lattice.jp k.1 ^ (-M) * Lattice.jp k.1 ^ M) *
        (Torus.funRealCoeff ψ k * Torus.partialDeriv j (Torus.realMode k) a) := by ring
    _ = _ := by rw [this, one_mul]

theorem eqglc_covForm_lpFun {M : ℝ} (hM : (d : ℝ) / 2 + 1 < M) {q : ℝ} (hq : 0 ≤ q)
    {ρ : Torus d → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {ψ₁ ψ₂ : Torus d → ℝ}
    (h₁ : Torus.IsSmooth ψ₁) (h₂ : Torus.IsSmooth ψ₂) :
    covForm M q (withDensityReal ρ) (lpFun M ψ₁) (lpFun M ψ₂) =
      2 * q * ∫ x, inner ℝ (Torus.grad ψ₁ x) (Torus.grad ψ₂ x) * ρ x := by
  haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hρ
  rw [eqglc_covForm_apply hM hq]
  have hpt : ∀ (j : Fin d) (a : Torus d),
      inner ℝ (Real.sqrt (2 * q) • bVec M j a) (lpFun M ψ₁) *
        inner ℝ (Real.sqrt (2 * q) • bVec M j a) (lpFun M ψ₂) =
      2 * q * (Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a) := by
    intro j a
    rw [inner_smul_left, inner_smul_left, eqglc_inner_bVec_lpFun hM h₁ j a,
      eqglc_inner_bVec_lpFun hM h₂ j a]
    have : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
    simp only [conj_trivial]
    calc Real.sqrt (2 * q) * Torus.partialDeriv j ψ₁ a * (Real.sqrt (2 * q) * Torus.partialDeriv j ψ₂ a)
        = (Real.sqrt (2 * q) * Real.sqrt (2 * q)) * (Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a) := by
          ring
      _ = _ := by rw [this]
  simp_rw [hpt]
  have hρm : Measurable ρ := hρ.measurable
  have h11 : Torus.IsCk 1 ψ₁ := by simpa using HRS.PDE.MFSemigroup.isCk_nat_of_isSmooth h₁ 1
  have h21 : Torus.IsCk 1 ψ₂ := by simpa using HRS.PDE.MFSemigroup.isCk_nat_of_isSmooth h₂ 1
  have hcont : ∀ j : Fin d, Continuous fun a =>
      Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a :=
    fun j => (HRS.PDE.continuous_partialDeriv j ψ₁ h11).mul (HRS.PDE.continuous_partialDeriv j ψ₂ h21)
  have hint : ∀ j : Fin d, Integrable (fun a => ρ a * (2 * q * (Torus.partialDeriv j ψ₁ a *
      Torus.partialDeriv j ψ₂ a))) := fun j =>
    (hρ.mul ((continuous_const.mul (hcont j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e1 : ∀ j : Fin d, ∫ a, 2 * q * (Torus.partialDeriv j ψ₁ a * Torus.partialDeriv j ψ₂ a)
      ∂(withDensityReal ρ) = ∫ a, ρ a * (2 * q * (Torus.partialDeriv j ψ₁ a *
        Torus.partialDeriv j ψ₂ a)) :=
    fun j => HRS.integral_withDensityReal_eq ρ hρm hρ0 _
  simp_rw [e1]
  rw [← integral_finset_sum _ (fun j _ => hint j)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ = 2 * q * (inner ℝ (Torus.grad ψ₁ x) (Torus.grad ψ₂ x) * ρ x)
  rw [PiLp.inner_apply]
  simp only [HRS.Commutator.StressAux.grad_apply]
  rw [← Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm, mul_left_comm]

end HRS.MD.EQGaussLyapCov

end

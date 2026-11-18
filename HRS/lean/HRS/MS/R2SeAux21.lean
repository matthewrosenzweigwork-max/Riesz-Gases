import HRS.MS.R2SeAux20

/-!
# S9.9 `r2_static_edgeworth`, packet 21: the Stein identity with a linear factor (E1b)

Worker S99, namespace `S99`.  `s99_E1b`: for a corrected observable `w` (`S46Feat`), a bounded `C¹` observable `b`,
`Y_b = √N(μ_N(b) - ν(b))` (bounded for each fixed `N`) and `ψ ∈ Bd 1`:

`E[Y_w Y_b ψ(W)] = E[√N R_w Y_b ψ(W)] + ∑_l E[T_{wl} Y_b ∂_lψ(W)] + E[T_{wb} ψ(W)]`.

It is `s99_E1` for the bounded test function `Ψ(z, y) = ϑ_R(y) ψ(z)`, with `ϑ_R(y) = y` for `|y| < R` and `R > 2√N ‖b‖_∞ ≥ |Y_b|`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section E1b

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU Cs : ℝ}
  (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (hT : ThermalData d s a β C c BU)
  (hN : 2 ≤ N) (hS : S46.S46Static d s a β γ Cs N)

include hd hs0 hsd ha hβ hγ hT hN hS

theorem s99_E1b {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ)
    {b : Euc d → ℝ} (hb : MemCb J b) {w χ : Euc d → ℝ} {Bw : ℝ} (hw : MemCb J w)
    (hwf : S46.S46Feat d s a β γ w χ Bw) {ψ : SeqL2 → ℝ} (hψ : Bd 1 ψ) :
    ∫ X, s45_Yi N w (pair (S46.s46_nu d s a β γ N) w) X *
        (s45_Yi N b (pair (S46.s46_nu d s a β γ N) b) X *
          ψ (featureVec φ (S46.s46_nu d s a β γ N) X)) ∂(S46.s46_P d s a β γ N) =
      ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (S46.s46_nu d s a β γ N)
          (S46.s46_P d s a β γ N) (commutatorKernel d s (gradient χ)) X) *
          (s45_Yi N b (pair (S46.s46_nu d s a β γ N) b) X *
            ψ (featureVec φ (S46.s46_nu d s a β γ N) X)) ∂(S46.s46_P d s a β γ N) +
      ∑' l, ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          (s45_Yi N b (pair (S46.s46_nu d s a β γ N) b) X *
            pd ψ l (featureVec φ (S46.s46_nu d s a β γ N) X)) ∂(S46.s46_P d s a β γ N) +
      ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient b x⟫)) *
          ψ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := hS.prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  set cbb : ℝ := cbNorm J b with hcbb
  have hcbb0 : 0 ≤ cbb := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbbd : ∀ x, |b x| ≤ cbb := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le hb x
    rwa [Real.norm_eq_abs] at this
  have hYb : ∀ X : EucConfig d N, |s45_Yi N b (pair ν b) X| ≤ 2 * Real.sqrt N * cbb := by
    intro X
    simp only [s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := s45_abs_pair_empirical_le hN1 hbbd X
    have h2 : |pair ν b| ≤ cbb := HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hbbd x)
    calc Real.sqrt N * |pair (empirical X) b - pair ν b|
        ≤ Real.sqrt N * (|pair (empirical X) b| + |pair ν b|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (cbb + cbb) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * cbb := by ring
  set R : ℝ := 2 * Real.sqrt N * cbb + 1 with hRdef
  have hRpos : 0 < R := by have := Real.sqrt_nonneg (N : ℝ); positivity
  obtain ⟨ϑ, hϑc, hϑid, hϑder, M, hM0, hM⟩ := s99_cutoff R hRpos
  have hϑd : Differentiable ℝ ϑ := hϑc.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable one_ne_zero
  set Ψ : SeqL2 × ℝ → ℝ := fun p => ϑ p.2 * ψ p.1 with hΨdef
  have hΨfd : ∀ p : SeqL2 × ℝ, HasFDerivAt Ψ (ϑ p.2 • (fderiv ℝ ψ p.1).comp
      (ContinuousLinearMap.fst ℝ SeqL2 ℝ) + ψ p.1 • (deriv ϑ p.2 • ContinuousLinearMap.snd ℝ SeqL2 ℝ)) p := by
    intro p
    have h1 : HasFDerivAt (fun p : SeqL2 × ℝ => ϑ p.2) (deriv ϑ p.2 • ContinuousLinearMap.snd ℝ SeqL2 ℝ) p :=
      (hϑd p.2).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : SeqL2 × ℝ => ψ p.1) ((fderiv ℝ ψ p.1).comp
        (ContinuousLinearMap.fst ℝ SeqL2 ℝ)) p := (hψd p.1).hasFDerivAt.comp p hasFDerivAt_fst
    exact h1.mul h2
  have hΨc : ContDiff ℝ 1 Ψ :=
    ((hϑc.of_le (by exact_mod_cast le_top)).comp contDiff_snd).mul (hψ.1.comp contDiff_fst)
  have hΨb : ∀ p, |Ψ p| ≤ M * 1 := fun p => by
    simp only [hΨdef]
    rw [abs_mul]
    exact mul_le_mul (hM p.2).1 (hψ.abs_le _) (abs_nonneg _) hM0
  have hΨD : ∀ p, ‖fderiv ℝ Ψ p‖ ≤ M * 1 + 1 * M := fun p => by
    rw [(hΨfd p).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun z => ?_
    have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
    have hz2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    have hd1 : |fderiv ℝ ψ p.1 z.1| ≤ ‖z‖ := by
      have h0 := (fderiv ℝ ψ p.1).le_opNorm z.1
      rw [Real.norm_eq_abs] at h0
      have h1 := hψ.fderiv_le p.1
      nlinarith [norm_nonneg z.1, norm_nonneg (fderiv ℝ ψ p.1)]
    have hd2 : |z.2| ≤ ‖z‖ := by rwa [Real.norm_eq_abs] at hz2
    simp only [add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
    rw [Real.norm_eq_abs]
    have e1 : |ϑ p.2 * fderiv ℝ ψ p.1 z.1| ≤ M * ‖z‖ := by
      rw [abs_mul]
      exact mul_le_mul (hM p.2).1 hd1 (abs_nonneg _) hM0
    have e2 : |ψ p.1 * (deriv ϑ p.2 * z.2)| ≤ 1 * (M * ‖z‖) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hψ.abs_le _) (mul_le_mul (hM p.2).2 hd2 (abs_nonneg _) hM0)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
    calc _ ≤ |ϑ p.2 * fderiv ℝ ψ p.1 z.1| + |ψ p.1 * (deriv ϑ p.2 * z.2)| := abs_add_le _ _
      _ ≤ M * ‖z‖ + 1 * (M * ‖z‖) := add_le_add e1 e2
      _ = (M * 1 + 1 * M) * ‖z‖ := by ring
  have hE := s99_E1 hd hs0 hsd ha hβ hγ hT hN hS hJ hφ hb hw hwf (Ψ := Ψ) hΨc hΨb hΨD
  -- evaluate along the configuration
  have hΨval : ∀ X : EucConfig d N, Ψ (Zq N φ b ν X) =
      s45_Yi N b (pair ν b) X * ψ (featureVec φ ν X) := by
    intro X
    have hlt : |s45_Yi N b (pair ν b) X| < R := by have := hYb X; linarith
    simp only [hΨdef, Zq]
    rw [hϑid _ hlt]
  have hΨz : ∀ (X : EucConfig d N) (l : ℕ), fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0) =
      s45_Yi N b (pair ν b) X * pd ψ l (featureVec φ ν X) := by
    intro X l
    have hlt : |s45_Yi N b (pair ν b) X| < R := by have := hYb X; linarith
    rw [(hΨfd _).fderiv]
    simp only [Zq, pd, add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, mul_zero, add_zero]
    rw [hϑid _ hlt]
  have hΨy : ∀ X : EucConfig d N, fderiv ℝ Ψ (Zq N φ b ν X) (0, 1) =
      ψ (featureVec φ ν X) := by
    intro X
    have hlt : |s45_Yi N b (pair ν b) X| < R := by have := hYb X; linarith
    rw [(hΨfd _).fderiv]
    simp only [Zq, add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, map_zero, mul_zero, zero_add, mul_one]
    rw [hϑder _ hlt]; ring
  rw [← hνdef, ← hPdef] at hE
  simp only [hΨval, hΨz, hΨy] at hE
  exact hE

end E1b

end S99

end

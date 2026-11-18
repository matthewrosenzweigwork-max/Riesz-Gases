import HRS.MS.SA16Y3S3

/-!
# S.A.16 (SA16Y3) L1: Lipschitz bound of the pairings of the mild solution with test-function-dependent constants

`sa16y3_lip_pairD`: for the mild solution `u` of `sa16r_fixedn_mild`-type data, the weak identity gives
`|ℓ_ψ(u τ) − ℓ_ψ(u τ')| ≤ (ν Lχ + Lψ) |τ − τ'|` whenever `|ℓ_χ(u r)| ≤ Lχ` and `|ℓ_ψ(K r (u r))| ≤ Lψ`.
Unlike `sa16y3_sub_lip_pair`, no operator bound `‖K r‖ ≤ BK` enters the constant (`hKb` is only qualitative); the constants
`Lχ, Lψ` may depend on the test functions `ψ, χ` (and on the energy bound of the path), not on the size of the drift.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section L1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_lip_pairD {k : ℕ} {ν T B BK Lψ Lχ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hB : 0 ≤ B)
    (K : ℝ → WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ BK) (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T))
    (φ : WmpSpace d (k + 1) p) {ψ χ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ)
    (hHW : SA16RHeatWeak d k p ν T hψ hχ)
    {u : ℝ → WmpSpace d (k + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d k p ν φ τ + voltOp (gainKer (sa16r_GamT d k p ν) K) u τ)
    (hLχ : ∀ r ∈ Icc (0 : ℝ) T, |sa16r_ell d (k + 1) p hχ (u r)| ≤ Lχ)
    (hLψ : ∀ r ∈ Icc (0 : ℝ) T, |sa16r_ell d k p hψ (K r (u r))| ≤ Lψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      |sa16r_ell d (k + 1) p hψ (u τ) - sa16r_ell d (k + 1) p hψ (u τ')| ≤
        (ν * Lχ + Lψ) * |τ - τ'| := by
  intro τ hτ τ' hτ'
  have hBK0 : 0 ≤ BK := (norm_nonneg (K 0)).trans (hKb 0 ⟨le_rfl, hT.le⟩)
  have hid := sa16r_fixedn_weak (B := BK) hν hT hBK0 k K hKb hKc φ hψ hχ hHW hu hsol
  set f : ℝ → ℝ := fun r => ν * sa16r_ell d (k + 1) p hχ (u r) + sa16r_ell d k p hψ (K r (u r)) with hf
  have hcont : ContinuousOn f (Icc 0 T) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul ((sa16r_ell d (k + 1) p hχ).continuous.comp_continuousOn hu)
    · exact (sa16r_ell d k p hψ).continuous.comp_continuousOn (sa16y3_K_continuousOn K hKb hKc hu)
  have hint : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, IntervalIntegrable f volume a b := by
    intro a ha b hb
    refine ContinuousOn.intervalIntegrable (hcont.mono ?_)
    exact uIcc_subset_Icc ha hb
  have hdiff : sa16r_ell d (k + 1) p hψ (u τ) - sa16r_ell d (k + 1) p hψ (u τ') =
      ∫ r in τ'..τ, f r := by
    rw [hid τ hτ, hid τ' hτ']
    simp only [add_sub_add_left_eq_sub]
    rw [intervalIntegral.integral_interval_sub_left (hint 0 (left_mem_Icc.2 hT.le) τ hτ)
      (hint 0 (left_mem_Icc.2 hT.le) τ' hτ')]
  rw [hdiff, ← Real.norm_eq_abs]
  have hmin : 0 ≤ min τ' τ := le_min hτ'.1 hτ.1
  have hmax : max τ' τ ≤ T := max_le hτ'.2 hτ.2
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ') (b := τ) (f := f)
    (C := ν * Lχ + Lψ) (fun r hr => by
      simp only [Set.uIoc, Set.mem_Ioc] at hr
      have hrI : r ∈ Icc (0 : ℝ) T := ⟨le_trans hmin (le_of_lt hr.1), le_trans hr.2 hmax⟩
      have hfr : ‖f r‖ ≤ ‖ν * sa16r_ell d (k + 1) p hχ (u r)‖ + ‖sa16r_ell d k p hψ (K r (u r))‖ :=
        norm_add_le _ _
      rw [norm_mul, Real.norm_of_nonneg hν.le, Real.norm_eq_abs, Real.norm_eq_abs] at hfr
      calc ‖f r‖ ≤ ν * |sa16r_ell d (k + 1) p hχ (u r)| + |sa16r_ell d k p hψ (K r (u r))| := hfr
        _ ≤ ν * Lχ + Lψ := add_le_add (mul_le_mul_of_nonneg_left (hLχ r hrI) hν.le) (hLψ r hrI))
  exact hbound

end L1

end HRS.Whole.AppendixA.Phase2SA16R

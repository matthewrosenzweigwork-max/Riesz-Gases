import HRS.MS.SA16RDuh2

/-!
# S.A.16 (SA16Y3) S3: sub-case Lipschitz bound for pairings of the mild solution (SA16S P8 item S3)

`sa16y3_K_continuousOn`: for an order-zero family `K r : W^{k+1} →L W^k` (bounded, pointwise continuous in `r`) and a
continuous path `u`, the map `r ↦ K r (u r)` is continuous on `[0,T]`.
`sa16y3_sub_lip_pair`: for the mild solution `u` of `sa16r_fixedn_mild`-type data, with `SA16RHeatWeak` for `ψ, χ`,
`|ℓ_ψ(u τ) − ℓ_ψ(u τ')| ≤ (ν ‖ℓ_χ‖ B_u + ‖ℓ_ψ‖ B_K B_u) |τ − τ'|` for `τ, τ' ∈ [0,T]`.
No dual identity and no order-one bound are used; the bound is pointwise on the integrand of `sa16r_fixedn_weak`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section S3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_K_continuousOn {k : ℕ} {T BK : ℝ} (K : ℝ → WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ BK) (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T))
    {u : ℝ → WmpSpace d (k + 1) p} (hu : ContinuousOn u (Icc 0 T)) :
    ContinuousOn (fun r => K r (u r)) (Icc 0 T) := by
  intro r₀ hr₀
  have hu₀ := hu r₀ hr₀
  -- decomposition `K r (u r) = K r (u r - u r₀) + K r (u r₀)`
  have hA : ContinuousWithinAt (fun r => K r (u r - u r₀)) (Icc 0 T) r₀ := by
    unfold ContinuousWithinAt
    have hlim : Tendsto (fun r => ‖u r - u r₀‖) (𝓝[Icc 0 T] r₀) (𝓝 0) := by
      have h := (tendsto_iff_norm_sub_tendsto_zero.1 hu₀)
      exact h
    have hsq : Tendsto (fun r => BK * ‖u r - u r₀‖) (𝓝[Icc 0 T] r₀) (𝓝 0) := by
      simpa using hlim.const_mul BK
    have hbound : ∀ᶠ r in 𝓝[Icc 0 T] r₀, ‖K r (u r - u r₀)‖ ≤ BK * ‖u r - u r₀‖ := by
      refine eventually_nhdsWithin_of_forall fun r hr => ?_
      exact (K r).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hKb r hr)
        (norm_nonneg _))
    have hz : Tendsto (fun r => K r (u r - u r₀)) (𝓝[Icc 0 T] r₀) (𝓝 0) :=
      squeeze_zero_norm' hbound hsq
    show Tendsto (fun r => K r (u r - u r₀)) (𝓝[Icc 0 T] r₀) (𝓝 (K r₀ (u r₀ - u r₀)))
    rw [sub_self, map_zero]
    exact hz
  have hC : ContinuousWithinAt (fun r => K r (u r₀)) (Icc 0 T) r₀ := hKc (u r₀) r₀ hr₀
  have hsum := hA.add hC
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · exact eventually_nhdsWithin_of_forall fun r _ => by simp
  · simp

theorem sa16y3_sub_lip_pair {k : ℕ} {ν T B BK Bu : ℝ} (hν : 0 < ν) (hT : 0 < T) (hB : 0 ≤ B)
    (K : ℝ → WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ BK) (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T))
    (φ : WmpSpace d (k + 1) p) {ψ χ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ)
    (hHW : SA16RHeatWeak d k p ν T hψ hχ)
    {u : ℝ → WmpSpace d (k + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d k p ν φ τ + voltOp (gainKer (sa16r_GamT d k p ν) K) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖u r‖ ≤ Bu) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      |sa16r_ell d (k + 1) p hψ (u τ) - sa16r_ell d (k + 1) p hψ (u τ')| ≤
        (ν * ‖sa16r_ell d (k + 1) p hχ‖ * Bu + ‖sa16r_ell d k p hψ‖ * BK * Bu) * |τ - τ'| := by
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
    (C := ν * ‖sa16r_ell d (k + 1) p hχ‖ * Bu + ‖sa16r_ell d k p hψ‖ * BK * Bu) (fun r hr => by
      simp only [Set.uIoc, Set.mem_Ioc] at hr
      have hrI : r ∈ Icc (0 : ℝ) T := ⟨le_trans hmin (le_of_lt hr.1), le_trans hr.2 hmax⟩
      have h1 : ‖sa16r_ell d (k + 1) p hχ (u r)‖ ≤ ‖sa16r_ell d (k + 1) p hχ‖ * Bu :=
        ((sa16r_ell d (k + 1) p hχ).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd r hrI) (norm_nonneg _))
      have hKu : ‖K r (u r)‖ ≤ BK * Bu :=
        ((K r).le_opNorm _).trans (mul_le_mul (hKb r hrI) (hbd r hrI) (norm_nonneg _)
          ((norm_nonneg (K r)).trans (hKb r hrI)))
      have h2 : ‖sa16r_ell d k p hψ (K r (u r))‖ ≤ ‖sa16r_ell d k p hψ‖ * (BK * Bu) :=
        ((sa16r_ell d k p hψ).le_opNorm _).trans (mul_le_mul_of_nonneg_left hKu (norm_nonneg _))
      have hfr : ‖f r‖ ≤ ‖ν * sa16r_ell d (k + 1) p hχ (u r)‖ + ‖sa16r_ell d k p hψ (K r (u r))‖ :=
        norm_add_le _ _
      rw [norm_mul, Real.norm_of_nonneg hν.le] at hfr
      calc ‖f r‖ ≤ ν * ‖sa16r_ell d (k + 1) p hχ (u r)‖ + ‖sa16r_ell d k p hψ (K r (u r))‖ := hfr
        _ ≤ ν * (‖sa16r_ell d (k + 1) p hχ‖ * Bu) + ‖sa16r_ell d k p hψ‖ * (BK * Bu) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hν.le) h2
        _ = ν * ‖sa16r_ell d (k + 1) p hχ‖ * Bu + ‖sa16r_ell d k p hψ‖ * BK * Bu := by ring)
  exact hbound

end S3

end HRS.Whole.AppendixA.Phase2SA16R

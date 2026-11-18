import HRS.MS.UniqN0b
import HRS.MH.ScreenedAsmLocal
import HRS.MH.ScreenedK5

/-!
# N0 of `UniqPlan.md`, part (a'): transfer of the S.B.4(ii) bounds to `H_i = g * ∂_iψ`

* `n0_memSobolev_one`: `ψ ∈ C¹_c ⇒ MemSobolev 1 ψ`; hence `sobolevNormE r ψ < ⊤` for all `r ≤ 1`
  (`n0_sobolevNormE_lt_top`), in particular for `r = kgOrder d s` and `r = s + 1 - d` (both `< 1`).
* `n0_kcd_local`: the `L²(ball)` bound of `screened_local` holds for the explicit function
  `kernelConvDeriv d s i ψ` (via `n0_gradKernelRep`, `screened_local_proof` and `gk_unique_proof`).
* `n0_kcd_global` (`s ≥ d - 1`): `kernelConvDeriv d s i ψ ∈ L²` with the global bound of `screened_local_global`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN0

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MH.Screened HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem n0_memSobolev_one {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    HRS.PDE.ToolboxRd.MemSobolev 1 ψ := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero
  have hmem : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hK : IsCompact (tsupport ψ) := hψc
  set V : ℝ := (volume (tsupport ψ)).toReal with hV
  have hind : Integrable ((tsupport ψ).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hK.isClosed.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
  refine memSobolev_one_of_diff_bound hmem (2 * (L : ℝ) ^ 2 * V) (fun h => ?_)
  have hind' : Integrable (fun x => (tsupport ψ).indicator (fun _ => (1 : ℝ)) (x - h)) volume :=
    hind.comp_sub_right h
  have hrhs : Integrable (fun x => (L : ℝ) ^ 2 * ‖h‖ ^ 2 *
      ((tsupport ψ).indicator (fun _ => (1 : ℝ)) x +
        (tsupport ψ).indicator (fun _ => (1 : ℝ)) (x - h))) volume :=
    (hind.add hind').const_mul _
  have hpt : ∀ x, (ψ x - ψ (x - h)) ^ 2 ≤ (L : ℝ) ^ 2 * ‖h‖ ^ 2 *
      ((tsupport ψ).indicator (fun _ => (1 : ℝ)) x +
        (tsupport ψ).indicator (fun _ => (1 : ℝ)) (x - h)) := by
    intro x
    have hi1 : 0 ≤ (tsupport ψ).indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hi2 : 0 ≤ (tsupport ψ).indicator (fun _ => (1 : ℝ)) (x - h) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases hx : x ∈ tsupport ψ
    · rw [Set.indicator_of_mem hx]
      have h1 : |ψ x - ψ (x - h)| ≤ L * ‖h‖ := by
        have := hL.dist_le_mul x (x - h)
        simpa [Real.dist_eq, dist_eq_norm] using this
      have h2 : (ψ x - ψ (x - h)) ^ 2 ≤ ((L : ℝ) * ‖h‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (L : ℝ)) (sq_nonneg ‖h‖)) hi2]
    · by_cases hxh : x - h ∈ tsupport ψ
      · rw [Set.indicator_of_mem hxh]
        have h1 : |ψ x - ψ (x - h)| ≤ L * ‖h‖ := by
          have := hL.dist_le_mul x (x - h)
          simpa [Real.dist_eq, dist_eq_norm] using this
        have h2 : (ψ x - ψ (x - h)) ^ 2 ≤ ((L : ℝ) * ‖h‖) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (L : ℝ)) (sq_nonneg ‖h‖)) hi1]
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxh,
          Set.indicator_of_notMem hx, Set.indicator_of_notMem hxh]
        simp
  calc ∫ x, (ψ x - ψ (x - h)) ^ 2
      ≤ ∫ x, (L : ℝ) ^ 2 * ‖h‖ ^ 2 * ((tsupport ψ).indicator (fun _ => (1 : ℝ)) x +
        (tsupport ψ).indicator (fun _ => (1 : ℝ)) (x - h)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hrhs
          (Eventually.of_forall hpt)
    _ = 2 * (L : ℝ) ^ 2 * V * ‖h‖ ^ 2 := by
        rw [integral_const_mul, integral_add hind hind', integral_indicator hK.isClosed.measurableSet,
          integral_sub_right_eq_self ((tsupport ψ).indicator (fun _ => (1 : ℝ))) h,
          integral_indicator hK.isClosed.measurableSet]
        simp [hV, Measure.real]
        ring

theorem n0_sobolevNormE_lt_top {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    {r : ℝ} (hr : r ≤ 1) : sobolevNormE r ψ < ⊤ := by
  unfold sobolevNormE
  rw [if_pos (memSobolev_mono hr (n0_memSobolev_one hψ hψc))]
  exact ENNReal.ofReal_lt_top

theorem n0_kgOrder_le_one {s : ℝ} (hsd : s < d) : kgOrder d s ≤ 1 := by
  unfold kgOrder
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine max_le (by linarith) zero_le_one

/-- The `L²(ball)` bound of `screened_local` for the explicit function `kernelConvDeriv d s i ψ`. -/
theorem n0_kcd_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (ψ : Euc d → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((closedBall c' r').indicator (kernelConvDeriv d s i ψ)) 2 volume ≤
          ENNReal.ofReal (C * ρ ^ C₀) * sobolevNormE (kgOrder d s) ψ := by
  obtain ⟨C₀, C, hC⟩ := screened_local_proof hd hs0 hsd
  refine ⟨C₀, C, fun i ρ hρ c ψ hψ hψc hsupp c' r' hr' => ?_⟩
  obtain ⟨w, hw, hbd⟩ := hC i ρ hρ c ψ hsupp (n0_sobolevNormE_lt_top hψ hψc (n0_kgOrder_le_one hsd))
  have hae : w =ᵐ[volume] kernelConvDeriv d s i ψ :=
    gk_unique_proof i hw (n0_gradKernelRep hs0 hsd i hψ hψc)
  have hae' : (closedBall c' r').indicator w =ᵐ[volume]
      (closedBall c' r').indicator (kernelConvDeriv d s i ψ) := by
    filter_upwards [hae] with x hx
    simp only [Set.indicator, hx]
  rw [← eLpNorm_congr_ae hae']
  exact hbd c' r' hr'

/-- The global bound of `screened_local_global` (`s ≥ d - 1`) for `kernelConvDeriv d s i ψ`. -/
theorem n0_kcd_global (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (hs1 : (d : ℝ) - 1 ≤ s) :
    ∃ C : ℝ, ∀ (i : Fin d) (ψ : Euc d → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      MemLp (kernelConvDeriv d s i ψ) 2 volume ∧
      eLpNorm (kernelConvDeriv d s i ψ) 2 volume ≤
        ENNReal.ofReal C * sobolevNormE (s + 1 - d) ψ := by
  have hs0 : 0 ≤ s := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C, hC⟩ := screened_local_global_proof hd hsd hs1
  refine ⟨C, fun i ψ hψ hψc => ?_⟩
  obtain ⟨w, hw, hmem, hbd⟩ := hC i ψ (n0_sobolevNormE_lt_top hψ hψc (by linarith))
  have hae : w =ᵐ[volume] kernelConvDeriv d s i ψ :=
    gk_unique_proof i hw (n0_gradKernelRep hs0 hsd i hψ hψc)
  refine ⟨hmem.ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae]
  exact hbd

end HRS.MS.UniqN0

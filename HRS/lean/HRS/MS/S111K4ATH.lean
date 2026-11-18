import HRS.MS.S111K4ATA

/-!
# S11.1 / all-tests boundary (S111K4AT), piece H: norm convergence of the Hermite sections in `Σ^m`

`k4hs_hermiteCoeff`: the Hermite coefficients of the section are the truncated coefficients of `φ`.
`k4at_eta_tendsto`: `‖ofFun φ_n - ofFun φ‖ → 0`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole

variable {d : ℕ}

theorem k4hs_hermiteCoeff (m : ℝ) (n : ℕ) (φ : Euc d → ℝ) (β : MultiIndex d) :
    hermiteCoeff (k4hs m n φ) β = if β.degree ≤ n then hermiteCoeff φ β else 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : MultiIndex d → ℝ, ∀ α, c α = oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α :=
    ⟨_, fun _ => rfl⟩
  have hk : k4hs m n φ = fun x => ∑ α ∈ (multiIndex_sublevel_finite d n).toFinset, c α * oscTestFun m α x := by
    funext x; simp only [k4hs, hc]
  have hcomb : hermiteCoeff (k4hs m n φ) β = ∑ α ∈ (multiIndex_sublevel_finite d n).toFinset,
      c α * hermiteCoeff (oscTestFun m α) β := by
    rw [hk]
    unfold hermiteCoeff
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_assoc]
    · intro α _
      have := (integrable_hermiteFunD_mul α β).const_mul (c α * oscEigenvalue d α ^ (-(m / 2)))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [oscTestFun]; ring
  rw [hcomb]
  simp_rw [hermiteCoeff_oscTestFun]
  by_cases hb : β.degree ≤ n
  · rw [if_pos hb, Finset.sum_eq_single β]
    · simp only [if_true, mul_one]
      have h1 := rpow_neg_half_mul m (oscEigenvalue d β) (oscEv_pos β)
      rw [hc β]
      calc (oscEigenvalue d β ^ (m / 2) * hermiteCoeff φ β) * oscEigenvalue d β ^ (-(m / 2))
          = hermiteCoeff φ β * (oscEigenvalue d β ^ (-(m / 2)) * oscEigenvalue d β ^ (m / 2)) := by ring
        _ = hermiteCoeff φ β := by rw [h1, mul_one]
    · intro α _ hα; simp [hα]
    · intro h; exact absurd (by simpa using hb) h
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun α hα => ?_
    have : α ≠ β := by
      rintro rfl
      exact hb (by simpa using hα)
    simp [this]

theorem k4at_lp_norm_sq (y : lp (fun _ : MultiIndex d => ℝ) 2) : ‖y‖ ^ 2 = ∑' β, (y β) ^ 2 := by
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
  simp_rw [Real.norm_eq_abs, sq_abs] at this
  exact this

theorem k4at_eta_sq (m : ℝ) (n : ℕ) {φ : Euc d → ℝ} (hφ : MemOsc m φ) :
    ‖OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ‖ ^ 2 =
      (∑' β, (OscSpace.coord (OscSpace.ofFun m φ) β) ^ 2) -
        ∑ β ∈ (multiIndex_sublevel_finite d n).toFinset, (OscSpace.coord (OscSpace.ofFun m φ) β) ^ 2 := by
  classical
  set x : MultiIndex d → ℝ := fun β => OscSpace.coord (OscSpace.ofFun m φ) β with hx
  have hxs : Summable fun β => (x β) ^ 2 := by
    exact lp_two_summable (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m φ)
  have hn : MemOsc m (k4hs m n φ) := (k4hs_osc m n φ).2
  have hcoord : ∀ β, OscSpace.coord (OscSpace.ofFun m (k4hs m n φ)) β = if β.degree ≤ n then x β else 0 := by
    intro β
    rw [OscSpace.coord_ofFun_eq hn, k4hs_hermiteCoeff, hx]
    simp only [OscSpace.coord_ofFun_eq hφ]
    split_ifs <;> simp
  have hy : ∀ β, (show lp (fun _ : MultiIndex d => ℝ) 2 from
      (OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ)) β = (if β.degree ≤ n then x β else 0) - x β := by
    intro β
    have := hcoord β
    simp only [OscSpace.coord] at this
    show ((show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m (k4hs m n φ)) -
      (show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m φ)) β = _
    rw [lp.coeFn_sub, Pi.sub_apply, this]
    rfl
  have hnorm : ‖OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ‖ ^ 2 =
      ∑' β, ((show lp (fun _ : MultiIndex d => ℝ) 2 from
        (OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ)) β) ^ 2 :=
    k4at_lp_norm_sq (show lp (fun _ : MultiIndex d => ℝ) 2 from
        (OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ))
  rw [hnorm]
  simp_rw [hy]
  have hpt : ∀ β, ((if β.degree ≤ n then x β else 0) - x β) ^ 2 =
      (x β) ^ 2 - (if β.degree ≤ n then x β else 0) ^ 2 := by
    intro β; split_ifs <;> ring
  simp_rw [hpt]
  have hfin : Summable fun β => (if β.degree ≤ n then x β else 0) ^ 2 := by
    refine summable_of_ne_finset_zero (s := (multiIndex_sublevel_finite d n).toFinset) fun β hβ => ?_
    have : ¬ β.degree ≤ n := by simpa using hβ
    simp [this]
  rw [hxs.tsum_sub hfin]
  congr 1
  rw [tsum_eq_sum (s := (multiIndex_sublevel_finite d n).toFinset)]
  · refine Finset.sum_congr rfl fun β hβ => ?_
    have : β.degree ≤ n := by simpa using hβ
    simp [this, hx]
  · intro β hβ
    have : ¬ β.degree ≤ n := by simpa using hβ
    simp [this]


theorem k4at_sublevel_atTop : Tendsto (fun n : ℕ => (multiIndex_sublevel_finite d n).toFinset) atTop
    (atTop : Filter (Finset (MultiIndex d))) := by
  refine tendsto_atTop_atTop.2 fun s => ⟨s.sup fun α => α.degree, fun n hn α hα => ?_⟩
  simp only [Set.Finite.mem_toFinset]
  show α.degree ≤ n
  exact (Finset.le_sup (f := fun α : MultiIndex d => α.degree) hα).trans hn

theorem k4at_eta_tendsto (m : ℝ) {φ : Euc d → ℝ} (hφ : MemOsc m φ) :
    Tendsto (fun n : ℕ => ‖OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ‖) atTop (𝓝 0) := by
  have hxs : Summable fun β : MultiIndex d => (OscSpace.coord (OscSpace.ofFun m φ) β) ^ 2 :=
    lp_two_summable (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m φ)
  have h1 := (hxs.hasSum.comp k4at_sublevel_atTop)
  have h2 : Tendsto (fun n : ℕ => ‖OscSpace.ofFun m (k4hs m n φ) - OscSpace.ofFun m φ‖ ^ 2) atTop (𝓝 0) := by
    have h3 := (tendsto_const_nhds (x := ∑' β : MultiIndex d, (OscSpace.coord (OscSpace.ofFun m φ) β) ^ 2)).sub h1
    rw [sub_self] at h3
    refine h3.congr fun n => ?_
    rw [k4at_eta_sq m n hφ]
    rfl
  have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h4
  refine h4.congr fun n => ?_
  simp [Real.sqrt_sq (norm_nonneg _)]

end HRS.MS.S111K4AT

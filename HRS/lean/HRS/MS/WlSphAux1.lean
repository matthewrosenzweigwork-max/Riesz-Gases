import HRS.Whole.Static
import HRS.MS.ThmLogAux2
import HRS.MS.Ste
import HRS.MS.Comm

/-!
# WL-1 (part 1): the spherical series of the logarithmic kernel and the head/tail split

Packet WL-1 of `docs/WR_LOG_PLAN.md` (S3.5, `r2_log_static`), namespace `HRS.MS.Wl`, helper prefix `wl_`.
These are infrastructure lemmas (not manuscript rows).  With `u = stereoInv` and
`τ(x,y) = (1 + ⟨u x, u y⟩)/2` (`wl_tau`):

* `wl_one_sub_tau`: `1 - τ = |x-y|² / ((1+|x|²)(1+|y|²))`, hence `0 ≤ τ ≤ 1`, `τ = 1` on the diagonal,
  `τ < 1` off it, and `K x y = -(1/2) log (1 - τ)` off the diagonal (`wl_K_eq_log`);
* `wl_K_series`: for `x ≠ y`, `K x y = ∑_{j ≥ 0} (1/2) τ^(j+1)/(j+1)` (`HasSum`);
* `wl_km M x y = ∑_{j<M} (1/2) τ^(j+1)/(j+1)` (the head, `wl_km_diag`: `km x x = wl_k0 M`), and the
  junk-safe tail `wl_qm M x y = if x = y then 0 else K x y - km M x y` (so `0 ≤ qm` EVERYWHERE, although
  `K x x = 2 ℓ x` and `K - km` can be negative on the diagonal); `wl_K_eq : K = km + qm` off the diagonal;
* `wl_qm_eq_tsum`: for all `x y` (also on the diagonal, where both sides are `0`: the series diverges and
  `tsum` is junk `0`), `qm M x y = ∑' j, (1/2) τ^(M+j+1)/(M+j+1)`;
* the band `wl_band M L = km L - km M` (`M ≤ L`) equals `∑_{j ∈ Ico M L}` of the same terms
  (`wl_band_eq_sum_Ico`), is `≥ 0`, and `qm M = qm L + band M L` off the diagonal (`wl_qm_eq_qm_add_band`);
* measurability (`wl_km_measurable`, `wl_qm_measurable`, `wl_band_measurable`; `km` and `band` are even
  continuous) and symmetry of all of them.

Deviations from the brief: the tail series is written with the index `M + j + 1` (not `M + 1 + j`).
`wl_K` is `HRS.Whole.sphericalLogKernel`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-- `τ(x,y) = (1 + ⟨u x, u y⟩)/2`, `u = stereoInv`. -/
def wl_tau (x y : Euc d) : ℝ := (1 + inner ℝ (stereoInv x) (stereoInv y)) / 2

lemma wl_tau_symm (x y : Euc d) : wl_tau x y = wl_tau y x := by
  unfold wl_tau; rw [real_inner_comm]

lemma wl_tau_self (x : Euc d) : wl_tau x x = 1 := by
  unfold wl_tau
  rw [real_inner_self_eq_norm_sq, ste_norm_stereoInv]; norm_num

lemma wl_tau_continuous : Continuous (fun p : Euc d × Euc d => wl_tau p.1 p.2) := by
  unfold wl_tau
  have h1 : Continuous (fun p : Euc d × Euc d => stereoInv p.1) :=
    t67_stereo_continuous.comp continuous_fst
  have h2 : Continuous (fun p : Euc d × Euc d => stereoInv p.2) :=
    t67_stereo_continuous.comp continuous_snd
  exact (continuous_const.add (h1.inner h2)).div_const 2

/-- `1 - τ = |x-y|² / ((1+|x|²)(1+|y|²))`. -/
lemma wl_one_sub_tau (x y : Euc d) :
    1 - wl_tau x y = ‖x - y‖ ^ 2 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
  have h := t67_chordal x y
  have hn : ‖stereoInv x - stereoInv y‖ ^ 2 = 2 - 2 * inner ℝ (stereoInv x) (stereoInv y) := by
    rw [@norm_sub_sq_real, ste_norm_stereoInv, ste_norm_stereoInv]; ring
  have hA : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hB : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  rw [hn] at h
  unfold wl_tau
  rw [eq_div_iff (by positivity)]
  field_simp at h ⊢
  linarith

lemma wl_tau_nonneg (x y : Euc d) : 0 ≤ wl_tau x y := by
  unfold wl_tau
  have := abs_real_inner_le_norm (stereoInv x) (stereoInv y)
  rw [ste_norm_stereoInv, ste_norm_stereoInv] at this
  have := (abs_le.1 this).1
  linarith

lemma wl_tau_le_one (x y : Euc d) : wl_tau x y ≤ 1 := by
  have : 0 ≤ 1 - wl_tau x y := by rw [wl_one_sub_tau]; positivity
  linarith

lemma wl_tau_lt_one {x y : Euc d} (hxy : x ≠ y) : wl_tau x y < 1 := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have : 0 < 1 - wl_tau x y := by rw [wl_one_sub_tau]; positivity
  linarith

lemma wl_one_sub_tau_pos {x y : Euc d} (hxy : x ≠ y) : 0 < 1 - wl_tau x y := by
  linarith [wl_tau_lt_one hxy]

/-- `K x y = -(1/2) log (1 - τ x y)` off the diagonal. -/
lemma wl_K_eq_log {x y : Euc d} (hxy : x ≠ y) :
    sphericalLogKernel x y = -(1 / 2) * Real.log (1 - wl_tau x y) := by
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hA : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have hB : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  rw [wl_one_sub_tau, Real.log_div (by positivity) (by positivity), Real.log_mul hA.ne' hB.ne',
    Real.log_pow]
  unfold sphericalLogKernel logWeight
  push_cast
  ring

/-- The base-term of the series: `(1/2) t^(j+1)/(j+1)`. -/
def wl_term (t : ℝ) (j : ℕ) : ℝ := (1 / 2) * (t ^ (j + 1) / ((j : ℝ) + 1))

lemma wl_term_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ wl_term t j := by
  unfold wl_term; positivity

/-- **The spherical series**: `K x y = ∑_{j ≥ 0} (1/2) τ^(j+1)/(j+1)` for `x ≠ y`. -/
theorem wl_K_series {x y : Euc d} (hxy : x ≠ y) :
    HasSum (fun j : ℕ => wl_term (wl_tau x y) j) (sphericalLogKernel x y) := by
  have h0 := wl_tau_nonneg x y
  have h1 := wl_tau_lt_one hxy
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := wl_tau x y)
    (by rw [abs_of_nonneg h0]; exact h1)
  have := h.mul_left (1 / 2)
  have e : sphericalLogKernel x y = 1 / 2 * -Real.log (1 - wl_tau x y) := by
    rw [wl_K_eq_log hxy]; ring
  rw [e]
  exact this

/-- `k0 M = (1/2) ∑_{j<M} 1/(j+1)`: the diagonal value of the head. -/
def wl_k0 (M : ℕ) : ℝ := (1 / 2) * ∑ j ∈ Finset.range M, 1 / ((j : ℝ) + 1)

lemma wl_k0_nonneg (M : ℕ) : 0 ≤ wl_k0 M := by unfold wl_k0; positivity

/-- The head `km M x y = ∑_{j<M} (1/2) τ^(j+1)/(j+1)`. -/
def wl_km (M : ℕ) (x y : Euc d) : ℝ := ∑ j ∈ Finset.range M, wl_term (wl_tau x y) j

lemma wl_km_diag (M : ℕ) (x : Euc d) : wl_km M x x = wl_k0 M := by
  unfold wl_km wl_k0 wl_term
  rw [wl_tau_self, Finset.mul_sum]
  simp

lemma wl_km_symm (M : ℕ) (x y : Euc d) : wl_km M x y = wl_km M y x := by
  unfold wl_km; rw [wl_tau_symm]

lemma wl_km_nonneg (M : ℕ) (x y : Euc d) : 0 ≤ wl_km M x y :=
  Finset.sum_nonneg fun j _ => wl_term_nonneg (wl_tau_nonneg x y) j

lemma wl_km_continuous (M : ℕ) : Continuous (fun p : Euc d × Euc d => wl_km M p.1 p.2) := by
  unfold wl_km wl_term
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((wl_tau_continuous.pow _).div_const _)

lemma wl_km_measurable (M : ℕ) : Measurable (fun p : Euc d × Euc d => wl_km M p.1 p.2) :=
  (wl_km_continuous M).measurable

lemma wl_km_le_k0 (M : ℕ) (x y : Euc d) : wl_km M x y ≤ wl_k0 M := by
  unfold wl_km wl_k0
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  unfold wl_term
  have h0 := wl_tau_nonneg x y
  have h1 := wl_tau_le_one x y
  have hp : wl_tau x y ^ (j + 1) ≤ 1 := pow_le_one₀ h0 h1
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have : wl_tau x y ^ (j + 1) / ((j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
    div_le_div_of_nonneg_right hp hj.le
  linarith

lemma wl_K_symm (x y : Euc d) : sphericalLogKernel x y = sphericalLogKernel y x := by
  unfold sphericalLogKernel; rw [norm_sub_rev]; ring

lemma wl_K_measurable : Measurable (fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) := by
  unfold sphericalLogKernel logWeight
  fun_prop

/-- The tail `qm M`, junk-safe: `0` on the diagonal, `K - km M` off it. -/
def wl_qm (M : ℕ) (x y : Euc d) : ℝ :=
  if x = y then 0 else sphericalLogKernel x y - wl_km M x y

lemma wl_qm_diag (M : ℕ) (x : Euc d) : wl_qm M x x = 0 := by simp [wl_qm]

lemma wl_qm_offdiag (M : ℕ) {x y : Euc d} (hxy : x ≠ y) :
    wl_qm M x y = sphericalLogKernel x y - wl_km M x y := by simp [wl_qm, hxy]

/-- `K = km + qm` off the diagonal. -/
lemma wl_K_eq (M : ℕ) {x y : Euc d} (hxy : x ≠ y) :
    sphericalLogKernel x y = wl_km M x y + wl_qm M x y := by
  rw [wl_qm_offdiag M hxy]; ring

lemma wl_qm_symm (M : ℕ) (x y : Euc d) : wl_qm M x y = wl_qm M y x := by
  unfold wl_qm
  by_cases h : x = y
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false, wl_K_symm x y, wl_km_symm M x y]

lemma wl_qm_measurable (M : ℕ) : Measurable (fun p : Euc d × Euc d => wl_qm M p.1 p.2) := by
  unfold wl_qm
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
    (wl_K_measurable.sub (wl_km_measurable M))

/-- Tail identity (off the diagonal, `HasSum` form). -/
lemma wl_qm_hasSum (M : ℕ) {x y : Euc d} (hxy : x ≠ y) :
    HasSum (fun j : ℕ => wl_term (wl_tau x y) (j + M)) (wl_qm M x y) := by
  have := (hasSum_nat_add_iff' M).mpr (wl_K_series hxy)
  rw [wl_qm_offdiag M hxy]
  exact this

lemma wl_not_summable_diag (M : ℕ) (x : Euc d) :
    ¬ Summable (fun j : ℕ => wl_term (wl_tau x x) (j + M)) := by
  intro h
  rw [summable_nat_add_iff (f := fun j : ℕ => wl_term (wl_tau x x) j) M] at h
  unfold wl_term at h
  simp only [wl_tau_self, one_pow] at h
  have h2 : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1)) := by
    simpa using h.mul_left 2
  have h3 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1 (by simpa using h2)
  exact Real.not_summable_one_div_natCast h3

/-- **Tail identity**, valid for ALL `x y`: `qm M x y = ∑' j, (1/2) τ^(M+j+1)/(M+j+1)` (both sides are
`0` on the diagonal: the series diverges there and `tsum` is the junk value `0`). -/
theorem wl_qm_eq_tsum (M : ℕ) (x y : Euc d) :
    wl_qm M x y = ∑' j : ℕ, wl_term (wl_tau x y) (M + j) := by
  by_cases h : x = y
  · subst h
    rw [wl_qm_diag]
    have := tsum_eq_zero_of_not_summable (wl_not_summable_diag M x)
    simp only [add_comm _ M] at this
    exact this.symm
  · have := (wl_qm_hasSum M h).tsum_eq
    simp only [add_comm _ M] at this
    exact this.symm

theorem wl_qm_nonneg (M : ℕ) (x y : Euc d) : 0 ≤ wl_qm M x y := by
  by_cases h : x = y
  · subst h; rw [wl_qm_diag]
  · exact (wl_qm_hasSum M h).nonneg fun j => wl_term_nonneg (wl_tau_nonneg x y) _

/-- On the diagonal `K x x = 2 ℓ x` (junk `-log 0 = 0`), which is why `qm` is not `K - km` there. -/
lemma wl_K_diag (x : Euc d) : sphericalLogKernel x x = 2 * logWeight x := by
  unfold sphericalLogKernel; simp; ring

/-! ### Bands -/

/-- The band `km L - km M` (`M ≤ L`: the terms `j ∈ [M, L)`). -/
def wl_band (M L : ℕ) (x y : Euc d) : ℝ := wl_km L x y - wl_km M x y

lemma wl_band_eq_sum_Ico {M L : ℕ} (hML : M ≤ L) (x y : Euc d) :
    wl_band M L x y = ∑ j ∈ Finset.Ico M L, wl_term (wl_tau x y) j := by
  unfold wl_band wl_km
  rw [Finset.sum_Ico_eq_sub _ hML]

lemma wl_band_nonneg {M L : ℕ} (hML : M ≤ L) (x y : Euc d) : 0 ≤ wl_band M L x y := by
  rw [wl_band_eq_sum_Ico hML]
  exact Finset.sum_nonneg fun j _ => wl_term_nonneg (wl_tau_nonneg x y) j

lemma wl_band_symm (M L : ℕ) (x y : Euc d) : wl_band M L x y = wl_band M L y x := by
  unfold wl_band; rw [wl_km_symm L, wl_km_symm M]

lemma wl_band_diag (M L : ℕ) (x : Euc d) : wl_band M L x x = wl_k0 L - wl_k0 M := by
  unfold wl_band; rw [wl_km_diag, wl_km_diag]

lemma wl_band_continuous (M L : ℕ) :
    Continuous (fun p : Euc d × Euc d => wl_band M L p.1 p.2) :=
  (wl_km_continuous L).sub (wl_km_continuous M)

lemma wl_band_measurable (M L : ℕ) : Measurable (fun p : Euc d × Euc d => wl_band M L p.1 p.2) :=
  (wl_band_continuous M L).measurable

lemma wl_band_zero (M : ℕ) (x y : Euc d) : wl_band 0 M x y = wl_km M x y := by
  simp [wl_band, wl_km]

/-- `qm M = qm L + band (M, L]` off the diagonal. -/
lemma wl_qm_eq_qm_add_band (M L : ℕ) {x y : Euc d} (hxy : x ≠ y) :
    wl_qm M x y = wl_qm L x y + wl_band M L x y := by
  rw [wl_qm_offdiag M hxy, wl_qm_offdiag L hxy]; unfold wl_band; ring

/-- `qm` is antitone in the head length (everywhere). -/
lemma wl_qm_anti {M L : ℕ} (hML : M ≤ L) (x y : Euc d) : wl_qm L x y ≤ wl_qm M x y := by
  by_cases h : x = y
  · subst h; simp [wl_qm_diag]
  · rw [wl_qm_eq_qm_add_band M L h]; linarith [wl_band_nonneg hML x y]

end HRS.MS.Wl

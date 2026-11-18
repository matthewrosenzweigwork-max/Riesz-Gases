import HRS.MS.SA12Z2NearN3C

/-!
# S.A.12 N3 (SA12Z2): `odd_same_finite`

The first Riesz derivative of `a u` against the compactly supported `u` is bounded by
`C cb ρ^d ‖u‖²₂`. Route: `∂_i (g * (au)) = g * ∂_i(au)` (`sa12z2_firstRiesz_eq`); the smoothed
pairings `Φ_ε` are symmetrized and bounded uniformly in `ε > 0` (`sa12z2_psi_bound`); the limit
`ε → 0` is by dominated convergence on the product, using the locally integrable majorant of the
smoothed kernels.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The majorant of the smoothed kernels on the ball `|z| ≤ 2ρ`. -/
def sa12z2_maj (d : ℕ) (s ρ : ℝ) (z : Euc d) : ℝ :=
  (Metric.closedBall (0 : Euc d) (2 * ρ)).indicator (fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) z

/-- The derivative `∂_i (a u)` as a function. -/
def sa12z2_w (d : ℕ) (i : Fin d) (a u : Euc d → ℝ) (y : Euc d) : ℝ :=
  fderiv ℝ (fun y => a y * u y) y (EuclideanSpace.single i (1 : ℝ))

/-- The smoothed pairing integrand `u(x) g_ε(x-y) ∂_i(au)(y)`. -/
def sa12z2_Phi (d : ℕ) (s : ℝ) (i : Fin d) (a u : Euc d → ℝ) (ε : ℝ) (p : Euc d × Euc d) : ℝ :=
  u p.1 * movtr_gEps d s ε (p.1 - p.2) * sa12z2_w d i a u p.2

theorem sa12z2_maj_nonneg (s ρ : ℝ) (z : Euc d) : 0 ≤ sa12z2_maj d s ρ z := by
  unfold sa12z2_maj
  exact Set.indicator_nonneg (fun z _ => by positivity) z

theorem sa12z2_maj_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ρ : ℝ) :
    Integrable (sa12z2_maj d s ρ) := by
  unfold sa12z2_maj
  exact ((n3_majorant_locInt hd hs0 hsd).integrableOn_isCompact
    (isCompact_closedBall (0 : Euc d) (2 * ρ))).integrable_indicator Metric.isClosed_closedBall.measurableSet

theorem sa12z2_maj_eq {s ρ : ℝ} {z : Euc d} (hz : ‖z‖ ≤ 2 * ρ) :
    sa12z2_maj d s ρ z = 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := by
  unfold sa12z2_maj
  rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hz)]

/-- Off the diagonal, the smoothed integrand is dominated by the majorant times the weight,
uniformly in `ε ∈ [0,1]`. -/
theorem sa12z2_phi_bound {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {u w : Euc d → ℝ} {c : Euc d} {ρ Cu : ℝ} (hCu : ∀ y, ‖u y‖ ≤ Cu)
    (hsu : Function.support u ⊆ Metric.closedBall c ρ)
    (hw0 : ∀ y, y ∉ Metric.closedBall c ρ → w y = 0) (p : Euc d × Euc d) (hz : p.1 - p.2 ≠ 0) :
    ‖u p.1 * movtr_gEps d s ε (p.1 - p.2) * w p.2‖ ≤
      Cu * (‖w p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)) := by
  have hCu0 : 0 ≤ Cu := (norm_nonneg _).trans (hCu p.1)
  have hu0 : ∀ y, y ∉ Metric.closedBall c ρ → u y = 0 := fun y hy =>
    by_contra fun h => hy (hsu (Function.mem_support.2 h))
  by_cases h : u p.1 = 0 ∨ w p.2 = 0
  · have h0 : ‖u p.1 * movtr_gEps d s ε (p.1 - p.2) * w p.2‖ = 0 := by
      rcases h with h | h <;> simp [h]
    rw [h0]
    exact mul_nonneg hCu0 (mul_nonneg (norm_nonneg _) (sa12z2_maj_nonneg s ρ _))
  push_neg at h
  have h1B : p.1 ∈ Metric.closedBall c ρ := by
    by_contra hc
    exact h.1 (hu0 _ hc)
  have h2B : p.2 ∈ Metric.closedBall c ρ := by
    by_contra hc
    exact h.2 (hw0 _ hc)
  have hnorm : ‖p.1 - p.2‖ ≤ 2 * ρ := by
    have h1 := Metric.mem_closedBall.1 h1B
    have h2 := Metric.mem_closedBall.1 h2B
    rw [← dist_eq_norm]
    have htri := dist_triangle p.1 c p.2
    rw [dist_comm c p.2] at htri
    linarith
  have hgM : |movtr_gEps d s ε (p.1 - p.2)| ≤ sa12z2_maj d s ρ (p.1 - p.2) := by
    rw [sa12z2_maj_eq hnorm]
    exact movtr_gEps_abs_le hs0 hε0 hε1 hz
  rw [norm_mul, norm_mul, Real.norm_eq_abs (movtr_gEps d s ε (p.1 - p.2))]
  have h1 : ‖u p.1‖ * |movtr_gEps d s ε (p.1 - p.2)| ≤ Cu * sa12z2_maj d s ρ (p.1 - p.2) :=
    mul_le_mul (hCu _) hgM (abs_nonneg _) hCu0
  calc ‖u p.1‖ * |movtr_gEps d s ε (p.1 - p.2)| * ‖w p.2‖
      ≤ (Cu * sa12z2_maj d s ρ (p.1 - p.2)) * ‖w p.2‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = Cu * (‖w p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)) := by ring

/-- `odd_same_finite`: the first Riesz derivative of `a u` paired with `u` is bounded by
`C ‖Da‖ ρ^d ‖u‖²₂` for `u` supported in a ball of radius `ρ ≥ 1`. -/
theorem odd_same_finite (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 ≤ C₀ ∧ ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∀ a : Euc d → ℝ, MemCb 1 a →
      ∀ (c : Euc d) (u : Euc d → ℝ), MemCb 2 u →
      Function.support u ⊆ Metric.closedBall c ρ →
      Integrable (fun x => u x*firstRiesz d s i (fun y => a y*u y) x) volume ∧
      |∫ x, u x*firstRiesz d s i (fun y => a y*u y) x| ≤
        C*cbNorm 1 a*ρ^C₀*(∫ x, u x^2) := by
  obtain ⟨Ck, hCk0, hCk⟩ := sa12z2_k_integral_le (d := d) hd hs0 hsd
  have hsig : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  refine ⟨1 + movtr_sigma s * Ck, (d : ℝ), by have := mul_nonneg hsig hCk0; linarith,
    Nat.cast_nonneg d, ?_⟩
  intro i ρ hρ a ha c u hu hsupp
  have hu0 : ∀ y, y ∉ Metric.closedBall c ρ → u y = 0 := fun y hy =>
    by_contra fun h => hy (hsupp (Function.mem_support.2 h))
  have hu_c : HasCompactSupport u :=
    HasCompactSupport.intro (isCompact_closedBall c ρ) hu0
  have hu_cont : Continuous u := hu.1.continuous
  have hu_C1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  have ha_C1 : ContDiff ℝ 1 a := ha.1
  have hv_C1 : ContDiff ℝ 1 (fun y => a y * u y) := ha_C1.mul hu_C1
  have hv_c : HasCompactSupport (fun y => a y * u y) :=
    HasCompactSupport.intro (isCompact_closedBall c ρ) (fun y hy => by simp [hu0 y hy])
  have hsv : Function.support (fun y => a y * u y) ⊆ Metric.closedBall c ρ := fun y hy =>
    hsupp (Function.mem_support.2 (right_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hw_c : Continuous (sa12z2_w d i a u) :=
    (hv_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hw0 : ∀ y, y ∉ Metric.closedBall c ρ → sa12z2_w d i a u y = 0 := fun y hy =>
    sa12z2_deriv_zero_outside hsv (EuclideanSpace.single i (1 : ℝ)) hy
  have hw_cs : HasCompactSupport (sa12z2_w d i a u) :=
    HasCompactSupport.intro (isCompact_closedBall c ρ) hw0
  obtain ⟨Cu, hCu⟩ := hu_cont.bounded_above_of_compact_support hu_c
  have hCu0 : 0 ≤ Cu := (norm_nonneg _).trans (hCu 0)
  -- integrable majorant of the pairing integrand
  have hbd_int : Integrable (fun p : Euc d × Euc d =>
      Cu * (‖sa12z2_w d i a u p.2‖ * sa12z2_maj d s ρ (p.1 - p.2))) (volume.prod volume) := by
    have hwn : Integrable (fun y => ‖sa12z2_w d i a u y‖) :=
      (hw_c.norm).integrable_of_hasCompactSupport hw_cs.norm
    have h := hwn.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (sa12z2_maj_integrable hd hs0 hsd ρ)
    have h' : Integrable (fun p : Euc d × Euc d =>
        ‖sa12z2_w d i a u p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)) (volume.prod volume) := by
      simpa using h
    exact h'.const_mul Cu
  have hPhi_meas : ∀ ε : ℝ, Measurable (sa12z2_Phi d s i a u ε) := fun ε => by
    unfold sa12z2_Phi
    exact ((hu_cont.measurable.comp measurable_fst).mul
      ((movtr_gEps_measurable (d := d) s ε).comp (measurable_fst.sub measurable_snd))).mul
      (hw_c.measurable.comp measurable_snd)
  have hPhi_bd : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ᵐ p ∂(volume.prod volume : Measure (Euc d × Euc d)),
      ‖sa12z2_Phi d s i a u ε p‖ ≤
        Cu * (‖sa12z2_w d i a u p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)) := by
    intro ε h0 h1
    filter_upwards [sa12z2_diag_ae hd] with p hp
    exact sa12z2_phi_bound hs0 h0 h1 hCu hsupp hw0 p hp
  -- the `ε = 0` integrand is integrable
  have hΦ0_int : Integrable (sa12z2_Phi d s i a u 0) (volume.prod volume) :=
    hbd_int.mono' (hPhi_meas 0).aestronglyMeasurable (hPhi_bd 0 le_rfl zero_le_one)
  -- the pointwise identity `∫_y Φ_0(x,y) = u(x) (g * ∂_i(au))(x)`
  have hΦ0_eq : ∀ x : Euc d, ∫ y, sa12z2_Phi d s i a u 0 (x, y) =
      u x * firstRiesz d s i (fun y => a y * u y) x := by
    intro x
    rw [sa12z2_firstRiesz_eq hs0 hsd i hv_C1 hv_c x]
    show ∫ y, u x * movtr_gEps d s 0 (x - y) * sa12z2_w d i a u y = _
    rw [movtr_gEps_zero, ← integral_const_mul]
    congr 1
    funext y
    rw [mul_assoc]
    rfl
  have hfirst_int : Integrable (fun x => u x * firstRiesz d s i (fun y => a y * u y) x) volume :=
    hΦ0_int.integral_prod_left.congr (Filter.Eventually.of_forall fun x => hΦ0_eq x)
  have hfubini : ∫ p, sa12z2_Phi d s i a u 0 p =
      ∫ x, u x * firstRiesz d s i (fun y => a y * u y) x := by
    refine (integral_prod _ hΦ0_int).trans ?_
    exact integral_congr_ae (Filter.Eventually.of_forall hΦ0_eq)
  -- uniform bound for `ε ∈ (0,1)`
  have hB : ∀ ε ∈ Ioo (0 : ℝ) 1,
      |∫ p, sa12z2_Phi d s i a u ε p| ≤
        movtr_sigma s / 2 * cbNorm 1 a * (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 := by
    intro ε hε
    show |∫ p : Euc d × Euc d, u p.1 * movtr_gEps d s ε (p.1 - p.2) *
        fderiv ℝ (fun y => a y * u y) p.2 (EuclideanSpace.single i (1 : ℝ))
          ∂(volume.prod volume)| ≤ _
    rw [sa12z2_prod_eq hu_cont hsupp s hε.1 i hv_C1 hv_c hsv]
    exact sa12z2_psi_bound hd hs0 hsd i ha hu_cont hu_c hsupp hε.1
  -- dominated convergence in `ε → 0+`
  have hlim : Tendsto (fun ε => ∫ p, sa12z2_Phi d s i a u ε p) (𝓝[>] 0)
      (𝓝 (∫ p, sa12z2_Phi d s i a u 0 p)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p : Euc d × Euc d => Cu * (‖sa12z2_w d i a u p.2‖ * sa12z2_maj d s ρ (p.1 - p.2)))
      (Filter.Eventually.of_forall fun ε => (hPhi_meas ε).aestronglyMeasurable) ?_ hbd_int ?_
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      exact hPhi_bd ε hε.1.le hε.2.le
    · filter_upwards [sa12z2_diag_ae hd] with p hp
      have hc := movtr_gEps_cont_eps (d := d) s hp
      have ht : Tendsto (fun ε => movtr_gEps d s ε (p.1 - p.2)) (𝓝[>] 0)
          (𝓝 (movtr_gEps d s 0 (p.1 - p.2))) :=
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact (ht.const_mul (u p.1)).mul_const (sa12z2_w d i a u p.2)
  have hbound0 : |∫ p, sa12z2_Phi d s i a u 0 p| ≤
      movtr_sigma s / 2 * cbNorm 1 a * (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 :=
    le_of_tendsto hlim.abs (by
      filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      exact hB ε hε)
  -- assemble
  refine ⟨hfirst_int, ?_⟩
  rw [← hfubini]
  refine hbound0.trans ?_
  rw [Real.rpow_natCast]
  have hkI := hCk ρ hρ
  have hU : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun x => sq_nonneg (u x)
  have hcb : 0 ≤ cbNorm 1 a := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_cb_nonneg ha
  have hρd : 0 ≤ ρ ^ d := pow_nonneg (by linarith) _
  have step1 : movtr_sigma s / 2 * cbNorm 1 a * (∫ z, sa12z2_k d s ρ z) * ∫ x, u x ^ 2 ≤
      movtr_sigma s / 2 * cbNorm 1 a * (Ck * ρ ^ d) * ∫ x, u x ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkI (mul_nonneg (by positivity) hcb)) hU
  have h1 : movtr_sigma s / 2 * Ck ≤ 1 + movtr_sigma s * Ck := by
    linarith [mul_nonneg hsig hCk0]
  have h2 : 0 ≤ cbNorm 1 a * ρ ^ d * ∫ x, u x ^ 2 :=
    mul_nonneg (mul_nonneg hcb hρd) hU
  have step2 : movtr_sigma s / 2 * cbNorm 1 a * (Ck * ρ ^ d) * ∫ x, u x ^ 2 ≤
      (1 + movtr_sigma s * Ck) * cbNorm 1 a * ρ ^ d * ∫ x, u x ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 h2
    nlinarith [this]
  exact step1.trans step2

end HRS.MH.AdjointRd.Phase2SA12Near

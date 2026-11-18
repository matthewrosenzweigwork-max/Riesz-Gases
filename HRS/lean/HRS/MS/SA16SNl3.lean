import HRS.MS.SA16SNl2

/-!
# S.A.16 (SA16S) Nl3: weak identity of the nonlocal operator on `WmpSpace` (packet P6)

`sa16so_weak_G`: if `T : W^{m,p} → W^{m,p}` is continuous linear with zeroth component `eucNonlocal s M μ φ` on the jet
of `φ ∈ C_c^∞` (`μ = C.ρ τ'` of class `C^1`, `0 ≤ s < d`) and `ψ ∈ C_c^∞` has `nonlocalTestRd C τ' ψ ∈ L^{p'}`, then
`ℓ_ψ(T G) = ∫ (zeroth component of G) · nonlocalTestRd C τ' ψ` for every `G ∈ W^{m,p}`.
`sa16so_memLp_decay`: the `L^q` membership from the decay bound of `test_nonlocal_decay`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nl3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `G ↦ ∫ G_τ(x) N(x) dx`, for `N ∈ L^{p'}` -/
def sa16so_pairN (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (τ : WIndex d m) {N : Euc d → ℝ}
    (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume) : WLp d m p →L[ℝ] ℝ :=
  ((((ContinuousLinearMap.mul ℝ ℝ).comp
      (ContinuousLinearMap.proj τ : (WIndex d m → ℝ) →L[ℝ] ℝ)).lpPairing
      (volume : Measure (Euc d)) (ENNReal.ofReal p)
      (ENNReal.conjExponent (ENNReal.ofReal p))).flip (hN.toLp N))

lemma sa16so_pairN_apply (m : ℕ) (τ : WIndex d m) {N : Euc d → ℝ}
    (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume) (G : WLp d m p) :
    sa16so_pairN d m p τ hN G = ∫ x, ((G : Euc d → (WIndex d m → ℝ)) x τ) * N x := by
  unfold sa16so_pairN
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hN] with x hx
  simp [hx]

/-- the pairing of the zeroth component with `N` as a functional on `WmpSpace` -/
def sa16so_ellN (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {N : Euc d → ℝ}
    (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume) : WmpSpace d m p →L[ℝ] ℝ :=
  (sa16so_pairN d m p (wZero d m) hN).comp (WmpSpace d m p).subtypeL

lemma sa16so_ellN_apply (m : ℕ) {N : Euc d → ℝ}
    (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume) (G : WmpSpace d m p) :
    sa16so_ellN d m p hN G = ∫ x, wrep d m p G x * N x := by
  unfold sa16so_ellN
  rw [ContinuousLinearMap.comp_apply, sa16so_pairN_apply]
  rfl

theorem sa16so_weak_G (m : ℕ) (C : WholeCoeff d) (τ' : ℝ) (hs0 : 0 ≤ C.s) (hsd : C.s < d)
    (hμ : ContDiff ℝ 1 (C.ρ τ')) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hN : MemLp (nonlocalTestRd C τ' ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (T : WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hT : ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d m p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal C.s C.M (C.ρ τ') φ.1) (G : WmpSpace d m p) :
    sa16r_ell d m p hψ (T G) = ∫ x, wrep d m p G x * nonlocalTestRd C τ' ψ x := by
  refine (sa16r_Jcc_dense d m p).induction_on G (isClosed_eq ?_ ?_) (fun φ => ?_)
  · exact (sa16r_ell d m p hψ).continuous.comp T.continuous
  · simp_rw [← sa16so_ellN_apply m hN]
    exact (sa16so_ellN d m p hN).continuous
  · rw [sa16r_ell_apply]
    have e1 : ∫ x, wrep d m p (T (sa16r_Jcc d m p φ)) x * ψ x =
        ∫ x, HRS.MH.AdjointRd.eucNonlocal C.s C.M (C.ρ τ') φ.1 x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hT φ] with x hx
      rw [hx]
    have e2 : ∫ x, wrep d m p (sa16r_Jcc d m p φ) x * nonlocalTestRd C τ' ψ x =
        ∫ x, φ.1 x * nonlocalTestRd C τ' ψ x := by
      refine integral_congr_ae ?_
      rw [sa16r_Jcc_eq]
      filter_upwards [sa16r_cc_elt_wrep (p := p) φ.2 m] with x hx
      rw [hx]
    rw [e1, e2]
    exact sa16sp_pairing_cc C τ' hs0 hsd hμ φ.2 hψ

lemma sa16so_jbracket_ge (x : Euc d) : (1 + ‖x‖) / Real.sqrt 2 ≤ jbracket x := by
  unfold jbracket
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have h2 : (1 + ‖x‖) ≤ Real.sqrt (2 * (1 + ‖x‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le h1
  rw [Real.sqrt_mul (by norm_num)] at h2
  linarith [mul_comm (Real.sqrt 2) (Real.sqrt (1 + ‖x‖ ^ 2))]

/-- `L^q` membership from a decay bound -/
lemma sa16so_memLp_decay {N : Euc d → ℝ} (hN : Continuous N) {K r : ℝ} (hr : (d : ℝ) < r)
    (hb : ∀ x, |N x| ≤ K * jbracket x ^ (-r)) {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ ⊤) :
    MemLp N q volume := by
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq1
  have hqr : (1 : ℝ) ≤ q.toReal := by
    have := ENNReal.toReal_mono hq hq1
    simpa using this
  refine (integrable_norm_rpow_iff hN.aestronglyMeasurable hq0 hq).1 ?_
  set q' := q.toReal with hq'
  set c : ℝ := |K| * Real.sqrt 2 ^ r with hc
  have hc0 : 0 ≤ c := by positivity
  have hrq : (d : ℝ) < r * q' := by nlinarith [show (0 : ℝ) < r from lt_of_le_of_lt (Nat.cast_nonneg d) hr]
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-(r * q'))) := by
    refine integrable_one_add_norm (E := Euc d) (μ := volume) ?_
    rwa [finrank_euclideanSpace_fin]
  refine (hint.const_mul (c ^ q')).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((hN.norm).rpow_const (fun _ => Or.inr (by linarith))).aestronglyMeasurable
  · have hx1 : 0 < 1 + ‖x‖ := by positivity
    have hjb : 0 < jbracket x := lt_of_lt_of_le (by positivity) (sa16so_jbracket_ge x)
    have hr0 : 0 < r := lt_of_le_of_lt (Nat.cast_nonneg d) hr
    have h1 : jbracket x ^ (-r) ≤ Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r) := by
      have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + ‖x‖) / Real.sqrt 2)
        (sa16so_jbracket_ge x) (by linarith : -r ≤ 0)
      rw [Real.div_rpow hx1.le (Real.sqrt_nonneg _), Real.rpow_neg (Real.sqrt_nonneg _),
        div_inv_eq_mul, mul_comm] at h2
      exact h2
    have h2 : ‖N x‖ ≤ c * (1 + ‖x‖) ^ (-r) := by
      rw [Real.norm_eq_abs]
      refine (hb x).trans ?_
      have hjp : 0 ≤ jbracket x ^ (-r) := Real.rpow_nonneg hjb.le _
      calc K * jbracket x ^ (-r) ≤ |K| * jbracket x ^ (-r) := mul_le_mul_of_nonneg_right (le_abs_self _) hjp
        _ ≤ |K| * (Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = c * (1 + ‖x‖) ^ (-r) := by rw [hc]; ring
    have hp0 : 0 ≤ (1 + ‖x‖) ^ (-r) := Real.rpow_nonneg hx1.le _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖N x‖ ^ q' ≤ (c * (1 + ‖x‖) ^ (-r)) ^ q' :=
          Real.rpow_le_rpow (norm_nonneg _) h2 (by linarith)
      _ = c ^ q' * (1 + ‖x‖) ^ (-(r * q')) := by
          rw [Real.mul_rpow hc0 hp0, ← Real.rpow_mul hx1.le]
          congr 2; ring

end Nl3

end HRS.Whole.AppendixA.Phase2SA16R

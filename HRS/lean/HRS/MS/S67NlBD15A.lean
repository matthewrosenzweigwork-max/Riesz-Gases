import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD14B

/-!
# S6.7 nonlinear, packet S6.7nl.15A: one Hermite sequence with locally uniform physical weighted-profile convergence

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4238-4245, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definition: `s67bd_profile`.
The sequence is `vn n = mo_pSum v n` (Hermite partial sums, Schwartz). The differences
`e_n = v - pSum_n` lie in `Sigma^m`, are continuous, hence equal their `C^7` Sobolev
representatives (`mn_sobolev_emb_gen`, `mn_ae_eq_cont`) with `C^1` norm at most `C osc(e_n) -> 0`.
The local potential is a convolution with the compactly supported `L^1` kernel `g_loc`
supported in `|z| <= 2`, so it is bounded by `|g_loc|_{L^1}` times the sup of the first
derivative of `sqrt(rho) e_n` on the ball `B(x,2)`; continuity of the profile is dominated
convergence for the translated convolution.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_profile (d : ℕ) (s : ℝ) (ρ v : Euc d → ℝ) (K : ℕ) (i : Fin d)
    (x : Euc d) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ K * s67bd_local d s (fun y => Real.sqrt (ρ y) * v y) i x

lemma s67bd15a_T_eq (κ w : Euc d → ℝ) (x : Euc d) :
    movb2_T κ w x = ∫ y, κ (x - y) * w y := by
  unfold movb2_T
  rw [← integral_sub_left_eq_self (fun z => κ z * w (x - z)) volume x]
  simp only [sub_sub_cancel]

lemma s67bd15a_loc_eq (h : Euc d → ℝ) (i : Fin d) (x : Euc d) :
    s67bd_local d s h i x = ∫ z, movb2_gloc d s z * fderiv ℝ h (x - z) (EuclideanSpace.single i 1) := by
  unfold s67bd_local s67bd_D
  rw [← s67bd15a_T_eq (movb2_gloc d s) (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) x]
  rfl

/-- continuity of the compactly supported local potential of a continuous integrand -/
lemma s67bd15a_conv_cont (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ}
    (hF : Continuous F) : Continuous fun x => ∫ z, movb2_gloc d s z * F (x - z) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨M, hM⟩ := (isCompact_closedBall x0 (3 : ℝ)).exists_bound_of_continuousOn hF.continuousOn
  have hgl : Integrable (movb2_gloc d s) volume := (mv1_gloc_integrable hd hs0 hsd).1
  refine continuousAt_of_dominated (bound := fun z => ‖movb2_gloc d s z‖ * M) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      (movb2_gloc_aesm hd hs0 hsd).mul (hF.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : 2 ≤ ‖z‖
    · rw [movb2_gloc_eq_zero hz]; simp
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (hM _ ?_) (norm_nonneg _)
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hx' : ‖x - x0‖ < 1 := by simpa [dist_eq_norm] using hx
      calc ‖x - z - x0‖ = ‖(x - x0) - z‖ := by congr 1; abel
        _ ≤ ‖x - x0‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 3 := by linarith [not_le.1 hz]
  · exact hgl.norm.mul_const M
  · exact Filter.Eventually.of_forall fun z =>
      (continuousAt_const.mul ((hF.comp (continuous_id.sub continuous_const)).continuousAt))

/-- bound on the local potential by the `L¹` mass of `g_loc` and the sup on `B(x,2)` -/
lemma s67bd15a_conv_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hFb : ∀ y, ‖y‖ ≤ 2 → |F y| ≤ A) (x : Euc d) :
    |∫ z, movb2_gloc d s z * F z| ≤ (∫ z, ‖movb2_gloc d s z‖) * A := by
  have hgl : Integrable (movb2_gloc d s) volume := (mv1_gloc_integrable hd hs0 hsd).1
  have := norm_integral_le_of_norm_le (hgl.norm.mul_const A)
    (Filter.Eventually.of_forall fun z => ?_) (f := fun z => movb2_gloc d s z * F z)
  · rw [integral_mul_const] at this
    simpa [Real.norm_eq_abs] using this
  · by_cases hz : 2 ≤ ‖z‖
    · rw [movb2_gloc_eq_zero hz]; simp
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hFb z (le_of_lt (not_le.1 hz))) (abs_nonneg _)

lemma s67bd15a_conv_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ}
    (hF : Continuous F) (x : Euc d) :
    Integrable (fun z => movb2_gloc d s z * F (x - z)) volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (2 : ℝ)).exists_bound_of_continuousOn hF.continuousOn
  have hgl : Integrable (movb2_gloc d s) volume := (mv1_gloc_integrable hd hs0 hsd).1
  refine (hgl.norm.mul_const M).mono'
    ((movb2_gloc_aesm hd hs0 hsd).mul (hF.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : 2 ≤ ‖z‖
  · rw [movb2_gloc_eq_zero hz]; simp
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hM _ ?_) (norm_nonneg _)
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖x - z - x‖ = ‖z‖ := by simp
      _ ≤ 2 := le_of_lt (not_le.1 hz)

theorem s67bd_local_approximation (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m)
    (v : Euc d → ℝ) (hvc : Continuous v) (hv : MemOsc (m : ℝ) v) :
    ∃ vn : ℕ → SchwartzMap (Euc d) ℝ,
      Tendsto (fun n => oscNorm (m : ℝ) (fun x => vn n x - v x)) atTop (𝓝 0) ∧
      ∀ (K : ℕ) (i : Fin d),
        Continuous (s67bd_profile d s ρ₀ v K i) ∧
        (∀ L : ℝ, 0 < L → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          ∀ x : Euc d, ‖x‖ ≤ L →
            |s67bd_profile d s ρ₀ (vn n) K i x - s67bd_profile d s ρ₀ v K i x| < ε) ∧
        ∀ x : Euc d, Tendsto (fun n => s67bd_profile d s ρ₀ (vn n) K i x)
          atTop (𝓝 (s67bd_profile d s ρ₀ v K i x)) := by
  have hd : 2 ≤ d := H.hd
  have hd1 : 1 ≤ d := by omega
  have hs0 := H.hs0
  have hsd := H.hsd
  obtain ⟨C, hC0, hemb⟩ := mn_sobolev_emb_gen (d := d) 7 m (by push_cast; linarith)
  choose vn hvn using fun n => mn_pSum_schwartz v n
  set e : ℕ → Euc d → ℝ := fun n x => v x - mo_pSum v n x with he
  have hecont : ∀ n, Continuous (e n) := fun n => by
    have : Continuous (mo_pSum v n) := by rw [← hvn n]; exact (vn n).continuous
    exact hvc.sub this
  have hereg : ∀ n, ContDiff ℝ ((7 : ℕ) : WithTop ℕ∞) (e n) ∧
      ∀ k ≤ 7, ∀ x, ‖iteratedFDeriv ℝ k (e n) x‖ ≤ C * oscNorm (m : ℝ) (e n) := by
    intro n
    obtain ⟨g, hg, hae, hb⟩ := hemb (e n) (mova2_sub_pSum (m : ℝ) hv n).1
    have hg' := mn_ae_eq_cont (hecont n) hg.continuous hae
    refine ⟨hg' ▸ hg, fun k hk x => ?_⟩
    have h1 := hb k hk x
    rw [← hg'] at h1
    exact h1
  have hv7 : ContDiff ℝ ((7 : ℕ) : WithTop ℕ∞) v := by
    obtain ⟨g, hg, hae, _⟩ := hemb v hv
    exact (mn_ae_eq_cont hvc hg.continuous hae) ▸ hg
  have hosc : Tendsto (fun n => oscNorm (m : ℝ) (e n)) atTop (𝓝 0) := mo_hsum_tail (m : ℝ) hv
  have hsq : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ₀ y)) := (mnb_rhoData H).sqrt_smooth
  have hsq1 : ContDiff ℝ 1 (fun y => Real.sqrt (ρ₀ y)) := hsq.of_le (by exact_mod_cast le_top)
  have hh : ContDiff ℝ 1 (fun y => Real.sqrt (ρ₀ y) * v y) :=
    hsq1.mul (hv7.of_le (by norm_num))
  have hhe : ∀ n, ContDiff ℝ 1 (fun y => Real.sqrt (ρ₀ y) * e n y) := fun n =>
    hsq1.mul ((hereg n).1.of_le (by norm_num))
  refine ⟨vn, ?_, fun K i => ?_⟩
  · have : ∀ n, oscNorm (m : ℝ) (fun x => vn n x - v x) = oscNorm (m : ℝ) (e n) := by
      intro n
      have h1 : (fun x => vn n x - v x) = fun x => (-1 : ℝ) * e n x := by
        funext x; rw [show (vn n) x = mo_pSum v n x from congrFun (hvn n) x]; simp only [he]; ring
      rw [h1, oscNorm_const_mul]; simp
    simp_rw [this]; exact hosc
  -- profile formulas
  have hF0c : Continuous (fun y => fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * v y) y (EuclideanSpace.single i 1)) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hprof : ∀ x, s67bd_profile d s ρ₀ v K i x = (1 + ‖x‖ ^ 2) ^ K *
      ∫ z, movb2_gloc d s z * fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * v y) (x - z)
        (EuclideanSpace.single i 1) := fun x => by
    unfold s67bd_profile; rw [s67bd15a_loc_eq]
  have hcont : Continuous (s67bd_profile d s ρ₀ v K i) := by
    have h1 := s67bd15a_conv_cont hd1 hs0 hsd hF0c
    have h2 : Continuous fun x : Euc d => (1 + ‖x‖ ^ 2) ^ K :=
      (continuous_const.add (continuous_norm.pow 2)).pow K
    have : s67bd_profile d s ρ₀ v K i = fun x => (1 + ‖x‖ ^ 2) ^ K *
        ∫ z, movb2_gloc d s z * fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * v y) (x - z)
          (EuclideanSpace.single i 1) := funext hprof
    rw [this]; exact h2.mul h1
  have hdiff : ∀ n x, s67bd_profile d s ρ₀ (vn n) K i x - s67bd_profile d s ρ₀ v K i x =
      -((1 + ‖x‖ ^ 2) ^ K * ∫ z, movb2_gloc d s z *
        fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * e n y) (x - z) (EuclideanSpace.single i 1)) := by
    intro n x
    have hfun : (fun y => Real.sqrt (ρ₀ y) * (vn n) y) = fun y =>
        Real.sqrt (ρ₀ y) * v y - Real.sqrt (ρ₀ y) * e n y := by
      funext y
      rw [show (vn n) y = mo_pSum v n y from congrFun (hvn n) y]; simp only [he]; ring
    have hfd : ∀ y, fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * (vn n) y) y =
        fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * v y) y - fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * e n y) y := by
      intro y
      rw [hfun]
      exact fderiv_sub ((hh.differentiable (by norm_num)) y) (((hhe n).differentiable (by norm_num)) y)
    unfold s67bd_profile
    rw [s67bd15a_loc_eq, s67bd15a_loc_eq]
    simp only [hfd, ContinuousLinearMap.sub_apply, mul_sub]
    have hi1 := s67bd15a_conv_int hd1 hs0 hsd (F := fun y => fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * v y) y
      (EuclideanSpace.single i 1)) hF0c x
    have hFe : Continuous (fun y => fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * e n y) y
        (EuclideanSpace.single i 1)) :=
      ((hhe n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hi2 := s67bd15a_conv_int hd1 hs0 hsd hFe x
    rw [integral_sub hi1 hi2]
    ring
  have hloc : ∀ L : ℝ, 0 < L → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : Euc d, ‖x‖ ≤ L →
      |s67bd_profile d s ρ₀ (vn n) K i x - s67bd_profile d s ρ₀ v K i x| < ε := by
    intro L hL ε hε
    obtain ⟨A1, hA1⟩ := (isCompact_closedBall (0 : Euc d) (L + 2)).exists_bound_of_continuousOn
      hsq.continuous.continuousOn
    obtain ⟨A2, hA2⟩ := (isCompact_closedBall (0 : Euc d) (L + 2)).exists_bound_of_continuousOn
      (hsq1.continuous_fderiv one_ne_zero).continuousOn
    set A : ℝ := max (max A1 A2) 0 with hA
    have hA0 : 0 ≤ A := le_max_right _ _
    set G0 : ℝ := ∫ z, ‖movb2_gloc d s z‖ with hG0
    have hG00 : 0 ≤ G0 := integral_nonneg fun z => norm_nonneg _
    set Q : ℝ := (1 + L ^ 2) ^ K * (G0 * (2 * A * C)) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have hev : ∀ᶠ n in atTop, Q * oscNorm (m : ℝ) (e n) < ε := by
      have := (hosc.const_mul Q).eventually (gt_mem_nhds (by rw [mul_zero]; exact hε : Q * 0 < ε))
      exact this
    filter_upwards [hev] with n hn x hx
    rw [hdiff n x, abs_neg, abs_mul]
    have hosc0 : 0 ≤ oscNorm (m : ℝ) (e n) := Real.sqrt_nonneg _
    have hbd : |∫ z, movb2_gloc d s z * fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * e n y) (x - z)
        (EuclideanSpace.single i 1)| ≤ G0 * (2 * A * C * oscNorm (m : ℝ) (e n)) := by
      have := s67bd15a_conv_bound hd1 hs0 hsd (x := x)
        (F := fun z => fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * e n y) (x - z) (EuclideanSpace.single i 1))
        (A := 2 * A * C * oscNorm (m : ℝ) (e n)) (by positivity) (fun z hz => ?_)
      · exact this
      · set y : Euc d := x - z with hy
        have hyb : y ∈ Metric.closedBall (0 : Euc d) (L + 2) := by
          rw [mem_closedBall_zero_iff]
          calc ‖y‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
            _ ≤ L + 2 := by linarith
        have hsy : |Real.sqrt (ρ₀ y)| ≤ A := by
          have := hA1 y hyb
          rw [Real.norm_eq_abs] at this
          exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
        have hdsy : |fderiv ℝ (fun y => Real.sqrt (ρ₀ y)) y (EuclideanSpace.single i 1)| ≤ A := by
          have h1 := (fderiv ℝ (fun y => Real.sqrt (ρ₀ y)) y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
          rw [PiLp.norm_single, norm_one, mul_one] at h1
          rw [← Real.norm_eq_abs]
          exact h1.trans ((hA2 y hyb).trans ((le_max_right A1 A2).trans (le_max_left _ _)))
        have hey : |e n y| ≤ C * oscNorm (m : ℝ) (e n) := by
          have := (hereg n).2 0 (by norm_num) y
          rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
        have hdey : |fderiv ℝ (e n) y (EuclideanSpace.single i 1)| ≤ C * oscNorm (m : ℝ) (e n) := by
          have h1 := (fderiv ℝ (e n) y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
          rw [PiLp.norm_single, norm_one, mul_one] at h1
          have h2 := (hereg n).2 1 (by norm_num) y
          rw [norm_iteratedFDeriv_one] at h2
          rw [← Real.norm_eq_abs]
          exact h1.trans h2
        have hdif : DifferentiableAt ℝ (fun y => Real.sqrt (ρ₀ y)) y := (hsq1.differentiable (by norm_num)) y
        have hdie : DifferentiableAt ℝ (e n) y := ((hereg n).1.differentiable (by norm_num)) y
        rw [show (fun y => Real.sqrt (ρ₀ y) * e n y) = (fun y => Real.sqrt (ρ₀ y)) * e n from rfl,
          fderiv_mul hdif hdie]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have := mul_le_mul hsy hdey (abs_nonneg _) hA0
        have := mul_le_mul hey hdsy (abs_nonneg _) (by positivity)
        nlinarith
    have hK : (1 + ‖x‖ ^ 2) ^ K ≤ (1 + L ^ 2) ^ K :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg x]) K
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + ‖x‖ ^ 2) ^ K)]
    calc (1 + ‖x‖ ^ 2) ^ K * |∫ z, movb2_gloc d s z * fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * e n y)
          (x - z) (EuclideanSpace.single i 1)|
        ≤ (1 + L ^ 2) ^ K * (G0 * (2 * A * C * oscNorm (m : ℝ) (e n))) :=
          mul_le_mul hK hbd (abs_nonneg _) (by positivity)
      _ = Q * oscNorm (m : ℝ) (e n) := by rw [hQ]; ring
      _ < ε := hn
  refine ⟨hcont, hloc, ?_⟩
  intro x
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hloc (‖x‖ + 1) (by positivity) ε hε] with n hn
  rw [Real.dist_eq]
  exact hn x (by linarith)

end HRS.MS.BreakdownS67
